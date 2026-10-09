import OAI.Computability.FourierTransform.BinaryFrames

/-!
# Colour network, part 1: orthonormal-basis toolkit (new; not part of OpenAI's development)

* `dtensor`: the tensor product of orthonormal bases of the factors of a *dependent* product
  `∀ j, H j` (OpenAI's `OBase.tensor` is for `J → H`; unequal factor sizes need the dependent one),
  and `mat_drect`, the projection onto a rectangle `piFinset s` (dependent `OBase.mat_rect`).
* `reindex`: permuting the index set of an orthonormal basis.
* Projection congruences (gate synchronisation compares projections, never bases):
  `mat_congr_family` (same vectors), `mat_compl`, `mat_congr_orth` (spans agree, checked by
  orthogonality of basis vectors), `mat_eq_canonical` (block-supported bases).
* `ind`, `dot_ind`: indicator vectors and their dot products (parity of the intersection).
-/

namespace OAI
namespace PowerSaving.Colour
open Finset Matrix Binary

section Basic
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Expansion of a vector in an orthonormal basis. -/
theorem expand (A : OBase α) (x : Space α) (i : α) :
    x i = ∑ k, dot (A.v k) x * A.v k i := by
  have h := congr_fun (OBase.proj_univ A x) i
  rw [← h]
  simp [OBase.proj, Finset.sum_apply, smul_eq_mul]

/-- A projection matrix is determined by the projection map. -/
theorem mat_eq_of_proj (A B : OBase α) (s t : Finset α) (h : A.proj s = B.proj t) :
    A.mat s = B.mat t := by
  ext i k
  have e := congr_fun (congr_fun h (eu k)) i
  simpa [OBase.proj_apply, eu, mul_ite] using e

/-- Same vectors on the same index set give the same projection. -/
theorem mat_congr_family (A B : OBase α) (s : Finset α) (h : ∀ i ∈ s, A.v i = B.v i) :
    A.mat s = B.mat s := by
  ext i j
  unfold OBase.mat
  apply sum_congr rfl
  intro k hk
  rw [h k hk]

/-- Complement of an index set. -/
theorem mat_compl (A : OBase α) (s : Finset α) : A.mat (univ \ s) = 1 - A.mat s := by
  rw [OBase.mat_sub A univ s (subset_univ _), OBase.mat_univ]

theorem mat_compl_congr (A B : OBase α) (s t : Finset α) (h : A.mat s = B.mat t) :
    A.mat (univ \ s) = B.mat (univ \ t) := by
  rw [mat_compl, mat_compl, h]

theorem mat_singleton_congr (A B : OBase α) (i k : α) (h : A.v i = B.v k) :
    A.mat {i} = B.mat {k} := by
  ext j l; simp [OBase.mat, h]

/-- Spans agree: every vector of `A` inside `s` is orthogonal to the vectors of `B` outside `t`,
and every vector of `A` outside `s` is orthogonal to the vectors of `B` inside `t`. -/
theorem mat_congr_orth (A B : OBase α) (s t : Finset α)
    (h₁ : ∀ i ∈ s, ∀ k ∉ t, dot (A.v i) (B.v k) = 0)
    (h₂ : ∀ i ∉ s, ∀ k ∈ t, dot (A.v i) (B.v k) = 0) :
    A.mat s = B.mat t := by
  ext i j
  unfold OBase.mat
  -- expand `A.v a j` in the basis `B`
  calc ∑ a ∈ s, A.v a i * A.v a j
      = ∑ a ∈ s, A.v a i * ∑ k, dot (B.v k) (A.v a) * B.v k j := by
        apply sum_congr rfl; intro a _; rw [← expand B (A.v a) j]
    _ = ∑ k, B.v k j * ∑ a ∈ s, dot (A.v a) (B.v k) * A.v a i := by
        simp only [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro k _
        apply sum_congr rfl; intro a _
        rw [dot_symm]; ring
    _ = ∑ k ∈ t, B.v k j * B.v k i := by
        rw [← sum_subset (subset_univ t)]
        · apply sum_congr rfl
          intro k hk
          congr 1
          rw [expand A (B.v k) i]
          rw [← sum_subset (subset_univ s)]
          intro a _ ha
          rw [h₂ a ha k hk, zero_mul]
        · intro k _ hk
          rw [sum_eq_zero, mul_zero]
          intro a ha
          rw [h₁ a ha k hk, zero_mul]
    _ = ∑ k ∈ t, B.v k i * B.v k j := by
        apply sum_congr rfl; intro k _; ring

/-- A basis whose vectors inside `s` are supported in `s`, and outside `s` are supported outside
`s`, has the coordinate projection on `s`. -/
theorem mat_eq_canonical (A : OBase α) (s : Finset α)
    (h₁ : ∀ k ∈ s, ∀ i ∉ s, A.v k i = 0) (h₂ : ∀ k ∉ s, ∀ i ∈ s, A.v k i = 0) :
    A.mat s = (OBase.canonical α).mat s := by
  apply mat_congr_orth
  · intro k hk i hi
    change dot (A.v k) (eu i) = 0
    rw [dot_eu_right]; exact h₁ k hk i hi
  · intro k hk i hi
    change dot (A.v k) (eu i) = 0
    rw [dot_eu_right]; exact h₂ k hk i hi

/-! ### Reindexing -/

/-- Permute the index set of an orthonormal basis: the new vector `i` is the old vector `e i`. -/
def reindex (A : OBase α) (e : α ≃ α) : OBase α :=
  ⟨fun i => A.v (e i), fun i j => by rw [A.rows]; simp [e.injective.eq_iff]⟩

@[simp] theorem reindex_v (A : OBase α) (e : α ≃ α) (i : α) : (reindex A e).v i = A.v (e i) := rfl

theorem mat_reindex (A : OBase α) (e : α ≃ α) (s : Finset α) :
    (reindex A e).mat s = A.mat (s.map e.toEmbedding) := by
  ext i j
  simp [OBase.mat, Finset.sum_map]

/-! ### Indicator vectors -/

/-- Indicator vector of a set of coordinates. -/
def ind (X : Finset α) : Space α := fun i => if i ∈ X then 1 else 0

omit [Fintype α] in
@[simp] theorem ind_apply (X : Finset α) (i : α) : ind X i = if i ∈ X then 1 else 0 := rfl

theorem dot_ind (X Y : Finset α) : dot (ind X) (ind Y) = ((X ∩ Y).card : F) := by
  unfold dot ind
  calc ∑ i, (if i ∈ X then (1:F) else 0) * (if i ∈ Y then 1 else 0)
      = ∑ i, (if i ∈ X ∩ Y then (1:F) else 0) := by
        apply sum_congr rfl; intro i _
        by_cases hx : i ∈ X <;> by_cases hy : i ∈ Y <;> simp [hx, hy]
    _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_one]

omit [Fintype α] in
theorem ind_singleton (i : α) : ind {i} = eu i := by
  funext j; simp [ind, eu, eq_comm]

omit [Fintype α] in
theorem ind_insert (a : α) (X : Finset α) (ha : a ∉ X) : ind (insert a X) = eu a + ind X := by
  funext j
  by_cases h : j = a
  · subst j; simp [ind, eu, ha]
  · simp [ind, eu, h, Ne.symm h]

@[simp] theorem dot_eu_eu (i j : α) : dot (eu i) (eu j) = if i = j then 1 else 0 := by
  rw [dot_eu_left]; simp [eu, eq_comm]

theorem dot_ind_self (X : Finset α) : dot (ind X) (ind X) = (X.card : F) := by
  rw [dot_ind, inter_self]

end Basic

/-! ### Dependent tensor products -/

section Tensor
variable {J : Type*} [Fintype J] [DecidableEq J]
  {H : J → Type*} [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)]

/-- Pure tensor of basis vectors. -/
def dpure (A : ∀ j, OBase (H j)) (k : ∀ j, H j) : Space (∀ j, H j) :=
  fun l => ∏ j, (A j).v (k j) (l j)

/-- Tensor product of orthonormal bases of the factors of a dependent product. -/
def dtensor (A : ∀ j, OBase (H j)) : OBase (∀ j, H j) where
  v := dpure A
  rows := fun x y => by
    classical
    simp only [dpure, dot, ← prod_mul_distrib]
    rw [← Fintype.prod_sum (fun j l => (A j).v (x j) l * (A j).v (y j) l)]
    have hh (j : J) : ∑ l, ((A j).v (x j) l * (A j).v (y j) l) =
        if x j = y j then 1 else 0 := (A j).rows (x j) (y j)
    simp only [hh]
    exact prod_delta x y

@[simp] theorem dtensor_v (A : ∀ j, OBase (H j)) (k : ∀ j, H j) (l : ∀ j, H j) :
    (dtensor A).v k l = ∏ j, (A j).v (k j) (l j) := rfl

/-- Projection onto a rectangle of index sets. -/
theorem mat_drect (A : ∀ j, OBase (H j)) (s : ∀ j, Finset (H j)) :
    (dtensor A).mat (Fintype.piFinset s) = digitProd (fun j => (A j).mat (s j)) := by
  ext x y
  simp only [digitProd_apply, OBase.mat, dtensor_v, ← prod_mul_distrib]
  exact (prod_univ_sum s (fun j l => (A j).v l (x j) * (A j).v l (y j))).symm

/-- Rectangle projections agree when every factor projection agrees. -/
theorem drect_congr (A B : ∀ j, OBase (H j)) (s t : ∀ j, Finset (H j))
    (h : ∀ j, (A j).mat (s j) = (B j).mat (t j)) :
    (dtensor A).mat (Fintype.piFinset s) = (dtensor B).mat (Fintype.piFinset t) := by
  rw [mat_drect, mat_drect]
  congr 1; funext j; exact h j

end Tensor

end PowerSaving.Colour
end OAI
