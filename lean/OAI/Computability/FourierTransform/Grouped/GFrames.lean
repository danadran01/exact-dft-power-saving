import OAI.Computability.FourierTransform.Grouped.BatchAlgebra
import OAI.Computability.FourierTransform.DirectionalWords

/-!
# Grouped frame changes (new; not part of OpenAI's development)

A whole edge of a role's frame path, i.e. adding (or removing) a set `R` of basis lines to the role's
frame, is ONE move. Its matrix is a translation times `bdir A R = ∏_{i∈R} dir (A.v i)`. Grouped paths
record the list of batch sizes `|R|`, which drives the grouped recursion: one recursive call of size
`|R|·f` per batch, instead of `|R|` calls of size `f`.
-/

namespace OAI
namespace PowerSaving.Binary
open Finset Matrix
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma batchMat_wrap (ρ : ℕ) (z : Fin ρ → Space α) :
    batchMat ρ z = wrap (fun x => ∏ k, tint (dot (z k) x)) := by
  induction ρ with
  | zero => simp [batchMat, wrap_one]
  | succ n ih =>
    simp only [batchMat] at ih ⊢
    rw [List.ofFn_succ', List.prod_concat, ih, dir_phase, wrap_mul]
    congr 1; funext x
    rw [Fin.prod_univ_castSucc]

/-- The batch of directional factors of the basis lines `R`. -/
def bdir (A : OBase α) (R : Finset α) : CMat α := wrap fun x => ∏ i ∈ R, tint (dot (A.v i) x)

lemma bdir_eq_batchMat (A : OBase α) (R : Finset α) :
    bdir A R = batchMat R.card (fun k => A.v (R.equivFin.symm k)) := by
  rw [batchMat_wrap, bdir]
  congr 1; funext x
  rw [← Finset.prod_coe_sort R]
  exact Fintype.prod_equiv R.equivFin _ _ (fun i => by simp)

/-- Product of the frame-change factors `delta` of the lines `R`. -/
def bdelta (A : OBase α) (R : Finset α) : CMat α :=
  wrap fun x => ∏ i ∈ R, lum (dot (A.v i) x • A.v i)

omit [DecidableEq α] in
lemma lum_smul_unit (z : Space α) (hz : dot z z = 1) (c : F) :
    lum (c • z) = tint c * (if lum z = Complex.I then 1 else sign c) := by
  rcases bit_cases c with rfl | rfl
  · simp [tint, sign]
  · rcases lum_of_unit z hz with h | h
    · simp [h, tint]
    · have hI : (-Complex.I) ≠ Complex.I := by
        intro hh; have := congrArg Complex.im hh; simp at this; norm_num at this
      simp [h, tint, sign, hI]

/-- Lines whose phase is `-i` (they need a translation correction). -/
def negLines (A : OBase α) (R : Finset α) : Finset α := R.filter (fun i => lum (A.v i) ≠ Complex.I)

lemma dot_sum_left (S : Finset α) (v : α → Space α) (x : Space α) :
    dot (∑ i ∈ S, v i) x = ∑ i ∈ S, dot (v i) x := by
  simp only [dot, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma bdelta_eq (A : OBase α) (R : Finset α) :
    bdelta A R = shift (∑ i ∈ negLines A R, A.v i) * bdir A R := by
  rw [bdelta, bdir, shift_phase, wrap_mul]
  congr 1; funext x
  simp_rw [lum_smul_unit _ (A.self _), Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [dot_sum_left, sign_sum, negLines, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : lum (A.v i) = Complex.I <;> simp [h]

/-- Adding a set of lines at once. -/
lemma frame_union (A : OBase α) (R s : Finset α) (h : Disjoint R s) :
    frame A (R ∪ s) = bdelta A R * frame A s := by
  induction R using Finset.induction_on with
  | empty => simp [bdelta, wrap_one]
  | @insert i R hi ih =>
    have hs : i ∉ R ∪ s := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hi, Finset.disjoint_left.mp h (Finset.mem_insert_self i R)⟩
    have hR : Disjoint R s := Finset.disjoint_of_subset_left (Finset.subset_insert i R) h
    rw [Finset.insert_union, frame_ins A _ i hs, ih hR, ← Matrix.mul_assoc]
    congr 1
    rw [delta, bdelta, bdelta, wrap_mul]
    congr 1; funext x
    rw [Finset.prod_insert hi]

lemma bdelta_sq (A : OBase α) (R : Finset α) :
    bdelta A R * bdelta A R = shift (∑ i ∈ R, A.v i) := by
  rw [bdelta, wrap_mul, shift_phase]
  congr 1; funext x
  rw [← Finset.prod_mul_distrib, dot_sum_left, sign_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [lum_sq]
  rcases bit_cases (dot (A.v i) x) with h | h <;> simp [h, A.self]

/-- Removing a set of lines at once: the inverse batch. -/
lemma frame_remove (A : OBase α) (R s : Finset α) (h : Disjoint R s) :
    frame A s = (shift (∑ i ∈ R, A.v i) * bdelta A R) * frame A (R ∪ s) := by
  rw [frame_union A R s h, ← Matrix.mul_assoc, Matrix.mul_assoc (shift _), bdelta_sq, shift_sq,
    Matrix.one_mul]

end
end PowerSaving.Binary
end OAI
