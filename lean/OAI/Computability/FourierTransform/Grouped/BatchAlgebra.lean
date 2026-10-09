import OAI.Computability.FourierTransform.TensorFibers

/-!
# Grouped edges, algebra (new; not part of OpenAI's development)

One edge of a role's frame path consists of the directional factors `dir z_k`, `k < ρ`.
The directions are linearly independent (they are distinct members of the role's orthonormal basis).
We prove that their product is, after one linear change of address coordinates
`e : Space α ≃ₗ Space β × Space (Fin ρ)` with `e (z k) = (0, eₖ)`, the kernel on the `ρ` new
coordinates (identity on the rest). This generalizes `peel_dir` (the case `ρ = 1`). It is the
algebraic content of Lemma 1 / Corollary 1 of `proofs/PROOFS.md`: one edge = ONE batch of `C^{⊗ρ}`.
-/

namespace OAI
namespace PowerSaving.Binary
open Finset Matrix
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The product of the directional factors of one edge. -/
def batchMat (ρ : ℕ) (z : Fin ρ → Space α) : CMat α := (List.ofFn fun k => dir (z k)).prod

lemma two_eq_zero : (1 : F) + 1 = 0 := by decide

lemma dir_apply (z w y : Space α) :
    dir z w y = ca * (if w = y then 1 else 0) + cb * (if w + z = y then 1 else 0) := by
  simp [dir, shift, Matrix.one_apply]

lemma littleC_zero_add (i j : F) : littleC i j = littleC 0 (i + j) := by
  rcases bit_cases i with rfl | rfl <;> rcases bit_cases j with rfl | rfl <;>
    simp [littleC, two_eq_zero]

lemma kernel_eq_zero_add (κ : Type*) [Fintype κ] (a b : Space κ) :
    kernel κ a b = kernel κ 0 (a + b) := by
  simp only [kernel, digitProd_apply]
  exact Finset.prod_congr rfl (fun k _ => by simpa using littleC_zero_add (a k) (b k))

lemma add_self_space (x : Space α) : x + x = 0 := by
  funext i; simp only [Pi.add_apply, Pi.zero_apply]; exact CharTwo.add_self_eq_zero (x i)

/-- Expansion of a batch into shifts, indexed by indicator vectors `s`. -/
lemma batchMat_apply (ρ : ℕ) (z : Fin ρ → Space α) (x y : Space α) :
    batchMat ρ z x y = ∑ s : Space (Fin ρ),
      if x + ∑ k, s k • z k = y then kernel (Fin ρ) 0 s else 0 := by
  induction ρ generalizing y with
  | zero =>
    have hs : ∀ s : Space (Fin 0), s = 0 := fun s => funext (fun k => k.elim0)
    rw [Fintype.sum_eq_single 0 (fun s hs' => (hs' (hs s)).elim)]
    simp [batchMat, kernel, Matrix.one_apply]
  | succ n ih =>
    have hprod : batchMat (n+1) z = batchMat n (fun k => z k.castSucc) * dir (z (Fin.last n)) := by
      simp only [batchMat]
      rw [List.ofFn_succ', List.prod_concat]
    rw [hprod, Matrix.mul_apply]
    simp_rw [dir_apply, mul_add, Finset.sum_add_distrib]
    -- the two terms: w = y and w + z_last = y
    have h1 : ∑ w, batchMat n (fun k => z k.castSucc) x w * (ca * if w = y then 1 else 0)
        = ca * batchMat n (fun k => z k.castSucc) x y := by
      simp [mul_comm, mul_left_comm]
    have h2 : ∑ w, batchMat n (fun k => z k.castSucc) x w *
          (cb * if w + z (Fin.last n) = y then 1 else 0)
        = cb * batchMat n (fun k => z k.castSucc) x (y + z (Fin.last n)) := by
      rw [Finset.sum_eq_single (y + z (Fin.last n))]
      · simp [add_assoc, add_self_space, mul_comm]
      · intro w _ hw
        have : ¬ (w + z (Fin.last n) = y) := by
          intro h; apply hw; rw [← h, add_assoc, add_self_space, add_zero]
        simp [this]
      · simp
    rw [h1, h2, ih, ih, Finset.mul_sum, Finset.mul_sum]
    -- split s : Space (Fin (n+1)) as (last bit, init)
    rw [← (Fin.snocEquiv (fun _ => F)).sum_comp, Fintype.sum_prod_type, sum_bits]
    have hsum (s' : Space (Fin n)) (b : F) :
        (∑ k, (Fin.snocEquiv (fun _ => F) (b, s')) k • z k)
          = (∑ k, s' k • z k.castSucc) + b • z (Fin.last n) := by
      rw [Fin.sum_univ_castSucc]
      simp [Fin.snocEquiv]
    have hker (s' : Space (Fin n)) (b : F) :
        kernel (Fin (n+1)) 0 (Fin.snocEquiv (fun _ => F) (b, s'))
          = kernel (Fin n) 0 s' * littleC 0 b := by
      simp only [kernel, digitProd_apply]
      rw [Fin.prod_univ_castSucc]
      simp [Fin.snocEquiv]
    simp_rw [hsum, hker]
    have hiff (S : Space α) : (x + (S + z (Fin.last n)) = y) ↔ (x + S = y + z (Fin.last n)) := by
      constructor
      · intro h; rw [← h, add_assoc, add_assoc, add_self_space, add_zero]
      · intro h; rw [← add_assoc, h, add_assoc, add_self_space, add_zero]
    congr 1
    · apply Finset.sum_congr rfl; intro s' _
      simp only [zero_smul, add_zero, littleC, if_pos rfl]
      split_ifs <;> ring
    · apply Finset.sum_congr rfl; intro s' _
      simp only [one_smul, hiff]
      have hc : littleC 0 1 = cb := by simp [littleC]
      rw [hc]
      split_ifs <;> ring

/-- **Batch = kernel on the peeled coordinates.** If an additive coordinate change
`e : Space α ≃ₗ[F] Space β × Space (Fin ρ)` sends each direction `z k` to `(0, eₖ)`, then
the batch matrix is the identity on the `β`-part tensored with `kernel (Fin ρ)`.
(`ρ = 1` is OpenAI's `peel_dir`.) -/
theorem batchMat_peel {β : Type*} [Fintype β] [DecidableEq β] (ρ : ℕ) (z : Fin ρ → Space α)
    (e : Space α ≃ₗ[F] Space β × Space (Fin ρ))
    (he : ∀ k, e (z k) = (0, Pi.single k 1)) (x y : Space α) :
    batchMat ρ z x y =
      if (e x).1 = (e y).1 then kernel (Fin ρ) (e x).2 (e y).2 else 0 := by
  rw [batchMat_apply]
  -- e (∑ s_k • z_k) = (0, s)
  have hes (s : Space (Fin ρ)) : e (∑ k, s k • z k) = (0, s) := by
    rw [map_sum]
    simp_rw [map_smul, he]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · funext j
      simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hcond (s : Space (Fin ρ)) :
      (x + ∑ k, s k • z k = y) ↔ ((e x).1 = (e y).1 ∧ (e x).2 + s = (e y).2) := by
    rw [← e.injective.eq_iff, map_add, hes, Prod.ext_iff]
    simp
  by_cases h1 : (e x).1 = (e y).1
  · rw [if_pos h1, Fintype.sum_eq_single ((e x).2 + (e y).2)]
    · rw [if_pos ((hcond _).2 ⟨h1, by rw [← add_assoc, add_self_space, zero_add]⟩)]
      exact (kernel_eq_zero_add _ _ _).symm
    · intro s hs
      rw [if_neg]
      intro h
      apply hs
      have h2 := ((hcond s).1 h).2
      rw [← h2, ← add_assoc, add_self_space, zero_add]
  · rw [if_neg h1]
    apply Finset.sum_eq_zero
    intro s _
    rw [if_neg]
    exact fun h => h1 ((hcond s).1 h).1

end
end PowerSaving.Binary
end OAI
