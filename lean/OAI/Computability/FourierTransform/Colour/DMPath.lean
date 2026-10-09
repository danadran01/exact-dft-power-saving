import OAI.Computability.FourierTransform.Grouped.GNetPaths

/-!
# Colour network, part 8: paired grouped paths for any role type (new)

OpenAI's `DPath` (NetworkInvocation) proves a shear `M` and its inverse-transpose shear `(M⁻¹)ᵀ`
together, along the same labels. Over the grouped API (`MPath`, multisets of batch sizes) and for an
arbitrary local role type `ρ` (the colour network's `Box` depends on the register design). The
inverse-transpose path is the stage-2 (reverse) invocation, so the forward schedule of Theorem C is
the only schedule that has to be formalised.
-/

namespace OAI
namespace PowerSaving.Colour
open Matrix Binary Finset

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

lemma actPoint_one : actPoint (1 : Matrix ρ ρ ℚ) = id := by
  funext x i
  unfold actPoint
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h; simp [one_apply, Ne.symm h]
  · simp

lemma actPoint_mul (M N : Matrix ρ ρ ℚ) : actPoint (M * N) = actPoint M ∘ actPoint N := by
  funext x i
  simp only [actPoint, Function.comp_apply, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul,
    sum_mul, mul_sum, _root_.mul_assoc]
  rw [sum_comm]

/-- A shear and its inverse-transpose along the same labels, with batch multiset `E`. -/
def DMPath (A : ρ → OBase α) (s t : ρ → Finset α) (M : Matrix ρ ρ ℚ) (E : Multiset ℕ) : Prop :=
  ∃ N : Matrix ρ ρ ℚ, M * N = 1 ∧ MPath A s t (actPoint M) E ∧ MPath A s t (actPoint Nᵀ) E

/-- Gate condition in projection form. -/
def Sync (A : ρ → OBase α) (s : ρ → Finset α) (Z : Matrix ρ ρ ℚ) : Prop :=
  ∀ i k, Z i k ≠ 0 → (A i).mat (s i) = (A k).mat (s k)

namespace DMPath
variable {A : ρ → OBase α} {s t u : ρ → Finset α} {M N : Matrix ρ ρ ℚ} {d e : Multiset ℕ}

lemma of_id (h : MPath A s t id d) : DMPath A s t 1 d := by
  refine ⟨1, mul_one _, ?_, ?_⟩ <;> simpa [actPoint_one]

lemma trans (a : DMPath A s t M d) (b : DMPath A t u N e) : DMPath A s u (N * M) (d + e) := by
  obtain ⟨x, hx, hm, hn⟩ := a
  obtain ⟨y, hy, hl, hk⟩ := b
  refine ⟨x * y, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, hx, one_mul, hy]
  · rw [actPoint_mul]; exact hm.trans hl
  · rw [transpose_mul, actPoint_mul]; exact hn.trans hk

lemma congrE (a : DMPath A s t M d) (h : d = e) : DMPath A s t M e := h ▸ a

lemma congrM (a : DMPath A s t M d) (h : M = N) : DMPath A s t N d := h ▸ a

/-- Square-zero gates `1 ± Z` whose nonzero entries join equal projections. -/
lemma paired {Z : Matrix ρ ρ ℚ} (h : Z * Z = 0) (g : Sync A s Z) :
    DMPath A s s (1 + Z) 0 ∧ DMPath A s s (1 - Z) 0 := by
  have cond (i k) (hz : Z i k ≠ 0) : frame (A i) (s i) = frame (A k) (s k) :=
    frame_congr _ _ _ _ (g i k hz)
  have inv1 : (1 + Z) * (1 - Z) = 1 := by simp [Matrix.mul_sub, Matrix.add_mul, h]
  have inv2 : (1 - Z) * (1 + Z) = 1 := by simp [Matrix.mul_add, Matrix.sub_mul, h]
  constructor
  · refine ⟨1 - Z, inv1, MPath.gate _ ?_, MPath.gate _ ?_⟩
    · intro i k hz
      by_cases hik : i = k
      · subst k; rfl
      · apply cond i k; simpa [one_apply, hik] using hz
    · intro i k hz
      by_cases hik : k = i
      · subst k; rfl
      · exact (cond k i (by simpa [one_apply, hik] using hz)).symm
  · refine ⟨1 + Z, inv2, MPath.gate _ ?_, MPath.gate _ ?_⟩
    · intro i k hz
      by_cases hik : i = k
      · subst k; rfl
      · apply cond i k; simpa [one_apply, hik] using hz
    · intro i k hz
      by_cases hik : k = i
      · subst k; rfl
      · exact (cond k i (by simpa [one_apply, hik] using hz)).symm

lemma rise (g : ∀ i, s i ⊆ t i) : DMPath A s t 1 (riseM s t) := of_id (MPath.inc _ g)

lemma fall (g : ∀ i, t i ⊆ s i) : DMPath A s t 1 (fallM s t) := of_id (MPath.dec _ g)

/-- Final form: the shear `1 + X` with `X² = 0` and its inverse-transpose `(1 - X)ᵀ`. -/
lemma final {X : Matrix ρ ρ ℚ} (hX : X * X = 0) (a : DMPath A s t (1 + X) d) :
    MPath A s t (actPoint (1 + X)) d ∧ MPath A s t (actPoint (1 - X)ᵀ) d := by
  obtain ⟨N, hN, H, G⟩ := a
  have hN' : N = 1 - X := by
    calc N = ((1 - X) * (1 + X)) * N := by
            rw [show (1 - X) * (1 + X) = 1 by simp [Matrix.mul_add, Matrix.sub_mul, hX], one_mul]
      _ = 1 - X := by rw [Matrix.mul_assoc, hN, mul_one]
  subst hN'
  exact ⟨H, G⟩

end DMPath
end PowerSaving.Colour
end OAI
