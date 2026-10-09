import OAI.Computability.FourierTransform.Grouped.GAllot

/-!
# Work bound for the grouped recursion (new; not part of OpenAI's development)

Analog of OpenAI's `allot_bound`. If the batch-size histogram `N` satisfies
`Σ_c N(c)·(c/u)^z < 2^a`, then `gallot u a N k = O(2^k (k+1)^z)`.
(Proof: `t(k) = gallot k / 2^k` obeys `t(k) ≤ 1 + 2^{-a} Σ_c N(c) t(c⌊k/u⌋)`, and
`C k^z` with `C = 1 + 2^a/(2^a - Σ)` is a supersolution.)
-/

namespace OAI
namespace PowerSaving.RAM
open Real

theorem gallot_bound (u a : ℕ) (N : ℕ → ℕ) (hu : 3 ≤ u) (hN0 : N 0 = 0) (z : ℝ) (hz : 0 ≤ z)
    (hN : ∑ c : Fin u, (N c : ℝ) * ((c:ℝ)/(u:ℝ))^z < (2:ℝ)^a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, (gallot u a N k : ℝ) ≤ C*(2:ℝ)^k*((k:ℝ)+1)^z := by
  set Q : ℝ := (2:ℝ)^a with hQd
  set S : ℝ := ∑ c : Fin u, (N c : ℝ) * ((c:ℝ)/(u:ℝ))^z with hSd
  have hQ : 0 < Q := by positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun c _ => by positivity)
  have ht : 0 < Q - S := sub_pos.mpr hN
  set C : ℝ := 1 + Q*(Q-S)⁻¹ with hCd
  have hc : 1 ≤ C := by
    have : 0 ≤ Q*(Q-S)⁻¹ := by positivity
    linarith
  -- C·(1 - S/Q) ≥ 1
  have hg : 1 ≤ C*(1 - S/Q) := by
    have he : C*(1 - S/Q) = (Q-S)/Q + 1 := by
      rw [hCd]; field_simp
    rw [he]
    have : 0 ≤ (Q-S)/Q := by positivity
    linarith
  have hu' : (0:ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have H (k : ℕ) (hk : 0 < k) : (gallot u a N k : ℝ) ≤ C*(2:ℝ)^k*(k:ℝ)^z := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have hk' : 1 ≤ (k:ℝ) := Nat.one_le_cast.mpr hk
      have hgk : 1 ≤ (k:ℝ)^z := Real.one_le_rpow hk' hz
      rw [gallot_eq]
      split_ifs with h
      · push_cast
        have key (c : Fin u) :
            (N c : ℝ) * (gbatches u a c k : ℝ) * (gallot u a N (c*(k/u)) : ℝ) ≤
              (C*(2:ℝ)^k/Q*(k:ℝ)^z) * ((N c : ℝ) * ((c:ℝ)/(u:ℝ))^z) := by
          by_cases hc0 : (c:ℕ) = 0
          · rw [hc0, hN0]; simp
          · have hpos : 0 < (c:ℕ)*(k/u) := Nat.mul_pos (Nat.pos_of_ne_zero hc0) h.2
            have ih' := ih _ (gdown_lt h c.isLt) hpos
            have hr := grounds_eq u a c k (by omega) h.1 c.isLt
            have hb : (gbatches u a c k : ℝ) * (2:ℝ)^((c:ℕ)*(k/u)) = (2:ℝ)^k / Q := by
              rw [eq_div_iff hQ.ne', hQd]
              have : ((gbatches u a c k * (2^a*2^((c:ℕ)*(k/u))) : ℕ) : ℝ) = ((2^k : ℕ) : ℝ) := by
                rw [hr]
              push_cast at this
              linarith [this]
            have hw : (((c:ℕ)*(k/u) : ℕ) : ℝ)^z ≤ ((c:ℝ)/(u:ℝ))^z * (k:ℝ)^z := by
              rw [← Real.mul_rpow (by positivity) (by positivity)]
              apply Real.rpow_le_rpow (by positivity) _ hz
              have hd : ((k/u : ℕ) : ℝ) ≤ (k:ℝ)/(u:ℝ) := Nat.cast_div_le
              push_cast
              calc (c:ℝ) * ((k/u : ℕ) : ℝ) ≤ (c:ℝ) * ((k:ℝ)/(u:ℝ)) := by gcongr
                _ = (c:ℝ)/(u:ℝ) * k := by ring
            calc (N c : ℝ) * (gbatches u a c k : ℝ) * (gallot u a N (c*(k/u)) : ℝ)
                ≤ (N c : ℝ) * (gbatches u a c k : ℝ) *
                    (C*(2:ℝ)^((c:ℕ)*(k/u))*(((c:ℕ)*(k/u) : ℕ) : ℝ)^z) := by
                  gcongr
              _ = C * ((gbatches u a c k : ℝ) * (2:ℝ)^((c:ℕ)*(k/u))) * (N c : ℝ) *
                    (((c:ℕ)*(k/u) : ℕ) : ℝ)^z := by ring
              _ = C * ((2:ℝ)^k / Q) * (N c : ℝ) * (((c:ℕ)*(k/u) : ℕ) : ℝ)^z := by rw [hb]
              _ ≤ C * ((2:ℝ)^k / Q) * (N c : ℝ) * (((c:ℝ)/(u:ℝ))^z * (k:ℝ)^z) := by gcongr
              _ = _ := by ring
        have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => key c)
        rw [← Finset.mul_sum] at hsum
        have hx : 0 < (2:ℝ)^k := by positivity
        have hfin : (2:ℝ)^k + C*(2:ℝ)^k/Q*(k:ℝ)^z * S ≤ C*(2:ℝ)^k*(k:ℝ)^z := by
          have h1 : (2:ℝ)^k * 1 ≤ (2:ℝ)^k * (C*(1 - S/Q)*(k:ℝ)^z) := by
            apply mul_le_mul_of_nonneg_left _ hx.le
            nlinarith
          have h2 : C*(2:ℝ)^k/Q*(k:ℝ)^z * S = (2:ℝ)^k * (C*(S/Q)*(k:ℝ)^z) := by
            field_simp
          rw [h2]
          nlinarith
        calc _ ≤ (2:ℝ)^k + C*(2:ℝ)^k/Q*(k:ℝ)^z * S := by
              rw [hSd]; linarith [hsum]
          _ ≤ _ := hfin
      · push_cast
        calc (2:ℝ)^k = 1*(2:ℝ)^k*1 := by ring
          _ ≤ _ := by gcongr
  refine ⟨C, hc, fun k => ?_⟩
  by_cases he : k = 0
  · subst k
    have h0 : gallot u a N 0 = 1 := by
      rw [gallot_eq]
      split_ifs with h1
      · exfalso
        have h2 := h1.1
        unfold threshold at h2
        have : 0 < u*(a+1) := by positivity
        omega
      · rfl
    rw [h0]; simp; exact hc
  · apply (H k (Nat.pos_of_ne_zero he)).trans
    have hk1 : 1 ≤ (k:ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero he)
    have : (k:ℝ)^z ≤ ((k:ℝ)+1)^z := Real.rpow_le_rpow (by positivity) (by linarith) hz
    have : 0 ≤ C*(2:ℝ)^k := by positivity
    gcongr

end PowerSaving.RAM
end OAI
