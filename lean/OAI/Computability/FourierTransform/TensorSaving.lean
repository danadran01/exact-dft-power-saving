import OAI.Computability.FourierTransform.Grouped.GSaving
import OAI.Computability.FourierTransform.Colour.Final
import OAI.Computability.FourierTransform.RecursionBounds
import OAI.Computability.FourierTransform.TensorCertificate

namespace OAI
namespace PowerSaving
open Real Filter Asymptotics
noncomputable section
namespace RAM

/-- Work bound for the flat recursion. k=0 treated with k+1 in the conclusion. -/
theorem allot_bound (u a D : ℕ) (hu : 3≤u) (z : ℝ) (hz : 0≤z)
    (hD : (D:ℝ)/(2:ℝ)^a < (u:ℝ)^z) :
    ∃ C : ℝ, 1≤C ∧ ∀ k : ℕ,
      (allot u a D k : ℝ) ≤ C*(2:ℝ)^k*((k:ℝ)+1)^z := by
  let Q := (2:ℝ)^a
  let s := (D:ℝ)/Q
  let t := (u:ℝ)^z
  have ht : 0<t-s := sub_pos.mpr hD
  let C := 1+(t-s)⁻¹
  have hc : 1≤C := by unfold C; simp [ht.le]
  have hg : 1 ≤ C*(t-s) := by unfold C; rw [add_mul, inv_mul_cancel₀ ht.ne']; linarith
  have hQ : 0<Q := by positivity
  have H (k : ℕ) (hk : 0<k) :
      (allot u a D k : ℝ) ≤ C*(2:ℝ)^k*(k:ℝ)^z := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have hk' : 1 ≤ (k:ℝ) := Nat.one_le_cast.mpr hk
      have hgk : 1≤(k:ℝ)^z := Real.one_le_rpow hk' hz
      rw [allot]
      split
      next h =>
        let f : ℕ := k/u
        have hf : 1 ≤ f := by
          have h := h.2
          unfold threshold at h
          apply (Nat.le_div_iff_mul_le (by omega)).2
          calc
            _ ≤ u*(a+1) := by simp [mul_add]
            _ ≤ _ := h
        let b := (batches u a k:ℝ)
        let x := (2:ℝ)^k
        let y := (2:ℝ)^f
        have he : x=b*(Q*y) := by
          dsimp only [x,b,y,Q,f]
          exact_mod_cast (rounds_eq u a k hu h.2).symm
        have hf' : 1 ≤ (f:ℝ) := Nat.one_le_cast.mpr hf
        have hy : 1 ≤ (f:ℝ)^z := Real.one_le_rpow hf' hz
        have hw : t*(f:ℝ)^z ≤ (k:ℝ)^z := by
          unfold t
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          apply Real.rpow_le_rpow (by positivity) _ hz
          exact_mod_cast Nat.mul_div_le k u
        have hs : 1+C*s*(f:ℝ)^z ≤ C*(k:ℝ)^z := calc
          _ ≤ C*(t-s)*(f:ℝ)^z + C*s*(f:ℝ)^z := by gcongr; nlinarith [hg,hy]
          _ = C*(t*(f:ℝ)^z) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
        push_cast
        change x + D*b* (allot u a D f:ℝ) ≤ C*x*(k:ℝ)^z
        calc
          _ ≤ x + D*b*(C*y*(f:ℝ)^z) := by
            apply add_le_add_right
            apply mul_le_mul_of_nonneg_left (ih f h.1 hf)
            positivity
          _ = x*(1+C*s*(f:ℝ)^z) := by rw [he]; unfold s; field
          _ ≤ x*(C*(k:ℝ)^z) := mul_le_mul_of_nonneg_left hs (by positivity)
          _ = _ := by ring
      next =>
        push_cast
        calc
          _ = 1*(2:ℝ)^k*1 := by simp
          _ ≤ _ := by gcongr
  refine ⟨C,hc,fun k => ?_⟩
  by_cases he : k=0
  · subst k; simpa [allot]
  · apply (H k (Nat.pos_of_ne_zero he)).trans
    gcongr
    first | exact hz | simp

end RAM

/-- MODIFIED (colour-register network + grouped recursion): the certified exponent. -/
def alpha : ℝ := Colour.Expo.zC

theorem alpha_pos : 0<alpha := by norm_num [alpha,Colour.Expo.zC]
theorem alpha_lt : alpha < 1 := by norm_num [alpha,Colour.Expo.zC]

/-- Natural envelopes using a ceiling for real powers. -/
def hills (k : ℕ) := Nat.ceil (((k:ℝ)+1)^alpha)

lemma hills_pos (k : ℕ) : 1≤hills k := by
  exact Nat.one_le_ceil_iff.mpr (by positivity)

lemma hills_mono {a b : ℕ} (h : a≤b) : hills a ≤ hills b := by
  unfold hills
  have := alpha_pos
  gcongr

lemma hills_le (k : ℕ) : hills k ≤ k+1 := by
  have hk : 1≤(k:ℝ)+1 := by simp
  apply Nat.ceil_le.mpr
  simpa using Real.rpow_le_rpow_of_exponent_le hk alpha_lt.le

lemma hills_real (k : ℕ) : (hills k:ℝ) ≤ 2*((k:ℝ)+1)^alpha := by
  have h := Real.one_le_rpow (show 1≤(k:ℝ)+1 by simp) alpha_pos.le
  have hh : (hills k:ℝ) < ((k:ℝ)+1)^alpha+1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith

/-- MODIFIED: from the grouped work bound, generic in the batch histogram `N`. -/
lemma total_hills (N : ℕ → ℕ) (hN0 : N 0 = 0)
    (hN : ∑ c : Fin 24600, (N c : ℝ) * ((c:ℝ)/24600)^alpha < (2:ℝ)^43) :
    ∃ c : ℕ, ∀ k : ℕ, RAM.gallot 24600 43 N k + 1 ≤ c*(2^k*hills k + 1) := by
  have hu : ((24600:ℕ):ℝ) = 24600 := by norm_num
  have hN' : ∑ c : Fin 24600, (N c : ℝ) * ((c:ℝ)/((24600:ℕ):ℝ))^alpha < (2:ℝ)^43 := by
    rw [hu]; exact hN
  obtain ⟨C,hC,h⟩ := RAM.gallot_bound 24600 43 N (by norm_num) hN0 alpha alpha_pos.le hN'
  obtain ⟨c,hc⟩ := exists_nat_ge C
  have ht : 1≤c := Nat.one_le_cast.mp (hC.trans hc)
  refine ⟨c,fun k => ?_⟩
  specialize h k
  have hg : (RAM.gallot 24600 43 N k : ℝ) ≤ c*((2:ℝ)^k*(hills k:ℝ)) := by
    rw [← mul_assoc]
    refine h.trans ?_
    have hh : ((k:ℝ)+1)^alpha ≤ (hills k:ℝ) := Nat.le_ceil _
    gcongr
  have he : RAM.gallot 24600 43 N k ≤ c*(2^k*hills k) := by exact_mod_cast hg
  rw [mul_add,mul_one]
  omega
end
end PowerSaving

end OAI
