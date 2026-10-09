import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Colour network, part 14: the exponent inequality (new)

Design- and network-independent part of the exponent certificate for the colour-register network
at factor sizes `(30, 20, 41)`, `u = m = 24600`, `2^43` roles, exponent `z = 1 - 321/10^8` (`3.21·10⁻⁶`, strictly
below the stated `3.2·10⁻⁶`; FORMALIZATION_CNET.md §5, row C14 of §6).

* `phiG u z c = (c/u)^z` and its three bounds:
  - `lemma5` (Lemma 5 of `proofs/PROOFS.md`): `(ρ/u)^{1-ε} ≤ (ρ/u)(1 + ε μ ℓ)`, `ℓ ≥ ln(u/ρ)`;
  - `tangent_sum` (one-point Jensen / Bernoulli): at most `n` nonzero sizes `f i ≥ 0` with
    `Σ f i ≤ S` give `Σ φ(f i) ≤ n φ(S/n)`;
  - `phiG_le_mul` (crude): `φ(c) ≤ c φ(1)` for `c ∈ ℕ`.
* tight logarithms (`log_le_of_exp_sum`): `ln x ≤ j·0.6931471808 + q` from
  `x ≤ 2^j Σ_{i<N} q^i/i!` (partial sums of the exponential series, `Real.sum_le_exp_of_nonneg`,
  and `Real.log_two_lt_d9`);
* the 22 rational bounds `phi ρ ≤ Rρ` for the batch-size classes of the network;
* the per-invocation cost classes of §5.2 (banks and centres fixed; side wires; coordinate
  X-registers with `≤ 2` middle edges; coordinate Y-registers with `≤ 10` middle edges; all
  other registers by the crude bound) and the padding cost;
* `bound cX cY sun side`: the explicit rational bound as a function of the per-factor counts,
  monotone in each count (`bound_mono`), and `exponent_ineq : bound (design counts) < 2^43`;
* `totalCost_lt`: the real-valued statement used by the certificate: for any counts dominated by the
  design counts, with the padding filling `2^43` roles, `Σ_j inv_j Φ(E_inv,j) + P(φ 1 + φ(u-1))`
  (in cost-class form, `totalCost`) is `< 2^43`.
-/

namespace OAI
namespace PowerSaving.Colour
namespace Expo
open Finset Real

/-! ### Generic analytic lemmas -/

/-- `φ_{u,z}(c) = (c/u)^z`. -/
noncomputable def phiG (u z c : ℝ) : ℝ := (c / u) ^ z

lemma phiG_zero (u z : ℝ) (hz : z ≠ 0) : phiG u z 0 = 0 := by
  simp [phiG, Real.zero_rpow hz]

lemma phiG_nonneg (u z c : ℝ) (hu : 0 ≤ u) (hc : 0 ≤ c) : 0 ≤ phiG u z c :=
  Real.rpow_nonneg (div_nonneg hc hu) z

/-- **Lemma 5** (`proofs/PROOFS.md`): for `1 ≤ ρ ≤ M`, `ln M ≤ Lm`, `c Lm < 1`, `ln(M/ρ) ≤ ℓ`,
`(ρ/M)^{1-c} ≤ (ρ/M)(1 + c μ ℓ)` with `μ = 1/(1 - c Lm)`. -/
theorem lemma5 (ρ M c Lm ℓ : ℝ) (hρ1 : 1 ≤ ρ) (hρM : ρ ≤ M) (hc : 0 ≤ c)
    (hLm : Real.log M ≤ Lm) (hcL : c * Lm < 1) (hℓ : Real.log (M / ρ) ≤ ℓ) :
    (ρ / M) ^ (1 - c) ≤ (ρ / M) * (1 + c * (1 / (1 - c * Lm)) * ℓ) := by
  have hρ : 0 < ρ := by linarith
  have hM : 0 < M := lt_of_lt_of_le hρ hρM
  have hx : 0 < ρ / M := div_pos hρ hM
  set y := c * Real.log (M / ρ) with hydef
  have hlogx0 : 0 ≤ Real.log (M / ρ) := Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
  have hy0 : 0 ≤ y := mul_nonneg hc hlogx0
  have hrw : (ρ / M) ^ (1 - c) = (ρ / M) * Real.exp y := by
    rw [Real.rpow_def_of_pos hx]
    have hl : Real.log (ρ / M) = - Real.log (M / ρ) := by
      rw [← Real.log_inv, inv_div]
    rw [hl, hydef]
    have : -Real.log (M / ρ) * (1 - c) = Real.log (ρ / M) + c * Real.log (M / ρ) := by
      rw [hl]; ring
    rw [this, Real.exp_add, Real.exp_log hx]
  rw [hrw]
  have hey : 0 < Real.exp y := Real.exp_pos y
  have hkey : Real.exp y * (1 - y) ≤ 1 := by
    have h := Real.add_one_le_exp (-y)
    have h' : (1 - y) * Real.exp y ≤ Real.exp (-y) * Real.exp y :=
      mul_le_mul_of_nonneg_right (by linarith) hey.le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h'
    linarith
  have hlogle : Real.log (M / ρ) ≤ Real.log M := by
    apply Real.log_le_log (div_pos hM hρ)
    rw [div_le_iff₀ hρ]
    nlinarith
  have hyL : y ≤ c * Lm := by
    have := mul_le_mul_of_nonneg_left (le_trans hlogle hLm) hc
    linarith
  have hμ : Real.exp y ≤ 1 / (1 - c * Lm) := by
    rw [le_div_iff₀ (by linarith)]
    have : Real.exp y * (1 - c * Lm) ≤ Real.exp y * (1 - y) :=
      mul_le_mul_of_nonneg_left (by linarith) hey.le
    linarith
  have h1 : Real.exp y ≤ 1 + y * Real.exp y := by linarith
  have h2 : y * Real.exp y ≤ c * (1 / (1 - c * Lm)) * ℓ := by
    have hyℓ : y ≤ c * ℓ := mul_le_mul_of_nonneg_left hℓ hc
    have hcℓ : 0 ≤ c * ℓ := le_trans hy0 hyℓ
    calc y * Real.exp y ≤ (c * ℓ) * Real.exp y := mul_le_mul_of_nonneg_right hyℓ hey.le
      _ ≤ (c * ℓ) * (1 / (1 - c * Lm)) := mul_le_mul_of_nonneg_left hμ hcℓ
      _ = c * (1 / (1 - c * Lm)) * ℓ := by ring
  have h3 : Real.exp y ≤ 1 + c * (1 / (1 - c * Lm)) * ℓ := by linarith
  exact mul_le_mul_of_nonneg_left h3 hx.le

/-- **Tight logarithm bounds**: `ln x ≤ j·0.6931471808 + q` whenever `x ≤ 2^j Σ_{i<N} q^i/i!`
(partial sums of the exponential series; `ln 2 < 0.6931471808`). -/
theorem log_le_of_exp_sum (x q : ℝ) (j N : ℕ) (hx : 0 < x) (hq : 0 ≤ q)
    (h : x ≤ 2 ^ j * ∑ i ∈ range N, q ^ i / (i.factorial : ℝ)) :
    Real.log x ≤ (j : ℝ) * 0.6931471808 + q := by
  have hs : ∑ i ∈ range N, q ^ i / (i.factorial : ℝ) ≤ Real.exp q :=
    Real.sum_le_exp_of_nonneg hq N
  have h2 : x ≤ 2 ^ j * Real.exp q := h.trans (by gcongr)
  have h2j : (0:ℝ) < 2 ^ j := by positivity
  have : Real.log x ≤ Real.log (2 ^ j * Real.exp q) := Real.log_le_log hx h2
  rw [Real.log_mul h2j.ne' (Real.exp_pos q).ne', Real.log_exp, Real.log_pow] at this
  have h1 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hj : (0 : ℝ) ≤ j := by positivity
  nlinarith

/-- **Tangent (Bernoulli) bound**: by concavity of `c ↦ (c/u)^z` at `x₀ > 0`,
`(c/u)^z ≤ (x₀/u)^z (1 - z + z c/x₀)` for `c ≥ 0`, `0 ≤ z ≤ 1`. -/
theorem rpow_le_tangent {u x₀ c z : ℝ} (hu : 0 < u) (hx : 0 < x₀) (hc : 0 ≤ c) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) : phiG u z c ≤ phiG u z x₀ * (1 - z + z * (c / x₀)) := by
  unfold phiG
  have e : c / u = (x₀ / u) * (c / x₀) := by field_simp
  rw [e, Real.mul_rpow (div_nonneg hx.le hu.le) (div_nonneg hc hx.le)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (div_nonneg hx.le hu.le) z)
  have hs : -1 ≤ c / x₀ - 1 := by have := div_nonneg hc hx.le; linarith
  have h := rpow_one_add_le_one_add_mul_self hs hz0 hz1
  have e1 : (1 + (c / x₀ - 1)) = c / x₀ := by ring
  rw [e1] at h
  linarith

/-- **Tangent bound for a register's middle edges**: at most `n` nonzero sizes `f i ≥ 0` of total
at most `S > 0` give `Σ φ(f i) ≤ n φ(S/n)`. -/
theorem tangent_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) {u z S : ℝ} {n : ℕ} (hu : 0 < u)
    (hz0 : 0 < z) (hz1 : z ≤ 1) (hn : 0 < n) (hS : 0 < S)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hcard : (s.filter (fun i => f i ≠ 0)).card ≤ n)
    (hsum : ∑ i ∈ s, f i ≤ S) :
    ∑ i ∈ s, phiG u z (f i) ≤ n * phiG u z (S / n) := by
  set x₀ := S / n with hx₀
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hx : 0 < x₀ := div_pos hS hnR
  set t := s.filter (fun i => f i ≠ 0) with ht
  have h1 : ∑ i ∈ s, phiG u z (f i) = ∑ i ∈ t, phiG u z (f i) := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun i => f i ≠ 0)]
    have : ∑ i ∈ s.filter (fun i => ¬ f i ≠ 0), phiG u z (f i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, not_not] at hi
      rw [hi.2]; exact phiG_zero u z hz0.ne'
    rw [this, add_zero]
  have h2 : ∑ i ∈ t, phiG u z (f i) ≤ ∑ i ∈ t, phiG u z x₀ * (1 - z + z * (f i / x₀)) :=
    Finset.sum_le_sum (fun i hi =>
      rpow_le_tangent hu hx (hf i (Finset.mem_filter.1 hi).1) hz0.le hz1)
  have e3 : ∀ i, phiG u z x₀ * (1 - z + z * (f i / x₀))
      = phiG u z x₀ * (1 - z) + (phiG u z x₀ * z / x₀) * f i := fun i => by ring
  have h3 : ∑ i ∈ t, phiG u z x₀ * (1 - z + z * (f i / x₀))
      = (t.card : ℝ) * (phiG u z x₀ * (1 - z)) + (phiG u z x₀ * z / x₀) * ∑ i ∈ t, f i := by
    rw [Finset.sum_congr rfl (fun i _ => e3 i), Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
  have h4 : ∑ i ∈ t, f i ≤ S :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i hi _ => hf i hi)).trans hsum
  have hφ : 0 ≤ phiG u z x₀ := phiG_nonneg u z x₀ hu.le hx.le
  have hc : (t.card : ℝ) ≤ n := by exact_mod_cast hcard
  have hk : 0 ≤ phiG u z x₀ * z / x₀ := by positivity
  have h5 : (phiG u z x₀ * z / x₀) * ∑ i ∈ t, f i ≤ (phiG u z x₀ * z / x₀) * S :=
    mul_le_mul_of_nonneg_left h4 hk
  have e6 : (phiG u z x₀ * z / x₀) * S = n * (phiG u z x₀ * z) := by
    rw [hx₀]; field_simp
  have h7 : (t.card : ℝ) * (phiG u z x₀ * (1 - z)) ≤ n * (phiG u z x₀ * (1 - z)) :=
    mul_le_mul_of_nonneg_right hc (mul_nonneg hφ (by linarith))
  calc ∑ i ∈ s, phiG u z (f i) = ∑ i ∈ t, phiG u z (f i) := h1
    _ ≤ ∑ i ∈ t, phiG u z x₀ * (1 - z + z * (f i / x₀)) := h2
    _ = (t.card : ℝ) * (phiG u z x₀ * (1 - z)) + (phiG u z x₀ * z / x₀) * ∑ i ∈ t, f i := h3
    _ ≤ n * (phiG u z x₀ * (1 - z)) + n * (phiG u z x₀ * z) := by linarith
    _ = n * phiG u z x₀ := by ring

/-- **Crude bound**: `φ(c) ≤ c φ(1)` for natural `c` (`c^z ≤ c`). -/
theorem phiG_le_mul {u z : ℝ} (hu : 0 < u) (hz0 : 0 < z) (hz1 : z ≤ 1) (c : ℕ) :
    phiG u z c ≤ c * phiG u z 1 := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.cast_zero, zero_mul, phiG_zero u z hz0.ne']
  · unfold phiG
    have hc1 : (1:ℝ) ≤ c := by exact_mod_cast hc
    rw [show (c:ℝ) / u = c * (1 / u) by ring, Real.mul_rpow (by positivity) (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (c:ℝ) ^ z ≤ (c:ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 hz1
      _ = c := Real.rpow_one _

/-- `φ` is monotone on `[0, ∞)`. -/
theorem phiG_mono {u z a b : ℝ} (hu : 0 < u) (hz : 0 ≤ z) (ha : 0 ≤ a) (hab : a ≤ b) :
    phiG u z a ≤ phiG u z b :=
  Real.rpow_le_rpow (div_nonneg ha hu.le) (div_le_div_of_nonneg_right hab hu.le) hz

/-! ### The concrete exponent -/

/-- The certified saving `ε = 3.21·10⁻⁶`. -/
noncomputable def epsC : ℝ := 321 / 10 ^ 8
/-- The certified exponent `z = 1 - 3.21·10⁻⁶` (strictly below the stated `1 - 3.2·10⁻⁶`). -/
noncomputable def zC : ℝ := 1 - 321 / 10 ^ 8

lemma zC_eq : zC = 1 - epsC := rfl
lemma zC_pos : 0 < zC := by norm_num [zC]
lemma zC_le_one : zC ≤ 1 := by norm_num [zC]

/-- `φ(c) = (c/u)^z` with `u = 24600`, `z = zC`. -/
noncomputable def phi (c : ℝ) : ℝ := phiG 24600 zC c

lemma phi_zero : phi 0 = 0 := phiG_zero _ _ zC_pos.ne'

lemma phi_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ phi c := phiG_nonneg _ _ _ (by norm_num) hc

/-- `L_u ≥ ln u` (`u = 24600 = 2^14 · 1.5015`). -/
noncomputable def LuC : ℝ := (14 : ℕ) * 0.6931471808 + 406441197 / 1000000000

/-- `μ = 1/(1 - ε L_u)`. -/
noncomputable def muC : ℝ := 1 / (1 - epsC * LuC)

lemma log_u_le : Real.log 24600 ≤ LuC := by
  apply log_le_of_exp_sum _ _ 14 13 (by norm_num) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]
  norm_num

/-- Lemma 5 at `u = 24600`, `z = zC`. -/
lemma phi_le_lem5 (ρ ℓ : ℝ) (h1 : 1 ≤ ρ) (h2 : ρ ≤ 24600) (hℓ : Real.log (24600 / ρ) ≤ ℓ) :
    phi ρ ≤ ρ / 24600 * (1 + epsC * muC * ℓ) := by
  have h := lemma5 ρ 24600 epsC LuC ℓ h1 h2 (by norm_num [epsC]) log_u_le
    (by norm_num [epsC, LuC]) hℓ
  unfold phi phiG
  rw [zC_eq]
  simpa [muC] using h

/-- One rational bound `φ(ρ) ≤ R` from a logarithm certificate. -/
lemma phi_le_of_log (ρ : ℝ) (j : ℕ) (q R : ℝ) (h1 : 1 ≤ ρ) (h2 : ρ ≤ 24600) (hq : 0 ≤ q)
    (hexp : 24600 / ρ ≤ 2 ^ j * ∑ i ∈ range 13, q ^ i / (i.factorial : ℝ))
    (hR : ρ / 24600 * (1 + epsC * muC * ((j : ℝ) * 0.6931471808 + q)) ≤ R) : phi ρ ≤ R :=
  (phi_le_lem5 ρ _ h1 h2 (log_le_of_exp_sum _ q j 13 (by positivity) hq hexp)).trans hR

/-! ### The 22 batch-size classes: `φ(ρ) ≤ Rρ` -/

/-- Rational upper bound for `φ(1)`. -/
noncomputable def R1 : ℝ := 406517258440605669 / 10 ^ 22

lemma phi_R1 : phi 1 ≤ R1 :=
  phi_le_of_log 1 (14 : ℕ) (406441197/1000000000) R1 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R1, epsC, muC, LuC])

/-- Rational upper bound for `φ(19/10)`. -/
noncomputable def R1p9 : ℝ := 772381199657512927 / 10 ^ 22

lemma phi_R1p9 : phi (19/10) ≤ R1p9 :=
  phi_le_of_log (19/10) (13 : ℕ) (457734491/1000000000) R1p9 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R1p9, epsC, muC, LuC])

/-- Rational upper bound for `φ(29/10)`. -/
noncomputable def R2p9 : ℝ := 1178896020325748314 / 10 ^ 22

lemma phi_R2p9 : phi (29/10) ≤ R2p9 :=
  phi_le_of_log (29/10) (13 : ℕ) (871941/25000000) R2p9 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R2p9, epsC, muC, LuC])

/-- Rational upper bound for `φ(4)`. -/
noncomputable def R4 : ℝ := 1626061797747253497 / 10 ^ 22

lemma phi_R4 : phi 4 ≤ R4 :=
  phi_le_of_log 4 (12 : ℕ) (406441197/1000000000) R4 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R4, epsC, muC, LuC])

/-- Rational upper bound for `φ(19/2)`. -/
noncomputable def R9p5 : ℝ := 3861886046498106325 / 10 ^ 22

lemma phi_R9p5 : phi (19/2) ≤ R9p5 :=
  phi_le_of_log (19/2) (11 : ℕ) (11729547/50000000) R9p5 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R9p5, epsC, muC, LuC])

/-- Rational upper bound for `φ(29/2)`. -/
noncomputable def R14p5 : ℝ := 5894449648897447965 / 10 ^ 22

lemma phi_R14p5 : phi (29/2) ≤ R14p5 :=
  phi_le_of_log (29/2) (10 : ℕ) (504881269/1000000000) R14p5 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R14p5, epsC, muC, LuC])

/-- Rational upper bound for `φ(18)`. -/
noncomputable def R18 : ℝ := 7317242761239624188 / 10 ^ 22

lemma phi_R18 : phi 18 ≤ R18 :=
  phi_le_of_log 18 (10 : ℕ) (288658161/1000000000) R18 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R18, epsC, muC, LuC])

/-- Rational upper bound for `φ(19)`. -/
noncomputable def R19 : ℝ := 7723754907460185852 / 10 ^ 22

lemma phi_R19 : phi 19 ≤ R19 :=
  phi_le_of_log 19 (10 : ℕ) (11729547/50000000) R19 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R19, epsC, muC, LuC])

/-- Rational upper bound for `φ(20)`. -/
noncomputable def R20 : ℝ := 8130266984968960738 / 10 ^ 22

lemma phi_R20 : phi 20 ≤ R20 :=
  phi_le_of_log 20 (10 : ℕ) (36659529/200000000) R20 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R20, epsC, muC, LuC])

/-- Rational upper bound for `φ(28)`. -/
noncomputable def R28 : ℝ := 11382361485010945505 / 10 ^ 22

lemma phi_R28 : phi 28 ≤ R28 :=
  phi_le_of_log 28 (9 : ℕ) (539972589/1000000000) R28 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R28, epsC, muC, LuC])

/-- Rational upper bound for `φ(29)`. -/
noncomputable def R29 : ℝ := 11788873067239907660 / 10 ^ 22

lemma phi_R29 : phi 29 ≤ R29 :=
  phi_le_of_log 29 (9 : ℕ) (504881269/1000000000) R29 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R29, epsC, muC, LuC])

/-- Rational upper bound for `φ(30)`. -/
noncomputable def R30 : ℝ := 12195384604462726349 / 10 ^ 22

lemma phi_R30 : phi 30 ≤ R30 :=
  phi_le_of_log 30 (9 : ℕ) (235489859/500000000) R30 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R30, epsC, muC, LuC])

/-- Rational upper bound for `φ(39)`. -/
noncomputable def R39 : ℝ := 15853986633586764854 / 10 ^ 22

lemma phi_R39 : phi 39 ≤ R39 :=
  phi_le_of_log 39 (9 : ℕ) (208615453/1000000000) R39 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R39, epsC, muC, LuC])

/-- Rational upper bound for `φ(40)`. -/
noncomputable def R40 : ℝ := 16260497789862075587 / 10 ^ 22

lemma phi_R40 : phi 40 ≤ R40 :=
  phi_le_of_log 40 (9 : ℕ) (36659529/200000000) R40 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R40, epsC, muC, LuC])

/-- Rational upper bound for `φ(41)`. -/
noncomputable def R41 : ℝ := 16667008913511009636 / 10 ^ 22

lemma phi_R41 : phi 41 ≤ R41 :=
  phi_le_of_log 41 (9 : ℕ) (158605033/1000000000) R41 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R41, epsC, muC, LuC])

/-- Rational upper bound for `φ(551)`. -/
noncomputable def R551 : ℝ := 223986471193129911849 / 10 ^ 22

lemma phi_R551 : phi 551 ≤ R551 :=
  phi_le_of_log 551 (5 : ℕ) (83257753/250000000) R551 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R551, epsC, muC, LuC])

/-- Rational upper bound for `φ(580)`. -/
noncomputable def R580 : ℝ := 235775194013347483685 / 10 ^ 22

lemma phi_R580 : phi 580 ≤ R580 :=
  phi_le_of_log 580 (5 : ℕ) (140868859/500000000) R580 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R580, epsC, muC, LuC])

/-- Rational upper bound for `φ(23960)`. -/
noncomputable def R23960 : ℝ := 9739838222563927949816 / 10 ^ 22

lemma phi_R23960 : phi 23960 ≤ R23960 :=
  phi_le_of_log 23960 (0 : ℕ) (823771/31250000) R23960 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R23960, epsC, muC, LuC])

/-- Rational upper bound for `φ(24000)`. -/
noncomputable def R24000 : ℝ := 9756098334301138544001 / 10 ^ 22

lemma phi_R24000 : phi 24000 ≤ R24000 :=
  phi_le_of_log 24000 (0 : ℕ) (4938523/200000000) R24000 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R24000, epsC, muC, LuC])

/-- Rational upper bound for `φ(24559)`. -/
noncomputable def R24559 : ℝ := 9983333386790553061927 / 10 ^ 22

lemma phi_R24559 : phi 24559 ≤ R24559 :=
  phi_le_of_log 24559 (0 : ℕ) (83403/50000000) R24559 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R24559, epsC, muC, LuC])

/-- Rational upper bound for `φ(24570)`. -/
noncomputable def R24570 : ℝ := 9987804917172595464408 / 10 ^ 22

lemma phi_R24570 : phi 24570 ≤ R24570 :=
  phi_le_of_log 24570 (0 : ℕ) (1220259/1000000000) R24570 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R24570, epsC, muC, LuC])

/-- Rational upper bound for `φ(24599)`. -/
noncomputable def R24599 : ℝ := 9999593497239942053918 / 10 ^ 22

lemma phi_R24599 : phi 24599 ≤ R24599 :=
  phi_le_of_log 24599 (0 : ℕ) (20327/500000000) R24599 (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)
    (by norm_num [R24599, epsC, muC, LuC])

/-! ### The cost classes of the colour network, stage order `(30, 20, 41)`

Stage `j` has `e = ∏_{i<j} h_i`, `F = ∏_{i>j} h_i`; Bot `(e-1)h`, top `eh(F-1)`, bank edges
`(e-1)(h-1)` and `h-1`, side-wire middle edge `h-2`, tangent points `(h-1)/2` (coordinate
X-registers, `≤ 2` middle edges) and `(h-1)/10` (coordinate Y-registers, `≤ 10` middle edges). -/

/-- `h_j`. -/
def hC : Fin 3 → ℕ := ![30, 20, 41]
/-- `v_j = C(h_j, 3)` (bank entries per invocation). -/
def vC : Fin 3 → ℕ := ![4060, 1140, 10660]
/-- Invocations per stage, `N₀ / v_j`. -/
def invC : Fin 3 → ℕ := ![12152400, 43279600, 4628400]
/-- `N₀ = ∏ v_j` (bank keys). -/
def N0C : ℕ := 49338744000

noncomputable def botR : Fin 3 → ℝ := ![0, 580, 24559]
noncomputable def topR : Fin 3 → ℝ := ![24570, 24000, 0]
noncomputable def bk1R : Fin 3 → ℝ := ![0, 551, 23960]
noncomputable def bk2R : Fin 3 → ℝ := ![29, 19, 40]
noncomputable def hR : Fin 3 → ℝ := ![30, 20, 41]
noncomputable def sdR : Fin 3 → ℝ := ![28, 18, 39]
noncomputable def txR : Fin 3 → ℝ := ![29 / 2, 19 / 2, 20]
noncomputable def tyR : Fin 3 → ℝ := ![29 / 10, 19 / 10, 4]

/-- Banks (`2 v_j` per invocation) and centres (`h_j` per invocation). -/
noncomputable def fixedCost (j : Fin 3) : ℝ :=
  2 * vC j * (phi (bk1R j) + phi (bk2R j)) + hC j * (phi (botR j) + 3 * phi (hR j) + phi (topR j))
/-- One side wire: `(e-1)h, 1, h-2, 1, eh(F-1)`. -/
noncomputable def sideCost (j : Fin 3) : ℝ :=
  phi (botR j) + 2 * phi 1 + phi (sdR j) + phi (topR j)
/-- A register with `≤ 2` middle edges (tangent bound) and its structural unit edge. -/
noncomputable def xsCost (j : Fin 3) : ℝ :=
  phi (botR j) + phi 1 + 2 * phi (txR j) + phi (topR j)
/-- A register with `≤ 10` middle edges (tangent bound) and its structural unit edge. -/
noncomputable def ysCost (j : Fin 3) : ℝ :=
  phi (botR j) + phi 1 + 10 * phi (tyR j) + phi (topR j)
/-- Any register (crude bound: `h - 1` middle units and the structural unit edge). -/
noncomputable def longCost (j : Fin 3) : ℝ :=
  phi (botR j) + hC j * phi 1 + phi (topR j)
/-- One padding role: `1, u - 1`. -/
noncomputable def padCost : ℝ := phi 1 + phi 24599

/-- Per-factor counts of one invocation's auxiliary roles: side wires, registers with `≤ 2`
middle edges (`xs`, X) and the other X-registers (`xl`), registers with `≤ 10` middle edges (`ys`,
Y) and the other Y-registers (`yl`). -/
structure Counts where
  side : ℕ
  xs : ℕ
  xl : ℕ
  ys : ℕ
  yl : ℕ

/-- Cost-class bound for `Φ(E_inv,j)`. -/
noncomputable def invCost (j : Fin 3) (c : Counts) : ℝ :=
  fixedCost j + c.side * sideCost j + c.xs * xsCost j + c.ys * ysCost j
    + (c.xl + c.yl) * longCost j

/-- Cost-class bound for `Φ(E_total) = Σ_j inv_j Φ(E_inv,j) + P (φ 1 + φ(u-1))`. -/
noncomputable def totalCost (c : Fin 3 → Counts) (P : ℕ) : ℝ :=
  ∑ j, (invC j : ℝ) * invCost j (c j) + P * padCost

/-- Number of non-padding roles. -/
def wnet (c : Fin 3 → Counts) : ℕ :=
  2 * N0C + ∑ j, invC j * (hC j + (c j).side + (c j).xs + (c j).xl + (c j).ys + (c j).yl)

/-! ### Rational costs -/

noncomputable def fixedR : Fin 3 → ℝ :=
  ![2 * 4060 * R29 + 30 * (3 * R30 + R24570),
    2 * 1140 * (R551 + R19) + 20 * (R580 + 3 * R20 + R24000),
    2 * 10660 * (R23960 + R40) + 41 * (R24559 + 3 * R41)]
noncomputable def sideR : Fin 3 → ℝ :=
  ![2 * R1 + R28 + R24570, R580 + 2 * R1 + R18 + R24000, R24559 + 2 * R1 + R39]
noncomputable def xsR : Fin 3 → ℝ :=
  ![R1 + 2 * R14p5 + R24570, R580 + R1 + 2 * R9p5 + R24000, R24559 + R1 + 2 * R20]
noncomputable def ysR : Fin 3 → ℝ :=
  ![R1 + 10 * R2p9 + R24570, R580 + R1 + 10 * R1p9 + R24000, R24559 + R1 + 10 * R4]
noncomputable def longR : Fin 3 → ℝ :=
  ![30 * R1 + R24570, R580 + 20 * R1 + R24000, R24559 + 41 * R1]
noncomputable def padR : ℝ := R1 + R24599

lemma fixed_le (j : Fin 3) : fixedCost j ≤ fixedR j := by
  have := phi_zero
  fin_cases j <;>
    simp only [fixedCost, fixedR, vC, hC, bk1R, bk2R, botR, hR, topR, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Nat.cast_ofNat] <;>
    linarith [phi_R29, phi_R30, phi_R24570, phi_R551, phi_R19, phi_R580, phi_R20, phi_R24000,
      phi_R23960, phi_R40, phi_R24559, phi_R41]

lemma side_le (j : Fin 3) : sideCost j ≤ sideR j := by
  have := phi_zero
  fin_cases j <;>
    simp only [sideCost, sideR, botR, sdR, topR, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    linarith [phi_R1, phi_R28, phi_R24570, phi_R580, phi_R18, phi_R24000, phi_R24559, phi_R39]

lemma xs_le (j : Fin 3) : xsCost j ≤ xsR j := by
  have := phi_zero
  fin_cases j <;>
    simp only [xsCost, xsR, botR, txR, topR, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    linarith [phi_R1, phi_R14p5, phi_R24570, phi_R580, phi_R9p5, phi_R24000, phi_R24559, phi_R20]

lemma ys_le (j : Fin 3) : ysCost j ≤ ysR j := by
  have := phi_zero
  fin_cases j <;>
    simp only [ysCost, ysR, botR, tyR, topR, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    linarith [phi_R1, phi_R2p9, phi_R24570, phi_R580, phi_R1p9, phi_R24000, phi_R24559, phi_R4]

lemma long_le (j : Fin 3) : longCost j ≤ longR j := by
  have := phi_zero
  fin_cases j <;>
    simp only [longCost, longR, botR, hC, topR, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Nat.cast_ofNat] <;>
    linarith [phi_R1, phi_R24570, phi_R580, phi_R24000, phi_R24559]

lemma pad_le : padCost ≤ padR := by
  have := phi_R1; have := phi_R24599
  unfold padCost padR; linarith

/-- Each auxiliary role costs more than the padding role it replaces (monotonicity in the counts),
and the tangent classes are cheaper than the crude class. -/
lemma gaps (j : Fin 3) : padR ≤ sideR j ∧ padR ≤ xsR j ∧ padR ≤ ysR j ∧ xsR j ≤ longR j ∧
    ysR j ≤ longR j := by
  fin_cases j <;>
    simp only [padR, sideR, xsR, ysR, longR, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    norm_num [R1, R1p9, R2p9, R4, R9p5, R14p5, R18, R20, R28, R39, R580, R24000, R24559, R24570,
      R24599]

/-! ### The explicit bound as a function of the per-factor counts -/

/-- Contribution of one invocation of stage `j`, with the padding it displaces subtracted;
`cX`, `cY`: coordinate X- and Y-registers, `sun`: sunflower registers, `sd`: side wires. -/
noncomputable def boundTerm (j : Fin 3) (cX cY sun sd : ℕ) : ℝ :=
  fixedR j - hC j * padR + sd * (sideR j - padR) + cX * (xsR j - padR) + cY * (ysR j - padR)
    + sun * (longR j - padR)

/-- **The explicit exponent bound** as a function of the per-factor counts (coordinate X-registers,
coordinate Y-registers, sunflower registers, side wires). -/
noncomputable def bound (cX cY sun sd : Fin 3 → ℕ) : ℝ :=
  (2 ^ 43 - 2 * N0C) * padR + ∑ j, (invC j : ℝ) * boundTerm j (cX j) (cY j) (sun j) (sd j)

lemma boundTerm_mono (j : Fin 3) {cX cY sun sd cX' cY' sun' sd' : ℕ} (h1 : cX ≤ cX')
    (h2 : cY ≤ cY') (h3 : sun ≤ sun') (h4 : sd ≤ sd') :
    boundTerm j cX cY sun sd ≤ boundTerm j cX' cY' sun' sd' := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := gaps j
  unfold boundTerm
  have k1 : (sd : ℝ) * (sideR j - padR) ≤ sd' * (sideR j - padR) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h4) (by linarith)
  have k2 : (cX : ℝ) * (xsR j - padR) ≤ cX' * (xsR j - padR) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h1) (by linarith)
  have k3 : (cY : ℝ) * (ysR j - padR) ≤ cY' * (ysR j - padR) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (by linarith)
  have k4 : (sun : ℝ) * (longR j - padR) ≤ sun' * (longR j - padR) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h3) (by linarith)
  linarith

/-- `bound` is monotone in each count. -/
theorem bound_mono {cX cY sun sd cX' cY' sun' sd' : Fin 3 → ℕ} (h1 : ∀ j, cX j ≤ cX' j)
    (h2 : ∀ j, cY j ≤ cY' j) (h3 : ∀ j, sun j ≤ sun' j) (h4 : ∀ j, sd j ≤ sd' j) :
    bound cX cY sun sd ≤ bound cX' cY' sun' sd' := by
  unfold bound
  gcongr with j
  exact boundTerm_mono j (h1 j) (h2 j) (h3 j) (h4 j)

/-- Design counts (FORMALIZATION_CNET.md §5.3), stage order `30/20/41`. -/
def coordX : Fin 3 → ℕ := ![96881, 18090, 304414]
def coordY : Fin 3 → ℕ := ![94429, 17552, 330907]
def sunC : Fin 3 → ℕ := ![24360, 6840, 63960]
def sideC : Fin 3 → ℕ := ![14763, 3076, 79147]

/-- **Exponent inequality** (exact rational arithmetic) at the design counts. -/
theorem exponent_ineq : bound coordX coordY sunC sideC < 2 ^ 43 := by
  simp only [bound, boundTerm, Fin.sum_univ_three, invC, coordX, coordY, sunC, sideC, hC, fixedR,
    sideR, xsR, ysR, longR, padR, N0C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Nat.cast_ofNat]
  norm_num [R1, R1p9, R2p9, R4, R9p5, R14p5, R18, R19, R20, R28, R29, R30, R39, R40, R41, R551,
    R580, R23960, R24000, R24559, R24570, R24599]

/-! ### From the cost classes to the bound -/

/-- One invocation, against the padding it displaces. -/
lemma inv_le (j : Fin 3) (c : Counts) (cX cY sX sY sd : ℕ) (hsd : c.side ≤ sd)
    (hx : c.xs + c.xl ≤ cX + sX) (hxl : c.xl ≤ sX) (hy : c.ys + c.yl ≤ cY + sY)
    (hyl : c.yl ≤ sY) :
    invCost j c - (hC j + c.side + c.xs + c.xl + c.ys + c.yl : ℕ) * padR
      ≤ boundTerm j cX cY (sX + sY) sd := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := gaps j
  have f1 := fixed_le j
  have f2 := side_le j
  have f3 := xs_le j
  have f4 := ys_le j
  have f5 := long_le j
  have hsdR : (c.side : ℝ) ≤ sd := by exact_mod_cast hsd
  have hxR : (c.xs : ℝ) + c.xl ≤ cX + sX := by exact_mod_cast hx
  have hxlR : (c.xl : ℝ) ≤ sX := by exact_mod_cast hxl
  have hyR : (c.ys : ℝ) + c.yl ≤ cY + sY := by exact_mod_cast hy
  have hylR : (c.yl : ℝ) ≤ sY := by exact_mod_cast hyl
  have n1 : (0:ℝ) ≤ c.side := Nat.cast_nonneg _
  have n2 : (0:ℝ) ≤ c.xs := Nat.cast_nonneg _
  have n3 : (0:ℝ) ≤ c.xl := Nat.cast_nonneg _
  have n4 : (0:ℝ) ≤ c.ys := Nat.cast_nonneg _
  have n5 : (0:ℝ) ≤ c.yl := Nat.cast_nonneg _
  -- real costs below rational costs
  have a2 : (c.side : ℝ) * sideCost j ≤ c.side * sideR j := mul_le_mul_of_nonneg_left f2 n1
  have a3 : (c.xs : ℝ) * xsCost j ≤ c.xs * xsR j := mul_le_mul_of_nonneg_left f3 n2
  have a4 : (c.ys : ℝ) * ysCost j ≤ c.ys * ysR j := mul_le_mul_of_nonneg_left f4 n4
  have a5 : ((c.xl : ℝ) + c.yl) * longCost j ≤ (c.xl + c.yl) * longR j :=
    mul_le_mul_of_nonneg_left f5 (by linarith)
  -- monotonicity in the counts
  have b1 : (c.side : ℝ) * (sideR j - padR) ≤ sd * (sideR j - padR) :=
    mul_le_mul_of_nonneg_right hsdR (by linarith)
  have b2 : ((c.xs : ℝ) + c.xl) * (xsR j - padR) ≤ (cX + sX) * (xsR j - padR) :=
    mul_le_mul_of_nonneg_right hxR (by linarith)
  have b3 : (c.xl : ℝ) * (longR j - xsR j) ≤ sX * (longR j - xsR j) :=
    mul_le_mul_of_nonneg_right hxlR (by linarith)
  have b4 : ((c.ys : ℝ) + c.yl) * (ysR j - padR) ≤ (cY + sY) * (ysR j - padR) :=
    mul_le_mul_of_nonneg_right hyR (by linarith)
  have b5 : (c.yl : ℝ) * (longR j - ysR j) ≤ sY * (longR j - ysR j) :=
    mul_le_mul_of_nonneg_right hylR (by linarith)
  unfold invCost boundTerm
  push_cast
  linarith

/-- The cost-class total is at most `bound`, for counts dominated by `(cX, cY, sX + sY, sd)`
(at most `sX j` X-registers and `sY j` Y-registers outside the tangent classes), when the padding
fills the `2^43` roles. -/
theorem totalCost_le_bound (c : Fin 3 → Counts) (P : ℕ) (hP : P + wnet c = 2 ^ 43)
    (cX cY sX sY sd : Fin 3 → ℕ) (hsd : ∀ j, (c j).side ≤ sd j)
    (hx : ∀ j, (c j).xs + (c j).xl ≤ cX j + sX j) (hxl : ∀ j, (c j).xl ≤ sX j)
    (hy : ∀ j, (c j).ys + (c j).yl ≤ cY j + sY j) (hyl : ∀ j, (c j).yl ≤ sY j) :
    totalCost c P ≤ bound cX cY (sX + sY) sd := by
  have hPR : (P : ℝ) = 2 ^ 43 - wnet c := by
    have : ((P + wnet c : ℕ) : ℝ) = ((2 ^ 43 : ℕ) : ℝ) := by rw [hP]
    push_cast at this; linarith
  have hpad : (P : ℝ) * padCost ≤ P * padR := mul_le_mul_of_nonneg_left pad_le (Nat.cast_nonneg _)
  have key : ∀ j, (invC j : ℝ) * invCost j (c j)
      ≤ invC j * ((hC j + (c j).side + (c j).xs + (c j).xl + (c j).ys + (c j).yl : ℕ) * padR)
        + invC j * boundTerm j (cX j) (cY j) (sX j + sY j) (sd j) := fun j => by
    have := inv_le j (c j) (cX j) (cY j) (sX j) (sY j) (sd j) (hsd j) (hx j) (hxl j) (hy j) (hyl j)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hw : (wnet c : ℝ) = 2 * N0C + ∑ j, (invC j : ℝ) *
      ((hC j + (c j).side + (c j).xs + (c j).xl + (c j).ys + (c j).yl : ℕ) : ℝ) := by
    unfold wnet; push_cast; ring
  unfold totalCost bound
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 3))) => key j)
  rw [Finset.sum_add_distrib] at hs
  simp only [Pi.add_apply]
  rw [hPR] at hpad
  have e : ∑ j, (invC j : ℝ) *
      (((hC j + (c j).side + (c j).xs + (c j).xl + (c j).ys + (c j).yl : ℕ) : ℝ) * padR)
      = (∑ j, (invC j : ℝ) *
      ((hC j + (c j).side + (c j).xs + (c j).xl + (c j).ys + (c j).yl : ℕ) : ℝ)) * padR := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
  rw [e] at hs
  rw [hPR, hw]
  rw [hw] at hpad
  linarith

/-- **The exponent statement in cost-class form**: for any per-invocation counts dominated by the
design counts (`sX + sY ≤ sun`), with `P` padding roles filling `2^43` roles,
`Σ_j inv_j·(cost of one invocation) + P (φ 1 + φ(u-1)) < 2^43`. -/
theorem totalCost_lt (c : Fin 3 → Counts) (P : ℕ) (hP : P + wnet c = 2 ^ 43)
    (sX sY : Fin 3 → ℕ) (hsun : ∀ j, sX j + sY j ≤ sunC j) (hsd : ∀ j, (c j).side ≤ sideC j)
    (hx : ∀ j, (c j).xs + (c j).xl ≤ coordX j + sX j) (hxl : ∀ j, (c j).xl ≤ sX j)
    (hy : ∀ j, (c j).ys + (c j).yl ≤ coordY j + sY j) (hyl : ∀ j, (c j).yl ≤ sY j) :
    totalCost c P < 2 ^ 43 :=
  ((totalCost_le_bound c P hP coordX coordY sX sY sideC hsd hx hxl hy hyl).trans
    (bound_mono (fun _ => le_rfl) (fun _ => le_rfl) hsun (fun _ => le_rfl))).trans_lt
    exponent_ineq

end Expo
end PowerSaving.Colour
end OAI
