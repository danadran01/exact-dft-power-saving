import OAI.Computability.FourierTransform.Grouped.GNetCert
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exponent inequality for the grouped certificate of OpenAI's network (new)

For `z = 1 - epsG` with `epsG = 1.4657·10⁻⁸`,
`∑_{c < 32^3} NOAI c · (c/32^3)^z < 2^50`,
i.e. the grouped recursion for OpenAI's network has exponent at most `1 - 1.4657·10⁻⁸`
(OpenAI's ungrouped bound: `1 - 2·10⁻¹¹`).

Method (Lemma 5 of `proofs/PROOFS.md`, ported from `lean/DFTDelta/All.lean`, Part 3):
`(c/u)^{1-ε} ≤ (c/u)·(1 + ε μ ℓ)` with `μ = 1/(1 - ε L_u)`, `L_u ≥ ln u`, `ℓ ≥ ln(u/c)`,
`ln 2 < 0.6931471808` and `ln y ≤ y - 1`; then exact rational arithmetic.
-/

namespace OAI
namespace PowerSaving.Cluster
open Finset

/-! ### Lemma 5 (ported from `DFTDelta/All.lean`) -/

lemma log_le_bound (x : ℝ) (j : ℕ) (hx : (2 : ℝ) ^ j ≤ x) :
    Real.log x ≤ (j : ℝ) * 0.6931471808 + (x / 2 ^ j - 1) := by
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hxpos : 0 < x := lt_of_lt_of_le h2j hx
  have hsplit : Real.log x = Real.log ((2 : ℝ) ^ j) + Real.log (x / 2 ^ j) := by
    rw [← Real.log_mul (ne_of_gt h2j) (ne_of_gt (div_pos hxpos h2j))]
    congr 1; field_simp
  rw [hsplit, Real.log_pow]
  have h1 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h2 : Real.log (x / 2 ^ j) ≤ x / 2 ^ j - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hxpos h2j)
  have hj : (0 : ℝ) ≤ j := by positivity
  have h3 : (j : ℝ) * Real.log 2 ≤ (j : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left h1.le hj
  linarith

lemma term_le (ρ M c Lm ℓ : ℝ) (hρ1 : 1 ≤ ρ) (hρM : ρ ≤ M) (hc : 0 ≤ c)
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

/-! ### From the histogram to a sum over the edge list -/

lemma NOAI_cons (e : ℕ × ℕ) (L : List (ℕ × ℕ)) (c : ℕ) :
    ((((e :: L).filter (·.1 = c)).map (·.2)).sum) =
      (if e.1 = c then e.2 else 0) + (((L.filter (·.1 = c)).map (·.2)).sum) := by
  by_cases h : e.1 = c <;> simp [h]

lemma sum_hist (L : List (ℕ × ℕ)) (M : ℕ) (w : ℕ → ℝ) (hL : ∀ e ∈ L, e.1 < M) :
    ∑ c : Fin M, ((((L.filter (·.1 = (c:ℕ))).map (·.2)).sum : ℕ) : ℝ) * w c =
      (L.map (fun e => (e.2 : ℝ) * w e.1)).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    rw [List.map_cons, List.sum_cons, ← ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he'))]
    simp only [NOAI_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    have ha : e.1 < M := hL e List.mem_cons_self
    rw [Fintype.sum_eq_single ⟨e.1, ha⟩]
    · simp
    · intro c hc
      have : ¬ e.1 = (c : ℕ) := fun h => hc (Fin.ext h.symm)
      simp [this]

/-! ### The certificate -/

/-- The certified exponent saving `ε = 1.4657·10⁻⁸`. -/
noncomputable def epsG : ℝ := 14657 / 10^12

/-- `j` with `2^j ≤ 32^3 / c < 2^{j+1}` for each size of `edgeList`. -/
def jList : List ℕ := [15, 10, 10, 10, 5, 5, 5, 5, 0, 0, 0, 0, 0]

def rateList : List ((ℕ × ℕ) × ℕ) := edgeList.zip jList

lemma edge_rate : edgeList = rateList.map Prod.fst := by decide +kernel

lemma rate_ok : ∀ e ∈ rateList, 1 ≤ e.1.1 ∧ e.1.1 ≤ mcol ∧ 2 ^ e.2 * e.1.1 ≤ mcol := by
  decide +kernel

noncomputable def ellR (e : (ℕ × ℕ) × ℕ) : ℝ :=
  (e.2 : ℝ) * 0.6931471808 + ((32768 : ℝ) / e.1.1 / 2 ^ e.2 - 1)

noncomputable def LmOAI : ℝ := (15 : ℕ) * 0.6931471808 + ((32768 : ℝ) / 2 ^ 15 - 1)

/-- The exact rational check (Lemma 5 applied term by term). -/
lemma rate_bound :
    (rateList.map (fun e => (e.1.2 : ℝ) * (((e.1.1 : ℝ) / 32768) *
      (1 + epsG * (1 / (1 - epsG * LmOAI)) * ellR e)))).sum < (2:ℝ)^50 := by
  simp only [rateList, edgeList, jList, List.zip_cons_cons, List.zip_nil_right, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, ellR, LmOAI, epsG, nbN, nnN, tower, nrRoles]
  norm_num

lemma mcol_real : ((mcol : ℕ) : ℝ) = 32768 := by norm_num [mcol]

/-- **Exponent inequality** for the grouped certificate of OpenAI's network. -/
theorem noai_rate :
    ∑ c : Fin mcol, (NOAI c : ℝ) * ((c:ℝ)/(mcol:ℝ))^(1 - epsG) < (2:ℝ)^50 := by
  have hsum := sum_hist edgeList mcol (fun c => ((c:ℝ)/(mcol:ℝ))^(1 - epsG))
    (fun e he => (edge_supp e he).2.2)
  beta_reduce at hsum
  unfold NOAI
  rw [hsum, edge_rate, List.map_map]
  refine lt_of_le_of_lt (List.sum_le_sum ?_) rate_bound
  intro e he
  obtain ⟨h1, h2, h3⟩ := rate_ok e he
  have h2' : e.1.1 ≤ 32768 := h2
  have h3' : 2 ^ e.2 * e.1.1 ≤ 32768 := h3
  simp only [Function.comp_apply]
  rw [mcol_real]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hρ1 : (1 : ℝ) ≤ e.1.1 := Nat.one_le_cast.mpr h1
  have hρm : (e.1.1 : ℝ) ≤ 32768 := by exact_mod_cast h2'
  have hρpos : (0 : ℝ) < e.1.1 := by linarith
  have hm : (2 : ℝ) ^ 15 ≤ (32768 : ℝ) := by norm_num
  apply term_le _ _ _ _ _ hρ1 hρm (by norm_num [epsG]) (log_le_bound _ 15 hm)
    (by norm_num [epsG, LmOAI])
  apply log_le_bound
  rw [le_div_iff₀ hρpos]
  exact_mod_cast h3'

end PowerSaving.Cluster
end OAI
