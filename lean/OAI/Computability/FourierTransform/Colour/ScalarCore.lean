import Mathlib

/-!
# Colour network, part 6: the scalar identity of Theorem C as a ring identity (new)

The forward invocation of the colour-register network (results/C_sidewires.md §1, steps 1–12) is a
product of twelve gates `1 ± z` with

* `g : X → centres`, `r : centres → Y` (Lemma A.2),
* `w : X → X-registers ⊕ side wires` (Π + V), `u : Y-registers ⊕ side wires → Y` (Ξ + J),
* `k : X-registers → Y-registers` (the transfer matrix `K̃`; step 5 is `∏_ℓ (1 + k_ℓ)` with `Σ k_ℓ = k`).

All products of these maps vanish except along composable arrows; `schedule_eq` shows that under
exactly those relations the twelve gates multiply to `1 + r g + u w + u k w`, whose `X → Y` block is
`RG + JV + ΞK̃Π` (Lemma C.4). The proof is the chronological computation of the partial products.
`levels_prod` handles the per-level gates of step 5, and `mul_eq_zero_of_supp` derives the
vanishing relations for block-supported matrices.
-/

namespace OAI
namespace PowerSaving.Colour
open Finset Matrix

section Ring
variable {R : Type*} [Ring R]

/-- Twelve gates of the forward invocation (chronologically right to left). -/
theorem schedule_eq (g r u w k : R)
    (gr : g * r = 0) (rr : r * r = 0) (ur : u * r = 0) (wr : w * r = 0) (kr : k * r = 0)
    (gu : g * u = 0) (ru : r * u = 0) (uu : u * u = 0) (wu : w * u = 0) (ku : k * u = 0)
    (ug : u * g = 0) (kg : k * g = 0) (wg : w * g = 0) (gg : g * g = 0)
    (gw : g * w = 0) (rw0 : r * w = 0) (ww : w * w = 0)
    (gk : g * k = 0) (rk : r * k = 0) (wk : w * k = 0) (kk : k * k = 0) :
    (1 + k) * ((1 - w) * ((1 - k) * ((1 - g) * ((1 + u) * ((1 + r) * ((1 + g) * ((1 + k) *
      ((1 + w) * ((1 - k) * ((1 - u) * (1 - r)))))))))))
      = 1 + r * g + u * w + u * k * w := by
  have e2 : (1 - u) * (1 - r) = 1 - r - u := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, ur]; abel
  have e3 : (1 - k) * (1 - r - u) = 1 - r - u - k := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, kr, ku]; abel
  have e4 : (1 + w) * (1 - r - u - k) = 1 - r - u - k + w := by
    simp only [add_mul, mul_sub, one_mul, mul_one, wr, wu, wk]; abel
  have e5 : (1 + k) * (1 - r - u - k + w) = 1 - r - u + w + k * w := by
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, kr, ku, kk]; abel
  have e6 : (1 + g) * (1 - r - u + w + k * w) = 1 - r - u + w + k * w + g := by
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, gr, gu, gw, ← mul_assoc, gk,
      zero_mul]; abel
  have e7 : (1 + r) * (1 - r - u + w + k * w + g) = 1 - u + w + k * w + g + r * g := by
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, rr, ru, rw0, ← mul_assoc, rk,
      zero_mul]; abel
  have e8 : (1 + u) * (1 - u + w + k * w + g + r * g)
      = 1 + w + k * w + g + r * g + u * w + u * k * w := by
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, uu, ug, ← mul_assoc, ur,
      zero_mul]; abel
  have e9 : (1 - g) * (1 + w + k * w + g + r * g + u * w + u * k * w)
      = 1 + w + k * w + r * g + u * w + u * k * w := by
    simp only [sub_mul, mul_add, one_mul, mul_one, gw, gg, ← mul_assoc, gk, gr, gu,
      zero_mul]; abel
  have e10 : (1 - k) * (1 + w + k * w + r * g + u * w + u * k * w)
      = 1 + w + r * g + u * w + u * k * w - k := by
    simp only [sub_mul, mul_add, one_mul, mul_one, ← mul_assoc, kk, kr, ku, zero_mul]; abel
  have e11 : (1 - w) * (1 + w + r * g + u * w + u * k * w - k)
      = 1 + r * g + u * w + u * k * w - k := by
    simp only [sub_mul, mul_add, mul_sub, one_mul, mul_one, ww, wk, ← mul_assoc, wr, wu,
      zero_mul]; abel
  have e12 : (1 + k) * (1 + r * g + u * w + u * k * w - k) = 1 + r * g + u * w + u * k * w := by
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, kk, ← mul_assoc, kr, ku,
      zero_mul]; abel
  rw [e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]

/-- Step 5 of the schedule: per-level gates with pairwise vanishing products. -/
theorem levels_prod (L : List R) (hL : ∀ a ∈ L, ∀ b ∈ L, a * b = 0) :
    (L.map (fun a => 1 + a)).prod = 1 + L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hz : ∀ M : List R, (∀ b ∈ M, a * b = 0) → a * M.sum = 0 := by
      intro M
      induction M with
      | nil => intro _; simp
      | cons c M ihM =>
        intro hM
        rw [List.sum_cons, mul_add, hM c (by simp), ihM (fun b hb => hM b (by simp [hb])),
          add_zero]
    rw [List.map_cons, List.prod_cons, ih (fun x hx y hy => hL x (by simp [hx]) y (by simp [hy])),
      List.sum_cons, add_mul, one_mul, mul_add, mul_one,
      hz L (fun b hb => hL a (by simp) b (by simp [hb]))]
    abel

/-- Inverses of the square-zero gates. -/
theorem one_add_inv {z : R} (hz : z * z = 0) : (1 + z) * (1 - z) = 1 := by
  simp [mul_sub, add_mul, hz]

theorem one_sub_inv {z : R} (hz : z * z = 0) : (1 - z) * (1 + z) = 1 := by
  simp [mul_add, sub_mul, hz]

end Ring

section Supp
variable {ι : Type*} [Fintype ι] {S : Type*} [Semiring S]

/-- Block support: if the columns used by `M` are never rows used by `N`, then `M * N = 0`. -/
theorem mul_eq_zero_of_supp (M N : Matrix ι ι S) (P : ι → Prop)
    (hM : ∀ i j, M i j ≠ 0 → P j) (hN : ∀ j k, N j k ≠ 0 → ¬ P j) : M * N = 0 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply sum_eq_zero
  intro j _
  by_cases h1 : M i j = 0
  · simp [h1]
  by_cases h2 : N j k = 0
  · simp [h2]
  exact absurd (hM i j h1) (hN j k h2)

end Supp

end PowerSaving.Colour
end OAI
