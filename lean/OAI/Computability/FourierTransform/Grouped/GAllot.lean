import OAI.Computability.FourierTransform.RecursionBounds

/-!
# Grouped work recursion (new; not part of OpenAI's development)

OpenAI's `allot u a D k = 2^k + D·2^{k-k/u-a}·allot(k/u)` charges one recursive call of size
`k/u` per directional move. In the grouped recursion, a batch of `c` directions of one edge is ONE
call of size `c·(k/u)`, and there are `2^{k-c(k/u)-a}` such calls (each call handles `2^a` roles).
`N c` is the number of batches of size `c` in the certificate word (`c < u`).
-/

namespace OAI
namespace PowerSaving.RAM

/-- Number of calls of size `c·(k/u)` for one batch of size `c`. -/
def gbatches (u a c k : ℕ) := 2^(k-c*(k/u)-a)

lemma gdown_lt {u a k c : ℕ} (hk : threshold u a ≤ k ∧ 0 < k/u) (hc : c < u) :
    c*(k/u) < k := by
  have h1 : c*(k/u) < u*(k/u) := Nat.mul_lt_mul_of_pos_right hc hk.2
  have h2 : u*(k/u) ≤ k := Nat.mul_div_le k u
  omega

def gallot (u a : ℕ) (N : ℕ → ℕ) (k : ℕ) : ℕ :=
  if h : threshold u a ≤ k ∧ 0 < k/u then
    2^k + ∑ c : Fin u, N c * gbatches u a c k * gallot u a N (c*(k/u))
  else 2^k
termination_by k
decreasing_by exact gdown_lt h c.isLt

lemma gallot_eq (u a : ℕ) (N : ℕ → ℕ) (k : ℕ) :
    gallot u a N k = if threshold u a ≤ k ∧ 0 < k/u then
      2^k + ∑ c : Fin u, N c * gbatches u a c k * gallot u a N (c*(k/u))
    else 2^k := by
  rw [gallot]; simp only [dite_eq_ite]

lemma grounds_eq (u a c k : ℕ) (hu : 1 ≤ u) (hk : threshold u a ≤ k) (hc : c < u) :
    gbatches u a c k * (2^a*2^(c*(k/u))) = 2^k := by
  have hh : a+1 ≤ k/u := (Nat.le_div_iff_mul_le (by omega)).2 (by
    simpa [threshold, mul_comm] using hk)
  have h1 : c*(k/u) + k/u ≤ u*(k/u) := by
    have : (c+1)*(k/u) ≤ u*(k/u) := Nat.mul_le_mul_right _ (by omega)
    simpa [add_mul] using this
  have h2 : u*(k/u) ≤ k := Nat.mul_div_le k u
  unfold gbatches
  rw [← pow_add, ← pow_add]
  congr 1; omega

end PowerSaving.RAM
end OAI
