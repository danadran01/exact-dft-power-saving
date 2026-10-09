import OAI.Computability.FourierTransform.Colour.Triples

/-!
# Colour network, part 3: the `h` centres of Lemma A.2 (new)

For triples (k = 3) the centre `c_*` of the paper is unnecessary: with `h` centres `c_i`,
`(G x)_i = ½ (Σ_{T ∋ i} x_T − ⅓ Σ_T x_T)` and `(R c)_S = Σ_{i ∈ S} c_i` give
`(RG)_{ST} = (|S∩T| − 1)/2` (`rg_entry`). With the transfer coefficient
`kval T S = −(|S∩T|−1)/2` (= ±½ on orthogonal pairs) one has
`(RG)_{ST} + [T ≠ S ∧ T ⊥ S]·kval T S = δ_{ST}` (`rg_add_k`): this is where the exact cover (D5)
of a register design enters the scalar identity.
-/

namespace OAI
namespace PowerSaving.Colour
open Finset Matrix

variable {h : ℕ}

/-- `G`: from the triples to the centres. -/
def glocal (h : ℕ) : Matrix (Fin h) (Trip h) ℚ := fun i T =>
  ((if i ∈ T.val then 1 else 0) - 1/3) / 2

/-- `R`: from the centres to the triples. -/
def rlocal (h : ℕ) : Matrix (Trip h) (Fin h) ℚ := fun S i => if i ∈ S.val then 1 else 0

lemma ind_mul_ind (S T : Trip h) :
    ∑ i : Fin h, ((if i ∈ S.val then (1:ℚ) else 0) * (if i ∈ T.val then 1 else 0))
      = (meet S T : ℚ) := by
  calc _ = ∑ i : Fin h, (if i ∈ S.val ∩ T.val then (1:ℚ) else 0) := by
          apply sum_congr rfl; intro i _
          by_cases hs : i ∈ S.val <;> by_cases ht : i ∈ T.val <;> simp [hs, ht]
    _ = _ := by rw [sum_ite_mem, univ_inter, sum_const, nsmul_one]; rfl

theorem rg_entry (S T : Trip h) :
    (rlocal h * glocal h) S T = ((meet S T : ℚ) - 1) / 2 := by
  rw [Matrix.mul_apply]
  simp only [rlocal, glocal]
  have e : ∀ i : Fin h, (if i ∈ S.val then (1:ℚ) else 0) *
      (((if i ∈ T.val then 1 else 0) - 1/3) / 2)
      = ((if i ∈ S.val then (1:ℚ) else 0) * (if i ∈ T.val then 1 else 0)) / 2
        - (if i ∈ S.val then (1:ℚ) else 0) / 6 := by intro i; ring
  simp_rw [e]
  rw [sum_sub_distrib, ← sum_div, ← sum_div, ind_mul_ind]
  have hS : ∑ i : Fin h, (if i ∈ S.val then (1:ℚ) else 0) = 3 := by
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_one, trip_card]; norm_num
  rw [hS]; ring

/-- Transfer coefficient `K_{ST}` from `x_T` into `y_S` (symmetric). -/
def kval (T S : Trip h) : ℚ := -(((meet T S : ℚ) - 1) / 2)

lemma kval_comm (T S : Trip h) : kval T S = kval S T := by simp [kval, meet_comm]

theorem rg_diag (T : Trip h) : (rlocal h * glocal h) T T = 1 := by
  rw [rg_entry, meet_self]; norm_num

/-- The scalar identity behind every invocation: centres plus one transfer (or side wire) per
ordered orthogonal pair give the identity. -/
theorem rg_add_k (S T : Trip h) :
    (rlocal h * glocal h) S T + (if T ≠ S ∧ neighbor T S then kval T S else 0)
      = if S = T then 1 else 0 := by
  rw [rg_entry]
  by_cases e : S = T
  · subst e; simp [meet_self]; norm_num
  · rw [if_neg e]
    by_cases hn : neighbor T S
    · rw [if_pos ⟨Ne.symm e, hn⟩, kval, meet_comm T S]; ring
    · rw [if_neg (fun hh => hn hh.2)]
      have hle := meet_le S T e
      have h1 : meet S T = 1 := by
        unfold neighbor at hn; rw [meet_comm T S] at hn; omega
      rw [h1]; norm_num

end PowerSaving.Colour
end OAI
