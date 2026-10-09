import OAI.Computability.FourierTransform.Colour.Certificate

/-!
# Colour network, part 13b: the certificate interface (new)

* `ccertificate_of`: from the network word `cnet_word` and two facts about its batch multiset
  `Etot` (all sizes in `[1, u)`, and `Σ_c N(c) (c/u)^z < 2^a`) to the interface consumed by the
  grouped recursion (`GSaving.gallot_bound`).
* Role counting: `keySplit` (`Key ≃ Trip h_j × Inv j`), `card_key`, `card_inv`, `card_role`.
* The concrete sizes `(30, 20, 41)` in stage order: `hsC`, `t0C`, `card_blk_C = 24600`,
  `card_key_C`, `card_inv_C`, the role count `WnetC`, padding `2^43 − WnetC`, and
  `card_roleC : card RoleC = 2^43`; `ccertificateC` is `ccertificate_of` at these parameters.

The design data (C15 sunflower, C16 coordinate) and the bounds on `Etot` (C11, C14) are supplied by
`InvocationCost`, `Exponent`, `SunDesign`, `CoordDesign`.
-/

namespace OAI
namespace PowerSaving.Colour
namespace Net
open Finset Matrix Binary

section General
variable {hs : Fin 3 → ℕ} [∀ i, NeZero (hs i)]
variable (Ds : ∀ j, RegisterDesign (hs j)) (t0 : Key hs) (P : ℕ)

/-- The certificate in the form consumed by the grouped recursion. -/
theorem ccertificate_of (hh : ∀ j, 9 ≤ hs j) (u a : ℕ) (z : ℝ)
    (hmem : ∀ c ∈ Etot Ds t0 P, 1 ≤ c ∧ c < u)
    (hphi : ∑ c : Fin u, ((Etot Ds t0 P).count (c : ℕ) : ℝ) * ((c : ℝ) / u) ^ z < 2 ^ a) :
    ∃ p : GWord (Blk hs) (Role Ds t0 P),
      (∀ c ∈ sizes p, 1 ≤ c ∧ c < u) ∧
      (∑ c : Fin u, (((sizes p).count (c : ℕ) : ℕ) : ℝ) * ((c : ℝ) / u) ^ z < 2 ^ a) ∧
      ∀ f (x : Data (Blk hs) (Role Ds t0 P) f),
        gwalk f p x = multiAct f (fun _ => kernel (Blk hs)) x := by
  obtain ⟨p, hp, hw⟩ := cnet_word Ds t0 P hh
  refine ⟨p, ?_, ?_, hw⟩
  · intro c hc
    apply hmem
    rw [← hp]
    exact Multiset.mem_coe.mpr hc
  · have hc : ∀ c : ℕ, (sizes p).count c = (Etot Ds t0 P).count c := by
      intro c; rw [← hp, Multiset.coe_count]
    simp only [hc]
    exact hphi

/-! ### Counting roles -/

@[simp] lemma omit_locate (j : Fin 3) (o : Inv t0 j) (T : Trip (hs j)) :
    omitJ t0 j (locate t0 j o T) = o := by
  apply Subtype.ext
  funext i
  by_cases h : i = j
  · subst h; simp [omitJ, locate, o.2]
  · simp [omitJ, locate, Function.update_of_ne h]

@[simp] lemma locate_self (j : Fin 3) (o : Inv t0 j) (T : Trip (hs j)) :
    locate t0 j o T j = T := by simp [locate]

/-- A key is a triple at `j` together with an invocation of stage `j`. -/
def keySplit (j : Fin 3) : Key hs ≃ Trip (hs j) × Inv t0 j where
  toFun d := (d j, omitJ t0 j d)
  invFun q := locate t0 j q.2 q.1
  left_inv d := locate_omit t0 j d
  right_inv q := by
    obtain ⟨T, o⟩ := q
    simp

omit [∀ i, NeZero (hs i)] in
lemma card_key : Fintype.card (Key hs) = ∏ j, (hs j).choose 3 := by
  rw [Fintype.card_pi]
  simp only [num_trip]

lemma card_key_split (j : Fin 3) :
    Fintype.card (Key hs) = (hs j).choose 3 * Fintype.card (Inv t0 j) := by
  rw [Fintype.card_congr (keySplit t0 j), Fintype.card_prod, num_trip]

lemma card_auxpart (j : Fin 3) : Fintype.card (AuxPart Ds j)
    = hs j + Fintype.card (Ds j).Side + Fintype.card (Ds j).XReg + Fintype.card (Ds j).YReg := by
  simp only [AuxPart, Fintype.card_sum, Fintype.card_fin]
  ring

lemma card_role : Fintype.card (Role Ds t0 P)
    = 2 * Fintype.card (Key hs) + (∑ j, Fintype.card (Inv t0 j) * Fintype.card (AuxPart Ds j))
      + P := by
  simp only [Role, AllAux, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin]
  ring

omit [∀ i, NeZero (hs i)] in
lemma card_blk : Fintype.card (Blk hs) = ∏ j, hs j := by
  rw [Fintype.card_pi]; simp

end General

/-! ### The concrete sizes (30, 20, 41) -/

/-- Factor sizes in stage order. -/
abbrev hsC : Fin 3 → ℕ := ![30, 20, 41]

instance hsC_ne (i : Fin 3) : NeZero (hsC i) := ⟨by fin_cases i <;> decide⟩

lemma hsC_ge (j : Fin 3) : 9 ≤ hsC j := by fin_cases j <;> decide

lemma card_three (j : Fin 3) : ({0, 1, 2} : Finset (Fin (hsC j))).card = 3 := by
  fin_cases j <;> decide

/-- Reference key: the triple `{0, 1, 2}` in every factor. -/
def t0C : Key hsC := fun j =>
  ⟨{0, 1, 2}, by
    show ({0, 1, 2} : Finset (Fin (hsC j))) ∈ (univ : Finset (Fin (hsC j))).powersetCard 3
    rw [mem_powersetCard]; exact ⟨subset_univ _, card_three j⟩⟩

lemma card_blk_C : Fintype.card (Blk hsC) = 24600 := by
  rw [card_blk, Fin.prod_univ_three]; rfl

/-- `N₀ = v₁ v₂ v₃`. -/
lemma card_key_C : Fintype.card (Key hsC) = 49338744000 := by
  rw [card_key, Fin.prod_univ_three]; decide

/-- Invocations per stage: `N₀ / v_j`. -/
lemma card_inv_C : Fintype.card (Inv t0C 0) = 12152400 ∧ Fintype.card (Inv t0C 1) = 43279600 ∧
    Fintype.card (Inv t0C 2) = 4628400 := by
  have h0 := card_key_split t0C 0
  have h1 := card_key_split t0C 1
  have h2 := card_key_split t0C 2
  rw [card_key_C] at h0 h1 h2
  have c0 : (hsC 0).choose 3 = 4060 := by decide
  have c1 : (hsC 1).choose 3 = 1140 := by decide
  have c2 : (hsC 2).choose 3 = 10660 := by decide
  rw [c0] at h0; rw [c1] at h1; rw [c2] at h2
  omega

variable (Ds : ∀ j, RegisterDesign (hsC j))

/-- Number of non-padding roles. -/
noncomputable def WnetC : ℕ :=
  2 * Fintype.card (Key hsC) + ∑ j, Fintype.card (Inv t0C j) * Fintype.card (AuxPart Ds j)

/-- The roles of the concrete network, padded to `2^43`. -/
abbrev RoleC := Role Ds t0C (2 ^ 43 - WnetC Ds)

theorem card_roleC (hW : WnetC Ds ≤ 2 ^ 43) : Fintype.card (RoleC Ds) = 2 ^ 43 := by
  rw [card_role]
  unfold WnetC at hW ⊢
  omega

/-- `WnetC` in terms of the per-invocation auxiliary counts. -/
lemma WnetC_eq : WnetC Ds = 2 * 49338744000 + 12152400 * Fintype.card (AuxPart Ds 0)
    + 43279600 * Fintype.card (AuxPart Ds 1) + 4628400 * Fintype.card (AuxPart Ds 2) := by
  obtain ⟨h0, h1, h2⟩ := card_inv_C
  rw [WnetC, card_key_C, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- **The colour certificate** at the sizes (30, 20, 41), `u = 24600`, `2^43` roles, conditional on
the role count and on the two facts about the batch multiset (supplied by C11, C14). -/
theorem ccertificateC (a : ℕ) (z : ℝ)
    (hmem : ∀ c ∈ Etot Ds t0C (2 ^ 43 - WnetC Ds), 1 ≤ c ∧ c < 24600)
    (hphi : ∑ c : Fin 24600, ((Etot Ds t0C (2 ^ 43 - WnetC Ds)).count (c : ℕ) : ℝ)
        * ((c : ℝ) / 24600) ^ z < 2 ^ a) :
    ∃ p : GWord (Blk hsC) (RoleC Ds),
      (∀ c ∈ sizes p, 1 ≤ c ∧ c < 24600) ∧
      (∑ c : Fin 24600, (((sizes p).count (c : ℕ) : ℕ) : ℝ) * ((c : ℝ) / 24600) ^ z < 2 ^ a) ∧
      ∀ f (x : Data (Blk hsC) (RoleC Ds) f),
        gwalk f p x = multiAct f (fun _ => kernel (Blk hsC)) x := by
  have := ccertificate_of Ds t0C (2 ^ 43 - WnetC Ds) hsC_ge 24600 a z hmem
  push_cast at this ⊢
  exact this hphi

end Net
end PowerSaving.Colour
end OAI
