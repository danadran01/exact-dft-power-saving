import OAI.Computability.FourierTransform.Colour.ExponentFinal
import OAI.Computability.FourierTransform.Colour.CoordDesigns
import OAI.Computability.FourierTransform.Colour.SunDesign

/-!
# The final colour-register certificate (new; not part of OpenAI's development)

The designs of the three factors (stage order `(30, 20, 41)`) are the searched coordinate designs
(`CoordDesigns`, kernel-checked data) assembled with the cyclic sunflower designs (`SunDesign`).
Their register and side counts satisfy the hypotheses of `Final.final_obligations`, which gives the
three remaining hypotheses of `Net.ccertificateC` at `z = Expo.zC = 1 - 321/10^8`, `a = 43`.
Result: `fcertificate`, a grouped certificate on `2^43` roles over `24600` coordinates.
-/

set_option linter.constructorNameAsVariable false

namespace OAI
namespace PowerSaving.Colour
open Finset Binary

namespace FinalAssembly

/-! ### Chain steps of coordinate registers -/

/-- A Y-register all of whose nonempty labels lie in a list of at most 9 labels has at most 10 level
changes (an empty label never starts a change, since the chain starts at `∅`). -/
lemma ysteps_le_list {h : ℕ} (D : RegisterDesign h) (r : D.YReg) (L : List (Finset (Fin h)))
    (hL : L.length ≤ 9) (hmem : ∀ ℓ, D.ylab r ℓ = ∅ ∨ D.ylab r ℓ ∈ L) : ICost.ysteps D r ≤ 10 := by
  unfold ICost.ysteps
  refine (ICost.steps_le_image (ICost.yc D r) (ICost.yc_mono D r) (h + 1)
    (insert (univ \ {D.yslot r}) L.toFinset) ?_).trans ?_
  · intro ℓ hℓ
    rw [mem_filter, mem_range] at hℓ
    rw [mem_insert, List.mem_toFinset]
    by_cases h1 : ℓ + 1 ≤ h
    · right
      have e : ICost.yc D r (ℓ + 1) = D.ylab r (ℓ + 1) := by
        unfold ICost.yc; rw [ite_eq_right (by omega), ite_eq_left h1]
      rcases hmem (ℓ + 1) with h0 | h0
      · exfalso
        apply hℓ.2
        have a1 := ICost.yc_mono D r ℓ
        rw [e, h0] at a1 ⊢
        exact (subset_empty.mp a1).symm
      · rw [e]; exact h0
    · left
      unfold ICost.yc; rw [ite_eq_right (by omega), ite_eq_right h1]
  · calc (insert (univ \ {D.yslot r}) L.toFinset).card ≤ L.toFinset.card + 1 := card_insert_le _ _
      _ ≤ L.length + 1 := by have := List.toFinset_card_le L; omega
      _ ≤ 10 := by omega

/-! ### Counts of an assembled design -/

section Generic
variable {h : ℕ} (C : CoordSpec h) (Ds : PDesign h PDesign.twoP)

/-- The assembled design: coordinate part ∪ sunflower part. -/
noncomputable abbrev Asm : RegisterDesign h := PDesign.assemble C.toPDesign Ds

lemma card_X : Fintype.card (Asm C Ds).XReg = Fintype.card C.toPDesign.XReg + Fintype.card Ds.XReg := by
  show Fintype.card (C.toPDesign.XReg ⊕ Ds.XReg) = _
  exact Fintype.card_sum
lemma card_Y : Fintype.card (Asm C Ds).YReg = Fintype.card C.toPDesign.YReg + Fintype.card Ds.YReg := by
  show Fintype.card (C.toPDesign.YReg ⊕ Ds.YReg) = _
  exact Fintype.card_sum
lemma card_S : Fintype.card (Asm C Ds).Side = Fintype.card C.toPDesign.Side + Fintype.card Ds.Side := by
  show Fintype.card (C.toPDesign.Side ⊕ Ds.Side) = _
  exact Fintype.card_sum

/-- Only sunflower X-registers can have more than 2 level changes. -/
lemma nXl_le : (univ.filter fun r : (Asm C Ds).XReg => ¬ ICost.xsteps (Asm C Ds) r ≤ 2).card
    ≤ Fintype.card Ds.XReg := by
  calc _ ≤ ((univ : Finset Ds.XReg).map
        (Function.Embedding.inr : Ds.XReg ↪ (Asm C Ds).XReg)).card := by
        apply card_le_card
        intro r hr
        rw [mem_filter] at hr
        match r, hr with
        | .inl a, hr => exact absurd (ICost.xsteps_le_two (Asm C Ds) (.inl a)
            (fun ℓ _ _ => C.xlab_const a ℓ 1)) hr.2
        | .inr b, _ => exact mem_map_of_mem _ (mem_univ b)
    _ = _ := by rw [card_map, card_univ]

/-- Only sunflower Y-registers can have more than 10 level changes. -/
lemma nYl_le : (univ.filter fun r : (Asm C Ds).YReg => ¬ ICost.ysteps (Asm C Ds) r ≤ 10).card
    ≤ Fintype.card Ds.YReg := by
  calc _ ≤ ((univ : Finset Ds.YReg).map
        (Function.Embedding.inr : Ds.YReg ↪ (Asm C Ds).YReg)).card := by
        apply card_le_card
        intro r hr
        rw [mem_filter] at hr
        match r, hr with
        | .inl a, hr =>
          obtain ⟨L, hL, hm⟩ := C.ylab_few a
          exact absurd (ysteps_le_list (Asm C Ds) (.inl a) L hL hm) hr.2
        | .inr b, _ => exact mem_map_of_mem _ (mem_univ b)
    _ = _ := by rw [card_map, card_univ]

end Generic

/-! ### The three factors -/

lemma h7 (j : Fin 3) : 7 ≤ Net.hsC j := le_trans (by norm_num) (Net.hsC_ge j)

/-- The searched coordinate designs (kernel-checked data). -/
noncomputable def coordD : (j : Fin 3) → CoordSpec (Net.hsC j)
  | 0 => CC.D30.data.spec coordValid30
  | 1 => CC.D20.data.spec coordValid20
  | 2 => CC.D41.data.spec coordValid41

/-- The cyclic sunflower designs. -/
noncomputable def sunD (j : Fin 3) : PDesign (Net.hsC j) PDesign.twoP := sunDesign (Net.hsC j) (h7 j)

/-- The final register designs. -/
noncomputable abbrev Dfinal (j : Fin 3) : RegisterDesign (Net.hsC j) := Asm (coordD j) (sunD j)

lemma coordD0 : coordD 0 = CC.D30.data.spec coordValid30 := rfl
lemma coordD1 : coordD 1 = CC.D20.data.spec coordValid20 := rfl
lemma coordD2 : coordD 2 = CC.D41.data.spec coordValid41 := rfl

set_option maxRecDepth 200000 in
/-- Coordinate part: register and side counts (from `CoordDesigns`). -/
lemma coord_counts : ∀ j : Fin 3,
    Fintype.card (coordD j).toPDesign.XReg ≤ Expo.coordX j ∧
    Fintype.card (coordD j).toPDesign.YReg ≤ Expo.coordY j ∧
    Fintype.card (coordD j).toPDesign.Side + Fintype.card (sunD j).Side ≤ Expo.sideC j
  | 0 => by
    have x := coordDesign30_XReg; have y := coordDesign30_YReg; have c := coordDesign30_Side
    rw [coordDesign_eq30] at x y c
    rw [coordD0]
    refine ⟨x, y, ?_⟩
    unfold sunD
    rw [sunDesign_card_Side]
    have e : (if Even (Net.hsC 0) then 0 else 3 * (Net.hsC 0).choose 3) = 0 := by decide +kernel
    have g : Expo.sideC 0 = 14763 := rfl
    rw [e, g]
    exact (Nat.add_le_add_right c 0).trans (by norm_num)
  | 1 => by
    have x := coordDesign20_XReg; have y := coordDesign20_YReg; have c := coordDesign20_Side
    rw [coordDesign_eq20] at x y c
    rw [coordD1]
    refine ⟨x, y, ?_⟩
    unfold sunD
    rw [sunDesign_card_Side]
    have e : (if Even (Net.hsC 1) then 0 else 3 * (Net.hsC 1).choose 3) = 0 := by decide +kernel
    have g : Expo.sideC 1 = 3076 := rfl
    rw [e, g]
    exact (Nat.add_le_add_right c 0).trans (by norm_num)
  | 2 => by
    have x := coordDesign41_XReg; have y := coordDesign41_YReg; have c := coordDesign41_Side
    rw [coordDesign_eq41] at x y c
    rw [coordD2]
    refine ⟨x, y, ?_⟩
    unfold sunD
    rw [sunDesign_card_Side]
    have e : (if Even (Net.hsC 2) then 0 else 3 * (Net.hsC 2).choose 3) = 31980 := by decide +kernel
    have g : Expo.sideC 2 = 79147 := rfl
    rw [e, g]
    exact (Nat.add_le_add_right c 31980).trans (by norm_num)

/-- Sunflower part: `#XReg + #YReg = 6·C(h,3) = sunC`. -/
lemma sun_counts (j : Fin 3) :
    Fintype.card (sunD j).XReg + Fintype.card (sunD j).YReg ≤ Expo.sunC j := by
  unfold sunD
  rw [sunDesign_card_regs]
  fin_cases j <;> decide +kernel

/-- The three remaining hypotheses of `Net.ccertificateC`, for the final designs. -/
theorem final_hyps :
    Net.WnetC Dfinal ≤ 2 ^ 43 ∧
    (∀ c ∈ Net.Etot Dfinal Net.t0C (2 ^ 43 - Net.WnetC Dfinal), 1 ≤ c ∧ c < 24600) ∧
    ∑ c : Fin 24600, ((Net.Etot Dfinal Net.t0C (2 ^ 43 - Net.WnetC Dfinal)).count (c : ℕ) : ℝ)
      * ((c : ℝ) / 24600) ^ Expo.zC < 2 ^ 43 := by
  refine Final.final_obligations Dfinal (fun j => Fintype.card (sunD j).XReg)
    (fun j => Fintype.card (sunD j).YReg) sun_counts ?_ ?_ ?_ ?_ ?_
  · intro j
    rw [card_S]; exact (coord_counts j).2.2
  · intro j
    rw [card_X]; have := (coord_counts j).1; omega
  · intro j
    exact nXl_le (coordD j) (sunD j)
  · intro j
    rw [card_Y]; have := (coord_counts j).2.1; omega
  · intro j
    exact nYl_le (coordD j) (sunD j)

end FinalAssembly

open FinalAssembly

/-- Roles and coordinates of the final network. -/
abbrev RoleF := Net.RoleC Dfinal
abbrev BlocksF := Blk Net.hsC

/-- **The final colour-register certificate**: one grouped word on `2^43` roles over `24600`
coordinates, computing `kernel` on every role, with all batch sizes in `[1, 24600)` and
`Σ_c N(c) (c/24600)^z < 2^43` at `z = 1 - 3.21·10⁻⁶`. -/
theorem fcertificate : ∃ p : GWord BlocksF RoleF,
    (∀ c ∈ sizes p, 1 ≤ c ∧ c < 24600) ∧
    (∑ c : Fin 24600, ((sizes p).count (c:ℕ) : ℝ) * ((c:ℝ)/24600)^Expo.zC < 2^43) ∧
    ∀ f (x : Data BlocksF RoleF f), gwalk f p x = multiAct f (fun _ => kernel BlocksF) x :=
  Net.ccertificateC Dfinal 43 Expo.zC final_hyps.2.1 final_hyps.2.2

theorem card_roleF : Fintype.card RoleF = 2^43 := Net.card_roleC Dfinal final_hyps.1
theorem card_blocksF : Fintype.card BlocksF = 24600 := Net.card_blk_C

end PowerSaving.Colour
end OAI
