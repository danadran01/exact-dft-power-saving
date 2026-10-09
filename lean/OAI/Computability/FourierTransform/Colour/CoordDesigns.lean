import OAI.Computability.FourierTransform.Colour.CoordBridge
import OAI.Computability.FourierTransform.Colour.Designs.D30
import OAI.Computability.FourierTransform.Colour.Designs.D20
import OAI.Computability.FourierTransform.Colour.Designs.D41

/-!
# Colour network, C16 (part 4): the coordinate designs of the three factors (new)

The searched coordinate designs `code/sidewires/designs/{d30_ch0_cyc,d20_ch14_cyc,d41_ch0_cyc}.json`
(stage order `hs = ![30, 20, 41]`), as partial register designs for the predicate "disjoint":

* `coordDesign30 : PDesign 30 PDesign.disjointP`, and likewise `coordDesign20`, `coordDesign41`;
* the data are the `Nat`-encoded modules `Designs/D30.lean`, `D20.lean`, `D41.lean`; their checks
  (`global_ok`, `groups_ok`, `elems_ok`, counts) are `decide +kernel` theorems, i.e. evaluated by the Lean
  kernel with GMP arithmetic (no `native_decide`, no extra axioms);
* soundness of the checks: `CoordBridge.lean`; the design construction (first-cover transfers, side pairs =
  the uncovered disjoint pairs): `CoordDesign.lean`.

Counts (upper bounds, as needed by the exponent):

| factor | X-registers ≤ | Y-registers ≤ | side pairs ≤ |
|---|---|---|---|
| h = 30 | 96 881 | 94 429 | 14 763 |
| h = 20 | 18 090 | 17 552 | 3 076 |
| h = 41 | 304 414 | 330 907 | 47 167 |

Chain facts: every X-register has a constant label (`xlab_const`, no level changes), and every Y-label is
empty or one of at most 9 labels (`ylab_few`), with at most 9 level changes (`ychanges`).
-/

namespace OAI
namespace PowerSaving.Colour
open Finset CC

/-! ### h = 30 -/

theorem coordValid30 : CC.D30.data.Valid where
  hh := by decide
  hv := by decide
  glob := CC.D30.global_ok
  grp := CC.D30.groups_ok
  el := CC.D30.elems_ok

noncomputable def coordDesign30 : PDesign 30 PDesign.disjointP := CC.D30.data.coordDesign coordValid30

theorem coordDesign30_XReg : Fintype.card coordDesign30.XReg ≤ 96881 :=
  CC.D30.nX_eq ▸ CC.D30.data.card_XReg_le coordValid30

theorem coordDesign30_YReg : Fintype.card coordDesign30.YReg ≤ 94429 :=
  CC.D30.nY_eq ▸ CC.D30.data.card_YReg_le coordValid30 _ CC.D30.v_le

theorem coordDesign30_Side : Fintype.card coordDesign30.Side ≤ 14763 :=
  CC.D30.nS_eq ▸ CC.D30.data.card_Side_le coordValid30

/-! ### h = 20 -/

theorem coordValid20 : CC.D20.data.Valid where
  hh := by decide
  hv := by decide
  glob := CC.D20.global_ok
  grp := CC.D20.groups_ok
  el := CC.D20.elems_ok

noncomputable def coordDesign20 : PDesign 20 PDesign.disjointP := CC.D20.data.coordDesign coordValid20

theorem coordDesign20_XReg : Fintype.card coordDesign20.XReg ≤ 18090 :=
  CC.D20.nX_eq ▸ CC.D20.data.card_XReg_le coordValid20

theorem coordDesign20_YReg : Fintype.card coordDesign20.YReg ≤ 17552 :=
  CC.D20.nY_eq ▸ CC.D20.data.card_YReg_le coordValid20 _ CC.D20.v_le

theorem coordDesign20_Side : Fintype.card coordDesign20.Side ≤ 3076 :=
  CC.D20.nS_eq ▸ CC.D20.data.card_Side_le coordValid20

/-! ### h = 41 -/

theorem coordValid41 : CC.D41.data.Valid where
  hh := by decide
  hv := by decide
  glob := CC.D41.global_ok
  grp := CC.D41.groups_ok
  el := CC.D41.elems_ok

noncomputable def coordDesign41 : PDesign 41 PDesign.disjointP := CC.D41.data.coordDesign coordValid41

theorem coordDesign41_XReg : Fintype.card coordDesign41.XReg ≤ 304414 :=
  CC.D41.nX_eq ▸ CC.D41.data.card_XReg_le coordValid41

theorem coordDesign41_YReg : Fintype.card coordDesign41.YReg ≤ 330907 :=
  CC.D41.nY_eq ▸ CC.D41.data.card_YReg_le coordValid41 _ CC.D41.v_le

theorem coordDesign41_Side : Fintype.card coordDesign41.Side ≤ 47167 :=
  CC.D41.nS_eq ▸ CC.D41.data.card_Side_le coordValid41

/-! ### Chain facts (all three designs are `CoordSpec.toPDesign`) -/

theorem coordDesign_eq30 : coordDesign30 = (CC.D30.data.spec coordValid30).toPDesign := rfl
theorem coordDesign_eq20 : coordDesign20 = (CC.D20.data.spec coordValid20).toPDesign := rfl
theorem coordDesign_eq41 : coordDesign41 = (CC.D41.data.spec coordValid41).toPDesign := rfl

namespace CoordSpec
variable {h : ℕ} (C : CoordSpec h)

/-- At most 9 distinct nonempty Y-labels per Y-register. -/
theorem ylab_few (r : C.toPDesign.YReg) :
    ∃ L : List (Finset (Fin h)), L.length ≤ 9 ∧ ∀ ℓ, C.toPDesign.ylab r ℓ = ∅ ∨ C.toPDesign.ylab r ℓ ∈ L :=
  ⟨C.labs r.1, C.labs_len r.1, C.ylab_mem r⟩

end CoordSpec

end PowerSaving.Colour
end OAI
