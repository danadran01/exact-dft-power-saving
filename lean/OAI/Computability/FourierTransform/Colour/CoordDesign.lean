import OAI.Computability.FourierTransform.Colour.Design
import OAI.Computability.FourierTransform.Colour.CoordBase

/-!
# Colour network, C16 (part 2): coordinate register designs from group data (new)

Abstract form of the searched coordinate part of a register design (results/C_sidewires.md §2,
FORMALIZATION_CNET.md §4.3), and its partial design for the pair predicate "disjoint".

`CoordSpec h`:
* groups `g : Fin G`, each with a reader set `R g` and a list of coordinate labels `labs g` that is
  totally ordered by inclusion (a prefix chain), every label of size in `[4, h-4]`, at most 9 labels;
* writer hints: `hints T` lists pairs `(g, i)`; each is an X-register of `T` at label `(labs g)[i] ⊇ T`.

The partial design `CoordSpec.toPDesign : PDesign h PDesign.disjointP`:
* X-register `(T, t)` (the `t`-th hint of `T`, label `A`): basis `coordBase T d` with pivot
  `d ∈ A \ T`, slot `d`, constant label `xlab ℓ = A`;
* Y-register `(g, S)` (`S ∈ R g`): its chain is every label of `g` avoiding `S` (*maximal* chains),
  `ylab ℓ` = the union of the chain labels of size `≤ ℓ`; basis `coordBase S d'` with pivot `d'` outside `S`
  and all chain labels;
* **first-cover semantics**: `covered T S` iff some hint `(g, i)` of `T` has `S ∈ R g` and `S` disjoint from
  the label. Transfers = the covered disjoint pairs (one transfer each, at the chosen hint; level = label
  size); side pairs = the uncovered disjoint pairs. So `cover` holds **by construction**.

Sync is `coord_sync` (Lemmas C.7/C.9). Counts: `card XReg = Σ_T #hints T`, `card YReg = Σ_g #R g`, and
`card Side ≤ Σ_T #sides T` whenever every uncovered disjoint pair is listed in `sides`. The chain facts
for the exponent: X-labels are constant, Y-labels take at most 9 nonempty values, `≤ 9` level changes.
-/

namespace OAI
namespace PowerSaving.Colour
open Finset

/-! ### Unions of chains of finsets -/

/-- Union of a list of finsets. -/
def lunion {α : Type*} [DecidableEq α] (l : List (Finset α)) : Finset α := l.foldr (· ∪ ·) ∅

section lunion
variable {α : Type*} [DecidableEq α]
set_option linter.unusedSectionVars false

@[simp] lemma lunion_nil : lunion ([] : List (Finset α)) = ∅ := rfl
@[simp] lemma lunion_cons (A : Finset α) (l : List (Finset α)) : lunion (A :: l) = A ∪ lunion l := rfl

lemma mem_lunion (l : List (Finset α)) (x : α) : x ∈ lunion l ↔ ∃ A ∈ l, x ∈ A := by
  induction l with
  | nil => simp
  | cons A l ih => simp [ih]

lemma subset_lunion {l : List (Finset α)} {A : Finset α} (hA : A ∈ l) : A ⊆ lunion l :=
  fun x hx => (mem_lunion l x).2 ⟨A, hA, hx⟩

/-- The union of a chain (pairwise `⊆` in list order) is empty or one of its members. -/
lemma lunion_eq (l : List (Finset α)) (hl : l.Pairwise (· ⊆ ·)) : lunion l = ∅ ∨ lunion l ∈ l := by
  induction l with
  | nil => simp
  | cons A t ih =>
    rw [List.pairwise_cons] at hl
    rcases ih hl.2 with e | e
    · right; rw [lunion_cons, e, union_empty]; exact List.mem_cons_self
    · right; rw [lunion_cons, union_eq_right.2 (hl.1 _ e)]; exact List.mem_cons_of_mem _ e

/-- Members of a chain are comparable. -/
lemma chain_comparable {l : List (Finset α)} (hl : l.Pairwise (· ⊆ ·)) {A B : Finset α}
    (hA : A ∈ l) (hB : B ∈ l) : A ⊆ B ∨ B ⊆ A := by
  induction l with
  | nil => simp at hA
  | cons C t ih =>
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.1 hA with hA1 | hA1 <;> rcases List.mem_cons.1 hB with hB1 | hB1
    · subst hA1; subst hB1; exact Or.inl subset_rfl
    · subst hA1; exact Or.inl (hl.1 _ hB1)
    · subst hB1; exact Or.inr (hl.1 _ hA1)
    · exact ih hl.2 hA1 hB1

end lunion

/-! ### Abstract coordinate design data -/

/-- Group data of a coordinate design for one factor `F₂^h` (§4.3 of FORMALIZATION_CNET.md). -/
structure CoordSpec (h : ℕ) where
  G : ℕ
  /-- readers of group `g` -/
  R : Fin G → Finset (Trip h)
  /-- the (nested) labels of group `g` -/
  labs : Fin G → List (Finset (Fin h))
  /-- writer hints `(g, i)` of `T` -/
  hints : Trip h → List (Fin G × ℕ)
  hh : 4 ≤ h
  labs_nest : ∀ g, (labs g).Pairwise (· ⊆ ·)
  labs_card : ∀ g, ∀ A ∈ labs g, 4 ≤ A.card ∧ A.card + 4 ≤ h
  labs_len : ∀ g, (labs g).length ≤ 9
  hint_lt : ∀ T, ∀ p ∈ hints T, p.2 < (labs p.1).length
  hint_sub : ∀ T, ∀ p ∈ hints T, T.val ⊆ (labs p.1).getD p.2 ∅

namespace CoordSpec
variable {h : ℕ} (C : CoordSpec h)

/-- The label of a hint. -/
def hlab (p : Fin C.G × ℕ) : Finset (Fin h) := (C.labs p.1).getD p.2 ∅

lemma hlab_mem {T : Trip h} {p : Fin C.G × ℕ} (hp : p ∈ C.hints T) : C.hlab p ∈ C.labs p.1 := by
  unfold hlab; rw [List.getD_eq_getElem _ _ (C.hint_lt T p hp)]; exact List.getElem_mem _

lemma hlab_card {T : Trip h} {p : Fin C.G × ℕ} (hp : p ∈ C.hints T) :
    4 ≤ (C.hlab p).card ∧ (C.hlab p).card + 4 ≤ h :=
  C.labs_card _ _ (C.hlab_mem hp)

/-! #### X-registers -/

/-- X-registers: the hints of each writer. -/
abbrev XR := Σ T : Trip h, Fin (C.hints T).length

def xhint (r : C.XR) : Fin C.G × ℕ := (C.hints r.1)[r.2]

lemma xhint_mem (r : C.XR) : C.xhint r ∈ C.hints r.1 := List.getElem_mem _

def xlabel (r : C.XR) : Finset (Fin h) := C.hlab (C.xhint r)

lemma xpiv_ne (r : C.XR) : (C.xlabel r \ r.1.val).Nonempty := by
  rw [← card_pos]
  have h1 := le_card_sdiff r.1.val (C.xlabel r)
  have h2 := (C.hlab_card (C.xhint_mem r)).1
  rw [trip_card] at h1
  unfold xlabel at h1 ⊢
  omega

/-- The pivot of an X-register: a label coordinate outside the owner. -/
def xslot (r : C.XR) : Fin h := (C.xlabel r \ r.1.val).min' (C.xpiv_ne r)

lemma xslot_mem (r : C.XR) : C.xslot r ∈ C.xlabel r ∧ C.xslot r ∉ r.1.val :=
  mem_sdiff.1 (min'_mem _ _)

lemma xlabel_sub (r : C.XR) : r.1.val ⊆ C.xlabel r := C.hint_sub r.1 _ (C.xhint_mem r)

/-! #### Y-registers -/

/-- Y-registers: the readers of each group. -/
abbrev YR := Σ g : Fin C.G, {S : Trip h // S ∈ C.R g}

def yown (r : C.YR) : Trip h := r.2.1

/-- The (maximal) chain of a reader: the labels of its group avoiding it. -/
def ychain (r : C.YR) : List (Finset (Fin h)) := (C.labs r.1).filter fun A => Disjoint (C.yown r).val A

def ylab (r : C.YR) (ℓ : ℕ) : Finset (Fin h) := lunion ((C.ychain r).filter fun A => A.card ≤ ℓ)

def yall (r : C.YR) : Finset (Fin h) := lunion (C.ychain r)

lemma ychain_pw (r : C.YR) : (C.ychain r).Pairwise (· ⊆ ·) :=
  (C.labs_nest r.1).sublist List.filter_sublist

lemma mem_ychain {r : C.YR} {A : Finset (Fin h)} :
    A ∈ C.ychain r ↔ A ∈ C.labs r.1 ∧ Disjoint (C.yown r).val A := by
  simp [ychain]

lemma yall_card (r : C.YR) : (C.yall r).card + 4 ≤ h := by
  rcases lunion_eq _ (C.ychain_pw r) with e | e
  · rw [yall, e, card_empty]; exact C.hh
  · exact (C.labs_card r.1 _ (C.mem_ychain.1 e).1).2

lemma ypiv_ne (r : C.YR) : (univ \ ((C.yown r).val ∪ C.yall r)).Nonempty := by
  rw [← card_pos, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  have h1 := card_union_le (C.yown r).val (C.yall r)
  have h2 := C.yall_card r
  rw [trip_card] at h1
  omega

/-- The pivot of a Y-register: outside the owner and all its chain labels. -/
def yslot (r : C.YR) : Fin h := (univ \ ((C.yown r).val ∪ C.yall r)).min' (C.ypiv_ne r)

lemma yslot_spec (r : C.YR) : C.yslot r ∉ (C.yown r).val ∧ C.yslot r ∉ C.yall r := by
  have := (univ \ ((C.yown r).val ∪ C.yall r)).min'_mem (C.ypiv_ne r)
  simp only [mem_sdiff, mem_univ, mem_union, not_or, true_and] at this
  exact this

lemma ylab_sub_yall (r : C.YR) (ℓ : ℕ) : C.ylab r ℓ ⊆ C.yall r := by
  intro x hx
  obtain ⟨A, hA, hx⟩ := (mem_lunion _ x).1 hx
  exact (mem_lunion _ x).2 ⟨A, List.mem_of_mem_filter hA, hx⟩

lemma ylab_mono (r : C.YR) : Monotone (C.ylab r) := by
  intro a b hab x hx
  obtain ⟨A, hA, hx⟩ := (mem_lunion _ x).1 hx
  rw [List.mem_filter] at hA
  refine (mem_lunion _ x).2 ⟨A, List.mem_filter.2 ⟨hA.1, ?_⟩, hx⟩
  have := of_decide_eq_true hA.2
  exact decide_eq_true (le_trans this hab)

/-- At the level of a chain label, the Y-register sits exactly at that label. -/
lemma ylab_at {r : C.YR} {A : Finset (Fin h)} (hA : A ∈ C.ychain r) : C.ylab r A.card = A := by
  ext x
  rw [ylab, mem_lunion]
  constructor
  · rintro ⟨B, hB, hx⟩
    rw [List.mem_filter] at hB
    have hc := of_decide_eq_true hB.2
    rcases chain_comparable (C.ychain_pw r) hB.1 hA with e | e
    · exact e hx
    · rw [eq_of_subset_of_card_le e hc]; exact hx
  · intro hx
    exact ⟨A, List.mem_filter.2 ⟨hA, decide_eq_true le_rfl⟩, hx⟩

/-- `ylab` is empty or one of the group's labels (so a Y-register has at most 9 labels). -/
lemma ylab_range (r : C.YR) (ℓ : ℕ) : C.ylab r ℓ = ∅ ∨ C.ylab r ℓ ∈ C.labs r.1 := by
  rcases lunion_eq _ ((C.ychain_pw r).sublist (List.filter_sublist (p := fun A => decide (A.card ≤ ℓ))))
    with e | e
  · exact Or.inl e
  · exact Or.inr (C.mem_ychain.1 (List.mem_of_mem_filter e)).1

/-! #### Transfers (first cover) and side pairs -/

/-- `T` writes to `S` through one of its hints. -/
def covered (T S : Trip h) : Prop :=
  ∃ t : Fin (C.hints T).length, S ∈ C.R (C.hints T)[t].1 ∧ Disjoint S.val (C.hlab (C.hints T)[t])

instance : DecidableRel C.covered := fun T S => by unfold covered; infer_instance

lemma covered_of_mem {T S : Trip h} {p : Fin C.G × ℕ} (hp : p ∈ C.hints T) (hS : S ∈ C.R p.1)
    (hd : Disjoint S.val (C.hlab p)) : C.covered T S := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hp
  exact ⟨⟨t, ht⟩, hS, hd⟩

abbrev TrT : Type := {p : Trip h × Trip h // meet p.1 p.2 = 0 ∧ C.covered p.1 p.2}
abbrev SideT : Type := {p : Trip h × Trip h // meet p.1 p.2 = 0 ∧ ¬ C.covered p.1 p.2}

/-- The hint used by a transfer (a choice; any covering hint works). -/
noncomputable def tidx (τ : C.TrT) : Fin (C.hints τ.1.1).length := Classical.choose τ.2.2

lemma tidx_spec (τ : C.TrT) :
    τ.1.2 ∈ C.R (C.hints τ.1.1)[C.tidx τ].1 ∧ Disjoint τ.1.2.val (C.hlab (C.hints τ.1.1)[C.tidx τ]) :=
  Classical.choose_spec τ.2.2

noncomputable def tx (τ : C.TrT) : C.XR := ⟨τ.1.1, C.tidx τ⟩

noncomputable def ty (τ : C.TrT) : C.YR :=
  ⟨(C.hints τ.1.1)[C.tidx τ].1, ⟨τ.1.2, (C.tidx_spec τ).1⟩⟩

lemma tlabel_mem (τ : C.TrT) : C.xlabel (C.tx τ) ∈ C.ychain (C.ty τ) :=
  C.mem_ychain.2 ⟨C.hlab_mem (C.xhint_mem (C.tx τ)), (C.tidx_spec τ).2⟩

lemma card_subtype_eq {α : Type*} (p : α → Prop) [DecidablePred p] [Fintype {x // p x}] (a : α)
    (q : {x // p x} → Prop) [DecidablePred q] (hq : ∀ x, q x ↔ x.1 = a) :
    (univ.filter q).card = if p a then 1 else 0 := by
  split_ifs with ha
  · rw [card_eq_one]
    refine ⟨⟨a, ha⟩, ?_⟩
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_singleton, hq, Subtype.ext_iff]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    exact ha ((hq x).1 hx ▸ x.2)

/-! #### The partial design -/

/-- **The coordinate partial design** (first-cover semantics) for the predicate "disjoint". -/
noncomputable def toPDesign : PDesign h PDesign.disjointP where
  XReg := C.XR
  YReg := C.YR
  Side := C.SideT
  Tr := C.TrT
  xown r := r.1
  yown := C.yown
  xbase r := coordBase r.1 (C.xslot r)
  ybase r := coordBase (C.yown r) (C.yslot r)
  xslot := C.xslot
  yslot := C.yslot
  xlab r _ := C.xlabel r
  ylab := C.ylab
  x_slot r := coordBase_slot r.1 (C.xslot_mem r).2
  y_slot r := coordBase_slot (C.yown r) (C.yslot_spec r).1
  x_mem r _ := (C.xslot_mem r).1
  y_out r ℓ hm := (C.yslot_spec r).2 (C.ylab_sub_yall r ℓ hm)
  x_mono _ := monotone_const
  y_mono := C.ylab_mono
  tx := C.tx
  ty := C.ty
  tlev τ := (C.xlabel (C.tx τ)).card
  tlev_mem τ := by
    have h1 := (C.hlab_card (C.xhint_mem (C.tx τ))).1
    have h2 := card_le_univ (C.xlabel (C.tx τ))
    rw [Fintype.card_fin] at h2
    exact mem_Icc.2 ⟨by unfold xlabel; omega, h2⟩
  sync τ := by
    show (coordBase (C.tx τ).1 (C.xslot (C.tx τ))).mat (C.xlabel (C.tx τ))
      = (coordBase (C.yown (C.ty τ)) (C.yslot (C.ty τ))).mat (C.ylab (C.ty τ) (C.xlabel (C.tx τ)).card)
    rw [C.ylab_at (C.tlabel_mem τ)]
    have hS := (C.mem_ychain.1 (C.tlabel_mem τ)).2
    exact coord_sync _ _ (C.xslot_mem _).2 (C.yslot_spec _).1 _ (C.xlabel_sub _) (C.xslot_mem _).1 hS
      (fun hm => (C.yslot_spec _).2 (subset_lunion (C.tlabel_mem τ) hm))
  sx σ := σ.1.1
  sy σ := σ.1.2
  side_ok σ := Or.inl σ.2.1
  cover T S := by
    rw [card_subtype_eq (fun p : Trip h × Trip h => meet p.1 p.2 = 0 ∧ C.covered p.1 p.2) (T, S)
        (fun τ : C.TrT => (C.tx τ).1 = T ∧ C.yown (C.ty τ) = S)
        (fun τ => (Prod.ext_iff (x := τ.1) (y := (T, S))).symm),
      card_subtype_eq (fun p : Trip h × Trip h => meet p.1 p.2 = 0 ∧ ¬ C.covered p.1 p.2) (T, S)
        (fun σ : C.SideT => σ.1.1 = T ∧ σ.1.2 = S)
        (fun σ => (Prod.ext_iff (x := σ.1) (y := (T, S))).symm)]
    by_cases hm : meet T S = 0 <;> by_cases hc : C.covered T S <;>
      simp [hm, hc, PDesign.disjointP]

/-! ### Counts and chain facts -/

theorem card_XReg : Fintype.card C.toPDesign.XReg = ∑ T, (C.hints T).length := by
  show Fintype.card C.XR = _
  rw [Fintype.card_sigma]; simp

theorem card_YReg : Fintype.card C.toPDesign.YReg = ∑ g, (C.R g).card := by
  show Fintype.card C.YR = _
  rw [Fintype.card_sigma]; simp

/-- Side wires are the uncovered disjoint pairs; any list containing them bounds their number. -/
theorem card_Side_le (sides : Trip h → List (Trip h))
    (hs : ∀ T S, meet T S = 0 → ¬ C.covered T S → S ∈ sides T) :
    Fintype.card C.toPDesign.Side ≤ ∑ T, (sides T).length := by
  show Fintype.card C.SideT ≤ _
  let f : C.SideT → Σ T : Trip h, {S : Trip h // S ∈ (sides T).toFinset} :=
    fun σ => ⟨σ.1.1, ⟨σ.1.2, List.mem_toFinset.2 (hs _ _ σ.2.1 σ.2.2)⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨T, S⟩, _⟩ ⟨⟨T', S'⟩, _⟩ e
    simp only [f, Sigma.mk.injEq] at e
    obtain ⟨rfl, e⟩ := e
    have := (Subtype.heq_iff_coe_eq (fun _ => Iff.rfl)).1 e
    simp only at this
    subst this
    rfl
  refine (Fintype.card_le_of_injective f hf).trans ?_
  rw [Fintype.card_sigma]
  apply sum_le_sum
  intro T _
  rw [Fintype.card_coe]
  exact List.toFinset_card_le _

/-- X-registers have a constant label on all levels. -/
theorem xlab_const (r : C.toPDesign.XReg) (ℓ ℓ' : ℕ) : C.toPDesign.xlab r ℓ = C.toPDesign.xlab r ℓ' :=
  rfl

theorem xchanges (r : C.toPDesign.XReg) :
    ((range h).filter fun ℓ => C.toPDesign.xlab r (ℓ + 1) ≠ C.toPDesign.xlab r ℓ).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro ℓ _ hne
  exact hne rfl

/-- Every Y-label is empty or one of the (at most 9) labels of the register's group. -/
theorem ylab_mem (r : C.toPDesign.YReg) (ℓ : ℕ) :
    C.toPDesign.ylab r ℓ = ∅ ∨ C.toPDesign.ylab r ℓ ∈ C.labs r.1 :=
  C.ylab_range r ℓ

theorem ylabs_len (r : C.toPDesign.YReg) : (C.labs r.1).length ≤ 9 := C.labs_len r.1

/-- A Y-register changes label at most 9 times along the levels. -/
theorem ychanges (r : C.toPDesign.YReg) :
    ((range h).filter fun ℓ => C.toPDesign.ylab r (ℓ + 1) ≠ C.toPDesign.ylab r ℓ).card ≤ 9 := by
  show ((range h).filter fun ℓ => C.ylab r (ℓ + 1) ≠ C.ylab r ℓ).card ≤ 9
  have hsub : ((range h).filter fun ℓ => C.ylab r (ℓ + 1) ≠ C.ylab r ℓ)
      ⊆ ((C.ychain r).map fun A => A.card - 1).toFinset := by
    intro ℓ hℓ
    rw [mem_filter] at hℓ
    rw [List.mem_toFinset, List.mem_map]
    by_contra hno
    push Not at hno
    apply hℓ.2
    ext x
    simp only [ylab, mem_lunion, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨A, ⟨hA, hc⟩, hx⟩
      refine ⟨A, ⟨hA, ?_⟩, hx⟩
      have h4 := (C.labs_card r.1 A (C.mem_ychain.1 hA).1).1
      have := hno A hA
      omega
    · rintro ⟨A, ⟨hA, hc⟩, hx⟩
      exact ⟨A, ⟨hA, by omega⟩, hx⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ((C.ychain r).map fun A => A.card - 1).length := List.toFinset_card_le _
    _ = (C.ychain r).length := List.length_map _
    _ ≤ (C.labs r.1).length := List.length_filter_le _ _
    _ ≤ 9 := C.labs_len r.1

end CoordSpec
end PowerSaving.Colour
end OAI
