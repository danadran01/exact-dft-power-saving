import OAI.Computability.FourierTransform.Colour.CoordDesign
import OAI.Computability.FourierTransform.Colour.CoordCheck

/-!
# Colour network, C16 (part 3): from kernel-checked `Nat` data to a coordinate design (new)

Soundness ("bridge") of the kernel checker `CoordCheck.lean`. If `D : CData` passes the three Boolean
checks (`globalOK`, `groupsOK`, `allR elemOK els`), all evaluated by `decide +kernel` in the data
modules `Designs/D*.lean`, then `D.spec` is a `CoordSpec D.h`:
* elements: `j ↦ {x | bit x of m_j}` is a bijection `Fin |els| ≃ Trip h` (masks strictly increasing,
  popcount 3, `|els| = C(h,3)`), and the `C_x` are its columns;
* group `g`: readers `{S | bit (idx S) of R_g}`, labels `{x | bit x of L_i}`;
* hints: the valid packed hints of each element.

Then (`D.coordDesign : PDesign D.h PDesign.disjointP`, by `CoordSpec.toPDesign`):
* `card XReg ≤ D.nX`, `card YReg ≤ Σ_g pcT d R_g`, and `card Side ≤ D.nS`, because every uncovered disjoint
  pair is a listed side pair (the per-element bitset identity of `elemOK`).
-/

namespace OAI
namespace PowerSaving.Colour
namespace CC
open Finset

/-! ### Bit-level lemmas for the checker functions -/

lemma bit_eq_one_iff (a i : ℕ) : (a >>> i) % 2 = 1 ↔ a.testBit i = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_iff]

lemma bit_val (a i : ℕ) : (a >>> i) % 2 = if a.testBit i then 1 else 0 := by
  by_cases hb : a.testBit i = true
  · rw [if_pos hb]; exact (bit_eq_one_iff a i).2 hb
  · rw [if_neg hb]
    have := Nat.mod_two_eq_zero_or_one (a >>> i)
    rcases this with e | e
    · exact e
    · exact absurd ((bit_eq_one_iff a i).1 e) hb

lemma bit_eq_iff (a i b k : ℕ) : (a >>> i) % 2 = (b >>> k) % 2 ↔ a.testBit i = b.testBit k := by
  rw [bit_val, bit_val]
  cases a.testBit i <;> cases b.testBit k <;> simp

lemma testBit_one_shiftLeft (t s : ℕ) : (1 <<< t).testBit s = decide (t = s) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

lemma testBit_full (v s : ℕ) : (2 ^ v - 1).testBit s = decide (s < v) := Nat.testBit_two_pow_sub_one v s

lemma colAux_spec {m j : ℕ} {Cs : List ℕ} {x : ℕ} (hc : colAux m j Cs x = true) :
    ∀ i < Cs.length, (Cs.getD i 0).testBit j = m.testBit (x + i) := by
  induction Cs generalizing x with
  | nil => intro i hi; simp at hi
  | cons C Cs ih =>
    rw [colAux_cons, Bool.and_eq_true] at hc
    intro i hi
    cases i with
    | zero => simpa using (bit_eq_iff C j m x).1 (Nat.eq_of_beq_eq_true hc.1)
    | succ i =>
      have := ih hc.2 i (by simp at hi; omega)
      simp only [List.getD_cons_succ]
      rw [this]; congr 1; omega

lemma nbhdAux_spec (L : ℕ) (Cs : List ℕ) (x s : ℕ) :
    (nbhdAux L Cs x).testBit s = true ↔
      ∃ i < Cs.length, L.testBit (x + i) = true ∧ (Cs.getD i 0).testBit s = true := by
  induction Cs generalizing x with
  | nil => simp [nbhdAux_nil]
  | cons C Cs ih =>
    rw [nbhdAux_cons, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h1 | ⟨i, hi, h2, h3⟩)
      · by_cases hL : Nat.beq ((L >>> x) % 2) 1 = true
        · rw [hL] at h1
          refine ⟨0, by simp, ?_, by simpa using h1⟩
          simpa using (bit_eq_one_iff L x).1 (Nat.eq_of_beq_eq_true hL)
        · rw [Bool.not_eq_true] at hL; rw [hL] at h1; simp at h1
      · refine ⟨i + 1, by simp; omega, by rw [show x + (i + 1) = x + 1 + i by omega]; exact h2, ?_⟩
        simpa using h3
    · rintro ⟨i, hi, h2, h3⟩
      cases i with
      | zero =>
        left
        have hb : Nat.beq ((L >>> x) % 2) 1 = true :=
          cast Nat.beq_eq.symm ((bit_eq_one_iff L x).2 (by simpa using h2))
        rw [hb]; simpa using h3
      | succ i =>
        right
        exact ⟨i, by simp at hi; omega, by rw [show x + 1 + i = x + (i + 1) by omega]; exact h2,
          by simpa using h3⟩

lemma popc_spec (n x : ℕ) : popc n x = ∑ i ∈ range n, if x.testBit i then 1 else 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [popc_succ, ih, Finset.sum_range_succ', add_comm]
    congr 1
    · apply sum_congr rfl; intro i _; rw [Nat.testBit_div_two]
    · rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one x with e | e <;> simp [e]

lemma pcT_spec (d x : ℕ) : pcT d x = ∑ i ∈ range (2 ^ d), if x.testBit i then 1 else 0 := by
  induction d generalizing x with
  | zero => rw [pcT_zero]; simp only [pow_zero, range_one, sum_singleton, Nat.testBit_zero];
            rcases Nat.mod_two_eq_zero_or_one x with e | e <;> simp [e]
  | succ d ih =>
    rw [pcT_succ, ih, ih, pow_succ, mul_two, Finset.sum_range_add]
    congr 1
    · apply sum_congr rfl; intro i hi
      rw [mem_range] at hi
      rw [Nat.testBit_mod_two_pow]; simp [hi]
    · apply sum_congr rfl; intro i _
      rw [Nat.testBit_div_two_pow, add_comm]

lemma sideBits_spec (l : List ℕ) (s : ℕ) : (sideBits l).testBit s = true ↔ s ∈ l := by
  induction l with
  | nil => simp [sideBits_nil]
  | cons t l ih =>
    rw [sideBits_cons, Nat.testBit_or, Bool.or_eq_true, ih, testBit_one_shiftLeft, List.mem_cons,
      decide_eq_true_iff, eq_comm]

lemma rowOf_spec {G : ℕ} {gt : GTree} {m s : ℕ} {l : List ℕ} (hr : (rowOf G gt m l).testBit s = true) :
    ∃ e ∈ l, (hintY G gt m e).testBit s = true := by
  induction l with
  | nil => simp [rowOf_nil] at hr
  | cons e l ih =>
    rw [rowOf_cons, Nat.testBit_or, Bool.or_eq_true] at hr
    rcases hr with h1 | h2
    · exact ⟨e, List.mem_cons_self, h1⟩
    · obtain ⟨e', he', h⟩ := ih h2; exact ⟨e', List.mem_cons_of_mem _ he', h⟩

lemma hintY_spec {G : ℕ} {gt : GTree} {m e s : ℕ} (hy : (hintY G gt m e).testBit s = true) :
    e / 16 < G ∧ m &&& (hintLab gt e).1 = m ∧ (hintLab gt e).2.testBit s = true := by
  unfold hintY at hy
  cases hc : (Nat.blt (e / 16) G && Nat.beq (m &&& (hintLab gt e).1) m)
  · rw [hc] at hy; simp at hy
  · rw [hc] at hy
    rw [Bool.and_eq_true] at hc
    exact ⟨cast Nat.blt_eq hc.1, Nat.eq_of_beq_eq_true hc.2, hy⟩

lemma unpackAux_length (n x : ℕ) : (unpackAux n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [unpackAux_succ, List.length_cons, ih]

lemma unpack_length (p : ℕ) : (unpack p).length = p % 256 := unpackAux_length _ _

lemma nthD_of_ge {l : List (ℕ × ℕ)} {n : ℕ} (hn : l.length ≤ n) : nthD l n = (0, 0) := by
  induction l generalizing n with
  | nil => rfl
  | cons p l ih =>
    cases n with
    | zero => simp at hn
    | succ n => rw [nthD_succ]; exact ih (by simp at hn; omega)

lemma nthD_of_lt {l : List (ℕ × ℕ)} {n : ℕ} (hn : n < l.length) : nthD l n = l[n] := by
  induction l generalizing n with
  | nil => simp at hn
  | cons p l ih =>
    cases n with
    | zero => rfl
    | succ n => rw [nthD_succ]; exact ih (by simp at hn; omega)

/-- `m ⊆ L` as bitmasks. -/
def msub (a b : ℕ) : Prop := a &&& b = a

lemma msub_trans {a b c : ℕ} (h1 : msub a b) (h2 : msub b c) : msub a c := by
  unfold msub at *
  rw [← h1, Nat.land_assoc, h2]

lemma msub_bit {a b i : ℕ} (h : msub a b) (ha : a.testBit i = true) : b.testBit i = true := by
  unfold msub at h
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at ha
  exact ha.2

/-! ### The Boolean checks, unpacked -/

lemma allR_spec {α : Type} {f : α → Bool} {l : List α} (h : allR f l = true) : ∀ a ∈ l, f a = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [allR_cons, Bool.and_eq_true] at h
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact ih h.2 b hb

lemma idxOK_spec {l : List Elem} {s : ℕ} (h : CData.idxOK l s = true) :
    ∀ i (hi : i < l.length), l[i].1 = s + i := by
  induction l generalizing s with
  | nil => intro i hi; simp at hi
  | cons e l ih =>
    simp only [CData.idxOK, Bool.and_eq_true] at h
    intro i hi
    cases i with
    | zero => simpa using Nat.eq_of_beq_eq_true h.1
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [ih h.2 i (by simp at hi; omega)]; omega

lemma sortedOK_cons {a : Elem} {l : List Elem} (h : CData.sortedOK (a :: l) = true) :
    (∀ x ∈ l, a.2.1 < x.2.1) ∧ CData.sortedOK l = true := by
  induction l generalizing a with
  | nil => simp [CData.sortedOK]
  | cons b l ih =>
    simp only [CData.sortedOK, Bool.and_eq_true] at h
    have hab : a.2.1 < b.2.1 := cast Nat.blt_eq h.1
    obtain ⟨h1, _⟩ := ih h.2
    refine ⟨?_, h.2⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hab
    · exact lt_trans hab (h1 x hx)

lemma sortedOK_spec {l : List Elem} (h : CData.sortedOK l = true) : (l.map fun e => e.2.1).Pairwise (· < ·) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := sortedOK_cons h
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih h2⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact h1 x hx

/-- Facts of one label of a group (from `labsOK`). -/
def LabFacts (D : CData) (R : ℕ) (p : ℕ × ℕ) : Prop :=
  4 ≤ popc D.h p.1 ∧ popc D.h p.1 + 4 ≤ D.h ∧ p.2 = R &&& (D.full ^^^ nbhdAux p.1 D.Cs 0)

lemma labsOK_spec {D : CData} {R prev : ℕ} {l : List (ℕ × ℕ)} (h : D.labsOK R prev l = true) :
    (∀ p ∈ l, LabFacts D R p ∧ msub prev p.1) ∧ l.Pairwise (fun a b => msub a.1 b.1) := by
  induction l generalizing prev with
  | nil => simp
  | cons p l ih =>
    simp only [CData.labsOK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨_, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    obtain ⟨hl1, hl2⟩ := ih h8
    have hp : LabFacts D R p ∧ msub prev p.1 :=
      ⟨⟨Nat.le_of_ble_eq_true h4, Nat.le_of_ble_eq_true h5, Nat.eq_of_beq_eq_true h7⟩,
        Nat.eq_of_beq_eq_true h6⟩
    refine ⟨?_, List.pairwise_cons.2 ⟨fun q hq => (hl1 q hq).2, hl2⟩⟩
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hp
    · exact ⟨(hl1 q hq).1, msub_trans hp.2 (hl1 q hq).2⟩

/-! ### Validity and the derived design -/

/-- The kernel-checked hypotheses on the data. -/
structure CData.Valid (D : CData) : Prop where
  hh : 4 ≤ D.h
  hv : D.v = D.h.choose 3
  glob : D.globalOK = true
  grp : D.groupsOK = true
  el : allR D.elemOK D.els = true

/-- The coordinates of a mask. -/
def CData.maskSet (h m : ℕ) : Finset (Fin h) := univ.filter fun x => m.testBit x

lemma CData.card_maskSet (h m : ℕ) : (maskSet h m).card = popc h m := by
  rw [CData.maskSet, card_filter, popc_spec, ← Fin.sum_univ_eq_sum_range (fun i => if m.testBit i then 1 else 0)]

lemma CData.maskSet_mono {h a b : ℕ} (hs : msub a b) : maskSet h a ⊆ maskSet h b := by
  intro x hx; simp only [CData.maskSet, mem_filter, mem_univ, true_and] at hx ⊢; exact msub_bit hs hx

/-- Validity of a hint `e` for the element of mask `m`. -/
def CData.hvalid (D : CData) (m e : ℕ) : Prop := e / 16 < D.G ∧ m &&& (hintLab D.gt e).1 = m

noncomputable instance (D : CData) (m e : ℕ) : Decidable (D.hvalid m e) := by
  unfold CData.hvalid; infer_instance

/-- Decoded hints of an element. -/
noncomputable def CData.hintsOf (D : CData) (m hp : ℕ) : List (Fin D.G × ℕ) :=
  (unpack hp).filterMap fun e => if hv : D.hvalid m e then some (⟨e / 16, hv.1⟩, e % 16) else none

lemma popc_zero_right (n : ℕ) : popc n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [popc_succ, ih]

lemma CData.mem_hintsOf {D : CData} {m hp : ℕ} {p : Fin D.G × ℕ} (h : p ∈ D.hintsOf m hp) :
    ∃ e ∈ unpack hp, D.hvalid m e ∧ (p.1 : ℕ) = e / 16 ∧ p.2 = e % 16 := by
  obtain ⟨e, he, hs⟩ := List.mem_filterMap.1 h
  by_cases hv : D.hvalid m e
  · rw [dif_pos hv] at hs
    cases hs
    exact ⟨e, he, hv, rfl, rfl⟩
  · rw [dif_neg hv] at hs; cases hs

lemma CData.hint_lt_of_valid {D : CData} {m e : ℕ} (hv : D.hvalid m e) (hm : popc D.h m = 3) :
    e % 16 < (D.gt.get (e / 16)).2.length := by
  by_contra hge
  push Not at hge
  have h0 := hv.2
  rw [show hintLab D.gt e = (0, 0) from nthD_of_ge hge, Nat.and_zero] at h0
  rw [← h0, popc_zero_right] at hm
  exact absurd hm (by decide)

namespace CData
variable (D : CData) (hD : D.Valid)
include hD

lemma len_els : D.els.length = D.v := by
  have := hD.glob; simp only [globalOK, Bool.and_eq_true] at this
  exact Nat.eq_of_beq_eq_true this.1.1.1

lemma len_Cs : D.Cs.length = D.h := by
  have := hD.glob; simp only [globalOK, Bool.and_eq_true] at this
  exact Nat.eq_of_beq_eq_true this.1.1.2

lemma idx_eq (j : Fin D.els.length) : (D.els[j]).1 = j := by
  have := hD.glob; simp only [globalOK, Bool.and_eq_true] at this
  have h := idxOK_spec this.1.2 j.1 j.2
  rw [zero_add] at h
  exact h

lemma mask_inj {i j : Fin D.els.length} (e : (D.els[i]).2.1 = (D.els[j]).2.1) : i = j := by
  have := hD.glob; simp only [globalOK, Bool.and_eq_true] at this
  have hnd := (sortedOK_spec this.2).imp (fun h => ne_of_lt h)
  have hnd' : (D.els.map fun e => e.2.1).Nodup := hnd
  have := (hnd'.getElem_inj_iff (i := i) (j := j) (hi := by simp) (hj := by simp)).1 (by simpa using e)
  exact Fin.ext this

lemma elem_ok (j : Fin D.els.length) : D.elemOK D.els[j] = true :=
  allR_spec hD.el _ (List.getElem_mem _)

/-- Facts of an element record (from `elemOK`). -/
lemma elem_facts (j : Fin D.els.length) :
    (D.els[j]).2.1 < 2 ^ D.h ∧ popc D.h (D.els[j]).2.1 = 3 ∧ colAux (D.els[j]).2.1 j D.Cs 0 = true ∧
      ((nbhdAux (D.els[j]).2.1 D.Cs 0 ||| rowOf D.G D.gt (D.els[j]).2.1 (unpack (D.els[j]).2.2.1)
        ||| sideBits (unpack (D.els[j]).2.2.2)) &&& D.full) = D.full := by
  have := D.elem_ok hD j
  simp only [elemOK, Bool.and_eq_true] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  refine ⟨cast Nat.blt_eq h1, Nat.eq_of_beq_eq_true h2, ?_, Nat.eq_of_beq_eq_true h4⟩
  rw [D.idx_eq hD j] at h3; exact h3

/-- The triple with index `j`. -/
def elem (j : Fin D.els.length) : Trip D.h :=
  ⟨maskSet D.h (D.els[j]).2.1, mem_powersetCard.2 ⟨subset_univ _, by
    rw [card_maskSet]; exact (D.elem_facts hD j).2.1⟩⟩

lemma elem_inj : Function.Injective (D.elem hD) := by
  intro i j e
  apply D.mask_inj hD
  have hs : maskSet D.h (D.els[i]).2.1 = maskSet D.h (D.els[j]).2.1 := congrArg Subtype.val e
  apply Nat.eq_of_testBit_eq
  intro x
  by_cases hx : x < D.h
  · have := congrArg (fun A => (⟨x, hx⟩ : Fin D.h) ∈ A) hs
    simpa [maskSet] using this
  · push Not at hx
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (D.elem_facts hD i).1 (Nat.pow_le_pow_right (by norm_num) hx)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (D.elem_facts hD j).1 (Nat.pow_le_pow_right (by norm_num) hx))]

/-- Element indices are a bijection onto the triples. -/
noncomputable def eqv : Fin D.els.length ≃ Trip D.h :=
  Equiv.ofBijective (D.elem hD) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨D.elem_inj hD, by rw [Fintype.card_fin, num_trip, D.len_els hD, hD.hv]⟩)

/-- Index of a triple. -/
noncomputable def idx (T : Trip D.h) : Fin D.els.length := (D.eqv hD).symm T

lemma elem_idx (T : Trip D.h) : D.elem hD (D.idx hD T) = T := (D.eqv hD).apply_symm_apply T

lemma mem_iff_bit (T : Trip D.h) (x : Fin D.h) : x ∈ T.val ↔ (D.els[D.idx hD T]).2.1.testBit x = true := by
  conv_lhs => rw [← D.elem_idx hD T]
  simp [elem, maskSet]

/-- Columns: bit `idx S` of `C_x` is `x ∈ S`. -/
lemma col_bit (S : Trip D.h) (x : Fin D.h) : (D.Cs.getD x 0).testBit (D.idx hD S) = true ↔ x ∈ S.val := by
  rw [D.mem_iff_bit hD S x, colAux_spec (D.elem_facts hD (D.idx hD S)).2.2.1 x (by rw [D.len_Cs hD]; exact x.2),
    zero_add]

/-- Neighbourhood bitsets: bit `idx S` of `N(L)` is `S ∩ L ≠ ∅`. -/
lemma nbhd_bit (L : ℕ) (S : Trip D.h) :
    (nbhdAux L D.Cs 0).testBit (D.idx hD S) = true ↔ ¬ Disjoint S.val (maskSet D.h L) := by
  rw [nbhdAux_spec, not_disjoint_iff]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    rw [D.len_Cs hD] at hi
    refine ⟨⟨i, hi⟩, (D.col_bit hD S ⟨i, hi⟩).1 h2, ?_⟩
    simpa [maskSet] using h1
  · rintro ⟨x, hxS, hxL⟩
    refine ⟨x, by rw [D.len_Cs hD]; exact x.2, by simpa [maskSet] using hxL, (D.col_bit hD S x).2 hxS⟩

/-! #### Groups -/

lemma grp_facts (g : Fin D.G) :
    (D.gt.get g).2.length ≤ 9 ∧ (∀ p ∈ (D.gt.get g).2, LabFacts D (D.gt.get g).1 p) ∧
      (D.gt.get g).2.Pairwise (fun a b => msub a.1 b.1) := by
  have := hD.grp
  simp only [groupsOK, List.all_eq_true, List.mem_range] at this
  have hg := this g g.2
  simp only [grpOK, Bool.and_eq_true] at hg
  obtain ⟨h1, h2⟩ := labsOK_spec hg.2
  exact ⟨Nat.le_of_ble_eq_true hg.1, fun p hp => (h1 p hp).1, h2⟩

lemma spec_hint_lt (T : Trip D.h) (p : Fin D.G × ℕ)
    (hp : p ∈ D.hintsOf (D.els[D.idx hD T]).2.1 (D.els[D.idx hD T]).2.2.1) :
    p.2 < ((D.gt.get p.1).2.map fun q => maskSet D.h q.1).length := by
  obtain ⟨e, -, hv, h1, h2⟩ := CData.mem_hintsOf hp
  rw [List.length_map, h1, h2]
  exact CData.hint_lt_of_valid hv (D.elem_facts hD (D.idx hD T)).2.1

lemma spec_hint_sub (T : Trip D.h) (p : Fin D.G × ℕ)
    (hp : p ∈ D.hintsOf (D.els[D.idx hD T]).2.1 (D.els[D.idx hD T]).2.2.1) :
    T.val ⊆ ((D.gt.get p.1).2.map fun q => maskSet D.h q.1).getD p.2 ∅ := by
  obtain ⟨e, -, hv, h1, h2⟩ := CData.mem_hintsOf hp
  have hlt := CData.hint_lt_of_valid hv (D.elem_facts hD (D.idx hD T)).2.1
  rw [h1, h2, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt), List.getElem_map,
    ← nthD_of_lt hlt]
  intro x hx
  have : (hintLab D.gt e).1.testBit x = true := msub_bit hv.2 ((D.mem_iff_bit hD T x).1 hx)
  simp only [maskSet, mem_filter, mem_univ, true_and]
  exact this

lemma spec_labs_nest (g : Fin D.G) :
    ((D.gt.get g).2.map fun p => maskSet D.h p.1).Pairwise (· ⊆ ·) := by
  rw [List.pairwise_map]
  exact (D.grp_facts hD g).2.2.imp fun h => maskSet_mono h

lemma spec_labs_card (g : Fin D.G) (A : Finset (Fin D.h))
    (hA : A ∈ (D.gt.get g).2.map fun p => maskSet D.h p.1) : 4 ≤ A.card ∧ A.card + 4 ≤ D.h := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hA
  have := (D.grp_facts hD g).2.1 p hp
  rw [card_maskSet]; exact ⟨this.1, this.2.1⟩

lemma spec_labs_len (g : Fin D.G) : ((D.gt.get g).2.map fun p => maskSet D.h p.1).length ≤ 9 := by
  rw [List.length_map]; exact (D.grp_facts hD g).1

/-- **The coordinate design data** decoded from `D`. -/
noncomputable def spec : CoordSpec D.h where
  G := D.G
  R g := univ.filter fun S : Trip D.h => (D.gt.get g).1.testBit (D.idx hD S)
  labs g := (D.gt.get g).2.map fun p => maskSet D.h p.1
  hints T := D.hintsOf (D.els[D.idx hD T]).2.1 (D.els[D.idx hD T]).2.2.1
  hh := hD.hh
  labs_nest g := D.spec_labs_nest hD g
  labs_card g A hA := D.spec_labs_card hD g A hA
  labs_len g := D.spec_labs_len hD g
  hint_lt T p hp := D.spec_hint_lt hD T p hp
  hint_sub := by
    intro T p hp
    have h := D.spec_hint_sub hD T p hp
    exact h

/-- **Coverage**: every disjoint pair is covered by a hint or listed as a side pair. -/
noncomputable def sidesOf (T : Trip D.h) : List (Trip D.h) :=
  (unpack (D.els[D.idx hD T]).2.2.2).filterMap fun s =>
    if hs : s < D.els.length then some (D.elem hD ⟨s, hs⟩) else none

theorem cover_or_side (T S : Trip D.h) (hm : meet T S = 0) :
    (D.spec hD).covered T S ∨ S ∈ D.sidesOf hD T := by
  set j := D.idx hD T
  set s := D.idx hD S
  have hf := (D.elem_facts hD j).2.2.2
  have hs : s.1 < D.v := by rw [← D.len_els hD]; exact s.2
  have hbit := congrArg (fun z => z.testBit s) hf
  simp only [Nat.testBit_and, full, testBit_full, decide_eq_true hs, Bool.and_true, Nat.testBit_or,
    Bool.or_eq_true] at hbit
  rcases hbit with (hn | hr) | hsd
  · exfalso
    have hT : maskSet D.h (D.els[j]).2.1 = T.val := congrArg Subtype.val (D.elem_idx hD T)
    have := (D.nbhd_bit hD _ S).1 hn
    rw [hT] at this
    apply this
    rw [disjoint_iff_inter_eq_empty, inter_comm, ← card_eq_zero]
    exact hm
  · left
    obtain ⟨e, he, hy⟩ := rowOf_spec hr
    obtain ⟨hg, hsub, hY⟩ := hintY_spec hy
    have hlt : e % 16 < (D.gt.get (e / 16)).2.length :=
      CData.hint_lt_of_valid (D := D) ⟨hg, hsub⟩ (D.elem_facts hD j).2.1
    have hlab : hintLab D.gt e = (D.gt.get (e / 16)).2[e % 16] := nthD_of_lt hlt
    have hfacts := (D.grp_facts hD ⟨e / 16, hg⟩).2.1 _ (List.getElem_mem hlt)
    rw [← hlab] at hfacts
    have hY' := hfacts.2.2
    rw [hY', Nat.testBit_and, Bool.and_eq_true, Nat.testBit_xor, full, testBit_full, decide_eq_true hs] at hY
    have hp : (⟨⟨e / 16, hg⟩, e % 16⟩ : Fin D.G × ℕ) ∈ (D.spec hD).hints T := by
      show _ ∈ D.hintsOf _ _
      refine List.mem_filterMap.2 ⟨e, he, ?_⟩
      rw [dif_pos ⟨hg, hsub⟩]
    refine (D.spec hD).covered_of_mem hp ?_ ?_
    · show S ∈ univ.filter fun S : Trip D.h => (D.gt.get (e / 16)).1.testBit (D.idx hD S)
      simpa using hY.1
    · show Disjoint S.val (((D.gt.get (e / 16)).2.map fun p => maskSet D.h p.1).getD (e % 16) ∅)
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt), List.getElem_map, ← hlab]
      have hnb : (nbhdAux (hintLab D.gt e).1 D.Cs 0).testBit s = false := by
        have := hY.2; simpa using this
      by_contra hc
      have := (D.nbhd_bit hD (hintLab D.gt e).1 S).2 hc
      rw [hnb] at this; exact absurd this (by decide)
  · right
    rw [sideBits_spec] at hsd
    refine List.mem_filterMap.2 ⟨s, hsd, ?_⟩
    rw [dif_pos s.2]
    exact congrArg some (D.elem_idx hD S)

/-! #### The design and its counts -/

/-- **The coordinate partial design** of the data `D`. -/
noncomputable def coordDesign : PDesign D.h PDesign.disjointP := (D.spec hD).toPDesign

lemma sum_trip_eq (f : Fin D.els.length → ℕ) : ∑ T : Trip D.h, f (D.idx hD T) = ∑ j, f j :=
  Fintype.sum_equiv (D.eqv hD).symm _ _ (fun _ => rfl)

omit hD in
lemma sum_els (f : Elem → ℕ) : ∑ j : Fin D.els.length, f D.els[j] = (D.els.map f).sum := by
  rw [← Fin.sum_univ_getElem (D.els.map f)]
  exact Fintype.sum_equiv (finCongr (List.length_map f).symm) _ _ (fun j => by simp)

theorem card_XReg_le : Fintype.card (D.coordDesign hD).XReg ≤ D.nX := by
  rw [coordDesign, CoordSpec.card_XReg]
  calc ∑ T, ((D.spec hD).hints T).length
      ≤ ∑ T : Trip D.h, (D.els[D.idx hD T]).2.2.1 % 256 := by
        apply sum_le_sum; intro T _
        show (D.hintsOf _ _).length ≤ _
        rw [← unpack_length]; exact List.length_filterMap_le _ _
    _ = D.nX := by
        rw [D.sum_trip_eq hD (fun j => (D.els[j]).2.2.1 % 256), D.sum_els (fun e => e.2.2.1 % 256)]; rfl

theorem card_Side_le : Fintype.card (D.coordDesign hD).Side ≤ D.nS := by
  rw [coordDesign]
  refine ((D.spec hD).card_Side_le (D.sidesOf hD) ?_).trans ?_
  · intro T S hm hc
    exact (D.cover_or_side hD T S hm).resolve_left hc
  · calc ∑ T, (D.sidesOf hD T).length
        ≤ ∑ T : Trip D.h, (D.els[D.idx hD T]).2.2.2 % 256 := by
          apply sum_le_sum; intro T _
          rw [← unpack_length]; exact List.length_filterMap_le _ _
      _ = D.nS := by
          rw [D.sum_trip_eq hD (fun j => (D.els[j]).2.2.2 % 256), D.sum_els (fun e => e.2.2.2 % 256)]; rfl

theorem card_YReg_le (d : ℕ) (hd : D.v ≤ 2 ^ d) :
    Fintype.card (D.coordDesign hD).YReg ≤ ((List.range D.G).map fun g => pcT d (D.gt.get g).1).sum := by
  rw [coordDesign, CoordSpec.card_YReg, RegisterDesign.list_sum_range, ← Fin.sum_univ_eq_sum_range]
  apply sum_le_sum; intro g _
  show (univ.filter fun S : Trip D.h => (D.gt.get g).1.testBit (D.idx hD S)).card ≤ _
  rw [pcT_spec, ← card_filter]
  calc (univ.filter fun S : Trip D.h => (D.gt.get g).1.testBit (D.idx hD S)).card
      = (univ.filter fun j : Fin D.els.length => (D.gt.get g).1.testBit j).card := by
        apply card_bij (fun S _ => D.idx hD S)
        · intro S hS; simpa using hS
        · intro S _ S' _ e; exact (D.eqv hD).symm.injective e
        · intro j hj
          refine ⟨D.eqv hD j, ?_, by simp [idx]⟩
          rw [mem_filter] at hj ⊢
          refine ⟨mem_univ _, ?_⟩
          show (D.gt.get g).1.testBit ((D.eqv hD).symm (D.eqv hD j)) = true
          rw [Equiv.symm_apply_apply]; exact hj.2
    _ ≤ ((range (2 ^ d)).filter fun i => (D.gt.get g).1.testBit i).card := by
        apply card_le_card_of_injOn (fun j => j.1)
        · intro j hj
          simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hj
          simp only [coe_filter, mem_range, Set.mem_setOf_eq]
          exact ⟨lt_of_lt_of_le j.2 (by rw [D.len_els hD]; exact hd), hj⟩
        · intro a _ b _ e; exact Fin.ext e

end CData
end CC
end PowerSaving.Colour
end OAI
