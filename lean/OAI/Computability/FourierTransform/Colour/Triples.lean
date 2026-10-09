import OAI.Computability.FourierTransform.Colour.Tensor

/-!
# Colour network, part 2: triples on `Fin h` and their bases (new)

Factor-level data of the triple family for an arbitrary size `h` (the colour network uses
`h ∈ {30, 20, 41}`). Unlike OpenAI's `NetworkRoles` (triples on 30 of 32 coordinates, two fixed
pivot coordinates), the triples here use *all* coordinates, so `m = h₁h₂h₃`. The pivot of a triple
is a coordinate outside it, and the bases are reindexed so that the triple indicator sits at
index `0` (`tripBase`), resp. the two indicators of an orthogonal pair at `0` and `1` (`pairBase`).
-/

namespace OAI
namespace PowerSaving.Colour
open Finset Matrix Binary

variable {h : ℕ}

def tripSet (h : ℕ) : Finset (Finset (Fin h)) := (univ : Finset (Fin h)).powersetCard 3
abbrev Trip (h : ℕ) := ↑(tripSet h)

lemma trip_card (T : Trip h) : T.val.card = 3 := (mem_powersetCard.mp T.property).2

lemma num_trip : Fintype.card (Trip h) = h.choose 3 := by
  rw [Fintype.card_coe]
  show (tripSet h).card = _
  unfold tripSet
  rw [card_powersetCard, card_univ, Fintype.card_fin]

lemma trip_nonempty (T : Trip h) : T.val.Nonempty :=
  card_pos.mp (by rw [trip_card]; norm_num)

/-- Indicator of a triple. -/
def tip (T : Trip h) : Space (Fin h) := ind T.val

lemma tip_apply (T : Trip h) (i : Fin h) : tip T i = if i ∈ T.val then 1 else 0 := rfl

def meet (T S : Trip h) : ℕ := (T.val ∩ S.val).card

/-- Orthogonal triples (even intersection). Neighbours are automatically distinct. -/
def neighbor (T S : Trip h) : Prop := meet T S = 0 ∨ meet T S = 2

instance (T S : Trip h) : Decidable (neighbor T S) := by unfold neighbor; infer_instance

lemma meet_comm (T S : Trip h) : meet T S = meet S T := by simp [meet, inter_comm]

lemma meet_self (T : Trip h) : meet T T = 3 := by simp [meet, trip_card]

lemma meet_le (T S : Trip h) (hne : T ≠ S) : meet T S ≤ 2 := by
  unfold meet
  by_contra he
  have hi := card_le_card (inter_subset_left (s₁ := T.val) (s₂ := S.val))
  have hh : (T.val ∩ S.val).card = 3 := by have := trip_card T; omega
  have hx : T.val ∩ S.val = T.val :=
    eq_of_subset_of_card_le inter_subset_left (by simp [hh, trip_card])
  have hy : T.val ∩ S.val = S.val :=
    eq_of_subset_of_card_le inter_subset_right (by simp [hh, trip_card])
  exact hne (Subtype.ext (hx.symm.trans hy))

lemma neighbor_comm (T S : Trip h) : neighbor T S ↔ neighbor S T := by
  simp only [neighbor, meet_comm T S]

lemma neighbor_ne {T S : Trip h} (hn : neighbor T S) : T ≠ S := by
  rintro rfl; rcases hn with e | e <;> rw [meet_self] at e <;> omega

lemma tip_dot (T S : Trip h) : dot (tip T) (tip S) = (meet T S : F) := dot_ind _ _

@[simp] lemma tip_unit (T : Trip h) : dot (tip T) (tip T) = 1 := by
  rw [tip_dot, meet_self]; decide

lemma tip_orth {T S : Trip h} (hn : neighbor T S) : dot (tip T) (tip S) = 0 := by
  rw [tip_dot]; rcases hn with e | e <;> rw [e] <;> decide

lemma tip_ne_zero (T : Trip h) : tip T ≠ 0 := by
  intro e; have := tip_unit T; rw [e, dot_zero_left] at this; exact zero_ne_one this

/-! ### The pivot of a triple and `tripBase` -/

/-- A coordinate outside the triple (when `h ≥ 4`). -/
def piv (T : Trip h) : Fin h :=
  if hne : (univ \ T.val).Nonempty then (univ \ T.val).min' hne else T.val.min' (trip_nonempty T)

lemma compl_nonempty (T : Trip h) (hh : 4 ≤ h) : (univ \ T.val).Nonempty := by
  rw [← card_pos, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, trip_card]
  omega

lemma piv_not_mem (T : Trip h) (hh : 4 ≤ h) : piv T ∉ T.val := by
  have hne := compl_nonempty T hh
  have := (univ \ T.val).min'_mem hne
  rw [piv, dif_pos hne]
  simpa using this

lemma tip_piv (T : Trip h) (hh : 4 ≤ h) : tip T (piv T) = 0 := by
  simp [tip_apply, piv_not_mem T hh]

/-- `adapt` of the canonical basis at the pivot (before reindexing). -/
def tripBase0 (T : Trip h) : OBase (Fin h) :=
  if hp : tip T (piv T) = 0 then
    OBase.adapt (OBase.canonical (Fin h)) (piv T) (tip T) (tip_unit T)
      (by change dot (tip T) (eu (piv T)) = 0; rw [dot_eu_right]; exact hp)
  else OBase.canonical _

lemma tripBase0_piv (T : Trip h) (hh : 4 ≤ h) : (tripBase0 T).v (piv T) = tip T := by
  unfold tripBase0; rw [dif_pos (tip_piv T hh)]; apply OBase.adapt_pivot

lemma tripBase0_other (T : Trip h) (hh : 4 ≤ h) (i : Fin h) (hi : i ≠ piv T) (hiT : i ∉ T.val) :
    (tripBase0 T).v i = eu i := by
  unfold tripBase0; rw [dif_pos (tip_piv T hh)]
  rw [OBase.adapt_other _ _ _ _ (Ne.symm hi)]
  · rfl
  · change dot (tip T) (eu i) = 0; rw [dot_eu_right]; simp [tip_apply, hiT]

variable [NeZero h]

/-- Orthonormal basis of `F₂^h` whose vector `0` is the triple indicator. -/
def tripBase (T : Trip h) : OBase (Fin h) := reindex (tripBase0 T) (Equiv.swap 0 (piv T))

@[simp] lemma tripBase_main (T : Trip h) (hh : 4 ≤ h) : (tripBase T).v 0 = tip T := by
  simp [tripBase, Equiv.swap_apply_left, tripBase0_piv T hh]

lemma tripBase_other (T : Trip h) (hh : 4 ≤ h) (i : Fin h) (h0 : i ≠ 0) (hp : i ≠ piv T)
    (hiT : i ∉ T.val) : (tripBase T).v i = eu i := by
  simp only [tripBase, reindex_v, Equiv.swap_apply_of_ne_of_ne h0 hp]
  exact tripBase0_other T hh i hp hiT

lemma fin_zero_ne_one (hh : 2 ≤ h) : (0 : Fin h) ≠ 1 := by
  intro e
  have := congrArg Fin.val e
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)] at this
  simp at this

/-! ### Pairs: `pairBase` -/

/-- A second free coordinate, outside both triples, `0` and the pivot of `T` (when `h ≥ 9`). -/
def qpiv (T S : Trip h) : Fin h :=
  if hne : (univ \ (T.val ∪ S.val ∪ {0, piv T})).Nonempty then
    (univ \ (T.val ∪ S.val ∪ {0, piv T})).min' hne else 0

lemma qpiv_spec (T S : Trip h) (hh : 9 ≤ h) :
    qpiv T S ∉ T.val ∧ qpiv T S ∉ S.val ∧ qpiv T S ≠ 0 ∧ qpiv T S ≠ piv T := by
  have hc : (T.val ∪ S.val ∪ {0, piv T}).card ≤ 8 := by
    calc (T.val ∪ S.val ∪ {0, piv T}).card ≤ (T.val ∪ S.val).card + ({0, piv T} : Finset _).card :=
          card_union_le _ _
      _ ≤ (T.val.card + S.val.card) + 2 := by
          gcongr
          · exact card_union_le _ _
          · exact card_insert_le _ _
      _ = 8 := by rw [trip_card, trip_card]
  have hne : (univ \ (T.val ∪ S.val ∪ {0, piv T})).Nonempty := by
    rw [← card_pos, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    omega
  have hm := (univ \ (T.val ∪ S.val ∪ {0, piv T})).min'_mem hne
  rw [qpiv, dif_pos hne]
  simp only [mem_sdiff, mem_univ, mem_union, mem_insert, mem_singleton, true_and, not_or] at hm
  exact ⟨hm.1.1, hm.1.2, hm.2.1, hm.2.2⟩

/-- Conditions under which `pairBase` is the adapted basis. -/
def PairOK (T S : Trip h) : Prop := 9 ≤ h ∧ neighbor T S

instance (T S : Trip h) : Decidable (PairOK T S) := by unfold PairOK; infer_instance

lemma pair_q (T S : Trip h) (hc : PairOK T S) : (tripBase T).v (qpiv T S) = eu (qpiv T S) := by
  obtain ⟨q1, _, q3, q4⟩ := qpiv_spec T S hc.1
  exact tripBase_other T (by have := hc.1; omega) _ q3 q4 q1

def pairBase0 (T S : Trip h) : OBase (Fin h) :=
  if hc : PairOK T S then
    OBase.adapt (tripBase T) (qpiv T S) (tip S) (tip_unit S)
      (by rw [pair_q T S hc, dot_eu_right, tip_apply]; simp [(qpiv_spec T S hc.1).2.1])
  else tripBase T

/-- Orthonormal basis whose vectors `0` and `1` are the indicators of the orthogonal pair `T, S`. -/
def pairBase (T S : Trip h) : OBase (Fin h) := reindex (pairBase0 T S) (Equiv.swap 1 (qpiv T S))

lemma pairBase_left (T S : Trip h) (hc : PairOK T S) : (pairBase T S).v 0 = tip T := by
  have hh := hc.1
  obtain ⟨_, _, q3, _⟩ := qpiv_spec T S hh
  have h01 : (0 : Fin h) ≠ 1 := fin_zero_ne_one (by omega)
  simp only [pairBase, reindex_v, Equiv.swap_apply_of_ne_of_ne h01 (Ne.symm q3)]
  unfold pairBase0; rw [dif_pos hc]
  rw [OBase.adapt_other _ _ _ _ q3]
  · exact tripBase_main T (by omega)
  · rw [tripBase_main T (by omega), dot_symm]; exact tip_orth hc.2

lemma pairBase_right (T S : Trip h) (hc : PairOK T S) : (pairBase T S).v 1 = tip S := by
  simp only [pairBase, reindex_v, Equiv.swap_apply_left]
  unfold pairBase0; rw [dif_pos hc]
  apply OBase.adapt_pivot

end PowerSaving.Colour
end OAI
