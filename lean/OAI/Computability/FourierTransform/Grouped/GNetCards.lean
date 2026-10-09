import OAI.Computability.FourierTransform.Grouped.GNetPaths
import OAI.Computability.FourierTransform.NetworkStages

/-!
# Sizes of OpenAI's network labels (new; not part of OpenAI's development)

Cardinalities of the masks used by OpenAI's invocation labels (`NetworkRoles`, `NetworkLabels`),
of the differences between consecutive labels, and the number of neighbour side pairs
(`4060 · 3006`). Everything is symbolic: no enumeration of the `32^3` addresses.
`sum_stamp` splits a sum over the `Box` roles of one invocation into its five role classes.
-/

namespace OAI
namespace PowerSaving.Cluster
open Finset Binary

/-! ### Label sizes -/

lemma card_rect (j : J) (e : Bool) (s : Finset H) :
    (rect j e s).card = s.card * (if e then 32^j.val else 1) := by
  rw [rect, Fintype.card_piFinset, Fin.prod_univ_three]
  fin_cases j <;> cases e <;> simp [sets, mul_comm]

lemma rect_false_sub (j : J) (s : Finset H) : rect j false s ⊆ rect j true s := by
  intro k hk
  simp only [mem_rect] at *
  exact ⟨hk.1, by simp, hk.2.2⟩

lemma card_big (j : J) : (big j).card = 32 * 32^j.val := by
  rw [big, card_rect]; simp

lemma card_xstart (j : J) (slot : H) : (xstart j slot).card = 32^j.val := by
  rw [xstart, card_rect]; simp

lemma card_ystart (j : J) (slot : H) : (ystart j slot).card = 32^j.val - 1 := by
  rw [ystart, xstart, card_sdiff_of_subset (rect_false_sub j {slot}), card_rect, card_rect]
  simp

lemma card_belt (j : J) : (belt j).card = 32 * 32^j.val - 32 := by
  rw [belt, card_sdiff_of_subset (rect_le_big j false univ), card_big, card_rect]; simp

lemma card_xstep (j : J) (slot : H) : (xstep j slot).card = 32 * 32^j.val - 31 := by
  rw [xstep, card_sdiff_of_subset (rect_le_big j false _), card_big, card_rect,
    card_sdiff_of_subset (subset_univ _)]
  simp

lemma card_ystep (j : J) (slot : H) : (ystep j slot).card = 32 * 32^j.val - 1 := by
  rw [ystep, card_sdiff_of_subset (rect_le_big j false _), card_big, card_rect]; simp

lemma card_univ_blocks : (univ : Mask).card = 32768 := by
  rw [card_univ, card_block, mcol]; norm_num

lemma card_rest_pole : (univ \ ({pole} : Mask)).card = 32767 := by
  rw [card_sdiff_of_subset (subset_univ _), card_univ_blocks, card_singleton]

/-! ### Inclusions between consecutive labels -/

lemma sub_ystart_belt (j : J) : ystart j 0 ⊆ belt j := by
  intro k hk; rw [in_belt]; rw [in_ystart] at hk; tauto
lemma sub_xstart_xstep (j : J) : xstart j 0 ⊆ xstep j 0 := by
  intro k hk; rw [in_xstep]; rw [in_xstart] at hk; tauto
lemma sub_ystart_xstep (j : J) : ystart j 1 ⊆ xstep j 0 := by
  intro k hk; rw [in_xstep]; rw [in_ystart] at hk; tauto
lemma sub_belt_ystep (j : J) : belt j ⊆ ystep j 0 := by
  intro k hk; rw [in_ystep]; rw [in_belt] at hk; tauto
lemma sub_xstep_ystep (j : J) : xstep j 0 ⊆ ystep j 1 := by
  intro k hk
  rw [in_ystep]
  rw [in_xstep] at hk
  obtain ⟨hf,h|h⟩ := hk
  · tauto
  · exact ⟨hf, Or.inr (by rw [h]; exact piv)⟩
lemma sub_xstep_big (j : J) : xstep j 0 ⊆ big j := sdiff_subset
lemma sub_belt_big (j : J) : belt j ⊆ big j := sdiff_subset
lemma sub_ystep_big (j : J) : ystep j 1 ⊆ big j := sdiff_subset

/-! ### Sizes of the batches (differences of consecutive labels) -/

lemma one_le_e (j : J) : 1 ≤ 32^j.val := Nat.one_le_pow _ _ (by norm_num)

lemma d_belt_ystart (j : J) : (belt j \ ystart j 0).card = 31 * 32^j.val - 31 := by
  rw [card_sdiff_of_subset (sub_ystart_belt j), card_belt, card_ystart]
  have := one_le_e j; generalize 32^j.val = e at *; omega
lemma d_xstep_xstart (j : J) : (xstep j 0 \ xstart j 0).card = 31 * 32^j.val - 31 := by
  rw [card_sdiff_of_subset (sub_xstart_xstep j), card_xstep, card_xstart]
  have := one_le_e j; generalize 32^j.val = e at *; omega
lemma d_xstep_ystart (j : J) : (xstep j 0 \ ystart j 1).card = 31 * 32^j.val - 30 := by
  rw [card_sdiff_of_subset (sub_ystart_xstep j), card_xstep, card_ystart]
  have := one_le_e j; generalize 32^j.val = e at *; omega
lemma d_big_xstep (j : J) : (big j \ xstep j 0).card = 31 := by
  rw [card_sdiff_of_subset (sub_xstep_big j), card_big, card_xstep]
  have := one_le_e j; generalize 32^j.val = e at *; omega
lemma d_ystep_belt (j : J) : (ystep j 0 \ belt j).card = 31 := by
  rw [card_sdiff_of_subset (sub_belt_ystep j), card_ystep, card_belt]
  have := one_le_e j; generalize 32^j.val = e at *; omega
lemma d_ystep_xstep (j : J) : (ystep j 1 \ xstep j 0).card = 30 := by
  rw [card_sdiff_of_subset (sub_xstep_ystep j), card_ystep, card_xstep]
  have := one_le_e j; generalize 32^j.val = e at *; omega
lemma d_big_ystep (j : J) : (big j \ ystep j 1).card = 1 := by
  rw [card_sdiff_of_subset (sub_ystep_big j), card_big, card_ystep]
  have := one_le_e j; generalize 32^j.val = e at *; omega
lemma d_univ_big (j : J) : (univ \ big j).card = 32768 - 32 * 32^j.val := by
  rw [card_sdiff_of_subset (subset_univ _), card_univ_blocks, card_big]

/-! ### Number of neighbour side pairs -/

/-- Sets of size `k` in `S` meeting `a ⊆ S` in exactly `i` points. -/
lemma card_filter_inter {β : Type*} [DecidableEq β] (S a : Finset β) (ha : a ⊆ S) (k i : ℕ)
    (hik : i ≤ k) :
    ((S.powersetCard k).filter (fun b => (a ∩ b).card = i)).card =
      a.card.choose i * (S \ a).card.choose (k - i) := by
  rw [← card_powersetCard i a, ← card_powersetCard (k - i) (S \ a), ← card_product]
  apply card_nbij' (fun b => (a ∩ b, b \ a)) (fun p => p.1 ∪ p.2)
  · intro b hb
    simp only [coe_filter, mem_powersetCard, Set.mem_ofPred_eq] at hb
    simp only [coe_product, Set.mem_prod, mem_coe, mem_powersetCard]
    refine ⟨⟨inter_subset_left, hb.2⟩, sdiff_subset_sdiff hb.1.1 (le_refl _), ?_⟩
    rw [card_sdiff, hb.1.2, hb.2]
  · rintro ⟨x, y⟩ hp
    simp only [coe_product, Set.mem_prod, mem_coe, mem_powersetCard] at hp
    obtain ⟨⟨hx, hxc⟩, ⟨hy, hyc⟩⟩ := hp
    have hya : Disjoint y a := by
      rw [disjoint_left]; intro z hz; exact (mem_sdiff.mp (hy hz)).2
    have hxy : Disjoint x y := disjoint_of_subset_left hx hya.symm
    have hax : a ∩ (x ∪ y) = x := by
      rw [inter_union_distrib_left, inter_eq_right.mpr hx,
        disjoint_iff_inter_eq_empty.mp hya.symm, union_empty]
    simp only [coe_filter, mem_powersetCard, Set.mem_ofPred_eq]
    refine ⟨⟨union_subset (hx.trans ha) (hy.trans sdiff_subset), ?_⟩, ?_⟩
    · rw [card_union_of_disjoint hxy, hxc, hyc]; omega
    · rw [hax, hxc]
  · intro b _
    simp only
    rw [inter_comm, union_comm]
    exact sdiff_union_inter b a
  · rintro ⟨x, y⟩ hp
    simp only [coe_product, Set.mem_prod, mem_coe, mem_powersetCard] at hp
    obtain ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ := hp
    have hya : Disjoint y a := by
      rw [disjoint_left]; intro z hz; exact (mem_sdiff.mp (hy hz)).2
    simp only [Prod.mk.injEq]
    constructor
    · rw [inter_union_distrib_left, inter_eq_right.mpr hx,
        disjoint_iff_inter_eq_empty.mp hya.symm, union_empty]
    · rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.mpr hx, empty_union,
        sdiff_eq_self_of_disjoint hya]

lemma card_trip_filter (P : Finset H → Prop) [DecidablePred P] :
    (univ.filter (fun b : Trip => P b.val)).card = (tripSet.filter P).card := by
  have e : (univ.filter (fun b : Trip => P b.val)).map (Function.Embedding.subtype _) =
      tripSet.filter P := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨⟨b, hb⟩, hP, rfl⟩; exact ⟨hb, hP⟩
    · rintro ⟨hx, hP⟩; exact ⟨⟨x, hx⟩, hP, rfl⟩
  rw [← e, card_map]

lemma card_freeSet : freeSet.card = 30 := by
  rw [freeSet, card_sdiff_of_subset (subset_univ _)]
  simp

lemma neighbors_of (a : Trip) : (univ.filter (fun b : Trip => neighbor a b)).card = 3006 := by
  have e : (univ.filter (fun b : Trip => neighbor a b)) =
      univ.filter (fun b : Trip => (a.val ∩ b.val).card = 0 ∨ (a.val ∩ b.val).card = 2) := by
    ext b
    simp only [mem_filter, mem_univ, true_and]
    rfl
  have hc : (freeSet \ a.val).card = 27 := by
    rw [card_sdiff_of_subset (trip_sub a), card_freeSet, trip_card]
  have hd : Disjoint (tripSet.filter (fun b => (a.val ∩ b).card = 0))
      (tripSet.filter (fun b => (a.val ∩ b).card = 2)) := by
    rw [disjoint_filter]
    intro b _ h0 h2
    omega
  have h0 : (tripSet.filter (fun b => (a.val ∩ b).card = 0)).card = 2925 := by
    rw [tripSet, card_filter_inter _ _ (trip_sub a) 3 0 (by norm_num), trip_card, hc]
    rfl
  have h2 : (tripSet.filter (fun b => (a.val ∩ b).card = 2)).card = 81 := by
    rw [tripSet, card_filter_inter _ _ (trip_sub a) 3 2 (by norm_num), trip_card, hc]
    rfl
  rw [e, card_trip_filter (fun b => (a.val ∩ b).card = 0 ∨ (a.val ∩ b).card = 2), filter_or,
    card_union_of_disjoint hd, h0, h2]

/-- Number of neighbour (used) side pairs per invocation. -/
def nbN : ℕ := 4060 * 3006
/-- Number of non-neighbour (unused) side pairs per invocation. -/
def nnN : ℕ := 4060 * 1054

lemma card_neighbor : (univ.filter (fun p : Side => neighbor p.1 p.2)).card = nbN := by
  rw [card_filter, Fintype.sum_prod_type]
  simp only [← card_filter, neighbors_of, sum_const, card_univ, num_trip, smul_eq_mul]
  rfl

lemma nonneighbors_of (a : Trip) :
    (univ.filter (fun b : Trip => ¬ neighbor a b)).card = 1054 := by
  rw [Finset.filter_not, card_sdiff_of_subset (filter_subset _ _), neighbors_of, card_univ,
    num_trip]

lemma card_not_neighbor : (univ.filter (fun p : Side => ¬ neighbor p.1 p.2)).card = nnN := by
  rw [card_filter, Fintype.sum_prod_type]
  simp only [← card_filter, nonneighbors_of, sum_const, card_univ, num_trip, smul_eq_mul]
  rfl

/-! ### Splitting a sum over the roles of one invocation into the five role classes -/

lemma sum_stamp {M : Type*} [AddCommMonoid M] (φ : Mask → Mask → M)
    (x₁ y₁ s₁ c₁ d₁ x₂ y₂ s₂ c₂ d₂ : Mask) :
    ∑ b : Box, φ (stamp x₁ y₁ s₁ c₁ d₁ b) (stamp x₂ y₂ s₂ c₂ d₂ b) =
      4060 • φ x₁ x₂ + (4060 • φ y₁ y₂ + (nbN • φ s₁ s₂ + (nnN • φ d₁ d₂ + 33 • φ c₁ c₂))) := by
  simp only [Fintype.sum_sum_type]
  have hs : ∀ p : Side, φ (stamp x₁ y₁ s₁ c₁ d₁ (.inr (.inl p)))
      (stamp x₂ y₂ s₂ c₂ d₂ (.inr (.inl p))) =
      if neighbor p.1 p.2 then φ s₁ s₂ else φ d₁ d₂ := by
    intro p; by_cases h : neighbor p.1 p.2 <;> simp [stamp, h]
  simp only [hs]
  rw [Finset.sum_ite, sum_const, sum_const, card_neighbor, card_not_neighbor]
  simp only [stamp, sum_const, card_univ, num_trip, Fintype.card_unit, Fintype.card_fin, one_nsmul]
  abel

/-- The five role classes of one invocation: X wires, Y wires, used sides, centres, unused sides.
(The list order is X, Y, used sides, unused sides, centres.) -/
def st (ax ay as ac ad : ℕ) : List (ℕ × ℕ) :=
  [(ax, 4060), (ay, 4060), (as, nbN), (ad, nnN), (ac, 33)]

lemma riseM_stamp (x₁ y₁ s₁ c₁ d₁ x₂ y₂ s₂ c₂ d₂ : Mask) :
    riseM (stamp x₁ y₁ s₁ c₁ d₁) (stamp x₂ y₂ s₂ c₂ d₂) =
      toMS (st (x₂ \ x₁).card (y₂ \ y₁).card (s₂ \ s₁).card (c₂ \ c₁).card (d₂ \ d₁).card) := by
  have h := sum_stamp (fun u v => bm (v \ u).card) x₁ y₁ s₁ c₁ d₁ x₂ y₂ s₂ c₂ d₂
  rw [riseM, h]
  simp [st, toMS_cons]

lemma fallM_stamp (x₁ y₁ s₁ c₁ d₁ x₂ y₂ s₂ c₂ d₂ : Mask) :
    fallM (stamp x₁ y₁ s₁ c₁ d₁) (stamp x₂ y₂ s₂ c₂ d₂) =
      toMS (st (x₁ \ x₂).card (y₁ \ y₂).card (s₁ \ s₂).card (c₁ \ c₂).card (d₁ \ d₂).card) := by
  have h := sum_stamp (fun u v => bm (u \ v).card) x₁ y₁ s₁ c₁ d₁ x₂ y₂ s₂ c₂ d₂
  rw [fallM, h]
  simp [st, toMS_cons]

end PowerSaving.Cluster
end OAI
