import OAI.Computability.FourierTransform.Colour.Design
import OAI.Computability.FourierTransform.Colour.Sunflower

/-!
# Colour network, part 15: the cyclic sunflower register design (Lemma C.8) (new)

For every `h ≥ 7` we build `sunDesign h hh : PDesign h PDesign.twoP`, the register design covering
exactly the ordered pairs of triples meeting in two points (results/C_sidewires.md, Lemma C.8;
FORMALIZATION_CNET.md §4.2).

Data (`n = h - 2`, `L = lmax h = 2⌊n/2⌋ - 1`, i.e. `n - 1` for even `h` and `n - 2` for odd `h`):

* an *axis* is a 2-set `A = {a, b}` of `Fin h` (`Axis h`); its complement `Q_A` is enumerated in
  increasing order `x₀ < … < x_{n-1}` (`ex A`); the triple `abx_i` is `owner A i = A ∪ {x_i}`;
* cyclic distance `cd i x = (x - i) mod n` on `Fin n`; the forward arc
  `U(i, s) = {x_i, …, x_{i+s-1}}` is `xset A i s`, the backward arc
  `U(k - s, s) = {x_{k-s}, …, x_{k-1}}` is `yset A k s`;
* X-register `(A, i)` (writer `abx_i`): basis `sunBase a b U(i, L+1)`, slot `x_i`,
  `xlab ℓ = U(i, max 1 (min ℓ L))`;
* Y-register `(A, k)` (reader `abx_k`): basis `sunBase a b U(k-L, L+1)` (`= U(k-L, L) ∪ {x_k}`),
  slot `x_k`, `ylab ℓ = U(k - s, s)` with `s = min ℓ L`;
* transfers `(A, i, k)` with `1 ≤ cd i k ≤ L`, at level `cd i k`, label `U(i, cd i k)`;
* side pairs `(A, i, k)` with `cd i k > L` (only for odd `h`, where they are the pairs `k = i - 1`,
  i.e. `(abx_i, abx_{i-1})`).

Both bases are `sunBase` of an arc of the even length `L + 1 = 2⌊n/2⌋`; the label `M(P)` is the
index set `P` in every sunflower basis of the axis, so (D4) is `sun_mat_congr`.

Main results: `sunDesign`, the counts `sunDesign_card_XReg`, `sunDesign_card_YReg`
(`= 3·C(h,3)`), `sunDesign_card_Side` (`3·C(h,3)` for odd `h`, `0` for even `h`),
`sunDesign_card_Tr`, `sunDesign_card_regs` (`6·C(h,3)`), the instances `sunDesign_counts_30/20/41`,
and the chain facts `sunDesign_xlab_card`, `sunDesign_ylab_card`,
`sunDesign_xstep`, `sunDesign_ystep`, `sunDesign_xchanges`, `sunDesign_ychanges`.
-/

namespace OAI
namespace PowerSaving.Colour
open Finset Matrix Binary

namespace SunD

/-! ### Cyclic distance on `Fin m` -/

section Cyc
variable {m : ℕ}

/-- Cyclic distance from `i` forward to `x`, i.e. `(x - i) mod m`, as a natural number. -/
def cd (i x : Fin m) : ℕ := if i.val ≤ x.val then x.val - i.val else m + x.val - i.val

lemma cd_lt (i x : Fin m) : cd i x < m := by
  have := i.isLt; have := x.isLt
  unfold cd; split_ifs <;> omega

lemma cd_self (i : Fin m) : cd i i = 0 := by simp [cd]

lemma cd_eq_zero {i x : Fin m} : cd i x = 0 ↔ i = x := by
  have := i.isLt; have := x.isLt
  rw [Fin.ext_iff]
  unfold cd; split_ifs <;> omega

lemma cd_pos {i x : Fin m} (hne : i ≠ x) : 1 ≤ cd i x := by
  have := mt cd_eq_zero.mp hne; omega

/-- The transfer arithmetic: for `ℓ = cd i k`, the forward arc of length `ℓ` starting at `i` is
the backward arc of length `ℓ` ending just before `k`. -/
lemma cd_arc (i k x : Fin m) : cd i x < cd i k ↔ 1 ≤ cd x k ∧ cd x k ≤ cd i k := by
  have := i.isLt; have := k.isLt; have := x.isLt
  unfold cd; split_ifs <;> omega

/-- The point at forward distance `d` from `i`. -/
def fwd (i : Fin m) (d : ℕ) (hd : d < m) : Fin m :=
  ⟨if i.val + d < m then i.val + d else i.val + d - m, by have := i.isLt; split_ifs <;> omega⟩

lemma cd_fwd (i : Fin m) (d : ℕ) (hd : d < m) : cd i (fwd i d hd) = d := by
  have := i.isLt
  unfold cd fwd; dsimp only; split_ifs <;> omega

/-- The point at backward distance `d` from `k`. -/
def bwd (k : Fin m) (d : ℕ) (hd : d < m) : Fin m :=
  ⟨if d ≤ k.val then k.val - d else m + k.val - d, by have := k.isLt; split_ifs <;> omega⟩

lemma cd_bwd (k : Fin m) (d : ℕ) (hd : d < m) : cd (bwd k d hd) k = d := by
  have := k.isLt
  unfold cd bwd; dsimp only; split_ifs <;> omega

lemma card_cd_left (i : Fin m) (q : ℕ → Prop) [DecidablePred q] :
    (univ.filter fun x : Fin m => q (cd i x)).card = ((range m).filter q).card := by
  apply card_bij (fun x _ => cd i x)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    simp [mem_filter, cd_lt, hx]
  · intro x _ y _ e
    have := x.isLt; have := y.isLt; have := i.isLt
    apply Fin.ext
    unfold cd at e; split_ifs at e <;> omega
  · intro d hd
    simp only [mem_filter, mem_range] at hd
    exact ⟨fwd i d hd.1, by simp [cd_fwd, hd.2], cd_fwd i d hd.1⟩

lemma card_cd_right (k : Fin m) (q : ℕ → Prop) [DecidablePred q] :
    (univ.filter fun x : Fin m => q (cd x k)).card = ((range m).filter q).card := by
  apply card_bij (fun x _ => cd x k)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    simp [mem_filter, cd_lt, hx]
  · intro x _ y _ e
    have := x.isLt; have := y.isLt; have := k.isLt
    apply Fin.ext
    unfold cd at e; split_ifs at e <;> omega
  · intro d hd
    simp only [mem_filter, mem_range] at hd
    exact ⟨bwd k d hd.1, by simp [cd_bwd, hd.2], cd_bwd k d hd.1⟩

lemma card_cd_pairs (q : ℕ → Prop) [DecidablePred q] :
    (univ.filter fun p : Fin m × Fin m => q (cd p.1 p.2)).card
      = m * ((range m).filter q).card := by
  rw [card_filter, Fintype.sum_prod_type]
  have e : ∀ a : Fin m, (∑ b : Fin m, if q (cd a b) then 1 else 0) = ((range m).filter q).card := by
    intro a; rw [← card_cd_left a q, card_filter]
  simp only [e, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end Cyc

/-! ### Counting in `range m` -/

lemma card_range_lt (m s : ℕ) : ((range m).filter (fun d => d < s)).card = min s m := by
  have : (range m).filter (fun d => d < s) = range (min s m) := by
    ext d; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

lemma card_range_le (m s : ℕ) : ((range m).filter (fun d => d ≤ s)).card = min (s + 1) m := by
  have : (range m).filter (fun d => d ≤ s) = range (min (s + 1) m) := by
    ext d; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

lemma card_range_Icc (m s : ℕ) :
    ((range m).filter (fun d => 1 ≤ d ∧ d ≤ s)).card = min (s + 1) m - 1 := by
  have : (range m).filter (fun d => 1 ≤ d ∧ d ≤ s) = Ico 1 (min (s + 1) m) := by
    ext d; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]

lemma card_range_gt (m s : ℕ) : ((range m).filter (fun d => s < d)).card = m - (s + 1) := by
  have : (range m).filter (fun d => s < d) = Ico (s + 1) m := by
    ext d; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]

/-! ### Axes and the enumeration of `Q_A` -/

variable {h : ℕ}

def axSet (h : ℕ) : Finset (Finset (Fin h)) := (univ : Finset (Fin h)).powersetCard 2

/-- An axis: a 2-subset `{a, b}` of `Fin h`. -/
abbrev Axis (h : ℕ) := ↑(axSet h)

lemma num_axis : Fintype.card (Axis h) = h.choose 2 := by
  rw [Fintype.card_coe]
  show (axSet h).card = _
  unfold axSet
  rw [card_powersetCard, card_univ, Fintype.card_fin]

lemma ax_card (A : Axis h) : A.val.card = 2 := (mem_powersetCard.mp A.property).2

lemma ax_nonempty (A : Axis h) : A.val.Nonempty := card_pos.mp (by rw [ax_card]; norm_num)

/-- The two points of the axis. -/
def ax0 (A : Axis h) : Fin h := A.val.min' (ax_nonempty A)
def ax1 (A : Axis h) : Fin h := A.val.max' (ax_nonempty A)

lemma ax0_mem (A : Axis h) : ax0 A ∈ A.val := min'_mem _ _
lemma ax1_mem (A : Axis h) : ax1 A ∈ A.val := max'_mem _ _

lemma ax0_ne_ax1 (A : Axis h) : ax0 A ≠ ax1 A :=
  ne_of_lt (min'_lt_max'_of_card _ (by rw [ax_card]; norm_num))

lemma ax_eq (A : Axis h) : A.val = {ax0 A, ax1 A} := by
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [ax0_mem A, ax1_mem A]
  · rw [ax_card, card_pair (ax0_ne_ax1 A)]

lemma q_card (A : Axis h) : (univ \ A.val).card = h - 2 := by
  rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, ax_card]

/-- The increasing enumeration `x₀ < … < x_{n-1}` of `Q_A = [h] ∖ A`. -/
def ex (A : Axis h) : Fin (h - 2) ↪o Fin h := (univ \ A.val).orderEmbOfFin (q_card A)

lemma ex_not_mem (A : Axis h) (i : Fin (h - 2)) : ex A i ∉ A.val := by
  have := (univ \ A.val).orderEmbOfFin_mem (q_card A) i
  simp only [mem_sdiff, mem_univ, true_and] at this
  exact this

lemma ex_inj (A : Axis h) {i j : Fin (h - 2)} : ex A i = ex A j ↔ i = j := (ex A).injective.eq_iff

lemma ex_surj (A : Axis h) {x : Fin h} (hx : x ∉ A.val) : ∃ i, ex A i = x := by
  have : x ∈ Set.range ((univ \ A.val).orderEmbOfFin (q_card A)) := by
    rw [range_orderEmbOfFin]; simpa using hx
  exact this

/-! ### Sunflower labels as index sets: `lab A p = {x_i : p i}` -/

/-- The index set `{x_i : p i}` (the sunflower label `M({x_i : p i})`). -/
def lab (A : Axis h) (p : Fin (h - 2) → Prop) [DecidablePred p] : Finset (Fin h) :=
  (univ.filter p).map (ex A).toEmbedding

section Lab
variable (A : Axis h) {p q : Fin (h - 2) → Prop} [DecidablePred p] [DecidablePred q]

lemma ex_mem_lab (i : Fin (h - 2)) : ex A i ∈ lab A p ↔ p i := by
  unfold lab
  rw [mem_map]
  constructor
  · rintro ⟨j, hj, e⟩
    have : j = i := (ex_inj A).mp e
    subst this
    simpa using hj
  · intro hi; exact ⟨i, by simpa using hi, rfl⟩

lemma not_mem_lab {y : Fin h} (hy : y ∈ A.val) : y ∉ lab A p := by
  unfold lab
  rw [mem_map]
  rintro ⟨j, -, e⟩
  exact ex_not_mem A j (by rw [← e] at hy; exact hy)

lemma lab_sub (hpq : ∀ i, p i → q i) : lab A p ⊆ lab A q := by
  unfold lab
  apply map_subset_map.mpr
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hpq i hi

lemma lab_congr (hpq : ∀ i, p i ↔ q i) : lab A p = lab A q :=
  Subset.antisymm (lab_sub A fun i => (hpq i).mp) (lab_sub A fun i => (hpq i).mpr)

lemma card_lab : (lab A p).card = (univ.filter p).card := by
  unfold lab; rw [card_map]

end Lab

/-! ### The owner triples `abx_i = A ∪ {x_i}` -/

/-- The triple `abx_i`. -/
def owner (A : Axis h) (i : Fin (h - 2)) : Trip h :=
  ⟨insert (ex A i) A.val, by
    show _ ∈ (univ : Finset (Fin h)).powersetCard 3
    rw [mem_powersetCard]
    exact ⟨subset_univ _, by rw [card_insert_of_notMem (ex_not_mem A i), ax_card]⟩⟩

lemma owner_val (A : Axis h) (i : Fin (h - 2)) : (owner A i).val = insert (ex A i) A.val := rfl

lemma owner_val3 (A : Axis h) (i : Fin (h - 2)) : (owner A i).val = {ax0 A, ax1 A, ex A i} := by
  rw [owner_val, ax_eq A]
  ext y; simp only [mem_insert, mem_singleton]; tauto

lemma owner_inter (A : Axis h) {i k : Fin (h - 2)} (hik : i ≠ k) :
    (owner A i).val ∩ (owner A k).val = A.val := by
  rw [owner_val, owner_val]
  have hne : ex A i ≠ ex A k := fun e => hik ((ex_inj A).mp e)
  ext y; simp only [mem_inter, mem_insert]
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩
    · exact absurd (h1.symm.trans h2) hne
    all_goals assumption
  · intro hy; exact ⟨Or.inr hy, Or.inr hy⟩

lemma meet_owner (A : Axis h) {i k : Fin (h - 2)} (hik : i ≠ k) :
    meet (owner A i) (owner A k) = 2 := by
  unfold meet; rw [owner_inter A hik, ax_card]

/-- The ordered pair `(abx_i, abx_k)`, `i ≠ k`, determines the axis and both indices. -/
lemma owner_inj {A A' : Axis h} {i k i' k' : Fin (h - 2)} (hik : i ≠ k) (hik' : i' ≠ k')
    (e1 : owner A i = owner A' i') (e2 : owner A k = owner A' k') :
    A = A' ∧ i = i' ∧ k = k' := by
  have hA : A = A' := Subtype.ext (by rw [← owner_inter A hik, ← owner_inter A' hik', e1, e2])
  subst hA
  refine ⟨rfl, ?_, ?_⟩
  · have e := congrArg Subtype.val e1
    rw [owner_val, owner_val, insert_inj (ex_not_mem A i)] at e
    exact (ex_inj A).mp e
  · have e := congrArg Subtype.val e2
    rw [owner_val, owner_val, insert_inj (ex_not_mem A k)] at e
    exact (ex_inj A).mp e

/-- Every ordered pair of triples meeting in two points is `(abx_i, abx_k)`. -/
lemma exists_owner (T S : Trip h) (hm : meet T S = 2) :
    ∃ A : Axis h, ∃ i k : Fin (h - 2), i ≠ k ∧ owner A i = T ∧ owner A k = S := by
  have hI : (T.val ∩ S.val).card = 2 := hm
  set A : Axis h := ⟨T.val ∩ S.val, mem_powersetCard.mpr ⟨subset_univ _, hI⟩⟩ with hAdef
  have hAv : A.val = T.val ∩ S.val := rfl
  have hT : (T.val \ S.val).card = 1 := by
    have := card_sdiff_add_card_inter T.val S.val; rw [trip_card, hI] at this; omega
  have hS : (S.val \ T.val).card = 1 := by
    have := card_sdiff_add_card_inter S.val T.val; rw [trip_card, inter_comm, hI] at this; omega
  obtain ⟨x, hx⟩ := card_eq_one.mp hT
  obtain ⟨y, hy⟩ := card_eq_one.mp hS
  have hxm : x ∈ T.val \ S.val := by rw [hx]; exact mem_singleton_self x
  have hym : y ∈ S.val \ T.val := by rw [hy]; exact mem_singleton_self y
  rw [mem_sdiff] at hxm hym
  have hxA : x ∉ A.val := fun hh => hxm.2 (mem_inter.mp hh).2
  have hyA : y ∉ A.val := fun hh => hym.2 (mem_inter.mp hh).1
  obtain ⟨i, hi⟩ := ex_surj A hxA
  obtain ⟨k, hk⟩ := ex_surj A hyA
  refine ⟨A, i, k, ?_, ?_, ?_⟩
  · rintro rfl
    rw [hi] at hk
    exact hxm.2 (hk ▸ hym.1)
  · apply Subtype.ext
    rw [owner_val, hi, hAv, insert_eq, ← hx, sdiff_union_inter]
  · apply Subtype.ext
    rw [owner_val, hk, hAv, inter_comm, insert_eq, ← hy, sdiff_union_inter]

/-! ### Pairs `(A, i, k)` and the cover count -/

/-- Candidate pairs `(A, i, k)`: writer `abx_i`, reader `abx_k`. -/
abbrev Pair (h : ℕ) := Axis h × Fin (h - 2) × Fin (h - 2)

lemma card_pair_owner_two (T S : Trip h) (hm : meet T S = 2) :
    (univ.filter fun π : Pair h =>
      π.2.1 ≠ π.2.2 ∧ owner π.1 π.2.1 = T ∧ owner π.1 π.2.2 = S).card = 1 := by
  obtain ⟨A, i, k, hik, hT, hS⟩ := exists_owner T S hm
  rw [card_eq_one]
  refine ⟨(A, i, k), ?_⟩
  ext ⟨A', i', k'⟩
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨hik', e1, e2⟩
    obtain ⟨rfl, rfl, rfl⟩ := owner_inj hik' hik (e1.trans hT.symm) (e2.trans hS.symm)
    rfl
  · intro e
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact ⟨hik, hT, hS⟩

lemma card_pair_owner_ne (T S : Trip h) (hm : meet T S ≠ 2) :
    (univ.filter fun π : Pair h =>
      π.2.1 ≠ π.2.2 ∧ owner π.1 π.2.1 = T ∧ owner π.1 π.2.2 = S).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro ⟨A, i, k⟩ - ⟨hik, rfl, rfl⟩
  exact hm (meet_owner A hik)

lemma card_filter_subtype {α : Type*} [Fintype α] (p c : α → Prop) [DecidablePred p]
    [DecidablePred c] :
    (univ.filter fun x : Subtype p => c x.1).card = (univ.filter fun a => p a ∧ c a).card := by
  rw [← card_map (Function.Embedding.subtype p)]
  congr 1
  ext a
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
    Subtype.exists, exists_and_right, exists_eq_right]
  tauto

/-! ### The level bound `ℓ_max` -/

/-- `ℓ_max = 2⌊(h-2)/2⌋ - 1`: `h - 3` for even `h`, `h - 4` for odd `h`. -/
def lmax (h : ℕ) : ℕ := 2 * ((h - 2) / 2) - 1

lemma lmax_even (he : Even h) : lmax h = h - 3 := by
  obtain ⟨r, rfl⟩ := he; unfold lmax; omega

lemma lmax_odd (ho : ¬ Even h) : lmax h = h - 4 := by
  rw [Nat.not_even_iff_odd] at ho
  obtain ⟨r, rfl⟩ := ho; unfold lmax; omega

lemma lmax_ge (hh : 7 ≤ h) : 3 ≤ lmax h := by unfold lmax; omega

lemma lmax_succ_le (hh : 7 ≤ h) : lmax h + 1 ≤ h - 2 := by unfold lmax; omega

lemma lmax_le (h : ℕ) : lmax h ≤ h := by unfold lmax; omega

lemma lmax_succ_even (hh : 7 ≤ h) : ((lmax h + 1 : ℕ) : F) = 0 := by
  have e : lmax h + 1 = 2 * ((h - 2) / 2) := by unfold lmax; omega
  rw [e]; push_cast
  rw [show (2 : F) = 0 from rfl, zero_mul]

/-! ### The arcs -/

/-- Forward arc `U(i, s) = {x_i, …, x_{i+s-1}}`. -/
def xset (A : Axis h) (i : Fin (h - 2)) (s : ℕ) : Finset (Fin h) := lab A fun x => cd i x < s

/-- Backward arc `U(k - s, s) = {x_{k-s}, …, x_{k-1}}`. -/
def yset (A : Axis h) (k : Fin (h - 2)) (s : ℕ) : Finset (Fin h) :=
  lab A fun x => 1 ≤ cd x k ∧ cd x k ≤ s

/-- The index set of the reader's basis: `U(k - L, L) ∪ {x_k}`. -/
def ybset (A : Axis h) (k : Fin (h - 2)) : Finset (Fin h) := lab A fun x => cd x k ≤ lmax h

lemma card_xset (A : Axis h) (i : Fin (h - 2)) (s : ℕ) : (xset A i s).card = min s (h - 2) := by
  unfold xset; rw [card_lab, card_cd_left i (fun d => d < s), card_range_lt]

lemma card_yset (A : Axis h) (k : Fin (h - 2)) (s : ℕ) :
    (yset A k s).card = min (s + 1) (h - 2) - 1 := by
  unfold yset; rw [card_lab, card_cd_right k (fun d => 1 ≤ d ∧ d ≤ s), card_range_Icc]

lemma card_ybset (A : Axis h) (k : Fin (h - 2)) :
    (ybset A k).card = min (lmax h + 1) (h - 2) := by
  unfold ybset; rw [card_lab, card_cd_right k (fun d => d ≤ lmax h), card_range_le]

lemma sunOK_x (hh : 7 ≤ h) (A : Axis h) (i : Fin (h - 2)) :
    SunOK (ax0 A) (ax1 A) (xset A i (lmax h + 1)) where
  hab := ax0_ne_ax1 A
  ha := not_mem_lab A (ax0_mem A)
  hb := not_mem_lab A (ax1_mem A)
  heven := by
    rw [card_xset, min_eq_left (lmax_succ_le hh)]; exact lmax_succ_even hh

lemma sunOK_y (hh : 7 ≤ h) (A : Axis h) (k : Fin (h - 2)) :
    SunOK (ax0 A) (ax1 A) (ybset A k) where
  hab := ax0_ne_ax1 A
  ha := not_mem_lab A (ax0_mem A)
  hb := not_mem_lab A (ax1_mem A)
  heven := by
    rw [card_ybset, min_eq_left (lmax_succ_le hh)]; exact lmax_succ_even hh

/-! ### The components of the design -/

/-- Transfers: `(A, i, k)` with `1 ≤ cd i k ≤ L`. -/
abbrev TrT (h : ℕ) := {π : Pair h // 1 ≤ cd π.2.1 π.2.2 ∧ cd π.2.1 π.2.2 ≤ lmax h}

/-- Side pairs: `(A, i, k)` with `cd i k > L` (nonempty only for odd `h`). -/
abbrev SideT (h : ℕ) := {π : Pair h // lmax h < cd π.2.1 π.2.2}

/-- The registers (X and Y): `(A, i)` ↔ the triple `abx_i`. -/
abbrev RegT (h : ℕ) := Axis h × Fin (h - 2)

noncomputable def xbaseF (r : RegT h) : OBase (Fin h) :=
  sunBase (ax0 r.1) (ax1 r.1) (xset r.1 r.2 (lmax h + 1))

noncomputable def ybaseF (r : RegT h) : OBase (Fin h) := sunBase (ax0 r.1) (ax1 r.1) (ybset r.1 r.2)

def xlabF (r : RegT h) (ℓ : ℕ) : Finset (Fin h) := xset r.1 r.2 (max 1 (min ℓ (lmax h)))

def ylabF (r : RegT h) (ℓ : ℕ) : Finset (Fin h) := yset r.1 r.2 (min ℓ (lmax h))

lemma x_slotF (hh : 7 ≤ h) (r : RegT h) : (xbaseF r).v (ex r.1 r.2) = tip (owner r.1 r.2) :=
  sunBase_tip _ _ _ (sunOK_x hh r.1 r.2) _ ((ex_mem_lab r.1 r.2).mpr (by rw [cd_self]; omega))
    (owner_val3 r.1 r.2)

lemma y_slotF (hh : 7 ≤ h) (r : RegT h) : (ybaseF r).v (ex r.1 r.2) = tip (owner r.1 r.2) :=
  sunBase_tip _ _ _ (sunOK_y hh r.1 r.2) _ ((ex_mem_lab r.1 r.2).mpr (by rw [cd_self]; omega))
    (owner_val3 r.1 r.2)

lemma x_memF (r : RegT h) (ℓ : ℕ) : ex r.1 r.2 ∈ xlabF r ℓ :=
  (ex_mem_lab r.1 r.2).mpr (by rw [cd_self]; omega)

lemma y_outF (r : RegT h) (ℓ : ℕ) : ex r.1 r.2 ∉ ylabF r ℓ := by
  unfold ylabF yset
  rw [ex_mem_lab, cd_self]; omega

lemma x_monoF (r : RegT h) : Monotone (xlabF r) := by
  intro ℓ ℓ' hle
  apply lab_sub
  intro x hx; omega

lemma y_monoF (r : RegT h) : Monotone (ylabF r) := by
  intro ℓ ℓ' hle
  apply lab_sub
  intro x hx; omega

lemma tlev_memF (τ : TrT h) : cd τ.1.2.1 τ.1.2.2 ∈ Finset.Icc 1 h := by
  have := lmax_le h
  have := τ.2
  rw [mem_Icc]; omega

lemma syncF (hh : 7 ≤ h) (τ : TrT h) :
    (xbaseF (τ.1.1, τ.1.2.1)).mat (xlabF (τ.1.1, τ.1.2.1) (cd τ.1.2.1 τ.1.2.2))
      = (ybaseF (τ.1.1, τ.1.2.2)).mat (ylabF (τ.1.1, τ.1.2.2) (cd τ.1.2.1 τ.1.2.2)) := by
  obtain ⟨⟨A, i, k⟩, h1, h2⟩ := τ
  dsimp only at h1 h2 ⊢
  have e1 : max 1 (min (cd i k) (lmax h)) = cd i k := by omega
  have e2 : min (cd i k) (lmax h) = cd i k := by omega
  have exy : xset A i (cd i k) = yset A k (cd i k) := lab_congr A fun x => cd_arc i k x
  unfold xbaseF ybaseF xlabF ylabF
  dsimp only
  rw [e1, e2, exy]
  apply sun_mat_congr _ _ _ _ _ (sunOK_x hh A i) (sunOK_y hh A k)
  · rw [← exy]; apply lab_sub; intro x hx; omega
  · apply lab_sub; intro x hx; omega

lemma side_okF (σ : SideT h) : neighbor (owner σ.1.1 σ.1.2.1) (owner σ.1.1 σ.1.2.2) := by
  have hne : σ.1.2.1 ≠ σ.1.2.2 := by
    intro e; have := σ.2; rw [e, cd_self] at this; omega
  exact Or.inr (meet_owner σ.1.1 hne)

lemma coverF_aux (T S : Trip h) :
    (univ.filter fun τ : TrT h => owner τ.1.1 τ.1.2.1 = T ∧ owner τ.1.1 τ.1.2.2 = S).card
      + (univ.filter fun σ : SideT h => owner σ.1.1 σ.1.2.1 = T ∧ owner σ.1.1 σ.1.2.2 = S).card
      = (univ.filter fun π : Pair h =>
          π.2.1 ≠ π.2.2 ∧ owner π.1 π.2.1 = T ∧ owner π.1 π.2.2 = S).card := by
  rw [card_filter_subtype (fun π : Pair h => 1 ≤ cd π.2.1 π.2.2 ∧ cd π.2.1 π.2.2 ≤ lmax h)
      (fun π : Pair h => owner π.1 π.2.1 = T ∧ owner π.1 π.2.2 = S),
    card_filter_subtype (fun π : Pair h => lmax h < cd π.2.1 π.2.2)
      (fun π : Pair h => owner π.1 π.2.1 = T ∧ owner π.1 π.2.2 = S),
    ← card_union_of_disjoint, ← filter_or]
  · congr 1
    ext ⟨A, i, k⟩
    simp only [mem_filter, mem_univ, true_and]
    have h0 : i ≠ k ↔ 1 ≤ cd i k := by
      constructor
      · exact cd_pos
      · intro hc e; rw [e, cd_self] at hc; omega
    rw [h0]
    constructor
    · rintro (⟨⟨a1, -⟩, a2⟩ | ⟨a1, a2⟩)
      · exact ⟨a1, a2⟩
      · exact ⟨by omega, a2⟩
    · rintro ⟨a1, a2⟩
      by_cases hc : cd i k ≤ lmax h
      · exact Or.inl ⟨⟨a1, hc⟩, a2⟩
      · exact Or.inr ⟨by omega, a2⟩
  · rw [disjoint_filter]
    rintro π - ⟨⟨-, a⟩, -⟩ ⟨b, -⟩
    omega

lemma coverF (T S : Trip h) :
    (univ.filter fun τ : TrT h => owner τ.1.1 τ.1.2.1 = T ∧ owner τ.1.1 τ.1.2.2 = S).card
      + (univ.filter fun σ : SideT h => owner σ.1.1 σ.1.2.1 = T ∧ owner σ.1.1 σ.1.2.2 = S).card
      = if PDesign.twoP T S then 1 else 0 := by
  rw [coverF_aux]
  by_cases hm : meet T S = 2
  · rw [card_pair_owner_two T S hm]; simp [show PDesign.twoP T S from hm]
  · rw [card_pair_owner_ne T S hm]; simp [show ¬ PDesign.twoP T S from hm]

end SunD

open SunD

/-- **The cyclic sunflower design** (Lemma C.8) for `h ≥ 7`: a partial register design covering
exactly the ordered pairs of triples meeting in two points. -/
noncomputable def sunDesign (h : ℕ) (hh : 7 ≤ h) : PDesign h PDesign.twoP where
  XReg := RegT h
  YReg := RegT h
  Side := SideT h
  Tr := TrT h
  xown r := owner r.1 r.2
  yown r := owner r.1 r.2
  xbase := xbaseF
  ybase := ybaseF
  xslot r := ex r.1 r.2
  yslot r := ex r.1 r.2
  xlab := xlabF
  ylab := ylabF
  x_slot := x_slotF hh
  y_slot := y_slotF hh
  x_mem := x_memF
  y_out := y_outF
  x_mono := x_monoF
  y_mono := y_monoF
  tx τ := (τ.1.1, τ.1.2.1)
  ty τ := (τ.1.1, τ.1.2.2)
  tlev τ := cd τ.1.2.1 τ.1.2.2
  tlev_mem := tlev_memF
  sync := syncF hh
  sx σ := owner σ.1.1 σ.1.2.1
  sy σ := owner σ.1.1 σ.1.2.2
  side_ok := side_okF
  cover := coverF

/-! ### Counts -/

section Counts
variable (h : ℕ) (hh : 7 ≤ h)

lemma choose_two_mul (h : ℕ) : h.choose 2 * (h - 2) = 3 * h.choose 3 := by
  rw [mul_comm 3]; exact (Nat.choose_succ_right_eq h 2).symm

lemma card_pair_cd (q : ℕ → Prop) [DecidablePred q] :
    (univ.filter fun π : Pair h => q (cd π.2.1 π.2.2)).card
      = h.choose 2 * ((h - 2) * ((range (h - 2)).filter q).card) := by
  have e : (univ.filter fun π : Pair h => q (cd π.2.1 π.2.2))
      = (univ : Finset (Axis h)) ×ˢ (univ.filter fun p : Fin (h - 2) × Fin (h - 2) => q (cd p.1 p.2)) := by
    ext ⟨A, i, k⟩; simp
  rw [e, card_product, card_univ, num_axis, card_cd_pairs]

theorem sunDesign_card_XReg : Fintype.card (sunDesign h hh).XReg = 3 * h.choose 3 := by
  show Fintype.card (Axis h × Fin (h - 2)) = _
  rw [Fintype.card_prod, num_axis, Fintype.card_fin, choose_two_mul]

theorem sunDesign_card_YReg : Fintype.card (sunDesign h hh).YReg = 3 * h.choose 3 := by
  show Fintype.card (Axis h × Fin (h - 2)) = _
  rw [Fintype.card_prod, num_axis, Fintype.card_fin, choose_two_mul]

/-- Number of transfers: `C(h,2)·n·ℓ_max = 3·C(h,3)·ℓ_max`. -/
theorem sunDesign_card_Tr :
    Fintype.card (sunDesign h hh).Tr = 3 * h.choose 3 * lmax h := by
  show Fintype.card (TrT h) = _
  rw [Fintype.card_subtype, card_pair_cd h (fun d => 1 ≤ d ∧ d ≤ lmax h), card_range_Icc,
    min_eq_left (lmax_succ_le hh), Nat.add_sub_cancel, ← choose_two_mul, mul_assoc]

theorem sunDesign_card_Side_gen :
    Fintype.card (sunDesign h hh).Side = h.choose 2 * ((h - 2) * (h - 2 - (lmax h + 1))) := by
  show Fintype.card (SideT h) = _
  rw [Fintype.card_subtype, card_pair_cd h (fun d => lmax h < d), card_range_gt]

/-- Side pairs: `3·C(h,3)` for odd `h`, none for even `h`. -/
theorem sunDesign_card_Side :
    Fintype.card (sunDesign h hh).Side = if Even h then 0 else 3 * h.choose 3 := by
  rw [sunDesign_card_Side_gen]
  split_ifs with he
  · rw [lmax_even he, show h - 2 - (h - 3 + 1) = 0 by omega]; simp
  · rw [lmax_odd he, show h - 2 - (h - 4 + 1) = 1 by omega, mul_one, choose_two_mul]

theorem sunDesign_card_Side_odd (ho : ¬ Even h) : Fintype.card (sunDesign h hh).Side = 3 * h.choose 3 := by
  rw [sunDesign_card_Side]; simp [ho]

theorem sunDesign_card_Side_even (he : Even h) : Fintype.card (sunDesign h hh).Side = 0 := by
  rw [sunDesign_card_Side]; simp [he]

/-- All sunflower registers: `card XReg + card YReg = 6·C(h,3)`. -/
theorem sunDesign_card_regs :
    Fintype.card (sunDesign h hh).XReg + Fintype.card (sunDesign h hh).YReg = 6 * h.choose 3 := by
  rw [sunDesign_card_XReg, sunDesign_card_YReg]; ring

lemma three_choose_three (h : ℕ) : 3 * h.choose 3 = h * (h - 1) / 2 * (h - 2) := by
  rw [← choose_two_mul, Nat.choose_two_right]

end Counts

/-! ### The three factor sizes of the network (`hs = ![30, 20, 41]`) -/

/-- `h = 30`: `v = C(30,3) = 4060`; `3v = 12180` X- and Y-registers each (`6v = 24360`), no side
pairs. -/
theorem sunDesign_counts_30 (hh : 7 ≤ 30) :
    Fintype.card (sunDesign 30 hh).XReg = 12180 ∧ Fintype.card (sunDesign 30 hh).YReg = 12180 ∧
      Fintype.card (sunDesign 30 hh).XReg + Fintype.card (sunDesign 30 hh).YReg = 24360 ∧
      Fintype.card (sunDesign 30 hh).Side = 0 := by
  have hx : Fintype.card (sunDesign 30 hh).XReg = 12180 := by
    rw [sunDesign_card_XReg, three_choose_three]
  have hy : Fintype.card (sunDesign 30 hh).YReg = 12180 := by
    rw [sunDesign_card_YReg, three_choose_three]
  exact ⟨hx, hy, by rw [hx, hy], sunDesign_card_Side_even 30 hh (by decide)⟩

/-- `h = 20`: `v = C(20,3) = 1140`; `3v = 3420` X- and Y-registers each (`6v = 6840`), no side
pairs. -/
theorem sunDesign_counts_20 (hh : 7 ≤ 20) :
    Fintype.card (sunDesign 20 hh).XReg = 3420 ∧ Fintype.card (sunDesign 20 hh).YReg = 3420 ∧
      Fintype.card (sunDesign 20 hh).XReg + Fintype.card (sunDesign 20 hh).YReg = 6840 ∧
      Fintype.card (sunDesign 20 hh).Side = 0 := by
  have hx : Fintype.card (sunDesign 20 hh).XReg = 3420 := by
    rw [sunDesign_card_XReg, three_choose_three]
  have hy : Fintype.card (sunDesign 20 hh).YReg = 3420 := by
    rw [sunDesign_card_YReg, three_choose_three]
  exact ⟨hx, hy, by rw [hx, hy], sunDesign_card_Side_even 20 hh (by decide)⟩

/-- `h = 41`: `v = C(41,3) = 10660`; `3v = 31980` X- and Y-registers each (`6v = 63960`), and
`3v = 31980` side pairs. -/
theorem sunDesign_counts_41 (hh : 7 ≤ 41) :
    Fintype.card (sunDesign 41 hh).XReg = 31980 ∧ Fintype.card (sunDesign 41 hh).YReg = 31980 ∧
      Fintype.card (sunDesign 41 hh).XReg + Fintype.card (sunDesign 41 hh).YReg = 63960 ∧
      Fintype.card (sunDesign 41 hh).Side = 31980 := by
  have hx : Fintype.card (sunDesign 41 hh).XReg = 31980 := by
    rw [sunDesign_card_XReg, three_choose_three]
  have hy : Fintype.card (sunDesign 41 hh).YReg = 31980 := by
    rw [sunDesign_card_YReg, three_choose_three]
  have hs : Fintype.card (sunDesign 41 hh).Side = 31980 := by
    rw [sunDesign_card_Side_odd 41 hh (by decide), three_choose_three]
  exact ⟨hx, hy, by rw [hx, hy], hs⟩

/-! ### Chain facts -/

section Chains
variable {h : ℕ} {hh : 7 ≤ h}

theorem sunDesign_xlab_card (r : (sunDesign h hh).XReg) (ℓ : ℕ) :
    ((sunDesign h hh).xlab r ℓ).card = max 1 (min ℓ (lmax h)) := by
  show (xset r.1 r.2 (max 1 (min ℓ (lmax h)))).card = _
  have := lmax_succ_le hh
  rw [card_xset]; omega

theorem sunDesign_ylab_card (r : (sunDesign h hh).YReg) (ℓ : ℕ) :
    ((sunDesign h hh).ylab r ℓ).card = min ℓ (lmax h) := by
  show (yset r.1 r.2 (min ℓ (lmax h))).card = _
  have := lmax_succ_le hh
  rw [card_yset]; omega

/-- The first X-label is the singleton of the slot (the label `Xb`). -/
theorem sunDesign_xlab_one (r : (sunDesign h hh).XReg) :
    (sunDesign h hh).xlab r 1 = {(sunDesign h hh).xslot r} := by
  symm
  apply eq_of_subset_of_card_le
  · intro y hy
    rw [mem_singleton] at hy; rw [hy]; exact (sunDesign h hh).x_mem r 1
  · rw [sunDesign_xlab_card, card_singleton]; omega

theorem sunDesign_ylab_zero (r : (sunDesign h hh).YReg) : (sunDesign h hh).ylab r 0 = ∅ := by
  rw [← card_eq_zero, sunDesign_ylab_card]; simp

/-- Each X-chain step adds at most one index (all middle edges of a sunflower X-register are
units). -/
theorem sunDesign_xstep (r : (sunDesign h hh).XReg) (ℓ : ℕ) :
    ((sunDesign h hh).xlab r (ℓ + 1) \ (sunDesign h hh).xlab r ℓ).card ≤ 1 := by
  rw [card_sdiff_of_subset ((sunDesign h hh).x_mono r (Nat.le_add_right ℓ 1)), sunDesign_xlab_card,
    sunDesign_xlab_card]
  omega

theorem sunDesign_ystep (r : (sunDesign h hh).YReg) (ℓ : ℕ) :
    ((sunDesign h hh).ylab r (ℓ + 1) \ (sunDesign h hh).ylab r ℓ).card ≤ 1 := by
  rw [card_sdiff_of_subset ((sunDesign h hh).y_mono r (Nat.le_add_right ℓ 1)), sunDesign_ylab_card,
    sunDesign_ylab_card]
  omega

/-- Nested labels with equal cardinality are equal. -/
lemma eq_iff_card_eq_of_sub {α : Type*} {s t : Finset α} (hst : s ⊆ t) : t = s ↔ t.card = s.card :=
  ⟨fun e => by rw [e], fun e => (eq_of_subset_of_card_le hst e.le).symm⟩

/-- The X-label changes exactly at the levels `ℓ → ℓ+1` with `1 ≤ ℓ < ℓ_max`. -/
theorem sunDesign_xchanges (r : (sunDesign h hh).XReg) :
    ((range h).filter fun ℓ => (sunDesign h hh).xlab r (ℓ + 1) ≠ (sunDesign h hh).xlab r ℓ).card
      = lmax h - 1 := by
  have hL := lmax_le h
  have hL3 := lmax_ge hh
  have : (range h).filter (fun ℓ => (sunDesign h hh).xlab r (ℓ + 1) ≠ (sunDesign h hh).xlab r ℓ)
      = Ico 1 (lmax h) := by
    ext ℓ
    rw [mem_filter, mem_range, mem_Ico, ne_eq,
      eq_iff_card_eq_of_sub ((sunDesign h hh).x_mono r (Nat.le_add_right ℓ 1)), sunDesign_xlab_card,
      sunDesign_xlab_card]
    omega
  rw [this, Nat.card_Ico]

/-- The Y-label changes exactly at the levels `ℓ → ℓ+1` with `ℓ < ℓ_max`. -/
theorem sunDesign_ychanges (r : (sunDesign h hh).YReg) :
    ((range h).filter fun ℓ => (sunDesign h hh).ylab r (ℓ + 1) ≠ (sunDesign h hh).ylab r ℓ).card
      = lmax h := by
  have hL := lmax_le h
  have hL3 := lmax_ge hh
  have : (range h).filter (fun ℓ => (sunDesign h hh).ylab r (ℓ + 1) ≠ (sunDesign h hh).ylab r ℓ)
      = range (lmax h) := by
    ext ℓ
    rw [mem_filter, mem_range, mem_range, ne_eq,
      eq_iff_card_eq_of_sub ((sunDesign h hh).y_mono r (Nat.le_add_right ℓ 1)), sunDesign_ylab_card,
      sunDesign_ylab_card]
    omega
  rw [this, card_range]

theorem sunDesign_xchanges_le (r : (sunDesign h hh).XReg) :
    ((range h).filter fun ℓ => (sunDesign h hh).xlab r (ℓ + 1) ≠ (sunDesign h hh).xlab r ℓ).card
      ≤ h := by
  rw [sunDesign_xchanges]; have := lmax_le h; omega

theorem sunDesign_ychanges_le (r : (sunDesign h hh).YReg) :
    ((range h).filter fun ℓ => (sunDesign h hh).ylab r (ℓ + 1) ≠ (sunDesign h hh).ylab r ℓ).card
      ≤ h := by
  rw [sunDesign_ychanges]; exact lmax_le h

/-- Every X-label is nonempty. -/
theorem sunDesign_xlab_pos (r : (sunDesign h hh).XReg) (ℓ : ℕ) :
    1 ≤ ((sunDesign h hh).xlab r ℓ).card := by
  rw [sunDesign_xlab_card]; omega

/-- Every Y-label at a level `ℓ ≥ 1` is nonempty. -/
theorem sunDesign_ylab_pos (r : (sunDesign h hh).YReg) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    1 ≤ ((sunDesign h hh).ylab r ℓ).card := by
  have := lmax_ge hh
  rw [sunDesign_ylab_card]; omega

/-- The terminal X-edge `xlab h → univ` has size `h - ℓ_max`. -/
theorem sunDesign_xtop (r : (sunDesign h hh).XReg) :
    (univ \ (sunDesign h hh).xlab r h).card = h - lmax h := by
  rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, sunDesign_xlab_card]
  have := lmax_le h; have := lmax_ge hh; omega

/-- The terminal Y-edge `ylab h → univ ∖ {yslot}` has size `h - 1 - ℓ_max`. -/
theorem sunDesign_ytop (r : (sunDesign h hh).YReg) :
    ((univ \ {(sunDesign h hh).yslot r}) \ (sunDesign h hh).ylab r h).card = h - 1 - lmax h := by
  have hsub : (sunDesign h hh).ylab r h ⊆ univ \ {(sunDesign h hh).yslot r} := by
    intro y hy
    rw [mem_sdiff, mem_singleton]
    exact ⟨mem_univ _, fun e => (sunDesign h hh).y_out r h (e ▸ hy)⟩
  rw [card_sdiff_of_subset hsub, card_sdiff_of_subset (subset_univ _), card_univ,
    Fintype.card_fin, card_singleton, sunDesign_ylab_card]
  have := lmax_le h; have := lmax_ge hh; omega

/-- Transfers happen at levels `1 ≤ ℓ ≤ ℓ_max`, and the level is the dimension of the label. -/
theorem sunDesign_tlev (τ : (sunDesign h hh).Tr) :
    1 ≤ (sunDesign h hh).tlev τ ∧ (sunDesign h hh).tlev τ ≤ lmax h ∧
      ((sunDesign h hh).xlab ((sunDesign h hh).tx τ) ((sunDesign h hh).tlev τ)).card
        = (sunDesign h hh).tlev τ := by
  have h1 : 1 ≤ (sunDesign h hh).tlev τ ∧ (sunDesign h hh).tlev τ ≤ lmax h := τ.2
  refine ⟨h1.1, h1.2, ?_⟩
  rw [sunDesign_xlab_card]; omega

end Chains

end PowerSaving.Colour
end OAI
