import OAI.Computability.FourierTransform.Colour.CCertificate
import OAI.Computability.FourierTransform.Colour.InvocationCost

/-!
# Colour network, part 14b: the exponent obligations of the certificate (new)

Combination of C11 (`InvocationCost`) and C14 (`Exponent`) on the network word of
`Certificate`/`CCertificate`:

* `Phi_Etot`: `Φ(E_total) = Σ_j |Inv j| Φ(E_inv,j) + P (φ 1 + φ(u-1))`;
* `mem_Etot`: all batch sizes in `[1, u)`;
* `invBound_eq`: at the sizes `(30, 20, 41)` the C11 bound is the cost-class bound of `Exponent`;
* **`final_obligations`**: for designs whose per-factor counts are dominated by the design counts of
  FORMALIZATION_CNET.md §5.3, the three remaining hypotheses of `Net.ccertificateC` at
  `z = Expo.zC = 1 - 321/10^8` and `a = 43`: `Net.WnetC Ds ≤ 2^43` and `hmem`, `hphi` for
  `Net.Etot Ds Net.t0C (2^43 - Net.WnetC Ds)`.
-/

-- The `constructorNameAsVariable` linter exceeds the recursion depth on the role type
-- `Net.Role` of the colour network (a linter failure, not a proof failure); it is disabled here.
set_option linter.constructorNameAsVariable false

namespace OAI
namespace PowerSaving.Colour
namespace Final
open Finset Binary

/-! ### Histogram sums -/

/-- `Σ_{c<M} N(c) f(c) = Σ_{c ∈ E} f(c)` when every element of `E` is `< M`. -/
lemma sum_count_eq (M : ℕ) (f : ℕ → ℝ) (E : Multiset ℕ) (hE : ∀ c ∈ E, c < M) :
    ∑ c : Fin M, (E.count (c : ℕ) : ℝ) * f c = (E.map f).sum := by
  induction E using Multiset.induction_on with
  | empty => simp
  | cons a E ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ← ih (fun c hc => hE c (Multiset.mem_cons_of_mem hc))]
    simp only [Multiset.count_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    rw [Fintype.sum_eq_single ⟨a, hE a (Multiset.mem_cons_self _ _)⟩]
    · simp
    · intro c hc
      have : (c : ℕ) ≠ a := fun h => hc (Fin.ext h)
      simp [this]

lemma sum_count_eq' (M : ℕ) (f : ℕ → ℝ) (E : Multiset ℕ) (hE : ∀ c ∈ E, 1 ≤ c ∧ c < M) :
    ∑ c : Fin M, (E.count (c : ℕ) : ℝ) * f c = (E.map f).sum :=
  sum_count_eq M f E (fun c hc => (hE c hc).2)

/-! ### The stage constants at `(30, 20, 41)` -/

lemma invBound_eq0 (nS a b c d : ℕ) :
    ICost.invBound (hs := Net.hsC) 0 24600 Expo.zC (Fintype.card (Trip (Net.hsC 0))) nS a b (c + d)
      2 10 = Expo.invCost 0 ⟨nS, a, c, b, d⟩ := by
  have e1 : ICost.bk1N (hs := Net.hsC) 0 = 0 := by decide
  have e2 : ICost.bk1yN (hs := Net.hsC) 0 = 0 := by decide
  have e3 : ICost.botN (hs := Net.hsC) 0 = 0 := by decide
  have e4 : ICost.topN (hs := Net.hsC) 0 = 24570 := by decide
  have e5 : Fintype.card (Trip (Net.hsC 0)) = 4060 := by rw [num_trip]; decide
  have e6 : Net.hsC 0 = 30 := rfl
  unfold ICost.invBound
  rw [e1, e2, e3, e4, e5]
  simp only [ICost.φn, Expo.invCost, Expo.fixedCost, Expo.sideCost, Expo.xsCost,
    Expo.ysCost, Expo.longCost, Expo.phi, Expo.vC, Expo.hC, Expo.bk1R, Expo.bk2R, Expo.botR,
    Expo.hR, Expo.topR, Expo.sdR, Expo.txR, Expo.tyR, e6, Matrix.cons_val_zero]
  norm_num
  ring

lemma invBound_eq1 (nS a b c d : ℕ) :
    ICost.invBound (hs := Net.hsC) 1 24600 Expo.zC (Fintype.card (Trip (Net.hsC 1))) nS a b (c + d)
      2 10 = Expo.invCost 1 ⟨nS, a, c, b, d⟩ := by
  have e1 : ICost.bk1N (hs := Net.hsC) 1 = 551 := by decide
  have e2 : ICost.bk1yN (hs := Net.hsC) 1 = 551 := by decide
  have e3 : ICost.botN (hs := Net.hsC) 1 = 580 := by decide
  have e4 : ICost.topN (hs := Net.hsC) 1 = 24000 := by decide
  have e5 : Fintype.card (Trip (Net.hsC 1)) = 1140 := by rw [num_trip]; decide
  have e6 : Net.hsC 1 = 20 := rfl
  unfold ICost.invBound
  rw [e1, e2, e3, e4, e5]
  simp only [ICost.φn, Expo.invCost, Expo.fixedCost, Expo.sideCost, Expo.xsCost,
    Expo.ysCost, Expo.longCost, Expo.phi, Expo.vC, Expo.hC, Expo.bk1R, Expo.bk2R, Expo.botR,
    Expo.hR, Expo.topR, Expo.sdR, Expo.txR, Expo.tyR, e6, Matrix.cons_val_one]
  norm_num
  ring

lemma invBound_eq2 (nS a b c d : ℕ) :
    ICost.invBound (hs := Net.hsC) 2 24600 Expo.zC (Fintype.card (Trip (Net.hsC 2))) nS a b (c + d)
      2 10 = Expo.invCost 2 ⟨nS, a, c, b, d⟩ := by
  have e1 : ICost.bk1N (hs := Net.hsC) 2 = 23960 := by decide
  have e2 : ICost.bk1yN (hs := Net.hsC) 2 = 23960 := by decide
  have e3 : ICost.botN (hs := Net.hsC) 2 = 24559 := by decide
  have e4 : ICost.topN (hs := Net.hsC) 2 = 0 := by decide
  have e5 : Fintype.card (Trip (Net.hsC 2)) = 10660 := by rw [num_trip]; decide
  have e6 : Net.hsC 2 = 41 := rfl
  unfold ICost.invBound
  rw [e1, e2, e3, e4, e5]
  simp only [ICost.φn, Expo.invCost, Expo.fixedCost, Expo.sideCost, Expo.xsCost,
    Expo.ysCost, Expo.longCost, Expo.phi, Expo.vC, Expo.hC, Expo.bk1R, Expo.bk2R, Expo.botR,
    Expo.hR, Expo.topR, Expo.sdR, Expo.txR, Expo.tyR, e6, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  norm_num
  ring

lemma invBound_eq (j : Fin 3) (nS a b c d : ℕ) :
    ICost.invBound (hs := Net.hsC) j 24600 Expo.zC (Fintype.card (Trip (Net.hsC j))) nS a b (c + d)
      2 10 = Expo.invCost j ⟨nS, a, c, b, d⟩ := by
  fin_cases j
  · exact invBound_eq0 nS a b c d
  · exact invBound_eq1 nS a b c d
  · exact invBound_eq2 nS a b c d


/-! ### The batch multiset of the whole network (any factor sizes)

Membership in the batch multisets is only ever handled here, for generic factor sizes: at the
concrete sizes, elaborating a hypothesis `c ∈ riseM …` over the roles makes Lean unfold the
`Fintype` instance of the 4.9·10¹⁰ bank keys. -/

section General
variable {hs : Fin 3 → ℕ} [∀ i, NeZero (hs i)]
variable (Ds : ∀ j, RegisterDesign (hs j)) (t0 : Key hs)

/-- The padding batches: `P` of size `1` and `P` of size `u - 1`; banks and auxiliary roles add
nothing after the last stage. -/
lemma Phi_pad (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (P : ℕ) :
    ICost.Phi ψ (riseM (Net.border Ds t0 P 3) (Net.sinkMid Ds t0 P)
      + riseM (Net.sinkMid Ds t0 P) (Net.sink Ds t0 P))
      = P * (ψ 1 + ψ (Fintype.card (Blk hs) - 1)) := by
  rw [ICost.Phi_add, ICost.Phi_riseM ψ h0, ICost.Phi_riseM ψ h0, ← sum_add_distrib]
  simp only [Fintype.sum_sum_type]
  have hpole : ((univ : Finset (Blk hs)) \ {Net.pole}).card = Fintype.card (Blk hs) - 1 := by
    rw [card_univ_sdiff, card_singleton]
  have hA : ∑ a : Net.AllAux Ds t0,
      (ψ (Net.sinkMid Ds t0 P (.inr (.inl a)) \ Net.border Ds t0 P 3 (.inr (.inl a))).card
      + ψ (Net.sink Ds t0 P (.inr (.inl a)) \ Net.sinkMid Ds t0 P (.inr (.inl a))).card) = 0 := by
    apply sum_eq_zero
    rintro ⟨j, o, x⟩ -
    simp [Net.border, Net.sinkMid, Net.sink, h0]
  rw [hA]
  simp [Net.border, Net.sinkMid, Net.sink, Net.region_full, Net.rim, h0, hpole]
  ring

/-- `Φ(E_total) = Σ_j |Inv j| Φ(E_inv,j) + P (φ 1 + φ(u-1))`. -/
lemma Phi_Etot (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (P : ℕ) :
    ICost.Phi ψ (Net.Etot Ds t0 P)
      = Fintype.card (Net.Inv t0 0) * ICost.Phi ψ (Inv.Einv 0 (Ds 0))
        + Fintype.card (Net.Inv t0 1) * ICost.Phi ψ (Inv.Einv 1 (Ds 1))
        + Fintype.card (Net.Inv t0 2) * ICost.Phi ψ (Inv.Einv 2 (Ds 2))
        + P * (ψ 1 + ψ (Fintype.card (Blk hs) - 1)) := by
  rw [Net.Etot, ICost.Phi_add, ICost.Phi_add, ICost.Phi_add, ICost.Phi_sum, ICost.Phi_sum,
    ICost.Phi_sum, Phi_pad Ds t0 ψ h0 P]
  simp only [sum_const, card_univ, nsmul_eq_mul]

lemma mem_pad (P : ℕ) (h2 : 2 ≤ Fintype.card (Blk hs)) :
    ∀ c ∈ riseM (Net.border Ds t0 P 3) (Net.sinkMid Ds t0 P)
      + riseM (Net.sinkMid Ds t0 P) (Net.sink Ds t0 P), 1 ≤ c ∧ c < Fintype.card (Blk hs) := by
  intro c hc
  have hne : c ≠ 0 := by
    rcases Multiset.mem_add.mp hc with h | h
    · obtain ⟨_, _, h'⟩ := ICost.mem_riseM h; exact h'
    · obtain ⟨_, _, h'⟩ := ICost.mem_riseM h; exact h'
  refine ⟨Nat.one_le_iff_ne_zero.mpr hne, ?_⟩
  by_contra hcM
  push Not at hcM
  set M := Fintype.card (Blk hs)
  have h0 : ICost.ind M 0 = 0 := by simp [ICost.ind]; omega
  have hall := Phi_pad Ds t0 (ICost.ind M) h0 P
  have e1 : ICost.ind M 1 = 0 := by simp [ICost.ind]; omega
  have e2 : ICost.ind M (M - 1) = 0 := by simp [ICost.ind]; omega
  rw [e1, e2, add_zero, mul_zero] at hall
  have hle : ICost.ind M c ≤ ICost.Phi (ICost.ind M) _ :=
    Multiset.single_le_sum (fun x hx => by
      obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hx; unfold ICost.ind; split_ifs <;> norm_num) _
      (Multiset.mem_map_of_mem (ICost.ind M) hc)
  have : ICost.ind M c = 1 := by simp [ICost.ind, hcM]
  linarith

/-- All batch sizes of the network lie in `[1, M)` once those of the invocations do. -/
lemma mem_Etot (P M : ℕ) (hinv : ∀ j, ∀ c ∈ Inv.Einv j (Ds j), 1 ≤ c ∧ c < M)
    (h2 : 2 ≤ Fintype.card (Blk hs)) (hM : Fintype.card (Blk hs) ≤ M) :
    ∀ c ∈ Net.Etot Ds t0 P, 1 ≤ c ∧ c < M := by
  intro c hc
  rw [Net.Etot] at hc
  rcases Multiset.mem_add.mp hc with h | h
  · rcases Multiset.mem_add.mp h with h | h
    · rcases Multiset.mem_add.mp h with h | h
      · obtain ⟨_, -, h⟩ := Multiset.mem_sum.mp h; exact hinv 0 c h
      · obtain ⟨_, -, h⟩ := Multiset.mem_sum.mp h; exact hinv 1 c h
    · obtain ⟨_, -, h⟩ := Multiset.mem_sum.mp h; exact hinv 2 c h
  · obtain ⟨h1, h2⟩ := mem_pad Ds t0 P h2 c h
    exact ⟨h1, lt_of_lt_of_le h2 hM⟩

end General

/-! ### The concrete network -/

section Network
variable (Ds : ∀ j, RegisterDesign (Net.hsC j))

lemma hsC_two (j : Fin 3) : 2 ≤ Net.hsC j := by fin_cases j <;> decide

lemma sizes_lt (j : Fin 3) : ICost.bk1N (hs := Net.hsC) j < 24600 ∧
    ICost.bk1yN (hs := Net.hsC) j < 24600 ∧ ICost.botN (hs := Net.hsC) j < 24600 ∧
    ICost.topN (hs := Net.hsC) j < 24600 ∧ Net.hsC j < 24600 := by
  fin_cases j <;> decide

/-- **All batch sizes of the network lie in `[1, u)`** (`hmem` of `Net.ccertificateC`). -/
theorem mem_EtotC (P : ℕ) : ∀ c ∈ Net.Etot Ds Net.t0C P, 1 ≤ c ∧ c < 24600 :=
  mem_Etot Ds Net.t0C P 24600 (fun j => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := sizes_lt j
      exact ICost.mem_Einv j (Ds j) (hsC_two j) 24600 h1 h2 h3 h4 h5)
    (by rw [Net.card_blk_C]; norm_num) (by rw [Net.card_blk_C])

/-- The per-invocation counts of the design `Ds j`. -/
noncomputable def dcounts (j : Fin 3) : Expo.Counts :=
  ⟨Fintype.card (Ds j).Side, ICost.nXs j (Ds j) 2, ICost.nXl j (Ds j) 2, ICost.nYs j (Ds j) 10,
    ICost.nYl j (Ds j) 10⟩

lemma xs_add_xl (j : Fin 3) :
    ICost.nXs j (Ds j) 2 + ICost.nXl j (Ds j) 2 = Fintype.card (Ds j).XReg := by
  unfold ICost.nXs ICost.nXl
  rw [card_filter_add_card_filter_not, card_univ]

lemma ys_add_yl (j : Fin 3) :
    ICost.nYs j (Ds j) 10 + ICost.nYl j (Ds j) 10 = Fintype.card (Ds j).YReg := by
  unfold ICost.nYs ICost.nYl
  rw [card_filter_add_card_filter_not, card_univ]

lemma wnet_eq : Expo.wnet (dcounts Ds) = Net.WnetC Ds := by
  rw [Net.WnetC_eq, Net.card_auxpart, Net.card_auxpart, Net.card_auxpart, ← xs_add_xl, ← xs_add_xl,
    ← xs_add_xl, ← ys_add_yl, ← ys_add_yl, ← ys_add_yl]
  simp only [Expo.wnet, dcounts, Fin.sum_univ_three, Expo.invC, Expo.hC, Expo.N0C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- `Φ(E_total)` is bounded by the cost-class total of `Exponent.lean`. -/
lemma Phi_Etot_le (P : ℕ) :
    ICost.Phi (ICost.φn 24600 Expo.zC) (Net.Etot Ds Net.t0C P) ≤ Expo.totalCost (dcounts Ds) P := by
  have h0 : ICost.φn 24600 Expo.zC 0 = 0 := ICost.φn_zero _ _ Expo.zC_pos.ne'
  obtain ⟨c0, c1, c2⟩ := Net.card_inv_C
  rw [Phi_Etot Ds Net.t0C _ h0 P, c0, c1, c2, Net.card_blk_C]
  have hb : ∀ j, ICost.Phi (ICost.φn 24600 Expo.zC) (Inv.Einv j (Ds j))
      ≤ Expo.invCost j (dcounts Ds j) := fun j => by
    have := ICost.Phi_Einv_le j (Ds j) (u := 24600) (by norm_num) Expo.zC_pos Expo.zC_le_one
      (hsC_two j) 2 10 (by norm_num) (by norm_num)
    rw [invBound_eq] at this
    exact this
  have hpad : ICost.φn 24600 Expo.zC 1 + ICost.φn 24600 Expo.zC (24600 - 1) = Expo.padCost := by
    simp [ICost.φn, Expo.padCost, Expo.phi]
  rw [hpad]
  unfold Expo.totalCost
  simp only [Fin.sum_univ_three, Expo.invC, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Nat.cast_ofNat]
  have := hb 0; have := hb 1; have := hb 2
  linarith

/-- **The remaining obligations of the colour certificate** (`hW`, `hmem`, `hphi` of
`Net.ccertificateC` at `z = Expo.zC = 1 - 3.21·10⁻⁶`, `a = 43`), for any designs whose counts per
factor are dominated by the design counts of FORMALIZATION_CNET.md §5.3:

* `#Side ≤ sideC j`;
* `#XReg ≤ coordX j + sX j`, and at most `sX j` X-registers have more than 2 level changes;
* `#YReg ≤ coordY j + sY j`, and at most `sY j` Y-registers have more than 10 level changes;
* `sX j + sY j ≤ sunC j` (the sunflower registers). -/
theorem final_obligations (sX sY : Fin 3 → ℕ) (hsun : ∀ j, sX j + sY j ≤ Expo.sunC j)
    (hside : ∀ j, Fintype.card (Ds j).Side ≤ Expo.sideC j)
    (hx : ∀ j, Fintype.card (Ds j).XReg ≤ Expo.coordX j + sX j)
    (hxl : ∀ j, ICost.nXl j (Ds j) 2 ≤ sX j)
    (hy : ∀ j, Fintype.card (Ds j).YReg ≤ Expo.coordY j + sY j)
    (hyl : ∀ j, ICost.nYl j (Ds j) 10 ≤ sY j) :
    Net.WnetC Ds ≤ 2 ^ 43 ∧
    (∀ c ∈ Net.Etot Ds Net.t0C (2 ^ 43 - Net.WnetC Ds), 1 ≤ c ∧ c < 24600) ∧
    ∑ c : Fin 24600, ((Net.Etot Ds Net.t0C (2 ^ 43 - Net.WnetC Ds)).count (c : ℕ) : ℝ)
      * ((c : ℝ) / 24600) ^ Expo.zC < 2 ^ 43 := by
  have hW : Net.WnetC Ds ≤ 2 ^ 43 := by
    rw [← wnet_eq]
    have h0 := hside 0; have h1 := hside 1; have h2 := hside 2
    have x0 := hx 0; have x1 := hx 1; have x2 := hx 2
    have y0 := hy 0; have y1 := hy 1; have y2 := hy 2
    have s0 := hsun 0; have s1 := hsun 1; have s2 := hsun 2
    have a0 := xs_add_xl Ds 0; have a1 := xs_add_xl Ds 1; have a2 := xs_add_xl Ds 2
    have b0 := ys_add_yl Ds 0; have b1 := ys_add_yl Ds 1; have b2 := ys_add_yl Ds 2
    simp only [Expo.wnet, dcounts, Fin.sum_univ_three, Expo.invC, Expo.hC, Expo.N0C, Expo.sideC,
      Expo.coordX, Expo.coordY, Expo.sunC, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at *
    omega
  refine ⟨hW, mem_EtotC Ds _, ?_⟩
  set P := 2 ^ 43 - Net.WnetC Ds
  have hP : P + Expo.wnet (dcounts Ds) = 2 ^ 43 := by rw [wnet_eq]; omega
  have key := sum_count_eq' 24600 (fun c : ℕ => ((c : ℝ) / 24600) ^ Expo.zC) (Net.Etot Ds Net.t0C P)
    (mem_EtotC Ds P)
  have hx' : ∀ j, (dcounts Ds j).xs + (dcounts Ds j).xl ≤ Expo.coordX j + sX j := by
    intro j; simp only [dcounts]; rw [xs_add_xl]; exact hx j
  have hy' : ∀ j, (dcounts Ds j).ys + (dcounts Ds j).yl ≤ Expo.coordY j + sY j := by
    intro j; simp only [dcounts]; rw [ys_add_yl]; exact hy j
  have hPhi : ((Net.Etot Ds Net.t0C P).map (fun c : ℕ => ((c : ℝ) / 24600) ^ Expo.zC)).sum
      = ICost.Phi (ICost.φn 24600 Expo.zC) (Net.Etot Ds Net.t0C P) := rfl
  beta_reduce at key
  rw [key, hPhi]
  calc ICost.Phi (ICost.φn 24600 Expo.zC) (Net.Etot Ds Net.t0C P)
      ≤ Expo.totalCost (dcounts Ds) P := Phi_Etot_le Ds P
    _ < 2 ^ 43 := Expo.totalCost_lt (dcounts Ds) P hP sX sY hsun hside hx' hxl hy' hyl

end Network

end Final
end PowerSaving.Colour
end OAI
