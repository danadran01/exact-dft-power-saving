import OAI.Computability.FourierTransform.Colour.Invocation

/-!
# Colour network, part 11: the invocation path (new)

The twelve gates of the forward schedule of Theorem C with their labels (`Inv.p0 … Inv.pend`),
composed as one `DMPath` whose matrix is `1 + D.eXY` (Lemma C.4, `RegisterDesign.net_eq`), and
the resulting forward (`y += x`) and reverse (`x −= y`, the inverse transpose) invocations.
-/

namespace OAI
namespace PowerSaving.Colour
namespace Inv
open Finset Matrix Binary RegisterDesign

variable {hs : Fin 3 → ℕ} [∀ i, NeZero (hs i)]
variable {j : Fin 3} {D : RegisterDesign (hs j)} {F : ∀ i, OBase (Fin (hs i))}

/-! ### Square-zero facts -/

lemma sq_zero (M : Matrix D.Box D.Box ℚ) (CM RM : Finset (Fin 6))
    (hc : ∀ i k, M i k ≠ 0 → D.kind k ∈ CM) (hr : ∀ i k, M i k ≠ 0 → D.kind i ∈ RM)
    (hd : Disjoint CM RM) : M * M = 0 := D.kind_mul_zero M M CM RM hc hr hd

lemma eG_sq : D.eG * D.eG = 0 := sq_zero _ _ _ D.cG D.rG (by decide)
lemma eR_sq : D.eR * D.eR = 0 := sq_zero _ _ _ D.cR D.rR (by decide)
lemma eW_sq : D.eW * D.eW = 0 := sq_zero _ _ _ D.cW D.rW (by decide)
lemma eU_sq : D.eU * D.eU = 0 := sq_zero _ _ _ D.cU D.rU (by decide)
lemma eKall_sq : D.eKall * D.eKall = 0 := sq_zero _ _ _ D.cK D.rK (by decide)
lemma eK_sq (ℓ : ℕ) : D.eK ℓ * D.eK ℓ = 0 :=
  sq_zero _ {4} {5} (fun i k hz => by simp [(D.eK_supp _ i k hz).2])
    (fun i k hz => by simp [(D.eK_supp _ i k hz).1]) (by decide)

/-! ### Gate synchronisation -/

/-- Shape of the support of `eR`, `eG`, `eKall`: one block. -/
lemma sync_block {Z : Matrix D.Box D.Box ℚ} {s : D.Box → Finset (Blk hs)} (I : Finset (Fin (hs j)))
    (hI : I = ∅ ∨ I = univ) (a b : Fin 6) (hZ : ∀ i k, Z i k ≠ 0 → D.kind i = a ∧ D.kind k = b)
    (hs' : ∀ i, D.kind i = a ∨ D.kind i = b → s i = L j I) : Sync (basisBox j D F) s Z :=
  sync_uniform I hI (fun i k hz => by
    obtain ⟨h1, h2⟩ := hZ i k hz
    exact ⟨hs' i (Or.inl h1), hs' k (Or.inr h2)⟩)

lemma kind_cases (i : D.Box) :
    (∃ T, i = D.bx T) ∨ (∃ S, i = D.byy S) ∨ (∃ c, i = D.bc c) ∨ (∃ σ, i = D.bs σ) ∨
    (∃ r, i = D.ba r) ∨ (∃ r, i = D.bb r) := by
  rcases i with ((T|S)|(c|σ|r|r))
  · exact Or.inl ⟨T, rfl⟩
  · exact Or.inr (Or.inl ⟨S, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨σ, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, rfl⟩))))

/-- Label of a kind-`κ` role in a phase given by `stamp`. -/
lemma stamp_kind {x y c : Finset (Blk hs)} {sd : D.Side → Finset (Blk hs)}
    {a : D.XReg → Finset (Blk hs)} {b : D.YReg → Finset (Blk hs)} (Λ : Finset (Blk hs))
    (i : D.Box)
    (h0 : D.kind i = 0 → x = Λ) (h1 : D.kind i = 1 → y = Λ) (h2 : D.kind i = 2 → c = Λ)
    (h3 : D.kind i = 3 → ∀ σ, sd σ = Λ) (h4 : D.kind i = 4 → ∀ r, a r = Λ)
    (h5 : D.kind i = 5 → ∀ r, b r = Λ) : stamp j D x y c sd a b i = Λ := by
  rcases i with ((T|S)|(c'|σ|r|r))
  · exact h0 rfl
  · exact h1 rfl
  · exact h2 rfl
  · exact h3 rfl σ
  · exact h4 rfl r
  · exact h5 rfl r

lemma sync1 : Sync (basisBox j D F) (p1 j D) D.eR :=
  sync_block ∅ (Or.inl rfl) 1 2 D.eR_supp (fun i hi => stamp_kind _ i
    (fun h => by rcases hi with e | e <;> simp_all) (fun _ => rfl) (fun _ => rfl)
    (fun h => by rcases hi with e | e <;> simp_all) (fun h => by rcases hi with e | e <;> simp_all)
    (fun h => by rcases hi with e | e <;> simp_all))

lemma sync7 : Sync (basisBox j D F) (p7 j D) D.eR :=
  sync_block ∅ (Or.inl rfl) 1 2 D.eR_supp (fun i hi => stamp_kind _ i
    (fun h => by rcases hi with e | e <;> simp_all) (fun _ => rfl) (fun _ => rfl)
    (fun h => by rcases hi with e | e <;> simp_all) (fun h => by rcases hi with e | e <;> simp_all)
    (fun h => by rcases hi with e | e <;> simp_all))

lemma sync6 : Sync (basisBox j D F) (p6 j D) D.eG :=
  sync_block univ (Or.inr rfl) 2 0 D.eG_supp (fun i hi => stamp_kind _ i
    (fun _ => rfl) (fun h => by rcases hi with e | e <;> simp_all) (fun _ => rfl)
    (fun h => by rcases hi with e | e <;> simp_all) (fun h => by rcases hi with e | e <;> simp_all)
    (fun h => by rcases hi with e | e <;> simp_all))

lemma sync9 : Sync (basisBox j D F) (p9 j D) D.eG :=
  sync_block univ (Or.inr rfl) 2 0 D.eG_supp (fun i hi => stamp_kind _ i
    (fun _ => rfl) (fun h => by rcases hi with e | e <;> simp_all) (fun _ => rfl)
    (fun h => by rcases hi with e | e <;> simp_all) (fun h => by rcases hi with e | e <;> simp_all)
    (fun h => by rcases hi with e | e <;> simp_all))

lemma sync3 : Sync (basisBox j D F) (p3 j D) D.eKall :=
  sync_block ∅ (Or.inl rfl) 5 4 D.eKall_supp (fun i hi => stamp_kind _ i
    (fun h => by rcases hi with e | e <;> simp_all) (fun h => by rcases hi with e | e <;> simp_all)
    (fun h => by rcases hi with e | e <;> simp_all) (fun h => by rcases hi with e | e <;> simp_all)
    (fun _ _ => rfl) (fun _ _ => rfl))

lemma sync10 : Sync (basisBox j D F) (p10 j D) D.eKall :=
  sync_block univ (Or.inr rfl) 5 4 D.eKall_supp (fun i hi => stamp_kind _ i
    (fun h => by rcases hi with e | e <;> simp_all) (fun h => by rcases hi with e | e <;> simp_all)
    (fun h => by rcases hi with e | e <;> simp_all) (fun h => by rcases hi with e | e <;> simp_all)
    (fun _ _ => rfl) (fun _ _ => rfl))

lemma sync12 : Sync (basisBox j D F) (p11 j D) D.eKall :=
  sync_block univ (Or.inr rfl) 5 4 D.eKall_supp (fun i hi => stamp_kind _ i
    (fun h => by rcases hi with e | e <;> simp_all) (fun h => by rcases hi with e | e <;> simp_all)
    (fun h => by rcases hi with e | e <;> simp_all) (fun h => by rcases hi with e | e <;> simp_all)
    (fun _ _ => rfl) (fun _ _ => rfl))

lemma sync2 : Sync (basisBox j D F) (p2 j D) D.eU := by
  intro i k hz
  obtain ⟨h1, h2⟩ := D.eU_supp i k hz
  have e1 : p2 j D i = L j ∅ := stamp_kind _ i (fun h => by simp_all) (fun _ => rfl)
    (fun h => by simp_all) (fun h => by simp_all) (fun h => by simp_all) (fun h => by simp_all)
  have e2 : p2 j D k = L j ∅ := stamp_kind _ k (fun h => by rcases h2 with e | e <;> simp_all)
    (fun h => by rcases h2 with e | e <;> simp_all) (fun h => by rcases h2 with e | e <;> simp_all)
    (fun _ _ => rfl) (fun h => by rcases h2 with e | e <;> simp_all) (fun _ _ => rfl)
  rw [e1, e2]; exact sync_any j D F ∅ (Or.inl rfl)

lemma sync11 : Sync (basisBox j D F) (p11 j D) D.eW := by
  intro i k hz
  obtain ⟨h1, h2⟩ := D.eW_supp i k hz
  have e1 : p11 j D i = L j univ := stamp_kind _ i (fun h => by rcases h1 with e | e <;> simp_all)
    (fun h => by rcases h1 with e | e <;> simp_all) (fun h => by rcases h1 with e | e <;> simp_all)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun h => by rcases h1 with e | e <;> simp_all)
  have e2 : p11 j D k = L j univ := stamp_kind _ k (fun _ => rfl) (fun h => by simp_all)
    (fun h => by simp_all) (fun h => by simp_all) (fun h => by simp_all) (fun h => by simp_all)
  rw [e1, e2]; exact sync_any j D F univ (Or.inr rfl)

section SizeNine
variable (hh : 9 ≤ hs j)
include hh

/-- Step 4: X, its X-registers and its side wires at `Xb(t_T)`. -/
lemma sync4 : Sync (basisBox j D F) (p4 j D) D.eW := by
  intro i k hz
  obtain ⟨h1, h2⟩ := D.eW_supp i k hz
  rcases kind_cases i with ⟨T, rfl⟩ | ⟨S, rfl⟩ | ⟨c, rfl⟩ | ⟨σ, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
    simp [RegisterDesign.kind] at h1
  all_goals
    rcases kind_cases k with ⟨T, rfl⟩ | ⟨S, rfl⟩ | ⟨c, rfl⟩ | ⟨σ', rfl⟩ | ⟨r', rfl⟩ | ⟨r', rfl⟩ <;>
      simp [RegisterDesign.kind] at h2
  · -- side wire σ ← x_T
    have hT : D.sx σ = T := by by_contra hne; exact hz (by simp [RegisterDesign.eW, hne])
    apply sync_of
    apply mat_singleton_congr
    simp only [fbase]
    rw [pairBase_left _ _ ⟨hh, D.side_ok σ⟩, tripBase_main _ (by omega), hT]
  · -- X-register r ← x_T
    have hT : D.xown r = T := by by_contra hne; exact hz (by simp [RegisterDesign.eW, hne])
    apply sync_of
    apply mat_singleton_congr
    simp only [fbase]
    rw [D.x_slot r, tripBase_main _ (by omega), hT]

/-- Step 8: Y, its Y-registers and its side wires at `Yt(t_S)`. -/
lemma sync8 : Sync (basisBox j D F) (p8 j D) D.eU := by
  intro i k hz
  obtain ⟨h1, h2⟩ := D.eU_supp i k hz
  rcases kind_cases i with ⟨T, rfl⟩ | ⟨S, rfl⟩ | ⟨c, rfl⟩ | ⟨σ, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
    simp [RegisterDesign.kind] at h1
  rcases kind_cases k with ⟨T, rfl⟩ | ⟨S', rfl⟩ | ⟨c, rfl⟩ | ⟨σ, rfl⟩ | ⟨r', rfl⟩ | ⟨r', rfl⟩ <;>
    simp [RegisterDesign.kind] at h2
  · -- y_S ← side wire σ
    have hS : D.sy σ = S := by by_contra hne; exact hz (by simp [RegisterDesign.eU, hne])
    apply sync_of
    apply mat_compl_congr
    apply mat_singleton_congr
    simp only [fbase]
    rw [pairBase_right _ _ ⟨hh, D.side_ok σ⟩, tripBase_main _ (by omega), hS]
  · -- y_S ← Y-register r'
    have hS : D.yown r' = S := by by_contra hne; exact hz (by simp [RegisterDesign.eU, hne])
    apply sync_of
    apply mat_compl_congr
    apply mat_singleton_congr
    simp only [fbase]
    rw [D.y_slot r', tripBase_main _ (by omega), hS]

end SizeNine

/-- Step 5, level `ℓ`: the transfers at level `ℓ` (D4). -/
lemma sync5 (ℓ : ℕ) : Sync (basisBox j D F) (p5 j D ℓ) (D.eK ℓ) := by
  intro i k hz
  obtain ⟨h1, h2⟩ := D.eK_supp ℓ i k hz
  rcases kind_cases i with ⟨T, rfl⟩ | ⟨S, rfl⟩ | ⟨c, rfl⟩ | ⟨σ, rfl⟩ | ⟨r, rfl⟩ | ⟨r', rfl⟩ <;>
    simp [RegisterDesign.kind] at h1
  rcases kind_cases k with ⟨T, rfl⟩ | ⟨S, rfl⟩ | ⟨c, rfl⟩ | ⟨σ, rfl⟩ | ⟨r, rfl⟩ | ⟨r'', rfl⟩ <;>
    simp [RegisterDesign.kind] at h2
  have hz' : D.tsum (fun τ => D.tlev τ = ℓ) r r' ≠ 0 := hz
  obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz'
  have hc : D.tx τ = r ∧ D.ty τ = r' ∧ D.tlev τ = ℓ := by
    by_contra hn; rw [if_neg hn] at hτ; exact hτ rfl
  obtain ⟨e1, e2, e3⟩ := hc
  apply sync_of
  simp only [fbase]
  rw [← e1, ← e2, ← e3]
  exact (D.sync τ).symm

/-! ### Composition -/

variable (j D F)

lemma eK_fsum : ∑ ℓ ∈ Finset.range (hs j), D.eK (ℓ + 1) = D.eKall :=
  (list_sum_range _ _).symm.trans D.eK_sum

/-- Step 5 as a loop over the levels `1..n`. -/
lemma step5 (n : ℕ) : DMPath (basisBox j D F) (p4 j D) (q5 j D n)
    (1 + ∑ ℓ ∈ Finset.range n, D.eK (ℓ + 1))
    (∑ ℓ ∈ Finset.range n, riseM (q5 j D ℓ) (p5 j D (ℓ + 1))) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    exact DMPath.of_id MPath.refl
  | succ n ih =>
    have g := (DMPath.paired (eK_sq (D := D) (n + 1)) (sync5 (F := F) (n + 1))).1
    have r := DMPath.rise (A := basisBox j D F) (inc_q5 j D n)
    have H := (ih.trans r).trans g
    have hz : D.eK (n + 1) * ∑ ℓ ∈ Finset.range n, D.eK (ℓ + 1) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro ℓ _
      exact D.kind_mul_zero _ _ {4} {5}
        (fun i k hz => by simp [(D.eK_supp _ i k hz).2])
        (fun i k hz => by simp [(D.eK_supp _ i k hz).1]) (by decide)
    refine DMPath.congrE (DMPath.congrM H ?_) ?_
    · rw [Matrix.one_mul, Finset.sum_range_succ, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
        Matrix.mul_one, hz, add_zero]
      abel
    · rw [Finset.sum_range_succ, add_zero]

/-- The batch multiset of one invocation. -/
def Einv : Multiset ℕ :=
  riseM (p0 j D) (p1 j D) + riseM (p1 j D) (p2 j D) + riseM (p2 j D) (p3 j D)
    + riseM (p3 j D) (p4 j D)
    + (∑ ℓ ∈ Finset.range (hs j), riseM (q5 j D ℓ) (p5 j D (ℓ + 1)))
    + riseM (q5 j D (hs j)) (p6 j D) + fallM (p6 j D) (p7 j D) + riseM (p7 j D) (p8 j D)
    + riseM (p8 j D) (p9 j D) + riseM (p9 j D) (p10 j D) + riseM (p10 j D) (p11 j D)
    + riseM (p11 j D) (pend j D)

/-- One invocation: the forward schedule of Theorem C as a paired grouped path (Lemma C.4). -/
theorem invocation_path (hh : 9 ≤ hs j) :
    DMPath (basisBox j D F) (p0 j D) (pend j D) (1 + D.eXY) (Einv j D) := by
  have h01 : (0 : Fin (hs j)) ≠ 1 := fin_zero_ne_one (by omega)
  have g1 := (DMPath.paired (eR_sq (D := D)) (sync1 (F := F))).2
  have g2 := (DMPath.paired (eU_sq (D := D)) (sync2 (F := F))).2
  have g3 := (DMPath.paired (eKall_sq (D := D)) (sync3 (F := F))).2
  have g4 := (DMPath.paired (eW_sq (D := D)) (sync4 (F := F) hh)).1
  have g6 := (DMPath.paired (eG_sq (D := D)) (sync6 (F := F))).1
  have g7 := (DMPath.paired (eR_sq (D := D)) (sync7 (F := F))).1
  have g8 := (DMPath.paired (eU_sq (D := D)) (sync8 (F := F) hh)).1
  have g9 := (DMPath.paired (eG_sq (D := D)) (sync9 (F := F))).2
  have g10 := (DMPath.paired (eKall_sq (D := D)) (sync10 (F := F))).2
  have g11 := (DMPath.paired (eW_sq (D := D)) (sync11 (F := F))).2
  have g12 := (DMPath.paired (eKall_sq (D := D)) (sync12 (F := F))).1
  have R : ∀ {s t : D.Box → Finset (Blk hs)}, (∀ r, s r ⊆ t r) →
      DMPath (basisBox j D F) s t 1 (riseM s t) := fun h => DMPath.rise h
  have H1 := (R (inc01 j D)).trans g1
  have H2 := (H1.trans (R (inc12 j D))).trans g2
  have H3 := (H2.trans (R (inc23 j D))).trans g3
  have H4 := (H3.trans (R (inc34 j D))).trans g4
  have H5 := H4.trans (step5 j D F (hs j))
  have H6 := (H5.trans (R (inc56 j D))).trans g6
  have H7 := (H6.trans (DMPath.fall (dec67 j D))).trans g7
  have H8 := (H7.trans (R (inc78 j D h01))).trans g8
  have H9 := (H8.trans (R (inc89 j D))).trans g9
  have H10 := (H9.trans (R (inc910 j D))).trans g10
  have H11 := (H10.trans (R (inc1011 j D))).trans g11
  have H := (H11.trans g12).trans (R (inc11e j D))
  refine DMPath.congrE (DMPath.congrM H ?_) ?_
  · simp only [Matrix.one_mul, Matrix.mul_one]
    rw [eK_fsum]
    exact D.net_eq
  · simp only [add_zero]; rfl

/-! ### Logical actions -/

omit [∀ i, NeZero (hs i)] in
lemma eXY_supp (i k : D.Box) (hz : D.eXY i k ≠ 0) : D.kind i = 1 ∧ D.kind k = 0 := by
  rcases i with ((_|_)|(_|_|_|_)) <;> rcases k with ((_|_)|(_|_|_|_)) <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd rfl hz

/-- Forward invocation (stages 1, 3): `y += x`. -/
def forward (x : D.Box → ℂ) : D.Box → ℂ
  | .inl (.inr S) => x (D.byy S) + x (D.bx S)
  | r => x r

/-- Reverse invocation (stage 2): `x −= y`. -/
def backward (x : D.Box → ℂ) : D.Box → ℂ
  | .inl (.inl T) => x (D.bx T) - x (D.byy T)
  | r => x r

lemma eXY_zero_row (i k : D.Box) (hi : D.kind i ≠ 1) : D.eXY i k = 0 := by
  by_contra hz; exact hi (eXY_supp j D i k hz).1

lemma eXY_zero_col (i k : D.Box) (hk : D.kind k ≠ 0) : D.eXY i k = 0 := by
  by_contra hz; exact hk (eXY_supp j D i k hz).2

lemma eXY_yx (S T : Trip (hs j)) : D.eXY (D.byy S) (D.bx T) = if S = T then 1 else 0 := rfl

lemma sum_row_one (x : D.Box → ℂ) (i : D.Box) :
    ∑ k, (((1 : Matrix D.Box D.Box ℚ) i k : ℚ) : ℂ) * x k = x i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Matrix.one_apply, Ne.symm hk]
  · simp

lemma sum_col_one (x : D.Box → ℂ) (i : D.Box) :
    ∑ k, (((1 : Matrix D.Box D.Box ℚ) k i : ℚ) : ℂ) * x k = x i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Matrix.one_apply, hk]
  · simp

lemma sum_row_xy (x : D.Box → ℂ) (S : Trip (hs j)) :
    ∑ k, ((D.eXY (D.byy S) k : ℚ) : ℂ) * x k = x (D.bx S) := by
  rw [Finset.sum_eq_single (D.bx S)]
  · simp [eXY_yx]
  · intro k _ hk
    by_cases hk0 : D.kind k = 0
    · rcases kind_cases k with ⟨T, rfl⟩ | ⟨T, rfl⟩ | ⟨c, rfl⟩ | ⟨σ, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
        simp [RegisterDesign.kind] at hk0
      have hT : S ≠ T := fun e => hk (by rw [e])
      rw [eXY_yx, if_neg hT]; simp
    · rw [eXY_zero_col j D _ _ hk0]; simp
  · simp

lemma sum_col_xy (x : D.Box → ℂ) (T : Trip (hs j)) :
    ∑ k, ((D.eXY k (D.bx T) : ℚ) : ℂ) * x k = x (D.byy T) := by
  rw [Finset.sum_eq_single (D.byy T)]
  · simp [eXY_yx]
  · intro k _ hk
    by_cases hk1 : D.kind k = 1
    · rcases kind_cases k with ⟨S, rfl⟩ | ⟨S, rfl⟩ | ⟨c, rfl⟩ | ⟨σ, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
        simp [RegisterDesign.kind] at hk1
      have hS : S ≠ T := fun e => hk (by rw [e])
      rw [eXY_yx, if_neg hS]; simp
    · rw [eXY_zero_row j D _ _ hk1]; simp
  · simp

lemma ap_f : actPoint (1 + D.eXY) = forward j D := by
  funext x i
  unfold actPoint
  simp only [Matrix.add_apply, Rat.cast_add, add_mul, Finset.sum_add_distrib, sum_row_one]
  rcases kind_cases i with ⟨T, rfl⟩ | ⟨S, rfl⟩ | ⟨c, rfl⟩ | ⟨σ, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [Finset.sum_eq_zero (fun k _ => by rw [eXY_zero_row j D _ _ (by simp [RegisterDesign.kind])]; simp)]
    simp [forward]
  · rw [sum_row_xy]; rfl
  all_goals
    rw [Finset.sum_eq_zero (fun k _ => by rw [eXY_zero_row j D _ _ (by simp [RegisterDesign.kind])]; simp)]
    simp [forward]

lemma ap_b : actPoint (1 - D.eXY)ᵀ = backward j D := by
  funext x i
  unfold actPoint
  simp only [Matrix.transpose_apply, Matrix.sub_apply, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib,
    sum_col_one]
  rcases kind_cases i with ⟨T, rfl⟩ | ⟨S, rfl⟩ | ⟨c, rfl⟩ | ⟨σ, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [sum_col_xy]; rfl
  all_goals
    rw [Finset.sum_eq_zero (fun k _ => by rw [eXY_zero_col j D _ _ (by simp [RegisterDesign.kind])]; simp)]
    simp [backward]

/-- One invocation, both directions, with the same labels and the same batches. -/
theorem invocation (hh : 9 ≤ hs j) :
    MPath (basisBox j D F) (p0 j D) (pend j D) (forward j D) (Einv j D) ∧
    MPath (basisBox j D F) (p0 j D) (pend j D) (backward j D) (Einv j D) := by
  have hX : D.eXY * D.eXY = 0 :=
    D.kind_mul_zero _ _ {0} {1} (fun i k hz => by simp [(eXY_supp j D i k hz).2])
      (fun i k hz => by simp [(eXY_supp j D i k hz).1]) (by decide)
  obtain ⟨H, G⟩ := DMPath.final hX (invocation_path j D F hh)
  exact ⟨ap_f j D ▸ H, ap_b j D ▸ G⟩

end Inv
end PowerSaving.Colour
end OAI
