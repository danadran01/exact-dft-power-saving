import OAI.Computability.FourierTransform.Grouped.GNetCards

/-!
# Grouped invocation of OpenAI's network (new; not part of OpenAI's development)

OpenAI's `invocation_path` (NetworkInvocation.lean) with the frame steps grouped: every `Path.inc`
becomes `MPath.inc` (per role ONE batch per edge), the decrease `b3 → b4` becomes `MPath.dec`,
and the last edge `b7 → bend` goes through the intermediate label `bmid` so that the full-role
steps `∅ → univ` of the unused side wires are split as `1 + (32^3 - 1)`.
Gates, gate conditions and scalar identities are OpenAI's, unchanged.
-/

namespace OAI
namespace PowerSaving.Cluster
open Matrix Binary Finset
noncomputable section

/-- Grouped `DPath`: shear and inverse-transpose shear together, with batch multiset `E`. -/
def GDPath (j : J) (F : StartAxes) (s t : Lab) (M : Q) (E : Multiset ℕ) : Prop :=
  let A := basisBox j F
  ∃ N : Q, M * N = 1 ∧ MPath A s t (actPoint M) E ∧ MPath A s t (actPoint Nᵀ) E

namespace GDPath
variable {j : J} {F : StartAxes} {s t u : Lab} {M N : Q} {d e : Multiset ℕ}

lemma of_id (h : MPath (basisBox j F) s t id d) : GDPath j F s t 1 d := by
  refine ⟨1,mul_one _,?_,?_⟩ <;> simpa [ap_one]

lemma trans (a : GDPath j F s t M d) (b : GDPath j F t u N e) :
    GDPath j F s u (N*M) (d+e) := by
  obtain ⟨x,hx,hm,hn⟩ := a
  obtain ⟨y,hy,hl,hk⟩ := b
  refine ⟨x*y,?_,?_,?_⟩
  · rwa [Matrix.mul_assoc, ← Matrix.mul_assoc M, hx, one_mul]
  · rw [ap_mul]
    exact hm.trans hl
  · rw [transpose_mul, ap_mul]
    exact hn.trans hk

lemma paired (h : M*M=0) (g : syncBox j F s M) :
    GDPath j F s s (1+M) 0 ∧ GDPath j F s s (1-M) 0 := by
  have cond (i k) (h : M i k≠0) :
      frame (basisBox j F i) (s i) = frame (basisBox j F k) (s k) :=
    frame_congr _ _ _ _ (g i k h)
  constructor
  · refine ⟨1-M,inv_one_add h,MPath.gate _ ?_,MPath.gate _ ?_⟩
    · intro i k h
      by_cases hik : i=k
      · subst k; rfl
      · apply cond i k; simpa [one_apply,hik] using h
    · intro i k h
      by_cases hik : k=i
      · subst k; rfl
      · exact (cond k i (by simpa [one_apply,hik] using h)).symm
  · refine ⟨1+M,inv_one_sub h,MPath.gate _ ?_,MPath.gate _ ?_⟩
    · intro i k h
      by_cases hik : i=k
      · subst k; rfl
      · apply cond i k; simpa [one_apply,hik] using h
    · intro i k h
      by_cases hik : k=i
      · subst k; rfl
      · exact (cond k i (by simpa [one_apply,hik] using h)).symm

lemma rise (g : ∀ i, s i ⊆ t i) : GDPath j F s t 1 (riseM s t) :=
  of_id (MPath.inc _ g)

lemma fall (g : ∀ i, t i ⊆ s i) : GDPath j F s t 1 (fallM s t) :=
  of_id (MPath.dec _ g)

end GDPath

/-- Intermediate label splitting the unused side wires' step `∅ → univ` as `1 + (32^3 - 1)`. -/
def bmid (j : J) := stamp (big j) (ystep j 0) univ univ {pole}

lemma dec_b3_b4 (j : J) : ∀ r, b4 j r ⊆ b3 j r := by
  apply stamp_mono <;> first | exact fun _ h => h | exact sub_belt_big j

lemma inc_b7_bmid (j : J) : ∀ r, b7 j r ⊆ bmid j r := by
  apply stamp_mono <;> first | exact fun _ h => h | simp

lemma inc_bmid_bend (j : J) : ∀ r, bmid j r ⊆ bend j r := by
  apply stamp_mono <;> first | exact fun _ h => h | simp

/-- The batch multiset of one grouped invocation, in path order. -/
def invSum (j : J) : Multiset ℕ :=
  riseM (bp j) (b0 j) + riseM (b0 j) (b1 j) + riseM (b1 j) (b2 j) + riseM (b2 j) (b3 j) +
  fallM (b3 j) (b4 j) + riseM (b4 j) (b5 j) + riseM (b5 j) (b6 j) + riseM (b6 j) (b7 j) +
  riseM (b7 j) (bmid j) + riseM (bmid j) (bend j)

theorem ginvocation_path (j : J) (F : StartAxes) :
    GDPath j F (bp j) (bend j) (1+eXY) (invSum j) := by
  have h0 := GDPath.paired zero_JJ (sync0 j F) |>.2
  have h1 := GDPath.paired zero_RR (sync1 j F) |>.2
  have h2 := GDPath.paired zero_VV (sync2 j F) |>.1
  have h3 := GDPath.paired zero_GG (sync3 j F) |>.1
  have h4 := GDPath.paired zero_RR (sync4 j F) |>.1
  have h5 := GDPath.paired zero_JJ (sync5 j F) |>.1
  have h6 := GDPath.paired zero_GG (sync6 j F) |>.2
  have h7 := GDPath.paired zero_VV (sync7 j F) |>.2
  have rise : ∀ {u v : Lab}, (∀ i, u i ⊆ v i) → GDPath j F u v 1 (riseM u v) :=
    fun h => GDPath.rise h
  have down : GDPath j F (b3 j) (b4 j) 1 (fallM (b3 j) (b4 j)) := GDPath.fall (dec_b3_b4 j)
  have H0 := (rise (inc_bp_b0 j)).trans h0
  have H1 := H0.trans (rise (inc_b0_b1 j)) |>.trans h1
  have H2 := H1.trans (rise (inc_b1_b2 j)) |>.trans h2
  have H3 := H2.trans (rise (inc_b2_b3 j)) |>.trans h3
  have H4 := H3.trans down |>.trans h4
  have H5 := H4.trans (rise (inc_b4_b5 j)) |>.trans h5
  have H6 := H5.trans (rise (inc_b5_b6 j)) |>.trans h6
  have H7 := H6.trans (rise (inc_b6_b7 j)) |>.trans h7
  have Hl := (H7.trans (rise (inc_b7_bmid j))).trans (rise (inc_bmid_bend j))
  rw [← net_eq, net]
  simpa only [← Matrix.mul_assoc, mul_one, one_mul, add_zero, invSum] using Hl

theorem ginvocation (j : J) (F : StartAxes) :
    MPath (basisBox j F) (bp j) (bend j) forward (invSum j) ∧
    MPath (basisBox j F) (bp j) (bend j) backward (invSum j) := by
  obtain ⟨N, hN, H, G⟩ := ginvocation_path j F
  have h : N=1-eXY := by
    calc
      N = ((1-eXY)*(1+eXY))*N := by rw [inv_one_sub zero_XX, one_mul]
      _ = _ := by rw [Matrix.mul_assoc,hN,mul_one]
  subst N
  exact ⟨ap_f ▸ H,ap_b ▸ G⟩

/-- Explicit batch list of one invocation at stage `j` (`e = 32^j`): ten frame edges, each
listing the batch size of the five role classes (X wire ×4060, Y wire ×4060, used side ×nbN,
unused side ×nnN, centre ×33); zero sizes are omitted by `toMS`. -/
def invList (e : ℕ) : List (ℕ × ℕ) :=
  st 0 0 (e - 1) 0 0 ++                               -- bp → b0
  st 0 (31 * e - 31) 0 (32 * e - 32) 0 ++             -- b0 → b1
  st (31 * e - 31) 0 (31 * e - 30) 0 0 ++             -- b1 → b2
  st 31 0 0 32 0 ++                                   -- b2 → b3
  st 0 0 0 32 0 ++                                    -- b3 → b4 (removal)
  st 0 31 30 0 0 ++                                   -- b4 → b5
  st 0 0 0 32 0 ++                                    -- b5 → b6
  st 0 0 1 0 0 ++                                     -- b6 → b7
  st 0 0 (32768 - 32 * e) (32768 - 32 * e) 1 ++       -- b7 → bmid
  st 0 0 0 0 32767                                    -- bmid → bend

theorem invSum_eq (j : J) : invSum j = toMS (invList (32^j.val)) := by
  simp only [invSum, bp, b0, b1, b2, b3, b4, b5, b6, b7, bmid, bend, riseM_stamp, fallM_stamp,
    invList, toMS_append, Finset.sdiff_self, Finset.sdiff_empty,
    Finset.card_empty, card_ystart, card_belt, d_belt_ystart, d_xstep_xstart, d_xstep_ystart,
    d_big_xstep, belt_drop, d_ystep_belt, d_ystep_xstep, d_big_ystep, d_univ_big,
    Finset.card_singleton, card_rest_pole]

end
end PowerSaving.Cluster
end OAI
