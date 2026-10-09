import OAI.Computability.FourierTransform.Grouped.GNetInvocation
import OAI.Computability.FourierTransform.TensorCertificate

/-!
# Grouped certificate for OpenAI's tensor network (new; not part of OpenAI's development)

OpenAI's `stage`, `all_stages` and `certificate` (ScalarNetwork.lean, TensorCertificate.lean)
re-derived for grouped paths. Every per-role frame edge is ONE batch; the full-role steps
`∅ → univ` (unused side wires, spare roles) are split as `1 + (32^3 - 1)`.

Main result: `gcertificate`. The word computes `kernel^{⊗}` on all `2^50` roles, every batch has
size `1 ≤ c < 32^3`, and the number of batches of size `c` is `NOAI c`, an explicit histogram
with 13 sizes (`edgeList`).
-/

namespace OAI
namespace PowerSaving.Cluster
open Finset Binary Matrix
noncomputable section

theorem gstage (rev : Bool) (j : J) :
    MPath bases (border j.val) (border (j.val+1)) (stageOp rev) ((4060^2) • invSum j) := by
  have hd : (4060^2) • invSum j = ∑ _i : Other j, invSum j := by
    rw [sum_const, card_univ, card_other]
  rw [hd]
  let h := fun _ : Other j => if rev then backward else forward
  apply MPath.parallel (position j) (pos_dis j) bases (h:=h)
  · intro i
    rw [bases_local,border_bp,border_end]
    cases rev
    · exact (ginvocation j (axes j i)).1
    · exact (ginvocation j (axes j i)).2
  · intro i x
    funext r
    rcases r with ((r|r)|(r|r)) <;> cases rev <;> rfl
  · rintro x ((k|k)|r) hr
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]
      exact ⟨bx (k j), congr_arg gx (locate_omit ..)⟩
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]
      exact ⟨byy (k j), congr_arg gy (locate_omit ..)⟩
    · rfl
  · rintro ((k|k)|(⟨i,p,a⟩|r)) hr
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]
      exact ⟨bx (k j), congr_arg gx (locate_omit ..)⟩
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]
      exact ⟨byy (k j), congr_arg gy (locate_omit ..)⟩
    · by_cases ig : i=j
      · subst i; exfalso; specialize hr p; apply hr; rw [cover_iff]; exact ⟨.inr a,rfl⟩
      · change (if i.val < j.val then univ else ∅) =
          (if i.val < j.val + 1 then univ else ∅)
        have h : i.val≠j.val := fun h => ig (Fin.ext h)
        simp only [show (i.val < j.val+1) ↔ (i.val < j.val) from (by omega)]
    · rfl

/-- Intermediate frame before the sink: spare roles get the single line `pole` first. -/
def sinkMid : Role → Mask
  | .inl (.inl _) => univ
  | .inl (.inr _) => univ \ {pole}
  | .inr (.inl _) => univ
  | .inr (.inr _) => {pole}

lemma border_le_mid (r : Role) : border 3 r ⊆ sinkMid r := by
  rcases r with ((k|k)|(⟨j,v,a⟩|r)) <;> simp [border, region_full, sinkMid, rim]

lemma mid_le_sink (r : Role) : sinkMid r ⊆ sink r := by
  rcases r with ((k|k)|(⟨j,v,a⟩|r)) <;> simp [sinkMid, sink]

/-- The batch multiset of the whole network path. -/
def Etot : Multiset ℕ :=
  (4060^2) • invSum 0 + (4060^2) • invSum 1 + (4060^2) • invSum 2 +
    (riseM (border 3) sinkMid + riseM sinkMid sink)

lemma gall_stages : MPath bases (border 0) sink exchange Etot := by
  have h := ((gstage false 0).trans (gstage true 1)).trans (gstage false 2)
  change MPath _ (border 0) (border 3) (stageOp false ∘ stageOp true ∘ stageOp false) _ at h
  have g := h.trans (MPath.inc_via bases border_le_mid mid_le_sink)
  have he : id ∘ (stageOp false ∘ stageOp true ∘ stageOp false) = exchange := by
    funext x r
    rcases r with (k|k)|r <;> simp [Function.comp_apply, stageOp,exchange,gx,gy]
  rw [he] at g
  exact g

/-- The final sink step: each spare role receives two batches, of sizes `1` and `32^3 - 1`. -/
def sinkList : List (ℕ × ℕ) := [(1, tower - nrRoles), (32767, tower - nrRoles)]

lemma sinkM_eq : riseM (border 3) sinkMid + riseM sinkMid sink = toMS sinkList := by
  have e1 : ∀ k : Key, sinkMid (.inl (.inl k)) \ border 3 (.inl (.inl k)) = ∅ := by
    intro k; simp [sinkMid, border, region_full]
  have e2 : ∀ k : Key, sinkMid (.inl (.inr k)) \ border 3 (.inl (.inr k)) = ∅ := by
    intro k; simp [sinkMid, border, rim, region_full]
  have e3 : ∀ x : AllAux, sinkMid (.inr (.inl x)) \ border 3 (.inr (.inl x)) = ∅ := by
    rintro ⟨j,v,a⟩; simp [sinkMid, border]
  have e4 : ∀ x : Spare, (sinkMid (.inr (.inr x)) \ border 3 (.inr (.inr x))).card = 1 := by
    intro x; simp [sinkMid, border]
  have f1 : ∀ k : Key, sink (.inl (.inl k)) \ sinkMid (.inl (.inl k)) = ∅ := by
    intro k; simp [sinkMid, sink]
  have f2 : ∀ k : Key, sink (.inl (.inr k)) \ sinkMid (.inl (.inr k)) = ∅ := by
    intro k; simp [sinkMid, sink]
  have f3 : ∀ x : AllAux, sink (.inr (.inl x)) \ sinkMid (.inr (.inl x)) = ∅ := by
    intro x; simp [sinkMid, sink]
  have f4 : ∀ x : Spare, (sink (.inr (.inr x)) \ sinkMid (.inr (.inr x))).card = 32767 := by
    intro x; exact card_rest_pole
  simp only [riseM, Fintype.sum_sum_type, e1, e2, e3, e4, f1, f2, f3, f4, card_empty, bm_zero,
    sum_const_zero, zero_add, sum_const, card_univ, Fintype.card_fin, sinkList, toMS_cons,
    toMS_nil, add_zero]

/-- The explicit (size, multiplicity) list of all batches, edge by edge and stage by stage. -/
def rawList : List (ℕ × ℕ) :=
  scale (4060^2) (invList 1) ++ scale (4060^2) (invList 32) ++ scale (4060^2) (invList 1024) ++
    sinkList

lemma Etot_eq : Etot = toMS rawList := by
  have e0 : (32:ℕ)^(0:J).val = 1 := rfl
  have e1 : (32:ℕ)^(1:J).val = 32 := rfl
  have e2 : (32:ℕ)^(2:J).val = 1024 := rfl
  rw [Etot, invSum_eq, invSum_eq, invSum_eq, sinkM_eq, nsmul_toMS, nsmul_toMS, nsmul_toMS,
    rawList, toMS_append, toMS_append, toMS_append, e0, e1, e2]

/-! ### The histogram -/

/-- The grouped histogram of OpenAI's network: (batch size `c`, number of batches of size `c`).
Here `4060^2` is the number of invocations per stage, `nbN = 4060·3006` the number of neighbour
(used) side pairs and `nnN = 4060·1054` of unused side pairs per invocation, `33` the number of
centres, and `tower - nrRoles` the number of spare roles. -/
def edgeList : List (ℕ × ℕ) := [
  (1, 4 * 4060^2 * nbN + 3 * 4060^2 * nnN + (tower - nrRoles)),
  (30, 3 * 4060^2 * nbN),
  (31, 6 * 4060^3 + 4060^2 * nbN),
  (32, 9 * 33 * 4060^2),
  (961, 2 * 4060^3),
  (962, 4060^2 * nbN),
  (992, 33 * 4060^2),
  (1023, 4060^2 * nbN),
  (31713, 2 * 4060^3),
  (31714, 4060^2 * nbN),
  (31744, 4060^2 * nbN + 33 * 4060^2),
  (32736, 4060^2 * nbN + 66 * 4060^2),
  (32767, 3 * 4060^2 * nnN + (tower - nrRoles))]

/-- Number of batches of size `c`. -/
def NOAI (c : ℕ) : ℕ := ((edgeList.filter (·.1 = c)).map (·.2)).sum

def supp : List ℕ := [1, 30, 31, 32, 961, 962, 992, 1023, 31713, 31714, 31744, 32736, 32767]

lemma raw_supp : ∀ e ∈ rawList, e.1 = 0 ∨ e.1 ∈ supp := by decide +kernel

lemma edge_supp : ∀ e ∈ edgeList, e.1 ∈ supp ∧ 1 ≤ e.1 ∧ e.1 < mcol := by decide +kernel

lemma hist_raw_supp : ∀ c ∈ supp, hist rawList c = NOAI c := by decide +kernel

lemma NOAI_eq_zero (c : ℕ) (hc : c ∉ supp) : NOAI c = 0 := by
  have : edgeList.filter (·.1 = c) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    simp only [decide_eq_true_eq]
    intro h
    exact hc (h ▸ (edge_supp e he).1)
  simp [NOAI, this]

lemma NOAI_zero : NOAI 0 = 0 := NOAI_eq_zero 0 (by decide)

lemma hist_raw (c : ℕ) : hist rawList c = NOAI c := by
  by_cases hc : c ∈ supp
  · exact hist_raw_supp c hc
  · rw [hist_eq_zero rawList supp raw_supp c hc, NOAI_eq_zero c hc]

lemma NOAI_support (c : ℕ) (h : 0 < NOAI c) : 1 ≤ c ∧ c < mcol := by
  by_contra hb
  have : edgeList.filter (·.1 = c) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    simp only [decide_eq_true_eq]
    intro h
    exact hb (h ▸ (edge_supp e he).2)
  simp [NOAI, this] at h

/-- **Grouped certificate** for OpenAI's tensor network: one word computing `kernel` on every
role, with explicit histogram `NOAI` of batch sizes, all in `[1, 32^3)`. -/
theorem gcertificate : ∃ p : GWord Blocks Role,
    (∀ c ∈ sizes p, 1 ≤ c ∧ c < mcol) ∧
    (∀ c, (sizes p).count c = NOAI c) ∧
    ∀ f (x : Data Blocks Role f), gwalk f p x = multiAct f (fun _ => kernel Blocks) x := by
  obtain ⟨p,hp,he⟩ := gall_stages
  obtain ⟨q,hq,hf⟩ := gtranslateAll correction
  have hs : sizes ((p ++ q) ++ [GMove.localM recoverM]) = sizes p := by
    rw [sizes_append, sizes_append, hq]; simp [sizes, GMove.size]
  have hc : ∀ c, (sizes ((p ++ q) ++ [GMove.localM recoverM])).count c = NOAI c := by
    intro c
    rw [hs, ← Multiset.coe_count, hp, Etot_eq, count_toMS, hist_raw]
  refine ⟨(p++q)++[.localM recoverM], ?_, hc, ?_⟩
  · intro c hc'
    have h1 := hc c
    have h2 : 0 < (sizes ((p ++ q) ++ [GMove.localM recoverM])).count c :=
      List.count_pos_iff.mpr hc'
    exact NOAI_support c (by omega)
  · intro f x
    rw [gwalk_append, gwalk_append, hf]
    obtain ⟨y,rfl⟩ := framed_surj bases (border 0) f x
    rw [he]
    simp only [gwalk, List.foldl_cons, List.foldl_nil, GMove.go, recover_eq]
    exact netEffect f y

end
end PowerSaving.Cluster
end OAI
