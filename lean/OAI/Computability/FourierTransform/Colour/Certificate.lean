import OAI.Computability.FourierTransform.Colour.Stages
import OAI.Computability.FourierTransform.TensorCertificate

/-!
# Colour network, part 13: the network word (new)

OpenAI's `TensorCertificate` for the colour network, grouped (`MPath`), for arbitrary register
designs `Ds j` with `9 ≤ h_j`, a reference key `t0` and `P` padding roles:

* `all_stages`: the three stages (forward, reverse, forward) from `border 0` to `sinkMid`, then the
  padding roles `∅ → {pole} → univ` (two batches, sizes `1` and `u − 1`, `MPath.inc_via`);
* `netEffect`: the terminal frames and the correction translation give `kernel` on every role;
* `cnet_word`: ONE grouped word computing `kernel^{⊗}` on all roles, whose batch multiset is
  `Etot` (explicitly: the invocation batches of all stages plus the padding batches).

The bounds on the batch sizes and on `Σ (c/u)^z` are stated on `Etot` (InvocationCost / Exponent).
-/

namespace OAI
namespace PowerSaving.Colour
namespace Net
open Finset Matrix Binary

variable {hs : Fin 3 → ℕ} [∀ i, NeZero (hs i)]
variable (Ds : ∀ j, RegisterDesign (hs j)) (t0 : Key hs) (P : ℕ)

/-- Terminal labels: `U_d^⊥` on `Y_d`, everything on the other roles. -/
def sink : Role Ds t0 P → Finset (Blk hs)
  | .inl (.inr _) => univ \ {pole}
  | _ => univ

/-- Intermediate frame before the sink: padding roles get the single line `pole` first. -/
def sinkMid : Role Ds t0 P → Finset (Blk hs)
  | .inl (.inl _) => univ
  | .inl (.inr _) => univ \ {pole}
  | .inr (.inl _) => univ
  | .inr (.inr _) => {pole}

lemma region_zero : region (hs := hs) 0 = {pole} := by
  ext x
  simp only [in_reg, Nat.zero_le, true_implies, mem_singleton, pole_iff]

lemma region_full : region (hs := hs) 3 = univ := by
  ext x
  simp only [in_reg, mem_univ, iff_true]
  intro i hi
  exact absurd i.isLt (by omega)

lemma border_le_mid (r : Role Ds t0 P) : border Ds t0 P 3 r ⊆ sinkMid Ds t0 P r := by
  rcases r with ((k|k)|(⟨j, o, a⟩|r))
  · simp [border, sinkMid, region_full]
  · simp [border, sinkMid, rim, region_full]
  · simp [border, sinkMid]
  · simp [border, sinkMid]

lemma mid_le_sink (r : Role Ds t0 P) : sinkMid Ds t0 P r ⊆ sink Ds t0 P r := by
  rcases r with ((k|k)|(⟨j, o, a⟩|r)) <;> simp [sinkMid, sink]

/-- The batch multiset of the whole network path. -/
def Etot : Multiset ℕ :=
  (∑ _o : Inv t0 0, Inv.Einv 0 (Ds 0)) + (∑ _o : Inv t0 1, Inv.Einv 1 (Ds 1))
    + (∑ _o : Inv t0 2, Inv.Einv 2 (Ds 2))
    + (riseM (border Ds t0 P 3) (sinkMid Ds t0 P) + riseM (sinkMid Ds t0 P) (sink Ds t0 P))

/-- `X_d ↦ −Y_d`, `Y_d ↦ X_d`, auxiliary roles unchanged. -/
def exchange (x : Role Ds t0 P → ℂ) : Role Ds t0 P → ℂ
  | .inl (.inl k) => -x (gy Ds t0 P k)
  | .inl (.inr k) => x (gx Ds t0 P k)
  | r => x r

theorem all_stages (hh : ∀ j, 9 ≤ hs j) :
    MPath (bases Ds t0 P) (border Ds t0 P 0) (sink Ds t0 P) (exchange Ds t0 P) (Etot Ds t0 P) := by
  have h := ((stage Ds t0 P false 0 (hh 0)).trans (stage Ds t0 P true 1 (hh 1))).trans
    (stage Ds t0 P false 2 (hh 2))
  have g := h.trans (MPath.inc_via (bases Ds t0 P) (border_le_mid Ds t0 P) (mid_le_sink Ds t0 P))
  have he : id ∘ (stageOp Ds t0 P false ∘ (stageOp Ds t0 P true ∘ stageOp Ds t0 P false))
      = exchange Ds t0 P := by
    funext x r
    rcases r with (k|k)|r <;> simp [Function.comp_apply, stageOp, exchange, gx, gy]
  rw [he] at g
  exact g

/-! ### Terminal correction -/

def correction : Role Ds t0 P → Space (Blk hs)
  | .inl (.inr k) => (bases Ds t0 P (gy Ds t0 P k)).v pole
  | _ => 0

def recover (x : Role Ds t0 P → ℂ) : Role Ds t0 P → ℂ
  | .inl (.inl k) => x (gy Ds t0 P k)
  | .inl (.inr k) => -x (gx Ds t0 P k)
  | r => x r

def pull : Role Ds t0 P → Role Ds t0 P
  | .inl (.inl k) => gy Ds t0 P k
  | .inl (.inr k) => gx Ds t0 P k
  | r => r

def flipSign : Role Ds t0 P → ℚ
  | .inl (.inr _) => -1
  | _ => 1

def recoverM : Matrix (Role Ds t0 P) (Role Ds t0 P) ℚ := fun i j =>
  if j = pull Ds t0 P i then flipSign Ds t0 P i else 0

lemma recover_eq : actPoint (recoverM Ds t0 P) = recover Ds t0 P := by
  funext x r
  unfold actPoint
  rw [sum_eq_single (pull Ds t0 P r)]
  · rcases r with (k|k)|r <;> simp [recoverM, pull, recover, flipSign]
  · intro i _ hi; simp [recoverM, hi]
  · simp

lemma border_inx (k : Key hs) : border Ds t0 P 0 (gx Ds t0 P k) = {pole} := region_zero
lemma border_iny (k : Key hs) : border Ds t0 P 0 (gy Ds t0 P k) = ∅ := by
  change rim 0 = ∅
  simp [rim, region_zero]
lemma border_inr (r : AllAux Ds t0 ⊕ Fin P) : border Ds t0 P 0 (.inr r) = ∅ := by
  rcases r with ⟨j, v, a⟩ | r <;> simp [border]

theorem netEffect (f : ℕ) (x : Data (Blk hs) (Role Ds t0 P) f) :
    point f (recover Ds t0 P)
      (multiAct f (fun r => Binary.shift (correction Ds t0 P r))
        (withFrame (bases Ds t0 P) (sink Ds t0 P) f (point f (exchange Ds t0 P) x))) =
    multiAct f (fun _ => kernel (Blk hs)) (withFrame (bases Ds t0 P) (border Ds t0 P 0) f x) := by
  have hneg (x : Sky (Blk hs) f → ℂ) : matAct f (kernel (Blk hs)) (-x) =
      -(matAct f (kernel (Blk hs)) x) := by rw [matAct, Matrix.mulVec_neg]; rfl
  funext r
  rcases r with (k|k)|r
  · change matAct f (Binary.shift (correction Ds t0 P (gy Ds t0 P k)))
        (matAct f (frame (bases Ds t0 P (gy Ds t0 P k)) _) (x (gx Ds t0 P k))) =
      matAct f (kernel (Blk hs))
        (matAct f (frame (bases Ds t0 P (gx Ds t0 P k)) (border Ds t0 P 0 (gx Ds t0 P k)))
          (x (gx Ds t0 P k)))
    rw [matAct_mul, matAct_mul, border_inx, terminal_calc]
    rfl
  · change -(matAct f (Binary.shift (0 : Space (Blk hs)))
        (matAct f (frame (bases Ds t0 P (gx Ds t0 P k)) univ) (-(x (gy Ds t0 P k))))) =
      matAct f _ (matAct f (frame (bases Ds t0 P (gy Ds t0 P k)) (border Ds t0 P 0 (gy Ds t0 P k)))
        (x (gy Ds t0 P k)))
    rw [border_iny, shift_zero, frame_zero, matAct_one, matAct_one, frame_univ, hneg, neg_neg]
  · change matAct f (Binary.shift (0 : Space (Blk hs)))
        (matAct f (frame (bases Ds t0 P (.inr r)) univ) (x (.inr r))) =
      matAct f _ (matAct f (frame (bases Ds t0 P (.inr r)) (border Ds t0 P 0 (.inr r))) (x (.inr r)))
    rw [border_inr, shift_zero, frame_zero, matAct_one, matAct_one, frame_univ]

/-- **The colour-network word.** One grouped word computing `kernel` on every role (for arbitrary
contents of all roles and any number `f` of columns), with batch multiset `Etot`. -/
theorem cnet_word (hh : ∀ j, 9 ≤ hs j) :
    ∃ p : GWord (Blk hs) (Role Ds t0 P),
      ((sizes p : List ℕ) : Multiset ℕ) = Etot Ds t0 P ∧
      ∀ f (x : Data (Blk hs) (Role Ds t0 P) f),
        gwalk f p x = multiAct f (fun _ => kernel (Blk hs)) x := by
  obtain ⟨p, hp, he⟩ := all_stages Ds t0 P hh
  obtain ⟨q, hq, hf⟩ := gtranslateAll (correction Ds t0 P)
  have hs' : sizes ((p ++ q) ++ [GMove.localM (recoverM Ds t0 P)]) = sizes p := by
    rw [sizes_append, sizes_append, hq]; simp [sizes, GMove.size]
  refine ⟨(p ++ q) ++ [.localM (recoverM Ds t0 P)], by rw [hs', hp], ?_⟩
  intro f x
  rw [gwalk_append, gwalk_append, hf]
  obtain ⟨y, rfl⟩ := framed_surj (bases Ds t0 P) (border Ds t0 P 0) f x
  rw [he]
  simp only [gwalk, List.foldl_cons, List.foldl_nil, GMove.go, recover_eq]
  exact netEffect Ds t0 P f y

end Net
end PowerSaving.Colour
end OAI
