import OAI.Computability.FourierTransform.Colour.Masks
import OAI.Computability.FourierTransform.Colour.Design
import OAI.Computability.FourierTransform.Colour.DMPath

/-!
# Colour network, part 10: one invocation (Theorem C, forward schedule + labels) (new)

For a stage `j`, a register design `D` for the factor `F₂^{h_j}` and the product basis `F` of the
other factors, we build the invocation path of Theorem C on the local roles `D.Box`:

* bases: `basisBox j D F b = dtensor (update F j (fbase b))` with the factor bases of §2.3 of
  FORMALIZATION_CNET.md (`tripBase` for banks, `canonical` for centres, `pairBase` for side wires,
  the design's own bases for registers);
* labels: the phases `p0 … pend` (all of the form `lam j I`, plus the bank in-labels and the
  terminals `∅`, `univ`);
* gates: the twelve gates of the forward schedule, step 5 split into the levels `1..h`;
* `invocation_path`: a `DMPath` from `p0` to `pend` with matrix `1 + D.eXY` (Lemma C.4 via
  `RegisterDesign.net_eq`), hence (`invocation`) the forward map `y += x` and, along the same labels
  and with the same batches, the reverse map `x −= y` (stage 2).
-/

namespace OAI
namespace PowerSaving.Colour
open Finset Matrix Binary

variable {hs : Fin 3 → ℕ} [∀ i, NeZero (hs i)]

/-- The blocks of the colour network: `∏_i F₂^{h_i}`. -/
abbrev Blk (hs : Fin 3 → ℕ) := ∀ i : Fin 3, Fin (hs i)

namespace Inv
variable (j : Fin 3) (D : RegisterDesign (hs j)) (F : ∀ i, OBase (Fin (hs i)))

/-- Factor-`j` basis of every local role (§2.3 of the blueprint). -/
def fbase : D.Box → OBase (Fin (hs j))
  | .inl (.inl T) => tripBase T
  | .inl (.inr S) => tripBase S
  | .inr (.inl _) => OBase.canonical _
  | .inr (.inr (.inl σ)) => pairBase (D.sx σ) (D.sy σ)
  | .inr (.inr (.inr (.inl r))) => D.xbase r
  | .inr (.inr (.inr (.inr r))) => D.ybase r

/-- Product basis of every local role. -/
def basisBox (b : D.Box) : OBase (Blk hs) := dtensor (Function.update F j (fbase j D b))

/-- The label family on this stage. -/
abbrev L (I : Finset (Fin (hs j))) : Finset (Blk hs) := lam (H := fun i => Fin (hs i)) j I

/-- Bank in-labels `E⊗⟨t⟩⊗Q` and `B⊗⟨t⟩⊗Q`. -/
def xin : Finset (Blk hs) := rect (H := fun i => Fin (hs i)) j true {0}
def yin : Finset (Blk hs) :=
  rect (H := fun i => Fin (hs i)) j true {0} \ rect (H := fun i => Fin (hs i)) j false {0}

/-- Labels per role kind. -/
def stamp (x y c : Finset (Blk hs)) (sd : D.Side → Finset (Blk hs))
    (a : D.XReg → Finset (Blk hs)) (b : D.YReg → Finset (Blk hs)) : D.Box → Finset (Blk hs)
  | .inl (.inl _) => x
  | .inl (.inr _) => y
  | .inr (.inl _) => c
  | .inr (.inr (.inl σ)) => sd σ
  | .inr (.inr (.inr (.inl r))) => a r
  | .inr (.inr (.inr (.inr r))) => b r

lemma stamp_mono {x y c x' y' c' : Finset (Blk hs)} {sd sd' : D.Side → Finset (Blk hs)}
    {a a' : D.XReg → Finset (Blk hs)} {b b' : D.YReg → Finset (Blk hs)}
    (hx : x ⊆ x') (hy : y ⊆ y') (hc : c ⊆ c') (hsd : ∀ σ, sd σ ⊆ sd' σ) (ha : ∀ r, a r ⊆ a' r)
    (hb : ∀ r, b r ⊆ b' r) :
    ∀ r, stamp j D x y c sd a b r ⊆ stamp j D x' y' c' sd' a' b' r := by
  rintro ((_|_)|(_|σ|r|r))
  · exact hx
  · exact hy
  · exact hc
  · exact hsd σ
  · exact ha r
  · exact hb r

/-! ### The phases -/

abbrev Bot : Finset (Blk hs) := L j ∅
abbrev Top : Finset (Blk hs) := L j univ
abbrev Xb0 : Finset (Blk hs) := L j {0}
abbrev Yt0 : Finset (Blk hs) := L j (univ \ {0})
abbrev Yt1 : Finset (Blk hs) := L j (univ \ {1})

def p0 := stamp j D (xin j) (yin j) ∅ (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)
def p1 := stamp j D (xin j) (Bot j) (Bot j) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)
def p2 := stamp j D (xin j) (Bot j) (Bot j) (fun _ => Bot j) (fun _ => ∅) (fun _ => Bot j)
def p3 := stamp j D (xin j) (Bot j) (Bot j) (fun _ => Bot j) (fun _ => Bot j) (fun _ => Bot j)
def p4 := stamp j D (Xb0 j) (Bot j) (Bot j) (fun _ => Xb0 j) (fun r => L j {D.xslot r})
  (fun _ => Bot j)
/-- Step 5, level `ℓ`. -/
def p5 (ℓ : ℕ) := stamp j D (Xb0 j) (Bot j) (Bot j) (fun _ => Xb0 j) (fun r => L j (D.xlab r ℓ))
  (fun r => L j (D.ylab r ℓ))
def p6 := stamp j D (Top j) (Bot j) (Top j) (fun _ => Xb0 j) (fun r => L j (D.xlab r (hs j)))
  (fun r => L j (D.ylab r (hs j)))
def p7 := stamp j D (Top j) (Bot j) (Bot j) (fun _ => Xb0 j) (fun r => L j (D.xlab r (hs j)))
  (fun r => L j (D.ylab r (hs j)))
def p8 := stamp j D (Top j) (Yt0 j) (Bot j) (fun _ => Yt1 j) (fun r => L j (D.xlab r (hs j)))
  (fun r => L j (univ \ {D.yslot r}))
def p9 := stamp j D (Top j) (Yt0 j) (Top j) (fun _ => Yt1 j) (fun r => L j (D.xlab r (hs j)))
  (fun r => L j (univ \ {D.yslot r}))
def p10 := stamp j D (Top j) (Yt0 j) (Top j) (fun _ => Yt1 j) (fun _ => Top j) (fun _ => Top j)
def p11 := stamp j D (Top j) (Yt0 j) (Top j) (fun _ => Top j) (fun _ => Top j) (fun _ => Top j)
def pend := stamp j D (Top j) (Yt0 j) univ (fun _ => univ) (fun _ => univ) (fun _ => univ)

/-- Step-5 phases including the start `p4`. -/
def q5 : ℕ → D.Box → Finset (Blk hs)
  | 0 => p4 j D
  | n + 1 => p5 j D (n + 1)

/-! ### Inclusions -/

lemma xin_le : xin (hs := hs) j ⊆ Xb0 j := by
  intro x hx
  rw [xin, mem_rect] at hx
  show x ∈ lam (H := fun i => Fin (hs i)) j {0}
  rw [mem_lam]; exact ⟨hx.1, Or.inr hx.2.2⟩

lemma yin_le : yin (hs := hs) j ⊆ Bot j := by
  intro x hx
  rw [yin, mem_sdiff, mem_rect, mem_rect] at hx
  show x ∈ lam (H := fun i => Fin (hs i)) j ∅
  rw [mem_lam]
  refine ⟨hx.1.1, Or.inl ?_⟩
  intro hp; exact hx.2 ⟨hx.1.1, fun _ => hp, hx.1.2.2⟩

lemma L_mono {I I' : Finset (Fin (hs j))} (h : I ⊆ I') : L j I ⊆ L j I' := lam_mono j h

lemma bot_le (I : Finset (Fin (hs j))) : Bot j ⊆ L j I := L_mono j (empty_subset _)
lemma le_top (I : Finset (Fin (hs j))) : L j I ⊆ Top j := L_mono j (subset_univ _)

lemma inc01 : ∀ r, p0 j D r ⊆ p1 j D r :=
  stamp_mono j D subset_rfl (yin_le j) (empty_subset _) (fun _ => subset_rfl) (fun _ => subset_rfl)
    (fun _ => subset_rfl)
lemma inc12 : ∀ r, p1 j D r ⊆ p2 j D r :=
  stamp_mono j D subset_rfl subset_rfl subset_rfl (fun _ => empty_subset _) (fun _ => subset_rfl)
    (fun _ => empty_subset _)
lemma inc23 : ∀ r, p2 j D r ⊆ p3 j D r :=
  stamp_mono j D subset_rfl subset_rfl subset_rfl (fun _ => subset_rfl) (fun _ => empty_subset _)
    (fun _ => subset_rfl)
lemma inc34 : ∀ r, p3 j D r ⊆ p4 j D r :=
  stamp_mono j D (xin_le j) subset_rfl subset_rfl (fun _ => bot_le j _) (fun _ => bot_le j _)
    (fun _ => subset_rfl)
lemma inc_q5 (n : ℕ) : ∀ r, q5 j D n r ⊆ p5 j D (n + 1) r := by
  cases n with
  | zero =>
    exact stamp_mono j D subset_rfl subset_rfl subset_rfl (fun _ => subset_rfl)
      (fun r => L_mono j (singleton_subset_iff.mpr (D.x_mem r 1))) (fun _ => bot_le j _)
  | succ n =>
    exact stamp_mono j D subset_rfl subset_rfl subset_rfl (fun _ => subset_rfl)
      (fun r => L_mono j (D.x_mono r (Nat.le_succ _))) (fun r => L_mono j (D.y_mono r (Nat.le_succ _)))
lemma q5_pos (n : ℕ) (hn : 0 < n) : q5 j D n = p5 j D n := by
  cases n with
  | zero => omega
  | succ n => rfl

lemma inc56 : ∀ r, q5 j D (hs j) r ⊆ p6 j D r := by
  rw [q5_pos j D (hs j) (Nat.pos_of_ne_zero (NeZero.ne _))]
  exact stamp_mono j D (le_top j _) subset_rfl (bot_le j _) (fun _ => subset_rfl)
    (fun _ => subset_rfl) (fun _ => subset_rfl)
lemma dec67 : ∀ r, p7 j D r ⊆ p6 j D r :=
  stamp_mono j D subset_rfl subset_rfl (bot_le j _) (fun _ => subset_rfl) (fun _ => subset_rfl)
    (fun _ => subset_rfl)
lemma inc78 (h01 : (0 : Fin (hs j)) ≠ 1) : ∀ r, p7 j D r ⊆ p8 j D r :=
  stamp_mono j D subset_rfl (bot_le j _) subset_rfl
    (fun _ => L_mono j (by simp [h01]))
    (fun _ => subset_rfl)
    (fun r => L_mono j (fun i hi => by
      rw [mem_sdiff, mem_singleton]
      exact ⟨mem_univ _, fun e : i = D.yslot r => D.y_out r (hs j) (e ▸ hi)⟩))
lemma inc89 : ∀ r, p8 j D r ⊆ p9 j D r :=
  stamp_mono j D subset_rfl subset_rfl (bot_le j _) (fun _ => subset_rfl) (fun _ => subset_rfl)
    (fun _ => subset_rfl)
lemma inc910 : ∀ r, p9 j D r ⊆ p10 j D r :=
  stamp_mono j D subset_rfl subset_rfl subset_rfl (fun _ => subset_rfl) (fun _ => le_top j _)
    (fun _ => le_top j _)
lemma inc1011 : ∀ r, p10 j D r ⊆ p11 j D r :=
  stamp_mono j D subset_rfl subset_rfl subset_rfl (fun _ => le_top j _) (fun _ => subset_rfl)
    (fun _ => subset_rfl)
lemma inc11e : ∀ r, p11 j D r ⊆ pend j D r :=
  stamp_mono j D subset_rfl subset_rfl (subset_univ _) (fun _ => subset_univ _)
    (fun _ => subset_univ _) (fun _ => subset_univ _)

/-! ### Synchronisation of the gates -/

/-- Generic sync: equal factor projections give equal label projections. -/
lemma sync_of {b b' : D.Box} {I I' : Finset (Fin (hs j))}
    (h : (fbase j D b).mat I = (fbase j D b').mat I') :
    (basisBox j D F b).mat (L j I) = (basisBox j D F b').mat (L j I') :=
  lam_sync j F _ _ h

lemma sync_any {b b' : D.Box} (I : Finset (Fin (hs j))) (hI : I = ∅ ∨ I = univ) :
    (basisBox j D F b).mat (L j I) = (basisBox j D F b').mat (L j I) := by
  rcases hI with rfl | rfl
  · exact (lam_sync_any j F _ _).1
  · exact (lam_sync_any j F _ _).2

variable {j D F}

/-- All nonzero entries of a matrix join roles whose labels are both `Bot` (or both `Top`). -/
lemma sync_uniform {Z : Matrix D.Box D.Box ℚ} {s : D.Box → Finset (Blk hs)} (I : Finset (Fin (hs j)))
    (hI : I = ∅ ∨ I = univ) (hs' : ∀ i k, Z i k ≠ 0 → s i = L j I ∧ s k = L j I) :
    Sync (basisBox j D F) s Z := by
  intro i k hz
  obtain ⟨h1, h2⟩ := hs' i k hz
  rw [h1, h2]; exact sync_any j D F I hI

end Inv
end PowerSaving.Colour
end OAI
