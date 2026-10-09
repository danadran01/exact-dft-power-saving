import OAI.Computability.FourierTransform.Colour.Centres
import OAI.Computability.FourierTransform.Colour.ScalarCore

/-!
# Colour network, part 9: register designs and the scalar identity (Theorem C, Lemma C.4) (new)

`RegisterDesign h` is the abstract interface of results/C_sidewires.md §1 for one factor `F₂^h`:

* X-registers (owner `xown`) and Y-registers (owner `yown`), each with its own orthonormal basis of
  `F₂^h` adapted to its whole chain (this *is* (D1)–(D3): every residual of the chain is spanned by
  basis vectors), the slot of the owner's indicator, and a monotone level → index-set function
  (the chain; levels are the dimensions `1..h` of the meeting labels, step 5 of the schedule);
* transfers `(x, y, level)` whose two registers have the same projection at that level (D4);
* side pairs (paper 'mod' side wires);
* (D5) `cover`: every ordered orthogonal pair is covered exactly once by transfers and side pairs.

On the local invocation type `Box = (X ⊕ Y) ⊕ (centres ⊕ side ⊕ X-regs ⊕ Y-regs)` we define the block
maps `g r w u k` of the schedule and prove `net_eq`: the twelve gates multiply to `1 + eXY`
(`y += x`). (D5) is used exactly once, in `xy_entry`.
-/

namespace OAI
namespace PowerSaving.Colour
open Finset Matrix Binary

/-- A register design for one factor `F₂^h` (Theorem C, (D1)–(D5)). -/
structure RegisterDesign (h : ℕ) where
  XReg : Type
  YReg : Type
  Side : Type
  Tr : Type
  [xF : Fintype XReg]
  [xD : DecidableEq XReg]
  [yF : Fintype YReg]
  [yD : DecidableEq YReg]
  [sF : Fintype Side]
  [sD : DecidableEq Side]
  [tF : Fintype Tr]
  [tD : DecidableEq Tr]
  xown : XReg → Trip h
  yown : YReg → Trip h
  xbase : XReg → OBase (Fin h)
  ybase : YReg → OBase (Fin h)
  xslot : XReg → Fin h
  yslot : YReg → Fin h
  xlab : XReg → ℕ → Finset (Fin h)
  ylab : YReg → ℕ → Finset (Fin h)
  x_slot : ∀ r, (xbase r).v (xslot r) = tip (xown r)
  y_slot : ∀ r, (ybase r).v (yslot r) = tip (yown r)
  x_mem : ∀ r ℓ, xslot r ∈ xlab r ℓ
  y_out : ∀ r ℓ, yslot r ∉ ylab r ℓ
  x_mono : ∀ r, Monotone (xlab r)
  y_mono : ∀ r, Monotone (ylab r)
  tx : Tr → XReg
  ty : Tr → YReg
  tlev : Tr → ℕ
  tlev_mem : ∀ τ, tlev τ ∈ Finset.Icc 1 h
  sync : ∀ τ, (xbase (tx τ)).mat (xlab (tx τ) (tlev τ)) = (ybase (ty τ)).mat (ylab (ty τ) (tlev τ))
  sx : Side → Trip h
  sy : Side → Trip h
  side_ok : ∀ σ, neighbor (sx σ) (sy σ)
  cover : ∀ T S : Trip h,
    (univ.filter fun τ : Tr => xown (tx τ) = T ∧ yown (ty τ) = S).card
      + (univ.filter fun σ : Side => sx σ = T ∧ sy σ = S).card
      = if T ≠ S ∧ neighbor T S then 1 else 0

attribute [instance] RegisterDesign.xF RegisterDesign.xD RegisterDesign.yF RegisterDesign.yD
  RegisterDesign.sF RegisterDesign.sD RegisterDesign.tF RegisterDesign.tD

namespace RegisterDesign
variable {h : ℕ} (D : RegisterDesign h)

/-- Roles of one invocation: banks (X, Y), centres, side wires, X-registers, Y-registers. -/
abbrev Box := (Trip h ⊕ Trip h) ⊕ (Fin h ⊕ D.Side ⊕ D.XReg ⊕ D.YReg)

abbrev bx (T : Trip h) : D.Box := .inl (.inl T)
abbrev byy (S : Trip h) : D.Box := .inl (.inr S)
abbrev bc (i : Fin h) : D.Box := .inr (.inl i)
abbrev bs (σ : D.Side) : D.Box := .inr (.inr (.inl σ))
abbrev ba (r : D.XReg) : D.Box := .inr (.inr (.inr (.inl r)))
abbrev bb (r : D.YReg) : D.Box := .inr (.inr (.inr (.inr r)))

/-- Kind of a box: 0 X, 1 Y, 2 centre, 3 side, 4 X-register, 5 Y-register. -/
def kind : D.Box → Fin 6
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr (.inl _) => 2
  | .inr (.inr (.inl _)) => 3
  | .inr (.inr (.inr (.inl _))) => 4
  | .inr (.inr (.inr (.inr _))) => 5

/-! ### The block maps of the schedule -/

/-- `g`: centres `+= G x`. -/
def eG : Matrix D.Box D.Box ℚ := fun i k =>
  match i, k with
  | .inr (.inl c), .inl (.inl T) => glocal h c T
  | _, _ => 0

/-- `r`: `y += R c`. -/
def eR : Matrix D.Box D.Box ℚ := fun i k =>
  match i, k with
  | .inl (.inr S), .inr (.inl c) => rlocal h S c
  | _, _ => 0

/-- `w`: X-registers and side wires `+= x_owner` (Π + V). -/
def eW : Matrix D.Box D.Box ℚ := fun i k =>
  match i, k with
  | .inr (.inr (.inr (.inl r))), .inl (.inl T) => if D.xown r = T then 1 else 0
  | .inr (.inr (.inl σ)), .inl (.inl T) => if D.sx σ = T then 1 else 0
  | _, _ => 0

/-- `u`: `y_S += Σ_{own b = S} b + Σ_{sy σ = S} K A_σ` (Ξ + J). -/
def eU : Matrix D.Box D.Box ℚ := fun i k =>
  match i, k with
  | .inl (.inr S), .inr (.inr (.inr (.inr r))) => if D.yown r = S then 1 else 0
  | .inl (.inr S), .inr (.inr (.inl σ)) => if D.sy σ = S then kval (D.sx σ) S else 0
  | _, _ => 0

/-- Transfers from X-register `r` to Y-register `r'` satisfying `p` (weighted by `K`). -/
def tsum (p : D.Tr → Prop) [DecidablePred p] (r : D.XReg) (r' : D.YReg) : ℚ :=
  ∑ τ, if D.tx τ = r ∧ D.ty τ = r' ∧ p τ then kval (D.xown r) (D.yown r') else 0

/-- `k_ℓ`: transfers at level `ℓ`, `b += K̃_ℓ a`. -/
def eK (ℓ : ℕ) : Matrix D.Box D.Box ℚ := fun i k =>
  match i, k with
  | .inr (.inr (.inr (.inr r'))), .inr (.inr (.inr (.inl r))) => D.tsum (fun τ => D.tlev τ = ℓ) r r'
  | _, _ => 0

/-- `k`: all transfers. -/
def eKall : Matrix D.Box D.Box ℚ := fun i k =>
  match i, k with
  | .inr (.inr (.inr (.inr r'))), .inr (.inr (.inr (.inl r))) => D.tsum (fun _ => True) r r'
  | _, _ => 0

/-- The net effect `y += x`. -/
def eXY : Matrix D.Box D.Box ℚ := fun i k =>
  match i, k with
  | .inl (.inr S), .inl (.inl T) => if S = T then 1 else 0
  | _, _ => 0

/-! ### Supports -/

lemma eG_supp (i k : D.Box) (hz : D.eG i k ≠ 0) : D.kind i = 2 ∧ D.kind k = 0 := by
  rcases i with ((_|_)|(_|_|_|_)) <;> rcases k with ((_|_)|(_|_|_|_)) <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd rfl hz

lemma eR_supp (i k : D.Box) (hz : D.eR i k ≠ 0) : D.kind i = 1 ∧ D.kind k = 2 := by
  rcases i with ((_|_)|(_|_|_|_)) <;> rcases k with ((_|_)|(_|_|_|_)) <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd rfl hz

lemma eW_supp (i k : D.Box) (hz : D.eW i k ≠ 0) : (D.kind i = 3 ∨ D.kind i = 4) ∧ D.kind k = 0 := by
  rcases i with ((_|_)|(_|_|_|_)) <;> rcases k with ((_|_)|(_|_|_|_)) <;>
    first | exact ⟨Or.inl rfl, rfl⟩ | exact ⟨Or.inr rfl, rfl⟩ | exact absurd rfl hz

lemma eU_supp (i k : D.Box) (hz : D.eU i k ≠ 0) : D.kind i = 1 ∧ (D.kind k = 3 ∨ D.kind k = 5) := by
  rcases i with ((_|_)|(_|_|_|_)) <;> rcases k with ((_|_)|(_|_|_|_)) <;>
    first | exact ⟨rfl, Or.inl rfl⟩ | exact ⟨rfl, Or.inr rfl⟩ | exact absurd rfl hz

lemma eK_supp (ℓ : ℕ) (i k : D.Box) (hz : D.eK ℓ i k ≠ 0) : D.kind i = 5 ∧ D.kind k = 4 := by
  rcases i with ((_|_)|(_|_|_|_)) <;> rcases k with ((_|_)|(_|_|_|_)) <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd rfl hz

lemma eKall_supp (i k : D.Box) (hz : D.eKall i k ≠ 0) : D.kind i = 5 ∧ D.kind k = 4 := by
  rcases i with ((_|_)|(_|_|_|_)) <;> rcases k with ((_|_)|(_|_|_|_)) <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd rfl hz

/-- Vanishing products from disjoint kinds. -/
lemma kind_mul_zero (M N : Matrix D.Box D.Box ℚ) (CM RN : Finset (Fin 6))
    (hM : ∀ i k, M i k ≠ 0 → D.kind k ∈ CM) (hN : ∀ i k, N i k ≠ 0 → D.kind i ∈ RN)
    (hd : Disjoint CM RN) : M * N = 0 :=
  mul_eq_zero_of_supp M N (fun j => D.kind j ∈ CM) hM
    (fun j k hz hj => disjoint_left.mp hd hj (hN j k hz))

lemma cG (i k : D.Box) (hz : D.eG i k ≠ 0) : D.kind k ∈ ({0} : Finset (Fin 6)) := by
  simp [(D.eG_supp i k hz).2]
lemma rG (i k : D.Box) (hz : D.eG i k ≠ 0) : D.kind i ∈ ({2} : Finset (Fin 6)) := by
  simp [(D.eG_supp i k hz).1]
lemma cR (i k : D.Box) (hz : D.eR i k ≠ 0) : D.kind k ∈ ({2} : Finset (Fin 6)) := by
  simp [(D.eR_supp i k hz).2]
lemma rR (i k : D.Box) (hz : D.eR i k ≠ 0) : D.kind i ∈ ({1} : Finset (Fin 6)) := by
  simp [(D.eR_supp i k hz).1]
lemma cW (i k : D.Box) (hz : D.eW i k ≠ 0) : D.kind k ∈ ({0} : Finset (Fin 6)) := by
  simp [(D.eW_supp i k hz).2]
lemma rW (i k : D.Box) (hz : D.eW i k ≠ 0) : D.kind i ∈ ({3, 4} : Finset (Fin 6)) := by
  rcases (D.eW_supp i k hz).1 with e | e <;> simp [e]
lemma cU (i k : D.Box) (hz : D.eU i k ≠ 0) : D.kind k ∈ ({3, 5} : Finset (Fin 6)) := by
  rcases (D.eU_supp i k hz).2 with e | e <;> simp [e]
lemma rU (i k : D.Box) (hz : D.eU i k ≠ 0) : D.kind i ∈ ({1} : Finset (Fin 6)) := by
  simp [(D.eU_supp i k hz).1]
lemma cK (i k : D.Box) (hz : D.eKall i k ≠ 0) : D.kind k ∈ ({4} : Finset (Fin 6)) := by
  simp [(D.eKall_supp i k hz).2]
lemma rK (i k : D.Box) (hz : D.eKall i k ≠ 0) : D.kind i ∈ ({5} : Finset (Fin 6)) := by
  simp [(D.eKall_supp i k hz).1]

/-! ### The X → Y block -/

lemma sum_box (f : D.Box → ℚ) :
    ∑ m, f m = (∑ T, f (D.bx T)) + (∑ S, f (D.byy S)) + (∑ c, f (D.bc c)) + (∑ σ, f (D.bs σ))
      + (∑ r, f (D.ba r)) + (∑ r, f (D.bb r)) := by
  simp only [Fintype.sum_sum_type]; ring

lemma rg_xy (S T : Trip h) : (D.eR * D.eG) (D.byy S) (D.bx T) = (rlocal h * glocal h) S T := by
  rw [Matrix.mul_apply, sum_box, Matrix.mul_apply]
  simp [eR, eG]

lemma uw_xy (S T : Trip h) : (D.eU * D.eW) (D.byy S) (D.bx T)
    = ((univ.filter fun σ : D.Side => D.sx σ = T ∧ D.sy σ = S).card : ℚ) * kval T S := by
  rw [Matrix.mul_apply, sum_box]
  simp only [eU, eW, mul_zero, sum_const_zero, zero_add, add_zero, mul_ite, mul_one, ite_self]
  rw [Finset.cast_card, Finset.sum_mul, Finset.sum_filter]
  apply sum_congr rfl
  intro σ _
  by_cases h1 : D.sx σ = T <;> by_cases h2 : D.sy σ = S <;> simp [h1, h2]

lemma uk_xy (S : Trip h) (r : D.XReg) : (D.eU * D.eKall) (D.byy S) (D.ba r)
    = ∑ τ, if D.tx τ = r ∧ D.yown (D.ty τ) = S then kval (D.xown r) S else 0 := by
  rw [Matrix.mul_apply, sum_box]
  simp only [eU, eKall, mul_zero, sum_const_zero, zero_add, add_zero]
  simp only [tsum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro τ _
  rw [Finset.sum_eq_single (D.ty τ)]
  · by_cases h1 : D.tx τ = r <;> by_cases h2 : D.yown (D.ty τ) = S <;> simp [h1, h2]
  · intro r' _ hr'
    simp [Ne.symm hr']
  · simp

lemma ukw_xy (S T : Trip h) : (D.eU * D.eKall * D.eW) (D.byy S) (D.bx T)
    = ((univ.filter fun τ : D.Tr => D.xown (D.tx τ) = T ∧ D.yown (D.ty τ) = S).card : ℚ)
        * kval T S := by
  rw [Matrix.mul_apply, sum_box]
  have hs : ∀ σ : D.Side, (D.eU * D.eKall) (D.byy S) (D.bs σ) = 0 := by
    intro σ
    rw [Matrix.mul_apply]; apply sum_eq_zero; intro m _
    by_cases hz : D.eKall m (D.bs σ) = 0
    · simp [hz]
    · exact absurd (D.eKall_supp m _ hz).2 (by simp [kind])
  simp only [eW, hs, mul_zero, zero_mul, sum_const_zero, zero_add, add_zero]
  simp only [uk_xy, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.cast_card, Finset.sum_mul, Finset.sum_filter]
  apply sum_congr rfl
  intro τ _
  rw [Finset.sum_eq_single (D.tx τ)]
  · by_cases h1 : D.xown (D.tx τ) = T <;> by_cases h2 : D.yown (D.ty τ) = S <;> simp [h1, h2]
  · intro r _ hr; simp [Ne.symm hr]
  · simp

/-- (D5) + Lemma A.2: the `X → Y` block is the identity. -/
theorem xy_entry (S T : Trip h) :
    (D.eR * D.eG + D.eU * D.eW + D.eU * D.eKall * D.eW) (D.byy S) (D.bx T)
      = if S = T then 1 else 0 := by
  rw [Matrix.add_apply, Matrix.add_apply, rg_xy, uw_xy, ukw_xy, ← rg_add_k S T]
  have hc := congrArg (Nat.cast : ℕ → ℚ) (D.cover T S)
  push_cast at hc
  have hq : ((univ.filter fun σ : D.Side => D.sx σ = T ∧ D.sy σ = S).card : ℚ)
      + ((univ.filter fun τ : D.Tr => D.xown (D.tx τ) = T ∧ D.yown (D.ty τ) = S).card : ℚ)
      = if T ≠ S ∧ neighbor T S then 1 else 0 := by
    rw [add_comm, hc]
  rw [add_assoc, ← add_mul, hq]
  split_ifs <;> ring

/-- Outside the `X → Y` block the three products vanish. -/
theorem off_entry (i k : D.Box) (hik : ¬ (D.kind i = 1 ∧ D.kind k = 0)) :
    (D.eR * D.eG + D.eU * D.eW + D.eU * D.eKall * D.eW) i k = 0 := by
  have z1 : (D.eR * D.eG) i k = 0 := by
    rw [Matrix.mul_apply]; apply sum_eq_zero; intro m _
    by_cases a : D.eR i m = 0
    · simp [a]
    by_cases b : D.eG m k = 0
    · simp [b]
    exact absurd ⟨(D.eR_supp i m a).1, (D.eG_supp m k b).2⟩ hik
  have z2 : (D.eU * D.eW) i k = 0 := by
    rw [Matrix.mul_apply]; apply sum_eq_zero; intro m _
    by_cases a : D.eU i m = 0
    · simp [a]
    by_cases b : D.eW m k = 0
    · simp [b]
    exact absurd ⟨(D.eU_supp i m a).1, (D.eW_supp m k b).2⟩ hik
  have z3 : (D.eU * D.eKall * D.eW) i k = 0 := by
    rw [Matrix.mul_apply]; apply sum_eq_zero; intro m _
    by_cases b : D.eW m k = 0
    · simp [b]
    have hk := (D.eW_supp m k b).2
    have : (D.eU * D.eKall) i m = 0 := by
      rw [Matrix.mul_apply]; apply sum_eq_zero; intro m' _
      by_cases a : D.eU i m' = 0
      · simp [a]
      exact absurd ⟨(D.eU_supp i m' a).1, hk⟩ hik
    simp [this]
  rw [Matrix.add_apply, Matrix.add_apply, z1, z2, z3]; ring

theorem block_eq : D.eR * D.eG + D.eU * D.eW + D.eU * D.eKall * D.eW = D.eXY := by
  ext i k
  rcases i with ((T|S)|(c|σ|r|r)) <;> rcases k with ((T'|S')|(c'|σ'|r'|r')) <;>
    first
    | exact (D.xy_entry S T').trans (by simp [eXY])
    | exact (D.off_entry _ _ (by simp [kind])).trans (by simp [eXY])

/-- Lemma C.4: the twelve gates of the forward invocation give `y += x`, for every design. -/
theorem net_eq :
    (1 + D.eKall) * ((1 - D.eW) * ((1 - D.eKall) * ((1 - D.eG) * ((1 + D.eU) * ((1 + D.eR) *
      ((1 + D.eG) * ((1 + D.eKall) * ((1 + D.eW) * ((1 - D.eKall) * ((1 - D.eU) *
      (1 - D.eR))))))))))) = 1 + D.eXY := by
  have z := D.kind_mul_zero
  rw [schedule_eq D.eG D.eR D.eU D.eW D.eKall
    (z _ _ _ _ D.cG D.rR (by decide)) (z _ _ _ _ D.cR D.rR (by decide))
    (z _ _ _ _ D.cU D.rR (by decide)) (z _ _ _ _ D.cW D.rR (by decide))
    (z _ _ _ _ D.cK D.rR (by decide))
    (z _ _ _ _ D.cG D.rU (by decide)) (z _ _ _ _ D.cR D.rU (by decide))
    (z _ _ _ _ D.cU D.rU (by decide)) (z _ _ _ _ D.cW D.rU (by decide))
    (z _ _ _ _ D.cK D.rU (by decide))
    (z _ _ _ _ D.cU D.rG (by decide)) (z _ _ _ _ D.cK D.rG (by decide))
    (z _ _ _ _ D.cW D.rG (by decide)) (z _ _ _ _ D.cG D.rG (by decide))
    (z _ _ _ _ D.cG D.rW (by decide)) (z _ _ _ _ D.cR D.rW (by decide))
    (z _ _ _ _ D.cW D.rW (by decide))
    (z _ _ _ _ D.cG D.rK (by decide)) (z _ _ _ _ D.cR D.rK (by decide))
    (z _ _ _ _ D.cW D.rK (by decide)) (z _ _ _ _ D.cK D.rK (by decide))]
  rw [add_assoc, add_assoc, ← add_assoc (D.eR * D.eG), block_eq]

lemma list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ ℓ ∈ Finset.range n, f ℓ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- The per-level transfer matrices add up to the full transfer matrix. -/
theorem eK_sum : ((List.range h).map fun ℓ => D.eK (ℓ + 1)).sum = D.eKall := by
  rw [list_sum_range]
  ext i k
  rw [Matrix.sum_apply]
  rcases i with ((T|S)|(c|σ|r|y)) <;> rcases k with ((T'|S')|(c'|σ'|x|y')) <;>
    try simp [eK, eKall]
  simp only [tsum, and_true]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro τ _
  have hm := Finset.mem_Icc.mp (D.tlev_mem τ)
  rw [Finset.sum_eq_single (D.tlev τ - 1)]
  · have e : D.tlev τ - 1 + 1 = D.tlev τ := by omega
    simp [e]
  · intro ℓ _ hℓ
    have : D.tlev τ ≠ ℓ + 1 := by omega
    simp [this]
  · intro hn; exfalso; apply hn; rw [Finset.mem_range]; omega

/-- Step 5 splits into the per-level gates (levels `1..h`). -/
theorem levels_eq : (((List.range h).map fun ℓ => D.eK (ℓ + 1)).map (fun a => 1 + a)).prod
    = 1 + D.eKall := by
  rw [levels_prod, eK_sum]
  intro a ha b hb
  simp only [List.mem_map, List.mem_range] at ha hb
  obtain ⟨ℓ, -, rfl⟩ := ha
  obtain ⟨ℓ', -, rfl⟩ := hb
  exact D.kind_mul_zero _ _ {4} {5}
    (fun i k hz => by simp [(D.eK_supp _ i k hz).2])
    (fun i k hz => by simp [(D.eK_supp _ i k hz).1]) (by decide)

end RegisterDesign

/-! ### Partial designs and their union (for the coordinate part ⊕ sunflower part) -/

/-- A register design whose transfers and side pairs cover exactly the ordered pairs satisfying
`Pr` ((D5) relative to `Pr`). The coordinate part uses `Pr = disjoint`, the sunflower part
`Pr = (meet = 2)`; `union` and `toDesign` assemble a full `RegisterDesign`. -/
structure PDesign (h : ℕ) (Pr : Trip h → Trip h → Prop) [DecidableRel Pr] where
  XReg : Type
  YReg : Type
  Side : Type
  Tr : Type
  [xF : Fintype XReg]
  [xD : DecidableEq XReg]
  [yF : Fintype YReg]
  [yD : DecidableEq YReg]
  [sF : Fintype Side]
  [sD : DecidableEq Side]
  [tF : Fintype Tr]
  [tD : DecidableEq Tr]
  xown : XReg → Trip h
  yown : YReg → Trip h
  xbase : XReg → OBase (Fin h)
  ybase : YReg → OBase (Fin h)
  xslot : XReg → Fin h
  yslot : YReg → Fin h
  xlab : XReg → ℕ → Finset (Fin h)
  ylab : YReg → ℕ → Finset (Fin h)
  x_slot : ∀ r, (xbase r).v (xslot r) = tip (xown r)
  y_slot : ∀ r, (ybase r).v (yslot r) = tip (yown r)
  x_mem : ∀ r ℓ, xslot r ∈ xlab r ℓ
  y_out : ∀ r ℓ, yslot r ∉ ylab r ℓ
  x_mono : ∀ r, Monotone (xlab r)
  y_mono : ∀ r, Monotone (ylab r)
  tx : Tr → XReg
  ty : Tr → YReg
  tlev : Tr → ℕ
  tlev_mem : ∀ τ, tlev τ ∈ Finset.Icc 1 h
  sync : ∀ τ, (xbase (tx τ)).mat (xlab (tx τ) (tlev τ)) = (ybase (ty τ)).mat (ylab (ty τ) (tlev τ))
  sx : Side → Trip h
  sy : Side → Trip h
  side_ok : ∀ σ, neighbor (sx σ) (sy σ)
  cover : ∀ T S : Trip h,
    (univ.filter fun τ : Tr => xown (tx τ) = T ∧ yown (ty τ) = S).card
      + (univ.filter fun σ : Side => sx σ = T ∧ sy σ = S).card
      = if Pr T S then 1 else 0

attribute [instance] PDesign.xF PDesign.xD PDesign.yF PDesign.yD PDesign.sF PDesign.sD PDesign.tF
  PDesign.tD

namespace PDesign
variable {h : ℕ}

lemma card_filter_sum {α β : Type*} [Fintype α] [Fintype β] (p : α ⊕ β → Prop) [DecidablePred p] :
    (univ.filter p).card
      = (univ.filter fun a => p (.inl a)).card + (univ.filter fun b => p (.inr b)).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_sum_type]

/-- Union of two partial designs for disjoint pair predicates. -/
def union {P₁ P₂ : Trip h → Trip h → Prop} [DecidableRel P₁] [DecidableRel P₂]
    (D₁ : PDesign h P₁) (D₂ : PDesign h P₂) (hdis : ∀ T S, ¬ (P₁ T S ∧ P₂ T S)) :
    PDesign h (fun T S => P₁ T S ∨ P₂ T S) where
  XReg := D₁.XReg ⊕ D₂.XReg
  YReg := D₁.YReg ⊕ D₂.YReg
  Side := D₁.Side ⊕ D₂.Side
  Tr := D₁.Tr ⊕ D₂.Tr
  xown := Sum.elim D₁.xown D₂.xown
  yown := Sum.elim D₁.yown D₂.yown
  xbase := Sum.elim D₁.xbase D₂.xbase
  ybase := Sum.elim D₁.ybase D₂.ybase
  xslot := Sum.elim D₁.xslot D₂.xslot
  yslot := Sum.elim D₁.yslot D₂.yslot
  xlab := Sum.elim D₁.xlab D₂.xlab
  ylab := Sum.elim D₁.ylab D₂.ylab
  x_slot := by rintro (r|r) <;> simp [D₁.x_slot, D₂.x_slot]
  y_slot := by rintro (r|r) <;> simp [D₁.y_slot, D₂.y_slot]
  x_mem := by rintro (r|r) ℓ <;> simp [D₁.x_mem, D₂.x_mem]
  y_out := by rintro (r|r) ℓ <;> simp [D₁.y_out, D₂.y_out]
  x_mono := by rintro (r|r) <;> simp [D₁.x_mono, D₂.x_mono]
  y_mono := by rintro (r|r) <;> simp [D₁.y_mono, D₂.y_mono]
  tx := Sum.map D₁.tx D₂.tx
  ty := Sum.map D₁.ty D₂.ty
  tlev := Sum.elim D₁.tlev D₂.tlev
  tlev_mem := by rintro (τ|τ) <;> simp [D₁.tlev_mem, D₂.tlev_mem]
  sync := by rintro (τ|τ) <;> simp [D₁.sync, D₂.sync]
  sx := Sum.elim D₁.sx D₂.sx
  sy := Sum.elim D₁.sy D₂.sy
  side_ok := by rintro (σ|σ) <;> simp [D₁.side_ok, D₂.side_ok]
  cover := by
    intro T S
    rw [card_filter_sum, card_filter_sum]
    have key : ((if P₁ T S then 1 else 0) + (if P₂ T S then 1 else 0) : ℕ)
        = if P₁ T S ∨ P₂ T S then 1 else 0 := by
      by_cases p1 : P₁ T S <;> by_cases p2 : P₂ T S
      · exact absurd ⟨p1, p2⟩ (hdis T S)
      all_goals simp [p1, p2]
    rw [← key, ← D₁.cover T S, ← D₂.cover T S]
    have e : ∀ a b c d : ℕ, a + b + (c + d) = (a + c) + (b + d) := by intros; ring
    rw [e]
    rfl

/-- A partial design covering exactly the ordered orthogonal pairs is a register design. -/
def toDesign {Pr : Trip h → Trip h → Prop} [DecidableRel Pr] (D : PDesign h Pr)
    (hPr : ∀ T S, Pr T S ↔ (T ≠ S ∧ neighbor T S)) : RegisterDesign h where
  XReg := D.XReg
  YReg := D.YReg
  Side := D.Side
  Tr := D.Tr
  xown := D.xown
  yown := D.yown
  xbase := D.xbase
  ybase := D.ybase
  xslot := D.xslot
  yslot := D.yslot
  xlab := D.xlab
  ylab := D.ylab
  x_slot := D.x_slot
  y_slot := D.y_slot
  x_mem := D.x_mem
  y_out := D.y_out
  x_mono := D.x_mono
  y_mono := D.y_mono
  tx := D.tx
  ty := D.ty
  tlev := D.tlev
  tlev_mem := D.tlev_mem
  sync := D.sync
  sx := D.sx
  sy := D.sy
  side_ok := D.side_ok
  cover := by
    intro T S
    rw [D.cover T S]
    by_cases hp : Pr T S
    · rw [if_pos hp, if_pos ((hPr T S).mp hp)]
    · rw [if_neg hp, if_neg (fun hh => hp ((hPr T S).mpr hh))]

/-- The pair predicates of the two parts. -/
def disjointP (T S : Trip h) : Prop := meet T S = 0
def twoP (T S : Trip h) : Prop := meet T S = 2

instance : DecidableRel (disjointP (h := h)) := fun T S => by unfold disjointP; infer_instance
instance : DecidableRel (twoP (h := h)) := fun T S => by unfold twoP; infer_instance

lemma parts_disjoint (T S : Trip h) : ¬ (disjointP T S ∧ twoP T S) := by
  rintro ⟨h1, h2⟩; unfold disjointP at h1; unfold twoP at h2; omega

lemma parts_cover (T S : Trip h) : (disjointP T S ∨ twoP T S) ↔ (T ≠ S ∧ neighbor T S) := by
  constructor
  · intro hp
    have hn : neighbor T S := hp
    exact ⟨neighbor_ne hn, hn⟩
  · rintro ⟨-, hn⟩; exact hn

/-- The full design of one factor: coordinate part (disjoint pairs) ∪ sunflower part (pairs
meeting in two points). -/
def assemble (Dc : PDesign h disjointP) (Dsun : PDesign h twoP) : RegisterDesign h :=
  (union Dc Dsun parts_disjoint).toDesign parts_cover

end PDesign

end PowerSaving.Colour
end OAI
