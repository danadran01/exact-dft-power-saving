import OAI.Computability.FourierTransform.Colour.InvocationPath

/-!
# Colour network, part 12: roles, bases and the three stages (new)

OpenAI's `NetworkStages` for the colour network, on the dependent product `∏ F₂^{h_i}` and for
arbitrary register designs `Ds j` (one per factor):

* banks `X_d`, `Y_d` (`d : Key = ∏ Trip h_i`), with the fixed basis `⊗ tripBase d_i`;
* per invocation `(j, o)` (`o : Inv t0 j`, the keys whose `j`-th triple is the reference `t0 j`) the
  auxiliary roles of `(Ds j).Box` (centres, side wires, X- and Y-registers);
* `P` padding roles.

`stage rev j`: all invocations of stage `j` in parallel (`MPath.parallel`), from `border j` to
`border (j+1)`, with point map `y += x` (`rev = false`) or `x −= y` (`rev = true`), and batch
multiset `∑_o Einv j (Ds j)`.
-/

namespace OAI
namespace PowerSaving.Colour
open Finset Matrix Binary

variable {hs : Fin 3 → ℕ} [∀ i, NeZero (hs i)]

/-- Bank index: one triple per factor. -/
abbrev Key (hs : Fin 3 → ℕ) := ∀ j : Fin 3, Trip (hs j)

namespace Net
variable (Ds : ∀ j, RegisterDesign (hs j)) (t0 : Key hs) (P : ℕ)

/-- Invocations of stage `j`: keys with the reference triple at `j`. -/
abbrev Inv (t0 : Key hs) (j : Fin 3) := {d : Key hs // d j = t0 j}

/-- Auxiliary roles of one invocation of stage `j`. -/
abbrev AuxPart (j : Fin 3) := Fin (hs j) ⊕ (Ds j).Side ⊕ (Ds j).XReg ⊕ (Ds j).YReg

abbrev AllAux := Σ j : Fin 3, Inv t0 j × AuxPart Ds j

/-- All roles: banks, auxiliary roles of all invocations, padding. -/
abbrev Role := (Key hs ⊕ Key hs) ⊕ (AllAux Ds t0 ⊕ Fin P)

instance keyDec : DecidableEq (Key hs) := fun a b =>
  decidable_of_iff (∀ j, a j = b j) ⟨funext, fun h _ => h ▸ rfl⟩
instance invDec (j : Fin 3) : DecidableEq (Inv t0 j) := fun a b =>
  decidable_of_iff (a.1 = b.1) Subtype.ext_iff.symm
instance auxDec : DecidableEq (AllAux Ds t0) := by unfold AllAux; infer_instance
instance roleDec : DecidableEq (Role Ds t0 P) := by unfold Role; infer_instance

abbrev gx (d : Key hs) : Role Ds t0 P := .inl (.inl d)
abbrev gy (d : Key hs) : Role Ds t0 P := .inl (.inr d)
abbrev gu (j : Fin 3) (o : Inv t0 j) (a : AuxPart Ds j) : Role Ds t0 P := .inr (.inl ⟨j, o, a⟩)

/-! ### Positions of the local roles -/

/-- The key of the bank entry `T` of invocation `(j, o)`. -/
def locate (j : Fin 3) (o : Inv t0 j) (T : Trip (hs j)) : Key hs := Function.update o.1 j T

/-- The invocation of stage `j` containing the key `d`. -/
def omitJ (j : Fin 3) (d : Key hs) : Inv t0 j := ⟨Function.update d j (t0 j), by simp⟩

@[simp] lemma locate_omit (j : Fin 3) (d : Key hs) : locate t0 j (omitJ t0 j d) (d j) = d := by
  funext i; by_cases h : i = j
  · subst h; simp [locate]
  · simp [locate, omitJ, Function.update_of_ne h]

lemma loc_inj {j : Fin 3} {o o' : Inv t0 j} {T T' : Trip (hs j)}
    (h : locate t0 j o T = locate t0 j o' T') : o = o' ∧ T = T' := by
  have hT : T = T' := by simpa [locate] using congr_fun h j
  refine ⟨Subtype.ext (funext fun i => ?_), hT⟩
  by_cases hi : i = j
  · subst hi; rw [o.2, o'.2]
  · simpa [locate, Function.update_of_ne hi] using congr_fun h i

def world (j : Fin 3) (o : Inv t0 j) : (Ds j).Box → Role Ds t0 P
  | .inl (.inl T) => gx Ds t0 P (locate t0 j o T)
  | .inl (.inr T) => gy Ds t0 P (locate t0 j o T)
  | .inr a => gu Ds t0 P j o a

lemma world_inj (j : Fin 3) (o o' : Inv t0 j) (x y : (Ds j).Box)
    (h : world Ds t0 P j o x = world Ds t0 P j o' y) : o = o' ∧ x = y := by
  rcases x with ((T|T)|a) <;> rcases y with ((T'|T')|a') <;>
    simp only [world, gx, gy, gu, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  · obtain ⟨h1, h2⟩ := loc_inj t0 h; exact ⟨h1, by rw [h2]⟩
  · obtain ⟨h1, h2⟩ := loc_inj t0 h; exact ⟨h1, by rw [h2]⟩
  · have h' := Sigma.mk.inj_iff.mp h
    have e := eq_of_heq h'.2
    simp only [Prod.mk.injEq] at e
    exact ⟨e.1, by rw [e.2]⟩

def position (j : Fin 3) (o : Inv t0 j) : (Ds j).Box ↪ Role Ds t0 P :=
  ⟨world Ds t0 P j o, fun {_ _} h => (world_inj Ds t0 P j o o _ _ h).2⟩

lemma pos_dis (j : Fin 3) (o o' : Inv t0 j) (h : o ≠ o') (r : Role Ds t0 P) :
    r ∈ covered (position Ds t0 P j o) → r ∉ covered (position Ds t0 P j o') := by
  simp only [cover_iff, not_exists]
  rintro ⟨u, hu⟩ v hv
  exact h (world_inj Ds t0 P j o o' u v (hu.trans hv.symm)).1

/-! ### Bases -/

/-- The product basis of the fixed key coordinates of an invocation. -/
def axes (j : Fin 3) (o : Inv t0 j) : ∀ i, OBase (Fin (hs i)) := fun i => tripBase (o.1 i)

def bases : Role Ds t0 P → OBase (Blk hs)
  | .inl (.inl d) => dtensor (fun i => tripBase (d i))
  | .inl (.inr d) => dtensor (fun i => tripBase (d i))
  | .inr (.inl ⟨j, o, a⟩) => Inv.basisBox j (Ds j) (axes t0 j o) (.inr a)
  | .inr (.inr _) => OBase.canonical _

lemma axes_update (j : Fin 3) (o : Inv t0 j) (T : Trip (hs j)) :
    (fun i => tripBase (locate t0 j o T i)) = Function.update (axes t0 j o) j (tripBase T) := by
  funext i
  exact Function.apply_update (fun k (t : Trip (hs k)) => tripBase t) o.1 j T i

lemma bases_local (j : Fin 3) (o : Inv t0 j) :
    bases Ds t0 P ∘ position Ds t0 P j o = Inv.basisBox j (Ds j) (axes t0 j o) := by
  funext z
  rcases z with ((T|T)|a)
  · exact congrArg dtensor (axes_update t0 j o T)
  · exact congrArg dtensor (axes_update t0 j o T)
  · rfl

/-! ### Stage boundaries -/

/-- `X` labels between stages: the first `t` factors free, the rest at the triple line. -/
def region (t : ℕ) : Finset (Blk hs) := univ.filter fun x => ∀ i : Fin 3, t ≤ i.val → x i = 0
def pole : Blk hs := fun _ => 0
/-- `Y` labels between stages. -/
def rim (t : ℕ) : Finset (Blk hs) := region t \ {pole}

def border (t : ℕ) : Role Ds t0 P → Finset (Blk hs)
  | .inl (.inl _) => region t
  | .inl (.inr _) => rim t
  | .inr (.inl ⟨j, _, _⟩) => if j.val < t then univ else ∅
  | .inr (.inr _) => ∅

lemma in_reg (x : Blk hs) (t : ℕ) : x ∈ region t ↔ ∀ i : Fin 3, t ≤ i.val → x i = 0 := by
  simp [region]

lemma region_begin (j : Fin 3) : region (hs := hs) j.val = Inv.xin j := by
  ext x
  rw [in_reg, Inv.xin, mem_rect]
  constructor
  · intro h
    exact ⟨fun i hi => h i (le_of_lt hi), by simp, by simpa using h j le_rfl⟩
  · rintro ⟨hf, -, hj⟩ i hi
    rcases eq_or_lt_of_le hi with he | he
    · have e : j = i := Fin.ext he
      subst e; simpa using hj
    · exact hf i he

lemma region_end (j : Fin 3) : region (hs := hs) (j.val + 1) = Inv.Top j := by
  ext x
  rw [in_reg, Inv.Top, Inv.L, lam_univ, in_big]
  exact ⟨fun h i hi => h i hi, fun h i hi => h i hi⟩

lemma pole_iff (x : Blk hs) : x = pole ↔ ∀ i, x i = 0 := by
  constructor
  · rintro rfl i; rfl
  · intro h; funext i; exact h i

lemma rim_begin (j : Fin 3) : rim (hs := hs) j.val = Inv.yin j := by
  ext x
  rw [rim, mem_sdiff, region_begin, Inv.yin, mem_sdiff, mem_singleton, pole_iff, Inv.xin, mem_rect,
    mem_rect]
  constructor
  · rintro ⟨⟨hf, -, hj⟩, hp⟩
    refine ⟨⟨hf, fun e => absurd e (by decide), hj⟩, ?_⟩
    rintro ⟨-, hprev, -⟩
    apply hp
    intro i
    rcases lt_trichotomy i j with h | rfl | h
    · exact hprev rfl i h
    · exact mem_singleton.mp hj
    · exact hf i h
  · rintro ⟨⟨hf, -, hj⟩, hn⟩
    refine ⟨⟨hf, fun e => absurd e (by decide), hj⟩, ?_⟩
    intro hall
    exact hn ⟨hf, fun _ i _ => hall i, hj⟩

lemma rim_end (j : Fin 3) : rim (hs := hs) (j.val + 1) = Inv.Yt0 j := by
  ext x
  rw [rim, mem_sdiff, region_end, mem_singleton, pole_iff, Inv.Top, Inv.Yt0, Inv.L, Inv.L, mem_lam,
    mem_lam]
  simp only [mem_univ, mem_sdiff, mem_singleton, true_and]
  constructor
  · rintro ⟨⟨hf, -⟩, hp⟩
    refine ⟨hf, ?_⟩
    by_contra hc
    push Not at hc
    apply hp
    intro i
    rcases lt_trichotomy i j with h | rfl | h
    · exact hc.1 i h
    · exact hc.2
    · exact hf i h
  · rintro ⟨hf, hn⟩
    refine ⟨⟨hf, Or.inr trivial⟩, ?_⟩
    intro hall
    rcases hn with h | h
    · exact h (fun i _ => hall i)
    · exact h (hall j)

lemma border_begin (j : Fin 3) (o : Inv t0 j) :
    border Ds t0 P j.val ∘ position Ds t0 P j o = Inv.p0 j (Ds j) := by
  funext z
  rcases z with ((T|T)|(c|σ|r|r))
  · exact region_begin j
  · exact rim_begin j
  all_goals
    change (if j.val < j.val then univ else ∅) = _
    simp [Inv.p0, Inv.stamp]

lemma border_end (j : Fin 3) (o : Inv t0 j) :
    border Ds t0 P (j.val + 1) ∘ position Ds t0 P j o = Inv.pend j (Ds j) := by
  funext z
  rcases z with ((T|T)|(c|σ|r|r))
  · exact region_end j
  · exact rim_end j
  all_goals
    change (if j.val < j.val + 1 then univ else ∅) = _
    simp [Inv.pend, Inv.stamp]

/-! ### The stages -/

/-- Point map of a stage: `Y_d += X_d` (forward) or `X_d −= Y_d` (reverse). -/
def stageOp (rev : Bool) (x : Role Ds t0 P → ℂ) : Role Ds t0 P → ℂ
  | .inl (.inl d) => if rev then x (gx Ds t0 P d) - x (gy Ds t0 P d) else x (gx Ds t0 P d)
  | .inl (.inr d) => if rev then x (gy Ds t0 P d) else x (gy Ds t0 P d) + x (gx Ds t0 P d)
  | .inr a => x (.inr a)

lemma covered_x (j : Fin 3) (d : Key hs) :
    gx Ds t0 P d ∈ covered (position Ds t0 P j (omitJ t0 j d)) := by
  rw [cover_iff]; exact ⟨.inl (.inl (d j)), congrArg (gx Ds t0 P) (locate_omit t0 j d)⟩

lemma covered_y (j : Fin 3) (d : Key hs) :
    gy Ds t0 P d ∈ covered (position Ds t0 P j (omitJ t0 j d)) := by
  rw [cover_iff]; exact ⟨.inl (.inr (d j)), congrArg (gy Ds t0 P) (locate_omit t0 j d)⟩

/-- One stage: all invocations of stage `j` in parallel. -/
theorem stage (rev : Bool) (j : Fin 3) (hh : 9 ≤ hs j) :
    MPath (bases Ds t0 P) (border Ds t0 P j.val) (border Ds t0 P (j.val + 1)) (stageOp Ds t0 P rev)
      (∑ _o : Inv t0 j, Inv.Einv j (Ds j)) := by
  let h := fun _ : Inv t0 j => if rev then Inv.backward j (Ds j) else Inv.forward j (Ds j)
  apply MPath.parallel (position Ds t0 P j) (pos_dis Ds t0 P j) (bases Ds t0 P) (h := h)
  · intro o
    rw [bases_local, border_begin, border_end]
    cases rev
    · exact (Inv.invocation j (Ds j) (axes t0 j o) hh).1
    · exact (Inv.invocation j (Ds j) (axes t0 j o) hh).2
  · intro o x
    funext r
    rcases r with ((r|r)|a) <;> cases rev <;> rfl
  · rintro x ((k|k)|r) hr
    · exact absurd (covered_x Ds t0 P j k) (hr _)
    · exact absurd (covered_y Ds t0 P j k) (hr _)
    · rfl
  · rintro ((k|k)|(⟨i, o, a⟩|r)) hr
    · exact absurd (covered_x Ds t0 P j k) (hr _)
    · exact absurd (covered_y Ds t0 P j k) (hr _)
    · by_cases ig : i = j
      · subst ig
        exact absurd (by rw [cover_iff]; exact ⟨.inr a, rfl⟩) (hr o)
      · change (if i.val < j.val then univ else ∅) = (if i.val < j.val + 1 then univ else ∅)
        have hne : i.val ≠ j.val := fun e => ig (Fin.ext e)
        simp only [show (i.val < j.val + 1) ↔ (i.val < j.val) from (by omega)]
    · rfl

end Net
end PowerSaving.Colour
end OAI
