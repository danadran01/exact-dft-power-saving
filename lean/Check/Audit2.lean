import OAI.Computability.FourierTransform.Goal

/-! Non-vacuity of the cost model: any `DFTProgram` must have `W n ≥ n` for `n ≥ 2`.
Invariant: every array occurring in a value produced by a run either has length at most
(input bound + work charged so far), or is literally the input array `X`. -/

namespace OAI.PowerSaving.RAM
open Ty

variable (X : Tape ℂ)

def isX : (b : Ty) → Tape b.T → Prop
  | .c _, v => v = X
  | _, _ => False

def Fresh (B : ℕ) : (t : Ty) → t.T → Prop
  | .w, _ => True
  | .c _, _ => True
  | .p s b, v => Fresh B s v.1 ∧ Fresh B b v.2
  | .a b, v => (v.len ≤ B ∨ isX X b v) ∧ ∀ i, Fresh B b (v.pos i)

variable {X}

theorem Fresh.mono {B B' : ℕ} (h : B ≤ B') : ∀ (t : Ty) (v : t.T), Fresh X B t v → Fresh X B' t v
  | .w, _, _ => trivial
  | .c _, _, _ => trivial
  | .p s b, v, ⟨h1, h2⟩ => ⟨Fresh.mono h s _ h1, Fresh.mono h b _ h2⟩
  | .a b, _, ⟨h1, h2⟩ => ⟨h1.imp (fun h' => le_trans h' h) id, fun i => Fresh.mono h b _ (h2 i)⟩

theorem Fresh.blank {B : ℕ} : ∀ t : Ty, Fresh X B t t.blank
  | .w => trivial
  | .c _ => trivial
  | .p s b => ⟨Fresh.blank s, Fresh.blank b⟩
  | .a _ => ⟨Or.inl (Nat.zero_le _), fun i => absurd i.2 (Nat.not_lt_zero _)⟩

theorem steps_inv {α : Type} (Q : ℕ → α → Prop) (init : α) (f : ℕ → α → Bill α) (B0 : ℕ)
    (hQ : ∀ B B' v, B ≤ B' → Q B v → Q B' v)
    (hf : ∀ i B' z, B0 ≤ B' → Q B' z → Q (B' + (f i z).work) (f i z).val) :
    ∀ l B', B0 ≤ B' → Q B' init →
      Q (B' + (Bill.steps init f l).work) (Bill.steps init f l).val
  | 0, B', _, hi => by
      simp only [Bill.steps, Bill.one]; exact hQ _ _ _ (by omega) hi
  | l+1, B', hB, hi => by
      have ih := steps_inv Q init f B0 hQ hf l B' hB hi
      have := hf l _ _ (by omega) ih
      simp only [Bill.steps, Bill.pay, Bill.pass]
      exact hQ _ _ _ (by omega) this

theorem sow_fresh (t : Ty) (len count : ℕ) (z : t.T) (f : ℕ → Bill (ℕ × t.T)) (B0 : ℕ)
    (hz : Fresh X B0 t z) (hf : ∀ i, Fresh X (B0 + (f i).work) t (f i).val.2) :
    Fresh X (B0 + (Bill.sow len count z f).work) (.a t) (Bill.sow len count z f).val := by
  let Q : ℕ → Tape t.T → Prop := fun B v => v.len = len ∧ ∀ k, Fresh X B t (v.pos k)
  have hQ : ∀ B B' v, B ≤ B' → Q B v → Q B' v :=
    fun B B' v h ⟨h1, h2⟩ => ⟨h1, fun k => Fresh.mono h t _ (h2 k)⟩
  have H := steps_inv Q (Tape.tab len (fun _ => z))
    (fun i v => (f i).pass (fun s => Bill.one (v.set s.1 s.2))) B0 hQ
    (by
      intro i B' v hB ⟨h1, h2⟩
      refine ⟨h1, fun k => ?_⟩
      simp only [Bill.pass, Bill.one, Tape.set]
      split
      · exact Fresh.mono (by omega) t _ (hf i)
      · exact Fresh.mono (by omega) t _ (h2 k))
    count B0 le_rfl ⟨rfl, fun _ => hz⟩
  obtain ⟨h1, h2⟩ := H
  simp only [Bill.sow, Bill.pay]
  refine ⟨Or.inl ?_, fun k => Fresh.mono (by omega) t _ (h2 k)⟩
  rw [h1]; omega

theorem Atom.fresh {allow a b} (op : Atom allow a b) (B : ℕ) (x : a.T) (hx : Fresh X B a x) :
    Fresh X (B + (op.run x).work) b (op.run x).val := by
  cases op <;> try trivial
  case id => exact Fresh.mono (by omega) _ _ hx
  case fst => exact Fresh.mono (by omega) _ _ hx.1
  case snd => exact Fresh.mono (by omega) _ _ hx.2
  case look =>
    obtain ⟨v, i⟩ := x
    simp only [Atom.run, Bill.one, Tape.look]
    split
    · exact Fresh.mono (by omega) _ _ (hx.1.2 _)
    · exact Fresh.blank _

def HGood (X : Tape ℂ) : (r : Port) → Handler r → Prop
  | none, _ => True
  | some (s,t), h => ∀ B x, Fresh X B s x → Fresh X (B + (h x).work) t (h x).val

theorem depthRun_fresh {s t : Ty} (base : s.T → Bill t.T)
    (step : (s.T → Bill t.T) → (s.T → Bill t.T))
    (hb : ∀ B x, Fresh X B s x → Fresh X (B + (base x).work) t (base x).val)
    (hs : ∀ h : s.T → Bill t.T, HGood X (some (s,t)) h → HGood X (some (s,t)) (step h)) :
    ∀ k, HGood X (some (s,t)) (depthRun base step k)
  | 0 => by
      intro B x hx
      simp only [depthRun, Bill.pay]
      exact Fresh.mono (by omega) _ _ (hb B x hx)
  | k+1 => by
      intro B x hx
      simp only [depthRun, Bill.pay]
      exact Fresh.mono (by omega) _ _ (hs _ (depthRun_fresh base step hb hs k) B x hx)

theorem Code.fresh {allow r s t} (f : Code allow r s t) :
    ∀ (h : Handler r), HGood X r h → ∀ B x, Fresh X B s x →
      Fresh X (B + (f.run h x).work) t (f.run h x).val := by
  induction f with
  | atom op => intro h _ B x hx; exact Atom.fresh op B x hx
  | comp f g ihf ihg =>
      intro h hh B x hx
      simp only [Code.run, Bill.pass, Bill.pay]
      exact Fresh.mono (by omega) _ _ (ihg h hh _ _ (ihf h hh B x hx))
  | fork f g ihf ihg =>
      intro h hh B x hx
      simp only [Code.run, Bill.pass, Bill.one]
      exact ⟨Fresh.mono (by omega) _ _ (ihf h hh B x hx),
        Fresh.mono (by omega) _ _ (ihg h hh B x hx)⟩
  | ifz q f g _ ihf ihg =>
      intro h hh B x hx
      simp only [Code.run, Bill.pass, Bill.pay]
      split
      · exact Fresh.mono (by omega) _ _ (ihf h hh B x hx)
      · exact Fresh.mono (by omega) _ _ (ihg h hh B x hx)
  | @loop r s t n init body _ ihi ihb =>
      intro h hh B x hx
      simp only [Code.run, Bill.pass, Bill.pay]
      have H := steps_inv (fun B v => Fresh X B t v) (init.run h x).val
        (fun i z => body.run h (x,(i,z))) B (fun _ _ v hle hv => Fresh.mono hle t v hv)
        (fun i B' z hB hz => ihb h hh B' (x,(i,z)) ⟨Fresh.mono hB s x hx, trivial, hz⟩)
        (n.run h x).val (B + (init.run h x).work) (by omega) (ihi h hh B x hx)
      exact Fresh.mono (by omega) _ _ H
  | @tab r s t n body _ ihb =>
      intro h hh B x hx
      have H := sow_fresh t (n.run h x).val (n.run h x).val t.blank
        (fun i => (body.run h (x,i)).pass (fun y => Bill.one (i,y))) B (Fresh.blank t)
        (fun i => by
          simp only [Bill.pass, Bill.one]
          exact Fresh.mono (by omega) _ _ (ihb h hh B (x,i) ⟨hx, trivial⟩))
      simp only [Code.run, Bill.pass, Bill.pay, Bill.tab] at H ⊢
      exact Fresh.mono (by omega) _ _ H
  | @sow r s t n count body _ _ ihb =>
      intro h hh B x hx
      simp only [Code.run, Bill.pass, Bill.pay]
      have H := sow_fresh t (n.run h x).val (count.run h x).val t.blank
        (fun i => body.run h (x,i)) B (Fresh.blank t)
        (fun i => (ihb h hh B (x,i) ⟨hx, trivial⟩).2)
      exact Fresh.mono (by omega) _ _ H
  | importClosed f ihf =>
      intro h _ B x hx
      simp only [Code.run, Bill.pay]
      exact Fresh.mono (by omega) _ _ (ihf () trivial B x hx)
  | call =>
      intro h hh B x hx
      simp only [Code.run, Bill.pay]
      exact Fresh.mono (by omega) _ _ (hh B x hx)
  | @descend r s t base body ihb ihs =>
      intro h _ B x hx
      obtain ⟨k, y⟩ := x
      simp only [Code.run, Bill.pay]
      have H := depthRun_fresh (base.run ()) (body.run) (fun B x hx => ihb () trivial B x hx)
        (fun h' hh' => fun B x hx => ihs h' hh' B x hx) k B y hx.2
      exact Fresh.mono (by omega) _ _ H

end OAI.PowerSaving.RAM

namespace OAI.PowerSaving
open RAM

lemma dft_single0 (n : ℕ) (hn : 0 < n) (j : Fin n) :
    dft n (Pi.single (⟨0, hn⟩ : Fin n) 1) j = 1 := by
  simp [dft, Pi.single_apply]

/-- Non-vacuity: every admissible `W` satisfies `n ≤ W n` for `n ≥ 2`. -/
theorem DFTProgram.work_ge {o : Prog false .w .w} {s : Prog false dftInKind dftOutKind}
    {W : ℕ → ℕ} (hP : DFTProgram o s W) (n : ℕ) (hn : 2 ≤ n) : n ≤ W n := by
  obtain ⟨c, hc⟩ := hP
  have h0 : 0 < n := by omega
  let x : Vec n := Pi.single (⟨0, h0⟩ : Fin n) 1
  obtain ⟨_, _, _, _, _, _, hx⟩ := hc n h0
  obtain ⟨_, _, hw, he⟩ := hx x
  set D := (run o n).val
  set res := run s (n, root D, (⟨n, x⟩ : Tape ℂ))
  have hin : Fresh (⟨n, x⟩ : Tape ℂ) 0 dftInKind (n, root D, (⟨n, x⟩ : Tape ℂ)) :=
    ⟨trivial, trivial, Or.inr rfl, fun _ => trivial⟩
  have H := (Code.fresh (X := (⟨n, x⟩ : Tape ℂ)) s () trivial 0 _ hin).1
  change res.val.len ≤ 0 + res.work ∨ res.val = (⟨n, x⟩ : Tape ℂ) at H
  rw [he] at H
  rcases H with H | H
  · simp at H; omega
  · exfalso
    have h1 := congrArg (fun v : Tape ℂ => v.look 1 0) H
    simp only [Tape.look, show 1 < n by omega, dite_true] at h1
    rw [dft_single0 n h0] at h1
    simp [x, Pi.single_apply] at h1

#print axioms DFTProgram.work_ge

end OAI.PowerSaving
