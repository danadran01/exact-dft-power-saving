import OAI.Computability.FourierTransform.Grouped.BatchRun
import OAI.Computability.FourierTransform.Grouped.GWords
import OAI.Computability.FourierTransform.TensorRecursion

/-!
# Grouped sweep (new; not part of OpenAI's development)

Analogs of OpenAI's `ferry`/`coastline` (`RoleArrays.lean`), `open_move`/`sweep`
(`RecursiveContract.lean`) and `amplifies`/`amplify` (`TensorRecursion.lean`) for grouped words.
A batch move `GMove.batch l A S τ` is `bdir A S` (`open_batch`: calls of order `|S|*f`) followed by
the translation `τ` (`shift_cost`). The charge of a word is the sum over its batches of
`nb c * τ c` where `c` is the batch size.
-/

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

def gferry (r f : ℕ) (u : GMove α ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => u.go f (fun i j => v (i,x.2.1,j)) x.1 x.2.2

/-- Total grouped certificate action. -/
def gcoast (r f : ℕ) (p : GWord α ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => gwalk f p (fun i j => v (i,x.2.1,j)) x.1 x.2.2

theorem gcoast_cons (r f : ℕ) (u : GMove α ρ) (p : GWord α ρ) (v : Grain α ρ r f) :
    gcoast r f (u::p) v = gcoast r f p (gferry r f u v) := rfl

lemma gferry_local (r f : ℕ) (M : Matrix ρ ρ ℚ) (v : Grain α ρ r f) :
    gferry r f (.localM M) v = ferry r f (.localM M) v := rfl

lemma gferry_shift (r f : ℕ) (l : ρ) (z : Space α) (v : Grain α ρ r f) :
    gferry r f (.shift l z) v = ferry r f (.shift l z) v := rfl

lemma gferry_batch (r f : ℕ) (l : ρ) (A : OBase α) (S : Finset α) (τ : Space α)
    (v : Grain α ρ r f) :
    gferry r f (.batch l A S τ) v = ferry r f (.shift l τ) (bferry r f l A S v) := by
  funext x
  simp only [gferry, ferry, bferry, GMove.go, Move.go]
  rw [← roleAct_mul]

end

section
universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {f : ι → ℕ} {nb τ : ℕ → ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
    {b : Bank (hatch cl) ι}

namespace Rig
variable (h : Rig m b.B f s x cl X R r v)
include h

lemma open_gmove (hk : ∀ c, 1 ≤ c → c < X.n → Contract cl b (fun i => c*f i) (τ c) R)
    (hg : ∀ c, 1 ≤ c → c < X.n → ∀ i, nb c i*(sim R (c*f i)).n=(book X r (f i)).n)
    (z : GMove α ρ) (hz : ∀ c ∈ z.size, 1 ≤ c ∧ c < X.n) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (gferry r (f i) z (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => (z.size.map fun c => nb c i * τ c i).sum) := by
  cases z with
  | localM M =>
    simpa [GMove.size, gferry_local] using
      (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.point_cost M))
  | shift l z =>
    simpa [GMove.size, gferry_shift] using
      (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.shift_cost l z))
  | batch l A S τ' =>
    obtain ⟨h1,h2⟩ := hz S.card (by simp [GMove.size])
    have H1 := h.open_batch l A S (hk _ h1 h2) (hg _ h1 h2)
    let v' i := bferry r (f i) l A S (v i)
    let env i : T (Ty.p s (bundle cl)) := (x i,(fleet X R r (f i)).tape (v' i))
    have hk' := h.gather id env (t:=Ty.p s (bundle cl)) Can.first
    have hl : Rig m b.B f (Ty.p s (bundle cl)) env cl X R r v' :=
      ⟨hk'.gear,hk'.imag,Can.second⟩
    have H2 := Able.of_can (b:=b) (hl.shift_cost l τ')
    have H := H1.save_keep H2
    simpa [GMove.size, gferry_batch] using H

lemma gsweep (hk : ∀ c, 1 ≤ c → c < X.n → Contract cl b (fun i => c*f i) (τ c) R)
    (hg : ∀ c, 1 ≤ c → c < X.n → ∀ i, nb c i*(sim R (c*f i)).n=(book X r (f i)).n)
    (P : GWord α ρ) (hP : ∀ c ∈ sizes P, 1 ≤ c ∧ c < X.n) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (gcoast r (f i) P (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => ((sizes P).map fun c => nb c i * τ c i).sum) := by
  induction P generalizing s v with
  | nil =>
    have ht := h.items.mono (W':=fun i => (fleet X R r (f i)).n) (fun _ => Nat.zero_le _)
    have hz := Able.of_can (b:=b) ht
    simp only [sizes_nil, List.map_nil, List.sum_nil]
    exact hz
  | cons g pth ih =>
    have hs : sizes (g :: pth) = g.size ++ sizes pth := by simp [sizes]
    rw [hs] at hP
    let v' i := gferry r (f i) g (v i)
    let env i : T (Ty.p s (bundle cl)) := (x i,(fleet X R r (f i)).tape (v' i))
    have hk' := h.gather id env (t:=Ty.p s (bundle cl)) Can.first
    have hl : Rig m b.B f (Ty.p s (bundle cl)) env cl X R r v' :=
      ⟨hk'.gear,hk'.imag,Can.second⟩
    have hh := ih hl (fun c hc => hP c (List.mem_append_right _ hc))
    have H := (h.open_gmove hk hg g (fun c hc => hP c (List.mem_append_left _ hc))).save_keep hh
    simpa only [gcoast_cons, hs, List.map_append, List.sum_append] using H

end Rig
end

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

lemma gamplifies (X : Layout α) (r f k : ℕ) (h : X.n*f+r=k) (p : GWord α ρ)
    (hp : ∀ v, gwalk f p v = multiAct f (fun _ => kernel α) v)
    (v : Sim ρ k → ℂ) :
    let e := ebb X r f k h v
    let z : Grain α ρ r f := fun i => chords r f (fun j => e (i.1,j)) i.2
    gcoast r f p z = ebb X r f k h (whole k v) := by
  intro e z
  funext i
  unfold gcoast
  rw [hp]
  exact (ripple_grid X r f h (fun j => v (i.1,j)) i.2).symm

universe U
variable {ι : Type U} {m : Bool}
    {k f : ι → ℕ} {nb τ : ℕ → ι → ℕ} {cl : Paint} {b : Bank (hatch cl) ι}
    {v : ∀ i, Sim ρ (k i)→ℂ}

/-- Body proof with fixed `r` for grouped words (analog of OpenAI's `amplify`). -/
lemma gamplify (m : Bool) (b : Bank (hatch cl) ι) (v : ∀ i, Sim ρ (k i) → ℂ)
    (X : Layout α) (R : Layout ρ) (r : ℕ)
    (hr : 3 ≤ X.n) (hq : ∀ i, X.n*f i+r=k i) (hd : r < X.n)
    (hc : ∀ c, 1 ≤ c → c < X.n → ∀ i, nb c i*(sim R (c*f i)).n=2^k i)
    (hk : ∀ c, 1 ≤ c → c < X.n → Contract cl b (fun i => c*f i) (τ c) R)
    (hB : Small b.B (fun i => 2^k i))
    (p : GWord α ρ) (hs : ∀ c ∈ sizes p, 1 ≤ c ∧ c < X.n)
    (hp : ∀ f v, gwalk f p v = multiAct f (fun _ => kernel α) v) :
    Able m b (simIn cl) (bundle cl) (fun i => loaded cl R (k i) (v i))
      (fun i => (sim R (k i)).tape (whole (k i) (v i)))
      (fun i => 2^k i) (fun i => ((sizes p).map fun c => nb c i * τ c i).sum) := by
  let W i := 2^k i
  let s := simIn cl
  let e (i : ι) := ebb X r (f i) (k i) (hq i) (v i)
  let z (i : ι) : Grain α ρ r (f i) :=
    fun j => chords r (f i) (fun l => e i (j.1,l)) j.2
  let sz i := (fleet X R r (f i)).n
  have hsz : Dom W sz := by
    refine ⟨R.n+1, fun i => ?_⟩
    unfold W sz fleet
    rw [Layout.pair_len, book_len,hq]
    simp only [mul_add,add_mul,mul_one,one_mul]
    gcongr <;> simp
  have hf (i) : f i ≤ k i := by
    have g := hq i
    have h := Nat.le_mul_of_pos_left (f i) (show 0 < X.n by omega)
    omega
  have hy (i) : k i ≤ W i := Nat.lt_two_pow_self.le
  have sd := hB.mono hy
  have sq := sd.mono hf
  let p2 i := 2^f i
  have hm : Small b.B p2 :=
    hB.mono (fun i => Nat.pow_le_pow_right (by omega) (hf i))
  have hcube (i) : p2 i ^ 3 ≤ W i := by
    unfold p2 W
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    have hh : 3*f i ≤ X.n*f i := Nat.mul_le_mul_right _ hr
    have hg := hq i
    rw [mul_comm]
    omega
  let env (i : ι) := loaded cl R (k i) (v i)
  have hmf : Can m b.B s Ty.w env f W := by
    have ht : Can m b.B s Ty.w env k W := Can.first
    refine (ht.dvdW (Can.wc X.n) sd).cong (fun _ => rfl) ?_
    intro i
    rw [← hq,mul_comm X.n]
    exact Layout.div_join hd
  have hmp : Can m b.B s (Ty.p Ty.w Ty.w) env (fun i => (f i,p2 i)) W :=
    hmf.pair (hmf.wTwo sq hm (Dom.of_le (fun i => (hf i).trans (hy i))))
  let T1 := Ty.p s (Ty.p Ty.w Ty.w)
  let Y (i : ι) : T T1 := (env i,f i,p2 i)
  have hmx : Can m b.B T1 (Ty.a Ty.w) Y (fun i => xorTab (f i)) W :=
    (Can.xor_prepare (m:=m) (f:=f) (B:=b.B) (s:=T1) (x:=Y)
      (Can.fst Can.second) (Can.snd Can.second) sq hm).mono hcube
  let T2 := Ty.p T1 (Ty.a Ty.w)
  let Y' (i : ι) : T T2 := (Y i,xorTab (f i))
  have hG : Rig m b.B f T2 Y' cl X R r e := by
    have H : Has m b.B T2 s Y' env := Can.fst Can.first
    refine ⟨⟨?_,?_,Can.second,hm⟩,?_,?_⟩
    · exact Can.snd (Can.snd Can.first)
    · exact Can.fst (Can.snd Can.first)
    · exact H.snd.fst
    · exact H.snd.snd.cong (fun _ => rfl) (fun i => (ebb_eq ..).symm)
  have HH : Can m b.B T2 (bundle cl) Y' (fun i => (fleet X R r (f i)).tape (z i)) W :=
    hG.dots_cost.weaken hsz
  let pre (i) := (fleet X R r (f i)).tape (z i)
  let T3 := Ty.p T2 (bundle cl)
  let A (i) : T T3 := (Y' i,pre i)
  have Hg := hG.gather id A (t:=T3) Can.first
  have G : Rig m b.B f T3 A cl X R r z := ⟨Hg.gear,Hg.imag,Can.second⟩
  have Hy := G.gsweep hk (nb:=nb)
    (fun c h1 h2 i => by rw [book_len,hq]; exact hc c h1 h2 i) p hs
  have heq (i) : gcoast r (f i) p (z i) = ebb X r (f i) (k i) (hq i) (whole (k i) (v i)) :=
    gamplifies X r (f i) (k i) (hq i) p (hp _) (v i)
  have ha (i) : (fleet X R r (f i)).tape (gcoast r (f i) p (z i)) =
      (sim R (k i)).tape (whole (k i) (v i)) := by
    rw [heq]; exact ebb_eq ..
  have Ho := (Hy.weaken hsz (fun _ => le_rfl)).cong (fun _ => rfl) ha
  have Hx := (Able.of_can (b:=b) hmp).save_keep
    ((Able.of_can (b:=b) hmx).save_keep ((Able.of_can (b:=b) HH).save_keep Ho))
  simpa only [Nat.zero_add] using Hx

end
end
end PowerSaving.RAM
end OAI
