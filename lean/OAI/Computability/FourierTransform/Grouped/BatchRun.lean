import OAI.Computability.FourierTransform.Grouped.BatchAddress
import OAI.Computability.FourierTransform.RecursiveContract

/-!
# One batch = recursive calls of order `c*f` (new; not part of OpenAI's development)

Analogs of OpenAI's `fill`, `yieldTape`, `fill_result`, `fill_read`, `fill_ready`,
`direction_get` (file `RecursiveBatches.lean`) and `open_dir` (file `RecursiveContract.lean`)
for a whole batch `bdir A S` (`c = |S|` lines) instead of one directional factor.
The fibres `Grid (Out S) r f` are cut into groups of `R.n` and every group is one simultaneous
kernel call of order `c*f`.
-/

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α]

/-- The batch matrix `bdir A S` on role `l` (a batch move before its translation). -/
def bferry [DecidableEq ρ] (r f : ℕ) (l : ρ) (A : OBase α) (S : Finset α)
    (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => roleAct f l (bdir A S) (fun i j => v (i,x.2.1,j)) x.1 x.2.2

/-- Source data for one recursive call (one group of fibres). -/
def bfill (l : ρ) (A : OBase α) (S : Finset α) {r f t : ℕ} (X : Layout (Out S))
    (R : Layout ρ) (h : t*R.n=(book X r f).n)
    (v : Grain α ρ r f) (b : Fin t) : Sim ρ (S.card*f) → ℂ :=
  fun (k,i) => v (l,(bBook A S r f).symm ((cut r f t X R h) (b,k),i))

/-- Collection of returned answers. -/
def byield (l : ρ) (A : OBase α) (S : Finset α) {r f t} (X : Layout (Out S))
    (R : Layout ρ) (h : t*R.n=(book X r f).n) (v : Grain α ρ r f) : Tape (Tape ℂ) :=
  (Layout.std t).tape fun b =>
    (sim R (S.card*f)).tape (whole (S.card*f) (bfill l A S X R h v b))

lemma bfill_result [DecidableEq ρ] (l : ρ) (A : OBase α) (S : Finset α) {r f t}
    (X : Layout (Out S)) (R : Layout ρ) h (v : Grain α ρ r f) (a : Grid α r f) :
    let q := bBook A S r f a
    let w := (cut r f t X R h).symm q.1
    bferry r f l A S v (l,a) = whole (S.card*f) (bfill l A S X R h v w.1) (w.2,q.2) := by
  intro q w
  unfold bferry roleAct
  simp only [ite_true]
  have H := bbook_act A S r f (fun p => v (l,p)) a
  refine H.trans ?_
  unfold whole bfill
  simp only [q,w,Prod.mk.eta,Equiv.apply_symm_apply]

end

section
universe U
variable {ι : Type U}

namespace Gear
variable {m : Bool} {B f : ι → ℕ} {s : Ty} {x : ι → T s}
variable (g : Gear m B f s x)
include g

lemma cpow (c : ℕ) : Knows m B s x (fun i => 2^(c*f i)) :=
  (g.power.wpow_fixed c g.bound).cong (fun _ => rfl) (fun i => by rw [← pow_mul, mul_comm])

lemma csmall (c : ℕ) : Small B (fun i => 2^(c*f i)) :=
  (g.bound.pow c).mono (fun i => le_of_eq (by rw [← pow_mul, mul_comm]))

end Gear

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {m : Bool} {B f n : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}

namespace Rig
variable (h : Rig m B f s x cl X R r v)
include h

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma bsimSmall (c : ℕ) : Small B fun i => (sim R (c*f i)).n :=
  (Small.const B R.n).mul (h.gear.csmall c)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma bsimSize (c : ℕ) : Knows m B s x fun i => (sim R (c*f i)).n :=
  Can.times (Can.wc R.n) (h.gear.cpow c) (Small.const B R.n) (h.gear.csmall c)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma bbatchSmall (S : Finset α) (X' : Layout (Out S))
    (hg : ∀ i, n i*R.n = (book X' r (f i)).n) (hr : 0<R.n) : Small B n :=
  (h.gear.grid_small X' r).mono (fun i => by
    rw [← hg]
    exact Nat.le_mul_of_pos_right _ hr)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma bbatchSize (S : Finset α) (X' : Layout (Out S))
    (hg : ∀ i, n i*R.n = (book X' r (f i)).n) (hr : 0<R.n) : Knows m B s x n :=
  ((h.gear.grid_size X' r).dvdW (Can.wc R.n) (h.gear.grid_small X' r)).cong
    (fun _ => rfl) (fun i => by rw [← hg]; exact Nat.mul_div_cancel _ hr)

variable (l : ρ) (A : OBase α) (S : Finset α) (X' : Layout (Out S))
variable (hg : ∀ i, n i*R.n = (book X' r (f i)).n)
include hg

omit [Fintype ρ] [DecidableEq ρ] in
lemma bfill_read (a : ∀ i, Sim ρ (S.card*f i)) (b : ∀ i, Fin (n i))
    (hd : Knows m B s x fun i => (sim R (S.card*f i)).loc (a i))
    (ha : Knows m B s x fun i => (b i).val) :
    Has m B s (c cl) x fun i => bfill l A S X' R (hg i) (v i) (b i) (a i) := by
  let L i := bits (S.card*f i)
  have hu := Can.addr_high (u:=a) (L:=fun _ => R) (R:=L) hd (h.gear.cpow _) (h.bsimSmall _)
  have hw := Can.addr_low (u:=a) (L:=fun _ => R) (R:=L) hd (h.gear.cpow _) (h.bsimSmall _)
  have hr : 0<R.n := lt_of_le_of_lt (Nat.zero_le _) (R.bd l)
  let C i := cut r (f i) (n i) X' R (hg i)
  let K i : Grid (Out S) r (f i) × Bits (S.card*f i) :=
    (C i (b i,(a i).1),(a i).2)
  have hs := Can.addr_join (L:=fun i => Layout.std (n i)) (R:=fun _ => R)
    (u:=fun i => (b i,(a i).1)) ha hu (Can.wc R.n)
    (h.bbatchSmall S X' hg hr) (Small.const B R.n)
  have hm : Knows m B s x fun i => (book X' r (f i)).loc (K i).1 :=
    hs.cong (fun _ => rfl) (fun i => (cut_eq r (f i) (n i) X' R _ _).symm)
  have hk := h.gear.to_basis X r A S X' K hm hw
  exact h.read (fun i => (l,(bBook A S r (f i)).symm (K i))) (Can.wc (R.loc l)) hk

omit [Fintype ρ] [DecidableEq ρ] in
lemma bfill_ready (b : ∀ i, Fin (n i))
    (ha : Knows m B s x fun i => (b i).val) :
    Can m B s (simIn cl) x
      (fun i => loaded cl R (S.card*f i) (bfill l A S X' R (hg i) (v i) (b i)))
      (fun i => (sim R (S.card*f i)).n) := by
  let W i := (sim R (S.card*f i)).n
  let V (i : ι) := bfill l A S X' R (hg i) (v i) (b i)
  have hd : Can m B s (bundle cl) x (fun i => (sim R (S.card*f i)).tape (V i)) W := by
    let Q := Σ i, Sim ρ (S.card*f i)
    let env (d : Q) : T (p s w) := (x d.1,(sim R (S.card*f d.1)).loc d.2)
    have G := h.gather (fun d : Q => d.1) env (t:=p s w) Can.first
    have hh := G.bfill_read l A S X' (n:=fun d=>n d.1) (fun d => hg d.1)
      (fun d => d.2) (fun d => b d.1) Can.second
      (Can.first.then_do (ha.reindex (Sigma.fst (β:=fun i => Sim ρ (S.card*f i)))))
    have ht := Can.layout (t:=c cl) (P:=fun _ => 0)
      (L:=fun i => sim R (S.card*f i)) (v:=V) (h.bsimSize _) hh (h.bsimSmall _)
    simpa [W] using ht
  have hf : Small B f := h.gear.bound.mono (fun i => Nat.lt_two_pow_self.le)
  have hc : Knows m B s x fun i => S.card*f i :=
    (Can.wc S.card).times h.gear.given (Small.const B _) hf
  exact (hc.mono (fun i => Nat.zero_le (W i))).pair
    ((h.imag.mono (fun i => Nat.zero_le (W i))).pair hd)

/-- Compute a batch outcome from the packed answers (and from unchanged roles). -/
lemma batch_get
    (H : Has m B s (Ty.a (bundle cl)) x fun i => byield l A S X' R (hg i) (v i))
    (a : ∀ i, Beach α ρ r (f i)) (ha : Knows m B s x fun i => (fleet X R r (f i)).loc (a i)) :
    Has m B s (c cl) x fun i => bferry r (f i) l A S (v i) (a i) := by
  obtain ⟨hx,hy⟩ := h.addrs a ha
  let C i := cut r (f i) (n i) X' R (hg i)
  let K i := bBook A S r (f i) (a i).2
  let Q i := (C i).symm (K i).1
  let Y i := ((Layout.std (n i)).pair R).loc (Q i)
  obtain ⟨hd,he⟩ := h.gear.from_basis X r A S X' (fun i => (a i).2) hy
  have hY : Knows m B s x Y :=
    hd.cong (fun _ => rfl) (fun i => uncut_eq r (f i) (n i) X' R _ (K i).1)
  have ls : Small B fun i => n i * R.n :=
    (h.gear.grid_small X' r).mono (fun i => le_of_eq (hg i))
  have hA := Can.addr_high (L:=fun i => Layout.std (n i)) (R:=fun _ => R)
    (u:=Q) hY (Can.wc R.n) ls
  have hB := Can.addr_low (L:=fun i => Layout.std (n i)) (R:=fun _ => R)
    (u:=Q) hY (Can.wc R.n) ls
  let F i b := bfill l A S X' R (hg i) (v i) b
  have hD := Can.fetch (t:=bundle cl) (L:=fun i => Layout.std (n i))
    (i:=fun i => (Q i).1)
    (v:=fun i b => (sim R (S.card*f i)).tape (whole (S.card*f i) (F i b))) H hA
  have hh := Can.fetch (t:=c cl) (L:=fun i => sim R (S.card*f i))
    (i:=fun i => ((Q i).2,(K i).2)) (v:=fun i => whole (S.card*f i) (F i (Q i).1))
    hD (Can.addr_join (L:=fun _ => R) (R:=fun i => bits (S.card*f i))
      (u:=fun i => ((Q i).2,(K i).2))
      hB he (h.gear.cpow _) (Small.const B R.n) (h.gear.csmall _))
  apply Can.cases_code (q:=fun i => (a i).1) R hx
  intro r'
  by_cases hL : r'=l
  · refine (hh.reindex (fun i : {i // (a i).1=r'} => i.val)).cong (fun _ => rfl)
      (fun i => ?_)
    have ht := bfill_result l A S (t:=n i.val)
      X' R (hg i.val) (v i.val) (a i.val).2
    have hC : (l,(a i.val).2) = (a i.val) := Prod.ext (i.property.trans hL).symm rfl
    exact ht.symm.trans (congr_arg _ hC)
  · refine ((h.read a hx hy).reindex (fun i : {i // (a i).1=r'} => i.val)).cong
      (fun _ => rfl) (fun i => ?_)
    have H : (a i.val).1≠l := fun hh => hL (i.property.symm.trans hh)
    simp only [bferry,roleAct, H,ite_false, Prod.mk.eta]

end Rig
end

section
universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {f n τ : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
    {b : Bank (hatch cl) ι}

omit [Fintype ρ] [DecidableEq ρ] in
lemma card_out (S : Finset α) : Fintype.card (Out S) + S.card = Fintype.card α := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have := S.card_le_univ; omega

namespace Rig
variable (h : Rig m b.B f s x cl X R r v)
include h

/-- One batch: `n` calls of order `S.card*f` (analog of OpenAI's `open_dir`). -/
lemma open_batch (l : ρ) (A : OBase α) (S : Finset α)
    (hk : Contract cl b (fun i => S.card*f i) τ R)
    (hg : ∀ i, n i*(sim R (S.card*f i)).n=(book X r (f i)).n) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (bferry r (f i) l A S (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => n i*τ i) := by
  let X' := Layout.someLayout (Out S)
  have he (i) : n i * R.n=(book X' r (f i)).n := by
    have hy : X'.n+S.card=X.n := by
      rw [← Layout.card X',← Layout.card X]; exact card_out S
    have hz := hg i
    change n i*(R.n*2^(S.card*f i)) = 2^r*(2^f i)^X.n at hz
    change n i * R.n = 2^r*(2^f i)^X'.n
    have h2 : (2^f i)^S.card = 2^(S.card*f i) := by rw [← pow_mul, mul_comm]
    rw [← hy, pow_add, h2, ← mul_assoc, ← mul_assoc] at hz
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hz
  let w i := (fleet X R r (f i)).n
  let y i := byield l A S X' R (he i) (v i)
  let sz i := (sim R (S.card*f i)).n
  let Tt := a (bundle cl)
  have hl : 0 < R.n := lt_of_le_of_lt (Nat.zero_le _) (R.bd l)
  have hy : Able m b s Tt x y w (fun i => n i*τ i) := by
    let arg (i) (k : Fin (n i)) := bfill l A S X' R (he i) (v i) k
    let g (i) (k : Fin (n i)) := (sim R (S.card*f i)).tape (whole (S.card*f i) (arg i k))
    let I (i : ι) := Fin (n i)
    let E0 (d : Σ i, I i) := (x d.1,(d.2:ℕ))
    have hs : Able m (b.comap (Sigma.fst (β:=I))) (p s Ty.w) (bundle cl)
        E0 (fun d => g d.1 d.2) (fun d => sz d.1) (fun d => τ d.1) := by
      have HH := h.gather (Sigma.fst (β:=I)) E0 (t:=p s Ty.w) Can.first
      have Hp := HH.bfill_ready l A S X' (n:=fun d=> n d.1) (fun d => he d.1)
        (fun d : Σ i,I i => d.2) Can.second
      have Hq : Able m (b.comap (Sigma.fst (β:=I))) (p s Ty.w) (simIn cl) E0
          (fun d => loaded cl R (S.card*f d.1) (arg d.1 d.2))
          (fun d => sz d.1) (fun _ => 0) := Able.of_can Hp
      have HG := Hq.comp (Able.use_call (ι:=Σ i,I i) (s:=simIn cl) (t:=bundle cl) (m:=m)
        (b:=b.comap (Sigma.fst (β:=I))) (Z:=fun d => τ d.1) (y:=fun d => g d.1 d.2)
        (fun d => hk d.1 (arg d.1 d.2)))
      simpa [Nat.zero_add] using HG
    have HT : Able m b s Ty.w x n (fun _=>0) (fun _=>0) :=
      Able.of_can (h.bbatchSize S X' he hl)
    have HH := Able.layout (L:=fun i => Layout.std (n i)) (v:=g) (t:=bundle cl)
      (P:=sz) (H:=τ) HT hs (h.bbatchSmall S X' he hl)
    refine HH.weaken ⟨2,fun i => ?_⟩ ?_
    · change 0+n i+n i*sz i+1 ≤ _
      have hj := hg i
      have hsz : sz i>0 := Nat.mul_pos hl (by change 0<2^(S.card*f i); positivity)
      have hy : n i*sz i ≤ w i :=
        calc
          _ = (book X r (f i)).n := hj
          _ ≤ R.n*(book X r (f i)).n := Nat.le_mul_of_pos_left _ hl
          _ = _ := rfl
      have gr : n i ≤ n i*sz i := Nat.le_mul_of_pos_right _ hsz
      omega
    · intro i; change 0+n i*τ i ≤ n i*τ i; omega
  let K := fun i => bferry r (f i) l A S (v i)
  have hh :
      Can m b.B (p s Tt) (bundle cl)
        (fun i => (x i,y i)) (fun i => (fleet X R r (f i)).tape (K i)) w := by
    let s' := p s Tt
    let env i : T s' := (x i,y i)
    have h' : Rig m b.B f s' env cl X R r v := h.gather id env Can.first
    refine h'.chart _ ?_
    let I (i : ι) := Beach α ρ r (f i)
    let u (d : Σ i, I i) : T (p s' Ty.w) := (env d.1,(fleet X R r (f d.1)).loc d.2)
    have HG := h'.gather (Sigma.fst (β:=I)) u (t:=p s' Ty.w) Can.first
    exact HG.batch_get l A S X' (n:=fun d => n d.1) (fun d => he d.1)
      (Can.snd Can.first) (fun d => d.2) Can.second
  exact hy.save_keep (Able.of_can hh)

end Rig
end
end
end PowerSaving.RAM
end OAI
