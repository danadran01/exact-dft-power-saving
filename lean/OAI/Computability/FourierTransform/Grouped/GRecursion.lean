import OAI.Computability.FourierTransform.Grouped.GSweep
import OAI.Computability.FourierTransform.Grouped.GAllot

/-!
# Grouped recursion closed (new; not part of OpenAI's development)

Analog of OpenAI's `RecursionBounds.lean` (`Desc`, `funds`, `charging`, `rec_body`,
`recurse_run`) for grouped words: a batch of size `c` is `gbatches u a c k` recursive calls of
order `c*(k/u)`, giving the work recursion `gallot` of `GAllot.lean`.
-/

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section

lemma gpos {u a k : ℕ} (hu : 1 ≤ u) (hk : threshold u a ≤ k) : 0 < k/u := by
  have hh : a+1 ≤ k/u := (Nat.le_div_iff_mul_le (by omega)).2 (by
    simpa [threshold, mul_comm] using hk)
  omega

/-- A sum over a list of sizes `< u`, grouped by multiplicity. -/
lemma sum_count (L : List ℕ) (u : ℕ) (hL : ∀ c ∈ L, c < u) (g : ℕ → ℕ) :
    (L.map g).sum = ∑ c : Fin u, L.count (c:ℕ) * g c := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih (fun c hc => hL c (List.mem_cons_of_mem _ hc))]
    have ha : a < u := hL a List.mem_cons_self
    have h1 : ∑ c : Fin u, (a::L).count (c:ℕ) * g c =
        ∑ c : Fin u, L.count (c:ℕ) * g c + ∑ c : Fin u, (if (c:ℕ) = a then g c else 0) := by
      rw [← sum_add_distrib]; apply sum_congr rfl; intro c _
      simp only [List.count_cons, add_mul]
      by_cases hc : (c:ℕ) = a
      · simp [hc]
      · simp [hc, Ne.symm hc]
    have h2 : ∑ c : Fin u, (if (c:ℕ) = a then g c else 0) = g a := by
      rw [Finset.sum_eq_single (⟨a,ha⟩ : Fin u)]
      · simp
      · intro c _ hc
        have : (c:ℕ) ≠ a := fun h => hc (Fin.ext h)
        simp [this]
      · simp
    rw [h1, h2]; omega

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- Parameters included in the open-code guarantee: calls of every order `c*(k/u)`, `1 ≤ c < u`,
with work `tau c`. -/
structure GDesc (cl : Paint) (u a : ℕ) (R : Layout ρ) where
  k : ℕ
  v : Sim ρ k → ℂ
  use : Handler (hatch cl)
  tau : ℕ → ℕ
  peak : ℕ
  works : threshold u a ≤ k → ∀ c, 1 ≤ c → c < u →
    ∀ (v : Sim ρ (c*(k/u))→ℂ), (use (loaded cl R (c*(k/u)) v)).OK
      ((sim R (c*(k/u))).tape (whole (c*(k/u)) v)) (tau c) peak

def gfunds {ρ} (cl : Paint) (u a : ℕ) (R : Layout ρ) :
    Bank (hatch cl) (GDesc cl u a R) := ⟨fun i => 2^i.k, GDesc.peak, GDesc.use⟩

def gcharging {cl u a R} (E : List ℕ) (i : GDesc cl u a (R:Layout ρ)) :=
  if threshold u a ≤ i.k then (E.map fun c => gbatches u a c i.k * i.tau c).sum else 0

lemma grec_body (cl : Paint) (m : Bool) (X : Layout α) (R : Layout ρ) (u a : ℕ)
    (hX : X.n=u) (hu : 3≤u) (hR : R.n=2^a) (p : GWord α ρ)
    (hs : ∀ c ∈ sizes p, 1 ≤ c ∧ c < u)
    (hp : ∀ f v, gwalk f p v = multiAct f (fun _ => kernel α) v) :
    let B := gfunds cl u a R
    Able m B (simIn cl) (bundle cl) (fun i => loaded cl R i.k i.v)
      (fun i => (sim R i.k).tape (whole i.k i.v)) B.B (gcharging (sizes p)) := by
  intro B
  let Y := GDesc cl u a R
  let K := threshold u a
  let x (i : Y) := loaded cl R i.k i.v
  have hx : Can m B.B (simIn cl) w x (fun i => i.k) B.B := Can.first
  apply Able.branch (hx.wlt (Can.wc K)) (fun i => K ≤ i.k)
    (fun i => by split <;> omega)
  -- big k. split according to r
  · let G := {i : Y // K ≤ i.k}
    let g (i : G) := i.1.k%u
    have hd (i : G) : g i<u := Nat.mod_lt _ (by omega)
    have hw : Small (fun i : G => B.B i.1) g :=
      (Small.const _ u).mono (fun i => (hd i).le)
    apply Able.dispatch (n:=g) u ((hx.reindex (fun i : G => i.1)).wmod (Can.wc u) hw) hd
    intro r hr
    let L := {i : G // g i=r}
    let l (i : L) : Y := i.1.1
    let T0 := B.comap l
    let k (i : L) := (l i).k
    let f (i : L) := k i/u
    let nb (c : ℕ) (i : L) := gbatches u a c (k i)
    let τ (c : ℕ) (i : L) := (l i).tau c
    have HH (i : L) : threshold u a ≤ k i := i.1.2
    have HK : ∀ c, 1 ≤ c → c < X.n → Contract cl T0 (fun i => c*f i) (τ c) R :=
      fun c h1 h2 i => (l i).works (HH i) c h1 (by omega)
    have H := gamplify (k:=k) (f:=f) (nb:=nb) (τ:=τ) m T0 (fun i => (l i).v)
      X R r (by omega) (fun i => by
        have h := Nat.div_add_mod (k i) u
        have hj : k i%u=r := i.2
        rw [hX,← hj]; exact h
        ) (by omega)
      (fun c h1 h2 i => by
        change gbatches u a c (k i)*(R.n*2^(c*(k i/u)))=2^k i
        rw [hR]
        exact grounds_eq u a c _ (by omega) (HH i) (by omega)) HK (Small.self _) p
      (fun c hc => by rw [hX]; exact hs c hc) hp
    exact H.mono (fun _ => le_rfl) (fun i => by
      change _ ≤ gcharging (sizes p) (l i)
      have hi : threshold u a ≤ (l i).k := HH i
      rw [gcharging, ite_eq_left hi])
  · let L := {i : Y // ¬ K ≤ i.k}
    have hl (i : L) : i.1.k<K := Nat.lt_of_not_ge i.2
    apply Able.dispatch K (hx.reindex (fun i : L => i.1)) hl
    intro j hj
    let T0 := {i : L // i.1.k=j}
    let l (i : T0) := i.1.1
    let Q := B.comap l
    have H := almost_fixed m (fun i => Q.B i) (fun i => Q.B i) cl
      (fun i => (l i).k) j (fun i => i.2) R (fun i => (l i).v)
    exact (Able.of_can (b:=Q) H).mono (fun _ => le_rfl) (fun _ => Nat.zero_le _)

/-- **Grouped recursion closed.** `recurse_run` with grouped words: the work is `gallot`, where
`N c` is the number of batches of size `c` of the certificate word. -/
theorem grecurse_run (cl : Paint) (m : Bool) (X : Layout α) (R : Layout ρ) (u a : ℕ)
    (hX : X.n=u) (hu : 3≤u) (hR : R.n=2^a) (p : GWord α ρ)
    (hs : ∀ c ∈ sizes p, 1 ≤ c ∧ c < u)
    (hp : ∀ f v, gwalk f p v = multiAct f (fun _ => kernel α) v) {ι : Type*}
    (k : ι→ℕ) (v : ∀ i,Sim ρ (k i)→ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl) (fun i => loaded cl R (k i) (v i))
      (fun i => (sim R (k i)).tape (whole (k i) (v i)))
      (fun i => gallot u a (fun c => (sizes p).count c) (k i)) := by
  obtain ⟨body,C,d,hc⟩ := grec_body cl m X R u a hX hu hR p hs hp
  let E := sizes p
  let N := fun c => E.count c
  let maxwork (k : ℕ) := gallot u a N k
  let K0 := 3*C+3
  let base : Prog m (simIn cl) (bundle cl) := .comp (.atom .snd) (.atom .snd)
  let fn := depthRun (base.run ()) body.run
  let P k := (2^k+2)^(d+1)
  have hE : ∀ c ∈ E, c < u := fun c hc => (hs c hc).2
  have h (n : ℕ) (j : ℕ) (hj : j<n) (v : Sim ρ j → ℂ) :
      (fn n (loaded cl R j v)).OK ((sim R j).tape (whole j v)) (K0*maxwork j)
        (max (P j) n) := by
    induction n generalizing j with
    | zero => omega
    | succ n ih =>
      let peak := max (P j) (n+1)
      let tau (c : ℕ) := K0*maxwork (c*(j/u))
      have pp (h : threshold u a ≤ j) (c : ℕ) (h1 : 1 ≤ c) (h2 : c < u)
          (v : Sim ρ (c*(j/u))→ℂ) :
          (fn n (loaded cl R (c*(j/u)) v)).OK ((sim R (c*(j/u))).tape (whole (c*(j/u)) v))
            (tau c) peak := by
        have hi := gdown_lt ⟨h, gpos (by omega) h⟩ h2
        have he := ih (c*(j/u)) (by omega) v
        apply he.mono le_rfl
        have hh : 2^(c*(j/u)) ≤ 2^j := Nat.pow_le_pow_right (by omega) hi.le
        exact max_le_max (by unfold P; gcongr) (by omega)
      let i : GDesc cl u a R := ⟨j,v,fn n,tau,peak,pp⟩
      have ht := hc i
      have H := ht.pay (t:=1) (z:=n+1) (le_trans
        (le_max_right (P j) (n+1))
        (show peak ≤ (gfunds cl u a R).cap d i from le_max_right _ _))
      apply H.mono
      · change C*(2^j+1)+gcharging E i +1 ≤ K0*gallot u a N j
        have hh : 1 ≤ 2^j := Nat.one_le_pow j 2 (by omega)
        have hs : C*(2^j+1)+1 ≤ K0*2^j := calc
          C*(2^j+1)+1 ≤ C*(2^j+2^j)+2^j := by gcongr
          _ ≤ _ := by
            dsimp [K0]
            simp only [_root_.mul_add, _root_.add_mul]
            nlinarith
        unfold gcharging
        by_cases ha : threshold u a≤j
        · have hd : threshold u a ≤ i.k := ha
          rw [ite_eq_left hd, gallot_eq,
            ite_eq_left (And.intro ha (gpos (by omega) ha) : threshold u a ≤ j ∧ 0 < j/u)]
          change C*(2^j+1)+(E.map fun c => gbatches u a c j * (K0*gallot u a N (c*(j/u)))).sum
            +1 ≤ _
          have he : (E.map fun c => gbatches u a c j * (K0*gallot u a N (c*(j/u)))).sum
              = K0 * ∑ c : Fin u, N c * gbatches u a c j * gallot u a N (c*(j/u)) := by
            rw [sum_count E u hE, Finset.mul_sum]; apply sum_congr rfl; intro c _
            dsimp only [N]; ring
          rw [he, _root_.mul_add K0]; omega
        · have hd : ¬threshold u a ≤ i.k := ha
          rw [ite_eq_right hd, gallot_eq,
            ite_eq_right (fun hp : threshold u a ≤ j ∧ 0 < j/u => ha hp.1), Nat.add_zero]
          exact hs
      · change max _ peak ≤ peak
        apply max_le _ le_rfl
        exact (Small.pow_mono_degree (2^j) (show d≤d+1 by omega)).trans
          (le_max_left _ _)
  let W i := maxwork (k i)
  let B i := 2^k i
  let x i := loaded cl R (k i) (v i)
  let X1 i : Ty.T (Ty.p w (simIn cl)) := (k i+1,x i)
  have L : Can m B (Ty.p w (simIn cl)) (bundle cl)
      X1 (fun i => (sim R (k i)).tape (whole (k i) (v i))) W := by
    refine ⟨.descend base body,K0+1,d+1,fun i => ?_⟩
    have hh := h (k i+1) (k i) (by omega) (v i)
    have hg : k i+1 ≤ P (k i) :=
      calc
        _ ≤ 2^(k i) := Nat.lt_two_pow_self
        _ ≤ (2^k i + 2)^1 := by simp
        _ ≤ _ := Small.pow_mono_degree _ (by omega)
    have H := hh.pay (t:=1) (z:=k i+1) (le_max_right ..)
    apply H.mono
    · change K0*W i+1 ≤ _
      simp [_root_.add_mul, _root_.mul_add]
      omega
    · exact max_le (le_max_left ..) (hg.trans (le_max_left ..))
  have hsmall : Small B k :=
    (Small.self B).mono (fun i => Nat.lt_two_pow_self.le)
  have HE : Can m B (simIn cl) (Ty.p w (simIn cl)) x X1 W := by
    exact ((show Can m B (simIn cl) w x k W from Can.first).plus (Can.wc 1) hsmall
      (Small.const ..)).pair Can.id
  exact HE.then_do L

end
end PowerSaving.RAM
end OAI
