import OAI.Computability.FourierTransform.Grouped.GWords
import OAI.Computability.FourierTransform.FrameLifting

/-!
# Grouped path combinators (new; not part of OpenAI's development)

`MPath A s t g E` is `GPath` with the batch sizes recorded as a multiset `E` (so that parallel
composition can sum them). Combinators:

* `MPath.inc`     : grouped `Path.inc`; per role ONE batch adding `t r \ s r` (omitted if empty);
* `MPath.dec`     : per role ONE batch removing `s r \ t r`;
* `MPath.reframe` : grouped `Path.reframe`; per role one removal batch and one addition batch;
* `GPath.split_up`, `GPath.fill_split` : any batch may be split into two batches
  (needed for full-role steps `∅ → univ`, which are split as `1 + (u-1)`);
* `MPath.lift`, `MPath.parallel` : grouped versions of OpenAI's `Path.lift`, `Path.parallel`.

Histograms: `bm n` is the batch multiset of one batch of size `n` (empty if `n = 0`),
`toMS L` the multiset of an explicit list `L` of (size, multiplicity) pairs and `hist L c` its count.
-/

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section

/-! ### Histogram bookkeeping -/

/-- One batch of size `n`; an empty batch is omitted. -/
def bm (n : ℕ) : Multiset ℕ := if n = 0 then 0 else {n}

@[simp] lemma bm_zero : bm 0 = 0 := by simp [bm]

lemma bm_pos {n : ℕ} (h : n ≠ 0) : bm n = {n} := by simp [bm, h]

lemma count_bm (c n : ℕ) : Multiset.count c (bm n) = if n = c ∧ c ≠ 0 then 1 else 0 := by
  unfold bm
  by_cases hn : n = 0
  · subst hn; simp only [↓reduceIte, Multiset.count_zero]; split_ifs <;> omega
  · simp only [hn, ↓reduceIte, Multiset.count_singleton]
    by_cases hc : c = n
    · subst hc; simp [hn]
    · simp [hc, Ne.symm hc]

/-- The multiset of a (size, multiplicity) list. Zero sizes are omitted. -/
def toMS (L : List (ℕ × ℕ)) : Multiset ℕ := (L.map (fun e => e.2 • bm e.1)).sum

/-- Count of the size `c` in `toMS L`. -/
def hist (L : List (ℕ × ℕ)) (c : ℕ) : ℕ :=
  (L.map (fun e => if e.1 = c ∧ c ≠ 0 then e.2 else 0)).sum

@[simp] lemma toMS_nil : toMS [] = 0 := rfl
lemma toMS_cons (e : ℕ × ℕ) (L : List (ℕ × ℕ)) : toMS (e :: L) = e.2 • bm e.1 + toMS L := by
  simp [toMS]
lemma toMS_append (L M : List (ℕ × ℕ)) : toMS (L ++ M) = toMS L + toMS M := by
  simp [toMS]

lemma count_toMS (L : List (ℕ × ℕ)) (c : ℕ) : Multiset.count c (toMS L) = hist L c := by
  induction L with
  | nil => simp [hist]
  | cons e L ih =>
    rw [toMS_cons, Multiset.count_add, Multiset.count_nsmul, ih, count_bm]
    simp only [hist, List.map_cons, List.sum_cons]
    congr 1
    split_ifs <;> simp

/-- Scale all multiplicities. -/
def scale (n : ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) := L.map (fun e => (e.1, n * e.2))

lemma nsmul_toMS (n : ℕ) (L : List (ℕ × ℕ)) : n • toMS L = toMS (scale n L) := by
  induction L with
  | nil => simp [scale]
  | cons e L ih =>
    simp only [scale, List.map_cons] at ih ⊢
    rw [toMS_cons, toMS_cons, smul_add, ih, smul_smul]

lemma hist_append (L M : List (ℕ × ℕ)) (c : ℕ) : hist (L ++ M) c = hist L c + hist M c := by
  simp [hist]

/-- Sizes outside a support set have count zero. -/
lemma hist_eq_zero (L : List (ℕ × ℕ)) (S : List ℕ) (hS : ∀ e ∈ L, e.1 = 0 ∨ e.1 ∈ S)
    (c : ℕ) (hc : c ∉ S) : hist L c = 0 := by
  unfold hist
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  rcases hS e he with h | h
  · simp [h]; omega
  · have : ¬ (e.1 = c ∧ c ≠ 0) := by
      rintro ⟨rfl, _⟩
      exact hc h
    simp only [this, ↓reduceIte]

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-! ### Multiset-labelled grouped paths -/

/-- Grouped path whose batch sizes form the multiset `E`. -/
def MPath (A : ρ → OBase α) (s t : ρ → Finset α) (g : (ρ → ℂ) → (ρ → ℂ))
    (E : Multiset ℕ) : Prop :=
  ∃ p : GWord α ρ, ((sizes p : List ℕ) : Multiset ℕ) = E ∧
    ∀ (f : ℕ) (x : Data α ρ f), gwalk f p (withFrame A s f x) = withFrame A t f (point f g x)

/-- Batches added per role going from `s` to `t` (sizes of `t r \ s r`, empty ones omitted). -/
def riseM (s t : ρ → Finset α) : Multiset ℕ := ∑ r, bm (t r \ s r).card
/-- Batches removed per role going from `s` to `t` (sizes of `s r \ t r`, empty ones omitted). -/
def fallM (s t : ρ → Finset α) : Multiset ℕ := ∑ r, bm (s r \ t r).card

namespace MPath
variable {A : ρ → OBase α} {s t u : ρ → Finset α}

theorem of_gpath {g : (ρ → ℂ) → (ρ → ℂ)} {E : List ℕ} (h : GPath A s t g E) :
    MPath A s t g (E : Multiset ℕ) := by
  obtain ⟨p, hp, ap⟩ := h
  exact ⟨p, by rw [hp], ap⟩

theorem refl : MPath A s s id 0 := ⟨[], rfl, fun _ _ => rfl⟩

theorem trans {g h : (ρ → ℂ) → (ρ → ℂ)} {E F : Multiset ℕ}
    (a : MPath A s t g E) (b : MPath A t u h F) : MPath A s u (h ∘ g) (E + F) := by
  obtain ⟨p, hp, ap⟩ := a
  obtain ⟨q, hq, aq⟩ := b
  refine ⟨p ++ q, by rw [sizes_append, ← Multiset.coe_add, hp, hq], ?_⟩
  intro f x
  rw [gwalk_append, ap, aq]; rfl

theorem congrE {g : (ρ → ℂ) → (ρ → ℂ)} {E F : Multiset ℕ} (a : MPath A s t g E) (h : E = F) :
    MPath A s t g F := h ▸ a

theorem gate (g : Matrix ρ ρ ℚ)
    (cond : ∀ i j, g i j ≠ 0 → frame (A i) (s i) = frame (A j) (s j)) :
    MPath A s s (actPoint g) 0 := of_gpath (GPath.gate g cond)

omit [Fintype α] [DecidableEq α] [Fintype ρ] in
lemma update_self_of {L : ρ → Finset α} (i : ρ) (v : Finset α) (h : L i = v) :
    Function.update L i v = L := by
  rw [← h]; exact Function.update_eq_self i L

omit [Fintype α] [DecidableEq α] [Fintype ρ] in
lemma update_eq_of {s : ρ → Finset α} (T : Finset ρ) (t : ρ → Finset α) (i : ρ) (hi : i ∉ T) :
    (fun r => if r ∈ insert i T then t r else s r) =
      Function.update (fun r => if r ∈ T then t r else s r) i (t i) := by
  funext r
  by_cases hr : r = i
  · subst hr; simp
  · simp [hr]

/-- Grouped `Path.inc`: per role ONE batch adds the lines `t r \ s r`. -/
theorem inc (A : ρ → OBase α) {s t : ρ → Finset α} (h : ∀ r, s r ⊆ t r) :
    MPath A s t id (riseM s t) := by
  have key : ∀ T : Finset ρ, MPath A s (fun r => if r ∈ T then t r else s r) id
      (∑ r ∈ T, bm (t r \ s r).card) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using (refl (A := A) (s := s))
    | @insert i T hi ih =>
      rw [Finset.sum_insert hi, add_comm]
      have hui : (if i ∈ T then t i else s i) = s i := by simp [hi]
      have step : MPath A (fun r => if r ∈ T then t r else s r)
          (fun r => if r ∈ insert i T then t r else s r) id (bm (t i \ s i).card) := by
        rw [update_eq_of T t i hi]
        by_cases he : t i \ s i = ∅
        · have hts : t i = s i :=
            Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp he) (h i)
          rw [he, Finset.card_empty, bm_zero, hts, update_self_of i (s i) hui]
          exact refl
        · have hc : (t i \ s i).card ≠ 0 := by rwa [Ne, Finset.card_eq_zero]
          rw [bm_pos hc]
          have hg := GPath.role_up (A := A) (s := fun r => if r ∈ T then t r else s r) i
            (t i \ s i) (by rw [hui]; exact Finset.sdiff_disjoint)
          rw [hui, Finset.sdiff_union_of_subset (h i)] at hg
          exact of_gpath hg
      exact ih.trans step
  have hu : (fun r => if r ∈ (univ : Finset ρ) then t r else s r) = t := by
    funext r; simp
  have := key univ
  rwa [hu] at this

/-- Per role ONE batch removes the lines `s r \ t r`. -/
theorem dec (A : ρ → OBase α) {s t : ρ → Finset α} (h : ∀ r, t r ⊆ s r) :
    MPath A s t id (fallM s t) := by
  have key : ∀ T : Finset ρ, MPath A s (fun r => if r ∈ T then t r else s r) id
      (∑ r ∈ T, bm (s r \ t r).card) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using (refl (A := A) (s := s))
    | @insert i T hi ih =>
      rw [Finset.sum_insert hi, add_comm]
      have hui : (if i ∈ T then t i else s i) = s i := by simp [hi]
      have step : MPath A (fun r => if r ∈ T then t r else s r)
          (fun r => if r ∈ insert i T then t r else s r) id (bm (s i \ t i).card) := by
        rw [update_eq_of T t i hi]
        by_cases he : s i \ t i = ∅
        · have hts : t i = s i :=
            Finset.Subset.antisymm (h i) (Finset.sdiff_eq_empty_iff_subset.mp he)
          rw [he, Finset.card_empty, bm_zero, hts, update_self_of i (s i) hui]
          exact refl
        · have hc : (s i \ t i).card ≠ 0 := by rwa [Ne, Finset.card_eq_zero]
          rw [bm_pos hc]
          have hg := GPath.role_down (A := A) (s := fun r => if r ∈ T then t r else s r) i
            (s i \ t i) (by rw [hui]; exact Finset.sdiff_subset)
          rw [hui, Finset.sdiff_sdiff_eq_self (h i)] at hg
          exact of_gpath hg
      exact ih.trans step
  have hu : (fun r => if r ∈ (univ : Finset ρ) then t r else s r) = t := by
    funext r; simp
  have := key univ
  rwa [hu] at this

/-- Grouped `Path.reframe`: per role one batch removes `s r \ t r` and one batch adds
`t r \ s r` (empty batches omitted). -/
theorem reframe (A : ρ → OBase α) (s t : ρ → Finset α) :
    MPath A s t id (fallM s t + riseM s t) := by
  have h1 := dec A (s := s) (t := fun r => s r ∩ t r) (fun _ => Finset.inter_subset_left)
  have h2 := inc A (s := fun r => s r ∩ t r) (t := t) (fun _ => Finset.inter_subset_right)
  have e1 : fallM s (fun r => s r ∩ t r) = fallM s t := by
    unfold fallM; simp only [Finset.sdiff_inter_self_left]
  have e2 : riseM (fun r => s r ∩ t r) t = riseM s t := by
    unfold riseM; simp only [Finset.sdiff_inter_self_right]
  rw [e1] at h1; rw [e2] at h2
  exact h1.trans h2

/-- Grouped `Path.inc` through an intermediate frame (splits batches). -/
theorem inc_via (A : ρ → OBase α) {s m t : ρ → Finset α} (h₁ : ∀ r, s r ⊆ m r)
    (h₂ : ∀ r, m r ⊆ t r) : MPath A s t id (riseM s m + riseM m t) :=
  (inc A h₁).trans (inc A h₂)

end MPath

namespace GPath
variable {A : ρ → OBase α} {s : ρ → Finset α}

/-- Splitting lemma: an addition batch `R₁ ∪ R₂` may be done as two batches. -/
theorem split_up (r : ρ) (R₁ R₂ : Finset α) (h₁ : Disjoint R₁ (s r))
    (h₂ : Disjoint R₂ (R₁ ∪ s r)) :
    GPath A s (Function.update s r (R₂ ∪ (R₁ ∪ s r))) id [R₁.card, R₂.card] := by
  have a := role_up (A := A) (s := s) r R₁ h₁
  have b := role_up (A := A) (s := Function.update s r (R₁ ∪ s r)) r R₂
    (by rw [Function.update_self]; exact h₂)
  rw [Function.update_self, Function.update_idem] at b
  exact a.trans b

/-- A full-role step `∅ → univ` done as two batches of sizes `1` and `|α| - 1`. -/
theorem fill_split (r : ρ) (p : α) (hs : s r = ∅) :
    GPath A s (Function.update s r univ) id [1, Fintype.card α - 1] := by
  have h := split_up (A := A) (s := s) r {p} (univ \ {p}) (by rw [hs]; exact disjoint_empty_right _)
    (by rw [hs, union_empty]; exact sdiff_disjoint)
  have e1 : (univ \ {p}) ∪ ({p} ∪ s r) = univ := by
    rw [hs, union_empty]; exact sdiff_union_of_subset (subset_univ _)
  have e2 : (univ \ ({p} : Finset α)).card = Fintype.card α - 1 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_singleton]
  rw [e1, e2, card_singleton] at h
  exact h

end GPath

/-! ### Lifting along an embedding of roles and parallel composition -/

section Lift
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def GMove.over (e : ρ ↪ σ) : GMove α ρ → GMove α σ
  | .localM M => .localM (wide e M)
  | .batch r B R τ => .batch (e r) B R τ
  | .shift r z => .shift (e r) z

lemma sizes_over (e : ρ ↪ σ) (p : GWord α ρ) : sizes (p.map (GMove.over e)) = sizes p := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    cases m <;> simp_all [sizes, GMove.over, GMove.size]

theorem ggo_over (e : ρ ↪ σ) (m : GMove α ρ) (f : ℕ) (x : Data α σ f) :
    (m.over e |>.go f x) ∘ e = m.go f (x ∘ e) := by
  funext i
  cases m with
  | localM M =>
    funext j; exact wide_in e M i _
  | batch => simp [GMove.over, GMove.go, Function.comp, roleAct]
  | shift => simp [GMove.over, GMove.go, Function.comp, roleAct]

omit [DecidableEq ρ] in
theorem ggo_out (e : ρ ↪ σ) (m : GMove α ρ) (f : ℕ)
    (x : Data α σ f) {i : σ} (h : i ∉ covered e) :
    ((m.over e).go f x) i = x i := by
  have hh (j : ρ) : i ≠ e j := fun g => h ((cover_iff ..).2 ⟨j, g.symm⟩)
  cases m with
  | localM M => funext j; exact wide_out e M _ h
  | batch => simp [GMove.over, GMove.go, roleAct, hh]
  | shift => simp [GMove.over, GMove.go, roleAct, hh]

theorem gwalk_over (e : ρ ↪ σ) (p : GWord α ρ) (f : ℕ) (x : Data α σ f) :
    gwalk f (p.map (GMove.over e)) x ∘ e = gwalk f p (x ∘ e) := by
  induction p generalizing x with
  | nil => rfl
  | cons m p ih =>
    change gwalk _ _ _ ∘ e = gwalk f p (m.go f (x∘e))
    rw [← ggo_over]
    exact ih _

omit [DecidableEq ρ] in
theorem gwalk_out (e : ρ ↪ σ) (p : GWord α ρ) (f : ℕ) (x : Data α σ f)
    {i : σ} (h : i ∉ covered e) :
    gwalk f (p.map (GMove.over e)) x i = x i := by
  induction p generalizing x with
  | nil => rfl
  | cons m p ih =>
    exact (ih _).trans (ggo_out e m f _ h)

namespace MPath

/-- Grouped `Path.lift`. The batch sizes are unchanged. -/
theorem lift (e : ρ ↪ σ) (A : σ → OBase α) {s t : σ → Finset α}
    {g : (σ→ℂ) → (σ→ℂ)} {h : (ρ→ℂ) → (ρ→ℂ)} {E : Multiset ℕ}
    (q : MPath (A ∘ e) (s ∘ e) (t ∘ e) h E)
    (hin : ∀ x, (g x) ∘ e = h (x ∘ e)) (hout : ∀ x i, i∉covered e → g x i=x i)
    (he : ∀ i, i∉covered e → s i = t i) :
    MPath A s t g E := by
  obtain ⟨p,hp,ha⟩ := q
  refine ⟨p.map (GMove.over e), by rw [sizes_over, hp], ?_⟩
  intro f x
  have frame_cont (s : σ → Finset α) (x : Data α σ f) :
      withFrame A s f x ∘ e = withFrame (A∘e) (s∘e) f (x∘e) := rfl
  have point_cont :
      point f g x ∘ e = point f h (x ∘ e) := by
    funext i j
    exact congr_fun (hin _) i
  funext i
  by_cases hm : i∈covered e
  · obtain ⟨j,rfl⟩ := (cover_iff ..).mp hm
    exact congr_fun (show gwalk f _ _ ∘ e = withFrame A t f _ ∘ e by
      rw [gwalk_over,frame_cont, ha,frame_cont,point_cont]) j
  · rw [gwalk_out e p _ _ hm]
    unfold withFrame multiAct
    simp only [he i hm]
    apply congrArg
    funext j
    exact (hout (fun r => x r j) i hm).symm

section Parallel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Grouped `Path.parallel`: compose paths on disjoint sets of roles; batch multisets add. -/
theorem parallel (e : ι → ρ ↪ σ)
    (dis : ∀ i j, i ≠ j → ∀ r ∈ covered (e i), r ∉ covered (e j))
    (A : σ → OBase α) {s t : σ → Finset α} {d : ι → Multiset ℕ}
    {g : (σ→ℂ)→(σ→ℂ)} {h : ι → (ρ→ℂ) → (ρ→ℂ)}
    (q : ∀ i, MPath (A ∘ e i) (s ∘ e i) (t ∘ e i) (h i) (d i))
    (hin : ∀ i x, (g x) ∘ e i = h i (x ∘ e i))
    (hout : ∀ x r, (∀ i, r∉covered (e i)) → g x r=x r)
    (he : ∀ r, (∀ i, r∉covered (e i)) → s r=t r) :
    MPath A s t g (∑ i, d i) := by
  let u (j : Finset ι) := j.biUnion fun i => covered (e i)
  let l (j : Finset ι) (r : σ) := if r∈u j then t r else s r
  let k (j : Finset ι) (x : σ→ℂ) (r : σ) := if r∈u j then g x r else x r
  have hh (j : Finset ι) : MPath A s (l j) (k j) (∑ i ∈ j, d i) := by
    induction j using Finset.induction with
    | empty =>
      simp only [k,l,u,biUnion_empty,notMem_empty,ite_false,sum_empty]
      exact refl
    | insert i j hi ih =>
      have hiu (r) (hr : r∈covered (e i)) : r ∉ u j := by
        intro hg
        obtain ⟨w,hw,he'⟩ := mem_biUnion.mp hg
        have hw' : i ≠ w := fun hh => hi (hh ▸ hw)
        exact dis _ _ hw' r hr he'
      have hui (r) : r∈u (insert i j) ↔ r∈covered (e i) ∨ r∈u j := by
        simp [u]
      let fn (x : σ→ℂ) (r : σ) := if r∈covered (e i) then g x r else x r
      have compi (x) : fn x ∘ e i = h i (x∘e i) := by
        rw [← hin]
        funext j; simp [fn,covered]
      have gg : MPath A (l j) (l (insert i j)) fn (d i) := by
        apply lift (e i) A (h:=h i) _ compi
        · intro x l hl; simp [fn,hl]
        · intro r hr; simp [l,hui,hr]
        · have eq1 : l j ∘ e i = s ∘ e i := by
            funext r
            have h : e i r ∈ covered (e i) := by simp [covered]
            simp [l, hiu _ h]
          have eq2 : l (insert i j) ∘ e i = t ∘ e i := by
            funext r
            have h : e i r ∈ covered (e i) := by simp [covered]
            simp [l,hui,h]
          rw [eq1,eq2]; apply q
      have cmp : fn ∘ k j = k (insert i j) := by
        funext x r
        by_cases hqr : r ∈ covered (e i)
        · obtain ⟨r,rfl⟩ := (cover_iff ..).mp hqr
          change fn (k j x) _ = _
          have eq : k j x ∘ e i = x ∘ e i := by
            funext r
            have h : e i r ∈ covered (e i) := by simp [covered]
            simp [k,hiu _ h]
          have H := congr_fun (show fn (k j x) ∘ e i = g x ∘ e i by rw [compi,eq,hin]) r
          exact H.trans (by simp [k,hui,hqr])
        · simp [Function.comp,k,fn,hui,hqr]
      rw [sum_insert hi,add_comm]
      rw [← cmp]
      exact ih.trans gg
  have ha (r) : r∉u univ ↔ ∀ i, r∉covered (e i) := by simp [u]
  have eq1 : l univ = t := by
    funext r; by_cases h : r∈u univ
    · simp [l,h]
    · simp [l,h,he r ((ha r).1 h)]
  have eq2 : k univ = g := by
    funext x r; by_cases h : r∈u univ
    · simp [k,h]
    · simp [k,h,hout x r ((ha r).1 h)]
  have H := hh univ
  rwa [eq1,eq2] at H

end Parallel
end MPath
end Lift

/-- Grouped `translateAll`: translations only, no batches. -/
theorem gtranslateAll (z : ρ → Space α) :
    ∃ p : GWord α ρ, sizes p = [] ∧ ∀ f x,
      gwalk f p x = multiAct f (fun i => Binary.shift (z i)) x := by
  have hh (s : Finset ρ) :
      ∃ p : GWord α ρ, sizes p = [] ∧ ∀ f x,
        gwalk f p x = multiAct f (fun i => if i∈s then Binary.shift (z i) else 1) x := by
    induction s using Finset.induction with
    | empty =>
      exact ⟨[], rfl, by intro f x; funext j; simp [gwalk, multiAct]⟩
    | insert i s h ih =>
      obtain ⟨p,hp,hm⟩ := ih
      refine ⟨p++[.shift i (z i)], by rw [sizes_append, hp]; rfl, ?_⟩
      intro f x
      rw [gwalk_append, hm]
      funext j; by_cases e : j=i
      · subst j; simp [gwalk, multiAct, GMove.go, roleAct, h]
      · simp [gwalk, multiAct, GMove.go, roleAct, e]
  obtain ⟨p,hp,h⟩ := hh univ
  exact ⟨p,hp,by simpa using h⟩

end
end
end PowerSaving.Binary
end OAI
