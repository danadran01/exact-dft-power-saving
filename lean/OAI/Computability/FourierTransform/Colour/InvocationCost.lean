import OAI.Computability.FourierTransform.Colour.InvocationPath
import OAI.Computability.FourierTransform.Colour.Exponent

/-!
# Colour network, part 11b: the cost of one invocation (C11) (new)

For any stage `j`, any register design `D` and any weight `ψ : ℕ → ℝ` with `ψ 0 = 0`,
`Phi ψ (Einv j D) = Σ_roles roleCost ψ r` (`Phi_Einv`: swapping steps and roles), and every role's
edge list is the template of FORMALIZATION_CNET.md §2.3 (`cost_bx`, `cost_by`, `cost_bc`, `cost_bs`,
`cost_ba`, `cost_bb`), with the sizes computed from the label cardinalities (`card_L`,
`card_L_sdiff`, ...):

* banks: `(e-1)(h-1)`, `h-1`; centres: `(e-1)h`, `h`, `h`, `h`, `eh(F-1)`;
* side wires: `(e-1)h`, `1`, `h-2`, `1`, `eh(F-1)`;
* registers: `(e-1)h`, the structural unit edge, the middle edges of the register's chain
  (`xc`, `yc`; they sum to `h-1`, `xc_sum`, `yc_sum`), `eh(F-1)`.

`Phi_Einv_le` (**C11**): with `φ = (·/u)^z`, `Φ(E_inv,j) ≤ invBound …`, explicit in the counts:
registers with at most `nX` (X) resp. `nY` (Y) level changes (`xsteps`, `ysteps`) get the tangent
bound `n φ((h-1)/n)`, all others the crude bound `(h-1) φ(1)`. Helpers for designs:
`xsteps_le_two` (chain constant on the levels `1..h`), `xsteps_le`, `ysteps_le` (at most `k`
distinct labels).

`mem_Einv`: every batch size of an invocation lies in `[1, M)` once the explicit sizes are `< M`.
-/

namespace OAI
namespace PowerSaving.Colour
namespace ICost
open Finset Binary
open _root_.OAI.PowerSaving.Colour.Inv

/-! ### `Φ` on batch multisets -/

/-- `Φ_ψ(E) = Σ_{c ∈ E} ψ(c)`. -/
noncomputable def Phi (ψ : ℕ → ℝ) (E : Multiset ℕ) : ℝ := (E.map ψ).sum

lemma Phi_add (ψ : ℕ → ℝ) (A B : Multiset ℕ) : Phi ψ (A + B) = Phi ψ A + Phi ψ B := by
  simp [Phi]

lemma Phi_sum (ψ : ℕ → ℝ) {ι : Type*} (s : Finset ι) (M : ι → Multiset ℕ) :
    Phi ψ (∑ i ∈ s, M i) = ∑ i ∈ s, Phi ψ (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Phi]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Phi_add, ih]

lemma Phi_nsmul (ψ : ℕ → ℝ) (n : ℕ) (A : Multiset ℕ) : Phi ψ (n • A) = n * Phi ψ A := by
  induction n with
  | zero => simp [Phi]
  | succ n ih => rw [succ_nsmul, Phi_add, ih]; push_cast; ring

lemma Phi_bm (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (n : ℕ) : Phi ψ (bm n) = ψ n := by
  by_cases h : n = 0
  · subst h; simp [Phi, h0]
  · rw [bm_pos h]; simp [Phi]

section Roles
variable {α ρ : Type*} [Fintype ρ] [DecidableEq α]

lemma Phi_riseM (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (s t : ρ → Finset α) :
    Phi ψ (riseM s t) = ∑ r, ψ (t r \ s r).card := by
  unfold riseM; rw [Phi_sum]; simp only [Phi_bm ψ h0]

lemma Phi_fallM (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (s t : ρ → Finset α) :
    Phi ψ (fallM s t) = ∑ r, ψ (s r \ t r).card := by
  unfold fallM; rw [Phi_sum]; simp only [Phi_bm ψ h0]

lemma mem_riseM {s t : ρ → Finset α} {c : ℕ} (hc : c ∈ riseM s t) :
    ∃ r, c = (t r \ s r).card ∧ c ≠ 0 := by
  unfold riseM at hc
  obtain ⟨r, -, hr⟩ := Multiset.mem_sum.mp hc
  by_cases h : (t r \ s r).card = 0
  · rw [h, bm_zero] at hr; exact absurd hr (Multiset.notMem_zero _)
  · rw [bm_pos h, Multiset.mem_singleton] at hr; exact ⟨r, hr, hr ▸ h⟩

lemma mem_fallM {s t : ρ → Finset α} {c : ℕ} (hc : c ∈ fallM s t) :
    ∃ r, c = (s r \ t r).card ∧ c ≠ 0 := by
  unfold fallM at hc
  obtain ⟨r, -, hr⟩ := Multiset.mem_sum.mp hc
  by_cases h : (s r \ t r).card = 0
  · rw [h, bm_zero] at hr; exact absurd hr (Multiset.notMem_zero _)
  · rw [bm_pos h, Multiset.mem_singleton] at hr; exact ⟨r, hr, hr ▸ h⟩

end Roles

/-! ### Cardinalities of the labels -/

variable {hs : Fin 3 → ℕ} [∀ i, NeZero (hs i)]

/-- `e_j = ∏_{i<j} h_i`. -/
def pre (hs : Fin 3 → ℕ) (j : Fin 3) : ℕ := ![1, hs 0, hs 0 * hs 1] j
/-- `F_j = ∏_{i>j} h_i`. -/
def post (hs : Fin 3 → ℕ) (j : Fin 3) : ℕ := ![hs 1 * hs 2, hs 2, 1] j

lemma card_rect (j : Fin 3) (e : Bool) (s : Finset (Fin (hs j))) :
    (rect (H := fun i => Fin (hs i)) j e s).card = (if e then pre hs j else 1) * s.card := by
  rw [rect, Fintype.card_piFinset, Fin.prod_univ_three]
  revert s
  fin_cases j <;> intro s <;> cases e <;>
    simp [sets, pre, Function.update_of_ne, Fin.lt_def]

omit [∀ i, NeZero (hs i)] in
lemma card_univ_blk (j : Fin 3) :
    (univ : Finset (Blk hs)).card = pre hs j * hs j * post hs j := by
  rw [Finset.card_univ, Fintype.card_pi, Fin.prod_univ_three]
  fin_cases j <;> simp [pre, post] <;> ring

lemma rect_false_le (j : Fin 3) (s : Finset (Fin (hs j))) :
    rect (H := fun i => Fin (hs i)) j false s ⊆ rect j true s := by
  intro x hx
  rw [mem_rect] at hx ⊢
  exact ⟨hx.1, fun h => absurd h (by decide), hx.2.2⟩

lemma card_L (j : Fin 3) (I : Finset (Fin (hs j))) :
    (L j I).card = pre hs j * hs j - (hs j - I.card) := by
  show (lam (H := fun i => Fin (hs i)) j I).card = _
  rw [lam, card_sdiff_of_subset (rect_le_big _ _ _), big, card_rect, card_rect, card_univ_sdiff,
    Finset.card_univ, Fintype.card_fin]
  simp

lemma card_L_sdiff (j : Fin 3) {I I' : Finset (Fin (hs j))} (h : I ⊆ I') :
    (L j I' \ L j I).card = (I' \ I).card := by
  show (lam (H := fun i => Fin (hs i)) j I' \ lam j I).card = _
  rw [lam_sdiff j h, card_rect]; simp

lemma card_xin (j : Fin 3) : (xin (hs := hs) j).card = pre hs j := by
  rw [xin, card_rect]; simp

lemma card_yin (j : Fin 3) : (yin (hs := hs) j).card = pre hs j - 1 := by
  rw [yin, card_sdiff_of_subset (rect_false_le _ _), card_rect, card_rect]; simp


/-! ### Register chains and their level changes -/

section Chains
variable {h : ℕ} (D : RegisterDesign h)

/-- The chain of an X-register: `{xslot} → xlab 1 → … → xlab h → univ`. -/
def xc (r : D.XReg) (ℓ : ℕ) : Finset (Fin h) :=
  if ℓ = 0 then {D.xslot r} else if ℓ ≤ h then D.xlab r ℓ else univ

/-- The chain of a Y-register: `∅ → ylab 1 → … → ylab h → univ \ {yslot}`. -/
def yc (r : D.YReg) (ℓ : ℕ) : Finset (Fin h) :=
  if ℓ = 0 then ∅ else if ℓ ≤ h then D.ylab r ℓ else univ \ {D.yslot r}

/-- Number of nonzero middle edges of an X-register (level changes of its chain). -/
def xsteps (r : D.XReg) : ℕ := ((range (h + 1)).filter fun ℓ => xc D r (ℓ + 1) ≠ xc D r ℓ).card

/-- Number of nonzero middle edges of a Y-register (level changes of its chain). -/
def ysteps (r : D.YReg) : ℕ := ((range (h + 1)).filter fun ℓ => yc D r (ℓ + 1) ≠ yc D r ℓ).card

lemma xc_mono (hh : 1 ≤ h) (r : D.XReg) (ℓ : ℕ) : xc D r ℓ ⊆ xc D r (ℓ + 1) := by
  unfold xc
  by_cases h0 : ℓ = 0
  · subst h0
    simp only [↓reduceIte, hh]
    exact singleton_subset_iff.mpr (D.x_mem r 1)
  · simp only [h0, ↓reduceIte, Nat.add_one_ne_zero]
    by_cases h1 : ℓ + 1 ≤ h
    · rw [ite_eq_left (by omega), ite_eq_left h1]; exact D.x_mono r (Nat.le_succ ℓ)
    · rw [ite_eq_right h1]; exact subset_univ _

lemma yc_mono (r : D.YReg) (ℓ : ℕ) : yc D r ℓ ⊆ yc D r (ℓ + 1) := by
  unfold yc
  by_cases h0 : ℓ = 0
  · subst h0; simp
  · simp only [h0, ↓reduceIte, Nat.add_one_ne_zero]
    by_cases h1 : ℓ + 1 ≤ h
    · rw [ite_eq_left (by omega), ite_eq_left h1]; exact D.y_mono r (Nat.le_succ ℓ)
    · rw [ite_eq_right h1]
      by_cases h2 : ℓ ≤ h
      · rw [ite_eq_left h2]
        intro i hi
        rw [mem_sdiff, mem_singleton]
        exact ⟨mem_univ _, fun e => D.y_out r ℓ (e ▸ hi)⟩
      · rw [ite_eq_right h2]

/-- Coordinate X-registers: a chain constant on the levels `1..h` has at most 2 level changes. -/
lemma xsteps_le_two (r : D.XReg) (hc : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ h → D.xlab r ℓ = D.xlab r 1) :
    xsteps D r ≤ 2 := by
  unfold xsteps
  calc _ ≤ ({0, h} : Finset ℕ).card := by
        apply card_le_card
        intro ℓ hℓ
        rw [mem_filter, mem_range] at hℓ
        rw [mem_insert, mem_singleton]
        by_contra hne
        push Not at hne
        apply hℓ.2
        unfold xc
        rw [ite_eq_right (by omega), ite_eq_right hne.1, ite_eq_left (by omega), ite_eq_left (by omega),
          hc (ℓ + 1) (by omega) (by omega), hc ℓ (by omega) (by omega)]
    _ ≤ 2 := card_le_two

/-- Monotone chains: different change points give different new values. -/
lemma steps_le_image {α : Type*} [DecidableEq α] (c : ℕ → Finset α) (hc : ∀ ℓ, c ℓ ⊆ c (ℓ + 1))
    (N : ℕ) (V : Finset (Finset α)) (hV : ∀ ℓ ∈ (range N).filter (fun ℓ => c (ℓ + 1) ≠ c ℓ),
      c (ℓ + 1) ∈ V) :
    ((range N).filter fun ℓ => c (ℓ + 1) ≠ c ℓ).card ≤ V.card := by
  have hm : Monotone c := monotone_nat_of_le_succ hc
  apply card_le_card_of_injOn (fun ℓ => c (ℓ + 1)) hV
  intro a ha b hb hab
  simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha hb
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · apply hb.2
    apply le_antisymm _ (hc b)
    calc c (b + 1) = c (a + 1) := hab.symm
      _ ⊆ c b := hm (by omega)
  · apply ha.2
    apply le_antisymm _ (hc a)
    calc c (a + 1) = c (b + 1) := hab
      _ ⊆ c a := hm (by omega)

/-- Coordinate Y-registers: a chain with at most `k` distinct labels on the levels `1..h` has at
most `k + 1` level changes. -/
lemma ysteps_le (r : D.YReg) (k : ℕ) (hk : ((Icc 1 h).image (D.ylab r)).card ≤ k) :
    ysteps D r ≤ k + 1 := by
  unfold ysteps
  refine (steps_le_image (yc D r) (yc_mono D r) (h + 1)
    (insert (univ \ {D.yslot r}) ((Icc 1 h).image (D.ylab r))) ?_).trans
    ((card_insert_le _ _).trans (by omega))
  intro ℓ hℓ
  rw [mem_filter, mem_range] at hℓ
  rw [mem_insert, mem_image]
  unfold yc
  rw [ite_eq_right (by omega)]
  by_cases h1 : ℓ + 1 ≤ h
  · rw [ite_eq_left h1]; exact Or.inr ⟨ℓ + 1, mem_Icc.mpr ⟨by omega, h1⟩, rfl⟩
  · rw [ite_eq_right h1]; exact Or.inl rfl

/-- X-registers: a chain with at most `k` distinct labels other than `{xslot}` on the levels
`1..h` has at most `k + 1` level changes (coordinate X-registers: `k = 1`). -/
lemma xsteps_le (hh : 1 ≤ h) (r : D.XReg) (k : ℕ)
    (hk : (((Icc 1 h).image (D.xlab r)).erase {D.xslot r}).card ≤ k) : xsteps D r ≤ k + 1 := by
  unfold xsteps
  have hm : Monotone (xc D r) := monotone_nat_of_le_succ (xc_mono D hh r)
  have h0 : xc D r 0 = {D.xslot r} := by simp [xc]
  refine (steps_le_image (xc D r) (xc_mono D hh r) (h + 1)
    (insert univ (((Icc 1 h).image (D.xlab r)).erase {D.xslot r})) ?_).trans
    ((card_insert_le _ _).trans (by omega))
  intro ℓ hℓ
  rw [mem_filter, mem_range] at hℓ
  rw [mem_insert]
  by_cases h1 : ℓ + 1 ≤ h
  · right
    have e : xc D r (ℓ + 1) = D.xlab r (ℓ + 1) := by
      unfold xc; rw [ite_eq_right (by omega), ite_eq_left h1]
    rw [mem_erase, mem_image]
    refine ⟨fun hs => hℓ.2 ?_, ⟨ℓ + 1, mem_Icc.mpr ⟨by omega, h1⟩, e.symm⟩⟩
    have a1 : xc D r ℓ ⊆ xc D r (ℓ + 1) := xc_mono D hh r ℓ
    have a2 : xc D r 0 ⊆ xc D r ℓ := hm (Nat.zero_le ℓ)
    rw [hs] at a1 ⊢
    rw [h0] at a2
    exact (subset_antisymm a1 a2).symm
  · left
    unfold xc; rw [ite_eq_right (by omega), ite_eq_right h1]

/-- Telescoping along a monotone chain. -/
lemma tele {α : Type*} [DecidableEq α] (c : ℕ → Finset α) (hc : ∀ ℓ, c ℓ ⊆ c (ℓ + 1)) (n : ℕ) :
    ∑ ℓ ∈ range n, (c (ℓ + 1) \ c ℓ).card + (c 0).card = (c n).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_right_comm, ih, add_comm, card_sdiff_add_card_eq_card (hc n)]

lemma xc_sum (hh : 1 ≤ h) (r : D.XReg) :
    ∑ ℓ ∈ range (h + 1), (xc D r (ℓ + 1) \ xc D r ℓ).card = h - 1 := by
  have := tele (xc D r) (xc_mono D hh r) (h + 1)
  have e0 : xc D r 0 = {D.xslot r} := by simp [xc]
  have e1 : xc D r (h + 1) = univ := by simp [xc]
  rw [e0, e1, card_singleton, card_univ, Fintype.card_fin] at this
  omega

lemma yc_sum (r : D.YReg) :
    ∑ ℓ ∈ range (h + 1), (yc D r (ℓ + 1) \ yc D r ℓ).card = h - 1 := by
  have := tele (yc D r) (yc_mono D r) (h + 1)
  have e0 : yc D r 0 = ∅ := by simp [yc]
  have e1 : yc D r (h + 1) = univ \ {D.yslot r} := by simp [yc]
  rw [e0, e1, card_empty, card_univ_sdiff, card_singleton, Fintype.card_fin] at this
  omega

end Chains

/-! ### Middle edges: tangent and crude bounds -/

/-- `φ` on batch sizes. -/
noncomputable def φn (u z : ℝ) (k : ℕ) : ℝ := Expo.phiG u z k

lemma φn_zero (u z : ℝ) (hz : z ≠ 0) : φn u z 0 = 0 := by
  simp [φn, Expo.phiG_zero u z hz]

section Middle
variable {u z : ℝ} (hu : 0 < u) (hz0 : 0 < z) (hz1 : z ≤ 1)
include hu hz0 hz1

/-- Crude bound for the middle edges of a chain: `Σ φ(Δ) ≤ (Σ Δ) φ(1)`. -/
lemma mid_crude {α : Type*} [DecidableEq α] (c : ℕ → Finset α) (N S : ℕ)
    (hS : ∑ ℓ ∈ range N, (c (ℓ + 1) \ c ℓ).card = S) :
    ∑ ℓ ∈ range N, φn u z (c (ℓ + 1) \ c ℓ).card ≤ S * φn u z 1 := by
  calc _ ≤ ∑ ℓ ∈ range N, ((c (ℓ + 1) \ c ℓ).card : ℝ) * φn u z 1 :=
        sum_le_sum (fun ℓ _ => by
          have := Expo.phiG_le_mul hu hz0 hz1 (c (ℓ + 1) \ c ℓ).card
          simpa [φn] using this)
    _ = S * φn u z 1 := by rw [← sum_mul, ← hS]; push_cast; rfl

/-- Tangent bound for the middle edges of a chain with at most `n` level changes. -/
lemma mid_tangent {α : Type*} [DecidableEq α] (c : ℕ → Finset α) (hc : ∀ ℓ, c ℓ ⊆ c (ℓ + 1))
    (N S n : ℕ) (hS : ∑ ℓ ∈ range N, (c (ℓ + 1) \ c ℓ).card = S) (hS0 : 0 < S) (hn : 0 < n)
    (hsteps : ((range N).filter fun ℓ => c (ℓ + 1) ≠ c ℓ).card ≤ n) :
    ∑ ℓ ∈ range N, φn u z (c (ℓ + 1) \ c ℓ).card ≤ n * Expo.phiG u z ((S : ℝ) / n) := by
  have key := Expo.tangent_sum (range N) (fun ℓ => ((c (ℓ + 1) \ c ℓ).card : ℝ)) hu hz0 hz1 hn
    (S := S) (by exact_mod_cast hS0) (fun _ _ => Nat.cast_nonneg _) ?_ ?_
  · exact key
  · refine le_trans (le_of_eq ?_) hsteps
    congr 1
    apply filter_congr
    intro ℓ _
    rw [Ne, Nat.cast_eq_zero, card_eq_zero, sdiff_eq_empty_iff_subset, Ne]
    constructor
    · intro h e; exact h (e ▸ subset_rfl)
    · intro h hsub; exact h (subset_antisymm hsub (hc ℓ))
  · rw [← hS]; push_cast; rfl

end Middle

/-! ### The edges of one invocation, role by role -/

section Edges
variable (j : Fin 3) (D : RegisterDesign (hs j))

/-- All edges of one local role, in schedule order, weighted by `ψ`. -/
noncomputable def roleCost (ψ : ℕ → ℝ) (r : D.Box) : ℝ :=
  ψ (p1 j D r \ p0 j D r).card + ψ (p2 j D r \ p1 j D r).card + ψ (p3 j D r \ p2 j D r).card
  + ψ (p4 j D r \ p3 j D r).card
  + ∑ ℓ ∈ range (hs j), ψ (p5 j D (ℓ + 1) r \ q5 j D ℓ r).card
  + ψ (p6 j D r \ q5 j D (hs j) r).card + ψ (p6 j D r \ p7 j D r).card
  + ψ (p8 j D r \ p7 j D r).card + ψ (p9 j D r \ p8 j D r).card
  + ψ (p10 j D r \ p9 j D r).card + ψ (p11 j D r \ p10 j D r).card
  + ψ (pend j D r \ p11 j D r).card

/-- Swapping the sums over steps and roles: `Φ(E_inv) = Σ_roles Φ(edges of the role)`. -/
theorem Phi_Einv (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) : Phi ψ (Einv j D) = ∑ r, roleCost j D ψ r := by
  have h5 : Phi ψ (∑ ℓ ∈ range (hs j), riseM (q5 j D ℓ) (p5 j D (ℓ + 1)))
      = ∑ r, ∑ ℓ ∈ range (hs j), ψ (p5 j D (ℓ + 1) r \ q5 j D ℓ r).card := by
    rw [Phi_sum]; simp only [Phi_riseM ψ h0]; exact Finset.sum_comm
  simp only [Einv, Phi_add, Phi_riseM ψ h0, Phi_fallM ψ h0, h5, roleCost, Finset.sum_add_distrib]

/-! Edge sizes (FORMALIZATION_CNET.md §2.3): `e = pre`, `F = post`. -/

/-- `(e-1)(h-1)`, X-bank. -/
def bk1N : ℕ := pre hs j * hs j - (hs j - 1) - pre hs j
/-- `(e-1)(h-1)`, Y-bank. -/
def bk1yN : ℕ := pre hs j * hs j - hs j - (pre hs j - 1)
/-- Bot `(e-1)h`. -/
def botN : ℕ := pre hs j * hs j - hs j
/-- Top `eh(F-1)`. -/
def topN : ℕ := pre hs j * hs j * post hs j - pre hs j * hs j

variable {j}

lemma e_Xb0_xin : (Xb0 (hs := hs) j \ xin j).card = bk1N (hs := hs) j := by
  rw [card_sdiff_of_subset (xin_le j), card_L, card_xin, bk1N, card_singleton]
lemma e_Top_Xb0 : (Top (hs := hs) j \ Xb0 j).card = hs j - 1 := by
  rw [card_L_sdiff j (subset_univ _), card_univ_sdiff, card_singleton, Fintype.card_fin]
lemma e_Bot_yin : (Bot (hs := hs) j \ yin j).card = bk1yN (hs := hs) j := by
  rw [card_sdiff_of_subset (yin_le j), card_L, card_yin, bk1yN, card_empty, Nat.sub_zero]
lemma e_Yt0_Bot : (Yt0 (hs := hs) j \ Bot j).card = hs j - 1 := by
  rw [card_L_sdiff j (empty_subset _), sdiff_empty, card_univ_sdiff, card_singleton,
    Fintype.card_fin]
lemma e_Bot : (Bot (hs := hs) j).card = botN (hs := hs) j := by
  rw [card_L, card_empty, Nat.sub_zero, botN]
lemma e_Top_Bot : (Top (hs := hs) j \ Bot j).card = hs j := by
  rw [card_L_sdiff j (empty_subset _), sdiff_empty, card_univ, Fintype.card_fin]
lemma e_univ_Top : ((univ : Finset (Blk hs)) \ Top j).card = topN (hs := hs) j := by
  rw [card_sdiff_of_subset (subset_univ _), card_univ_blk j, card_L, card_univ, Fintype.card_fin,
    Nat.sub_self, Nat.sub_zero, topN]
lemma e_Xb0_Bot : (Xb0 (hs := hs) j \ Bot j).card = 1 := by
  rw [card_L_sdiff j (empty_subset _), sdiff_empty, card_singleton]
lemma e_Yt1_Xb0 (hh : 2 ≤ hs j) : (Yt1 (hs := hs) j \ Xb0 j).card = hs j - 2 := by
  have h01 : (0 : Fin (hs j)) ≠ 1 := fin_zero_ne_one (by omega)
  have hsub : ({0} : Finset (Fin (hs j))) ⊆ univ \ {1} := by
    intro x hx; rw [mem_singleton] at hx; subst hx; simp [h01]
  rw [card_L_sdiff j hsub, card_sdiff_of_subset hsub, card_univ_sdiff, card_singleton,
    card_singleton, Fintype.card_fin]
  omega
lemma e_Top_Yt1 : (Top (hs := hs) j \ Yt1 j).card = 1 := by
  rw [card_L_sdiff j (subset_univ _), sdiff_sdiff_right_self, inf_eq_inter, univ_inter,
    card_singleton]
lemma e_slot_Bot (x : Fin (hs j)) : (L (hs := hs) j {x} \ Bot j).card = 1 := by
  rw [card_L_sdiff j (empty_subset _), sdiff_empty, card_singleton]
lemma e_Top_slot (y : Fin (hs j)) : (Top (hs := hs) j \ L j (univ \ {y})).card = 1 := by
  rw [card_L_sdiff j (subset_univ _), sdiff_sdiff_right_self, inf_eq_inter, univ_inter,
    card_singleton]

variable (j)

lemma cost_bx (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (T : Trip (hs j)) :
    roleCost j D ψ (D.bx T) = ψ (bk1N (hs := hs) j) + ψ (hs j - 1) := by
  have hq : ∀ ℓ, q5 j D ℓ (D.bx T) = Xb0 j := fun ℓ => by cases ℓ <;> rfl
  simp [roleCost, hq, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, pend, stamp, h0, e_Xb0_xin, e_Top_Xb0]

lemma cost_by (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (S : Trip (hs j)) :
    roleCost j D ψ (D.byy S) = ψ (bk1yN (hs := hs) j) + ψ (hs j - 1) := by
  have hq : ∀ ℓ, q5 j D ℓ (D.byy S) = Bot j := fun ℓ => by cases ℓ <;> rfl
  simp [roleCost, hq, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, pend, stamp, h0, e_Bot_yin, e_Yt0_Bot]

lemma cost_bc (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (c : Fin (hs j)) :
    roleCost j D ψ (D.bc c) = ψ (botN (hs := hs) j) + 3 * ψ (hs j) + ψ (topN (hs := hs) j) := by
  have hq : ∀ ℓ, q5 j D ℓ (D.bc c) = Bot j := fun ℓ => by cases ℓ <;> rfl
  simp [roleCost, hq, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, pend, stamp, h0, e_Bot, e_Top_Bot, e_univ_Top]
  ring

lemma cost_bs (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (hh : 2 ≤ hs j) (σ : D.Side) :
    roleCost j D ψ (D.bs σ) = ψ (botN (hs := hs) j) + 2 * ψ 1 + ψ (hs j - 2)
      + ψ (topN (hs := hs) j) := by
  have hq : ∀ ℓ, q5 j D ℓ (D.bs σ) = Xb0 j := fun ℓ => by cases ℓ <;> rfl
  have e1 := e_Xb0_Bot (hs := hs) (j := j)
  have e2 := e_Top_Yt1 (hs := hs) (j := j)
  simp [roleCost, hq, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, pend, stamp, h0, e1, e2, e_Bot, e_Yt1_Xb0 hh, e_univ_Top]
  ring

lemma q5_ba (r : D.XReg) (ℓ : ℕ) (hℓ : ℓ ≤ hs j) : q5 j D ℓ (D.ba r) = L j (xc D r ℓ) := by
  cases ℓ with
  | zero => rfl
  | succ n => simp [q5, p5, stamp, xc, hℓ]

lemma q5_bb (r : D.YReg) (ℓ : ℕ) (hℓ : ℓ ≤ hs j) : q5 j D ℓ (D.bb r) = L j (yc D r ℓ) := by
  cases ℓ with
  | zero => simp [q5, p4, stamp, yc]
  | succ n => simp [q5, p5, stamp, yc, hℓ]

lemma cost_ba (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (r : D.XReg) :
    roleCost j D ψ (D.ba r) = ψ (botN (hs := hs) j) + ψ 1
      + ∑ ℓ ∈ range (hs j + 1), ψ (xc D r (ℓ + 1) \ xc D r ℓ).card + ψ (topN (hs := hs) j) := by
  have hpos : 0 < hs j := Nat.pos_of_ne_zero (NeZero.ne _)
  have hmid : ∑ ℓ ∈ range (hs j), ψ (p5 j D (ℓ + 1) (D.ba r) \ q5 j D ℓ (D.ba r)).card
      + ψ (p10 j D (D.ba r) \ p9 j D (D.ba r)).card
      = ∑ ℓ ∈ range (hs j + 1), ψ (xc D r (ℓ + 1) \ xc D r ℓ).card := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro ℓ hℓ
      rw [mem_range] at hℓ
      rw [q5_ba j D r ℓ hℓ.le]
      have e : p5 j D (ℓ + 1) (D.ba r) = L j (xc D r (ℓ + 1)) := by
        simp [p5, stamp, xc, show ℓ + 1 ≤ hs j by omega]
      rw [e, card_L_sdiff j (xc_mono D hpos r ℓ)]
    · have e1 : p10 j D (D.ba r) = L j (xc D r (hs j + 1)) := by simp [p10, stamp, xc]
      have e2 : p9 j D (D.ba r) = L j (xc D r (hs j)) := by
        simp [p9, stamp, xc, Nat.pos_iff_ne_zero.mp hpos]
      rw [e1, e2, card_L_sdiff j (xc_mono D hpos r _)]
  have hsplit : roleCost j D ψ (D.ba r) = ψ (p1 j D (D.ba r) \ p0 j D (D.ba r)).card
      + ψ (p2 j D (D.ba r) \ p1 j D (D.ba r)).card + ψ (p3 j D (D.ba r) \ p2 j D (D.ba r)).card
      + ψ (p4 j D (D.ba r) \ p3 j D (D.ba r)).card + ψ (p6 j D (D.ba r) \ p5 j D (hs j) (D.ba r)).card
      + ψ (p6 j D (D.ba r) \ p7 j D (D.ba r)).card + ψ (p8 j D (D.ba r) \ p7 j D (D.ba r)).card
      + ψ (p9 j D (D.ba r) \ p8 j D (D.ba r)).card + ψ (p11 j D (D.ba r) \ p10 j D (D.ba r)).card
      + ψ (pend j D (D.ba r) \ p11 j D (D.ba r)).card
      + (∑ ℓ ∈ range (hs j), ψ (p5 j D (ℓ + 1) (D.ba r) \ q5 j D ℓ (D.ba r)).card
        + ψ (p10 j D (D.ba r) \ p9 j D (D.ba r)).card) := by
    rw [roleCost, q5_pos j D (hs j) hpos]; ring
  have e1 := e_slot_Bot (hs := hs) (j := j) (D.xslot r)
  rw [hsplit, hmid]
  simp [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, pend, stamp, h0, e1, e_Bot, e_univ_Top]
  ring

lemma cost_bb (ψ : ℕ → ℝ) (h0 : ψ 0 = 0) (r : D.YReg) :
    roleCost j D ψ (D.bb r) = ψ (botN (hs := hs) j) + ψ 1
      + ∑ ℓ ∈ range (hs j + 1), ψ (yc D r (ℓ + 1) \ yc D r ℓ).card + ψ (topN (hs := hs) j) := by
  have hpos : 0 < hs j := Nat.pos_of_ne_zero (NeZero.ne _)
  have hmid : ∑ ℓ ∈ range (hs j), ψ (p5 j D (ℓ + 1) (D.bb r) \ q5 j D ℓ (D.bb r)).card
      + ψ (p8 j D (D.bb r) \ p7 j D (D.bb r)).card
      = ∑ ℓ ∈ range (hs j + 1), ψ (yc D r (ℓ + 1) \ yc D r ℓ).card := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro ℓ hℓ
      rw [mem_range] at hℓ
      rw [q5_bb j D r ℓ hℓ.le]
      have e : p5 j D (ℓ + 1) (D.bb r) = L j (yc D r (ℓ + 1)) := by
        simp [p5, stamp, yc, show ℓ + 1 ≤ hs j by omega]
      rw [e, card_L_sdiff j (yc_mono D r ℓ)]
    · have e1 : p8 j D (D.bb r) = L j (yc D r (hs j + 1)) := by simp [p8, stamp, yc]
      have e2 : p7 j D (D.bb r) = L j (yc D r (hs j)) := by
        simp [p7, stamp, yc, Nat.pos_iff_ne_zero.mp hpos]
      rw [e1, e2, card_L_sdiff j (yc_mono D r _)]
  have hsplit : roleCost j D ψ (D.bb r) = ψ (p1 j D (D.bb r) \ p0 j D (D.bb r)).card
      + ψ (p2 j D (D.bb r) \ p1 j D (D.bb r)).card + ψ (p3 j D (D.bb r) \ p2 j D (D.bb r)).card
      + ψ (p4 j D (D.bb r) \ p3 j D (D.bb r)).card + ψ (p6 j D (D.bb r) \ p5 j D (hs j) (D.bb r)).card
      + ψ (p6 j D (D.bb r) \ p7 j D (D.bb r)).card + ψ (p10 j D (D.bb r) \ p9 j D (D.bb r)).card
      + ψ (p9 j D (D.bb r) \ p8 j D (D.bb r)).card + ψ (p11 j D (D.bb r) \ p10 j D (D.bb r)).card
      + ψ (pend j D (D.bb r) \ p11 j D (D.bb r)).card
      + (∑ ℓ ∈ range (hs j), ψ (p5 j D (ℓ + 1) (D.bb r) \ q5 j D ℓ (D.bb r)).card
        + ψ (p8 j D (D.bb r) \ p7 j D (D.bb r)).card) := by
    rw [roleCost, q5_pos j D (hs j) hpos]; ring
  have e1 := e_Top_slot (hs := hs) (j := j) (D.yslot r)
  rw [hsplit, hmid]
  simp [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, pend, stamp, h0, e1, e_Bot, e_univ_Top]
  ring

end Edges

/-! ### C11: the per-invocation cost bound -/

section Bound
variable (j : Fin 3) (D : RegisterDesign (hs j))

/-- Short X-registers: at most `nX` nonzero middle edges. -/
def nXs (nX : ℕ) : ℕ := (univ.filter fun r : D.XReg => xsteps D r ≤ nX).card
/-- The other X-registers. -/
def nXl (nX : ℕ) : ℕ := (univ.filter fun r : D.XReg => ¬ xsteps D r ≤ nX).card
/-- Short Y-registers: at most `nY` nonzero middle edges. -/
def nYs (nY : ℕ) : ℕ := (univ.filter fun r : D.YReg => ysteps D r ≤ nY).card
/-- The other Y-registers. -/
def nYl (nY : ℕ) : ℕ := (univ.filter fun r : D.YReg => ¬ ysteps D r ≤ nY).card

/-- **The explicit per-invocation bound** `B_j` in terms of the counts: `v` bank pairs, `h`
centres, `nS` side wires, `nXs`/`nYs` registers with at most `nX`/`nY` middle edges (tangent
bound), `nL` other registers (crude bound). -/
noncomputable def invBound (u z : ℝ) (v nS nXs nYs nL nX nY : ℕ) : ℝ :=
  v * (φn u z (bk1N (hs := hs) j) + φn u z (hs j - 1))
    + v * (φn u z (bk1yN (hs := hs) j) + φn u z (hs j - 1))
    + hs j * (φn u z (botN (hs := hs) j) + 3 * φn u z (hs j) + φn u z (topN (hs := hs) j))
    + nS * (φn u z (botN (hs := hs) j) + 2 * φn u z 1 + φn u z (hs j - 2)
      + φn u z (topN (hs := hs) j))
    + nXs * (φn u z (botN (hs := hs) j) + φn u z 1
      + nX * Expo.phiG u z (((hs j - 1 : ℕ) : ℝ) / nX) + φn u z (topN (hs := hs) j))
    + nYs * (φn u z (botN (hs := hs) j) + φn u z 1
      + nY * Expo.phiG u z (((hs j - 1 : ℕ) : ℝ) / nY) + φn u z (topN (hs := hs) j))
    + nL * (φn u z (botN (hs := hs) j) + hs j * φn u z 1 + φn u z (topN (hs := hs) j))

lemma sum_ite_le {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] (f : ι → ℝ) (A B : ℝ)
    (hA : ∀ i, p i → f i ≤ A) (hB : ∀ i, f i ≤ B) :
    ∑ i, f i ≤ (univ.filter p).card * A + (univ.filter fun i => ¬ p i).card * B := by
  calc ∑ i, f i ≤ ∑ i, (if p i then A else B) :=
        sum_le_sum (fun i _ => by split_ifs with h; exacts [hA i h, hB i])
    _ = _ := by rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]

/-- **C11**: `Φ(E_inv,j) ≤ B_j` for any register design. -/
theorem Phi_Einv_le {u z : ℝ} (hu : 0 < u) (hz0 : 0 < z) (hz1 : z ≤ 1) (hh : 2 ≤ hs j)
    (nX nY : ℕ) (hnX : 0 < nX) (hnY : 0 < nY) :
    Phi (φn u z) (Einv j D) ≤ invBound (hs := hs) j u z (Fintype.card (Trip (hs j))) (Fintype.card D.Side)
      (nXs j D nX) (nYs j D nY) (nXl j D nX + nYl j D nY) nX nY := by
  have h0 : φn u z 0 = 0 := φn_zero u z hz0.ne'
  set ψ := φn u z with hψ
  rw [Phi_Einv j D ψ h0]
  simp only [Fintype.sum_sum_type]
  have h1 : (1 : ℝ) ≤ hs j := by exact_mod_cast (show 1 ≤ hs j by omega)
  have hcast : (((hs j - 1 : ℕ)) : ℝ) = hs j - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hS : 0 < hs j - 1 := by omega
  have s1 : ∑ T : Trip (hs j), roleCost j D ψ (.inl (.inl T))
      = Fintype.card (Trip (hs j)) * (ψ (bk1N (hs := hs) j) + ψ (hs j - 1)) := by
    rw [sum_congr rfl (fun T _ => cost_bx j D ψ h0 T), sum_const, card_univ, nsmul_eq_mul]
  have s2 : ∑ S : Trip (hs j), roleCost j D ψ (.inl (.inr S))
      = Fintype.card (Trip (hs j)) * (ψ (bk1yN (hs := hs) j) + ψ (hs j - 1)) := by
    rw [sum_congr rfl (fun S _ => cost_by j D ψ h0 S), sum_const, card_univ, nsmul_eq_mul]
  have s3 : ∑ c : Fin (hs j), roleCost j D ψ (.inr (.inl c))
      = hs j * (ψ (botN (hs := hs) j) + 3 * ψ (hs j) + ψ (topN (hs := hs) j)) := by
    rw [sum_congr rfl (fun c _ => cost_bc j D ψ h0 c), sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have s4 : ∑ σ : D.Side, roleCost j D ψ (.inr (.inr (.inl σ)))
      = Fintype.card D.Side * (ψ (botN (hs := hs) j) + 2 * ψ 1 + ψ (hs j - 2)
        + ψ (topN (hs := hs) j)) := by
    rw [sum_congr rfl (fun σ _ => cost_bs j D ψ h0 hh σ), sum_const, card_univ, nsmul_eq_mul]
  have s5 := sum_ite_le (fun r : D.XReg => xsteps D r ≤ nX)
    (fun r => roleCost j D ψ (.inr (.inr (.inr (.inl r)))))
    (ψ (botN (hs := hs) j) + ψ 1 + nX * Expo.phiG u z (((hs j - 1 : ℕ) : ℝ) / nX)
      + ψ (topN (hs := hs) j))
    (ψ (botN (hs := hs) j) + hs j * ψ 1 + ψ (topN (hs := hs) j))
    (fun r hr => by
      show roleCost j D ψ (D.ba r) ≤ _
      rw [cost_ba j D ψ h0 r]
      have := mid_tangent hu hz0 hz1 (xc D r) (xc_mono D (by omega) r) (hs j + 1) (hs j - 1) nX
        (xc_sum D (by omega) r) hS hnX hr
      linarith)
    (fun r => by
      show roleCost j D ψ (D.ba r) ≤ _
      rw [cost_ba j D ψ h0 r]
      have := mid_crude hu hz0 hz1 (xc D r) (hs j + 1) (hs j - 1) (xc_sum D (by omega) r)
      rw [hcast] at this
      nlinarith)
  have s6 := sum_ite_le (fun r : D.YReg => ysteps D r ≤ nY)
    (fun r => roleCost j D ψ (.inr (.inr (.inr (.inr r)))))
    (ψ (botN (hs := hs) j) + ψ 1 + nY * Expo.phiG u z (((hs j - 1 : ℕ) : ℝ) / nY)
      + ψ (topN (hs := hs) j))
    (ψ (botN (hs := hs) j) + hs j * ψ 1 + ψ (topN (hs := hs) j))
    (fun r hr => by
      show roleCost j D ψ (D.bb r) ≤ _
      rw [cost_bb j D ψ h0 r]
      have := mid_tangent hu hz0 hz1 (yc D r) (yc_mono D r) (hs j + 1) (hs j - 1) nY
        (yc_sum D r) hS hnY hr
      linarith)
    (fun r => by
      show roleCost j D ψ (D.bb r) ≤ _
      rw [cost_bb j D ψ h0 r]
      have := mid_crude hu hz0 hz1 (yc D r) (hs j + 1) (hs j - 1) (yc_sum D r)
      rw [hcast] at this
      nlinarith)
  rw [s1, s2, s3, s4]
  unfold invBound nXs nXl nYs nYl
  push_cast
  linarith

/-- The constant-indicator weight used to locate the batch sizes. -/
noncomputable def ind (M : ℕ) (c : ℕ) : ℝ := if M ≤ c then 1 else 0

lemma Einv_ne_zero : ∀ c ∈ Einv j D, c ≠ 0 := by
  intro c hc
  simp only [Einv, Multiset.mem_add] at hc
  rcases hc with (((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  all_goals first
    | (obtain ⟨_, _, h'⟩ := mem_riseM h; exact h')
    | (obtain ⟨ℓ, -, hℓ⟩ := Multiset.mem_sum.mp h; obtain ⟨_, _, h'⟩ := mem_riseM hℓ; exact h')

/-- **Batch sizes of one invocation**: all in `[1, M)` once the explicit edge sizes are `< M`. -/
theorem mem_Einv (hh : 2 ≤ hs j) (M : ℕ) (hM1 : bk1N (hs := hs) j < M) (hM2 : bk1yN (hs := hs) j < M)
    (hM3 : botN (hs := hs) j < M) (hM4 : topN (hs := hs) j < M) (hM5 : hs j < M) :
    ∀ c ∈ Einv j D, 1 ≤ c ∧ c < M := by
  intro c hc
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Einv_ne_zero j D c hc), ?_⟩
  by_contra hcM
  push Not at hcM
  have h0 : ind M 0 = 0 := by simp [ind]; omega
  have hz : ∀ k, k < M → ind M k = 0 := fun k hk => by simp [ind]; omega
  have hmid : ∀ (A B : Finset (Fin (hs j))), ind M (A \ B).card = 0 := fun A B =>
    hz _ (lt_of_le_of_lt ((card_le_univ _).trans (by rw [Fintype.card_fin])) hM5)
  have hall : Phi (ind M) (Einv j D) = 0 := by
    rw [Phi_Einv j D _ h0]
    apply sum_eq_zero
    rintro ((T|S)|(c|σ|r|r)) -
    · rw [show (Sum.inl (Sum.inl T) : D.Box) = D.bx T from rfl, cost_bx j D _ h0,
        hz _ hM1, hz _ (by omega)]; simp
    · rw [show (Sum.inl (Sum.inr S) : D.Box) = D.byy S from rfl, cost_by j D _ h0,
        hz _ hM2, hz _ (by omega)]; simp
    · rw [show (Sum.inr (Sum.inl c) : D.Box) = D.bc c from rfl, cost_bc j D _ h0,
        hz _ hM3, hz _ hM5, hz _ hM4]; simp
    · rw [show (Sum.inr (Sum.inr (Sum.inl σ)) : D.Box) = D.bs σ from rfl, cost_bs j D _ h0 hh,
        hz _ hM3, hz 1 (by omega), hz _ (by omega), hz _ hM4]; simp
    · rw [show (Sum.inr (Sum.inr (Sum.inr (Sum.inl r))) : D.Box) = D.ba r from rfl,
        cost_ba j D _ h0, hz _ hM3, hz 1 (by omega), hz _ hM4]; simp [hmid]
    · rw [show (Sum.inr (Sum.inr (Sum.inr (Sum.inr r))) : D.Box) = D.bb r from rfl,
        cost_bb j D _ h0, hz _ hM3, hz 1 (by omega), hz _ hM4]; simp [hmid]
  have hle : ind M c ≤ Phi (ind M) (Einv j D) :=
    Multiset.single_le_sum (fun x hx => by
      obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hx; unfold ind; split_ifs <;> norm_num) _
      (Multiset.mem_map_of_mem _ hc)
  rw [hall] at hle
  have : ind M c = 1 := by simp [ind, hcM]
  linarith

end Bound

end ICost
end PowerSaving.Colour
end OAI
