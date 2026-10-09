import OAI.Computability.FourierTransform.Colour.Tensor

/-!
# Colour network, part 7: labels on the dependent product (new)

OpenAI's masks (`NetworkRoles`: `sets`, `rect`, `big`, `belt`, `xstep`, `ystep`) generalised to a
dependent product `∀ i : Fin 3, H i` (unequal factor sizes), plus the uniform label family of the
colour network

  `lam j I = Λ_I = (B ⊗ D_j ⊥ P ⊗ span(I)) ⊗ Q`   (in index form, w.r.t. a product basis whose past and
  future factors carry `P`, `Q` at index `0`).

`Bot = lam j ∅` (OpenAI's `belt`), `Top = lam j univ` (`big`), `Xb = lam j {slot}` (`xstep`),
`Yt = lam j (univ \ {slot})` (`ystep`). Main facts: membership, monotonicity, the residual
`lam j I' \ lam j I = rect j false (I' \ I)`, and projection congruence (`lam_proj`), which reduces
every gate synchronisation to a factor-level identity.
-/

namespace OAI
namespace PowerSaving.Colour
open Finset Matrix Binary

variable {H : Fin 3 → Type*} [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)] [∀ i, Zero (H i)]

/-- Factor sets of a rectangle: past free (`e = true`) or at `0`; `s` at `j`; future at `0`. -/
def sets (j : Fin 3) (e : Bool) (s : Finset (H j)) : ∀ i, Finset (H i) :=
  Function.update (fun i => if i < j ∧ e = true then univ else {0}) j s

def rect (j : Fin 3) (e : Bool) (s : Finset (H j)) : Finset (∀ i, H i) :=
  Fintype.piFinset (sets j e s)

def future (j : Fin 3) (x : ∀ i, H i) : Prop := ∀ i, j < i → x i = 0
def previous (j : Fin 3) (x : ∀ i, H i) : Prop := ∀ i, i < j → x i = 0

lemma sets_self (j : Fin 3) (e : Bool) (s : Finset (H j)) : sets j e s j = s := by
  simp [sets]

lemma sets_ne (j : Fin 3) (e : Bool) (s : Finset (H j)) (i : Fin 3) (hi : i ≠ j) :
    sets j e s i = if i < j ∧ e = true then univ else {0} := by
  simp [sets, Function.update_of_ne hi]

lemma mem_rect (j : Fin 3) (e : Bool) (s : Finset (H j)) (x : ∀ i, H i) :
    x ∈ rect j e s ↔ future j x ∧ (e = false → previous j x) ∧ x j ∈ s := by
  rw [rect, Fintype.mem_piFinset]
  constructor
  · intro hx
    refine ⟨fun i hi => ?_, fun he i hi => ?_, by simpa [sets_self] using hx j⟩
    · have := hx i
      rw [sets_ne j e s i (ne_of_gt hi)] at this
      simpa [not_lt.mpr hi.le] using this
    · have := hx i
      rw [sets_ne j e s i (ne_of_lt hi)] at this
      simpa [he] using this
  · rintro ⟨hf, hp, hs⟩ i
    rcases lt_trichotomy i j with hi | rfl | hi
    · rw [sets_ne j e s i (ne_of_lt hi)]
      cases e
      · simp [hp rfl i hi]
      · simp [hi]
    · simpa [sets_self] using hs
    · rw [sets_ne j e s i (ne_of_gt hi)]
      simp [not_lt.mpr hi.le, hf i hi]

/-- `E ⊗ D_j ⊗ Q` (OpenAI's `big`). -/
def big (j : Fin 3) : Finset (∀ i, H i) := rect j true univ

/-- The uniform label family `Λ_I`. -/
def lam (j : Fin 3) (I : Finset (H j)) : Finset (∀ i, H i) := big j \ rect j false (univ \ I)

theorem in_big (j : Fin 3) (x : ∀ i, H i) : x ∈ big j ↔ future j x := by
  simp [big, mem_rect]

theorem mem_lam (j : Fin 3) (I : Finset (H j)) (x : ∀ i, H i) :
    x ∈ lam j I ↔ future j x ∧ (¬ previous j x ∨ x j ∈ I) := by
  simp only [lam, mem_sdiff, in_big, mem_rect, mem_univ, true_and, eq_self_iff_true, true_implies]
  tauto

lemma rect_le_big (j : Fin 3) (e : Bool) (s : Finset (H j)) : rect j e s ⊆ big j :=
  fun x hx => (in_big j x).2 ((mem_rect j e s x).1 hx).1

lemma lam_le_big (j : Fin 3) (I : Finset (H j)) : lam j I ⊆ big j := sdiff_subset

theorem lam_univ (j : Fin 3) : lam j (univ : Finset (H j)) = big j := by
  ext x; rw [mem_lam, in_big]; simp

theorem lam_mono (j : Fin 3) {I I' : Finset (H j)} (h : I ⊆ I') : lam j I ⊆ lam j I' := by
  intro x hx
  rw [mem_lam] at hx ⊢
  rcases hx with ⟨hf, hp | hi⟩
  · exact ⟨hf, Or.inl hp⟩
  · exact ⟨hf, Or.inr (h hi)⟩

/-- The residual of a `lam`-edge is `P ⊗ span(I' \ I) ⊗ Q`. -/
theorem lam_sdiff (j : Fin 3) {I I' : Finset (H j)} (h : I ⊆ I') :
    lam j I' \ lam j I = rect j false (I' \ I) := by
  ext x
  have hx := @h (x j)
  simp only [mem_sdiff, mem_lam, mem_rect, eq_self_iff_true, true_implies]
  tauto

/-- Rectangle projections for product bases that agree off `j`. -/
lemma rect_proj {b d : ∀ i, OBase (H i)} {j : Fin 3} {s t : Finset (H j)}
    (hi : ∀ i, i ≠ j → b i = d i) (hh : (b j).mat s = (d j).mat t) (e : Bool) :
    (dtensor b).mat (rect j e s) = (dtensor d).mat (rect j e t) := by
  unfold rect
  apply drect_congr
  intro i
  by_cases h : i = j
  · subst h; simpa [sets_self] using hh
  · rw [sets_ne j e s i h, sets_ne j e t i h, hi i h]

/-- Projection congruence for the labels `lam`: only the factor `j` matters. -/
theorem lam_proj {b d : ∀ i, OBase (H i)} {j : Fin 3} {I I' : Finset (H j)}
    (hi : ∀ i, i ≠ j → b i = d i) (hh : (b j).mat I = (d j).mat I') :
    (dtensor b).mat (lam j I) = (dtensor d).mat (lam j I') := by
  unfold lam
  rw [OBase.mat_sub _ _ _ (rect_le_big ..), OBase.mat_sub _ _ _ (rect_le_big ..)]
  have hbig : (dtensor b).mat (big j) = (dtensor d).mat (big j) :=
    rect_proj hi (by rw [OBase.mat_univ, OBase.mat_univ]) true
  rw [hbig, rect_proj hi (mat_compl_congr _ _ _ _ hh) false]

/-- Product bases differing only at factor `j`. -/
lemma update_same (j : Fin 3) (F : ∀ i, OBase (H i)) (u v : OBase (H j)) :
    ∀ i, i ≠ j → Function.update F j u i = Function.update F j v i := by
  intro i hi; simp [Function.update_of_ne hi]

/-- The form used for gate synchronisation in an invocation. -/
theorem lam_sync (j : Fin 3) (F : ∀ i, OBase (H i)) (Z Z' : OBase (H j)) {I I' : Finset (H j)}
    (hh : Z.mat I = Z'.mat I') :
    (dtensor (Function.update F j Z)).mat (lam j I)
      = (dtensor (Function.update F j Z')).mat (lam j I') :=
  lam_proj (update_same j F Z Z') (by simpa using hh)

/-- Labels not involving factor `j` (Bot, Top) do not depend on the factor basis. -/
theorem lam_sync_any (j : Fin 3) (F : ∀ i, OBase (H i)) (Z Z' : OBase (H j)) :
    (dtensor (Function.update F j Z)).mat (lam j ∅)
      = (dtensor (Function.update F j Z')).mat (lam j ∅) ∧
    (dtensor (Function.update F j Z)).mat (lam j univ)
      = (dtensor (Function.update F j Z')).mat (lam j univ) := by
  constructor
  · apply lam_sync; ext i k; simp [OBase.mat]
  · apply lam_sync; rw [OBase.mat_univ, OBase.mat_univ]

end PowerSaving.Colour
end OAI
