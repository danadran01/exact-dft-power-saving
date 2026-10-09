import OAI.Computability.FourierTransform.Grouped.GFrames

/-!
# Grouped words and grouped paths (new; not part of OpenAI's development)

`GMove.batch r A R τ` changes role `r` by the whole batch `shift τ * bdir A R`.
`GPath A s t g E` is OpenAI's `Path` with the list `E` of batch sizes in place of the count of
directional steps. The grouped recursion charges one recursive call of size `|R|·f` per batch.
-/

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α]

inductive GMove (α ρ : Type*) [Fintype α] [DecidableEq α]
  | localM (g : Matrix ρ ρ ℚ)
  | batch (r : ρ) (A : OBase α) (R : Finset α) (τ : Space α)
  | shift (r : ρ) (z : Space α)

abbrev GWord (α ρ : Type*) [Fintype α] [DecidableEq α] := List (GMove α ρ)

def GMove.size : GMove α ρ → List ℕ
  | .batch _ _ R _ => [R.card]
  | _ => []

def sizes (p : GWord α ρ) : List ℕ := p.flatMap GMove.size

@[simp] lemma sizes_nil : sizes ([] : GWord α ρ) = [] := rfl
lemma sizes_append (p q : GWord α ρ) : sizes (p ++ q) = sizes p ++ sizes q := by
  simp [sizes, List.flatMap_append]

variable [Fintype ρ] [DecidableEq ρ]

def GMove.go (f : ℕ) : GMove α ρ → Data α ρ f → Data α ρ f
  | .localM g => point f (actPoint g)
  | .batch r A R τ => roleAct f r (Binary.shift τ * bdir A R)
  | .shift r z => roleAct f r (Binary.shift z)

def gwalk (f : ℕ) (p : GWord α ρ) (x : Data α ρ f) : Data α ρ f :=
  p.foldl (fun y s => s.go f y) x

lemma gwalk_append (f : ℕ) (p q : GWord α ρ) (x : Data α ρ f) :
    gwalk f (p ++ q) x = gwalk f q (gwalk f p x) := by simp [gwalk]

/-- Grouped path: frame change from `s` to `t` with point map `g`, using batches of sizes `E`. -/
def GPath (A : ρ → OBase α) (s t : ρ → Finset α) (g : (ρ → ℂ) → (ρ → ℂ)) (E : List ℕ) : Prop :=
  ∃ p : GWord α ρ, sizes p = E ∧
    ∀ (f : ℕ) (x : Data α ρ f), gwalk f p (withFrame A s f x) = withFrame A t f (point f g x)

lemma shift_add (a b : Space α) : Binary.shift a * Binary.shift b = Binary.shift (a + b) := by
  rw [shift_phase, shift_phase, shift_phase, wrap_mul]
  congr 1; funext x
  rw [← sign_add]
  congr 1
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

namespace GPath
variable {A : ρ → OBase α} {s t u : ρ → Finset α}

theorem refl : GPath A s s id [] := ⟨[], rfl, fun _ _ => rfl⟩

theorem trans {g h E F} (a : GPath A s t g E) (b : GPath A t u h F) :
    GPath A s u (h ∘ g) (E ++ F) := by
  obtain ⟨p, hp, ap⟩ := a
  obtain ⟨q, hq, aq⟩ := b
  refine ⟨p ++ q, by rw [sizes_append, hp, hq], ?_⟩
  intro f x
  rw [gwalk_append, ap, aq]; rfl

/-- Move through a gate (OpenAI's `Path.gate`, grouped version). -/
theorem gate (g : Matrix ρ ρ ℚ)
    (cond : ∀ i j, g i j ≠ 0 → frame (A i) (s i) = frame (A j) (s j)) :
    GPath A s s (actPoint g) [] := by
  refine ⟨[.localM g], rfl, ?_⟩
  intro f x
  let M (r : ρ) := digitProd (fun _ : Fin f => frame (A r) (s r))
  funext r i
  change ∑ j, (g r j:ℂ)* (∑ a, M j i a * x j a)
    = ∑ a, M r i a * (∑ j, (g r j:ℂ)*x j a)
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro j hj
  by_cases gh : g r j = 0
  · simp [gh]
  · dsimp only [M]
    have eq := cond r j gh
    rw [eq]
    ac_rfl

lemma point_id (f : ℕ) (x : Data α ρ f) : point f id x = x := rfl

lemma roleAct_withFrame (f : ℕ) (r : ρ) (M : CMat α) (N : Finset α)
    (hM : M * frame (A r) (s r) = frame (A r) N) (x : Data α ρ f) :
    roleAct f r M (withFrame A s f x) = withFrame A (Function.update s r N) f x := by
  funext j
  by_cases hj : j = r
  · subst j
    simp [roleAct, withFrame, multiAct, matAct_mul, hM, Function.update_self]
  · simp [roleAct, hj, withFrame, multiAct, Function.update_of_ne hj]

/-- ONE batch adds the lines `R` to role `r`'s frame (an increasing edge). -/
theorem role_up (r : ρ) (R : Finset α) (h : Disjoint R (s r)) :
    GPath A s (Function.update s r (R ∪ s r)) id [R.card] := by
  refine ⟨[.batch r (A r) R (∑ i ∈ negLines (A r) R, (A r).v i)], rfl, ?_⟩
  intro f x
  rw [point_id]
  change roleAct f r _ (withFrame A s f x) = _
  apply roleAct_withFrame
  rw [frame_union _ R _ h, bdelta_eq]

/-- ONE batch removes the lines `R ⊆ s r` from role `r`'s frame (a decreasing edge). -/
theorem role_down (r : ρ) (R : Finset α) (hR : R ⊆ s r) :
    GPath A s (Function.update s r (s r \ R)) id [R.card] := by
  refine ⟨[.batch r (A r) R ((∑ i ∈ R, (A r).v i) + ∑ i ∈ negLines (A r) R, (A r).v i)], rfl, ?_⟩
  intro f x
  rw [point_id]
  change roleAct f r _ (withFrame A s f x) = _
  apply roleAct_withFrame
  have hd : Disjoint R (s r \ R) := Finset.disjoint_sdiff
  have hu : R ∪ (s r \ R) = s r := Finset.union_sdiff_of_subset hR
  have := frame_remove (A r) R (s r \ R) hd
  rw [hu, bdelta_eq, ← Matrix.mul_assoc, shift_add] at this
  exact this.symm

end GPath
end
end
end PowerSaving.Binary
end OAI
