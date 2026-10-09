import OAI.Computability.FourierTransform.Colour.Triples

/-!
# Colour network, part 4: bases of coordinate registers (Lemmas C.7 / C.9) (new)

A coordinate register of owner `T` uses `coordBase T d = adapt canonical d t_T` with a pivot `d ∉ T`:
`v_d = t_T`, `v_k = e_k + t_T + e_d` for `k ∈ T`, and `v_k = e_k` otherwise.

* writer `T` at a coordinate label `F^A` (`T ⊆ A`, pivot `d ∈ A`): index set `A`, Xb at `{d}`;
* reader `S` with a chain `F^{A₁} ⊂ ⋯ ⊂ F^{A_k}` (`S ∩ A_k = ∅`, pivot `d ∉ A_k`): index sets `A_i`,
  Yt at `univ \ {d}`.

In both cases the projection of the index set `A` is the coordinate projection
(`mat_coord_of_sub`, `mat_coord_of_disj`), so all registers meeting at `F^A` are synchronised.
-/

namespace OAI
namespace PowerSaving.Colour
open Finset Matrix Binary

variable {h : ℕ}

/-- Basis of a coordinate register with owner `T` and pivot `d`. -/
def coordBase (T : Trip h) (d : Fin h) : OBase (Fin h) :=
  if hd : tip T d = 0 then
    OBase.adapt (OBase.canonical (Fin h)) d (tip T) (tip_unit T)
      (by change dot (tip T) (eu d) = 0; rw [dot_eu_right]; exact hd)
  else OBase.canonical _

lemma tip_of_not_mem {T : Trip h} {d : Fin h} (hd : d ∉ T.val) : tip T d = 0 := by
  simp [tip_apply, hd]

lemma coordBase_slot (T : Trip h) {d : Fin h} (hd : d ∉ T.val) : (coordBase T d).v d = tip T := by
  unfold coordBase; rw [dif_pos (tip_of_not_mem hd)]; apply OBase.adapt_pivot

/-- Explicit entries. -/
lemma coordBase_apply (T : Trip h) {d : Fin h} (hd : d ∉ T.val) (k i : Fin h) :
    (coordBase T d).v k i = eu k i + (tip T k + eu d k) * (tip T i + eu d i) := by
  unfold coordBase; rw [dif_pos (tip_of_not_mem hd)]
  simp only [OBase.adapt, OBase.acted, OBase.tv, OBase.canonical, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, dot_eu_right]

lemma coordBase_other (T : Trip h) {d : Fin h} (hd : d ∉ T.val) (k : Fin h) (hk : k ∉ T.val)
    (hkd : k ≠ d) : (coordBase T d).v k = eu k := by
  funext i
  rw [coordBase_apply T hd]
  simp [tip_apply, hk, eu, Ne.symm hkd]

lemma coordBase_supp (T : Trip h) {d : Fin h} (hd : d ∉ T.val) (k i : Fin h)
    (hne : (coordBase T d).v k i ≠ 0) : i = k ∨ i ∈ T.val ∨ i = d := by
  rw [coordBase_apply T hd] at hne
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2, h3⟩ := hc
  apply hne
  simp [eu, tip_apply, h2, Ne.symm h1, Ne.symm h3]

/-- Writer side (C.7): owner and pivot inside the label. -/
theorem mat_coord_of_sub (T : Trip h) {d : Fin h} (hd : d ∉ T.val) (A : Finset (Fin h))
    (hT : T.val ⊆ A) (hdA : d ∈ A) :
    (coordBase T d).mat A = (OBase.canonical (Fin h)).mat A := by
  apply mat_eq_canonical
  · intro k hk i hi
    by_contra hne
    rcases coordBase_supp T hd k i hne with e | e | e
    · exact hi (e ▸ hk)
    · exact hi (hT e)
    · exact hi (e ▸ hdA)
  · intro k hk i hi
    have hkT : k ∉ T.val := fun g => hk (hT g)
    have hkd : k ≠ d := fun g => hk (g ▸ hdA)
    rw [coordBase_other T hd k hkT hkd]
    simp [eu]; intro e; exact hk (e ▸ hi)

/-- Reader side (C.9): owner and pivot outside the label. -/
theorem mat_coord_of_disj (T : Trip h) {d : Fin h} (hd : d ∉ T.val) (A : Finset (Fin h))
    (hT : Disjoint T.val A) (hdA : d ∉ A) :
    (coordBase T d).mat A = (OBase.canonical (Fin h)).mat A := by
  apply mat_eq_canonical
  · intro k hk i hi
    have hkT : k ∉ T.val := fun g => disjoint_left.mp hT g hk
    have hkd : k ≠ d := fun g => hdA (g ▸ hk)
    rw [coordBase_other T hd k hkT hkd]
    simp [eu]; intro e; exact hi (e ▸ hk)
  · intro k hk i hi
    by_contra hne
    rcases coordBase_supp T hd k i hne with e | e | e
    · exact hk (e ▸ hi)
    · exact disjoint_left.mp hT e hi
    · exact hdA (e ▸ hi)

/-- Any two registers meeting at the coordinate label `A` have the same projection there. -/
theorem coord_sync (T S : Trip h) {d d' : Fin h} (hd : d ∉ T.val) (hd' : d' ∉ S.val)
    (A : Finset (Fin h)) (hT : T.val ⊆ A) (hdA : d ∈ A) (hS : Disjoint S.val A) (hd'A : d' ∉ A) :
    (coordBase T d).mat A = (coordBase S d').mat A := by
  rw [mat_coord_of_sub T hd A hT hdA, mat_coord_of_disj S hd' A hS hd'A]

end PowerSaving.Colour
end OAI
