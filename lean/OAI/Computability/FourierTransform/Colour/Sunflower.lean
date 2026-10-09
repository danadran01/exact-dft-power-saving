import OAI.Computability.FourierTransform.Colour.Triples

/-!
# Colour network, part 5: sunflower labels and their bases (Lemma C.6) (new)

Fix an axis `a ≠ b` and `g_x = e_a + e_b + e_x`. For `U ⊆ [h] ∖ {a,b}` of **even** size,
`sunBase a b U` is the orthonormal basis indexed by `Fin h` itself:

* `v x = g_x` for `x ∈ U`, `v y = e_y` for `y ∉ U ∪ {a,b}`,
* `v a = e_a + 1_U`, `v b = e_b + 1_U`.

So the sunflower label `M(P) = span{g_x : x ∈ P}` (`P ⊆ U`) is the index set `P` of every such basis,
with the same vectors: all sunflower registers of an axis are synchronised (`sun_mat_congr`).
Odd sizes are absorbed by adding one more `y₀ ∉ U ∪ {a,b}` (the paper's absorption step); the
alternating case of C.6(d) is exactly when no such `y₀` exists.
-/

namespace OAI
namespace PowerSaving.Colour
open Finset Matrix Binary

variable {h : ℕ}

/-- The sunflower vector `e_a + e_b + e_x`. -/
def gvec (a b x : Fin h) : Space (Fin h) := eu a + eu b + eu x

/-- Hypotheses on the axis and the even set `U`. -/
structure SunOK (a b : Fin h) (U : Finset (Fin h)) : Prop where
  hab : a ≠ b
  ha : a ∉ U
  hb : b ∉ U
  heven : (U.card : F) = 0

/-- The vectors of the sunflower basis. -/
def sunv (a b : Fin h) (U : Finset (Fin h)) (i : Fin h) : Space (Fin h) :=
  if i = a then eu a + ind U else if i = b then eu b + ind U else if i ∈ U then gvec a b i else eu i

section Rows
variable {a b : Fin h} {U : Finset (Fin h)}

lemma eu_apply' (i j : Fin h) : eu i j = if i = j then 1 else 0 := rfl

lemma dot_ind_eu (U : Finset (Fin h)) (j : Fin h) : dot (ind U) (eu j) = if j ∈ U then 1 else 0 := by
  rw [dot_eu_right]; rfl

lemma dot_eu_ind (U : Finset (Fin h)) (j : Fin h) : dot (eu j) (ind U) = if j ∈ U then 1 else 0 := by
  rw [dot_eu_left]; rfl

variable (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U) (hUU : dot (ind U) (ind U) = 0)
include hab ha hb hUU

omit hab hb in
lemma d_aa : dot (eu a + ind U) (eu a + ind U) = 1 := by
  simp only [dot_add_left, dot_add_right, dot_eu_eu, dot_ind_eu, dot_eu_ind, hUU]
  simp [ha]

lemma d_ab : dot (eu a + ind U) (eu b + ind U) = 0 := by
  simp only [dot_add_left, dot_add_right, dot_eu_eu, dot_ind_eu, dot_eu_ind, hUU]
  simp [ha, hb, hab]

omit hUU in
lemma d_ag {x : Fin h} (hx : x ∈ U) : dot (eu a + ind U) (gvec a b x) = 0 := by
  have hxa : a ≠ x := fun e => ha (e ▸ hx)
  simp only [gvec, dot_add_left, dot_add_right, dot_eu_eu, dot_ind_eu, dot_eu_ind]
  simp [ha, hb, hab, hxa, hx]

omit hab ha hb hUU in
lemma d_ae {y : Fin h} (hya : y ≠ a) (hy : y ∉ U) : dot (eu a + ind U) (eu y) = 0 := by
  simp only [dot_add_left, dot_eu_eu, dot_ind_eu]
  simp [Ne.symm hya, hy]

omit hab ha hb hUU in
lemma d_ge {x y : Fin h} (h1 : y ≠ a) (h2 : y ≠ b) (h3 : y ≠ x) : dot (gvec a b x) (eu y) = 0 := by
  simp only [gvec, dot_add_left, dot_eu_eu]
  simp [Ne.symm h1, Ne.symm h2, Ne.symm h3]

omit ha hb hUU in
lemma d_gg {x y : Fin h} (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    dot (gvec a b x) (gvec a b y) = if x = y then 1 else 0 := by
  simp only [gvec, dot_add_left, dot_add_right, dot_eu_eu]
  by_cases e : x = y
  · subst e
    simp [hab, Ne.symm hab, hxa, hxb, Ne.symm hxa, Ne.symm hxb]
    try decide
  · simp [hab, Ne.symm hab, Ne.symm hya, Ne.symm hyb, hxa, hxb, e]

end Rows

section Rows2
variable {a b : Fin h} {U : Finset (Fin h)}

theorem sunv_rows (hs : SunOK a b U) (i j : Fin h) :
    dot (sunv a b U i) (sunv a b U j) = if i = j then 1 else 0 := by
  obtain ⟨hab, ha, hb, hev⟩ := hs
  have hUU : dot (ind U) (ind U) = 0 := by rw [dot_ind_self, hev]
  have hba : b ≠ a := Ne.symm hab
  -- the four kinds of indices and their vectors
  have cls : ∀ x : Fin h, (x = a ∧ sunv a b U x = eu a + ind U) ∨
      (x = b ∧ sunv a b U x = eu b + ind U) ∨
      (x ≠ a ∧ x ≠ b ∧ x ∈ U ∧ sunv a b U x = gvec a b x) ∨
      (x ≠ a ∧ x ≠ b ∧ x ∉ U ∧ sunv a b U x = eu x) := by
    intro x
    by_cases h1 : x = a
    · subst h1; exact Or.inl ⟨rfl, by simp [sunv]⟩
    by_cases h2 : x = b
    · subst h2; exact Or.inr (Or.inl ⟨rfl, by simp [sunv, h1]⟩)
    by_cases h3 : x ∈ U
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, by simp [sunv, h1, h2, h3]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, by simp [sunv, h1, h2, h3]⟩))
  have dAA := d_aa (a := a) ha hUU
  have dBB := d_aa (a := b) hb hUU
  have dAB := d_ab hab ha hb hUU
  have dBA := d_ab hba hb ha hUU
  rcases cls i with ⟨i1, ei⟩ | ⟨i1, ei⟩ | ⟨i1, i2, i3, ei⟩ | ⟨i1, i2, i3, ei⟩ <;>
  rcases cls j with ⟨j1, ej⟩ | ⟨j1, ej⟩ | ⟨j1, j2, j3, ej⟩ | ⟨j1, j2, j3, ej⟩ <;>
  rw [ei, ej]
  -- i = a
  · rw [if_pos (i1.trans j1.symm)]; exact dAA
  · rw [if_neg (by rw [i1, j1]; exact hab)]; exact dAB
  · rw [if_neg (by rw [i1]; exact Ne.symm j1)]; exact d_ag hab ha hb j3
  · rw [if_neg (by rw [i1]; exact Ne.symm j1)]; exact d_ae (U := U) (a := a) j1 j3
  -- i = b
  · rw [if_neg (by rw [i1, j1]; exact hba)]; exact dBA
  · rw [if_pos (i1.trans j1.symm)]; exact dBB
  · rw [if_neg (by rw [i1]; exact Ne.symm j2)]
    have := d_ag (a := b) (b := a) hba hb ha j3
    rwa [show gvec b a j = gvec a b j by unfold gvec; abel] at this
  · rw [if_neg (by rw [i1]; exact Ne.symm j2)]; exact d_ae (U := U) (a := b) j2 j3
  -- i ∈ U
  · rw [if_neg (by rw [j1]; exact i1), dot_symm]; exact d_ag hab ha hb i3
  · rw [if_neg (by rw [j1]; exact i2), dot_symm]
    have := d_ag (a := b) (b := a) hba hb ha i3
    rwa [show gvec b a i = gvec a b i by unfold gvec; abel] at this
  · exact d_gg hab i1 i2 j1 j2
  · rw [if_neg (fun e : i = j => j3 (e ▸ i3))]
    exact d_ge j1 j2 (fun e : j = i => j3 (e ▸ i3))
  -- other
  · rw [if_neg (by rw [j1]; exact i1), dot_symm]; exact d_ae (U := U) (a := a) i1 i3
  · rw [if_neg (by rw [j1]; exact i2), dot_symm]; exact d_ae (U := U) (a := b) i2 i3
  · rw [if_neg (fun e : i = j => i3 (e ▸ j3)), dot_symm]
    exact d_ge i1 i2 (fun e : i = j => i3 (e ▸ j3))
  · exact dot_eu_eu i j



end Rows2

/-- The sunflower basis (canonical basis if the hypotheses fail). -/
noncomputable def sunBase (a b : Fin h) (U : Finset (Fin h)) : OBase (Fin h) :=
  haveI := Classical.propDecidable (SunOK a b U)
  if hs : SunOK a b U then ⟨sunv a b U, sunv_rows hs⟩ else OBase.canonical _

lemma sunBase_v (a b : Fin h) (U : Finset (Fin h)) (hs : SunOK a b U) (i : Fin h) :
    (sunBase a b U).v i = sunv a b U i := by
  unfold sunBase; rw [dif_pos hs]

/-- The index `x ∈ U` carries `g_x`. -/
theorem sunBase_g (a b : Fin h) (U : Finset (Fin h)) (hs : SunOK a b U) {x : Fin h} (hx : x ∈ U) :
    (sunBase a b U).v x = gvec a b x := by
  rw [sunBase_v a b U hs]
  have hxa : x ≠ a := fun e => hs.ha (e ▸ hx)
  have hxb : x ≠ b := fun e => hs.hb (e ▸ hx)
  simp [sunv, hxa, hxb, hx]

/-- (C.6a) the sunflower vectors are orthonormal. -/
theorem gvec_dot (a b x y : Fin h) (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a)
    (hyb : y ≠ b) : dot (gvec a b x) (gvec a b y) = if x = y then 1 else 0 :=
  d_gg hab hxa hxb hya hyb

/-- (C.6b) the indicator of the triple `{a, b, x}` is `g_x`. -/
theorem tip_eq_gvec (T : Trip h) (a b x : Fin h) (hT : T.val = {a, b, x}) (hab : a ≠ b)
    (hxa : x ≠ a) (hxb : x ≠ b) : tip T = gvec a b x := by
  unfold tip gvec
  rw [hT, ind_insert a _ (by simp [hab, Ne.symm hxa]), ind_insert b _ (by simp [Ne.symm hxb]),
    ind_singleton, add_assoc]

/-- (C.6) synchronisation: sunflower labels `M(P)` agree in all sunflower bases of the axis. -/
theorem sun_mat_congr (a b : Fin h) (U U' P : Finset (Fin h)) (hs : SunOK a b U) (hs' : SunOK a b U')
    (hP : P ⊆ U) (hP' : P ⊆ U') : (sunBase a b U).mat P = (sunBase a b U').mat P := by
  apply mat_congr_family
  intro x hx
  rw [sunBase_g a b U hs (hP hx), sunBase_g a b U' hs' (hP' hx)]

/-- A sunflower basis puts the owner's indicator at the owner's own index. -/
theorem sunBase_tip (a b : Fin h) (U : Finset (Fin h)) (hs : SunOK a b U) (T : Trip h) {x : Fin h}
    (hx : x ∈ U) (hT : T.val = {a, b, x}) : (sunBase a b U).v x = tip T := by
  have hxa : x ≠ a := fun e => hs.ha (e ▸ hx)
  have hxb : x ≠ b := fun e => hs.hb (e ▸ hx)
  rw [sunBase_g a b U hs hx, tip_eq_gvec T a b x hT hs.hab hxa hxb]

/-- Absorption of an odd set: add one more element of the complement. -/
theorem sunOK_insert (a b : Fin h) (U : Finset (Fin h)) (y : Fin h) (hab : a ≠ b) (ha : a ∉ U)
    (hb : b ∉ U) (hya : y ≠ a) (hyb : y ≠ b) (hy : y ∉ U) (hodd : (U.card : F) = 1) :
    SunOK a b (insert y U) where
  hab := hab
  ha := by simp [Ne.symm hya, ha]
  hb := by simp [Ne.symm hyb, hb]
  heven := by rw [card_insert_of_notMem hy]; push_cast; rw [hodd]; decide

end PowerSaving.Colour
end OAI
