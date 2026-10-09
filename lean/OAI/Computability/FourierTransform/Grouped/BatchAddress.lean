import OAI.Computability.FourierTransform.Grouped.GFrames
import OAI.Computability.FourierTransform.ColumnAddresses

/-!
# Batch addresses (new; not part of OpenAI's development)

A batch `bdir A S = ∏_{i∈S} dir (A.v i)` of `c = |S|` basis lines is, in the coordinates
`x ↦ (A.v i · x)_i` of the orthonormal basis `A`, the identity on the lines outside `S` tensored
with `kernel` on the `c` lines of `S` (`bdir_peel`). Per digit column the fibres are
`Sky (Fin c) f ≅ Bits (c*f)` (`bserial`), so `matAct f (bdir A S)` is `ripple (c*f)` on fibres
(`act_bdir`, `bbook_act`; generalizing OpenAI's `act_dir`, `peel_act`).

The address change is constant work for fixed `α`: every new coordinate column is an XOR-fold of
old coordinate columns (`Gear.addr_comb`), see `Gear.from_basis`/`Gear.to_basis`
(generalizing OpenAI's `from_grid`/`to_grid`).
-/

namespace OAI
namespace PowerSaving.Binary
open Finset Matrix
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Lines outside the batch. -/
abbrev Out (S : Finset α) := {i : α // i ∉ S}

/-- Coefficients on all lines from coefficients outside the batch and on the batch. -/
def glue (S : Finset α) (q : Space (Out S) × Space (Fin S.card)) : Space α :=
  fun j => if h : j ∈ S then q.2 (S.equivFin ⟨j,h⟩) else q.1 ⟨j,h⟩

lemma basis_sum (A : OBase α) (x : Space α) : ∑ j, dot (A.v j) x • A.v j = x := by
  simpa [OBase.proj] using A.proj_univ x

lemma dot_basis_sum (A : OBase α) (c : Space α) (i : α) :
    dot (A.v i) (∑ j, c j • A.v j) = c i := by
  rw [dot_sum]; simp [A.rows]

/-- Coordinates in the basis `A`: lines outside `S`, then the lines of `S`. -/
def bsplit (A : OBase α) (S : Finset α) :
    Space α ≃ₗ[F] Space (Out S) × Space (Fin S.card) where
  toFun x := (fun i => dot (A.v i) x, fun k => dot (A.v (S.equivFin.symm k)) x)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  invFun q := ∑ j, glue S q j • A.v j
  left_inv x := by
    have h (j : α) : glue S (fun i => dot (A.v i) x, fun k => dot (A.v (S.equivFin.symm k)) x) j
        = dot (A.v j) x := by
      unfold glue; split <;> simp
    simp only [h]; exact basis_sum A x
  right_inv q := by
    ext i
    · show dot (A.v i) (∑ j, glue S q j • A.v j) = q.1 i
      rw [dot_basis_sum]; simp [glue, i.2]
    · show dot (A.v (S.equivFin.symm i)) (∑ j, glue S q j • A.v j) = q.2 i
      rw [dot_basis_sum]; simp [glue]

lemma bsplit_symm_apply (A : OBase α) (S : Finset α) (q : Space (Out S) × Space (Fin S.card)) :
    (bsplit A S).symm q = ∑ j, glue S q j • A.v j := rfl

lemma bsplit_line (A : OBase α) (S : Finset α) (k : Fin S.card) :
    bsplit A S (A.v (S.equivFin.symm k)) = (0, Pi.single k 1) := by
  ext i
  · have : (i:α) ≠ S.equivFin.symm k := fun h => i.2 (h ▸ (S.equivFin.symm k).2)
    simp [bsplit, A.rows, this]
  · simp [bsplit, A.rows, Pi.single_apply]

/-- **Batch = kernel on the batch coordinates** (in the basis `A`). -/
theorem bdir_peel (A : OBase α) (S : Finset α) (x y : Space α) :
    bdir A S x y = if (bsplit A S x).1 = (bsplit A S y).1 then
      kernel (Fin S.card) (bsplit A S x).2 (bsplit A S y).2 else 0 := by
  rw [bdir_eq_batchMat]
  exact batchMat_peel _ _ (bsplit A S) (bsplit_line A S) x y

/-- Serial order of the batch coordinates of all `f` digit columns. -/
def bserial (c f : ℕ) : Sky (Fin c) f ≃ Bits (c*f) :=
  (Equiv.uniqueProd (Sky (Fin c) f) (Bits 0)).symm.trans
    (serial (Layout.std c) 0 f (k:=c*f) (show (Layout.std c).n*f+0 = c*f from rfl))

lemma bserial_code (c f : ℕ) (y : Sky (Fin c) f) :
    (bits (c*f)).loc (bserial c f y) = (bodyOrder (Layout.std c) f).loc y := by
  rw [bserial, Equiv.trans_apply, serial_code]
  simp [book, bits_loc]

lemma kernel_bserial (c f : ℕ) (y y' : Sky (Fin c) f) :
    kernel (Fin (c*f)) (bserial c f y) (bserial c f y') =
      digitProd (fun _ : Fin f => kernel (Fin c)) y y' := by
  rw [bserial, Equiv.trans_apply, Equiv.trans_apply, kernel_serial]
  simp [kernel]

/-- Per column: (lines outside `S`), and the serialized batch coordinates. -/
def bSkySplit (A : OBase α) (S : Finset α) (f : ℕ) :
    Sky α f ≃ Sky (Out S) f × Bits (S.card*f) where
  toFun x := (fun k => (bsplit A S (x k)).1, bserial S.card f (fun k => (bsplit A S (x k)).2))
  invFun q k := (bsplit A S).symm (q.1 k, (bserial S.card f).symm q.2 k)
  left_inv x := by funext k; simp
  right_inv q := by
    apply Prod.ext
    · funext k; simp
    · simp

def bBook (A : OBase α) (S : Finset α) (r f : ℕ) :
    Grid α r f ≃ Grid (Out S) r f × Bits (S.card*f) where
  toFun x := ((x.1,(bSkySplit A S f x.2).1),(bSkySplit A S f x.2).2)
  invFun p := (p.1.1,(bSkySplit A S f).symm (p.1.2,p.2))
  left_inv x := by simp
  right_inv p := by simp

theorem product_bdir (A : OBase α) (S : Finset α) (f : ℕ) (x y : Sky α f) :
    let e := bSkySplit A S f
    digitProd (fun _ : Fin f => bdir A S) x y =
    if (e x).1=(e y).1 then kernel (Fin (S.card*f)) (e x).2 (e y).2 else 0 := by
  intro e
  have h (a b : Space α) : bdir A S a b =
      (if (bsplit A S a).1 = (bsplit A S b).1 then (1:ℂ) else 0) *
        kernel (Fin S.card) (bsplit A S a).2 (bsplit A S b).2 := by
    rw [bdir_peel]; split <;> simp
  rw [digitProd_apply]
  simp_rw [h]
  rw [prod_mul_distrib]
  change (∏ k:Fin f, (if (e x).1 k=(e y).1 k then (1:ℂ) else 0)) *
    digitProd (fun _ : Fin f => kernel (Fin S.card)) (fun k => (bsplit A S (x k)).2)
      (fun k => (bsplit A S (y k)).2) = _
  rw [prod_delta (κ:=fun _ : Fin f => Space (Out S)), ← kernel_bserial]
  split <;> simp [e, bSkySplit]

lemma act_bdir (A : OBase α) (S : Finset α) (f : ℕ) (x : Sky α f → ℂ) (j : Sky α f) :
    let e := bSkySplit A S f
    matAct f (bdir A S) x j = ripple (S.card*f) (fun k => x (e.symm ((e j).1,k))) (e j).2 := by
  intro e
  change ∑ y, digitProd (fun _ => bdir A S) j y * x y =
    ∑ k, kernel (Fin (S.card*f)) _ k * x _
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  have h (k : Sky (Out S) f × Bits (S.card*f)) :
      digitProd (fun _ : Fin f => bdir A S) j (e.symm k) =
        if k.1=(e j).1 then kernel (Fin (S.card*f)) (e j).2 k.2 else 0 := by
    rw [product_bdir A S f]
    change (if _ = (e (e.symm k)).1 then kernel _ _ (e (e.symm k)).2 else 0)=_
    rw [e.apply_symm_apply]
    congr 1
    all_goals apply propext eq_comm
  rw [sum_eq_single (e j).1]
  · simp_rw [h]; simp
  · intro l _ hl
    apply sum_eq_zero; intro k hk
    rw [h,ite_eq_right]; simp; exact hl
  · simp

lemma bbook_act (A : OBase α) (S : Finset α) (r f : ℕ) (x : Grid α r f → ℂ) (j : Grid α r f) :
    let e := bBook A S r f
    matAct f (bdir A S) (fun k => x (j.1,k)) j.2 =
    ripple (S.card*f) (fun k => x (e.symm ((e j).1,k))) (e j).2 :=
  act_bdir A S f (fun k => x (j.1,k)) j.2

end
end PowerSaving.Binary

namespace PowerSaving.RAM
open Binary Ty Finset
noncomputable section

universe U
variable {ι : Type U}

namespace Gear
variable {m : Bool} {B f : ι → ℕ} {s : Ty} {x : ι → T s}
variable (g : Gear m B f s x)
include g

/-- XOR of a fixed set of known columns. -/
lemma addr_sum {κ : Type*} (S : Finset κ) (y : ∀ i, Fin (f i) → κ → F)
    (h : ∀ j ∈ S, Knows m B s x (fun i => (bits (f i)).loc (fun l => y i l j))) :
    Knows m B s x (fun i => (bits (f i)).loc (fun l => ∑ j ∈ S, y i l j)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine (Can.wc 0).cong (fun _ => rfl) (fun i => ?_)
    simp [bits_loc]
  | @insert j S hj ih =>
    let q i : Bits (f i) × Bits (f i) := (fun l => y i l j, fun l => ∑ j ∈ S, y i l j)
    refine (g.addr_xor q (h j (mem_insert_self _ _))
      (ih (fun j' hj' => h j' (mem_insert_of_mem hj')))).cong (fun _ => rfl) (fun i => ?_)
    apply congr_arg (bits (f i)).loc
    funext l; simp [q, sum_insert hj]

/-- A fixed `F`-linear combination of known columns. -/
lemma addr_comb {κ : Type*} [Fintype κ] (w : κ → F) (y : ∀ i, Fin (f i) → κ → F)
    (h : ∀ j, Knows m B s x (fun i => (bits (f i)).loc (fun l => y i l j))) :
    Knows m B s x (fun i => (bits (f i)).loc (fun l => ∑ j, w j * y i l j)) := by
  classical
  refine (g.addr_sum (univ.filter fun j => w j = 1) y (fun j _ => h j)).cong
    (fun _ => rfl) (fun i => ?_)
  apply congr_arg (bits (f i)).loc
  funext l
  rw [sum_filter]
  apply sum_congr rfl; intro j _
  rcases bit_cases (w j) with hw|hw <;> simp [hw]

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (X : Layout α) (r : ℕ)

/-- From grid addresses to (fibre, within-fibre) addresses of a batch. -/
lemma from_basis (A : OBase α) (S : Finset α) (X' : Layout (Out S))
    (v : ∀ i, Grid α r (f i))
    (h : Knows m B s x (fun i => (book X r (f i)).loc (v i))) :
    let u i := bBook A S r (f i) (v i)
    Knows m B s x (fun i => (book X' r (f i)).loc (u i).1) ∧
    Knows m B s x (fun i => (bits (S.card*f i)).loc (u i).2) := by
  intro u
  obtain ⟨hg, hh⟩ := g.grid_fetch X r (v:=v) h
  have ht (l : α) := g.body_get X (fun i => (v i).2) l hh
  have hd (z : Space α) := g.addr_comb z (fun i k j => (v i).2 k j) ht
  refine ⟨g.grid_combine X' r (v:=fun i => (u i).1) hg
    (g.body_set X' (fun i => (u i).1.2) (fun l => hd (A.v l))), ?_⟩
  have hb := g.body_set (Layout.std S.card) (fun i k => (bsplit A S ((v i).2 k)).2)
    (fun l => hd (A.v (S.equivFin.symm l)))
  exact hb.cong (fun _ => rfl) (fun i => (bserial_code ..).symm)

/-- From (fibre, within-fibre) addresses of a batch back to grid addresses. -/
lemma to_basis (A : OBase α) (S : Finset α) (X' : Layout (Out S))
    (u : ∀ i, Grid (Out S) r (f i) × Bits (S.card*f i))
    (h : Knows m B s x (fun i => (book X' r (f i)).loc (u i).1))
    (k : Knows m B s x (fun i => (bits (S.card*f i)).loc (u i).2)) :
    let v i := (bBook A S r (f i)).symm (u i)
    Knows m B s x (fun i => (book X r (f i)).loc (v i)) := by
  intro v
  obtain ⟨hg, hh⟩ := g.grid_fetch X' r (v:=fun i => (u i).1) h
  have ha (l : Out S) := g.body_get X' (fun i => (u i).1.2) l hh
  let Y i := (bserial S.card (f i)).symm (u i).2
  have hY : Knows m B s x (fun i => (bodyOrder (Layout.std S.card) (f i)).loc (Y i)) :=
    k.cong (fun _ => rfl) (fun i => by rw [← bserial_code, Equiv.apply_symm_apply])
  have hb (l : Fin S.card) := g.body_get (Layout.std S.card) Y l hY
  let q i (k : Fin (f i)) : Space α := glue S ((u i).1.2 k, Y i k)
  have hq (j : α) : Knows m B s x (fun i => (bits (f i)).loc (fun k => q i k j)) := by
    by_cases hj : j ∈ S
    · refine (hb (S.equivFin ⟨j,hj⟩)).cong (fun _ => rfl) (fun i => ?_)
      simp [q, glue, hj]
    · refine (ha ⟨j,hj⟩).cong (fun _ => rfl) (fun i => ?_)
      simp [q, glue, hj]
  refine g.grid_combine X r (v:=v) hg (g.body_set X (fun i => (v i).2) (fun l => ?_))
  refine (g.addr_comb (fun j => A.v j l) q hq).cong (fun _ => rfl) (fun i => ?_)
  apply congr_arg (bits (f i)).loc
  funext k
  simp [v, q, Y, bBook, bSkySplit, bsplit_symm_apply, Finset.sum_apply, mul_comm]

end Gear
end
end PowerSaving.RAM
end OAI
