/-!
# Colour network, C16 (part 1): kernel checker for coordinate register designs (core Lean only)

The searched coordinate part of a register design (results/C_sidewires.md §2,
FORMALIZATION_CNET.md §4.3) is stored as `Nat` data (bitsets as big literals) and checked with
`decide +kernel` (GMP-accelerated `Nat` operations in the kernel; no `native_decide`).
See results/DESIGN_kernel.md §7.

Encoding (`CData`), for the triples of `Fin h`, `v = C(h,3)`:
* elements `els = [(j, m_j, hp_j, sp_j)]`: `j` the index, `m_j` the mask of the `j`-th triple
  (strictly increasing), `hp_j` packed writer hints, `sp_j` packed side partners (`unpack`);
* `Cs = [C_0, …, C_{h-1}]`, `C_x` the bitset (over element indices) of the triples containing `x`;
* groups in a tree `gt`: group `g` is `(R_g, [(L_0,Y_0), …])` with `R_g` the reader bitset, `L_i` the
  nested coordinate labels and `Y_i = R_g ∩ {S : S ∩ L_i = ∅}` (maximal reader chains); a hint
  `e = 16 g + i` is an X-register of the element at label `L_i` of group `g`.

The hot functions are written with explicit recursors (the kernel evaluates them ~4× faster than
`brecOn` code); their equation lemmas hold by `rfl` and are stated here for the bridge proofs
(`CoordBridge.lean`).
-/

namespace OAI
namespace PowerSaving.Colour
namespace CC

/-- Balanced tree of groups; leaf = (reader bitset, labels `(L, Y)`). -/
inductive GTree where
  | leaf (R : Nat) (labs : List (Nat × Nat))
  | node (l r : GTree)

/-- Lookup with LSB-first index bits. (No lemma about it is needed: groups are *defined* by it.) -/
noncomputable def GTree.get (t : GTree) : Nat → Nat × List (Nat × Nat) :=
  @GTree.rec (fun _ => Nat → Nat × List (Nat × Nat)) (fun R labs _ => (R, labs))
    (fun _ _ fl fr k => bif Nat.beq (k % 2) 0 then fl (k / 2) else fr (k / 2)) t

/-- `l[n]`, or `(0,0)`. -/
noncomputable def nthD (l : List (Nat × Nat)) : Nat → Nat × Nat :=
  @List.rec (Nat × Nat) (fun _ => Nat → Nat × Nat) (fun _ => (0, 0))
    (fun p _ ih n => @Nat.casesOn (fun _ => Nat × Nat) n p (fun k => ih k)) l

theorem nthD_nil (n : Nat) : nthD [] n = (0, 0) := rfl
theorem nthD_zero (p : Nat × Nat) (l : List (Nat × Nat)) : nthD (p :: l) 0 = p := rfl
theorem nthD_succ (p : Nat × Nat) (l : List (Nat × Nat)) (n : Nat) :
    nthD (p :: l) (n + 1) = nthD l n := rfl

noncomputable def unpackAux (n : Nat) : Nat → List Nat :=
  @Nat.rec (fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih x => x % 65536 :: ih (x / 65536)) n

theorem unpackAux_zero (x : Nat) : unpackAux 0 x = [] := rfl
theorem unpackAux_succ (n x : Nat) : unpackAux (n + 1) x = x % 65536 :: unpackAux n (x / 65536) := rfl

/-- Packed list: low byte = length, then 16-bit fields. -/
noncomputable def unpack (p : Nat) : List Nat := unpackAux (p % 256) (p / 256)

/-- Number of set bits among the low `n` bits. -/
noncomputable def popc (n : Nat) : Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat) (fun _ => 0) (fun _ ih x => x % 2 + ih (x / 2)) n

theorem popc_zero (x : Nat) : popc 0 x = 0 := rfl
theorem popc_succ (n x : Nat) : popc (n + 1) x = x % 2 + popc n (x / 2) := rfl

/-- `OR` of the `C_x` over the `x ∈ L` (positions counted from the start value `x`). -/
noncomputable def nbhdAux (L : Nat) (Cs : List Nat) : Nat → Nat :=
  @List.rec Nat (fun _ => Nat → Nat) (fun _ => 0)
    (fun C _ ih x => (bif Nat.beq ((L >>> x) % 2) 1 then C else 0) ||| ih (x + 1)) Cs

theorem nbhdAux_nil (L x : Nat) : nbhdAux L [] x = 0 := rfl
theorem nbhdAux_cons (L C : Nat) (Cs : List Nat) (x : Nat) :
    nbhdAux L (C :: Cs) x = (bif Nat.beq ((L >>> x) % 2) 1 then C else 0) ||| nbhdAux L Cs (x + 1) := rfl

/-- Column check: bit `j` of `C_x` equals bit `x` of `m`, for all `x`. -/
noncomputable def colAux (m j : Nat) (Cs : List Nat) : Nat → Bool :=
  @List.rec Nat (fun _ => Nat → Bool) (fun _ => true)
    (fun C _ ih x => Nat.beq ((C >>> j) % 2) ((m >>> x) % 2) && ih (x + 1)) Cs

theorem colAux_nil (m j x : Nat) : colAux m j [] x = true := rfl
theorem colAux_cons (m j C : Nat) (Cs : List Nat) (x : Nat) :
    colAux m j (C :: Cs) x = (Nat.beq ((C >>> j) % 2) ((m >>> x) % 2) && colAux m j Cs (x + 1)) := rfl

/-- Label `(L, Y)` of hint `e = 16 g + i` (or `(0, 0)` if `i` is out of range). -/
noncomputable def hintLab (gt : GTree) (e : Nat) : Nat × Nat := nthD (gt.get (e / 16)).2 (e % 16)

/-- Reader set of a hint, if the hint is valid for the element with mask `m` (else `0`). -/
noncomputable def hintY (G : Nat) (gt : GTree) (m e : Nat) : Nat :=
  bif Nat.blt (e / 16) G && Nat.beq (m &&& (hintLab gt e).1) m then (hintLab gt e).2 else 0

noncomputable def rowOf (G : Nat) (gt : GTree) (m : Nat) (l : List Nat) : Nat :=
  @List.rec Nat (fun _ => Nat) 0 (fun e _ ih => hintY G gt m e ||| ih) l

theorem rowOf_nil (G : Nat) (gt : GTree) (m : Nat) : rowOf G gt m [] = 0 := rfl
theorem rowOf_cons (G : Nat) (gt : GTree) (m e : Nat) (l : List Nat) :
    rowOf G gt m (e :: l) = hintY G gt m e ||| rowOf G gt m l := rfl

noncomputable def sideBits (l : List Nat) : Nat :=
  @List.rec Nat (fun _ => Nat) 0 (fun s _ ih => 1 <<< s ||| ih) l

theorem sideBits_nil : sideBits [] = 0 := rfl
theorem sideBits_cons (s : Nat) (l : List Nat) : sideBits (s :: l) = 1 <<< s ||| sideBits l := rfl

/-- `List.all` by the recursor. -/
noncomputable def allR {α : Type} (f : α → Bool) (l : List α) : Bool :=
  @List.rec α (fun _ => Bool) true (fun a _ ih => f a && ih) l

theorem allR_nil {α : Type} (f : α → Bool) : allR f [] = true := rfl
theorem allR_cons {α : Type} (f : α → Bool) (a : α) (l : List α) :
    allR f (a :: l) = (f a && allR f l) := rfl
theorem allR_append {α : Type} (f : α → Bool) (l₁ l₂ : List α) :
    allR f (l₁ ++ l₂) = (allR f l₁ && allR f l₂) := by
  induction l₁ with
  | nil => rfl
  | cons a l ih => rw [List.cons_append, allR_cons, allR_cons, ih, Bool.and_assoc]

/-- One element record: (index, mask, packed hints, packed side partners). -/
abbrev Elem := Nat × Nat × Nat × Nat

structure CData where
  h : Nat
  v : Nat
  G : Nat
  gt : GTree
  Cs : List Nat
  els : List Elem

namespace CData

def full (D : CData) : Nat := 2 ^ D.v - 1

/-- Per element: a triple mask consistent with the `C_x`, and every disjoint partner is covered by a
valid hint or listed as a side partner. -/
noncomputable def elemOK (D : CData) (e : Elem) : Bool :=
  Nat.blt e.2.1 (2 ^ D.h) && Nat.beq (popc D.h e.2.1) 3 && colAux e.2.1 e.1 D.Cs 0 &&
    Nat.beq ((nbhdAux e.2.1 D.Cs 0 ||| rowOf D.G D.gt e.2.1 (unpack e.2.2.1)
      ||| sideBits (unpack e.2.2.2)) &&& D.full) D.full

def idxOK : List Elem → Nat → Bool
  | [], _ => true
  | e :: es, j => Nat.beq e.1 j && idxOK es (j + 1)

def sortedOK : List Elem → Bool
  | e₁ :: e₂ :: es => Nat.blt e₁.2.1 e₂.2.1 && sortedOK (e₂ :: es)
  | _ => true

def globalOK (D : CData) : Bool :=
  Nat.beq D.els.length D.v && Nat.beq D.Cs.length D.h && idxOK D.els 0 && sortedOK D.els

/-- Labels of a group: sizes in `[4, h-4]`, nested, `Y = R ∩ (readers avoiding L)`. -/
noncomputable def labsOK (D : CData) (R : Nat) : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | prev, p :: ps =>
      Nat.blt p.1 (2 ^ D.h) && Nat.ble 4 (popc D.h p.1) && Nat.ble (popc D.h p.1 + 4) D.h &&
        Nat.beq (prev &&& p.1) prev && Nat.beq p.2 (R &&& (D.full ^^^ nbhdAux p.1 D.Cs 0)) &&
        labsOK D R p.1 ps

noncomputable def grpOK (D : CData) (g : Nat) : Bool :=
  Nat.ble (D.gt.get g).2.length 9 && labsOK D (D.gt.get g).1 0 (D.gt.get g).2

noncomputable def groupsOK (D : CData) : Bool := (List.range D.G).all D.grpOK

/-- Number of hints (= number of coordinate X-registers, an upper bound). -/
def nX (D : CData) : Nat := (D.els.map fun e => e.2.2.1 % 256).sum

/-- Number of listed side partners (an upper bound for the side wires). -/
def nS (D : CData) : Nat := (D.els.map fun e => e.2.2.2 % 256).sum

end CData

/-- Divide-and-conquer popcount of the low `2^d` bits. -/
noncomputable def pcT (d : Nat) : Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat) (fun x => x % 2)
    (fun k ih x => ih (x % 2 ^ 2 ^ k) + ih (x / 2 ^ 2 ^ k)) d

theorem pcT_zero (x : Nat) : pcT 0 x = x % 2 := rfl
theorem pcT_succ (d x : Nat) : pcT (d + 1) x = pcT d (x % 2 ^ 2 ^ d) + pcT d (x / 2 ^ 2 ^ d) := rfl

end CC
end PowerSaving.Colour
end OAI
