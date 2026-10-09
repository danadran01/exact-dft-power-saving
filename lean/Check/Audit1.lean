import OAI.Computability.FourierTransform.Main

open Lean Meta Elab Command

namespace AuditCheck

/-- transitive closure of constants used by a declaration (type + value, plus ctors/recursors
of inductives). -/
partial def closure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        if let .inductInfo ii := ci then cs := cs ++ ii.ctors.toArray
        if let .ctorInfo ci' := ci then cs := cs.push ci'.induct
        for c in cs do
          if !seen.contains c then stack := c :: stack
  return seen

def isLib (m : Name) : Bool :=
  [`Mathlib, `Init, `Std, `Lean, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
   `LeanSearchClient, `ImportGraph].any (fun p => p.isPrefixOf m)

elab "#audit_closure " id:ident : command => do
  let env ← getEnv
  let s := closure env [id.getId]
  let mut byMod : Std.HashMap Name (Array Name) := {}
  let mut nOther := 0
  for n in s.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if isLib m then nOther := nOther + 1
      else byMod := byMod.insert m ((byMod.getD m #[]).push n)
    | none => byMod := byMod.insert `CURRENT_FILE ((byMod.getD `CURRENT_FILE #[]).push n)
  logInfo s!"closure size {s.size}; library constants {nOther}"
  for (m, ns) in byMod.toList do
    logInfo s!"{m}: {ns.size} constants: {ns.qsort (·.toString < ·.toString)}"

end AuditCheck

#audit_closure OAI.PowerSaving.ImprovedGoal
#audit_closure OAI.PowerSaving.DFTGoal

set_option pp.fullNames true in
#print OAI.PowerSaving.ImprovedGoal
set_option pp.fullNames true in
#print OAI.PowerSaving.improvedTime
set_option pp.fullNames true in
#print OAI.PowerSaving.improvedExponent
set_option pp.fullNames true in
#print OAI.PowerSaving.DFTProgram
set_option pp.fullNames true in
#print OAI.PowerSaving.TimeBounds
set_option pp.fullNames true in
#print OAI.PowerSaving.dft
set_option pp.fullNames true in
#print OAI.PowerSaving.root
set_option pp.fullNames true in
#print OAI.ExactFourier.zeta
#check @OAI.PowerSaving.transform_improved
#print axioms OAI.PowerSaving.transform_improved

namespace OAI.PowerSaving
open RAM Filter Asymptotics

-- explicit elaboration checks: the statement's pieces are the intended Mathlib objects
example : ImprovedGoal = ∃ order solve W, DFTProgram order solve W ∧ TimeBounds W ∧
    Asymptotics.IsBigO (Filter.atTop : Filter ℕ) (fun n => (W n : ℝ))
      (fun n : ℕ => (n:ℝ) * Real.rpow (Real.log (n:ℝ)) (1 - 32/(10:ℝ)^7)) := rfl

example : root = fun n : ℕ => Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) := rfl

example (n : ℕ) (x : Vec n) (j : Fin n) :
    dft n x j = ∑ k : Fin n, Complex.exp (2 * Real.pi * Complex.I / n) ^ (j.val * k.val) * x k :=
  rfl

-- root n is a primitive n-th root of unity (n ≥ 1)
example (n : ℕ) (hn : n ≠ 0) : IsPrimitiveRoot (root n) n := Complex.isPrimitiveRoot_exp n hn

lemma root4 : root 4 = Complex.I := by
  have : (2 * Real.pi * Complex.I / ((4:ℕ) : ℂ)) = (Real.pi / 2 : ℝ) * Complex.I := by
    push_cast; ring
  simp only [root, ExactFourier.zeta, this]
  rw [Complex.exp_mul_I]
  simp

lemma root2 : root 2 = -1 := by
  have : (2 * Real.pi * Complex.I / ((2:ℕ) : ℂ)) = Real.pi * Complex.I := by
    push_cast; ring
  simp only [root, ExactFourier.zeta, this, Complex.exp_pi_mul_I]

lemma dft1 (x : Vec 1) : dft 1 x = x := by
  funext j
  fin_cases j
  simp [dft]

lemma dft2 (x : Vec 2) : dft 2 x = ![x 0 + x 1, x 0 - x 1] := by
  funext j
  fin_cases j <;> simp [dft, Fin.sum_univ_two, root2] <;> ring

lemma dft4_e1 : dft 4 (Pi.single 1 1) = ![1, Complex.I, -1, -Complex.I] := by
  funext j
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases j <;> simp [dft, root4, Pi.single_apply]

lemma exp_lt_one : improvedExponent < 1 ∧ 0 < improvedExponent ∧
    improvedExponent = 1 - 32/10000000 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [improvedExponent]

lemma improved_vs_decimal : decimalExponent > improvedExponent := by
  norm_num [decimalExponent, improvedExponent]

lemma improvedTime_ge_one : ∀ᶠ n in atTop, (1:ℝ) ≤ improvedTime n := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hl : (1:ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hq : 0 ≤ improvedExponent := (exp_lt_one.2.1).le
  have := Real.one_le_rpow hl hq
  unfold improvedTime
  nlinarith

-- the comparison of outputs is a full Tape equality: length and every entry
example (n : ℕ) (f g : Fin n → ℂ) (h : (⟨n, f⟩ : Tape ℂ) = ⟨n, g⟩) : f = g := by
  cases h; rfl

-- trivial consequences of DFTProgram: W n ≥ 1, and order gives D with 0 < D < 1024 n^3
example (o : Prog false .w .w) (s) (W : ℕ → ℕ) (h : DFTProgram o s W) (n : ℕ) (hn : 0 < n) :
    1 ≤ W n := by
  obtain ⟨c, hc⟩ := h
  have := (hc n hn).2.2.2.2.2.2 0
  simp only at this
  omega

#check @matrix_definition

end OAI.PowerSaving
