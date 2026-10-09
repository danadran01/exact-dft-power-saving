# Adversarial audit of the STATEMENT `OAI.PowerSaving.transform_improved : ImprovedGoal`

Project: the `lean/` directory of this repository (Mathlib `d13f23b7…`; pristine, `git status` clean).
Build: `lake build --no-build OAI.Computability.FourierTransform.Main` reports "All targets up-to-date (9048 jobs)",
so the oleans used below match the sources.

Check files (reproducible, outside the build globs):
- `lean/Check/Audit1.lean`: provenance closure, `#print`s, `rfl` elaboration checks, sanity lemmas.
- `lean/Check/Audit2.lean`: a machine-checked non-vacuity theorem, `DFTProgram … W → ∀ n ≥ 2, n ≤ W n`.

Both compile with **no errors**. Run with
`cd lean && lake env lean Check/AuditN.lean`.

## Verdict

**No FATAL or SERIOUS findings.** `ImprovedGoal` says what the claim says. It refers only to OpenAI's
unmodified definitions plus three transparent new ones (`improvedExponent`, `improvedTime`, `ImprovedGoal`).
The DFT is the standard unnormalized matrix (ζ_n^{jk}) with ζ_n = exp(2πi/n). The full output tape is compared.
The quantifiers are uniform. The cost model has no free-work loophole that I could find, and its content is
shown by a Lean proof that W n ≥ n. The MINOR items below concern presentation and model conventions.

---

## The statement

```lean
-- Main.lean (new)
def improvedExponent : ℝ := 1 - 32/(10:ℝ)^7
def improvedTime (n : ℕ) : ℝ := (n:ℝ) * (Real.log (n:ℝ)) ^ improvedExponent
def ImprovedGoal : Prop := ∃ order solve W, DFTProgram order solve W ∧ TimeBounds W ∧
  (fun n => (W n : ℝ)) =O[atTop] improvedTime
```
`#print axioms OAI.PowerSaving.transform_improved` gives `[propext, Classical.choice, Quot.sound]`.

The fully elaborated form (`pp.fullNames`):
```
def OAI.PowerSaving.ImprovedGoal : Prop :=
∃ order solve W, OAI.PowerSaving.DFTProgram order solve W ∧
    OAI.PowerSaving.TimeBounds W ∧ (fun n => ↑(W n)) =O[Filter.atTop] OAI.PowerSaving.improvedTime
def OAI.ExactFourier.zeta : ℕ → ℂ := fun n => Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)
def OAI.PowerSaving.dft : (n : ℕ) → Vec n → Vec n := fun n x j => ∑ k, root n ^ (↑j * ↑k) * x k
```

## 1. The DFT: VERIFIED-OK

- `root = ExactFourier.zeta`, and `zeta n = Complex.exp (2 * Real.pi * Complex.I / n)`.
  - Lean check (`rfl`): `root = fun n => Complex.exp (2*Real.pi*Complex.I/(n:ℂ))`.
  - Lean check: `IsPrimitiveRoot (root n) n` for `n ≠ 0`, by `Complex.isPrimitiveRoot_exp`.
- `dft n x j = ∑ k, ζ_n^(j·k) · x k` is the unnormalized DFT with the positive sign, matching the claim and
  the paper's F_d = (ζ_d^{jk}).
  - Lean check (`rfl`): `dft n x j = ∑ k, Complex.exp (2πi/n)^(j.val*k.val) * x k`.
  - OpenAI's `matrix_definition : dft n x = (dftMatrix n).mulVec x` is present and holds by `rfl`.
    Here `dftMatrix = fourierMatrix`, with `fourierMatrix n j k = zeta n ^ (j*k)`.
- Sanity lemmas proved in `Audit1.lean`:
  - `root 2 = -1` and `root 4 = Complex.I`;
  - `dft 1 x = x`;
  - `dft 2 x = ![x 0 + x 1, x 0 - x 1]`;
  - `dft 4 (Pi.single 1 1) = ![1, I, -1, -I]`.
- The output check `result.val = (⟨n, dft n x⟩ : Tape ℂ)` is a structure equality, so it fixes the length and
  every entry. Lean check: `(⟨n,f⟩ : Tape ℂ) = ⟨n,g⟩ → f = g`.
- The root: `solve` receives `root d.val` where `d := run order n`. `order : Prog false w w` is a fixed program
  whose only input is n. The statement requires `0 < d.val`, `d.val < 1024*n^3`, `d.val ≤ cap`, `d.valid`,
  `d.peak ≤ cap`, and charges `d.work + 1` (the +1 is the root primitive). D cannot depend on x.
  - A degenerate D does not help. In DFT mode the data are only added, subtracted, and scaled by scalars
    generated from {ζ_D, 1, inverses}, i.e. elements of ℚ(ζ_D). An exact DFT for n ≥ 3 therefore forces
    ζ_n ∈ ℚ(ζ_D). That is the prover's burden, and the proof meets it (`transform_main_order`: D = receipt n < 8n³).

## 2. The cost model (RAM.lean): VERIFIED-OK

I checked every constructor of `Atom.run`, `Code.run`, `Bill.steps/sow/tab` and `depthRun`.
- **Every atom costs 1.** `Bill.one` and `Bill.word` have work 1. `Bill.word` also records the produced integer
  in `peak`. This covers `lit`, `int` (add/sub/mul/div/mod/lt), and `len`.
- **Composite code is charged in full.**
  - `comp`, `ifz`, `loop`, `tab`, `sow`, `importClosed`, `call` and `descend` each add +1 on top of the sum of
    their sub-runs (`Bill.pass` adds the work).
  - `fork` pays both branches plus `Bill.one`.
  - `ifz` pays only the branch it takes, which is correct.
- **Loops are charged per iteration.** `Bill.steps` pays 1 per iteration and records `i+1` in `peak`, so the
  trip counts are bounded by `cap`.
- **Arrays are charged their length.** `Bill.sow len count` pays `1+len` for allocation plus one step per write,
  and records `len` in `peak`. `tab` is `sow len len`. No atom does a whole-array update; `Tape.map` and
  `Tape.set` are not reachable as instructions.
- **Recursion is charged per call.** `descend` charges +1 per level of `depthRun` and records the fuel `k` in
  `peak`, and each `call` pays its callee's full `Bill` plus 1. Tree recursion is therefore charged for every call.
- **No magic constants.** The only scalar constants are `cz` (0), `cone` (1) and the supplied root. There is no
  atom for an arbitrary complex constant.
- **No data-dependent control and no data products.**
  - No atom maps ℂ to ℕ, so tests and loop bounds cannot depend on x.
  - No atom converts the `left` paint to `scalar`, and `cross` needs `allow = true`, while DFT programs are
    `Prog false`.
  - So the program is, for each n, a fixed linear straight-line computation in x with input-independent
    coefficients. This matches the paper's §1.1.
- **`valid` cannot be used to escape.** It is a conjunction of `x ≠ 0` side conditions for `inv`, and
  `DFTProgram` requires `d.valid ∧ result.valid` for every x. A false `valid` makes `DFTProgram` false; it does
  not make it easier.
- **Integers and memory are polynomially bounded.**
  - `cap = (n+2)^cBound` bounds `d.peak`, `result.peak`, `d.val`, and also `W n + 10(n+2)`.
  - Every integer reaches a register either through `word`/`steps`/`sow`/`depthRun`, which record it in `peak`,
    or by being moved (`id/fst/snd/look`), so `peak` covers all integers.
  - Memory is bounded by work, since each unit leaves O(1) cells and arrays are charged their length.
    Hence memory ≤ W n ≤ cap.
- **W is an upper bound on all charged work:** `d.work + 1 + result.work ≤ W n` for all x.

**Non-vacuity, machine-checked** (`Audit2.lean`, axioms `[propext, Classical.choice, Quot.sound]`):
```lean
theorem DFTProgram.work_ge {o s W} (hP : DFTProgram o s W) (n : ℕ) (hn : 2 ≤ n) : n ≤ W n
```
The proof is an induction over all `Code` constructors, with an invariant over handlers: every array in any
produced value has length ≤ (work charged so far) or is literally the input tape. With x = e₀ we get
`dft n e₀ = (1,…,1) ≠ e₀`, so the output must be a fresh array, and its length n must have been charged.
So W cannot be trivially small, and the O-bound has real content. Separately: `TimeBounds` holds,
`improvedTime → ∞`, and `improvedTime n ≥ 1` eventually (proved).

## 3. Quantifiers: VERIFIED-OK

- `∃ order solve W` comes first, then `DFTProgram`'s `∃ cBound` with `∀ n > 0`, then `∀ x : Vec n`. So the
  program, W and the polynomial exponent are fixed before n, and correctness holds for every x.
- `Code` is an inductive, so programs are finite syntax trees. Literals are fixed naturals.
- Lean check (`rfl`): `ImprovedGoal` equals
  `∃ order solve W, DFTProgram order solve W ∧ TimeBounds W ∧ IsBigO (atTop : Filter ℕ) (fun n => (W n : ℝ)) (fun n => n * Real.rpow (Real.log n) (1 - 32/10^7))`.
  The filter is `atTop` on ℕ, the log is the natural log, and `^` is `Real.rpow` applied to `log n` (not `log (n^q)`).
- Exponent checks (proved): `improvedExponent = 1 - 32/10⁷ = 1 - 3.2·10⁻⁶`, with
  `0 < improvedExponent < 1` and `improvedExponent < decimalExponent = 1 - 10⁻¹³`.
  So the new bound is strictly stronger than OpenAI's corollary, not implied by it.
- `TimeBounds W` (OpenAI's three bounds) is also required.

## 4. Name provenance and shadowing: VERIFIED-OK

I computed the transitive closure of all constants used by `ImprovedGoal` (types, values, constructors) and
grouped them by originating module with `Environment.getModuleIdxFor?`:
```
closure size 16477; library constants 16349
OAI.Computability.FourierTransform.Goal : DFTProgram, TimeBounds, Vec, dft, root, dftInKind, dftOutKind,
     paperTime, decimalTime, nlogn, theta, paperM/W/Delta/Multiplier, decimalExponent (+ _proof aux)
OAI.Computability.FourierCircuit.Core  : ExactFourier.zeta (+ _proof_1)
OAI.Computability.FourierTransform.RAM : 101 constants (Atom, Bill, Code, NOp, Paint, Ty, depthRun, run, …)
OAI.Computability.FourierTransform.Main: ImprovedGoal, improvedExponent, improvedTime (+ _proof aux)
```
- No constant from `Grouped/`, `Colour/` or any other project module is in the closure.
- All the other 16349 constants come from library modules (Mathlib/Init/Std/…), and Mathlib is the pinned
  commit with a clean worktree.
- A grep over all of `OAI/` found:
  - no `axiom`, `opaque`, `implemented_by`, `extern`, `macro`, `notation` or `elab`;
  - only innocuous `Decidable`/`Fintype` instances on project-local types.

## 5. Agreement with OpenAI's challenge file: VERIFIED-OK

- `RAM.lean`: the region from `/-!` to `end RAM` is textually identical to the challenge file (`diff` empty).
- `Goal.lean` and `Core.zeta`: after stripping comments, every definition in the challenge file is identical:
  `zeta, paperM, paperW, paperDelta, paperMultiplier, theta, decimalExponent, paperTime, decimalTime, nlogn, root,
  Vec, dft, conv, dftInKind, dftOutKind, convInKind, convOutKind, DFTProgram, ConvProgram, TimeBounds, DFTGoal, ConvGoal`.
  The only extra definition is `dftMatrix`, which does not appear in the statement.
- The opening namespaces (`open RAM RAM.Ty Filter Asymptotics`) are the same.
- SHA-256 hashes:
  - `RAM.lean`, `Goal.lean` and `FourierCircuit/Core.lean` are byte-identical across the verified build, OpenAI's original
    sources and this repository's `lean/`.
  - `ComparatorChallenges/UniformFourier.lean` (`4c571f27…`) is identical across all three copies.
- `Main.lean` differs from OpenAI's original `Main.lean` only in two ways:
  - proof internals (`alpha` → `Colour.Expo.epsC/zC` in three `norm_num`s);
  - the appended improvement block.

## Findings by severity

**FATAL**: none.

**SERIOUS**: none.

**MINOR**
1. *`ImprovedGoal` is not in a comparator challenge file.* OpenAI's `UniformFourier.lean` only states
   `DFTGoal`. `ImprovedGoal` is defined in `Main.lean`, the same module as the proof. Its trust rests on this
   review and the closure check, not on a comparator match.
   - Recommendation: add `ComparatorChallenges/ImprovedFourier.lean` = OpenAI's file + the three definitions
     + `theorem transform_improved : ImprovedGoal := sorry`, and run the comparator.
2. *Model convention: the root primitive.* ζ_D is supplied at unit cost, with D computed by the fixed `order`
   program and 0 < D < 1024n³. So "all scalar preparation charged" means everything except this one primitive.
   This is exactly OpenAI's model (paper §1.1, Thm 1.1) and is charged as `+1`.
3. *Model convention: exact unit-cost complex arithmetic, no bit complexity.* Complex registers are unbounded
   exact values, and integers/addresses are bounded by `(n+2)^c`. Memory is not a separate field: it is bounded
   by `work ≤ W n ≤ cap` through the charging convention, which is sound as audited. The claim's "polynomially
   bounded memory" is therefore a consequence, not a separately stated conjunct.
4. *Sign convention.* The DFT uses exp(+2πi/n), which matches the claim. Readers used to e^{−2πi jk/n} should
   note this. The two differ by the output permutation j ↦ −j mod n.
5. *Redundancy.* `TimeBounds W` is implied by the new O-bound. It is harmless, and a useful cross-check.
