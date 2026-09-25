/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The analytic input of the assembly: a right inverse of `∂̄_{Jstd+A}` on polydiscs

This file isolates, as a *structure*, the single analytic statement from which the perturbation
assembly of Newlander–Nirenberg produces the local holomorphic frame: a **right inverse of
`∂̄_{Jstd + A}` on `∂̄_J`-closed `(0,1)`-forms on the nested polydiscs `pd n ρ 4 → pd n ρ 1`**, with
a gain of one derivative in the `C^{1,α}` scale and mapping smooth data to smooth solutions.

The structure is the flat-model, `∂̄_J`-analogue of `Work.NN.Final.FlatOne` (which is the same
statement for the *standard* structure) and of `Work.NN.Core.DbarSolverH` (its `E n`-model
counterpart).  Its classical content is the solvability of the `∂̄`-equation of an integrable almost
complex structure on a polydisc with interior Schauder estimates: the classical (Hörmander/Kohn/
Nirenberg) input of Newlander–Nirenberg.

`Work.NN.Assemble.exists_frame_of_solver` in the companion file
`Submission/Work/NN/Assemble/exists_frame_of_solver.lean` reduces the conclusion of the assembly
lemma to the existence of such a solver for every small `A` with `A`-independent constants; the
fixed-point argument of `Work.NN.Assemble.perturbedDbarSol_exists` shows why the *standard*
structure's Poincaré operator (`FlatOne`) alone is not enough: the datum of the iteration
(`ξ(v) = L_A(z_j - v)`) is not `∂̄₀`-closed.
-/
import Mathlib
import Submission.Work.NN.Assemble.Setup
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Assemble

/-- **The data of the `∂̄_J`-equation are `(0,1)`-forms**: a smooth `(0,1)`-form `f` for the
structure `J = JstdCn n + A` is `J z`-antilinear at every point.  This condition is *essential*: for
any `z` the form `dbarCn J u z` is `J z`-antilinear (`Work.NN.Core.dbarCn_antilinear`), so no datum
which is not antilinear can be solved. -/
def IsJAntilinear {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ) : Prop :=
  ∀ z (v : Work.NN.Core.Cn n), f z ((Work.NN.Core.JstdCn n + A) z v) = -Complex.I * f z v

/-- **A right inverse of `∂̄_{Jstd+A}` on nested polydiscs.**  For an almost complex structure
`J = JstdCn n + A` on `pd n ρ 4`, `T` solves `∂̄_J v = f` on `pd n ρ 1` for every smooth
`∂̄_J`-closed `(0,1)`-form `f` on `pd n ρ 4`, with the `C^{1,α}` estimate
`‖T f‖_{C^{1,α}(pd n ρ 1)} ≤ C Σ_m ‖f (e_m)‖_{C^{0,α}(pd n ρ 4)}`, and maps smooth data to smooth
solutions. -/
structure DbarJSolver {n : ℕ} (α : ℝ) (ρ : Fin n → ℝ)
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) where
  /-- the constant of the `C^{1,α}` estimate (independent of `A`) -/
  C : ℝ
  hC : 0 < C
  /-- the solution operator -/
  T : (Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ) → (Work.NN.Core.Cn n → ℂ)
  /-- `T f` solves `∂̄_J v = f` on `pd n ρ 1` when `f` is smooth and `∂̄_J`-closed on `pd n ρ 4` -/
  solves : ∀ f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ,
    (∀ m : ℕ, ContDiff ℝ m f) → IsJAntilinear A f →
    (∀ z : Work.NN.Core.Cn n, z ∈ pd n ρ 4 → ∀ V W : Work.NN.Core.Cn n,
      Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
        (fun z' => Work.NN.Final.dOne f z') z V W = 0) →
    ∀ z : Work.NN.Core.Cn n, z ∈ pd n ρ 1 →
      Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) (T f) z = f z
  /-- the gain of one derivative in the `C^{1,α}` scale -/
  est : ∀ f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ,
    (∀ m : ℕ, ContDiff ℝ m f) → IsJAntilinear A f →
    (∀ z : Work.NN.Core.Cn n, z ∈ pd n ρ 4 → ∀ V W : Work.NN.Core.Cn n,
      Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
        (fun z' => Work.NN.Final.dOne f z') z V W = 0) →
    Work.CR.Flat.holderNorm 1 α (T f) (pd n ρ 1)
      ≤ ENNReal.ofReal C * ∑ m : Fin n,
          Work.CR.Flat.holderNorm 0 α (fun z => f z (Pi.single m (1 : ℂ))) (pd n ρ 4)
  /-- smooth data give smooth solutions -/
  smooth : ∀ f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ,
    (∀ m : ℕ, ContDiff ℝ m f) → IsJAntilinear A f →
    (∀ z : Work.NN.Core.Cn n, z ∈ pd n ρ 4 → ∀ V W : Work.NN.Core.Cn n,
      Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
        (fun z' => Work.NN.Final.dOne f z') z V W = 0) →
    ∀ m : ℕ, ContDiffOn ℝ m (T f) (pd n ρ 1)

end Work.NN.Assemble
