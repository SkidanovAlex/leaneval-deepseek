import Mathlib
import Submission.Work.Core.Std
import Submission.Work.Core.Solvable
import Submission.Work.NN.Core.Defs
import Submission.Work.NN.Core.Solver
import Submission.Work.NN.Core.Flat

/-!
# The analytic core of Newlander–Nirenberg: main results

This module assembles the analytic core of the Newlander–Nirenberg theorem in the normalised form
used by the rest of the development (`Submission/Work/Core/`).

## The shape of the analytic input

The single analytic input is `Work.NN.Core.DbarSolverH n J α P P'` (`Solver.lean`): a solution
operator for the linear equation `∂̄_J w = ∂̄_J u` on closed data, with a gain of one derivative
measured in a **Hölder** norm of the datum
(`‖d(solve u)‖_{∞,P'} ≤ C₀ · δ`, where `δ` bounds the `C^{0,α}`-norm of `∂̄_J u` on the slightly
larger set `P`), and mapping smooth data to smooth corrections.

This is the classical Kohn/Hörmander small polydisc `∂̄`-estimate for the *integrable* structure
`J`: the datum `∂̄_J u` is `∂̄_J`-exact, hence closed because `∂̄_J ∘ ∂̄_J = 0` (the vanishing of the
Nijenhuis tensor is exactly what makes `∂̄_J` a differential), which is the class of data for which
the classical estimates hold.  The estimates themselves are classical Calderón–Zygmund/Schauder
estimates for manifolds with smooth coefficients; the *flat* case is being formalised in
`Submission/Work/CR/Flat` (see `Work.NN.Core.flat_dbar_holder` for the flat `∂̄`-Poincaré result
with a gain of one derivative, in Hölder form).

The auxiliary datum hypothesis `DbarDataBound J (zvec T) α P δ` says that `‖∂̄_J z_j‖ ≤ δ` and
`[∂̄_J z_j]_{α} ≤ δ` on `P`.  On a polydisc of radius `r` around `0` one has `δ = O(r) + O(r^{1-α})`
because `∂̄_J z_j = (i/2)·dz_j ∘ (J - stdOf T)` and `J - stdOf T` vanishes at `0`; this is what makes
the smallness hypothesis `C₀ δ ‖tupleDerivInv T‖ < 1` satisfiable on a small enough polydisc.

## Main statements

* `local_holomorphic_functions` — the analytic core, normalised form.
* `local_holomorphic_functions'` — the same in the exact shape required by the challenge.
* `dbarSolvable_of_solver` — the same in the shape `Submission.DbarSolvable J U 0 T`.
* `Flat.isHolomorphicFrame_stdOf` — the flat case `A = 0`, unconditionally.

## History

An earlier version of this directory packaged the analytic input in *supremum* norms
(`Defs.lean`'s `FlatSolver`/`PertSolver`).  Those interfaces are unsatisfiable: the operator
`∂Δ^{-1}∂` is a Calderón–Zygmund transform of order `0` and hence is **not** bounded on `L^∞`, so
"data bounded in `L^∞` by `δ` gives `‖d(solve u)‖ ≤ C₀ δ`" is false even for the flat structure on
a disc in `ℂ`.  The honest interface is the Hölder one above; see `Solver.lean` for the details.
-/

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Filter
open Set
open scoped ContDiff Topology

namespace Work.NN.Core

variable {n : ℕ}

/-- `T` intertwines `J 0` with multiplication by `i` on `ℂⁿ` if and only if `J 0` is the
transported standard structure `stdOf T`. -/
lemma eq_stdOf_iff (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n) :
    (∀ v : E n, T (J 0 v) = Complex.I • T v) ↔ J 0 = stdOf T 0 := by
  constructor
  · intro h
    refine ContinuousLinearMap.ext (fun v => ?_)
    have h2 : T.symm (T (J 0 v)) = T.symm (Complex.I • T v) := by rw [h v]
    simpa [stdOf_apply] using h2
  · intro h v
    rw [h, stdOf_apply]
    exact T.apply_symm_apply (Complex.I • T v)

/-- The datum `∂̄_J z_j` equals `L_A z_j`, i.e. `dbarPert` of the perturbation. -/
lemma dbar_zcoord_eq {n : ℕ} {T : E n ≃L[ℝ] F n} (J : E n → E n →L[ℝ] E n) (j : Fin n)
    (y : E n) :
    dbar J (zcoord T j) y = dbarPert (perturbation J T) (zcoord T j) y := by
  rw [dbar_linearization T J (zcoord T j) y]
  have hstd : dbar (stdOf T) (zcoord T j) y = 0 := by
    rw [dbar_eq_zero_iff]
    exact fun w => zcoord_hol T j y w
  rw [hstd, zero_add, dbarPert_perturbation]

/-- **The analytic core of Newlander–Nirenberg**, normalised form.

`J` is a field of endomorphisms on an open `U ∋ 0` with `J y ∘ J y = -1` and vanishing Nijenhuis
tensor, which at `0` is the transport of the standard structure `stdOf T`.  Let `P' ⊆ U` be open
with `0 ∈ P'`, let `P` be an open set containing the datum of the equation, and suppose

* the datum `∂̄_J z_j` has `C^{0,α}`-norm at most `δ` on `P` (`hdata`), and
* the classical small polydisc `∂̄`-solver `S : DbarSolverH n J α P P'` is available, and
* `C₀ δ ‖tupleDerivInv T‖ < 1` (`hsmall`).

Then some neighbourhood `V ∋ 0` carries `n` independent `J`-holomorphic functions. -/
theorem local_holomorphic_functions {n : ℕ} {U : Set (E n)} {J : E n → E n →L[ℝ] E n}
    {T : E n ≃L[ℝ] F n}
    (hU : IsOpen U) (hJ : IsAlmostComplexOn J U) (_hN : NijenhuisVanishesOn J U)
    (hT : ∀ v : E n, T (J 0 v) = Complex.I • T v)
    {P P' : Set (E n)} (hPopen : IsOpen P) (hP'open : IsOpen P')
    (h0P' : (0 : E n) ∈ P') (hP'U : P' ⊆ U) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hdata : DbarDataBound J (zvec T) α P δ)
    (S : DbarSolverH n J α P P')
    (hsmall : S.C₀ * δ * ‖tupleDerivInv T‖ < 1) :
    ∃ V : Set (E n), IsOpen V ∧ 0 ∈ V ∧ V ⊆ U ∧
      ∃ u : Fin n → E n → ℂ, IsHolomorphicFrame J V u := by
  obtain ⟨v, _hv, hframe⟩ :=
    exists_frame_of_solver hP'open h0P' hδ hdata S hsmall
  exact ⟨P', hP'open, h0P', hP'U, fun j y => zcoord T j y - v y j, hframe⟩

/-- **The analytic core in the exact shape of the challenge statement**: `n` independent
`J`-holomorphic functions near `0`, with holomorphicity written as `d u_j ∘ J = i · d u_j`. -/
theorem local_holomorphic_functions' {n : ℕ} {U : Set (E n)} {J : E n → E n →L[ℝ] E n}
    {T : E n ≃L[ℝ] F n}
    (hU : IsOpen U) (hJ : IsAlmostComplexOn J U) (hN : NijenhuisVanishesOn J U)
    (hT : ∀ v : E n, T (J 0 v) = Complex.I • T v)
    {P P' : Set (E n)} (hPopen : IsOpen P) (hP'open : IsOpen P')
    (h0P' : (0 : E n) ∈ P') (hP'U : P' ⊆ U) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hdata : DbarDataBound J (zvec T) α P δ)
    (S : DbarSolverH n J α P P')
    (hsmall : S.C₀ * δ * ‖tupleDerivInv T‖ < 1) :
    ∃ V : Set (E n), IsOpen V ∧ 0 ∈ V ∧ V ⊆ U ∧ ∃ u : Fin n → E n → ℂ,
      (∀ j, ContDiffOn ℝ ∞ (u j) V) ∧
      (∀ j, ∀ y ∈ V, ∀ v : E n,
        fderiv ℝ (u j) y (J y v) = Complex.I * fderiv ℝ (u j) y v) ∧
      (∀ y ∈ V, Function.Bijective (fderiv ℝ (fun y : E n => fun j => u j y) y)) := by
  obtain ⟨V, hV, h0V, hVU, u, hframe⟩ :=
    local_holomorphic_functions hU hJ hN hT hPopen hP'open h0P' hP'U hα0 hα1 hδ hdata S hsmall
  obtain ⟨h1, h2, h3⟩ := (isHolomorphicFrame_iff J V u).mp hframe
  exact ⟨V, hV, h0V, hVU, u, h1, h2, h3⟩

/-- The same conclusion in the shape of `Submission.DbarSolvable`, so that the reduction
`Submission.nn_core_of_dbar` applies. -/
theorem dbarSolvable_of_solver {n : ℕ} {U : Set (E n)} {J : E n → E n →L[ℝ] E n}
    {T : E n ≃L[ℝ] F n}
    (hU : IsOpen U) (hJ : IsAlmostComplexOn J U) (_hN : NijenhuisVanishesOn J U)
    (hT : ∀ v : E n, T (J 0 v) = Complex.I • T v)
    {P P' : Set (E n)} (hPopen : IsOpen P) (hP'open : IsOpen P')
    (h0P' : (0 : E n) ∈ P') (hP'U : P' ⊆ U) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hdata : DbarDataBound J (zvec T) α P δ)
    (S : DbarSolverH n J α P P')
    (hsmall : S.C₀ * δ * ‖tupleDerivInv T‖ < 1) :
    DbarSolvable J U 0 T := by
  obtain ⟨v, hv, hframe⟩ := exists_frame_of_solver hP'open h0P' hδ hdata S hsmall
  have hvsm : ∀ j, ContDiffOn ℝ ∞ (fun y => v y j) P' := by
    intro j
    have h := (contDiff_zcoord T j).contDiffOn.sub (hframe.contDiff j)
    have h2 : (fun y : E n => zcoord T j y - (zcoord T j y - v y j))
        = (fun y => v y j) := by
      funext y
      ring
    rwa [h2] at h
  refine ⟨P', hP'open, h0P', hP'U, fun j y => v y j, hvsm, ?_, ?_⟩
  · intro j y hy
    rw [hv j y hy, dbar_zcoord_eq J j y, dbarPert_perturbation]
  · intro y hy
    exact hframe.bijective y hy

/-- **Convenience form**: it suffices that there *exist* `P, P'` and `δ` on which the datum bound,
the solver and the smallness condition are available simultaneously. -/
theorem local_holomorphic_functions_of_exists {n : ℕ} {U : Set (E n)}
    {J : E n → E n →L[ℝ] E n} {T : E n ≃L[ℝ] F n}
    (hU : IsOpen U) (hJ : IsAlmostComplexOn J U) (hN : NijenhuisVanishesOn J U)
    (hT : ∀ v : E n, T (J 0 v) = Complex.I • T v)
    (h : ∃ (P P' : Set (E n)) (α δ : ℝ) (S : DbarSolverH n J α P P'),
        IsOpen P ∧ IsOpen P' ∧ (0 : E n) ∈ P' ∧ P' ⊆ U ∧ 0 < α ∧ α < 1 ∧ 0 ≤ δ ∧
        DbarDataBound J (zvec T) α P δ ∧ S.C₀ * δ * ‖tupleDerivInv T‖ < 1) :
    ∃ V : Set (E n), IsOpen V ∧ 0 ∈ V ∧ V ⊆ U ∧
      ∃ u : Fin n → E n → ℂ, IsHolomorphicFrame J V u := by
  obtain ⟨P, P', α, δ, S, hPopen, hP'open, h0P', hP'U, hα0, hα1, hδ, hdata, hsmall⟩ := h
  exact local_holomorphic_functions hU hJ hN hT hPopen hP'open h0P' hP'U hα0 hα1 hδ hdata S hsmall

end Work.NN.Core
