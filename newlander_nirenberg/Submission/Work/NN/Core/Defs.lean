import Mathlib
import Submission.Work.Core.Std
import Submission.Work.Core.Solvable

/-!
# The analytic core of Newlander–Nirenberg: the perturbation setup

This module sets up the notation for the local (analytic) part of the proof of
Newlander–Nirenberg, in the normalised situation fixed by `Submission/Work/Core/Std.lean`:
`T : E n ≃L[ℝ] F n` is a real-linear isomorphism, `stdOf T` is the resulting *constant*
complex structure on `E n` (the transport of multiplication by `i` on `ℂⁿ`), `zcoord T j` are
the standard coordinate functions, and `dbar_linearization` writes the `∂̄`-operator of a field
`J` as

  `∂̄_J u = ∂̄_{stdOf T} u + dbarPert (perturbation J T) u`,

with `perturbation J T = J - stdOf T` and `dbarPert A u = (i/2)·du ∘ A`.  The chart equation
`∂̄_J u = 0` is therefore *linear* in `u`, and becomes solvable by a contraction once
`∂̄_{stdOf T}` is inverted with a gain of one derivative:

  `∂̄_J v = ∂̄_J z_j  ⟺  ∂̄_{stdOf T} v = dbarPert A (z_j - v)  ⟺  v = T₀ (g - L_A v)`,

where `T₀` is the flat solver, `g = dbarPert A z_j` and `L_A = dbarPert A`.

The two analytic inputs are packaged as structures here:

* `FlatSolver n T P` — the flat `∂̄`-equation has a solution on the open set `P`, linear in the
  data, with a gain of one derivative (step 2 of the classical proof, Hörmander/Kohn's small
  polydisc estimates, produced by the subproject `Submission/Work/CR/Flat`), and solutions with
  smooth data are smooth;
* `DbarRegular n J P` — interior regularity (hypoellipticity) of `∂̄_J`: a `C¹` solution whose
  `∂̄_J`-datum is smooth is smooth (step 4).  This is the classical elliptic regularity of the
  overdetermined elliptic system `∂̄_J` with smooth coefficients.

The contraction itself (step 3), the invertibility of the differential (step 3) and the assembly
are in the other modules of this directory.
-/

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Filter
open Set
open scoped ContDiff

namespace Work.NN.Core

variable {n : ℕ}

/-! ## The perturbation of the `∂̄`-operator -/

/-- The discrepancy `A = J - stdOf T` between the field `J` and the reference constant complex
structure attached to `T`.  In the normalised situation `J 0 = stdOf T 0`, so `A` vanishes at the
origin and is small near it. -/
noncomputable def perturbation (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n) :
    E n → E n →L[ℝ] E n :=
  fun y => J y - stdOf T y

@[simp] lemma perturbation_apply (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n) (y v : E n) :
    perturbation J T y v = J y v - stdOf T y v := rfl

/-- The perturbation `L_A u = (i/2)·du ∘ A` of the `∂̄`-operator, as a `ℂ`-valued `(0,1)`-form
valued function. -/
noncomputable def dbarPert (A : E n → E n →L[ℝ] E n) (u : E n → ℂ) : E n → E n →L[ℝ] ℂ :=
  fun y => (Complex.I / 2) • ((fderiv ℝ u y).comp (A y))

@[simp] lemma dbarPert_apply (A : E n → E n →L[ℝ] E n) (u : E n → ℂ) (y v : E n) :
    dbarPert A u y v = (Complex.I / 2) * (fderiv ℝ u y (A y v)) := by
  simp [dbarPert, smul_eq_mul]

/-- Data of a `∂̄`-equation for a `ℂⁿ`-valued unknown: a family of `ℂ`-valued `(0,1)`-forms,
indexed by the coordinate. -/
abbrev DbarData (n : ℕ) := E n → Fin n → E n →L[ℝ] ℂ

/-- The perturbation operator applied to a `ℂⁿ`-valued function, componentwise. -/
noncomputable def dbarPertVec (A : E n → E n →L[ℝ] E n) (v : E n → Fin n → ℂ) : DbarData n :=
  fun y j => dbarPert A (fun z => v z j) y

@[simp] lemma dbarPert_perturbation (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n)
    (u : E n → ℂ) (y : E n) :
    dbarPert (perturbation J T) u y
      = (Complex.I / 2) • ((fderiv ℝ u y).comp (J y - stdOf T y)) := rfl

@[simp] lemma dbarPertVec_apply (A : E n → E n →L[ℝ] E n) (v : E n → Fin n → ℂ) (y : E n)
    (j : Fin n) : dbarPertVec A v y j = dbarPert A (fun z => v z j) y := rfl

/-- The tuple of standard coordinate functions, as a `ℂⁿ`-valued function. -/
noncomputable def zvec (T : E n ≃L[ℝ] F n) : E n → Fin n → ℂ := fun y j => zcoord T j y

@[simp] lemma zvec_apply (T : E n ≃L[ℝ] F n) (y : E n) (j : Fin n) :
    zvec T y j = zcoord T j y := rfl

/-- The differential of the tuple of standard coordinates: `y ↦ (zcoord T j y)_j`, a continuous
linear map `E n → (Fin n → ℂ)` obtained from `T` by identifying `F n` with coordinate space. -/
noncomputable def tupleDeriv (T : E n ≃L[ℝ] F n) : E n →L[ℝ] (Fin n → ℂ) :=
  (ecInvL n).comp (T : E n →L[ℝ] F n)

/-- The inverse of `tupleDeriv T`, as a continuous linear map. -/
noncomputable def tupleDerivInv (T : E n ≃L[ℝ] F n) : (Fin n → ℂ) →L[ℝ] E n :=
  (T.symm : F n →L[ℝ] E n).comp (ecL n)

/-- The condition number of the normalisation attached to `T`.  The contraction argument needs
the perturbation `A` to be small compared with the reciprocal of this number. -/
noncomputable def frameConst (T : E n ≃L[ℝ] F n) : ℝ :=
  ‖tupleDeriv T‖ * ‖tupleDerivInv T‖ + 1

/-! ## The two analytic inputs (legacy)

**WARNING (unsatisfiable interfaces).**  The two structures below, `FlatSolver` and `PertSolver`,
state the `∂̄`-estimate in *supremum* norms: "data bounded by `δ` in sup norm gives a solution with
`‖d(solve u)‖ ≤ C₀ δ`".  Such an operator does **not** exist, even for the flat structure on a disc
in `ℂ`: for `J = stdOf T` the correction `solve u` is determined by `∂̄_J(solve u) = ∂̄_Ju` only
modulo `J`-holomorphic functions, and the resulting operator (the Calderón–Zygmund transform
`∂Δ^{-1}∂`, of order `0`) is bounded on `L^p` and on the Hölder spaces `C^{0,α}` with `α > 0`, but
*not* on `L^∞`.  The structures are kept only because the first-order Neumann-series scheme of
`Contraction.lean`/`Limit.lean`/`Frame.lean` is a correct derivation from them; those four modules
should be regarded as superseded.

The honest interface is `Work.NN.Core.DbarSolverH` in `Solver.lean` (a Hölder-based estimate,
with the datum measured on a slightly larger set), and the reductions from it are in
`Solver.lean`/`Main.lean`. -/

/-- **The flat `∂̄`-solver (step 2 of the classical proof).**

`solve` is a right inverse of `∂̄_{stdOf T}` on the open set `P`, linear in the data, which gains
one derivative in sup norms (the `estimate` field, with constant `C₀`) and which produces smooth
solutions from smooth data (`smooth`).

*CAVEAT.*  Because `∂̄₀ ∘ ∂̄₀ = 0` (the flat operator has constant coefficients), the range of
`∂̄₀` consists of closed forms only, so such a `solve` exists only when *every* `(0,1)`-form on
`P` is `∂̄₀`-closed, e.g. on a disc in `ℂ` (`n = 1`, the Beltrami case), or on a domain of complex
dimension one.  For `n ≥ 2` no such operator exists, and the correct classical input is instead
the perturbed solver `PertSolver` below (Hörmander/Kohn's small polydisc estimates for the
*integrable* structure `J` itself, which solve `∂̄_J v = f` for `∂̄_J`-closed `f`, i.e. in
particular for `f = ∂̄_J u`).  `FlatSolver` is kept because it is exactly what the first-order
Neumann-series contraction of `Contraction.lean`/`Limit.lean` needs, and that contraction is
correct whenever such a solver exists. -/
structure FlatSolver (n : ℕ) (T : E n ≃L[ℝ] F n) (P : Set (E n)) where
  /-- the solution operator, linear in the data -/
  solve : DbarData n →ₗ[ℝ] (E n → Fin n → ℂ)
  /-- the constant in the gain-of-one-derivative estimate -/
  C₀ : NNReal
  /-- `solve` is a right inverse of `∂̄_{stdOf T}` -/
  solves : ∀ (f : DbarData n) (j : Fin n) (y : E n), y ∈ P →
    dbar (stdOf T) (fun z => solve f z j) y = f y j
  /-- gain of one derivative in sup norms: data bounded by `δ` on `P` gives a solution whose
  value and derivative are bounded by `C₀ * δ` on `P` -/
  estimate : ∀ (f : DbarData n) (δ : ℝ), 0 ≤ δ →
    (∀ (j : Fin n) (y : E n), y ∈ P → ‖f y j‖ ≤ δ) →
    ∀ (j : Fin n) (y : E n), y ∈ P →
      ‖solve f y j‖ ≤ (C₀ : ℝ) * δ ∧ ‖fderiv ℝ (fun z => solve f z j) y‖ ≤ (C₀ : ℝ) * δ
  /-- solutions with smooth data are smooth, locally: on any open `P' ⊆ P` on which the datum is
  smooth, the solution is smooth (local elliptic regularity for the flat `∂̄`-operator) -/
  smooth : ∀ (P' : Set (E n)), P' ⊆ P → IsOpen P' → ∀ f : DbarData n,
    (∀ j, ContDiffOn ℝ ∞ (fun y => f y j) P') → ContDiffOn ℝ ∞ (fun y => solve f y) P'

/-- **The perturbed `∂̄`-solver (steps 2–4 of the classical proof, in the form in which they are
classically available).**

`solve` corrects a function to a solution of the same `∂̄_J`-equation: `∂̄_J (solve u) = ∂̄_J u`.
The data `∂̄_J u` is exact, hence (when the Nijenhuis tensor of `J` vanishes, so that
`∂̄_J ∘ ∂̄_J = 0`) closed, which is exactly the class of data for which the classical small
polydisc estimates solve the equation.  The `estimate` field is the gain of one derivative:
if `‖∂̄_J u‖ ≤ δ` on `P` then `‖solve u‖ ≤ C₀ δ` and `‖d (solve u)‖ ≤ C₀ δ` on `P`; `smooth` is
the regularity statement (smooth data give smooth solutions).

Classically: on a small ball, the `∂̄`-equation for an integrable almost complex structure close
to the standard one, with a strictly plurisubharmonic weight, satisfies the Bochner–Kodaira–Nakano
estimate `‖∂̄v‖² + ‖∂̄^*v‖² ≥ t‖v‖²`; consequently the harmonic `(0,1)`-forms vanish, `∂̄` has
closed range `= ker ∂̄^*^⊥ ⊇ range ∂̄`, and `∂̄^* N` solves `∂̄ v = f` for `f ⊥ ker ∂̄^*`
(in particular for `f = ∂̄ u`, since `⟨∂̄u, η⟩ = ⟨u, ∂̄^*η⟩ = 0` for `∂̄^*η = 0`), with the
gain of one derivative after localising; interior Schauder estimates give the smoothness. -/
structure PertSolver (n : ℕ) (J : E n → E n →L[ℝ] E n) (P : Set (E n)) where
  /-- the correction: `solve u` solves the same `∂̄_J`-equation as `u` -/
  solve : (E n → Fin n → ℂ) → (E n → Fin n → ℂ)
  /-- the constant in the gain-of-one-derivative estimate -/
  C₀ : NNReal
  /-- `∂̄_J (solve u) = ∂̄_J u` -/
  solves : ∀ (u : E n → Fin n → ℂ) (j : Fin n) (y : E n), y ∈ P →
    dbar J (fun z => solve u z j) y = dbar J (fun z => u z j) y
  /-- gain of one derivative in sup norms -/
  estimate : ∀ (u : E n → Fin n → ℂ) (δ : ℝ), 0 ≤ δ →
    (∀ (j : Fin n) (y : E n), y ∈ P → ‖dbar J (fun z => u z j) y‖ ≤ δ) →
    ∀ (j : Fin n) (y : E n), y ∈ P →
      ‖solve u y j‖ ≤ (C₀ : ℝ) * δ ∧ ‖fderiv ℝ (fun z => solve u z j) y‖ ≤ (C₀ : ℝ) * δ
  /-- smooth data give a smooth correction -/
  smooth : ∀ u : E n → Fin n → ℂ, (∀ j, ContDiffOn ℝ ∞ (fun y => u y j) P) →
    ContDiffOn ℝ ∞ (fun y => solve u y) P

/-- **Interior regularity of `∂̄_J` (step 4 of the classical proof).**  A `C¹` solution of the
equation `∂̄_J u = f` whose datum `f` is smooth is smooth.  This is the classical hypoellipticity
of the overdetermined elliptic system `∂̄_J` (injective principal symbol, guaranteed by
`J y ∘ J y = -1`), and it does not use integrability. -/
structure DbarRegular (n : ℕ) (J : E n → E n →L[ℝ] E n) (P : Set (E n)) : Prop where
  smooth_of_dbar : ∀ u : E n → Fin n → ℂ,
    (∀ j, ∀ y ∈ P, DifferentiableAt ℝ (fun z => u z j) y) →
    (∀ j, ContDiffOn ℝ ∞ (fun y => dbar J (fun z => u z j) y) P) →
    ContDiffOn ℝ ∞ u P

/-! ## The conclusion -/

/-- `u : Fin n → E n → ℂ` is an independent `J`-holomorphic frame on `V`: the `u j` are smooth on
`V`, `J`-holomorphic there, and their joint differential is bijective at every point of `V`. -/
def IsHolomorphicFrame (J : E n → E n →L[ℝ] E n) (V : Set (E n))
    (u : Fin n → E n → ℂ) : Prop :=
  (∀ j, ContDiffOn ℝ ∞ (u j) V) ∧
  (∀ j, IsJHolomorphicOn J (u j) V) ∧
  (∀ y ∈ V, Function.Bijective (fderiv ℝ (fun y : E n => fun j => u j y) y))

lemma IsHolomorphicFrame.contDiff {J : E n → E n →L[ℝ] E n} {V : Set (E n)}
    {u : Fin n → E n → ℂ} (h : IsHolomorphicFrame J V u) (j : Fin n) :
    ContDiffOn ℝ ∞ (u j) V := h.1 j

lemma IsHolomorphicFrame.holomorphic {J : E n → E n →L[ℝ] E n} {V : Set (E n)}
    {u : Fin n → E n → ℂ} (h : IsHolomorphicFrame J V u) (j : Fin n) :
    IsJHolomorphicOn J (u j) V := h.2.1 j

lemma IsHolomorphicFrame.bijective {J : E n → E n →L[ℝ] E n} {V : Set (E n)}
    {u : Fin n → E n → ℂ} (h : IsHolomorphicFrame J V u) :
    ∀ y ∈ V, Function.Bijective (fderiv ℝ (fun y : E n => fun j => u j y) y) := h.2.2

/-- The conclusion of the analytic core in the shape of the challenge statement: each coordinate
is `J`-holomorphic in the sense `d(u j) ∘ J = i · d(u j)`. -/
theorem isHolomorphicFrame_iff (J : E n → E n →L[ℝ] E n) (V : Set (E n))
    (u : Fin n → E n → ℂ) :
    IsHolomorphicFrame J V u ↔
      (∀ j, ContDiffOn ℝ ∞ (u j) V) ∧
      (∀ j, ∀ y ∈ V, ∀ v : E n,
        fderiv ℝ (u j) y (J y v) = Complex.I * fderiv ℝ (u j) y v) ∧
      (∀ y ∈ V, Function.Bijective (fderiv ℝ (fun y : E n => fun j => u j y) y)) := by
  simp only [IsHolomorphicFrame, IsJHolomorphicOn, IsJHolomorphicAt, smul_eq_mul]

/-- The tuple of standard coordinates is smooth. -/
lemma contDiff_zvec (T : E n ≃L[ℝ] F n) : ContDiff ℝ ∞ (zvec T) := by
  rw [show zvec T = (tupleDeriv T : E n → Fin n → ℂ) from rfl]
  exact ContinuousLinearMap.contDiff (tupleDeriv T)

end Work.NN.Core
