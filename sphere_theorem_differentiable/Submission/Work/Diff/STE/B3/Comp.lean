import Mathlib
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.friedrichs_commutator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the component maps `R_i`, the composite pairing and norm, and the mollifier `J_ε`

Fix Layer B3 data `D` (`B3Data ι₀ g₀`, see `B3/Data.lean`): chart centres `x₀ i`, radii `σ i`,
cut-offs `χ i`, normalised weights `ζ i`, a `g₀`-orthonormal frame `e i a`, and the volume
densities `dens i`.  This file sets up the analytic objects of the global Galerkin scheme.

* `D.mat i h a b z`: the chart matrix of a section `h : Bil` in the orthonormal frame `e i`, at the
  point `D.pt i z` with flat coordinate `z`;
* `D.R i h a b`: the **localised component** `ψ i z * mat i h a b z` with `ψ i = χ i * ζ i ∘ pt i`
  (`B3Data.psi`); it is supported in the open unit cube, so its periodisation is smooth and
  `1`-periodic, and it is the function to which Layer A applies;
* `D.Rper i h a b`: the **periodisation** of the localised component (a `1`-periodic `ℂ`-valued
  function);
* `D.CPair i u v`: the component pairing `Σ_{ab} ∫_{cube} u_{ab} v_{ab} · dens i`, i.e. the
  `L²(g₀)` pairing of the chart-`i` matrix entries against `dvol`;
* `D.BPair h k`: the **composite pairing** `Σ_i CPair_i (R_i h) (R_i k)`, which the normalisation
  `Σ_i ζ_i² = 1` makes equal to the intrinsic pairing `∫_M (h : k)_{g₀} dvol` (this is
  `Work.Diff.STE.B3.BPair_eq_intrinsic`, delegated);
* `D.BNorm k h`: the **composite norm** `Σ_i Σ_{ab} CSq k (fourierCoeff (Rper i h a b))`;
* `D.Rstar i u`: the **reconstruction** `p ↦ ζ i p · Σ_{ab} u_{ab}(coord i p) · e^a ♭ ⊗ e^b ♭`;
* `D.J ρ ε h`: the **Friedrichs mollifier** `Σ_i R_i*(S_ε (R_i h))`.

The three analytic facts about this vocabulary (all delegated, since they are independent):
`Rper` is smooth and `1`-periodic, the adjunction `BPair (Rstar i u) k = CPair i u (R i k)`, and the
Friedrichs commutator estimate for `J`.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

namespace B3Data

variable (D : B3Data (I := I) (M := M) ι₀ g₀)

/-- **The chart matrix of a section** in the `g₀`-orthonormal frame of chart `i`, at the point with
flat coordinate `z`. -/
def mat (i : ι₀) (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) : ℝ :=
  h (D.pt i z) (D.e i a (D.pt i z)) (D.e i b (D.pt i z))

/-- **The chart matrix of a section in chart coordinates** (`y : E` ranging over the chart target):
this is `D.mat` with the flat coordinate replaced by the chart coordinate, so that it matches the
smoothness hypothesis of the B2 sibling `Work.Diff.STE.fill.contDiff_bilPer_of_bump`. -/
def matChart (i : ι₀) (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => h ((extChartAt I (D.x₀ i)).symm y)
    (D.e i a ((extChartAt I (D.x₀ i)).symm y)) (D.e i b ((extChartAt I (D.x₀ i)).symm y))

/-- `D.mat` is `D.matChart` composed with the affine flat coordinate. -/
lemma mat_eq_matChart (i : ι₀) (h : Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) :
    D.mat i h a b z = D.matChart i h a b (flatToE (I := I) (D.x₀ i) z) := rfl

/-- `D.mat` as a function is `D.matChart` composed with the affine flat coordinate. -/
lemma mat_eq (i : ι₀) (h : Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) :
    D.mat i h a b
      = fun z => D.matChart i h a b (flatToE (I := I) (D.x₀ i) z) := rfl

/-- **The localised component** `R_i h` of a section: the chart matrix times the localised weight
times the *square root* of the volume density.  The square root is essential: it makes the
component pairing `CPair i` below the *unweighted* `L²` pairing, for which the Fourier truncation
`STruncR` is self-adjoint (a real Fourier multiplier), while `BPair` is still the intrinsic
`L²(g₀)` pairing.  (With the density sitting in `CPair` instead, `STruncR` would not be
self-adjoint and the mollifier `J` would not be either.) -/
def R (i : ι₀) (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) : ℝ :=
  D.psi i z * Real.sqrt (D.dens i z) * D.mat i h a b z

/-- **The periodisation** of the localised component: a `1`-periodic `ℂ`-valued function, to which
the whole Fourier theory of Layer A applies. -/
def Rper (i : ι₀) (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
  fun z => ∑' m : Fin (Module.finrank ℝ E) → ℤ,
    ((D.R i h a b (z + iVec m) : ℝ) : ℂ)

/-- The **centred** unit cube `(-1/2,1/2]^n`, the fundamental domain on which the localised
component `R i` lives: `B3Data.hχsupp` puts `support (χ i)` (hence `support (R i h a b)`) inside
the open centred cube, so an integral over `centreCube` agrees with the integral over any other
fundamental domain, in particular with the one used to define the Fourier coefficients.  (The
*positive* cube `unitCube = (0,1]^n` of `Work.Diff.STE` sees only part of the support and must NOT
be used for the pairing.) -/
def centreCube : Set (Fin (Module.finrank ℝ E) → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))

/-- **The component pairing** of two families of component functions: the *unweighted* `L²`
pairing of the component functions over the centred fundamental cube.  It is unweighted on purpose,
so that the Fourier truncation `STruncR` (a real Fourier multiplier) is self-adjoint for it; the
volume density is carried by the components `R i` themselves. -/
def CPair (i : ι₀)
    (u v : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) : ℝ :=
  ∑ a, ∑ b, ∫ z in centreCube (E := E), u a b z * v a b z

/-- **The composite pairing** of two sections. -/
def BPair (h k : Bil (I := I) (M := M)) : ℝ :=
  ∑ i, CPair i (D.R i h) (D.R i k)

/-- **The composite `Hᵏ` norm** of a section. -/
def BNorm (k : ℕ) (h : Bil (I := I) (M := M)) : ℝ :=
  ∑ i, ∑ a, ∑ b, CSq k (fourierCoeff (D.Rper i h a b))

/-- **The reconstruction** of a section from a family of component functions.

The coefficient is `ζ i p · χ i (coord i p) · (√(dens i (coord i p)))⁻¹ · u a b (coord i p)`.
The factor `ζ i p` is essential: it makes the section vanish identically off the support of `ζ i`,
where the values of `coord i` (hence of `χ i (coord i p)`, `dens i (coord i p)` and
`u a b (coord i p)`) are the *junk* values of the partial chart maps.  On the support of `ζ i` the
coefficient equals `ψ i (coord i p) · (√(dens i (coord i p)))⁻¹ · u a b (coord i p)`, which is what
the adjunction `BPair_Rstar` requires. -/
def Rstar (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) : Bil (I := I) (M := M) :=
  fun p => ∑ a, (g₀.inner p (D.e i a p)).smulRight
    (∑ b, (D.ζ i p * D.χ i (coord (I := I) (D.x₀ i) p)
        * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)))⁻¹
        * u a b (coord (I := I) (D.x₀ i) p)) • g₀.inner p (D.e i b p))

/-- The **Friedrichs truncation** of a real function: the `1`-periodic function whose Fourier
coefficients are `ρ (ε m) · ĝ(m)`, where `ĝ` are the Fourier coefficients of the **periodisation**
`Σ_m f (· + m)` of `f` (taken in the real part, which is legitimate for a real symmetric coefficient
family and a real multiplier `ρ`).

Taking the coefficients of the *periodisation* (and not simply the integral of `f` over the positive
cube `unitCube`) is essential: the components `R i h a b` are supported in the *centred* cube
`centreCube`, so an integral over `unitCube` sees only part of the support and `STruncR` would fail
to be self-adjoint for the pairing `CPair`.  With `per f(z) = Σ_m f (z + m)` one has
`fourierCoeff (per f) m = ∫_{ℝⁿ} e_{-2πi m·z} f z dz`, which is the right notion. -/
def STruncR (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun z => (seriesFun (trunc ρ ε (fourierCoeff fun y =>
    ∑' m : Fin (Module.finrank ℝ E) → ℤ, ((f (y + iVec m) : ℝ) : ℂ))) z).re

/-- **The Friedrichs mollifier** `J_ε = Σ_i R_i* (S_ε (R_i ·))`. -/
def J (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (h : Bil (I := I) (M := M)) : Bil (I := I) (M := M) :=
  ∑ i, D.Rstar i (fun a b z => B3Data.STruncR ρ ε (D.R i h a b) z)

end B3Data

end Work.Diff.STE
