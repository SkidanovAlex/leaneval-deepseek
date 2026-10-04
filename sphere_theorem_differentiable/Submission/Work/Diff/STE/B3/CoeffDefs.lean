/-
# The coefficient family of the transport: definitions

This module fixes the vocabulary for `Work.Diff.STE.B3.transport_exists_A_uniform`.

For the Layer B3 data `D`, a chart index `j` and a section `h`, the coefficient matrix `A` of the
transport identity is the inverse of the coordinate-frame chart matrix `Gf D h j` of `h`.  The
construction here is *global*: since the `g₀`-orthonormal frame `e i` of another chart `i` is
available at every point `p` with `‖coord_i p‖ ≤ 2 σ i`, the pointwise reconstruction identity
`Work.Diff.STE.B3.mat_recon_gen` expresses `h` at such a point in terms of the *localised component*
`D.R i h` (which carries all the `h`-dependence and whose flat jets are controlled by the hypothesis
`hjet` of the transport).  Summing over `i` with the *normalised weights* `ζ i ^ 2` (which satisfy
`Σ i, ζ i p ^ 2 = 1`) gives the global identity

`Gf D h j z = ∑ i, Gterm D h j i z`

(see `Gtot_identity`), where each summand `Gterm D h j i z` involves only `D.R i h` and the
`D`-dependent data `ζ i`, `χ i`, `dens i`, `coord i`, the frame vectors and `g₀`.

The main objects:

* `trCoef D j i z a c` — the coefficient of the coordinate-frame vector `∂_a` of the chart at
  `x₀ j` in the frame `e i`;
* `xiMap D j i z` — the flat coordinate of `D.pt j z` in the chart at `x₀ i`;
* `Gterm`, `Gtot` — the summands and the sum of the reconstruction;
* `thetaFun s d` — a smooth bump equal to `1` on `‖z‖ ≤ s` and supported in `‖z‖ < s + d / 4`;
* `perR f` — the real `1`-periodisation `z ↦ ∑' m, f (z + m)`;
* `Afun` — the coefficient matrix of the transport: the periodisation of the clamped inverse of
  `Gtot`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.TransportDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The coordinate-frame vector `∂_a` of the chart at `x₀ j` at the point `D.pt j z`. -/
def cFrameAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a : Fin (Module.finrank ℝ E)) : TangentSpace I (D.pt j z) :=
  Submission.Geodesic.frameVector (I := I) (D.x₀ j) (D.pt j z) (Work.Diff.EXT.bB (E := E) a)

/-- **The change-of-frame coefficient**: the coefficient of the coordinate-frame vector `∂_a` of the
chart at `x₀ j` in the frame `e i` at the point `D.pt j z`. -/
def trCoef (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a c : Fin (Module.finrank ℝ E)) : ℝ :=
  g₀.inner (D.pt j z) (cFrameAt (I := I) (M := M) D j z a) (D.e i c (D.pt j z))

/-- The flat coordinate of the point `D.pt j z` in the chart at `x₀ i`. -/
def xiMap (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) : Fin (Module.finrank ℝ E) → ℝ :=
  Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)

/-- **The `i`-th summand of the global reconstruction of `Gf`**: the localised component `D.R i h`
of the section, contracted with the change-of-frame coefficients, weighted by the normalised weight
`ζ i` and the reciprocal volume density. -/
def Gterm (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)) : ℝ :=
  D.ζ i (D.pt j z) * (Real.sqrt (D.dens i (xiMap (I := I) (M := M) D j i z)))⁻¹
    * ∑ c, ∑ d, trCoef (I := I) (M := M) D j i z a c * trCoef (I := I) (M := M) D j i z b d
        * D.R i h c d (xiMap (I := I) (M := M) D j i z)

/-- **The global reconstruction of `Gf`**: the sum of the `i`-th summands.  It agrees with the
coordinate-frame chart matrix of `h` (`Gtot_identity`), and each summand is built from the localised
component `D.R i h` and the `D`-dependent data only, which is what makes the jet bounds uniform in
`h`. -/
def Gtot (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ i : ι₀, Gterm (I := I) (M := M) D h j i z a b

/-- The `1`-periodisation of a function on `Fin n → ℝ`: `z ↦ ∑' m, f (z + m)`, `m` ranging over the
integer lattice.  For a function supported in a ball of radius `≤ 1 / 2` this is a locally finite
sum with at most one non-zero term at every point (so it is smooth with the same jet bounds as `f`,
see `perR_jet_bound`). -/
def perR {n : ℕ} (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun z => ∑' m : Fin n → ℤ, f (z + fun i => (m i : ℝ))

/-- A smooth bump equal to `1` on the closed ball of radius `s` and supported in the open ball of
radius `s + d / 4`. -/
def thetaFun {n : ℕ} (s d : ℝ) (z : Fin n → ℝ) : ℝ :=
  Real.smoothTransition ((s + d / 4 - ‖z‖) / (d / 4))

/-- **The coefficient matrix of the transport**: the clamped inverse `K` of the global
reconstruction `Gtot`, cut off by `theta` and periodised, added to the constant `lam' · 1`.  On the
`2 σ j`-ball it is the honest inverse of the chart matrix of `h`. -/
def Afun {n : ℕ} (θ : (Fin n → ℝ) → ℝ) (lam' : ℝ)
    (K : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ)) (G : (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (z : Fin n → ℝ) (p q : Fin n) : ℝ :=
  (if p = q then lam' else 0)
    + perR (fun w => θ w * (K (fun a b => G w a b) p q - (if p = q then lam' else 0))) z

end Work.Diff.STE.B3
