import Submission.Work.OddBound.IndexBound
import Submission.Work.OddBound.IndexDirichlet
import Submission.Work.OddBound.IndexPair
import Submission.Work.OddBound.strongIndex.not_dirichletIndexLeOne_of_parallelNormalPair
import Submission.Work.OddBound.exists_parallelNormalPair
import Submission.Work.OddBound.two_pi_div_sqrt_le_of_inj
import Submission.Work.OddBound.GExp_two_mul_eq_of_cutPointData
import Submission.Work.OddBound.curveSpeed_GExp_ray_eq_one
import Submission.Work.EvenBound.Attain.injSup_attained_of_lt_pi_div_sqrt
import Submission.RayConj
import Submission.KlingenbergEven
import Submission.KlingenbergLemma
import Submission.UniformInj

/-!
# The minimax route to Klingenberg's odd-dimensional length bound

This module assembles the **classical** proof of Klingenberg's injectivity-radius estimate in odd
dimensions (W. Klingenberg, *Über Riemannsche Mannigfaltigkeiten mit positiver Krümmung*, Comment.
Math. Helv. **35** (1961) 47–54; U. Abresch and W. T. Meyer, *Injectivity radius estimates and
sphere theorems*, MSRI Publ. **30** (1997), Theorem 1.6) from two ingredients:

* the **loop-space minimax** (`MinimaxInput`, below): from a short nontrivial geodesic digon the
  free-loop-space minimax (Condition C of Palais–Smale plus the degenerate Morse lemma of
  Gromoll–Meyer) produces a **long closed geodesic `c̄` of length `≥ 2π/√K` with Morse index `≤ 1`**
  — its lower bound is Klingenberg's **long homotopy lemma** (Klingenberg 1962; Abresch–Meyer
  Lemma 4.3), and its non-existence would contradict the minimax;
* the **index bound** `Work.OddBound.strongIndex.not_dirichletIndexLeOne_of_parallelNormalPair`
  (proved in
  `Submission/Work/OddBound/IndexBound.lean`), which shows that a geodesic of length
  `≥ π/√(K/4) = 2π/√K` whose curvature on the planes of a parallel normal pair is `≥ K/4 + ε`
  (`ε > 0`; this is what *strict* quarter-pinching gives, by compactness) has index `≥ 2`.

Together they give the odd-dimensional estimate in the **strictly** quarter-pinched case:

`Work.OddBound.klingenberg_length_bound_odd_strict`:
for a compact, connected, simply connected, odd-dimensional Riemannian manifold of dimension `≥ 3`
with `K/4 + ε ≤ sec ≤ K`, `0 < K < 4`, every closed geodesic loop has length `≥ 2π/√K`.

This is exactly the hypothesis of the challenge (`QuarterPinched cov` says `1 < sec ≤ 4`, so
`sec > K/4` at `K = 4`), and it removes the odd-specific holonomy input `HasRotatingFieldInput` of
`Submission/Work/OddBound/OddBound.lean` in favour of the classical minimax.

## The two forms of the input

`MinimaxInput hmet K` is stated for a **closed unit-speed geodesic `γ` of length `L < 2π/√K` whose
two halves are minimising** (a *nontrivial geodesic digon*: in the flush configuration of the
closest cut point, `γ` is the `ξ`-ray of length `2m`, and its two halves are the two minimising
geodesics between `p` and its closest cut point).  In the loop space `ΩM` of `M`, the minimax value
of a null-homotopy of `γ` is `≥ 2π/√K` by the long homotopy lemma, and its minimising sequence
subconverges to a closed geodesic `c̄` with `L(c̄) ≥ 2π/√K` and `IndexAtMostOne c̄ L(c̄)`.

Nothing in the classical proof of the minimax uses the conclusion of the odd-dimensional Klingenberg
estimate; the input is the *hard step* of Klingenberg 1961, isolated here as a single statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

namespace Work.OddBound

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## 1. The minimax input -/

/-! ## 0. The class of based null-homotopies and the long homotopy lower bound -/

/-- **The class of based null-homotopies** of a loop `γ` with base point `p`: a jointly smooth map
`H : ℝ × [0,1] → M` with `H (s+1) t = H s t` (closed curves), `H 0 t = p` (all curves based at `p`),
`H s 0 = γ (L * s)` (starting at the closed curve `γ`, parametrised by arclength over the period `L`)
and `H s 1 = p` (ending at the point curve).  These are exactly the
competing families of Klingenberg's minimax. -/
def SmoothBasedNullHomotopy (p : M) (L : ℝ) (γ : ℝ → M) (H : ℝ → ℝ → M) : Prop :=
  ContMDiff (𝓘(ℝ, ℝ × ℝ)) I ∞ (fun u : ℝ × ℝ => H u.1 u.2) ∧
    (∀ s t : ℝ, H (s + 1) t = H s t) ∧ (∀ t : ℝ, H 0 t = p) ∧
    (∀ s : ℝ, H s 0 = γ (L * s)) ∧ (∀ s : ℝ, H s 1 = p)

/-- **The long homotopy lower bound** (the conclusion of Klingenberg's long homotopy lemma).

It says that there is **no** based null-homotopy of `γ` in which both halves of every curve are
strictly shorter than `π/√K`: this is exactly the situation in which Klingenberg's lifting argument
(Klingenberg 1962 p. 50; Abresch--Meyer Lemma 4.3) applies and produces a contradiction.  It is
therefore the statement "every based null-homotopy of `γ` contains a curve of length
`≥ 2π/√K`", written in the contrapositive and in the *halved* form adapted to the lifting argument
(each curve is cut at its base point into the two arcs `[0,1/2]`, `[1/2,1]`; a homotopy whose curves
are parametrized proportionally to arclength and have total length `< 2π/√K` satisfies this).

This statement is **proved** in
`Submission/Work/OddBound/longHomotopy/long_homotopy_lower_bound.lean`
(`Work.OddBound.longHomotopy.long_homotopy_lower_bound`), from the lifting core
(`Work.OddBound.longHomotopy.lift_family_of_short`), the fact that the lift of a geodesic is a
straight ray (`Work.OddBound.longHomotopy.lift_of_geodesic_ray`) and the clopen step
(`Work.OddBound.longHomotopy.eq_at_zero_of_continuous_lift_eq`).  The proof (in the arclength
normalisation, `γ : ℝ → M` a smooth geodesic with `γ (t + L) = γ t`, `γ 0 = p` and nowhere vanishing
velocity) runs as follows.

* Let `h₁ s := γ (L * s)` and `h₂ s := γ (L * (1 - s))`; these are the two halves of the closed
  curve `s ↦ γ (L * s)` at its base point `p`, and `h₂ s = γ (-(L * s))` by the periodicity `hper`
  (`γ (L - L*s) = γ ((L - L*s) - L)`, i.e. use `hper` with `t = -(L * s)`).
* By `Work.OddBound.longHomotopy.lift_family_of_short` (the lifting core, applied with `S = 1/2`
  to the families `c₁ s t := H s t` and `c₂ s t := H (1 - s) t`) there are jointly continuous lifts
  `Wp`, `Wm` with `GExp p (Wp s t) = H s t`, `GExp p (Wm s t) = H (1 - s) t`, `Wp 0 t = Wm 0 t = 0`
  and the norm bounds `‖Wp s t‖ ≤ curveLength (H · t) 0 s`, `‖Wm s t‖ ≤ curveLength (H · t) (1 - s) 1`
  (`Work.OddBound.longHomotopy.curveLength_comp_sub` converts the half-length hypothesis for `c₂`).
* At `t = 0` the two lifts are the straight rays of the two halves
  (`Work.OddBound.longHomotopy.lift_of_geodesic_ray`, applied to `h₁` and `h₂`; the geodesic
  property of the halves follows from `KlingenbergEven.eq_GExp_of_isGeodesicAt` for `γ` and the
  periodicity of the `GExp`-ray, and the velocities are `L • curveVelocity γ 0` and its negative,
  by `Submission.Length.curveVelocity_comp_mul_add`):
  `Wp (1/2) 0 = (1/2) • (L • curveVelocity γ 0)` and `Wm (1/2) 0 = -((1/2) • (L • curveVelocity γ 0))`.
* At `t = 1`, `H · 1` is the point curve, so `Wp (1/2) 1 = Wm (1/2) 1 = 0` (again by
  `lift_of_geodesic_ray`, applied to the constant geodesic `s ↦ p`).
* The clopen step `Work.OddBound.longHomotopy.eq_at_zero_of_continuous_lift_eq`, applied to the
  continuous curves `t ↦ Wp (1/2) t`, `t ↦ Wm (1/2) t` (whose `GExp`-images agree because
  `H (1/2) t = H (1 - 1/2) t`), then gives `Wp (1/2) 0 = Wm (1/2) 0`.
* Comparing with the straight rays at `t = 0` gives `L • curveVelocity γ 0 = -(L • curveVelocity γ 0)`,
  hence `curveVelocity γ 0 = 0`, contradicting the hypothesis that the velocity never vanishes. -/
def LongHomotopyLowerBound (K : ℝ) (p : M) (L : ℝ) (γ : ℝ → M) : Prop :=
  ∀ H : ℝ → ℝ → M, SmoothBasedNullHomotopy (I := I) p L γ H →
    (∀ t ∈ Icc (0 : ℝ) 1,
      curveLength (I := I) (fun s : ℝ => H s t) 0 (1 / 2) < Real.pi / Real.sqrt K ∧
      curveLength (I := I) (fun s : ℝ => H s t) (1 / 2) 1 < Real.pi / Real.sqrt K) →
    False

/-! ## 0bis. The minimax extraction (the isolated Morse-theoretic input) -/

/-- **The minimax extraction**: Klingenberg's loop-space minimax, isolated as the single remaining
classical input.

Given a closed unit-speed geodesic loop `γ` at `p` whose based null-homotopies all contain a curve of
length `≥ 2π/√K` (the hypothesis `LongHomotopyLowerBound`, a *theorem* here), the minimax on the
based loop space `Ω_p M` produces a closed unit-speed geodesic loop `c` at `p` of length `≥ 2π/√K`
with **Morse index at most one** (`DirichletIndexLeOne`, `Submission/Work/OddBound/IndexPair.lean`):

> there is no two-dimensional space of smooth fields along `c`, vanishing at both ends, on which the
> index form is negative definite.

(This is the *correct* form of the index conclusion; the earlier `DirichletIndexAtMostOne` —
"any two fields with negative index integral are proportional" — is strictly stronger and is *not*
what a minimax yields, see the docstring of `IndexPair`.)

This is the content of Palais--Smale Condition C for the energy functional on the based loop space
together with the minimax principle (Birkhoff 1927; Klingenberg 1961; Gromoll--Meyer 1969 for the
degenerate Morse lemma; Abresch--Meyer Remark 4.4).  It is **not** a consequence of the pinching
hypothesis and its proof uses neither the pinching nor the dimension: it is a general theorem of the
calculus of variations on loop spaces.

Everything else in the odd-dimensional Klingenberg estimate is proved in this directory; in
particular `MinimaxInput` follows from `MinimaxExtraction` plus the long homotopy lemma
(`Work.OddBound.minimaxInput_of_extraction`). -/
def MinimaxExtraction (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (K : ℝ) : Prop :=
  SimplyConnectedSpace M →
  Submission.RauchK.CurvLe cov K → 0 < K →
  ∀ {p : M} {γ : ℝ → M} {L : ℝ}, 0 < L → L < 2 * Real.pi / Real.sqrt K →
    ContMDiff 𝓘(ℝ) I ∞ γ →
    (∀ t : ℝ, IsGeodesicAt (I := I) cov γ t) →
    (∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0) →
    (∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1) →
    γ L = γ 0 → γ 0 = p →
    (∀ t : ℝ, γ (t + L) = γ t) →
    LongHomotopyLowerBound (I := I) K p L γ →
    ∃ (T : ℝ) (c : ℝ → M),
      2 * Real.pi / Real.sqrt K ≤ T ∧ c T = c 0 ∧
      ContMDiff 𝓘(ℝ) I ∞ c ∧
      (∀ t : ℝ, IsGeodesicAt (I := I) cov c t) ∧
      (∀ t : ℝ, curveVelocity (I := I) c t ≠ 0) ∧
      (∀ t ∈ Icc (0 : ℝ) T, curveSpeed (I := I) c t = 1) ∧
      DirichletIndexLeOne (I := I) (cov := cov) c T

/-- **The minimax input of the odd-dimensional Klingenberg estimate.**  For a compact, simply
connected `M` with `sec ≤ K` (`0 < K`) and a closed **unit-speed** geodesic `γ` of length
`L < 2π/√K` whose two halves are minimising geodesics between their endpoints (a *nontrivial geodesic
digon*), the free-loop-space minimax produces a closed unit-speed geodesic `c` of length
`T ≥ 2π/√K` with **Morse index at most one** (`DirichletIndexLeOne`).

This is Klingenberg 1961's step, in the form the classical proof uses.  It is the conjunction of two
pieces: the *lower bound* on `T` is the long homotopy lemma (proved in
`Submission/Work/OddBound/LongHomotopy.lean`), and the *existence of `c` with index `≤ 1`* is the
loop-space minimax (`MinimaxExtraction`, the isolated Morse-theoretic input).  `MinimaxInput` follows
from those two (`Work.OddBound.minimaxInput_of_extraction`).  It is **not** a consequence of the
sphere theorem and its proof uses neither the pinching hypothesis nor the dimension. -/
def MinimaxInput (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (K : ℝ) : Prop :=
  SimplyConnectedSpace M →
  Submission.RauchK.CurvLe cov K → 0 < K →
  ∀ {γ : ℝ → M} {L : ℝ}, 0 < L → L < 2 * Real.pi / Real.sqrt K →
    ContMDiff 𝓘(ℝ) I ∞ γ →
    (∀ t : ℝ, IsGeodesicAt (I := I) cov γ t) →
    (∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0) →
    (∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1) →
    γ L = γ 0 →
    (∀ t : ℝ, γ (t + L) = γ t) →
    Manifold.riemannianEDist I (γ 0) (γ (L / 2)) = ENNReal.ofReal (L / 2) →
    ∃ (T : ℝ) (c : ℝ → M),
      2 * Real.pi / Real.sqrt K ≤ T ∧ c T = c 0 ∧
      ContMDiff 𝓘(ℝ) I ∞ c ∧
      (∀ t : ℝ, IsGeodesicAt (I := I) cov c t) ∧
      (∀ t : ℝ, curveVelocity (I := I) c t ≠ 0) ∧
      (∀ t ∈ Icc (0 : ℝ) T, curveSpeed (I := I) c t = 1) ∧
      DirichletIndexLeOne (I := I) (cov := cov) c T

/-! ## 2. The injectivity-radius estimate in the strictly pinched case -/

/-- **The odd-dimensional Klingenberg estimate from the minimax input, strictly pinched form.**
`3 ≤ finrank ℝ E`, `sec ≥ K/4 + ε` with `ε > 0` and `sec ≤ K`, `0 < K`.  Then the injectivity radius
is at least `π/√K`.

The proof is the classical one: suppose `injSup < π/√K`; Xu's theorem gives the flush configuration
at an attained closest cut point, whose `ξ`-ray `γ` is a nontrivial geodesic digon of length
`2m < 2π/√K`.  The minimax input produces a long closed geodesic `c̄` of index `≤ 1`; the index bound
(whose Dirichlet fields are the `sin (π · / L) • X_j` of two parallel orthonormal normal fields,
`Work.OddBound.exists_parallelNormalPair`) contradicts the index bound because
`L(c̄) ≥ 2π/√K = π/√(K/4)` and the curvature is `≥ K/4 + ε` on all orthonormal pairs. -/
theorem injAllAtLeast_pi_div_sqrt_odd_of_minimaxInput
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hDim : 3 ≤ Module.finrank ℝ E)
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 + ε ≤ inner ℝ (curvVec cov p u v v) u)
    (hminimax : MinimaxInput (I := I) (cov := cov) hmet htor K) :
    InjAllAtLeast hmet (Real.pi / Real.sqrt K) := by
  classical
  suffices hle : Real.pi / Real.sqrt K ≤ Submission.InjSup.injSup hmet by
    intro x
    exact Submission.InjRadius.injAtLeast_mono (I := I) hmet
      (Submission.InjSup.injAllAtLeast_injSup (I := I) hmet x) hle
  by_contra hcon
  push_neg at hcon
  -- ## the flush configuration at an attained closest cut point
  obtain ⟨p, hattain1, hmax⟩ :=
    Work.EvenBound.Attain.injSup_attained_of_lt_pi_div_sqrt (I := I) (cov := cov) hmet htor
      hcurv hK hcon
  obtain ⟨ρ, hρpos, hρall⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  obtain ⟨R, -, hR⟩ := Submission.CutTime.exists_edist_le (I := I) (cov := cov) hmet htor p
  have hbdd : BddAbove {r : ℝ | InjAllAtLeast hmet r} :=
    Submission.InjSup.bddAbove_injAllAtLeast_of_diam_le (I := I) (cov := cov) hmet htor hR
  have hm0 : 0 < Submission.InjSup.injSup hmet := by
    have : ρ ≤ sSup {r : ℝ | InjAllAtLeast hmet r} := le_csSup hbdd hρall
    exact lt_of_lt_of_le hρpos this
  have hinjall : InjAllAtLeast hmet (Submission.InjSup.injSup hmet) :=
    Submission.InjSup.injAllAtLeast_injSup (I := I) hmet
  obtain ⟨ξ, η, hξ, hη, hξη, hmeet, -, -, -, -, -, hmin1, hmin2⟩ :=
    Submission.RayConj.exists_broken_minimising_loop_of_injAtLeast_of_lt_pi_div_sqrt
      (I := I) (cov := cov) hmet htor hcurv hK hm0 hcon hattain1 hmax
  have hminξ : Manifold.riemannianEDist I p
      (GExp (cov := cov) hmet p (Submission.InjSup.injSup hmet • ξ))
      = ENNReal.ofReal (Submission.InjSup.injSup hmet) :=
    hmin1 (Submission.InjSup.injSup hmet) ⟨hm0.le, le_rfl⟩
  have hminη : Manifold.riemannianEDist I p
      (GExp (cov := cov) hmet p (Submission.InjSup.injSup hmet • η))
      = ENNReal.ofReal (Submission.InjSup.injSup hmet) := by
    have h := hmin2 0 ⟨le_rfl, hm0.le⟩
    rw [sub_zero] at h
    exact h
  have hper : ∀ u : ℝ,
      GExp (cov := cov) hmet p ((u + 2 * Submission.InjSup.injSup hmet) • ξ)
        = GExp (cov := cov) hmet p (u • ξ) :=
    Submission.KlingenbergEven.ray_periodic_of_two_minimising (I := I) (cov := cov) hmet htor
      hcurv hK hm0 hcon hattain1 hmax hinjall hξ hη hξη hmeet hminξ hminη
  have hξne : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξ
    norm_num at hξ
  -- ## the unit-speed ray of `ξ` is a nontrivial geodesic digon of length `2m`
  have hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t :=
    fun t => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξne t
  have hneΓ : ∀ t : ℝ,
      curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t ≠ 0 :=
    fun t => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξne t
  have hspeedΓ : ∀ t ∈ Icc (0 : ℝ) (2 * Submission.InjSup.injSup hmet),
      curveSpeed (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t = 1 :=
    fun t _ => curveSpeed_GExp_ray_eq_one (cov := cov) hmet hξ t
  have hclosedΓ : (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
        (2 * Submission.InjSup.injSup hmet)
      = (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) 0 := by
    show GExp (cov := cov) hmet p ((2 * Submission.InjSup.injSup hmet) • ξ)
      = GExp (cov := cov) hmet p ((0 : ℝ) • ξ)
    rw [zero_smul, GExp_zero]
    exact GExp_two_mul_eq_of_cutPointData (cov := cov) hmet htor hcurv hK hm0 hcon
      hattain1 hmax hξ hη hξη hmeet hminξ hminη
  have hhalfΓ : Manifold.riemannianEDist I
        ((fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) 0)
        ((fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
          ((2 * Submission.InjSup.injSup hmet) / 2))
      = ENNReal.ofReal ((2 * Submission.InjSup.injSup hmet) / 2) := by
    have harg : (2 * Submission.InjSup.injSup hmet) / 2 = Submission.InjSup.injSup hmet := by ring
    rw [harg]
    show Manifold.riemannianEDist I (GExp (cov := cov) hmet p ((0 : ℝ) • ξ))
      (GExp (cov := cov) hmet p (Submission.InjSup.injSup hmet • ξ)) = _
    rw [zero_smul, GExp_zero]
    exact hminξ
  -- ## the minimax
  have hlt : 2 * Submission.InjSup.injSup hmet < 2 * Real.pi / Real.sqrt K := by
    rw [mul_div_assoc]
    linarith
  have hγsm : ContMDiff 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hξne
  obtain ⟨T, c, hT, hc0, hcsm, hcgeo, hcne, hcsp, hidx⟩ :=
    hminimax ‹SimplyConnectedSpace M› hcurv hK (by positivity) hlt hγsm hgeo hneΓ hspeedΓ
      hclosedΓ (by simpa using hper) hhalfΓ
  -- ## the index bound
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
  obtain ⟨hp⟩ :=
    exists_parallelNormalPair (I := I) (cov := cov) hmet htor (contMDiffOn_univ.mpr hcsm) hcgeo
      hcne (by linarith) hDim
  have hπeq : Real.pi / Real.sqrt (K / 4) = 2 * Real.pi / Real.sqrt K := by
    have h4 : Real.sqrt (K / 4) = Real.sqrt K / 2 := by
      rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ K) 4]
      norm_num
    rw [h4]
    field_simp
  have hπlt : Real.pi / Real.sqrt (K / 4 + ε) < Real.pi / Real.sqrt (K / 4) := by
    refine div_lt_div_of_pos_left Real.pi_pos (Real.sqrt_pos.mpr (by positivity)) ?_
    exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hπ' : Real.pi / Real.sqrt (K / 4 + ε) < T := by
    rw [hπeq] at hπlt
    linarith
  exact not_dirichletIndexLeOne_of_dirichletIndexNotLeOne (I := I) (cov := cov)
    (strongIndex.not_dirichletIndexLeOne_of_parallelNormalPair (I := I) (cov := cov) hmet htor
      (contMDiffOn_univ.mpr hcsm) hcne hTpos hcsp (by positivity) hε hπ'
      (fun t _ u v hu hv huv => hpinch (c t) u v hu hv huv) hp) hidx


/-! ## 3. The length bound -/

/-- **Klingenberg's length bound in odd dimensions, strictly quarter-pinched form.**

For a compact, connected, simply connected Riemannian manifold of odd dimension `≥ 3` (the `Odd`
hypothesis of the requested statement implies `≥ 3` once `2 ≤ finrank`, as in the challenge) with
`K/4 + ε ≤ sec ≤ K` and `0 < K`, every closed geodesic loop has length `≥ 2π/√K`.

The hypothesis `K/4 + ε ≤ sec` (`ε > 0`, a *uniform* margin) is Klingenberg 1961's "strictly
quarter-pinched" condition: on a compact manifold the pointwise strict inequality `K/4 < sec`
(pinching ratio `< 4`, which is exactly the challenge's `1 < sec ≤ 4` at `K = 4`) upgrades to a
uniform margin by compactness of the unit tangent bundle.  The remaining input is the loop-space
minimax `MinimaxInput K`. -/
theorem klingenberg_length_bound_odd_strict_of_minimaxInput
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hDim : 3 ≤ Module.finrank ℝ E)
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 + ε ≤ inner ℝ (curvVec cov p u v v) u)
    (hminimax : MinimaxInput (I := I) (cov := cov) hmet htor K) :
    ∀ {p : M} {T : ℝ} {γ : ℝ → M},
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt (I := I) hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T := by
  intro p T γ hloop
  have hInj : InjAtLeast hmet p (Real.pi / Real.sqrt K) :=
    Submission.InjRadius.injAtLeast_of_injAllAtLeast (I := I) hmet
      (injAllAtLeast_pi_div_sqrt_odd_of_minimaxInput (I := I) (cov := cov) hmet htor hDim hK hε
        hcurv hpinch hminimax) p
  exact two_pi_div_sqrt_le_of_inj (cov := cov) hmet htor hK hloop hInj le_rfl

/-! ## 4. `MinimaxInput` from the extraction plus the (proved) long homotopy lemma -/

/-- **`MinimaxInput` from the isolated Morse-theoretic input and the long homotopy lemma.**

The minimax extraction (`MinimaxExtraction`) already takes the *value bound* as its hypothesis, in the
form of `LongHomotopyLowerBound`; that hypothesis is a **theorem** here
(`Work.OddBound.longHomotopy.long_homotopy_lower_bound`, module
`Submission.Work.OddBound.longHomotopy.long_homotopy_lower_bound`, proved from the lifting core and
the clopen argument).  Hence `MinimaxInput` follows from
`MinimaxExtraction` alone, and the whole odd-dimensional Klingenberg estimate follows from the
minimax extraction plus statements proved in this directory. -/
theorem minimaxInput_of_extraction
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hext : MinimaxExtraction (I := I) (cov := cov) hmet htor K)
    (hlhl : ∀ {p : M} {γ : ℝ → M} {L : ℝ}, 0 < L →
      ContMDiff 𝓘(ℝ) I ∞ γ → (∀ t : ℝ, IsGeodesicAt (I := I) cov γ t) →
      (∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0) → (∀ t : ℝ, γ (t + L) = γ t) → γ 0 = p →
      LongHomotopyLowerBound (I := I) K p L γ) :
    MinimaxInput (I := I) (cov := cov) hmet htor K := by
  intro hsc hcurv hK γ L hL hLπ hγsm hgeo hne hspeed hclosed hper hhalf
  exact hext hsc hcurv hK hL hLπ hγsm hgeo hne hspeed hclosed rfl hper
    (hlhl hL hγsm hgeo hne hper rfl)


end

end Work.OddBound

