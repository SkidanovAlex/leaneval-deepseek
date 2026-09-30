import Submission.Work.RiemLib.IndexIntrinsic2
import Submission.Work.RiemLib.Commons.Topology.continuousOn_Icc_of_continuousOn_pieces

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The polarised index integrand over a chart cover, and the corner pairing

This file completes the polarised chapter of `Submission/IndexIntrinsic2.lean` by assembling it over a
**finite chart cover** of the interval.  The bundled predicate

* `IsBilPiece` — the chart data of one piece: `γ` described by a chart geodesic `u`, the pair `(V,Z)`
  described by a chart Jacobi field and its covariant derivative, and the pair `(W,Y)` by an arbitrary
  chart field and its covariant derivative (with `ContinuousOn Wc'`);

supports the atomic lemmas

* `continuousOn_bilAlong_of_isBilPiece`, `integral_bilAlong_eq_sub_of_isBilPiece`,

and then

* `integral_bilAlong_eq_sub_of_pieces` — the telescoping over a partition;
* `integral_bilAlong_eq_sub_of_cover` — **the polarised FTC over a chart cover**;
* `integral_bilAlong_corner_of_cover` — **the corner pairing over a chart cover**:
  `W 0 = 0` ⟹ `∫_0^{t₀} bilAlong = ⟪∇J(t₀), W(t₀)⟫`;
* `continuousOn_bilAlong_of_cover` — global continuity of the integrand from a cover (this uses the
  shared commons lemma `Commons.Topology.continuousOn_Icc_of_continuousOn_pieces`).

The corner pairing is the quantity that contradicts the negative semidefiniteness of the index form of
a minimising geodesic in the "index-form" reformulation of the shortening argument (Roadmap §97.4);
what is still missing downstream is the global second-variation formula (Roadmap §97.9).
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
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.CurvatureVec
open Submission.CurvatureSym
open Submission.Rauch
open Submission.Gauss
open Submission.Curvature
open Submission.SecondVariation
open Submission.ChartBounds
open Submission.BonnetMyers
open Submission.IndexForm
open Submission.IndexForm2
open Submission.SecondVar2
open Submission.IndexCorner
open Submission.IndexCorner2
open Submission.ChartIndep
open Submission.IndexIntrinsic
open Submission.IndexIntrinsic2

namespace Submission.IndexIntrinsic3

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- The chart data of one piece of a cover on which `(V,Z)` is a Jacobi pair and `(W,Y)` an
arbitrary pair (the test field and its covariant derivative). -/
def IsBilPiece (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M)
    (V Z W Y : (t : ℝ) → TangentSpace I (γ t)) (a b A B : ℝ) : Prop :=
  ∃ (x₀ : M) (u w w' J J' J'' Wc Wc' : ℝ → E),
    A < a ∧ b < B ∧
    (∀ t ∈ Icc A B, γ t = (extChartAt I x₀).symm (u t)) ∧
    (∀ t ∈ Icc A B, HasDerivAt u (w t) t) ∧
    (∀ t ∈ Icc A B, HasDerivAt w (w' t) t) ∧
    (∀ t ∈ Icc A B, u t ∈ (extChartAt I x₀).target) ∧
    (∀ t ∈ Icc A B, HasDerivAt J (J' t) t) ∧
    (∀ t ∈ Icc A B, HasDerivAt J' (J'' t) t) ∧
    (∀ t ∈ Icc A B, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0) ∧
    (∀ t ∈ Icc A B, V t = frameVector (I := I) x₀ (γ t) (J t)) ∧
    (∀ t ∈ Icc A B, Z t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u J w J' t)) ∧
    (∀ t ∈ Icc A B, HasDerivAt Wc (Wc' t) t) ∧
    ContinuousOn Wc' (Icc A B) ∧
    (∀ t ∈ Icc A B, W t = frameVector (I := I) x₀ (γ t) (Wc t)) ∧
    (∀ t ∈ Icc A B, Y t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u Wc w Wc' t))

/-- The polarised integrand is continuous on a piece carrying `IsBilPiece` data. -/
theorem continuousOn_bilAlong_of_isBilPiece (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) {γ : ℝ → M} {V Z W Y : (t : ℝ) → TangentSpace I (γ t)}
    {a b A B : ℝ} (h : IsBilPiece (I := I) cov γ V Z W Y a b A B) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => bilAlong (cov := cov) γ V W Z Y t) (Icc a b) := by
  obtain ⟨x₀, u, w, w', J, J', J'', Wc, Wc', hA, hB, hγeq, hu, hw, htgt, hJ, hJ', hjac, hV, hZ,
    hW, hWc'c, hWh, hY⟩ := h
  exact continuousOn_bilAlong (cov := cov) hmet htor x₀ hA hab hB hγeq hu hw htgt hJ hJ' hV hZ hW
    hWh hY hWc'c

/-- The polarised FTC on one piece. -/
theorem integral_bilAlong_eq_sub_of_isBilPiece (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) {γ : ℝ → M} {V Z W Y : (t : ℝ) → TangentSpace I (γ t)}
    {a b A B : ℝ} (h : IsBilPiece (I := I) cov γ V Z W Y a b A B) (hab : a ≤ b) :
    ∫ t in a..b, bilAlong (cov := cov) γ V W Z Y t
      = inner ℝ (Z b) (W b) - inner ℝ (Z a) (W a) := by
  obtain ⟨x₀, u, w, w', J, J', J'', Wc, Wc', hA, hB, hγeq, hu, hw, htgt, hJ, hJ', hjac, hV, hZ,
    hW, hWc'c, hWh, hY⟩ := h
  exact integral_bilAlong_eq_sub (cov := cov) hmet htor x₀ hA hab hB hγeq hu hw htgt hJ hJ' hjac
    hV hZ hW hWh hY hWc'c

/-- Telescoping of the polarised FTC over a partition. -/
theorem integral_bilAlong_eq_sub_of_pieces {γ : ℝ → M}
    {V Z W Y : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ}
    {N : ℕ} {c : ℕ → ℝ} (hc0 : c 0 = a) (hcN : c N = b)
    (hint : ∀ k < N, IntervalIntegrable
      (fun t : ℝ => bilAlong (cov := cov) γ V W Z Y t) volume (c k) (c (k + 1)))
    (hpiece : ∀ k < N, ∫ t in (c k)..(c (k + 1)), bilAlong (cov := cov) γ V W Z Y t
        = inner ℝ (Z (c (k + 1))) (W (c (k + 1))) - inner ℝ (Z (c k)) (W (c k))) :
    ∫ t in a..b, bilAlong (cov := cov) γ V W Z Y t
      = inner ℝ (Z b) (W b) - inner ℝ (Z a) (W a) := by
  rw [← hc0, ← hcN]
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint,
    Finset.sum_congr rfl (fun k hk => hpiece k (Finset.mem_range.mp hk))]
  exact Finset.sum_range_sub (fun k => inner ℝ (Z (c k)) (W (c k))) N

/-- **The polarised FTC over a chart cover.** -/
theorem integral_bilAlong_eq_sub_of_cover (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) {γ : ℝ → M} {V Z W Y : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ}
    {N : ℕ} {c : ℕ → ℝ} {A B : ℕ → ℝ} (hc0 : c 0 = a) (hcN : c N = b)
    (hmono : ∀ k < N, c k ≤ c (k + 1))
    (hpiece : ∀ k < N, IsBilPiece (I := I) cov γ V Z W Y (c k) (c (k + 1)) (A k) (B k)) :
    ∫ t in a..b, bilAlong (cov := cov) γ V W Z Y t
      = inner ℝ (Z b) (W b) - inner ℝ (Z a) (W a) := by
  have hint : ∀ k < N, IntervalIntegrable (fun t : ℝ => bilAlong (cov := cov) γ V W Z Y t)
      volume (c k) (c (k + 1)) := fun k hk =>
    (continuousOn_bilAlong_of_isBilPiece (cov := cov) hmet htor (hpiece k hk)
      (hmono k hk)).intervalIntegrable_of_Icc (hmono k hk)
  exact integral_bilAlong_eq_sub_of_pieces (cov := cov) hc0 hcN hint
    (fun k hk => integral_bilAlong_eq_sub_of_isBilPiece (cov := cov) hmet htor (hpiece k hk)
      (hmono k hk))

/-- **The corner pairing over a chart cover.** -/
theorem integral_bilAlong_corner_of_cover (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) {γ : ℝ → M} {V Z W Y : (t : ℝ) → TangentSpace I (γ t)} {t₀ : ℝ}
    {N : ℕ} {c : ℕ → ℝ} {A B : ℕ → ℝ} (hc0 : c 0 = 0) (hcN : c N = t₀)
    (hmono : ∀ k < N, c k ≤ c (k + 1))
    (hpiece : ∀ k < N, IsBilPiece (I := I) cov γ V Z W Y (c k) (c (k + 1)) (A k) (B k))
    (hW0 : W 0 = 0) :
    ∫ t in (0 : ℝ)..t₀, bilAlong (cov := cov) γ V W Z Y t = inner ℝ (Z t₀) (W t₀) := by
  rw [integral_bilAlong_eq_sub_of_cover (cov := cov) hmet htor hc0 hcN hmono hpiece, hW0]
  simp

/-- **Global continuity of the polarised integrand over a chart cover** (this is where the commons
gluing lemma `Commons.Topology.continuousOn_Icc_of_continuousOn_pieces` is used). -/
theorem continuousOn_bilAlong_of_cover (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {V Z W Y : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ}
    {N : ℕ} {c : ℕ → ℝ} {A B : ℕ → ℝ} (hc0 : c 0 = a) (hcN : c N = b)
    (hmono : ∀ k < N, c k ≤ c (k + 1))
    (hpiece : ∀ k < N, IsBilPiece (I := I) cov γ V Z W Y (c k) (c (k + 1)) (A k) (B k)) :
    ContinuousOn (fun t : ℝ => bilAlong (cov := cov) γ V W Z Y t) (Icc a b) :=
  Commons.Topology.continuousOn_Icc_of_continuousOn_pieces hc0 hcN hmono
    (fun k hk => continuousOn_bilAlong_of_isBilPiece (cov := cov) hmet htor (hpiece k hk)
      (hmono k hk))

end

end Submission.IndexIntrinsic3
