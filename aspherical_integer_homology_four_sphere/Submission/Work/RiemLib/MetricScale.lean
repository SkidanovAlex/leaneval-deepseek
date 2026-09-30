import Submission.Work.RiemLib.PinchUniform
import Submission.Work.RiemLib.Commons.Geometry.Manifold.Riemannian.exists_scaleMetric
import Submission.Work.RiemLib.Commons.Geometry.Manifold.Riemannian.metricCompatible_scaleMetric

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Scaling the Riemannian metric by a constant

`Submission.PinchUniform` produces a constant `c > 1` strictly below every sectional curvature.
Scaling the metric by `c` (i.e. `g' = c · g`, so `⟪·,·⟫' = c ⟪·,·⟫`) turns a pointwise strictly
quarter-pinched metric into one with sectional curvature in `(1, 4/c]`, which is exactly what
Grove–Shiohama and Klingenberg's estimate ask for (with the strict upper bound `4/c < 4`).

Because comparing two `RiemannianBundle` instances on the same bundle is delicate, the transfers
below are stated for the *instance-free* forms `QuarterPinchedFor g` / `IsMetricCompatibleFor g`,
which spell out the fibres through `g.inner`; the conversion to the typeclass-level predicates
`QuarterPinched` / `IsMetricCompatible` is a definitional identity (`…_iff`).

## Main results

* `quarterPinchedFor`, `isMetricCompatibleFor`: instance-free versions of the two predicates;
* `quarterPinchedFor_iff`, `isMetricCompatibleFor_iff`: agreement with the typeclass versions;
* `quarterPinched_pointwise_le`: `sec ≤ 4` for arbitrary orthonormal pairs;
* `isMetricCompatibleFor_scale`, `quarterPinchedFor_scale`: the two transfers.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Curvature
open Submission.CurvatureVec
open Commons.Geometry.Manifold.VectorField
open Commons.Geometry.Manifold.Riemannian

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [hamb : RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.MetricScale

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- The ambient fibre metric evaluated as `g.inner`. -/
lemma inner_eq_g (x : M) (v w : TangentSpace I x) :
    inner ℝ v w = hamb.g.inner x v w := rfl

/-- The ambient fibre metric is linear in its first slot. -/
lemma inner_smul_left (p : M) (a : ℝ) (w z : TangentSpace I p) :
    hamb.g.inner p (a • w) z = a * hamb.g.inner p w z := by
  simp only [map_smul, smul_apply, smul_eq_mul]

/-- The ambient fibre metric is linear in its second slot. -/
lemma inner_smul_right (p : M) (b : ℝ) (w z : TangentSpace I p) :
    hamb.g.inner p w (b • z) = b * hamb.g.inner p w z := by
  simp only [map_smul, smul_apply, smul_eq_mul]

/-- The ambient fibre metric is bilinear in its two slots. -/
lemma inner_smul_smul (p : M) (a b : ℝ) (w z : TangentSpace I p) :
    hamb.g.inner p (a • w) (b • z) = a * b * hamb.g.inner p w z := by
  rw [inner_smul_left, inner_smul_right]
  ring

/-! ## Instance-free forms of the two predicates -/

/-- **Quarter pinching, spelled out through `g.inner`.** -/
def QuarterPinchedFor (g : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ (X Y : Π x : M, TangentSpace I x), CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) → ∀ x : M,
    g.inner x (X x) (X x) = 1 → g.inner x (Y x) (Y x) = 1 → g.inner x (X x) (Y x) = 0 →
    (1 : ℝ) < g.inner x (curv cov X Y Y x) (X x) ∧
      g.inner x (curv cov X Y Y x) (X x) ≤ (4 : ℝ)

/-- **Metric compatibility, spelled out through `g.inner`.** -/
def IsMetricCompatibleFor (g : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ (Y Z : Π x : M, TangentSpace I x), CMDiff ∞ (T% Y) → CMDiff ∞ (T% Z) →
    ∀ (x : M) (v : TangentSpace I x),
      mvfderiv I (fun y : M => g.inner y (Y y) (Z y)) x v
        = g.inner x (cov Y x v) (Z x) + g.inner x (Y x) (cov Z x v)

/-- The instance-free form of `QuarterPinched` agrees with it. -/
theorem quarterPinchedFor_iff :
    QuarterPinched cov ↔ QuarterPinchedFor hamb.g cov := Iff.rfl

/-- The instance-free form of `IsMetricCompatible` agrees with it. -/
theorem isMetricCompatibleFor_iff :
    IsMetricCompatible cov ↔ IsMetricCompatibleFor hamb.g cov := Iff.rfl

/-- **The pointwise form of `QuarterPinchedFor`**, for an *arbitrary* metric `g` (not necessarily the
ambient instance): the sectional curvature of every `g`-orthonormal pair lies in `(1, 4]`.

This is the form in which the pinching is consumed by the diameter/Klingenberg estimates, where the
metric is a parameter.  The proof is the same as for `quarterPinched_pointwise_le`: extend the two
vectors to global smooth sections. -/
theorem quarterPinchedFor_pointwise {g : RiemannianMetric (fun x : M ↦ TangentSpace I x)}
    (hpinch : QuarterPinchedFor g cov) (x : M)
    (u v : TangentSpace I x) (hu : g.inner x u u = 1) (hv : g.inner x v v = 1)
    (huv : g.inner x u v = 0) :
    (1 : ℝ) < g.inner x (curvVec cov x u v v) u ∧ g.inner x (curvVec cov x u v v) u ≤ 4 := by
  obtain ⟨X, hX, hXu⟩ := exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYv⟩ := exists_contMDiff_section_apply_eq (I := I) (M := M) v
  have h1 : g.inner x (X x) (X x) = 1 := by rw [hXu]; exact hu
  have h2 : g.inner x (Y x) (Y x) = 1 := by rw [hYv]; exact hv
  have h3 : g.inner x (X x) (Y x) = 0 := by rw [hXu, hYv]; exact huv
  obtain ⟨hlo, hup⟩ := hpinch X Y hX hY x h1 h2 h3
  have h0 : g.inner x (curv cov X Y Y x) (X x) = g.inner x (curvVec cov x u v v) u := by
    rw [← curvVec_eq cov ‹ContMDiffCovariantDerivative cov ∞› hX hY hY hXu hYv hYv, hXu]
  rw [h0] at hlo hup
  exact ⟨hlo, hup⟩

/-! ## The pointwise upper bound from `QuarterPinched` -/

/-- **`QuarterPinched` gives the pointwise upper bound `sec ≤ 4`** for arbitrary orthonormal pairs
of tangent vectors. -/
theorem quarterPinched_pointwise_le (hpinch : QuarterPinched cov) (x : M)
    (u v : TangentSpace I x) (hu : hamb.g.inner x u u = 1) (hv : hamb.g.inner x v v = 1)
    (huv : hamb.g.inner x u v = 0) :
    hamb.g.inner x (curvVec cov x u v v) u ≤ 4 := by
  obtain ⟨X, hX, hXu⟩ := exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYv⟩ := exists_contMDiff_section_apply_eq (I := I) (M := M) v
  have h1 : inner ℝ (X x) (X x) = 1 := by rw [hXu]; exact hu
  have h2 : inner ℝ (Y x) (Y x) = 1 := by rw [hYv]; exact hv
  have h3 : inner ℝ (X x) (Y x) = 0 := by rw [hXu, hYv]; exact huv
  have h := (hpinch X Y hX hY x h1 h2 h3).2
  have h0 : inner ℝ (curv cov X Y Y x) (X x) = inner ℝ (curvVec cov x u v v) u := by
    rw [← curvVec_eq cov ‹ContMDiffCovariantDerivative cov ∞› hX hY hY hXu hYv hYv]
    simp only [hXu, hYv]
  rw [h0, inner_eq_g] at h
  exact h

/-! ## The two transfers -/

/-- **Metric compatibility survives scaling.** -/
theorem isMetricCompatibleFor_scale (hmet : IsMetricCompatibleFor hamb.g cov) {c : ℝ} (hc : 0 < c)
    (g' : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (hinner : ∀ (x : M) (v w : TangentSpace I x), g'.inner x v w = c * hamb.g.inner x v w) :
    IsMetricCompatibleFor g' cov :=
  Commons.Geometry.Manifold.Riemannian.metricCompatible_scaleMetric
    (M := M) (g := hamb.g) (g' := g') (c := c) (cov := cov) hc hinner hmet

/-- **Quarter pinching survives scaling.**  If the ambient metric has `sec > c` (uniformly, with the
same constant `c` by which we scale) and `sec ≤ 4`, then the scaled metric `g' = c · g` satisfies
`1 < sec ≤ 4`. -/
theorem quarterPinchedFor_scale {c : ℝ} (hc1 : 1 < c)
    (g' : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (hinner : ∀ (x : M) (v w : TangentSpace I x), g'.inner x v w = c * hamb.g.inner x v w)
    (hpinch : QuarterPinched cov)
    (hlt : ∀ (x : M) (u v : TangentSpace I x), hamb.g.inner x u u = 1 →
      hamb.g.inner x v v = 1 → hamb.g.inner x u v = 0 →
      c < hamb.g.inner x (curvVec cov x u v v) u) :
    QuarterPinchedFor g' cov := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc1
  have hsq : Real.sqrt c * Real.sqrt c = c := by rw [← sq, Real.sq_sqrt hcpos.le]
  have hsq2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hcpos.le
  intro X Y hX hY x hXX hYY hXY
  -- scaled orthonormality, transferred to the ambient metric
  have hXX' : c * hamb.g.inner x (X x) (X x) = 1 :=
    (hinner x (X x) (X x)).symm.trans hXX
  have hYY' : c * hamb.g.inner x (Y x) (Y x) = 1 :=
    (hinner x (Y x) (Y x)).symm.trans hYY
  have hXY' : c * hamb.g.inner x (X x) (Y x) = 0 :=
    (hinner x (X x) (Y x)).symm.trans hXY
  have hXu : hamb.g.inner x (X x) (X x) = 1 / c := by
    rw [eq_div_iff hcpos.ne']; linarith
  have hYv : hamb.g.inner x (Y x) (Y x) = 1 / c := by
    rw [eq_div_iff hcpos.ne']; linarith
  have hXYv : hamb.g.inner x (X x) (Y x) = 0 := by
    rcases mul_eq_zero.mp hXY' with h | h
    · exact absurd h hcpos.ne'
    · exact h
  -- the rescaled tangent vectors, which are orthonormal for the *ambient* metric
  have hunn : hamb.g.inner x (Real.sqrt c • X x) (Real.sqrt c • X x) = 1 := by
    rw [inner_smul_smul, hXu, hsq, mul_one_div, div_self hcpos.ne']
  have hvvn : hamb.g.inner x (Real.sqrt c • Y x) (Real.sqrt c • Y x) = 1 := by
    rw [inner_smul_smul, hYv, hsq, mul_one_div, div_self hcpos.ne']
  have huvn : hamb.g.inner x (Real.sqrt c • X x) (Real.sqrt c • Y x) = 0 := by
    rw [inner_smul_smul, hXYv, mul_zero]
  have hlow := hlt x (Real.sqrt c • X x) (Real.sqrt c • Y x) hunn hvvn huvn
  have hup := quarterPinched_pointwise_le (cov := cov) hpinch x
    (Real.sqrt c • X x) (Real.sqrt c • Y x) hunn hvvn huvn
  -- the curvature term rescales by `c ^ 2`
  have hkey : hamb.g.inner x (curvVec cov x (Real.sqrt c • X x) (Real.sqrt c • Y x)
        (Real.sqrt c • Y x)) (Real.sqrt c • X x)
      = c ^ 2 * (hamb.g.inner x (curvVec cov x (X x) (Y x) (Y x)) (X x)) := by
    rw [curvVec_smul_left cov ‹ContMDiffCovariantDerivative cov ∞› x (Real.sqrt c) (X x)
        (Real.sqrt c • Y x) (Real.sqrt c • Y x),
      curvVec_smul_middle cov ‹ContMDiffCovariantDerivative cov ∞› x (Real.sqrt c) (X x) (Y x)
        (Real.sqrt c • Y x),
      curvVec_smul_right cov ‹ContMDiffCovariantDerivative cov ∞› x (Real.sqrt c) (X x) (Y x)
        (Y x),
      ]
    simp only [inner_smul_left, inner_smul_right, smul_smul, hsq]
    ring_nf
    rw [hsq2]
    ring
  rw [hkey] at hlow hup
  have hsc : g'.inner x (curv cov X Y Y x) (X x)
      = c * hamb.g.inner x (curvVec cov x (X x) (Y x) (Y x)) (X x) := by
    rw [← curvVec_eq cov ‹ContMDiffCovariantDerivative cov ∞› hX hY hY rfl rfl rfl]
    exact hinner x (curvVec cov x (X x) (Y x) (Y x)) (X x)
  constructor
  · rw [hsc]; nlinarith [hlow, hcpos]
  · rw [hsc]
    have hc1le : 1 ≤ c := hc1.le
    nlinarith [hup, hcpos, hc1le]

/-- **The sharp upper bound for the scaled metric**: if the ambient metric satisfies `sec ≤ 4` at
every orthonormal pair, then a `g'`-orthonormal pair has `g'`-sectional curvature `≤ 4 / c`. -/
theorem scaled_sec_le {c : ℝ} (hc1 : 1 < c)
    (g' : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (hinner : ∀ (x : M) (v w : TangentSpace I x), g'.inner x v w = c * hamb.g.inner x v w)
    (hup4 : ∀ (x : M) (u v : TangentSpace I x), hamb.g.inner x u u = 1 →
      hamb.g.inner x v v = 1 → hamb.g.inner x u v = 0 →
      hamb.g.inner x (curvVec cov x u v v) u ≤ 4) :
    ∀ (x : M) (u v : TangentSpace I x), g'.inner x u u = 1 → g'.inner x v v = 1 →
      g'.inner x u v = 0 → g'.inner x (curvVec cov x u v v) u ≤ 4 / c := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc1
  have hsq : Real.sqrt c * Real.sqrt c = c := by rw [← sq, Real.sq_sqrt hcpos.le]
  have hsq2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hcpos.le
  intro x u v hu hv huv
  have hu' : c * hamb.g.inner x u u = 1 := (hinner x u u).symm.trans hu
  have hv' : c * hamb.g.inner x v v = 1 := (hinner x v v).symm.trans hv
  have huv' : c * hamb.g.inner x u v = 0 := (hinner x u v).symm.trans huv
  have hXu : hamb.g.inner x u u = 1 / c := by rw [eq_div_iff hcpos.ne']; linarith
  have hYv : hamb.g.inner x v v = 1 / c := by rw [eq_div_iff hcpos.ne']; linarith
  have hXYv : hamb.g.inner x u v = 0 := by
    rcases mul_eq_zero.mp huv' with h | h
    · exact absurd h hcpos.ne'
    · exact h
  have hunn : hamb.g.inner x (Real.sqrt c • u) (Real.sqrt c • u) = 1 := by
    rw [inner_smul_smul, hXu, hsq, mul_one_div, div_self hcpos.ne']
  have hvvn : hamb.g.inner x (Real.sqrt c • v) (Real.sqrt c • v) = 1 := by
    rw [inner_smul_smul, hYv, hsq, mul_one_div, div_self hcpos.ne']
  have huvn : hamb.g.inner x (Real.sqrt c • u) (Real.sqrt c • v) = 0 := by
    rw [inner_smul_smul, hXYv, mul_zero]
  have hup := hup4 x (Real.sqrt c • u) (Real.sqrt c • v) hunn hvvn huvn
  have hkey : hamb.g.inner x (curvVec cov x (Real.sqrt c • u) (Real.sqrt c • v)
        (Real.sqrt c • v)) (Real.sqrt c • u)
      = c ^ 2 * (hamb.g.inner x (curvVec cov x u v v) u) := by
    rw [curvVec_smul_left cov ‹ContMDiffCovariantDerivative cov ∞› x (Real.sqrt c) u
        (Real.sqrt c • v) (Real.sqrt c • v),
      curvVec_smul_middle cov ‹ContMDiffCovariantDerivative cov ∞› x (Real.sqrt c) u v
        (Real.sqrt c • v),
      curvVec_smul_right cov ‹ContMDiffCovariantDerivative cov ∞› x (Real.sqrt c) u v v]
    simp only [inner_smul_left, inner_smul_right, smul_smul, hsq]
    ring_nf
    rw [hsq2]
    ring
  rw [hkey] at hup
  simp only [hinner x (curvVec cov x u v v) u]
  rw [le_div_iff₀ hcpos]
  nlinarith [hup]

end

end Submission.MetricScale
