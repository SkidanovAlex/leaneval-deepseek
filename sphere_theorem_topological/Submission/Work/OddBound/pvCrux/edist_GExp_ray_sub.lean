import Mathlib
import Submission.Work.OddBound.LiftKit

namespace Work.OddBound.pvCrux

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

set_option autoImplicit false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- **Sub-arcs of a ray below the injectivity radius are minimising.**  If `GExp p` is injective on
the ball of radius `ρ` and `‖v‖ ≤ ρ`, then for `0 ≤ a ≤ b ≤ 1` the sub-arc of the ray from the point
at parameter `a` to the point at parameter `b` has length exactly `(b - a) * ‖v‖`:
`d (GExp p (a • v)) (GExp p (b • v)) = (b - a) * ‖v‖`.

Ingredients: `Submission.GExpRay2.edist_GExp_smul_le_mul_norm` for `≤` and
`Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast` at the two parameters, plus the reverse
triangle inequality and `ENNReal` arithmetic. -/
theorem edist_GExp_ray_sub
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ρ : ℝ} (hinj : Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet p ρ)
    {v : TangentSpace I p} (hv : ‖v‖ ≤ ρ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Manifold.riemannianEDist I
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • v))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (b • v))
      = ENNReal.ofReal ((b - a) * ‖v‖) := by
  have hb0 : 0 ≤ b := ha.trans hab
  -- the norms of the two velocity vectors
  have hna : ‖a • v‖ = a * ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg ha]
  have hnb : ‖b • v‖ = b * ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg hb0]
  -- both stay below the injectivity radius
  have hva : a * ‖v‖ ≤ ρ := by
    have h1 : a * ‖v‖ ≤ 1 * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hab.trans hb) (norm_nonneg v)
    rw [one_mul] at h1
    exact h1.trans hv
  have hvb : b * ‖v‖ ≤ ρ := by
    have h1 : b * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
    rw [one_mul] at h1
    exact h1.trans hv
  -- distances from the base point `p`
  have hd_a : Manifold.riemannianEDist I p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • v)) = ENNReal.ofReal (a * ‖v‖) := by
    have h := Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast (cov := cov) hmet htor
      hinj (w := a • v) (by rw [hna]; exact hva)
    rwa [hna] at h
  have hd_b : Manifold.riemannianEDist I p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (b • v)) = ENNReal.ofReal (b * ‖v‖) := by
    have h := Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast (cov := cov) hmet htor
      hinj (w := b • v) (by rw [hnb]; exact hvb)
    rwa [hnb] at h
  -- the sub-arc is no longer than the induced segment
  have hle : Manifold.riemannianEDist I
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • v))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (b • v))
      ≤ ENNReal.ofReal ((b - a) * ‖v‖) :=
    Submission.GExpRay2.edist_GExp_smul_le_mul_norm (cov := cov) hmet p ha hab
  -- and no shorter, by the reverse triangle inequality applied at `p`
  refine le_antisymm hle ?_
  set D : ℝ≥0∞ := Manifold.riemannianEDist I
    (Submission.GlobalExp.GExp (cov := cov) hmet p (a • v))
    (Submission.GlobalExp.GExp (cov := cov) hmet p (b • v)) with hDdef
  have hDtop : D ≠ ⊤ := by
    rw [hDdef]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have htri := Manifold.riemannianEDist_triangle (I := I) (x := p)
    (y := Submission.GlobalExp.GExp (cov := cov) hmet p (a • v))
    (z := Submission.GlobalExp.GExp (cov := cov) hmet p (b • v))
  rw [hd_a, hd_b] at htri
  have hsumtop : (ENNReal.ofReal (a * ‖v‖) + D) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hDtop⟩
  have hreal := ENNReal.toReal_mono hsumtop htri
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hDtop] at hreal
  rw [ENNReal.toReal_ofReal (mul_nonneg ha (norm_nonneg v))] at hreal
  rw [ENNReal.toReal_ofReal (mul_nonneg hb0 (norm_nonneg v))] at hreal
  have hkey : (b - a) * ‖v‖ = b * ‖v‖ - a * ‖v‖ := by ring
  have hgeq : (b - a) * ‖v‖ ≤ D.toReal := by linarith
  have hfin : ENNReal.ofReal ((b - a) * ‖v‖) ≤ ENNReal.ofReal D.toReal :=
    ENNReal.ofReal_le_ofReal hgeq
  rwa [ENNReal.ofReal_toReal hDtop] at hfin

end Work.OddBound.pvCrux
