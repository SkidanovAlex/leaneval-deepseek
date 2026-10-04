import Submission.HingeGlobal
import Submission.HingeLocal
import Submission.GlobalExp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local hinge comparison for the *global* exponential map `GExp`

`Submission/HingeLocal.edist_expMap_le_model` proves the local hinge comparison for the chart-based
`expMap`.  That map is **atlas-dependent**: `expMap cov x v` takes the junk value `x` unless the
chart-`x` geodesic equation can be solved with velocity `v` on the whole interval `Ioo (-2) 2`
*inside the chart at `x`*, so its radius of validity depends on how large the chosen atlas' charts
are (see `Submission/Roadmap.lean` §38 for the obstruction).  All the *uniform* statements must
therefore be phrased with the chart-invariant `GlobalExp.GExp`.

Here we record the translation: for `‖v‖` (the fibre norm) small enough, `GExp hmet x v` and
`expMap cov x v` agree (`GlobalExp.exists_pos_GExp_eq_expMap`), so the pointwise local comparison
transfers verbatim.

## Main result

* `edist_GExp_le_model` — the local hinge comparison at `x₀` for `GExp`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HingeLocal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

namespace Submission.HingeGExp

noncomputable section

variable [I.Boundaryless]

/-- **The local hinge comparison for `GExp`.**  There is `ρ > 0` such that for all unit vectors
`U`, `V` in `T_{x₀}M` and all `r₁, r₂ ∈ (0, ρ)`,
`d(GExp x₀ (r₁ U), GExp x₀ (r₂ V)) ≤ arccos (cos r₁ cos r₂ + sin r₁ sin r₂ ⟪U,V⟫)`. -/
theorem edist_GExp_le_model [Nontrivial E] [CompactSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (r₁ r₂ : ℝ) (U V : TangentSpace I x₀),
      0 < r₁ → r₁ < ρ → 0 < r₂ → r₂ < ρ → ‖U‖ = 1 → ‖V‖ = 1 →
      Manifold.riemannianEDist I (GExp (cov := cov) hmet x₀ (r₁ • U))
          (GExp (cov := cov) hmet x₀ (r₂ • V))
        ≤ ENNReal.ofReal (Real.arccos (Real.cos r₁ * Real.cos r₂
            + Real.sin r₁ * Real.sin r₂ * inner ℝ U V)) := by
  obtain ⟨ρ₁, hρ₁, hcompp⟩ := edist_expMap_le_model (cov := cov) hmet htor hpinch x₀
  obtain ⟨ρ₂, hρ₂, hagree⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet x₀
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun r₁ r₂ U V hr1 hr1ρ hr2 hr2ρ hU hV => ?_⟩
  have hr1₁ : r₁ < ρ₁ := lt_of_lt_of_le hr1ρ (min_le_left _ _)
  have hr2₁ : r₂ < ρ₁ := lt_of_lt_of_le hr2ρ (min_le_left _ _)
  have hr1₂ : r₁ < ρ₂ := lt_of_lt_of_le hr1ρ (min_le_right _ _)
  have hr2₂ : r₂ < ρ₂ := lt_of_lt_of_le hr2ρ (min_le_right _ _)
  have hnorm1 : ‖r₁ • U‖ = r₁ := by
    rw [norm_smul, hU, mul_one, Real.norm_of_nonneg hr1.le]
  have hnorm2 : ‖r₂ • V‖ = r₂ := by
    rw [norm_smul, hV, mul_one, Real.norm_of_nonneg hr2.le]
  rw [hagree (r₁ • U) (by rw [hnorm1]; exact hr1₂),
    hagree (r₂ • V) (by rw [hnorm2]; exact hr2₂)]
  exact hcompp r₁ r₂ U V hr1 hr1₁ hr2 hr2₁ hU hV

end

end Submission.HingeGExp
