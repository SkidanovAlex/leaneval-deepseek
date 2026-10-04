import Submission.GExpPieceData
import Submission.IndexScale

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Rauch
open Submission.RauchGlobal
open Submission.GExpFlow
open Submission.JacobiCoords
open Submission.IntrinsicVariation
open Submission.SecondVarGlobal
open Submission.IndexScale

/-!
# The phase condition of `energy_second_deriv_piece` at a small scale

`Submission.SecondVarGlobal.energy_second_deriv_piece` needs the **phase condition**

`(chartCoord z γ t, flowScale D • (σ • u t)) ∈ chartData z Z`  for `|σ| ≤ 1` and `t` in the room,

for the *chart coordinates* `u` of the field.  `GExpPieceData.mem_chartData_phase'` reduces it to the
uniform bound `flowScale D * ‖u t‖ ≤ 1`, which fails for a general (large) field.

This module supplies the missing step (Roadmap §102.6 (i)): **shrinking the field by a factor `c`
makes the phase condition hold**, with `c` bounded below only by the sup-norm of the field's chart
coordinates on the (compact) interval.  The two lemmas here are the pieces of `hphase`:
`exists_pos_flowScale_mul_norm_le` (the uniform bound) and `exists_pos_phase_condition` (the phase
condition itself, for `σ ∈ [-1,1]`).
-/

namespace Submission.EnergyPhase

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

/-- **The uniform smallness of the scaled chart coordinates**: for a flow datum `D` and a field whose
chart coordinates are continuous on a compact interval, there is `c₀ > 0` such that for every
`c ∈ (0, c₀]` the scaled coordinates satisfy `flowScale D * ‖u‖ ≤ 1` on the interval. -/
lemma exists_pos_flowScale_mul_norm_le {z : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z Z)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {A B : ℝ} (hAB : A ≤ B)
    (hVcd : ContinuousOn (chartCoords (I := I) z γ V) (Icc A B)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c ∈ Set.Ioc (0 : ℝ) c₀, ∀ t ∈ Icc A B,
      flowScale D * ‖chartCoords (I := I) z γ (fun s => c • V s) t‖ ≤ 1 := by
  obtain ⟨t₀, _ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (⟨A, left_mem_Icc.mpr hAB⟩ : (Icc A B).Nonempty) hVcd.norm
  set Mm : ℝ := ‖chartCoords (I := I) z γ V t₀‖ with hMdef
  have hMnn : 0 ≤ Mm := norm_nonneg _
  have hDpos : 0 < flowScale D := flowScale_pos (cov := cov) (I := I) D
  have hMpos : 0 < flowScale D * (Mm + 1) := mul_pos hDpos (by linarith)
  refine ⟨1 / (flowScale D * (Mm + 1)), div_pos one_pos hMpos, ?_⟩
  intro c hc t ht
  have hcpos : 0 < c := hc.1
  have hbound : c * (flowScale D * (Mm + 1)) ≤ 1 := by
    have h := hc.2
    rw [div_eq_mul_inv, one_mul] at h
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hMpos)
    rwa [inv_mul_cancel₀ (ne_of_gt hMpos)] at h2
  have hle : ‖chartCoords (I := I) z γ V t‖ ≤ Mm := hmax ht
  rw [chartCoords_smul]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
  have hstep : flowScale D * (c * ‖chartCoords (I := I) z γ V t‖)
      ≤ flowScale D * (c * (Mm + 1)) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hDpos)
    exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hcpos)
  have hstep2 : flowScale D * (c * (Mm + 1)) ≤ 1 := by
    rw [show flowScale D * (c * (Mm + 1)) = c * (flowScale D * (Mm + 1)) by ring]
    exact hbound
  linarith [hstep, hstep2]

/-- **The phase condition of `energy_second_deriv_piece` at a small scale.** -/
lemma exists_pos_phase_condition {z : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z Z)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {A B : ℝ} (hAB : A ≤ B)
    (hVcd : ContinuousOn (chartCoords (I := I) z γ V) (Icc A B))
    (hγZ : ∀ t ∈ Icc A B, γ t ∈ Z) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c ∈ Set.Ioc (0 : ℝ) c₀, ∀ σ ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc A B,
      (chartCoord (I := I) z γ t,
          flowScale D • (σ • chartCoords (I := I) z γ (fun s => c • V s) t))
        ∈ chartData (I := I) z Z := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := exists_pos_flowScale_mul_norm_le (cov := cov) D hAB hVcd
  refine ⟨c₀, hc₀pos, ?_⟩
  intro c hc σ hσ t ht
  exact GExpPieceData.mem_chartData_phase' (cov := cov) D (hγZ t ht) hσ (hc₀ c hc t ht)

end

end Submission.EnergyPhase
