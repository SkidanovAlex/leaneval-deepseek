import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs8.A.abs_wSmall1Pair_chiB_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

open MeasureTheory

/-- Integrating the pointwise domination `abs_wSmall1Pair_chiB_le` over the analysis cube: the `y`-integral of `|wSmall1Pair|` is at most `(smallConvLower M)⁻¹·χ_{B(u)}(z)·∫_{acube L} |g₀(z−y)|·χ_{B(u)}(y)`. -/
theorem abs_integral_wSmall1Pair_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    {M : ℕ} (hM : 1 ≤ M) {d : ℕ} (hd : (0 : ℝ) < (d : ℝ))
    (hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * (d : ℝ)) / 16)
    (hdRχ : ∀ L : ℝ, 1 ≤ L → R0 ≤ L * Submission.BoseGases.chiR0)
    {L : ℝ} (hL : 1 ≤ L) (u z : EuclideanSpace ℝ (Fin 3)) :
    ∫ y in Submission.BoseGases.acube L,
        |Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y| ≤
      (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M L (d : ℝ) u z *
        ∫ y in Submission.BoseGases.acube L,
          |Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  -- The constant `c = (smallConvLower M)⁻¹·χ_{B(u)}(z)` pulling out of the `y`-integral.
  set c : ℝ := (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) *
      Submission.BoseGases.chiSmallB M L (d : ℝ) u z with hcdef
  -- Continuity (hence measurability) of `y ↦ χ_{B(u)}(y)`.
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M L (d : ℝ) u y) := by
    have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale L y) :=
      Submission.BoseGases.chiScale_continuous L
    have h2 : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiSmall M ((L * (d : ℝ))⁻¹ • y - u)) :=
      (Submission.BoseGases.chiSmall_continuous hM).comp
        ((continuous_id.const_smul ((L * (d : ℝ))⁻¹)).sub continuous_const)
    exact h1.mul h2
  -- The uniform sup bound `χ_{B(u)} ≤ chiSupAbs · chiSmallDecay M`.
  set c₂ : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M with hc₂def
  have hchiB_le : ∀ y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiSmallB M L (d : ℝ) u y ≤ c₂ := by
    intro y
    rw [hc₂def]
    have hb := Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := L) (d := (d : ℝ)) hM u y
    have h2 : Submission.BoseGases.chiSmall M ((L * (d : ℝ))⁻¹ • y - u) ≤
        Submission.BoseGases.chiSmallDecay M := by
      have h' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((L * (d : ℝ))⁻¹ • y - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at h'
    have hbnn : 0 ≤ Submission.BoseGases.chiSmallB M L (d : ℝ) u y :=
      Submission.BoseGases.chiSmallB_nonneg M L (d : ℝ) u y
    rw [abs_of_nonneg hbnn] at hb
    calc Submission.BoseGases.chiSmallB M L (d : ℝ) u y
        ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmall M ((L * (d : ℝ))⁻¹ • y - u) := hb
      _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
          mul_le_mul_of_nonneg_left h2 Submission.BoseGases.chiSupAbs_nonneg
  -- Pointwise domination, regrouped with `c` in front.
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y| ≤
        c * (|Submission.BoseGases.g0 v h (z - y)| *
          Submission.BoseGases.chiSmallB M L (d : ℝ) u y) := by
    intro y
    have hD := Work.UBBInputs8.A.abs_wSmall1Pair_chiB_le (v := v) hv_supp hR0 h hM hLpos hd
      (hdR L hL) (hdRχ L hL) u z y
    calc |Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y|
        ≤ (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M L (d : ℝ) u z *
            |Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y := hD
      _ = c * (|Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y) := by
            rw [hcdef]; ring
  -- Integrability of the majorant `c·(|g₀(z−·)|·χ_{B(u)}(·))` on the whole space.
  have hgi : Integrable (fun y : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h (z - y)|) :=
    (Submission.BoseGases.g0_integrable hR0 hv_supp h).abs.comp_sub_left z
  have hdom : Integrable (fun y : EuclideanSpace ℝ (Fin 3) => c₂ * |Submission.BoseGases.g0 v h (z - y)|) :=
    hgi.const_mul c₂
  have hmeas : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
      |Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y) :=
    hgi.aestronglyMeasurable.mul hcont.aestronglyMeasurable
  have hbound : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      ‖|Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y‖
        ≤ c₂ * |Submission.BoseGases.g0 v h (z - y)| := by
    filter_upwards with y
    have hle : |Submission.BoseGases.chiSmallB M L (d : ℝ) u y| ≤ c₂ := by
      have hbnn : 0 ≤ Submission.BoseGases.chiSmallB M L (d : ℝ) u y :=
        Submission.BoseGases.chiSmallB_nonneg M L (d : ℝ) u y
      rw [abs_of_nonneg hbnn]
      exact hchiB_le y
    have hAnn : 0 ≤ |Submission.BoseGases.g0 v h (z - y)| := abs_nonneg _
    calc ‖|Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y‖
        = |Submission.BoseGases.g0 v h (z - y)| * |Submission.BoseGases.chiSmallB M L (d : ℝ) u y| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hAnn]
      _ ≤ |Submission.BoseGases.g0 v h (z - y)| * c₂ := mul_le_mul_of_nonneg_left hle hAnn
      _ = c₂ * |Submission.BoseGases.g0 v h (z - y)| := by ring
  have hprod : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      |Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y) :=
    hdom.mono' hmeas hbound
  have hmajOn : IntegrableOn (fun y : EuclideanSpace ℝ (Fin 3) =>
      c * (|Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y))
      (Submission.BoseGases.acube L) := (hprod.const_mul c).integrableOn
  -- Monotonicity of the box integral.
  have hstep1 : ∫ y in Submission.BoseGases.acube L,
        |Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y| ≤
      ∫ y in Submission.BoseGases.acube L,
        c * (|Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y) := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun y => abs_nonneg _)
    · exact hmajOn
    · filter_upwards with y; exact hpt y
  have hstep2 : ∫ y in Submission.BoseGases.acube L,
        c * (|Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y)
      = c * ∫ y in Submission.BoseGases.acube L,
        (|Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y) :=
    integral_const_mul c _
  calc ∫ y in Submission.BoseGases.acube L,
        |Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y|
      ≤ ∫ y in Submission.BoseGases.acube L,
        c * (|Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y) := hstep1
    _ = c * ∫ y in Submission.BoseGases.acube L,
        (|Submission.BoseGases.g0 v h (z - y)| * Submission.BoseGases.chiSmallB M L (d : ℝ) u y) := hstep2

end Work.UBBInputs8.A
