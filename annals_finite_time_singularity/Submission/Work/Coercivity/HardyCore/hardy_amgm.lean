import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity.HardyCore

/-- Pointwise AM–GM (Young) inequality behind the Hardy-type coercivity estimate:
for `z > 0`, `2 (g z) (g' z) / z ≤ (1/2) g z ^ 2 / z ^ 2 + 2 (g' z) ^ 2`,
i.e. `(1/2) (a - 2b) ^ 2 ≥ 0` with `a = g z / z`, `b = g' z`. -/
private lemma hardy_amgm_ptwise (g g' : ℝ → ℝ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      2 * (g z * g' z) / z ≤ (1 / 2) * (g z ^ 2 / z ^ 2) + 2 * (g' z) ^ 2 := by
  intro z hz
  have hzne : z ≠ 0 := ne_of_gt hz
  have h1 : 2 * (g z / z) * (g' z) ≤ (1 / 2) * (g z / z) ^ 2 + 2 * (g' z) ^ 2 := by
    nlinarith [sq_nonneg (g z / z - 2 * (g' z))]
  calc 2 * (g z * g' z) / z = 2 * (g z / z) * (g' z) := by field_simp
    _ ≤ (1 / 2) * (g z / z) ^ 2 + 2 * (g' z) ^ 2 := h1
    _ = (1 / 2) * (g z ^ 2 / z ^ 2) + 2 * (g' z) ^ 2 := by field_simp

theorem hardy_amgm (g g' : ℝ → ℝ)
    (hA : MeasureTheory.IntegrableOn (fun z => g z ^ 2 / z ^ 2) (Set.Ioi (0 : ℝ)))
    (hB : MeasureTheory.IntegrableOn (fun z => g' z ^ 2) (Set.Ioi (0 : ℝ))) :
    ∫ z in Set.Ioi (0 : ℝ), 2 * (g z * g' z) / z
      ≤ (1 / 2) * (∫ z in Set.Ioi (0 : ℝ), g z ^ 2 / z ^ 2)
        + 2 * ∫ z in Set.Ioi (0 : ℝ), (g' z) ^ 2 := by
  have hA' : MeasureTheory.Integrable (fun z => g z ^ 2 / z ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hA
  have hB' : MeasureTheory.Integrable (fun z => (g' z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hB
  -- The majorant `F z = (1/2) g z ^ 2 / z ^ 2 + 2 (g' z) ^ 2` is integrable.
  have hFint : MeasureTheory.Integrable
      (fun z => (1 / 2) * (g z ^ 2 / z ^ 2) + 2 * (g' z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hA'.const_mul (1 / 2)).add (hB'.const_mul 2)
  -- The pointwise bound holds a.e. for the restricted measure.
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      2 * (g z * g' z) / z ≤ (1 / 2) * (g z ^ 2 / z ^ 2) + 2 * (g' z) ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun z => fun hz => hardy_amgm_ptwise g g' z hz)
  -- The majorant is nonnegative.
  have hFnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      (fun z => (1 / 2) * (g z ^ 2 / z ^ 2) + 2 * (g' z) ^ 2) := by
    apply Filter.Eventually.of_forall
    intro z
    simp only [Pi.zero_apply]
    have h1 : (0 : ℝ) ≤ g z ^ 2 / z ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ (g' z) ^ 2 := sq_nonneg _
    linarith
  -- Integral of the majorant.
  have hIntF : ∫ z, ((1 / 2) * (g z ^ 2 / z ^ 2) + 2 * (g' z) ^ 2)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      = (1 / 2) * (∫ z, g z ^ 2 / z ^ 2 ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
        + 2 * (∫ z, (g' z) ^ 2 ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
    rw [MeasureTheory.integral_add (hA'.const_mul (1 / 2)) (hB'.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- Comparison of the two integrals.  If the left integrand is integrable we use
  -- monotonicity; otherwise its integral is `0` by convention and the right-hand
  -- side is nonnegative.
  have key : ∫ z, 2 * (g z * g' z) / z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      ≤ ∫ z, ((1 / 2) * (g z ^ 2 / z ^ 2) + 2 * (g' z) ^ 2)
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    by_cases hu : MeasureTheory.Integrable (fun z => 2 * (g z * g' z) / z)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    · exact MeasureTheory.integral_mono_ae hu hFint hae
    · rw [MeasureTheory.integral_undef hu]
      exact MeasureTheory.integral_nonneg_of_ae hFnn
  calc ∫ z in Set.Ioi (0 : ℝ), 2 * (g z * g' z) / z
      = ∫ z, 2 * (g z * g' z) / z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := rfl
    _ ≤ ∫ z, ((1 / 2) * (g z ^ 2 / z ^ 2) + 2 * (g' z) ^ 2)
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := key
    _ = (1 / 2) * (∫ z, g z ^ 2 / z ^ 2 ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
        + 2 * (∫ z, (g' z) ^ 2 ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := hIntF
    _ = (1 / 2) * (∫ z in Set.Ioi (0 : ℝ), g z ^ 2 / z ^ 2)
        + 2 * (∫ z in Set.Ioi (0 : ℝ), (g' z) ^ 2) := rfl

end Work.Coercivity.HardyCore
