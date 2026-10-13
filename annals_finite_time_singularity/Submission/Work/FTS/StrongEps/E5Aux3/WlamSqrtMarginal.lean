import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
import Submission.Work.Elliptic.L12densFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Radial Cauchy–Schwarz against the sublinear weight `Wlam s = s/(1+s)²`

`Wlam` is nonnegative and square-integrable on `(0,∞)`, with `∫_{(0,∞)} Wlam² = W2` by
definition.  Hence for every nonnegative `H : ℝ → ℝ` with `H` integrable on `(0,∞)` the
pairing `∫_{(0,∞)} Wlam s · √(H s)` is controlled by the `L²`-norms of the two factors:

`∫_{(0,∞)} Wlam s · √(H s) ds ≤ √W2 · √(∫_{(0,∞)} H)`.

This is exactly `L²`-Cauchy–Schwarz for the pair (`Wlam`, `√H`): `(√H)² = H` since `H ≥ 0`,
so `√H ∈ L²((0,∞))` with `∫ (√H)² = ∫ H`, and `Wlam ∈ L²((0,∞))` with `∫ Wlam² = W2`.

The only imported ingredient is the square-integrability of the weight,
`Work.Elliptic.psi_sq_integrable_aux` (`(s/(1+s)²)² ∈ L¹((0,∞))`).
-/

namespace Work.FTS.StrongEps.E5Aux3

open MeasureTheory Set Filter
open scoped Real Topology

/-- `Wlam` is a.e. strongly measurable on `(0,∞)` (it is continuous there). -/
lemma aestronglyMeasurable_wlam :
    AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam (volume.restrict (Set.Ioi (0 : ℝ))) := by
  change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
    (volume.restrict (Set.Ioi (0 : ℝ)))
  refine ContinuousOn.aestronglyMeasurable (μ := volume)
    (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_) measurableSet_Ioi
  intro s hs
  have hne : (1 : ℝ) + s ≠ 0 := by
    simp only [Set.mem_Ioi] at hs
    linarith
  exact pow_ne_zero 2 hne

/-- `Wlam²` is integrable on `(0,∞)` (its integral is `W2` by definition). -/
lemma integrableOn_wlam_sq :
    IntegrableOn (fun s : ℝ => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi (0 : ℝ)) := by
  simpa only [Work.FTS.GalBasis.cc.Wlam] using Work.Elliptic.psi_sq_integrable_aux

/-- `Wlam ∈ L²((0,∞))`. -/
lemma memLp_wlam : MemLp Work.FTS.GalBasis.cc.Wlam 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
  (memLp_two_iff_integrable_sq aestronglyMeasurable_wlam).mpr integrableOn_wlam_sq

/-- `√H ∈ L²((0,∞))` whenever `H ≥ 0` is integrable there. -/
lemma memLp_sqrt {H : ℝ → ℝ} (hHnn : ∀ s, 0 ≤ H s)
    (hH : IntegrableOn H (Set.Ioi (0 : ℝ))) :
    MemLp (fun s : ℝ => Real.sqrt (H s)) 2 (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hA_aesm : AEStronglyMeasurable (fun s : ℝ => Real.sqrt (H s))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hH.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s : ℝ => Real.sqrt (H s) ^ 2) (Set.Ioi (0 : ℝ)) :=
    hH.congr (Filter.Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
  exact (memLp_two_iff_integrable_sq hA_aesm).mpr hA2_int

/-- The integrand `Wlam · √H` is nonnegative on `(0,∞)`, hence so is its integral
(`√` is nonnegative and `Wlam` is nonnegative on `(0,∞)`). -/
lemma integral_wlam_sqrt_nonneg (H : ℝ → ℝ) :
    0 ≤ ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s) := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  show ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
    (0 : ℝ) ≤ Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  exact Eventually.of_forall fun s hs =>
    mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt hs)) (Real.sqrt_nonneg _)

/-- **Radial Cauchy–Schwarz against `Wlam`.**  For `H ≥ 0` integrable on `(0,∞)`,
`∫_{(0,∞)} Wlam s · √(H s) ds ≤ √W2 · √(∫_{(0,∞)} H)`. -/
theorem WlamSqrtMarginal {H : ℝ → ℝ}
    (hHnn : ∀ s, 0 ≤ H s) (hH : MeasureTheory.IntegrableOn H (Set.Ioi 0)) :
    ∫ s in Set.Ioi 0, Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)
      ≤ Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (∫ s in Set.Ioi 0, H s) := by
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
    (u := Work.FTS.GalBasis.cc.Wlam) (v := fun s : ℝ => Real.sqrt (H s))
    (s := Set.Ioi (0 : ℝ)) memLp_wlam (memLp_sqrt hHnn hH)
  -- `∫ (√H)² = ∫ H` on `(0,∞)`
  have hsq : ∫ s in Set.Ioi (0 : ℝ), Real.sqrt (H s) ^ 2 = ∫ s in Set.Ioi (0 : ℝ), H s :=
    setIntegral_congr_fun measurableSet_Ioi fun s _ => Real.sq_sqrt (hHnn s)
  rw [hsq] at hcs
  -- `W2` *is* `∫_{(0,∞)} Wlam²`, so the second factor can be named
  have hW2 : Real.sqrt (∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s ^ 2)
      = Real.sqrt Work.FTS.GalBasis.cc.W2 := by
    simp only [Work.FTS.GalBasis.cc.W2]
  calc ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)
      = |∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)| :=
        (abs_of_nonneg (integral_wlam_sqrt_nonneg H)).symm
    _ ≤ Real.sqrt (∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s ^ 2)
          * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), H s) := hcs
    _ = Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), H s) := by
        rw [hW2]

end Work.FTS.StrongEps.E5Aux3
