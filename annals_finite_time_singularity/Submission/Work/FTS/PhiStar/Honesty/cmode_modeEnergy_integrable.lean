/-
Copyright: work module for the Elgindi finite-time singularity project.

# The mode energy of the source: `∫_0^1 (cmode m F t)²/t⁴ dt < ∞` and
`∫_1^∞ (cmode m F t)² dt < ∞`

`Work.FTS.PhiStar.Series.cmode m F t` is the `e_m`-coefficient of the slice `F t ·` in the
self-adjoint weight `cos θ dθ`.  The two claims of this file are the *near-`0`* and the
*far-`∞`* integrability of the mode energy.

**Route.**  The sharp (Bessel/Cauchy–Schwarz) per-mode slice bound
`Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass` states, for every `z` where the
slice mass is `Iθ`-integrable,

  `eNorm m · (cmode m F z)² ≤ M z`,   `M z := ∫_{Iθ} (F z θ)² · sin(2θ)^{-η}`,

with the constant `eNorm m > 0` *independent of `z`*.  Hence

  `(cmode m F z)² / z⁴ ≤ (eNorm m)^{-1} · M z / z⁴`   (`z > 0`),
  `(cmode m F z)²      ≤ (eNorm m)^{-1} · M z`         (`z > 1`),

and the two right-hand sides are integrable on `(0,1)` resp. `(1,∞)` purely from
`HkMem α 0 F`: at level `k = 0` the `H^k`-integrand collapses to
`HkIntegrand α 0 F z θ = w z² · (F z θ)² · sin(2θ)^{-η}`, so

* `HkMem` gives the integrability of `w z² · M z`, and `M z / z⁴ = (w z² M z)/(1+z)⁴` with
  `(1+z)⁴ ≥ 1` on `(0,1)` (`integrableOn_sliceMass_div_z4_of_HkMem`);
* `w z² ≥ 1` on `(1,∞)`, so `M z ≤ w z² M z` (`integrableOn_sliceMass_Ioi_one_of_HkMem`).

The only remaining ingredient is the a.e. strong measurability of `z ↦ cmode m F z` on `(0,∞)`
(`Work.EllipticEst.ModalSolution.aesm_cmode`, the analytic content of
`aemeasurable_cmode_clamp`), restricted to the target halves of the line.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.cmode_sq_le_slice
import Submission.Work.FTS.PhiStar.Honesty.aemeasurable_cmode_clamp
import Submission.Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_div_z4_of_HkMem
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_Ioi_one_of_HkMem
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.FTS.PhiStar.Honesty

/-- At `k = 0` the `H^k`-integrand collapses to a single square: the `D_z`-sum has the one term
`i = 0` and the mixed double sum is empty. -/
private theorem HkIntegrand_zero_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- **The slice mass is `Iθ`-integrable at every `z > 0`.**  This is the hypothesis `hint`
required by the per-mode slice bounds; it follows from `HkMem α 0 F` because at level `k = 0`
the `H^k`-integrand is `w z²` times the slice mass, and `w z ≠ 0` for `z > 0`. -/
private theorem sliceMass_integrableOn_Iθ {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 0 F) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
  have hz' : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hwt : Work.FTS.EllipticEst.AngSecond.w2 z ≠ 0 := by
    rw [Work.FTS.EllipticEst.AngSecond.w2]
    exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 (by linarith : (1 : ℝ) + z ≠ 0))
      (pow_ne_zero 2 (ne_of_gt hz)))
  have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 F z θ)
      Work.Spaces.Iθ := hF.1 z hz'
  have h2 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.w2 z
      * ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) Work.Spaces.Iθ :=
    h1.congr_fun (fun θ hθ => by
      dsimp only
      rw [HkIntegrand_zero_eq α F z θ, Work.FTS.EllipticEst.AngSecond.sq_mul_W F hθ]
      simp only [Work.FTS.EllipticEst.AngSecond.sig]
      ring) measurableSet_Icc
  have h3 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.FTS.EllipticEst.AngSecond.w2 z)⁻¹ * (Work.FTS.EllipticEst.AngSecond.w2 z
        * ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))) Work.Spaces.Iθ :=
    h2.const_mul _
  exact h3.congr_fun (fun θ hθ => by field_simp) measurableSet_Icc

/-- The squared mode coefficient is a.e. strongly measurable on the open half-line `(0,∞)`. -/
private theorem aeStronglyMeasurable_cmode_sq {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  (Work.EllipticEst.ModalSolution.aesm_cmode hsm m).pow 2

theorem cmode_modeEnergy_integrable {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 0 F) :
    MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 / t ^ 4) (Set.Ioo 0 1) ∧
      MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioi 1) := by
  -- the slice mass and the per-mode bound with a `z`-independent constant
  set M : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hM
  have hEpos : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  have hbound : ∀ z : ℝ, 0 < z →
      (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        ≤ (Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * M z := by
    intro z hz
    have h := Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass (m := m) (F := F) (z := z)
      (sliceMass_integrableOn_Iθ hF hz)
    rw [hM]
    have hdiv : (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ,
            (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          / Work.EllipticEst.ModalSolution.eNorm m := by
      rw [le_div_iff₀ hEpos]
      calc (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * Work.EllipticEst.ModalSolution.eNorm m
          = Work.EllipticEst.ModalSolution.eNorm m
              * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := by ring
        _ ≤ ∫ θ in Work.Spaces.Iθ,
              (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := h
    calc (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ,
            (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          / Work.EllipticEst.ModalSolution.eNorm m := hdiv
      _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
            * (∫ θ in Work.Spaces.Iθ,
                (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          rw [div_eq_inv_mul]
  constructor
  · -- near `0`: `(cmode m F z)²/z⁴` is dominated by `M z / z⁴`, integrable by `HkMem α 0 F`
    have hMint : MeasureTheory.IntegrableOn (fun z : ℝ => M z / z ^ 4) (Set.Ioo 0 1) := by
      rw [hM]
      exact Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_div_z4_of_HkMem hF
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * (M z / z ^ 4))
        (Set.Ioo 0 1) := hMint.const_mul _
    refine hdom.mono' ?_ ?_
    · -- a.e. strong measurability on `(0,1)`
      have h1 : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
        (aeStronglyMeasurable_cmode_sq (F := F) m hsm).mono_measure
          (Measure.restrict_mono (fun z hz => hz.1) le_rfl)
      have h2 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (z ^ 4)⁻¹)
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
        ((measurable_inv.comp (Measurable.pow_const measurable_id 4)).aemeasurable).aestronglyMeasurable
      exact h1.mul h2
    · -- the pointwise domination
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo ?_
      intro z hz
      have hz4 : (0 : ℝ) < z ^ 4 := pow_pos hz.1 4
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hz4))]
      calc (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 / z ^ 4
          ≤ ((Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * M z) / z ^ 4 :=
            div_le_div_of_nonneg_right (hbound z hz.1) (le_of_lt hz4)
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * (M z / z ^ 4) := by ring
  · -- far `∞`: `(cmode m F z)²` is dominated by `M z`, integrable by `HkMem α 0 F`
    have hMint : MeasureTheory.IntegrableOn M (Set.Ioi 1) := by
      rw [hM]
      exact Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_Ioi_one_of_HkMem hF
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * M z) (Set.Ioi 1) :=
      hMint.const_mul _
    refine hdom.mono' ?_ ?_
    · have h1 : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
        (aeStronglyMeasurable_cmode_sq (F := F) m hsm).mono_measure
          (Measure.restrict_mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)) le_rfl)
      simpa only using h1
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro z hz
      have hz1 : 0 < z := by linarith [Set.mem_Ioi.mp hz]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound z hz1

end Work.FTS.PhiStar.Honesty
