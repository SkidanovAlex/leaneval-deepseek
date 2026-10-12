import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.LatGreen.RadialWeightFourierDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseFixR.LatGreen

/-- **Explicit-constant radial Fourier decay for an a.e.-measurable profile.**

The constant is `(8π(R+1)+8)·∫₀^∞ r|ψ r|`, which is uniform over families of profiles whose first
moments are bounded.  Proof: reuse of the (existential-constant) proof in
`Submission.Work.BoseFixR.LatGreen.RadialWeightFourierDecay` with the two regimes combined
explicitly: `|chat (ψ∘‖·‖) q| ≤ 4π·D` for all `q` (`D = ∫₀^∞ r²|ψ r| ≤ max R 1 · L`) and
`|chat (ψ∘‖·‖) q| ≤ 4πL/‖q‖` for `q ≠ 0`, hence at `q = (2π)•ν`
`|chat| (1+‖ν‖) ≤ 8π max R 1 L ≤ (8π(R+1)+8)L` when `‖ν‖ ≤ 1` and
`|chat| (1+‖ν‖) ≤ 2L·2 = 4L ≤ (8π(R+1)+8)L` when `‖ν‖ ≥ 1`. -/
theorem radialWeight_fourier_decay_explicit {ψ : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hψ : ∀ r : ℝ, R ≤ r → ψ r = 0)
    (hψm : AEStronglyMeasurable ψ (volume.restrict (Set.Ioi (0 : ℝ))))
    (hInt : IntegrableOn (fun r : ℝ => r * |ψ r|) (Set.Ioi (0 : ℝ))) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) ∧
      ∀ ν : EuclideanSpace ℝ (Fin 3),
        ‖FourierTransform.fourier
            (fun x : EuclideanSpace ℝ (Fin 3) => ((ψ ‖x‖ : ℝ) : ℂ)) ν‖
          ≤ (8 * Real.pi * (R + 1) + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ψ r|) / (1 + ‖ν‖) := by
  obtain ⟨hIntψ2, hIntabs2⟩ := integrableOn_sq_mul_of_aemeasurable hR hψ hψm hInt
  have hWint : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) :=
    (Submission.BoseGases.integrable_radial_r3 (f := ψ)).mpr hIntψ2
  -- the two integrals `L = ∫₀^∞ r|ψ r|` and `D = ∫₀^∞ r²|ψ r|`
  set L : ℝ := ∫ r in Set.Ioi (0 : ℝ), r * |ψ r| with hL
  set D : ℝ := ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * |ψ r| with hD
  have hLnn : 0 ≤ L := by
    rw [hL]
    exact setIntegral_nonneg measurableSet_Ioi (fun r hr => mul_nonneg hr.le (abs_nonneg _))
  have hDle : D ≤ max R 1 * L := by
    rw [hD, hL]
    have hdom : Integrable (fun r : ℝ => max R 1 * (r * |ψ r|))
        (volume.restrict (Set.Ioi (0 : ℝ))) := hInt.const_mul (max R 1)
    have hpt : (fun r : ℝ => r ^ 2 * |ψ r|)
        ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun r : ℝ => max R 1 * (r * |ψ r|)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      have hrp : 0 < r := hr
      by_cases hRr : R ≤ r
      · simp [hψ r hRr]
      · rw [show r ^ 2 * |ψ r| = r * (r * |ψ r|) from by ring]
        exact mul_le_mul_of_nonneg_right (le_trans (le_of_lt (lt_of_not_ge hRr)) (le_max_left R 1))
          (mul_nonneg hrp.le (abs_nonneg _))
    calc (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * |ψ r|)
        ≤ ∫ r in Set.Ioi (0 : ℝ), max R 1 * (r * |ψ r|) :=
          integral_mono_ae hIntabs2 hdom hpt
      _ = max R 1 * ∫ r in Set.Ioi (0 : ℝ), r * |ψ r| := integral_const_mul _ _
  -- measurability and integrability of the oscillatory integrand against `sincR`
  have hsinc_meas : ∀ q : EuclideanSpace ℝ (Fin 3), AEStronglyMeasurable
      (fun r : ℝ => Work.BoseFixR.sincR (‖q‖ * r))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun q => (measurable_sincR.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  have hgq_int : ∀ q : EuclideanSpace ℝ (Fin 3), IntegrableOn
      (fun r : ℝ => r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)) (Set.Ioi (0 : ℝ)) := by
    intro q
    refine hIntabs2.mono'
      (((continuous_id.pow 2).aestronglyMeasurable).mul hψm |>.mul (hsinc_meas q)) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg r)]
    calc r ^ 2 * |ψ r| * |Work.BoseFixR.sincR (‖q‖ * r)| ≤ r ^ 2 * |ψ r| * 1 :=
          mul_le_mul_of_nonneg_left (Work.BoseFixR.abs_sincR_le_one _)
            (mul_nonneg (sq_nonneg r) (abs_nonneg _))
      _ = r ^ 2 * |ψ r| := mul_one _
  -- the two regimes
  have hbnd1 : ∀ q : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) q|
        ≤ 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * |ψ r| := by
    intro q
    rw [Work.BoseFixR.Rb5Lin.radial_fourier_sinc hWint (fun x => rfl) q]
    have h1 : |∫ r in Set.Ioi (0 : ℝ), r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)|
        ≤ ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * |ψ r| := by
      refine le_trans (abs_integral_Ioi_le (f := fun r : ℝ =>
          r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)))
        (integral_mono_ae (integrable_abs_restrict (hgq_int q)) hIntabs2 ?_)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r _
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg r)]
      calc r ^ 2 * |ψ r| * |Work.BoseFixR.sincR (‖q‖ * r)| ≤ r ^ 2 * |ψ r| * 1 :=
            mul_le_mul_of_nonneg_left (Work.BoseFixR.abs_sincR_le_one _)
              (mul_nonneg (sq_nonneg r) (abs_nonneg _))
        _ = r ^ 2 * |ψ r| := mul_one _
    calc |4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ),
            r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)|
        = 4 * Real.pi * |∫ r in Set.Ioi (0 : ℝ),
            r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
      _ ≤ 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * |ψ r| :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  have hbnd2 : ∀ q : EuclideanSpace ℝ (Fin 3), 1 ≤ ‖q‖ →
      |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) q|
        ≤ 4 * Real.pi * (∫ r in Set.Ioi (0 : ℝ), r * |ψ r|) / ‖q‖ := by
    intro q hq
    rw [Work.BoseFixR.Rb5Lin.radial_fourier_sinc hWint (fun x => rfl) q]
    have hqpos : 0 < ‖q‖ := lt_of_lt_of_le one_pos hq
    have hqne : ‖q‖ ≠ 0 := ne_of_gt hqpos
    have h1 : |∫ r in Set.Ioi (0 : ℝ), r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)|
        ≤ (∫ r in Set.Ioi (0 : ℝ), r * |ψ r|) / ‖q‖ := by
      rw [← integral_div ‖q‖ (fun r : ℝ => r * |ψ r|)]
      refine le_trans (abs_integral_Ioi_le (f := fun r : ℝ =>
          r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)))
        (integral_mono_ae (integrable_abs_restrict (hgq_int q)) (hInt.integrable.div_const ‖q‖) ?_)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      have hrp : 0 < r := hr
      have hqr : ‖q‖ * r ≠ 0 := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg r)]
      calc r ^ 2 * |ψ r| * |Work.BoseFixR.sincR (‖q‖ * r)|
          ≤ r ^ 2 * |ψ r| * (1 / (‖q‖ * r)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg r) (abs_nonneg _))
            have h := abs_sincR_le_inv_abs hqr
            rwa [abs_of_pos (by positivity : (0 : ℝ) < ‖q‖ * r)] at h
        _ = (r * |ψ r|) / ‖q‖ := by
            field_simp
            try ring
    calc |4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ),
            r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)|
        = 4 * Real.pi * |∫ r in Set.Ioi (0 : ℝ),
            r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
      _ ≤ 4 * Real.pi * ((∫ r in Set.Ioi (0 : ℝ), r * |ψ r|) / ‖q‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * Real.pi * (∫ r in Set.Ioi (0 : ℝ), r * |ψ r|) / ‖q‖ := by ring

  refine ⟨hWint, fun ν => ?_⟩
  rw [fourier_ofReal_eq_chat hWint (fun x : EuclideanSpace ℝ (Fin 3) => by simp) ν,
    norm_ofReal_complex, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + ‖ν‖)]
  set q : EuclideanSpace ℝ (Fin 3) := (2 * Real.pi) • ν with hq
  have hqnorm : ‖q‖ = 2 * Real.pi * ‖ν‖ := by
    rw [hq, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  by_cases hν : ‖ν‖ ≤ 1
  · have h1' : |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) q|
        ≤ 4 * Real.pi * max R 1 * L := by
      have h3 : 4 * Real.pi * D ≤ 4 * Real.pi * (max R 1 * L) :=
        mul_le_mul_of_nonneg_left hDle (by positivity)
      linarith [hbnd1 q]
    have h4 : 1 + ‖ν‖ ≤ (2 : ℝ) := by linarith
    have h6 : |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) q|
          * (1 + ‖ν‖) ≤ (4 * Real.pi * max R 1 * L) * 2 :=
      mul_le_mul h1' h4 (by positivity) (by positivity)
    have h7 : (4 * Real.pi * max R 1 * L) * 2 ≤ (8 * Real.pi * (R + 1) + 8) * L := by
      have hm : max R 1 ≤ R + 1 := max_le (by linarith) (by linarith)
      have h8 : (4 * Real.pi * max R 1 * L) * 2 = 8 * Real.pi * max R 1 * L := by ring
      rw [h8]
      have hmul : 8 * Real.pi * max R 1 * L ≤ 8 * Real.pi * (R + 1) * L := by
        have h9 : (0 : ℝ) ≤ 8 * Real.pi * L := by positivity
        nlinarith [hm, hLnn, Real.pi_pos]
      have h10 : 8 * Real.pi * (R + 1) * L ≤ (8 * Real.pi * (R + 1) + 8) * L := by
        have h11 : (0 : ℝ) ≤ 8 * L := by positivity
        nlinarith [Real.pi_pos, hR, hLnn]
      linarith
    linarith
  · rw [not_le] at hν
    have hq1 : 1 ≤ ‖q‖ := by
      rw [hqnorm]
      nlinarith [hν, Real.pi_gt_three]
    have h2 : |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) q| ≤ 2 * L / ‖ν‖ := by
      have h0 := hbnd2 q hq1
      rw [← hL, hqnorm] at h0
      have hπ : (2 * Real.pi) ≠ 0 := by positivity
      calc |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) q|
          ≤ 4 * Real.pi * L / (2 * Real.pi * ‖ν‖) := h0
        _ = 2 * L / ‖ν‖ := by
            field_simp
            ring
    have h7 : (2 * L / ‖ν‖) * (1 + ‖ν‖) ≤ (8 * Real.pi * (R + 1) + 8) * L := by
      have hνpos : 0 < ‖ν‖ := by linarith
      have h5 : 1 + ‖ν‖ ≤ 2 * ‖ν‖ := by linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ hνpos]
      have h6 : 2 * L * (1 + ‖ν‖) ≤ 2 * L * (2 * ‖ν‖) :=
        mul_le_mul_of_nonneg_left h5 (by linarith)
      have h8 : 2 * L * (2 * ‖ν‖) ≤ (8 * Real.pi * (R + 1) + 8) * L * ‖ν‖ := by
        have h9 : (4 : ℝ) ≤ 8 * Real.pi * (R + 1) + 8 := by nlinarith [Real.pi_pos, hR]
        nlinarith [hLnn, norm_nonneg ν, h9]
      linarith
    have h8 : |Work.BoseFixR.chat (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) q|
          * (1 + ‖ν‖) ≤ (8 * Real.pi * (R + 1) + 8) * L :=
      le_trans (mul_le_mul_of_nonneg_right h2 (by positivity)) h7
    exact h8

end Work.BoseFixR.LatGreen
