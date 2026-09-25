import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.cauchyGreen_origin
import Submission.Work.CR.Flat.Cauchy.cauchyTransform_eq_unsub
import Submission.Work.CR.Flat.Cauchy.pompeiuFormula
import Submission.Work.CR.Flat.Cauchy.polarDz
import Submission.Work.CR.Flat.Cauchy.integrableOn_sub_div_sq
import Submission.Work.CR.Flat.Cauchy.setIntegral_polZ1_zero
import Submission.Work.CR.Flat.Cauchy.setIntegral_polZ2_zero

noncomputable section

open scoped NNReal ENNReal Real Topology
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- `w ↦ ∂_zF(w)/w` is integrable on the disc: `∂_zF` is continuous and `w ↦ w⁻¹` is
locally integrable on the plane. -/
lemma integrableOn_dzC_div_ball {ρ : ℝ} {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) :
    IntegrableOn (fun w : ℂ => dzC F w / w) (Metric.ball (0 : ℂ) ρ) := by
  have hcont : Continuous (fun w : ℂ => dzC F w) := by
    have h1 : Continuous (fun w : ℂ => fderiv ℝ F w) := hF.continuous_fderiv one_ne_zero
    rw [show (fun w : ℂ => dzC F w)
        = fun w => (1 / 2 : ℂ) * (fderiv ℝ F w 1 - Complex.I * fderiv ℝ F w Complex.I) by
      funext w; rw [dzC]]
    exact continuous_const.mul ((h1.clm_apply continuous_const).sub
      (continuous_const.mul (h1.clm_apply continuous_const)))
  have h : (fun w : ℂ => dzC F w / w) = fun w => dzC F w * w⁻¹ := by
    funext w; rw [div_eq_mul_inv]
  rw [h]
  exact ((LocallyIntegrable.continuous_mul hcont locallyIntegrable_inv_complex).integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) ρ)).mono_set Metric.ball_subset_closedBall

/-- **The `∂_z` form of the Cauchy–Green kernel identity for `1/w`.**

For `C¹` `F` vanishing on `‖w‖ ≥ ρ`, the identity
`∫_{‖w‖<ρ} (∂_zF)(w)/w dA(w) = ∫_{‖w‖<ρ} (F w - F 0)/w² dA(w)`
holds, where `dzC F w = (1/2)(∂_xF(w) - i∂_yF(w))` is the flat `∂_z` operator of
`Submission/Work/CR/Flat/Cauchy.lean`.  Both integrals are absolutely convergent
(`dzC F` is bounded on the disc and `‖w‖⁻¹` is integrable there).

This is the `∂_z`-analogue of `cauchyGreen_origin` (which handles `∂̄` and `1/ζ`), and it is
what turns the `z`-derivative of the Cauchy potential into the Beurling transform.

Put `G w = (F w - F 0)/w`.  The Leibniz rule (`dzC (w ↦ w⁻¹) = -(w ↦ w⁻²)`, note `dzC`, not
`dbarC`) gives `dzC G w = dzC F w / w - (F w - F 0)/w²` for `w ≠ 0`, so it suffices to prove
`∫_{‖w‖<ρ} dzC G = 0`.

Proof route — copy the structure of `cauchyGreen_origin.lean` (which is complete and sorry-free,
and whose polar-coordinate lemmas `polarUnit*`, `cauchyGreen_origin`, `integral_deriv_rho`,
`integral_deriv_theta`, `setIntegral_prod_rev`, `integrableOn_Ioo_prod_of_continuous`,
`polarCoord_symm_eq`, ... are available for import), with the sign of the `i∂_θ` term flipped:

* A `∂_z` analogue of `Work.CR.Flat.Cauchy.polar_algebra` in `pompeiuFormula.lean`:
  `L (cos θ + sin θ I) - (I/ρ) L (I (ρ (cos θ + sin θ I)))
     = (cos θ + sin θ I) (L 1 - I (L I))`,
  giving the pointwise chain-rule identity
  `∂_ρ G(p) - (I/ρ) ∂_θ G(p) = 2 (ζ/ρ) (dzC F)(ζ)` for `ζ = polarCoord.symm p`, `p.1 = ρ > 0`
  (i.e. `= 2 e^{iθ} (dzC F)(ζ)`).
* `Complex.integral_comp_polarCoord_symm` pushes `∫_ℂ (indicator of ball 0 ρ) * dzC G` to the
  iterated integral over `Complex.polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π`, and
  `‖polarCoord.symm p‖ = |p.1|` restricts the `ρ`-integral to `(0,ρ)`.  (Important: keep the
  indicator of `ball 0 ρ`; `dzC G` itself is *not* supported for `‖w‖ ≥ ρ`, it decays only like
  `F 0 / w²`, so `∫_ℂ dzC G` does not converge absolutely.)
* With `K(ρ,θ) = e^{-2iθ}(F(ρ e^{iθ}) - F 0)` (so `K/r = e^{-2iθ}(F(ρe^{iθ}) - F0)/ρ`),
  `ρ · dzC G (ρ e^{iθ}) = (1/2) ∂_ρ K - (i/2) ∂_θ (K/ρ)`; Fubini plus
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` (the lemmas `integral_deriv_rho`,
  `integral_deriv_theta` of `cauchyGreen_origin.lean` are templates) give
  `∫_0^ρ ∫_{-π}^{π} (1/2) ∂_ρ K dθ dρ = (1/2) ∫_{-π}^{π} (K(ρ,θ) - K(0,θ)) dθ = 0`
  (`K(0,θ) = 0`, `F(ρ e^{iθ}) = 0` by `hsupp`, and `∫_{-π}^{π} e^{-2iθ} dθ = 0`), while
  `∫_0^ρ ∫_{-π}^{π} (i/2) ∂_θ (K/ρ) dθ dρ = (i/2) ∫_0^ρ ((K/ρ)(ρ,π) - (K/ρ)(ρ,-π)) dρ = 0`
  by periodicity (`polarUnit π = polarUnit (-π) = -1`, `polarCoord_symm_pi`). -/
theorem integral_dzC_div_eq_integral_sub_div_sq {ρ : ℝ} (hρ : 0 < ρ) {F : ℂ → ℂ}
    (hF : ContDiff ℝ 1 F) (hsupp : SupportedInBall ρ F) :
    ∫ w in Metric.ball (0 : ℂ) ρ, dzC F w / w
      = ∫ w in Metric.ball (0 : ℂ) ρ, (F w - F 0) / w ^ 2 := by
  have hA : IntegrableOn (fun w : ℂ => dzC F w / w) (Metric.ball (0 : ℂ) ρ) :=
    integrableOn_dzC_div_ball hF
  have hB : IntegrableOn (fun w : ℂ => (F w - F 0) / w ^ 2) (Metric.ball (0 : ℂ) ρ) :=
    integrableOn_sub_div_sq hF
  -- The difference of the two integrands is `∂_z G` for `G = (F - F 0)/w`, and its integral
  -- over the disc vanishes by the polar computation.
  have hmain : ∫ w in Metric.ball (0 : ℂ) ρ, (dzC F w / w - (F w - F 0) / w ^ 2) = 0 := by
    -- Step 1: polar coordinates.
    have hpush : ∫ w in Metric.ball (0 : ℂ) ρ, (dzC F w / w - (F w - F 0) / w ^ 2)
        = ∫ p in Ioo (0 : ℝ) ρ ×ˢ Ioo (-Real.pi) Real.pi,
            (polZ1 F p + polZ2 F p) := by
      rw [← MeasureTheory.integral_indicator measurableSet_ball]
      rw [(Complex.integral_comp_polarCoord_symm
        ((Metric.ball (0 : ℂ) ρ).indicator
          (fun w : ℂ => dzC F w / w - (F w - F 0) / w ^ 2))).symm]
      rw [show (polarCoord.target : Set (ℝ × ℝ))
          = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from Complex.polarCoord_target]
      have key : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • (Metric.ball (0 : ℂ) ρ).indicator
              (fun w : ℂ => dzC F w / w - (F w - F 0) / w ^ 2) (Complex.polarCoord.symm p)
            = (Ioo (0 : ℝ) ρ ×ˢ Ioo (-Real.pi) Real.pi).indicator
                (fun q : ℝ × ℝ => polZ1 F q + polZ2 F q) p := by
        intro p hp
        obtain ⟨hp1, hp2⟩ := hp
        by_cases hlt : p.1 < ρ
        · have hmb : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) ρ := by
            rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp1]
            exact hlt
          have hmU : p ∈ Ioo (0 : ℝ) ρ ×ˢ Ioo (-Real.pi) Real.pi := ⟨⟨hp1, hlt⟩, hp2⟩
          rw [Set.indicator_of_mem hmb, Set.indicator_of_mem hmU, Complex.real_smul]
          exact polar_dzC_diff p hp1
        · have hmb : Complex.polarCoord.symm p ∉ Metric.ball (0 : ℂ) ρ := by
            rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp1]
            exact not_lt.mpr (not_lt.mp hlt)
          have hmU : p ∉ Ioo (0 : ℝ) ρ ×ˢ Ioo (-Real.pi) Real.pi := fun h => hlt h.1.2
          rw [Set.indicator_of_notMem hmb, Set.indicator_of_notMem hmU, smul_zero]
      rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) key]
      rw [setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
      have hset : (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) ∩
            (Ioo (0 : ℝ) ρ ×ˢ Ioo (-Real.pi) Real.pi)
          = Ioo (0 : ℝ) ρ ×ˢ Ioo (-Real.pi) Real.pi := by
        rw [Set.prod_inter_prod, Set.inter_self]
        congr 1
        ext x
        simp only [Set.mem_Ioi, Set.mem_Ioo, Set.mem_inter_iff]
        tauto
      rw [hset]
    -- Step 2: the two halves of the polar integrand have vanishing integrals
    -- (fundamental theorem of calculus in `ρ`, resp. in `θ` + periodicity).
    rw [hpush]
    have hsum : (∫ p in Ioo (0 : ℝ) ρ ×ˢ Ioo (-Real.pi) Real.pi,
          (polZ1 F p + polZ2 F p))
        = (∫ p in Ioo (0 : ℝ) ρ ×ˢ Ioo (-Real.pi) Real.pi, polZ1 F p)
          + (∫ p in Ioo (0 : ℝ) ρ ×ˢ Ioo (-Real.pi) Real.pi, polZ2 F p) :=
      MeasureTheory.integral_add (integrableOn_polZ1 hF) (integrableOn_polZ2 hF hsupp)
    have hz1 : (∫ p in Ioo (0 : ℝ) ρ ×ˢ Ioo (-Real.pi) Real.pi, polZ1 F p) = 0 :=
      setIntegral_polZ1_zero hρ hF hsupp
    have hz2 : (∫ p in Ioo (0 : ℝ) ρ ×ˢ Ioo (-Real.pi) Real.pi, polZ2 F p) = 0 :=
      setIntegral_polZ2_zero hρ hF hsupp
    rw [hsum, hz1, hz2, add_zero]
  rw [← sub_eq_zero, ← MeasureTheory.integral_sub hA hB]
  exact hmain

end Work.CR.Flat.Cauchy
