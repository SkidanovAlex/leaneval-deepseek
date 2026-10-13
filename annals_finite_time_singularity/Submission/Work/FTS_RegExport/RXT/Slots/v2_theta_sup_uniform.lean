/-
Copyright: work module for the Elgindi finite-time singularity project.

# `v2_theta_sup_uniform` — the *uniform* angular sup bound for a mixed slot

For `0 < α ≤ 1`, a datum `f` which is `C⁴` on the open quadrant and honestly in `ℋ⁴`, and a
mixed slot `D_z^b D_θ^a f` of order `a + b ≤ 3`, there is a constant `K = K(α) ≥ 0` — the
**same** for every `f` and every slot — with

  `(D_z^b D_θ^a f (s,θ) · w(s))² ≤ K · ∫_σ HkIntegrand α 4 f (s,σ) dσ`

for every `s > 0` and every `θ ∈ (0,π/2)`, where `w(s) = (1+s)²/s²`.

The point is that the radial weight `w` is a function of `s` alone, so it commutes with every
`θ`-derivative; the whole estimate is therefore *angular*, and the constant is independent of
the slot and of the datum.

The analytic ingredients (the pointwise slot bounds against `HkIntegrand`, the integrability
of the two angular integrands, and the angular mean–variation bound of Agmon type) live in the
companion module `Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_aux`; here only the
assembly by `D_θ = sin(2θ) ∂_θ`, `w(s)²` and `∫_{Iθ} sin(2θ)^{γ-2} ≤ 100/(γ-1)` is performed.
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.integral_sin_rpow
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The target -/

theorem v2_theta_sup_uniform {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℝ → ℝ,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 f →
      ∀ b a : ℕ, a + b ≤ 3 → ∀ s : ℝ, 0 < s → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed b a f s θ * Work.Spaces.w s) ^ 2
        ≤ K * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ) := by
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]; linarith
  refine ⟨8 / Real.pi + 200 / (Work.Spaces.gam α - 1), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 8 / Real.pi := by positivity
    have h2 : (0 : ℝ) ≤ 200 / (Work.Spaces.gam α - 1) :=
      div_nonneg (by norm_num) hγpos.le
    linarith
  intro f h4 hmem b a hab s hs θ hθ0 hθ1
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hWnn : (0 : ℝ) ≤ Work.Spaces.w s := w_nonneg_aux s
  -- the two hypotheses of the angular bound
  have hderiv : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' => Work.Spaces.mixed b a f s σ')
        (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) σ := by
    intro σ hσ
    exact ((Work.FTS_RegExport.RXA1w.contDiffOn_slice_mixed h4 b a 1 (by omega) hs).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hσ) |>.hasDerivAt
  have hgc : ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := continuousOn_pth_mixed_slice_aux h4 b a (by omega) hs
  have hI1 := integrable_slot_sq_aux hα h4 hmem b a hab hs
  have hI2 := integrable_pth_sq_sin_aux hα h4 hmem b a hab hs
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hang := angular_meanVar_aux (γ := Work.Spaces.gam α) hγ1 hγ2 hderiv hgc hI1 hI2 θ hθmem
  -- the scalar bounds
  have hAeq : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2) * (Work.Spaces.w s) ^ 2
      = ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun σ => by ring)
  have hAle : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2) * (Work.Spaces.w s) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ := by
    rw [hAeq]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun σ => sq_nonneg _)
      (hmem.1 s hsI) ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact slot_le_HkIntegrand_aux hα b a (by omega) s hσ
  have hBeq : (∫ σ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2
      = ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
    have hpth : Work.Spaces.pth (Work.Spaces.mixed b a f) s σ
        = Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ) := by
      have hD := Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a (by omega) hs hσ
      rw [Work.Spaces.Dth] at hD
      rw [eq_div_iff (ne_of_gt hsin), mul_comm]
      exact hD
    rw [hpth]
    have h2 : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
        Real.rpow_add hsin, Real.rpow_ofNat]
    have e1 : (Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ)) ^ 2
        = (Work.Spaces.mixed b (a + 1) f s σ) ^ 2 / (Real.sin (2 * σ)) ^ 2 :=
      div_pow _ _ 2
    have hwne : Work.Spaces.w s ≠ 0 := ne_of_gt (w_pos_aux hs)
    rw [e1, h2]
    field_simp <;> ring_nf
  have hBle : (∫ σ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ := by
    rw [hBeq]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 s hsI) ?_
    · filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _)
    · filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
      exact slot_sin_le_HkIntegrand_aux hα b a (by omega) s hσ
  have hGle : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
      ≤ 100 / (Work.Spaces.gam α - 1) := Work.Spaces.integral_sin_rpow α hα hα1
  have hGnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _
  have hHnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ :=
    MeasureTheory.integral_nonneg fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f s σ
  have hAnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2 :=
    MeasureTheory.integral_nonneg fun σ => sq_nonneg _
  have hBnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _)
  -- assembly
  have h3 : (0 : ℝ) ≤ 8 / Real.pi := by positivity
  have h4 : (0 : ℝ) ≤ 2 * (∫ σ in Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2)) := by linarith
  have h5 : 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
      ≤ 200 / (Work.Spaces.gam α - 1) := by
    have h5a : 2 * (100 / (Work.Spaces.gam α - 1)) = 200 / (Work.Spaces.gam α - 1) := by
      field_simp <;> norm_num
    linarith
  calc (Work.Spaces.mixed b a f s θ * Work.Spaces.w s) ^ 2
      = (Work.Spaces.mixed b a f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by ring
    _ ≤ ((8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2)
          + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)))
        * (Work.Spaces.w s) ^ 2 := mul_le_mul_of_nonneg_right hang (sq_nonneg _)
    _ = (8 / Real.pi) * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2)
            * (Work.Spaces.w s) ^ 2)
        + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2) := by
      ring
    _ ≤ (8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ)
        + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ) :=
      add_le_add (mul_le_mul_of_nonneg_left hAle h3) (mul_le_mul_of_nonneg_left hBle h4)
    _ ≤ (8 / Real.pi + 200 / (Work.Spaces.gam α - 1))
          * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ) := by
      have h6 := mul_le_mul_of_nonneg_right h5 hHnn
      have h7 : (8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ)
            + (200 / (Work.Spaces.gam α - 1))
              * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ)
          = (8 / Real.pi + 200 / (Work.Spaces.gam α - 1))
              * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ) := by
        ring
      linarith [h6, h7]

end Work.FTS_RegExport.RXT.Slots
