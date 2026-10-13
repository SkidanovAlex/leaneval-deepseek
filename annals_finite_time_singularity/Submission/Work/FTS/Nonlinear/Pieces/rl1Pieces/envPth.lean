/-
# The `rl¹`-envelope of `∂_θ g` (`rl1Pieces/envPth`)

This file proves **`Work.FTS.Nonlinear.Pieces.rl1Pieces.envPth`**, the third of the three
*basis bounds* of the `rl¹`-norm of the perturbation `g`: the full `rl¹`-norm of `∂_θ g`,

  `∫⁻_r r⁻¹ (∫⁻_θ |∂_θ g (r,θ)|)  ≤  10 √(10/α) · |g|_{ℋ⁴}`,

for `0 < α ≤ 1` and admissible data (`SmoothQuad g`, `HkMem α 4 g`).

## Mathematics

`D_θ g = sin(2θ) ∂_θ g`, so `|∂_θ g| = |D_θ g| / sin(2θ) = |D_θ g| sin(2θ)^{-γ/2} ·
sin(2θ)^{γ/2-1}` and Cauchy–Schwarz in `θ` gives

  `∫_θ |∂_θ g| ≤ √(∫_θ (D_θg)² sin(2θ)^{-γ}) · √(∫_θ sin(2θ)^{γ-2})`,

the second factor being the `α^{-1/2}` of Elgindi's `γ = 1 + α/10`: the *sharp* value of
the integral is `(√π/2) Γ((γ-1)/2)/Γ(γ/2) ≈ 1/(γ-1) = 10/α`, and
`Work.Spaces.integral_sin_rpow` supplies the generous bound `100/(γ-1) = 1000/α`.

For the radial step write `r⁻¹ = w(r) · r/(1+r)²` and
`w(r)√E = √(w(r)²E) ≤ √(∫_θ HkIntegrand)`
(the mixed `(i,j) = (1,0)` slot of the `ℋ⁴`-integrand); then Cauchy–Schwarz in `r` against
the two `L²`-functions `r ↦ r/(1+r)²` (`∫ (r/(1+r)²)² ≤ 1`) and `r ↦ √(∫_θ HkIntegrand)`
gives the statement.  The radial Hölder engine is
`Work.FTS.Nonlinear.Pieces.rl1Tools.radial_of_sqrt`.

Everything is formulated with `∫⁻`, so no integrability of `∂_θ g` has to be assumed; the
only integrability statement needed is the per-slice one, which follows from the AM–GM
bound `|∂_θ g| ≤ ((D_θg)² sin^{-γ} + sin^{γ-2})/2`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gSlots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

set_option maxHeartbeats 1600000

/-! ## The two auxiliary estimates -/

/-- The angular Cauchy–Schwarz partner of `∂_θ g`: with `γ = 1 + α/10`,

  `√(∫_θ sin(2θ)^{γ-2}) ≤ 10 √(10/α)`  (the sharp value of the integral is `≈ 10/α`).

`Work.Spaces.integral_sin_rpow` gives `∫_θ sin(2θ)^{γ-2} ≤ 100/(γ-1) = 1000/α`, and
`√(1000/α) = √100 · √(10/α) = 10 √(10/α)`. -/
theorem sqrt_integral_sin_rpow {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2))
      ≤ 10 * Real.sqrt (10 / α) := by
  have h := Work.Spaces.integral_sin_rpow α hα hα1
  have hg1 : Work.Spaces.gam α - 1 = α / 10 := by rw [Work.Spaces.gam]; ring
  rw [hg1] at h
  have h100 : (100 : ℝ) / (α / 10) = 1000 / α := by ring
  rw [h100] at h
  refine le_trans (Real.sqrt_le_sqrt h) ?_
  rw [show (1000 : ℝ) / α = 100 * (10 / α) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 100)]
  have h10 : Real.sqrt (100 : ℝ) = 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h10]

/-- The `θ`-slice of `∂_θ g` is integrable on `Iθ` for `r > 0`, for admissible data.

This is the only integrability fact the envelope needs: it lets the `∫⁻`-statement be
converted into one about the ordinary integral.  The bound is the AM–GM inequality
`|∂_θ g| = (|D_θg| sin^{-γ/2})·(sin^{γ/2-1}) ≤ ((D_θg)² sin^{-γ} + sin^{γ-2})/2`,
whose two terms are integrable because `(D_θg)² sin^{-γ} ≤ HkIntegrand α 4 g`
(`Dth_sq_le_HkIntegrand`) resp. `-1 < γ-2 ≤ 0` (`Work.Spaces.sin_two_rpow`). -/
theorem integrableOn_pth_slice {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {r : ℝ}
    (hr : 0 < r) :
    MeasureTheory.IntegrableOn (fun θ => |Work.Spaces.pth g r θ|) Work.Spaces.Iθ := by
  -- the `D_θ`-slice, with its `sin(2θ)^{-γ}` weight, is dominated by the `ℋ⁴`-integrand
  have hDint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ := by
    change Integrable
      (fun θ => (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ)
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
    refine Integrable.mono'
      ((hmem.1 r hr.le).mono_set (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩)) ?_ ?_
    · have hcont : ContinuousOn
          (fun θ => (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Set.Ioo (0 : ℝ) (π / 2)) :=
        ((Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Dth_slice hsm hr).pow 2).mul
          (((Real.continuous_sin.comp
            (continuous_const.mul continuous_id)).continuousOn).rpow_const
              (fun θ hθ => Or.inl
                (ne_of_gt (Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ))))
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hpt := Work.FTS.Nonlinear.Pieces.rl1Tools.Dth_sq_le_HkIntegrand α hα (g := g) hr hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ)) _))]
      exact hpt
  have hSint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2)
      (by rw [Work.Spaces.gam]; linarith) (by rw [Work.Spaces.gam]; linarith)).1
  -- the AM–GM majorant
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ => ((Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) / 2) Work.Spaces.Iθ :=
    (hDint.add hSint).div_const 2
  refine Integrable.mono' hmaj ?_ ?_
  · -- a.e. strong measurability, from the identity `|∂_θg| = |D_θg|/sin(2θ)` on `(0,π/2)`
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
    have hQ : ContinuousOn
        (fun θ => |Work.Spaces.Dth g r θ| * (Real.sin (2 * θ))⁻¹) (Set.Ioo (0 : ℝ) (π / 2)) :=
      (Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Dth_slice hsm hr).abs.mul
        (ContinuousOn.inv₀
          ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
          (fun θ hθ => ne_of_gt (Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ)))
    have hQaesm : AEStronglyMeasurable
        (fun θ => |Work.Spaces.Dth g r θ| * (Real.sin (2 * θ))⁻¹)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
      hQ.aestronglyMeasurable measurableSet_Ioo
    refine hQaesm.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    show |Work.Spaces.Dth g r θ| * (Real.sin (2 * θ))⁻¹ = |Work.Spaces.pth g r θ|
    have hs := Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.abs_Dth_eq hθ]
    rw [mul_assoc, mul_comm (|Work.Spaces.pth g r θ|) ((Real.sin (2 * θ))⁻¹), ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hs), one_mul]
  · -- the pointwise AM–GM bound
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hs := Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ
    set A : ℝ := |Work.Spaces.Dth g r θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
      with hA
    set B : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1) with hB
    have hpow : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
      congr 1
      ring
    have hA2 : A ^ 2
        = (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [hA, mul_pow, sq_abs, hpow]
    have hpowB : ((Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
      congr 1
      ring
    have hB2 : B ^ 2 = (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2) := by
      rw [hB, hpowB]
    have hab : |Work.Spaces.pth g r θ| = A * B := by
      have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
            * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1)
          = (Real.sin (2 * θ)) ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hs]
        congr 1
        ring
      rw [hA, hB, mul_assoc, h1, Work.FTS.Nonlinear.Pieces.rl1Tools.abs_Dth_eq hθ,
        Real.rpow_neg_one]
      rw [mul_comm (Real.sin (2 * θ)) (|Work.Spaces.pth g r θ|), mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hs), mul_one]
    rw [Real.norm_eq_abs, abs_abs, hab]
    calc A * B ≤ (A ^ 2 + B ^ 2) / 2 := by nlinarith [sq_nonneg (A - B)]
      _ = ((Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            + (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) / 2 := by
          rw [hA2, hB2]

/-! ## The target -/

theorem envPth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.pth g r θ|))
      ≤ ENNReal.ofReal (10 * Real.sqrt (10 / α) * Work.Spaces.HkNorm α 4 g) := by
  set cc : ℝ := 10 * Real.sqrt (10 / α) with hcc
  have hcc_nn : 0 ≤ cc := by rw [hcc]; positivity
  have hsqrtC := sqrt_integral_sin_rpow hα hα1
  have hsqrtC' : Real.sqrt (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) ≤ cc := by rw [hcc]; exact hsqrtC
  -- ## The per-slice estimate
  have key : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.pth g r θ|)
        ≤ ENNReal.ofReal (cc * (r / (1 + r) ^ 2) *
            Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)) := by
    intro r hr
    have hw : 0 < Work.Spaces.w r := Work.FTS.Nonlinear.Pieces.rl1Tools.w_pos_of_pos hr
    have hzw : r⁻¹ = Work.Spaces.w r * (r / (1 + r) ^ 2) := by
      rw [Work.Spaces.w, inv_eq_one_div]; field_simp
    have hint := integrableOn_pth_slice hα hα1 hsm hmem hr
    have hlin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.pth g r θ|)
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth g r θ|) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun θ => abs_nonneg _)).symm
    -- Cauchy–Schwarz in `θ`, with the `D_θ`-slot of the `ℋ⁴`-integrand
    have hreal :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.slice_pth_abs_le_sqrt α hα hα1 hsm hmem r hr
    have hslot : (Work.Spaces.w r) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 r hr.le) ?_
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        refine mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) ?_)
        refine Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
      · rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
        exact Work.FTS.Nonlinear.Pieces.rl1Tools.w2_Dth_sq_le_HkIntegrand α hα hr hθ
    -- the radial weight `r⁻¹ = w(r)·r/(1+r)²` and `w(r)√E ≤ √(∫_θ HkIntegrand)`
    have hwE : Work.Spaces.w r *
          Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) := by
      rw [show Work.Spaces.w r * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          = Real.sqrt ((Work.Spaces.w r) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hw)]]
      exact Real.sqrt_le_sqrt hslot
    have hinner : r⁻¹ * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth g r θ|)
        ≤ cc * (r / (1 + r) ^ 2) *
            Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) := by
      calc r⁻¹ * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth g r θ|)
          ≤ r⁻¹ * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
              * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2))) :=
            mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr hr.le)
        _ = (Work.Spaces.w r * (r / (1 + r) ^ 2)) *
              (Real.sqrt (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                  (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2))) := by rw [hzw]
        _ = (r / (1 + r) ^ 2) *
              ((Work.Spaces.w r * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
                * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                    (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2))) := by ring
        _ ≤ (r / (1 + r) ^ 2) *
              (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) * cc) := by
            refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hr.le (by positivity))
            exact mul_le_mul hwE hsqrtC' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = cc * (r / (1 + r) ^ 2) *
              Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) := by ring
    rw [hlin, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
    exact ENNReal.ofReal_le_ofReal hinner
  -- ## The radial Hölder step
  have hae : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.pth g r θ|)
        ≤ ENNReal.ofReal (cc * (r / (1 + r) ^ 2) *
            Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => key r hr)
  have hmain := Work.FTS.Nonlinear.Pieces.rl1Tools.radial_of_sqrt
    (J := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
    (A := fun r => ENNReal.ofReal r⁻¹ *
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.pth g r θ|))
    (c := cc) hcc_nn (hmem.2.mono_set Set.Ioi_subset_Ici_self)
    (fun r => MeasureTheory.integral_nonneg
      fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g r θ) hae
  rw [← Work.FTS.Nonlinear.Pieces.rl1Tools.HkSq_eq_integral_Ioi α g] at hmain
  refine le_trans hmain ?_
  rw [hcc]
  exact le_of_eq rfl

end Work.FTS.Nonlinear.Pieces.rl1Pieces
