import Mathlib
import Submission.Work.LinnikAreas.A5.Basic
import Submission.Work.LinnikAreas.A5.G0_closed
import Submission.Work.LinnikAreas.A5.g0_elementary
import Submission.Work.LinnikAreas.A5.g0_deriv_bound
import Submission.Work.LinnikAreas.A5.lam_limit

open Complex
open scoped Topology

namespace Work.LinnikAreas.A5

/-- `K · G0 K z = ∫₀ᴷ e^{−zt} (K − t) dt`: the `g0 = (K−t)/K` branch on `[0,K]` turns the
Laplace transform of `g0` into `1/K` times the Laplace transform of the affine `t ↦ K − t`. -/
lemma K_mul_G0_eq_integral {K : ℝ} (hK : 0 < K) (z : ℂ) :
    (K : ℂ) * G0 K z =
      ∫ t in (0 : ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((K - t : ℝ) : ℂ) := by
  have hcongr : G0 K z =
      ∫ t in (0 : ℝ)..K, Complex.exp (-(z * (t : ℂ))) * (((K - t) / K : ℝ) : ℂ) := by
    rw [G0]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hK.le] at ht
    rw [g0_of_le ht.2]
  rw [hcongr]
  have hpt : (∫ t in (0 : ℝ)..K, Complex.exp (-(z * (t : ℂ))) * (((K - t) / K : ℝ) : ℂ)) =
      (∫ t in (0 : ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((K - t : ℝ) : ℂ)) / (K : ℂ) := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [Complex.ofReal_div]
    ring
  rw [hpt, ← mul_div_assoc]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast ne_of_gt hK)

/-
Elementary data for the λ → 0 "limit" test function of HB 13.3: g0 K t = (K-t)/K on [0,K],
0 for t ≥ K (definition `Work.LinnikAreas.A5.g0` in `Submission/Work/LinnikAreas/A5/Basic.lean`),
normalised so that g0 K 0 = 1, together with the substitution inequality that replaces HB's
(13.2) at λ = 0:

  ‖F₂ K z‖ ≤ (2K·G0 K z).re  for Re z ≥ 0,

where F₂ K z = ((1-e^{-Kz})/z)² (`Work.LinnikContract.F2`) and G0 K is the Laplace transform of
g0.  This is the λ → 0 limit of HB's (13.2) (Re F₁(z) ≥ (λ/2)e^{Kλ}|F₂(λ+z)|): on the imaginary
axis 2K·Re G0(iy) = ‖F₂(iy)‖ holds with EQUALITY, and the extension to Re z ≥ 0 is
`Commons.Analysis.Complex.re_ge_norm_of_boundary` (boundary norm inequality plus decay).  Note
that in Lean `F2 K 0 = 0` (junk value), so the boundary function is discontinuous at 0; patch it
there or treat z = 0 separately.  The remaining items are routine: continuity, C² on (0,K) with
vanishing second derivative, and the bounds 0 ≤ g0 ≤ 1 and |g0'| ≤ 1/K on [0,K].

Here the inequality is instead obtained as the λ → 0⁺ limit of HB's (13.2) stated for λ > 0,
`Work.LinnikAreas.A5.F1_re_ge`: dividing that inequality by λ > 0 and letting λ → 0⁺ (the two
limits being `Work.LinnikAreas.A5.lam_limit`) gives `‖F₂ K z‖ ≤ 2 Re (K·G0 K z)` for z ≠ 0, and
z = 0 is handled separately (both sides being the junk value 0 resp. K²/2 · 2K ≥ 0).
-/
theorem g0_data (K : ℝ) (hK : 0 < K) :
    ContinuousOn (Work.LinnikAreas.A5.g0 K) (Set.Ici 0) ∧
    ContDiffOn ℝ 2 (Work.LinnikAreas.A5.g0 K) (Set.Ioo 0 K) ∧
    (∀ t ∈ Set.Ioo (0:ℝ) K, ‖iteratedDeriv 2 (Work.LinnikAreas.A5.g0 K) t‖ ≤ 0) ∧
    (∀ t ∈ Set.Icc (0:ℝ) K, ‖Work.LinnikAreas.A5.g0 K t‖ ≤ 1) ∧
    (∀ t : ℝ, 0 ≤ Work.LinnikAreas.A5.g0 K t) ∧
    (∀ t ∈ Set.Icc (0:ℝ) K, ‖deriv (Work.LinnikAreas.A5.g0 K) t‖ ≤ 1 / K) ∧
    (∀ z : ℂ, 0 ≤ z.re → ‖Work.LinnikContract.F2 K z‖ ≤ (2 * (K:ℂ) * Work.LinnikAreas.A5.G0 K z).re) := by
  obtain ⟨hG0c, hG0z⟩ := G0_closed K hK
  obtain ⟨hlam1, hlam2⟩ := lam_limit K hK
  obtain ⟨hcont, hcd, hidt, hbnd, hpos⟩ := g0_elementary K hK
  refine ⟨hcont, hcd, hidt, hbnd, hpos, g0_deriv_bound K hK, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · -- at `z = 0` both closed forms are junk: `F2 K 0 = 0` and `2K·G0 K 0 = K²`
    subst hz0
    have hF2 : Work.LinnikContract.F2 K 0 = 0 := by simp [Work.LinnikContract.F2]
    rw [hF2, norm_zero, hG0z]
    have h : (2 * (K:ℂ) * ((K:ℂ)/2)).re = K^2 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h]; positivity
  · -- `z ≠ 0`: pass Heath-Brown's (13.2) to the limit `λ → 0⁺`
    have hlimlhs : Filter.Tendsto
        (fun lam : ℝ => (1/2) * Real.exp (K * lam) * ‖Work.LinnikContract.F2 K ((lam:ℂ) + z)‖)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((1/2) * ‖Work.LinnikContract.F2 K z‖)) := by
      have hKlam : Filter.Tendsto (fun lam : ℝ => K * lam) (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhds (K * 0)) :=
        ((continuous_const.mul continuous_id).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
      have hexp : Filter.Tendsto (fun lam : ℝ => Real.exp (K * lam)) (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhds (Real.exp (K * 0))) := Real.continuous_exp.continuousAt.tendsto.comp hKlam
      have h12 := hexp.const_mul (1/2)
      have h := h12.mul (hlam2 z hz0)
      simpa [mul_assoc, Real.exp_zero] using h
    have hlimrhs : Filter.Tendsto (fun lam : ℝ => (Work.LinnikAreas.A5.F1 K lam z).re / lam)
        (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (((K:ℂ) * Work.LinnikAreas.A5.G0 K z).re)) := by
      have h := Complex.continuous_re.continuousAt.tendsto.comp (hlam1 z hz0)
      rw [K_mul_G0_eq_integral hK z]
      refine h.congr' ?_
      filter_upwards with lam
      exact Complex.div_ofReal_re _ _
    have h_lt1 : ∀ᶠ lam : ℝ in nhdsWithin (0:ℝ) (Set.Ioi 0), lam < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
    have hineq : (fun lam : ℝ => (1/2) * Real.exp (K * lam) * ‖Work.LinnikContract.F2 K ((lam:ℂ) + z)‖)
        ≤ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
        (fun lam : ℝ => (Work.LinnikAreas.A5.F1 K lam z).re / lam) := by
      filter_upwards [self_mem_nhdsWithin, h_lt1] with lam hpos _hlt
      have hlam : 0 < lam := hpos
      have hF := Work.LinnikAreas.A5.F1_re_ge hK hlam z hz
      have h1 : (1/2) * Real.exp (K * lam) * ‖Work.LinnikContract.F2 K ((lam:ℂ) + z)‖
          = (lam/2 * Real.exp (lam*K) * ‖Work.LinnikContract.F2 K ((lam:ℂ) + z)‖) / lam := by
        field_simp
      rw [h1]
      exact div_le_div_of_nonneg_right hF hlam.le
    have hfin := le_of_tendsto_of_tendsto hlimlhs hlimrhs hineq
    have h2 : (2 * (K:ℂ) * Work.LinnikAreas.A5.G0 K z).re
        = 2 * ((K:ℂ) * Work.LinnikAreas.A5.G0 K z).re := by
      simp [Complex.mul_re]
      ring
    rw [h2]
    linarith

end Work.LinnikAreas.A5
