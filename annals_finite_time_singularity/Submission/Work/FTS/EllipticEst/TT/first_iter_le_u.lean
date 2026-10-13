import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs
import Submission.Work.FTS.EllipticEst.slice_deriv_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- For `0 ≤ s ≤ 1`, `0 < γ` and `γ ≤ 2` one has `s ^ 2 * s ^ (-γ) ≤ 1`: it is the standard
comparison `s ^ (2 - γ) ≤ s ^ 0 = 1` (the case `s = 0` is trivial). -/
private lemma sq_mul_rpow_neg_le_one {s γ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ0 : 0 < γ) (hγ2 : γ ≤ 2) : s ^ 2 * s ^ (-γ) ≤ 1 := by
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow (show (-γ) ≠ 0 by linarith)]
    norm_num
  · rw [show s ^ 2 = s ^ (2 : ℝ) from (Real.rpow_two s).symm,
      ← Real.rpow_add h (2 : ℝ) (-γ), show (2 : ℝ) + -γ = 2 - γ by ring]
    calc s ^ (2 - γ) ≤ s ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_ge h hs1 (by linarith)
      _ = 1 := Real.rpow_zero s

/-- **The first angular derivative costs nothing, uniformly in `α` and `u`.**

There is a universal constant `C` such that for every `α ∈ (0, 1/4]` and every `u` smooth on a
neighbourhood of `[0, π/2]` with `u 0 = u (π/2) = 0`, with `Gη u` and `Fη u` honest integrals,

`Gγ α 1 u = ∫_θ (D_θ u)² sin(2θ)^{-γ} ≤ C (Gη u + Fη u)`,  `γ = 1 + α/10`.

`C` is quantified before `α` and `u`, so in particular it must not blow up as `γ → 1`.

Proof route: `(D_θ u)² sin(2θ)^{-γ} = (u')² sin(2θ)^{2-γ} ≤ (u')²` (as `2 - γ ≥ 0` and
`sin(2θ) ≤ 1` on `Iθ`).  For `∫_{Iθ}(u')²` use the pointwise boundary estimate
`Work.FTS.EllipticEst.slice_deriv_sq_le`, which gives
`(∂_θ u θ)² ≤ (∫_{Iθ} (u'')² sin(2θ)^{-η}) · (∫_{Iθ} sin(2θ)^η) ≤ (π/2) Gη u` for every
`θ ∈ Iθ` (the two endpoint values of `u` agree, so `∂_θ u` has a zero on `Iθ`; Rolle plus
Cauchy–Schwarz).  Integrating over `Iθ` and using `∫_{Iθ} sin(2θ)^η ≤ π/2` yields
`∫_{Iθ}(u')² ≤ (π/2)² Gη u`, and then `(π/2)² Gη u ≤ 4 (Gη u + Fη u)` because `Fη u ≥ 0`. -/
theorem first_iter_le_u : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 / 4 → Work.Elliptic.SmoothSlice u → u 0 = 0 →
      u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      Work.FTS.EllipticEst.TT.Gγ α 1 u ≤ C * (Work.FTS.EllipticEst.TT.Gη u + Work.FTS.EllipticEst.TT.Fη u) := by
  refine ⟨4, by norm_num, ?_⟩
  intro α u hα hα4 hsm h0 h1 hGint _hFint
  -- ### The constants
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hγ2 : Work.Spaces.gam α ≤ 2 := by
    rw [Work.Spaces.gam]; linarith
  -- ### Nonnegativity of the two energies
  have hGηnn : 0 ≤ Gη u := by
    rw [Gη]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  have hFηnn : 0 ≤ Fη u := by
    rw [Fη]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  -- ### The pointwise comparison `(D_θ u)² sin(2θ)^{-γ} ≤ (u')²`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * sGam α θ ≤ (deriv u θ) ^ 2 := by
    intro θ hθ
    have hsin0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hkey := sq_mul_rpow_neg_le_one hsin0 hsin1 hγpos hγ2
    simp only [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_zero,
      Work.Elliptic.Dth1, sGam]
    rw [mul_pow]
    have hre : (Real.sin (2 * θ)) ^ 2 * (deriv u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (deriv u θ) ^ 2
          * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      ring
    rw [hre]
    calc (deriv u θ) ^ 2
          * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ (deriv u θ) ^ 2 * 1 := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
      _ = (deriv u θ) ^ 2 := by ring
  -- ### Step 1: `Gγ α 1 u ≤ ∫_{Iθ} (u')²`
  have hderiv_cont : ContinuousOn (deriv u) Work.Spaces.Iθ := by
    have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
      intro x hx
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
    exact ((hsm.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn).mono hsub
  have hd2_int : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ :=
    (hderiv_cont.pow 2).integrableOn_compact isCompact_Icc
  have hstep1 : (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * sGam α θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 := by
    refine integral_mono_of_nonneg ?_ hd2_int ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (sGam_nonneg α hθ)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hpt θ hθ
  -- ### Step 2: `∫_{Iθ} (u')² ≤ (π/2)² Gη u`, via the pointwise boundary estimate
  have hss : Work.FTS.EllipticEst.SliceSmooth u := hsm
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := by
    simpa only [Work.FTS.EllipticEst.sliceV, D2, Work.FTS.EllipticEst.thEta, sEta]
      using hGint
  have hB : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      ≤ Real.pi / 2 := (Work.FTS.EllipticEst.integrableOn_sin_two_rpow
        Work.Spaces.eta_nonneg).2
  have hBnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) :=
    setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg hθ) _)
  have hbd : ∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2
      ≤ Gη u * (∫ θ' in Work.Spaces.Iθ, (Real.sin (2 * θ')) ^ (Work.Spaces.eta)) := by
    intro θ hθ
    have h := Work.FTS.EllipticEst.slice_deriv_sq_le hss (by rw [h0, h1]) hint θ hθ
    simpa only [Gη, D2, Work.FTS.EllipticEst.sliceV, sEta, Work.FTS.EllipticEst.thEta] using h
  have hvol : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def,
      show (volume : Measure ℝ) Work.Spaces.Iθ = ENNReal.ofReal (Real.pi / 2) from by
        rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl, Real.volume_Icc,
          sub_zero],
      ENNReal.toReal_ofReal (by positivity)]
  have hconst_int : MeasureTheory.IntegrableOn
      (fun _ : ℝ => Gη u * (∫ θ' in Work.Spaces.Iθ, (Real.sin (2 * θ')) ^ (Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    integrableOn_const (by
      rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl, Real.volume_Icc,
        sub_zero]
      exact ENNReal.ofReal_ne_top)
  have hstep2 : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      ≤ (Real.pi / 2) ^ 2 * Gη u := by
    have h1 : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ,
            Gη u * (∫ θ' in Work.Spaces.Iθ, (Real.sin (2 * θ')) ^ (Work.Spaces.eta)) := by
      refine integral_mono_of_nonneg ?_ hconst_int ?_
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        exact sq_nonneg _
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hbd θ hθ
    have h2 : (∫ θ in Work.Spaces.Iθ,
          Gη u * (∫ θ' in Work.Spaces.Iθ, (Real.sin (2 * θ')) ^ (Work.Spaces.eta)))
        = (Real.pi / 2)
          * (Gη u * (∫ θ' in Work.Spaces.Iθ, (Real.sin (2 * θ')) ^ (Work.Spaces.eta))) := by
      rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
    rw [h2] at h1
    have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
    calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ (Real.pi / 2)
            * (Gη u * (∫ θ' in Work.Spaces.Iθ, (Real.sin (2 * θ')) ^ (Work.Spaces.eta))) := h1
      _ ≤ (Real.pi / 2) * (Gη u * (Real.pi / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hGηnn) (le_of_lt hpi2)
      _ = (Real.pi / 2) ^ 2 * Gη u := by ring
  -- ### Assembly
  have hGγ_le : Gγ α 1 u ≤ (Real.pi / 2) ^ 2 * Gη u := by
    rw [Gγ]
    exact le_trans hstep1 hstep2
  have hπ2 : (Real.pi / 2) ^ 2 ≤ 4 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hfinal : (Real.pi / 2) ^ 2 * Gη u ≤ 4 * (Gη u + Fη u) := by
    nlinarith [mul_le_mul_of_nonneg_right hπ2 hGηnn, hFηnn]
  linarith [hGγ_le, hfinal]

end Work.FTS.EllipticEst.TT
