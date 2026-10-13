import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.slice_u_div_cos_sq_le
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-!
# A uniform-in-`γ` bound for `(u / cos θ)² sin(2θ)^{2-γ}`

`Work.FTS.EllipticEst.remov.slice_u_div_cos_sq_le` proves, for each fixed `γ ∈ [1, 3/2]`, the
slice inequality

`∫_{Iθ} (u/cos θ)² sin(2θ)^{2-γ} ≤ C(γ) (∫_{Iθ} (u')² + ∫_{Iθ} u²)`

with a constant `C(γ)` that a priori depends on `γ`.  The quantifier placement is however
immaterial, because `Iθ = [0, π/2]` is exactly the set on which `0 ≤ sin(2θ) ≤ 1`: there the
weight `sin(2θ)^{2-γ}` is a *decreasing* function of `γ`, so the single instance `γ = 3/2` — the
worst case — dominates all the others,

`sin(2θ)^{2-γ} ≤ sin(2θ)^{1/2}`  for `γ ≤ 3/2`, `θ ∈ Iθ`.

Hence one may take `C := C(3/2)`: integrability of the general integrand is supplied by the
`γ`-instance of the sibling theorem, and the integral comparison follows from
`MeasureTheory.integral_mono_ae` between two integrable functions.
-/

/-- On `Iθ = [0, π/2]` the weight `sin(2θ)^{2-γ}` is decreasing in `γ`: for `γ ≤ 3/2` it is
bounded by the exponent-`1/2` weight. -/
private lemma sin_rpow_two_sub_mono {γ : ℝ} (hγ : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ Real.rpow (Real.sin (2 * θ)) (2 - (3 / 2 : ℝ)) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · have h1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) = 0 := by
      rw [← h0]
      exact Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
    have h2 : Real.rpow (Real.sin (2 * θ)) (2 - (3 / 2 : ℝ)) = 0 := by
      rw [← h0]
      exact Real.zero_rpow (by norm_num : (2 : ℝ) - 3 / 2 ≠ 0)
    rw [h1, h2]
  · exact Real.rpow_le_rpow_of_exponent_ge hpos (Real.sin_le_one _) (by linarith)

/-- Pointwise monotonicity of the whole integrand in `γ` on `Iθ`. -/
private lemma integrand_le_of_gamma_le {γ : ℝ} (hγ : γ ≤ 3 / 2) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - (3 / 2 : ℝ)) :=
  mul_le_mul_of_nonneg_left (sin_rpow_two_sub_mono hγ hθ) (sq_nonneg _)

theorem sliceUdivCosUniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u : ℝ → ℝ), 1 ≤ γ → γ ≤ 3 / 2 →
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))) := by
  -- the worst case `γ = 3/2` supplies both the constant and the dominating integrand
  obtain ⟨C, hCpos, H⟩ := slice_u_div_cos_sq_le (3 / 2) (by norm_num) (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro γ u hγ1 hγ2 hC3 hcont hu0 hpi hIntd hIntu
  obtain ⟨_, _, Hγ⟩ := slice_u_div_cos_sq_le γ hγ1 hγ2
  obtain ⟨hIntγ, _⟩ := Hγ u hC3 hcont hu0 hpi hIntd hIntu
  obtain ⟨hInt32, hle32⟩ := H u hC3 hcont hu0 hpi hIntd hIntu
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact measurableSet_Icc
  have hmono : (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ≤ (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - (3 / 2 : ℝ))) := by
    refine MeasureTheory.integral_mono_ae hIntγ hInt32 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθ
    exact integrand_le_of_gamma_le hγ2 u hθ
  exact ⟨hIntγ, le_trans hmono hle32⟩

end Work.FTS.EllipticEst.remov
