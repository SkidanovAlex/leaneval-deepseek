/-
# The `L¹`-mass of `λ_k · η_{≤jj}''`

This is the estimate that bounds the whole-line integral

  `∫ ‖λ_k(x) · η_{≤jj}''(x)‖ dx`

by `C · 2^k · (max (2^{k+jj-1}) 1)^{-N}` for `k ≤ 0`, `0 ≤ jj`, `0 ≤ k + jj`, uniformly in `k`
and `jj` (with `C` depending on `N`).  It is one of the three terms produced by the Leibniz rule
for the second derivative of the "mid-range" piece `η_{≤jj} λ_k` of the off-diagonal decomposition
of the Ionescu--Wainger projections (see `offPieceMid`, `offPiece3MassDecay`).

## The mathematics

Two facts are used.

* `offCutDeriv`: `‖η_{≤jj}''(x)‖ ≤ Cd · (2^{-jj})²` for *every* `x`, uniformly in `jj`.
* `offLamTail` (for `i = 0`): the tail of `λ_k = 𝓕⁻ η_{≤k}` beyond the scale `R` satisfies
  `∫⁻_{R ≤ |x|} ‖λ_k(x)‖ ≤ Ct · (max (2^k R) 1)^{-N}`.

The second derivative `η_{≤jj}''` vanishes on the ball `{|x| < 2^{jj-1}}` — the cutoff is locally
constant there (`bmp_one_of_le`, and `Filter.EventuallyEq.iteratedDerivWithin_eq`)— so the
integrand is supported on the tail `{|x| ≥ 2^{jj-1}}`, where the Schwartz decay of `λ_k` applies:

  `∫ ‖λ_k · η_{≤jj}''‖ ≤ Cd (2^{-jj})² · ∫⁻_{2^{jj-1} ≤ |x|} ‖λ_k‖
      ≤ Cd Ct (2^{-jj})² (max (2^{k+jj-1}) 1)^{-N}`,

and `(2^{-jj})² = 2^{-2jj} ≤ 2^k` because `jj ≥ -k` (from `0 ≤ k + jj`) and `k ≤ 0`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.offCutDeriv
import Submission.Work.KMTAreas.A4.offPieceMid

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- The second derivative of the rescaled cutoff `η_{≤jj}` vanishes on the ball
`{|x| < 2^{jj-1}}` on which the cutoff is identically `1`. -/
theorem iteratedDeriv2_bmp_eq_zero_of_abs_lt (jj : ℤ) {x : ℝ}
    (hx : |x| < (2 : ℝ) ^ (jj - 1)) :
    iteratedDeriv 2 ((bmp jj : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 := by
  have hpos : 0 < (2 : ℝ) ^ (jj - 1) - |x| := by
    have h0 : (0 : ℝ) < (2 : ℝ) ^ (jj - 1) := zpow_pos (by norm_num) _
    linarith
  have hev : ((bmp jj : SchwartzMap ℝ ℂ) : ℝ → ℂ) =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Metric.ball x ((2 : ℝ) ^ (jj - 1) - |x|), Metric.ball_mem_nhds x hpos, ?_⟩
    intro z hz
    rw [Metric.mem_ball, Real.dist_eq] at hz
    have hz' : |z| ≤ (2 : ℝ) ^ (jj - 1) := by
      have h1 : z = x + (z - x) := by ring
      rw [h1]
      calc |x + (z - x)| ≤ |x| + |z - x| := abs_add_le _ _
        _ ≤ |x| + ((2 : ℝ) ^ (jj - 1) - |x|) := by linarith
        _ = (2 : ℝ) ^ (jj - 1) := by ring
    exact bmp_one_of_le jj hz'
  have h := Filter.EventuallyEq.iteratedDerivWithin_eq (s := Set.univ) (n := 2)
    (by simpa using hev) (by simpa using hev.eq_of_nhds)
  rw [iteratedDerivWithin_univ, iteratedDerivWithin_univ, iteratedDeriv_const,
    if_neg (by norm_num : ¬ ((2 : ℕ) = 0))] at h
  exact h

/-- The Schwartz tail of `λ_k = 𝓕⁻ η_{≤k}` beyond the scale `2^{jj-1}`, in the exact shape needed
by `integralLamMulIteratedDeriv2BmpLe`. -/
theorem lam_tail_le (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ),
    ∫⁻ x in {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|}, ‖(lam k) x‖ₑ
      ≤ ENNReal.ofReal (C * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := offLamTail 0 N
  refine ⟨C, hCpos, fun k jj => ?_⟩
  have h := hC k ((2 : ℝ) ^ (jj - 1)) (le_of_lt (zpow_pos (by norm_num) _))
  have hfun : (fun x : ℝ => ‖iteratedDeriv 0
        ((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ₑ)
      = (fun x : ℝ => ‖(lam k) x‖ₑ) := by
    funext x
    rw [lam_eq_etaMult_K, iteratedDeriv_zero]
  have hz : (2 : ℝ) ^ k * (2 : ℝ) ^ (jj - 1) = (2 : ℝ) ^ (k + jj - 1) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [hfun, hz, pow_zero, mul_one] at h
  exact h

theorem integralLamMulIteratedDeriv2BmpLe (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj → ∫⁻ x : ℝ, ‖Work.KMTAreas.A4.lam k x * iteratedDeriv 2 (Work.KMTAreas.A4.bmp jj) x‖ₑ ≤ ENNReal.ofReal (C * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := offCutDeriv
  obtain ⟨Ct, hCtpos, hCt⟩ := lam_tail_le N
  refine ⟨Cd * Ct, mul_pos hCdpos hCtpos, ?_⟩
  intro k jj hk hjj hkjj
  have hBnn : (0 : ℝ) ≤ (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) :=
    Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ 1)) _
  have hcnn : (0 : ℝ) ≤ Cd * ((2 : ℝ) ^ (-jj)) ^ 2 := by positivity
  have hms : MeasurableSet {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  -- pointwise: `‖λ_k · η_{≤jj}''‖` is bounded by `Cd (2^{-jj})² ‖λ_k‖` on the tail
  have hpt : ∀ x : ℝ, ‖lam k x * iteratedDeriv 2 (bmp jj) x‖ₑ
      ≤ ENNReal.ofReal (Cd * ((2 : ℝ) ^ (-jj)) ^ 2)
          * {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|}.indicator (fun z => ‖lam k z‖ₑ) x := by
    intro x
    by_cases hx : x ∈ {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|}
    · have hd : ‖iteratedDeriv 2 ((bmp jj : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖
          ≤ Cd * ((2 : ℝ) ^ (-jj)) ^ 2 := by
        simpa only [bmp] using (hCd jj x).2
      rw [Set.indicator_of_mem hx, enorm_complex_eq_ofReal_norm (lam k x)]
      calc ‖lam k x * iteratedDeriv 2 (bmp jj) x‖ₑ
          = ENNReal.ofReal ‖lam k x * iteratedDeriv 2 (bmp jj) x‖ :=
              enorm_complex_eq_ofReal_norm _
        _ = ENNReal.ofReal (‖lam k x‖ * ‖iteratedDeriv 2 (bmp jj) x‖) := by rw [norm_mul]
        _ = ENNReal.ofReal ‖lam k x‖ * ENNReal.ofReal ‖iteratedDeriv 2 (bmp jj) x‖ := by
              rw [ENNReal.ofReal_mul (norm_nonneg _)]
        _ ≤ ENNReal.ofReal ‖lam k x‖ * ENNReal.ofReal (Cd * ((2 : ℝ) ^ (-jj)) ^ 2) := by
              gcongr
        _ = ENNReal.ofReal (Cd * ((2 : ℝ) ^ (-jj)) ^ 2)
              * ENNReal.ofReal ‖lam k x‖ := mul_comm _ _
    · have hlt : |x| < (2 : ℝ) ^ (jj - 1) := lt_of_not_ge hx
      simp [Set.indicator_of_notMem hx, iteratedDeriv2_bmp_eq_zero_of_abs_lt jj hlt]
  -- the numerical comparison `(2^{-jj})² ≤ 2^k`
  have hnum : ((2 : ℝ) ^ (-jj)) ^ 2 ≤ (2 : ℝ) ^ k := by
    have h1 : ((2 : ℝ) ^ (-jj)) ^ 2 = (2 : ℝ) ^ (-2 * jj) := by
      rw [pow_two, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      ring
    rw [h1]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hfin : Cd * ((2 : ℝ) ^ (-jj)) ^ 2
        * (Ct * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
      ≤ Cd * Ct * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
    calc Cd * ((2 : ℝ) ^ (-jj)) ^ 2 * (Ct * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
        = Cd * Ct * ((2 : ℝ) ^ (-jj)) ^ 2
            * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by ring
      _ ≤ Cd * Ct * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hBnn
          exact mul_le_mul_of_nonneg_left hnum (by positivity)
  calc ∫⁻ x : ℝ, ‖lam k x * iteratedDeriv 2 (bmp jj) x‖ₑ
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal (Cd * ((2 : ℝ) ^ (-jj)) ^ 2)
          * {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|}.indicator (fun z => ‖lam k z‖ₑ) x :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (Cd * ((2 : ℝ) ^ (-jj)) ^ 2)
          * ∫⁻ x : ℝ, {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|}.indicator
              (fun z => ‖lam k z‖ₑ) x :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Cd * ((2 : ℝ) ^ (-jj)) ^ 2)
          * ∫⁻ x in {x : ℝ | (2 : ℝ) ^ (jj - 1) ≤ |x|}, ‖lam k x‖ₑ := by
        rw [lintegral_indicator hms]
    _ ≤ ENNReal.ofReal (Cd * ((2 : ℝ) ^ (-jj)) ^ 2)
          * ENNReal.ofReal (Ct * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
        gcongr
        exact (hCt k jj)
    _ = ENNReal.ofReal (Cd * ((2 : ℝ) ^ (-jj)) ^ 2
          * (Ct * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))) :=
        (ENNReal.ofReal_mul hcnn).symm
    _ ≤ ENNReal.ofReal (Cd * Ct * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) :=
        ENNReal.ofReal_le_ofReal hfin

end

end Work.KMTAreas.A4
