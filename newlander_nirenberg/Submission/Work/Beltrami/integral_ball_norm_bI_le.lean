import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.CR.Flat.Cauchy.integral_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

namespace Work.Beltrami

open MeasureTheory Set

/-- Elementary real inequality behind the near-field bound: for `r ≥ 0` and `α > 0`,
`r^α · (r²)⁻¹ ≤ r^{α-2}` (equality when `r > 0`; both sides vanish at `r = 0` unless `α = 2`,
where the inequality still holds). -/
private lemma rpow_mul_inv_sq_le {α : ℝ} (hα : 0 < α) (r : ℝ) (hr : 0 ≤ r) :
    r ^ α * (r ^ 2)⁻¹ ≤ r ^ (α - 2) := by
  rcases eq_or_lt_of_le hr with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hα), zero_mul]
    exact Real.rpow_nonneg le_rfl _
  · have hconv : (r ^ 2 : ℝ) = r ^ (2 : ℝ) := (Real.rpow_natCast r 2).symm
    rw [hconv, ← div_eq_mul_inv, ← Real.rpow_sub h α 2]

/-- Near-field bound for the Beurling integrand of `Work.Beltrami.beurling`: for `f` bounded by
`M` and `α`-Hölder with constant `K` (`α > 0`), the absolute value of the integrand
`ζ ↦ (f ζ - χ(ζ-z) f z) (ζ-z)⁻²` (with `χ = bumpC`) is bounded in the mean over the disc
`B(z,ρ)` by `2πKρ^α/α + 4πMρ²`.  (The pointwise bound is
`‖·‖ ≤ K‖ζ-z‖^{α-2} + 4M` for every `ζ` — near `z` because `χ = 1`, and for `‖ζ-z‖ ≥ 1/2`
because `‖ζ-z‖^{-2} ≤ 4`; the disc formula is
`Work.CR.Flat.Cauchy.integral_norm_rpow_ball`, transported to a disc centred at `z` by
translation invariance.) -/
theorem integral_ball_norm_bI_le {α K M : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hM : 0 ≤ M)
    {f : ℂ → ℂ} (hMb : ∀ z, ‖f z‖ ≤ M) (hKb : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α)
    (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ ζ in Metric.ball z ρ,
        ‖(f ζ - (Work.Beltrami.bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹‖
      ≤ 2 * Real.pi * K * ρ ^ α / α + 4 * Real.pi * M * ρ ^ 2 := by
  classical
  -- Pointwise bound by `K‖ζ-z‖^{α-2} + 4M`.
  have hpt : ∀ ζ : ℂ, ‖(f ζ - (Work.Beltrami.bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹‖
      ≤ K * ‖ζ - z‖ ^ (α - 2) + 4 * M := by
    intro ζ
    have hdecomp : f ζ - (Work.Beltrami.bumpC (ζ - z) : ℂ) * f z
        = (f ζ - f z) + (((1 : ℝ) - Work.Beltrami.bumpC (ζ - z) : ℝ) : ℂ) * f z := by
      push_cast; ring
    have hfac : ‖f ζ - (Work.Beltrami.bumpC (ζ - z) : ℂ) * f z‖
        ≤ K * ‖ζ - z‖ ^ α + (1 - Work.Beltrami.bumpC (ζ - z)) * M := by
      rw [hdecomp]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖f ζ - f z‖ ≤ K * ‖ζ - z‖ ^ α := hKb ζ z
      have h2 : ‖(((1 : ℝ) - Work.Beltrami.bumpC (ζ - z) : ℝ) : ℂ) * f z‖
          ≤ (1 - Work.Beltrami.bumpC (ζ - z)) * M := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [Work.Beltrami.bumpC_le_one (ζ - z)])]
        exact mul_le_mul_of_nonneg_left (hMb z)
          (by linarith [Work.Beltrami.bumpC_le_one (ζ - z)])
      linarith
    rw [norm_mul]
    have hnorm_inv : ‖((ζ - z) ^ 2)⁻¹‖ = (‖ζ - z‖ ^ 2)⁻¹ := by rw [norm_inv, norm_pow]
    rw [hnorm_inv]
    refine (mul_le_mul_of_nonneg_right hfac (by positivity)).trans ?_
    by_cases hle : ‖ζ - z‖ ≤ 1 / 2
    · -- Near `z`: the cutoff equals `1`, so the Hölder bound applies directly.
      have hchi : Work.Beltrami.bumpC (ζ - z) = 1 := Work.Beltrami.bumpC_eq_one hle
      rw [hchi, sub_self, zero_mul, add_zero]
      have h1 := rpow_mul_inv_sq_le hα ‖ζ - z‖ (norm_nonneg _)
      have h2 : K * (‖ζ - z‖ ^ α * (‖ζ - z‖ ^ 2)⁻¹) ≤ K * ‖ζ - z‖ ^ (α - 2) :=
        mul_le_mul_of_nonneg_left h1 hK
      have h3 : K * (‖ζ - z‖ ^ α * (‖ζ - z‖ ^ 2)⁻¹)
          = K * ‖ζ - z‖ ^ α * (‖ζ - z‖ ^ 2)⁻¹ := by ring
      rw [h3] at h2
      linarith [hM]
    · -- Away from `z`: `‖ζ-z‖^{-2} ≤ 4` and the cutoff term is bounded by `M`.
      have hle' : 1 / 2 < ‖ζ - z‖ := lt_of_not_ge hle
      have hrpos : 0 < ‖ζ - z‖ := by linarith
      have hchi1 : Work.Beltrami.bumpC (ζ - z) ≤ 1 := Work.Beltrami.bumpC_le_one _
      have hchi0 : 0 ≤ Work.Beltrami.bumpC (ζ - z) := Work.Beltrami.bumpC_nonneg _
      have hii : 0 ≤ (‖ζ - z‖ ^ 2)⁻¹ := by positivity
      have hcoef : (K * ‖ζ - z‖ ^ α + (1 - Work.Beltrami.bumpC (ζ - z)) * M)
          ≤ K * ‖ζ - z‖ ^ α + M := by nlinarith
      refine (mul_le_mul_of_nonneg_right hcoef hii).trans ?_
      have hr2pos : 0 < ‖ζ - z‖ ^ 2 := pow_pos hrpos 2
      have h4 : (‖ζ - z‖ ^ 2)⁻¹ ≤ 4 := by
        rw [inv_le_iff_one_le_mul₀ hr2pos]
        nlinarith
      have h1 := rpow_mul_inv_sq_le hα ‖ζ - z‖ (norm_nonneg _)
      have hk : K * ‖ζ - z‖ ^ α * (‖ζ - z‖ ^ 2)⁻¹ ≤ K * ‖ζ - z‖ ^ (α - 2) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hK
      have hm : M * (‖ζ - z‖ ^ 2)⁻¹ ≤ M * 4 := mul_le_mul_of_nonneg_left h4 hM
      rw [add_mul]
      linarith
  -- Integrability of the dominating function on the disc, by translating the known
  -- integrability of `w ↦ ‖w‖^{α-2}` on the disc `B(0,ρ)`.
  have hint_pow : IntegrableOn (fun ζ : ℂ => ‖ζ - z‖ ^ (α - 2)) (Metric.ball z ρ) volume := by
    have he : MeasurableEmbedding (fun x : ℂ => x + (-z)) :=
      (Homeomorph.addRight (-z)).measurableEmbedding
    have hL : IntegrableOn (fun w : ℂ => ‖w‖ ^ (α - 2)) (Metric.ball 0 ρ)
        (Measure.map (fun x : ℂ => x + (-z)) volume) := by
      rw [map_add_right_eq_self]
      exact Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (by linarith)
    have hR := (MeasurableEmbedding.integrableOn_map_iff he).mp hL
    convert hR using 1
    · ext ζ; simp [Function.comp, sub_eq_add_neg]
    · ext ζ; simp [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg]
  have hint1 : IntegrableOn (fun ζ : ℂ => K * ‖ζ - z‖ ^ (α - 2)) (Metric.ball z ρ) volume :=
    hint_pow.const_mul K
  have hint2 : IntegrableOn (fun ζ : ℂ => (4 * M : ℝ)) (Metric.ball z ρ) volume :=
    integrableOn_const (s := Metric.ball z ρ) (C := (4 * M : ℝ))
      (by exact (measure_ball_lt_top).ne)
  -- Value of the dominating integral.
  have hcalc : ∫ ζ in Metric.ball z ρ, (K * ‖ζ - z‖ ^ (α - 2) + 4 * M)
      = 2 * Real.pi * K * ρ ^ α / α + 4 * Real.pi * M * ρ ^ 2 := by
    have htrans : ∫ ζ in Metric.ball z ρ, ‖ζ - z‖ ^ (α - 2)
        = ∫ w in Metric.ball (0:ℂ) ρ, ‖w‖ ^ (α - 2) := by
      have h1 : (fun ζ => (Metric.ball z ρ).indicator (fun ζ => ‖ζ - z‖ ^ (α - 2)) ζ)
          = (fun ζ => (Metric.ball (0:ℂ) ρ).indicator (fun w => ‖w‖ ^ (α - 2)) (ζ - z)) := by
        funext ζ
        rw [Set.indicator_apply, Set.indicator_apply]
        congr 1
        simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
      rw [← integral_indicator measurableSet_ball (f := fun ζ => ‖ζ - z‖ ^ (α - 2))]
      rw [h1]
      rw [show (fun ζ => (Metric.ball (0:ℂ) ρ).indicator (fun w => ‖w‖ ^ (α - 2)) (ζ - z))
          = (fun ζ => (Metric.ball (0:ℂ) ρ).indicator (fun w => ‖w‖ ^ (α - 2)) (ζ + (-z))) from by
        funext ζ; simp only [sub_eq_add_neg]]
      rw [integral_add_right_eq_self
        (fun w => (Metric.ball (0:ℂ) ρ).indicator (fun w => ‖w‖ ^ (α - 2)) w) (-z)]
      rw [integral_indicator measurableSet_ball (f := fun w => ‖w‖ ^ (α - 2))]
    have hnorm_int : ∫ w in Metric.ball (0:ℂ) ρ, ‖w‖ ^ (α - 2) = 2 * Real.pi * ρ ^ α / α := by
      rw [Work.CR.Flat.Cauchy.integral_norm_rpow_ball hρ (by linarith)]
      rw [show α - 2 + 2 = α from by ring]
    have hvol : (volume : Measure ℂ).real (Metric.ball z ρ) = Real.pi * ρ ^ 2 := by
      rw [MeasureTheory.Measure.real, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hρ.le, ENNReal.coe_toReal]
      rw [show (NNReal.pi : ℝ) = Real.pi from rfl]
      ring
    rw [integral_add hint1 hint2, integral_const_mul, htrans, hnorm_int, setIntegral_const, hvol]
    simp only [smul_eq_mul]
    ring
  rw [← hcalc]
  exact MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ζ => norm_nonneg _)
    (hint1.add hint2) (Filter.Eventually.of_forall hpt)

end Work.Beltrami
