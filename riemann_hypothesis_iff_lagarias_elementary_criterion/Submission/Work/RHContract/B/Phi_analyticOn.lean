import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# Analyticity of the Landau integral `Φ`

`Work.RHContract.Landau.Phi s = ∫_2^∞ (ψ t − t) k(t) t^{−s} dt` is the Mellin transform
(with exponent `1 - s`) of the compactly-supported function
`t ↦ 1_{(2,∞)}(t) · (ψ t − t) k(t)`.

Mathlib's `mellin_differentiableAt_of_isBigO_rpow` shows that the Mellin transform of a
locally integrable function which is `O(t^{-a})` at infinity and `O(t^{-b})` near `0` is
complex differentiable on the strip `b < re s < a`.  Since `ψ t − t = O(t)` (Chebyshev) and
`k(t) = O(t^{-2})`, the integrand is `O(t^{-1})` at infinity, while the factor `1_{(2,∞)}`
makes it vanish near `0`.  This gives differentiability of `Φ` on the half plane `re s > 0`,
hence analyticity there, since a complex function which is differentiable on a neighbourhood
of a point is analytic at that point (`Complex.analyticAt_iff_eventually_differentiableAt`).
-/

namespace Work.RHContract.B

open MeasureTheory Set Filter Asymptotics
open scoped Topology

noncomputable section

/-- The integrand `(ψ t − t) · k(t)` of `Φ`, as a complex-valued function of `t`. -/
def phiIntegrand (t : ℝ) : ℂ := ((Chebyshev.psi t - t) * Work.RHContract.kW t : ℂ)

/-- The same integrand, cut down to the range `t > 2` of the integral defining `Φ`. -/
def phiIntegrandCut (t : ℝ) : ℂ := (Set.Ioi 2).indicator phiIntegrand t

/-- The norm of a real number viewed as a complex number is its absolute value. -/
lemma norm_ofReal (x : ℝ) : ‖(x : ℂ)‖ = |x| := by simp

/-! ## Pointwise bounds -/

/-- Chebyshev's bound `ψ t ≤ (log 4 + 4) t` gives `|ψ t − t| ≤ (log 4 + 4) t` for `t ≥ 0`. -/
lemma abs_psi_sub_id_le {t : ℝ} (ht : 0 ≤ t) :
    |Chebyshev.psi t - t| ≤ (Real.log 4 + 4) * t := by
  have hpsi : Chebyshev.psi t ≤ (Real.log 4 + 4) * t := Chebyshev.psi_le_const_mul_self ht
  have hpsi0 : 0 ≤ Chebyshev.psi t := Chebyshev.psi_nonneg t
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith

/-- For `t ≥ 2`, `|k(t)| ≤ 4 / t²`. -/
lemma abs_kW_le {t : ℝ} (ht : 2 ≤ t) : |Work.RHContract.kW t| ≤ 4 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hLge : (69 : ℝ) / 100 ≤ Real.log t := by
    have h2 : (69 : ℝ) / 100 < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    exact le_trans h2.le (Real.log_le_log (by norm_num) ht)
  have hkey : Real.log t + 1 ≤ 4 * (Real.log t) ^ 2 := by
    nlinarith [sq_nonneg (Real.log t - (69 : ℝ) / 100)]
  have hden : 0 < t ^ 2 * (Real.log t) ^ 2 := by positivity
  have hpos : 0 < (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by positivity
  rw [Work.RHContract.kW, abs_of_pos hpos, div_le_div_iff₀ hden (by positivity)]
  nlinarith [hkey, sq_nonneg t, ht0]

/-- The integrand of `Φ` is `O(t^{-1})` for `t ≥ 2`. -/
lemma norm_phiIntegrand_le {t : ℝ} (ht : 2 ≤ t) :
    ‖phiIntegrand t‖ ≤ 4 * (Real.log 4 + 4) / t := by
  have ht0 : 0 < t := by linarith
  have h1 : |Chebyshev.psi t - t| ≤ (Real.log 4 + 4) * t := abs_psi_sub_id_le ht0.le
  have h2 : |Work.RHContract.kW t| ≤ 4 / t ^ 2 := abs_kW_le ht
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc : phiIntegrand t = (((Chebyshev.psi t - t) * Work.RHContract.kW t : ℝ) : ℂ) := by
    rw [phiIntegrand]
    push_cast
    ring
  rw [hc, norm_ofReal, abs_mul]
  calc |Chebyshev.psi t - t| * |Work.RHContract.kW t|
      ≤ ((Real.log 4 + 4) * t) * (4 / t ^ 2) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 4 * (Real.log 4 + 4) / t := by field_simp

/-! ## Measurability and local integrability -/

lemma measurable_phiIntegrand : Measurable phiIntegrand := by
  have hψ : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
  unfold phiIntegrand Work.RHContract.kW
  fun_prop

lemma locallyIntegrableOn_phiIntegrandCut :
    LocallyIntegrableOn phiIntegrandCut (Set.Ioi 0) := by
  have hcont : Continuous (fun t : ℝ => 4 * (Real.log 4 + 4) / max t 1) := by
    refine Continuous.div continuous_const (continuous_id.max continuous_const) (fun t => ?_)
    have h1 : (1 : ℝ) ≤ max t 1 := le_max_right _ _
    linarith
  have hdom : LocallyIntegrableOn (fun t : ℝ => 4 * (Real.log 4 + 4) / max t 1)
      (Set.Ioi 0) := hcont.locallyIntegrable.locallyIntegrableOn _
  refine hdom.mono ?_ ?_
  · exact (measurable_phiIntegrand.indicator measurableSet_Ioi).aestronglyMeasurable
  · filter_upwards with t
    by_cases ht : t ∈ Set.Ioi 2
    · have ht2 : 2 ≤ t := le_of_lt ht
      have ht0 : 0 < t := by linarith
      have hcut : phiIntegrandCut t = phiIntegrand t := by
        rw [phiIntegrandCut, Set.indicator_of_mem ht]
      rw [hcut, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 4 * (Real.log 4 + 4) / max t 1),
        max_eq_left (by linarith : (1 : ℝ) ≤ t)]
      exact norm_phiIntegrand_le ht2
    · have hcut : phiIntegrandCut t = 0 := by
        rw [phiIntegrandCut, Set.indicator_of_notMem ht]
      rw [hcut, norm_zero]
      positivity

/-! ## Growth at infinity and near `0` -/

lemma phiIntegrandCut_isBigO_atTop :
    phiIntegrandCut =O[atTop] (fun t : ℝ => t ^ (-(1 : ℝ))) := by
  refine IsBigO.of_bound (4 * (Real.log 4 + 4)) ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  have hb := norm_phiIntegrand_le ht.le
  have h1 : phiIntegrandCut t = phiIntegrand t := by
    unfold phiIntegrandCut
    exact Set.indicator_of_mem ht phiIntegrand
  rw [h1, Real.norm_eq_abs, Real.rpow_neg_one, abs_of_pos (inv_pos.mpr ht0)]
  simpa [div_eq_mul_inv] using hb

/-- Since `phiIntegrandCut` vanishes on a neighbourhood of `0`, the `O`-estimate at `0`
holds with an arbitrary exponent. -/
lemma phiIntegrandCut_isBigO_nhdsGT (b : ℝ) :
    phiIntegrandCut =O[nhdsWithin 0 (Set.Ioi 0)] (fun t : ℝ => t ^ (-b)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [show Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0)
      from Ioo_mem_nhdsGT zero_lt_one] with t ht
  have hnot : t ∉ Set.Ioi 2 := by
    simp only [Set.mem_Ioi]
    linarith [ht.2]
  rw [phiIntegrandCut, Set.indicator_of_notMem hnot, norm_zero]
  positivity

/-! ## `Φ` is the Mellin transform of the cut integrand -/

lemma Phi_eq_mellin :
    Work.RHContract.Landau.Phi = fun z : ℂ => mellin phiIntegrandCut (1 - z) := by
  funext z
  have hexp : (1 - z) - 1 = -z := by ring
  have hpoint : ∀ t : ℝ, (t : ℂ) ^ ((1 - z) - 1) • phiIntegrandCut t =
      (Set.Ioi 2).indicator (fun t => phiIntegrand t * (t : ℂ) ^ (-z)) t := by
    intro t
    rw [hexp, phiIntegrandCut]
    by_cases ht : t ∈ Set.Ioi 2
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, mul_comm]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  rw [Work.RHContract.Landau.Phi, mellin]
  simp only [hpoint]
  rw [setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2))]
  rfl

/-- `Φ` is differentiable at `z` as soon as `0 < re z` and the Mellin strip bound
`b < re (1 - z)` holds for some `b`. -/
lemma differentiableAt_Phi (z : ℂ) (b : ℝ) (hz : 0 < z.re) (hb : b < 1 - z.re) :
    DifferentiableAt ℂ Work.RHContract.Landau.Phi z := by
  rw [Phi_eq_mellin]
  have hm : DifferentiableAt ℂ (mellin phiIntegrandCut) (1 - z) :=
    mellin_differentiableAt_of_isBigO_rpow (a := 1) (b := b) locallyIntegrableOn_phiIntegrandCut
      phiIntegrandCut_isBigO_atTop
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (phiIntegrandCut_isBigO_nhdsGT b)
      (by simp only [Complex.sub_re, Complex.one_re]; exact hb)
  have hi : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := differentiableAt_id.const_sub 1
  exact hm.comp z hi

theorem Phi_analyticOn (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ Work.RHContract.Landau.Phi s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < s.re + 2} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  filter_upwards [hopen.mem_nhds ⟨hs, by linarith⟩] with z hz
  exact differentiableAt_Phi z (-(s.re + 1)) hz.1 (by linarith [hz.2])

end

end Work.RHContract.B
