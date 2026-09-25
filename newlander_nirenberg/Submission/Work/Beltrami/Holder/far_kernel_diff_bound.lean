import Mathlib
import Submission.Work.Beltrami.HolderAux
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.norm_inv_sq_sub_inv_sq_le
import Submission.Work.Beltrami.integral_norm_rpow_exterior

namespace Work.Beltrami.Holder

open MeasureTheory

/-- The indicator identity behind the translation invariance of the exterior radial-power
integral: the indicator of a disc exterior centred at `x` is the translate of the indicator
of the disc exterior centred at `0`. -/
theorem indicator_norm_sub_eq {s a : ℝ} (x : ℂ) (u : ℂ) :
    ({u : ℂ | a ≤ ‖u - x‖}.indicator (fun u : ℂ => ‖u - x‖ ^ s)) u
      = ({w : ℂ | a ≤ ‖w‖}.indicator (fun w : ℂ => ‖w‖ ^ s)) (u - x) := by
  by_cases h : a ≤ ‖u - x‖
  · rw [Set.indicator_of_mem (show u ∈ {u : ℂ | a ≤ ‖u - x‖} from h),
        Set.indicator_of_mem (show (u - x) ∈ {w : ℂ | a ≤ ‖w‖} from h)]
  · rw [Set.indicator_of_notMem (show u ∉ {u : ℂ | a ≤ ‖u - x‖} from h),
        Set.indicator_of_notMem (show (u - x) ∉ {w : ℂ | a ≤ ‖w‖} from h)]

/-- Translation form of the exterior radial-power integral: for `a > 0`, `s < -2` and any
centre `x`, `∫_{a ≤ ‖u-x‖} ‖u-x‖^s dA(u) = 2π a^{s+2}/(-(s+2))`. -/
theorem integral_norm_sub_rpow_exterior {s a : ℝ} (ha : 0 < a) (hs : s < -2) (x : ℂ) :
    ∫ u in {u : ℂ | a ≤ ‖u - x‖}, ‖u - x‖ ^ s
      = 2 * Real.pi * a ^ (s + 2) / (-(s + 2)) := by
  have hT : MeasurableSet {u : ℂ | a ≤ ‖u - x‖} :=
    measurableSet_le measurable_const
      (continuous_norm.measurable.comp (measurable_id.sub measurable_const))
  have hE : MeasurableSet {w : ℂ | a ≤ ‖w‖} :=
    measurableSet_le measurable_const measurable_norm
  rw [← integral_indicator hT]
  rw [show (fun u : ℂ => ({u : ℂ | a ≤ ‖u - x‖}.indicator (fun u : ℂ => ‖u - x‖ ^ s)) u)
      = fun u : ℂ => ({w : ℂ | a ≤ ‖w‖}.indicator (fun w : ℂ => ‖w‖ ^ s)) (u - x)
      from funext (indicator_norm_sub_eq (s := s) (a := a) x)]
  rw [integral_sub_right_eq_self _ x, integral_indicator hE]
  exact (exterior_rpow_integral ha hs).2

/-- Integrability of the translated exterior radial-power integrand. -/
theorem integrableOn_norm_sub_rpow_exterior {s a : ℝ} (ha : 0 < a) (hs : s < -2) (x : ℂ) :
    IntegrableOn (fun u : ℂ => ‖u - x‖ ^ s) {u : ℂ | a ≤ ‖u - x‖} volume := by
  have hT : MeasurableSet {u : ℂ | a ≤ ‖u - x‖} :=
    measurableSet_le measurable_const
      (continuous_norm.measurable.comp (measurable_id.sub measurable_const))
  have hE : MeasurableSet {w : ℂ | a ≤ ‖w‖} :=
    measurableSet_le measurable_const measurable_norm
  rw [← integrable_indicator_iff hT]
  refine (((integrable_indicator_iff hE).mpr
    (exterior_rpow_integral ha hs).1).comp_sub_right x).congr ?_
  filter_upwards with u
  exact (indicator_norm_sub_eq (s := s) (a := a) x u).symm

/-- Far-field Calderón–Zygmund bound for the difference of the Beurling kernels: for `f`
`α`-Hölder with constant `K` (`α < 1`) and `δ = ‖x-y‖ > 0`,
`‖∫_{(B(x,2δ) ∪ B(y,2δ))ᶜ} (f u - f x) · ((u-x)⁻² - (u-y)⁻²) dA(u)‖
   ≤ (12 π 2^{α-1} / (1-α)) · (K δ^α)`.

On the complement of the two balls one has `2δ ≤ ‖u-x‖`, so
`‖(u-x)⁻² - (u-y)⁻²‖ ≤ 6δ‖u-x‖⁻³` by `Work.Beltrami.norm_inv_sq_sub_inv_sq_le` (applied with
`u = u-x`, `v = u-y`), and `‖f u - f x‖ ≤ K‖u-x‖^α`; hence the integrand is dominated by
`6Kδ‖u-x‖^{α-3}`, whose integral over the complement of the disc of radius `2δ` is
`6Kδ · 2π(2δ)^{α-1}/(1-α) = 12π2^{α-1}Kδ^α/(1-α)` by `Work.Beltrami.exterior_rpow_integral`
with `s = α-3 < -2` (after the substitution `w = u-x`, using that the complement of the two
balls is contained in the complement of `B(x,2δ)`, and translation invariance of Lebesgue
measure). -/
theorem far_kernel_diff_bound {α K δ : ℝ} (hα1 : α < 1) (hδ : 0 < δ) {f : ℂ → ℂ}
    (hK : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) {x y : ℂ} (hxy : ‖x - y‖ = δ) :
    ‖∫ u in (Metric.ball x (2 * δ) ∪ Metric.ball y (2 * δ))ᶜ,
        (f u - f x) * (((u - x) ^ 2)⁻¹ - ((u - y) ^ 2)⁻¹) ∂MeasureTheory.volume‖
      ≤ (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * (K * δ ^ α) := by
  -- The Hölder hypothesis forces `K ≥ 0`.
  have hK0 : 0 ≤ K := by
    have h := hK (0 : ℂ) 1
    have h' : ‖f (0 : ℂ) - f 1‖ ≤ K := by simpa using h
    linarith [norm_nonneg (f (0 : ℂ) - f 1)]
  have hα3 : α - 3 < -2 := by linarith
  have h2δ : 0 < 2 * δ := by linarith
  set S : Set ℂ := (Metric.ball x (2 * δ) ∪ Metric.ball y (2 * δ))ᶜ with hS
  have hS_eq : ∀ u : ℂ, u ∈ S ↔ 2 * δ ≤ ‖u - x‖ ∧ 2 * δ ≤ ‖u - y‖ := by
    intro u
    simp only [hS, Set.mem_compl_iff, Set.mem_union, not_or, Metric.mem_ball, not_lt,
      dist_eq_norm]
  have hTn : MeasurableSet {u : ℂ | 2 * δ ≤ ‖u - x‖} :=
    measurableSet_le measurable_const
      (continuous_norm.measurable.comp (measurable_id.sub measurable_const))
  have hSmeas : MeasurableSet S := by
    rw [show S = {u : ℂ | 2 * δ ≤ ‖u - x‖ ∧ 2 * δ ≤ ‖u - y‖} from Set.ext hS_eq]
    exact hTn.inter (measurableSet_le measurable_const
      (continuous_norm.measurable.comp (measurable_id.sub measurable_const)))
  -- Pointwise Calderón–Zygmund domination on `S`.
  have hbd : ∀ u ∈ S, ‖(f u - f x) * (((u - x) ^ 2)⁻¹ - ((u - y) ^ 2)⁻¹)‖
      ≤ (6 * K * δ) * ‖u - x‖ ^ (α - 3) := by
    intro u hu
    have hux : 2 * δ ≤ ‖u - x‖ := ((hS_eq u).mp hu).1
    have huxpos : 0 < ‖u - x‖ := lt_of_lt_of_le h2δ hux
    have hker : ‖((u - x) ^ 2)⁻¹ - ((u - y) ^ 2)⁻¹‖ ≤ 6 * δ * ‖u - x‖ ^ (-3 : ℝ) := by
      have hd : ‖(u - x) - (u - y)‖ = δ := by
        rw [show (u - x) - (u - y) = y - x by ring, norm_sub_rev, hxy]
      have h2 : 2 * ‖(u - x) - (u - y)‖ ≤ ‖u - x‖ := by rw [hd]; linarith
      have h := norm_inv_sq_sub_inv_sq_le h2
      rw [hd] at h
      refine le_trans h (le_of_eq ?_)
      rw [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_neg huxpos.le ((3 : ℕ) : ℝ)]
      norm_num
    have hfu : ‖f u - f x‖ ≤ K * ‖u - x‖ ^ α := hK u x
    rw [norm_mul]
    have hstep : ‖f u - f x‖ * ‖((u - x) ^ 2)⁻¹ - ((u - y) ^ 2)⁻¹‖
        ≤ (K * ‖u - x‖ ^ α) * (6 * δ * ‖u - x‖ ^ (-3 : ℝ)) :=
      mul_le_mul hfu hker (norm_nonneg _)
        (mul_nonneg hK0 (Real.rpow_nonneg (norm_nonneg _) _))
    have hrpow : ‖u - x‖ ^ α * ‖u - x‖ ^ (-3 : ℝ) = ‖u - x‖ ^ (α - 3) := by
      rw [← Real.rpow_add huxpos, show α + (-3 : ℝ) = α - 3 by ring]
    have heq : (K * ‖u - x‖ ^ α) * (6 * δ * ‖u - x‖ ^ (-3 : ℝ))
        = (6 * K * δ) * ‖u - x‖ ^ (α - 3) := by
      rw [show (K * ‖u - x‖ ^ α) * (6 * δ * ‖u - x‖ ^ (-3 : ℝ))
          = (6 * K * δ) * (‖u - x‖ ^ α * ‖u - x‖ ^ (-3 : ℝ)) by ring, hrpow]
    exact le_trans hstep heq.le
  -- Integrability of the majorant, on `S` and on the larger exterior disc.
  have hbT : IntegrableOn (fun u : ℂ => (6 * K * δ) * ‖u - x‖ ^ (α - 3))
      {u : ℂ | 2 * δ ≤ ‖u - x‖} volume :=
    (integrableOn_norm_sub_rpow_exterior h2δ hα3 x).const_mul _
  have hbS : IntegrableOn (fun u : ℂ => (6 * K * δ) * ‖u - x‖ ^ (α - 3)) S volume :=
    hbT.mono_set (fun u hu => ((hS_eq u).mp hu).1)
  have hstep1 : ‖∫ u in S, (f u - f x) * (((u - x) ^ 2)⁻¹ - ((u - y) ^ 2)⁻¹)‖
      ≤ ∫ u in S, (6 * K * δ) * ‖u - x‖ ^ (α - 3) := by
    refine norm_integral_le_of_norm_le hbS ?_
    rw [ae_restrict_iff' hSmeas]
    exact Filter.Eventually.of_forall hbd
  have hstep2 : ∫ u in S, (6 * K * δ) * ‖u - x‖ ^ (α - 3)
      ≤ ∫ u in {u : ℂ | 2 * δ ≤ ‖u - x‖}, (6 * K * δ) * ‖u - x‖ ^ (α - 3) := by
    refine setIntegral_mono_set hbT ?_ ?_
    · filter_upwards [ae_restrict_mem hTn] with u _
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) hδ.le)
        (Real.rpow_nonneg (norm_nonneg _) _)
    · exact Filter.Eventually.of_forall (fun u hu => ((hS_eq u).mp hu).1)
  have hval : ∫ u in {u : ℂ | 2 * δ ≤ ‖u - x‖}, (6 * K * δ) * ‖u - x‖ ^ (α - 3)
      = 6 * K * δ * (2 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α)) := by
    rw [integral_const_mul, integral_norm_sub_rpow_exterior h2δ hα3 x,
      show (α - 3) + 2 = α - 1 by ring, show -((α - 1)) = (1 : ℝ) - α by ring]
  have hfinal : 6 * K * δ * (2 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α))
      = (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * (K * δ ^ α) := by
    have hδmul : δ * δ ^ (α - 1) = δ ^ α := by
      rw [show δ * δ ^ (α - 1) = δ ^ (1 : ℝ) * δ ^ (α - 1) from by rw [Real.rpow_one]]
      rw [← Real.rpow_add hδ, show (1 : ℝ) + (α - 1) = α by ring]
    rw [Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num) hδ.le]
    rw [show 6 * K * δ * (2 * Real.pi * (2 ^ (α - 1) * δ ^ (α - 1)) / (1 - α))
        = (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * (K * (δ * δ ^ (α - 1))) by ring]
    rw [hδmul]
  calc ‖∫ u in S, (f u - f x) * (((u - x) ^ 2)⁻¹ - ((u - y) ^ 2)⁻¹)‖
      ≤ ∫ u in S, (6 * K * δ) * ‖u - x‖ ^ (α - 3) := hstep1
    _ ≤ ∫ u in {u : ℂ | 2 * δ ≤ ‖u - x‖}, (6 * K * δ) * ‖u - x‖ ^ (α - 3) := hstep2
    _ = 6 * K * δ * (2 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α)) := hval
    _ = (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * (K * δ ^ α) := hfinal

end Work.Beltrami.Holder
