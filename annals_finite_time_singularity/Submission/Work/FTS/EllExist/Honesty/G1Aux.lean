/-
# `Work.FTS.EllExist.Honesty.G1Aux` — scaffolding for the `z^{s⁻}` Green term `G1`

`G1 α m c` is the singular (`z → 0`) term of the explicit radial Green function `radGreen`:

  `G1 α m c z = z^{s⁻} · ∫_0^z c t t^{a-1} dt`,   `s⁻ = -(2m+5)/α = -a`,  `a = (2m+5)/α > 0`.

This file names the integral `G1A`, the integrand `G1f`, and the constants that occur in the
weighted `L²` estimate `G1_est`:

* `M0 = ∫_{(0,1)} c z²/z⁴` — finite and nonnegative under the standing hypothesis
  `IntegrableOn (fun z => c z²/z⁴) (Ioo 0 1)` (`h0`), and monotone in the interval:
  `∫_x^y c z²/z⁴ ≤ M0` for `0 < x < y < 1`;
* `C0 = M0/2 + 1/(2(2a+3))`, `CΦ = C0²` — the endpoint bound `G1 x²/x³ ≤ CΦ` for all `x > 0`;
* `η = 2/(3+2a)`, `M = 2(η M0 + CΦ)/(3+2a)` — the uniform bound
  `∫_x^y G1 z²/z⁴ ≤ M` for `0 < x < y < 1`.

The elementary pieces proved here are the pointwise Young/AM–GM inequality, the continuity of the
integrand, its integrability on `(0,1)` (from `h0`), the fundamental theorem of calculus for
`G1A`, and the monotonicity of `∫ c z²/z⁴`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllExist.Honesty.RadGreenDefs
import Submission.Work.FTS.PhiStar.Radial.intervalIntegrable_of_Ioi_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.EllExist.Honesty

set_option autoImplicit false

/-- The exponent `s⁻ = -(2m+5)/α` of the singular Green term `G1`. -/
def G1s (α : ℝ) (m : ℕ) : ℝ := -(2 * (m : ℝ) + 5) / α

/-- The positive exponent `a = (2m+5)/α = -s⁻`. -/
def G1a (α : ℝ) (m : ℕ) : ℝ := (2 * (m : ℝ) + 5) / α

/-- The integrand `t ↦ c t · t^{a-1}` of the inner integral of `G1`. -/
def G1f (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ :=
  fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)

/-- The inner integral `z ↦ ∫₀^z c t t^{a-1} dt` of `G1`. -/
def G1A (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, G1f α m c t

/-- `M0 = ∫_{(0,1)} c z²/z⁴`. -/
def G1M0 (c : ℝ → ℝ) : ℝ := ∫ z in Set.Ioo 0 1, c z ^ 2 / z ^ 4

/-- The endpoint constant `C0 = M0/2 + 1/(2(2a+3))`. -/
def G1C0 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ := G1M0 c / 2 + 1 / (2 * (2 * G1a α m + 3))

/-- The endpoint bound `CΦ = C0²` for `G1 z²/z³`. -/
def G1CPhi (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ := G1C0 α m c ^ 2

/-- The AM–GM parameter `η = 2/(3+2a)`. -/
def G1eta (α : ℝ) (m : ℕ) : ℝ := 2 / (3 + 2 * G1a α m)

/-- The uniform bound `M = 2(η M0 + CΦ)/(3+2a)`. -/
def G1M (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ :=
  2 * (G1eta α m * G1M0 c + G1CPhi α m c) / (3 + 2 * G1a α m)

/-- `G1` is `z^{s⁻}` times the inner integral `G1A` (definitional). -/
theorem G1_eq_zpow_mul_G1A (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    G1 α m c z = z ^ (G1s α m) * G1A α m c z := rfl

/-- `s⁻ = -a`. -/
theorem G1s_eq_neg_G1a (α : ℝ) (m : ℕ) : G1s α m = -G1a α m := by
  simp only [G1s, G1a, neg_div]

/-- `a > 0` when `α > 0`. -/
theorem G1a_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < G1a α m := by
  rw [G1a]; positivity

/-- Young's inequality `2|XY| ≤ X² + Y²`. -/
theorem G1_two_mul_abs_mul_le (X Y : ℝ) : 2 * |X * Y| ≤ X ^ 2 + Y ^ 2 := by
  have h := sq_nonneg (|X| - |Y|)
  rw [sub_sq, sq_abs, sq_abs] at h
  rw [abs_mul]
  nlinarith [h]

/-- The weighted Young inequality `2|XY| ≤ λX² + Y²/λ` for `λ > 0`. -/
theorem G1_two_mul_abs_mul_le_mul {l X Y : ℝ} (hl : 0 < l) :
    2 * |X * Y| ≤ l * X ^ 2 + Y ^ 2 / l := by
  have h := G1_two_mul_abs_mul_le (l * X) Y
  rw [abs_mul, abs_mul, abs_of_pos hl, mul_pow] at h
  have h' : l * (2 * |X * Y|) ≤ l * (l * X ^ 2 + Y ^ 2 / l) := by
    have e : l * (l * X ^ 2 + Y ^ 2 / l) = l ^ 2 * X ^ 2 + Y ^ 2 := by
      field_simp
    rw [e, abs_mul]
    nlinarith [h]
  exact le_of_mul_le_mul_left h' hl

/-- `M0` is nonnegative (the integrand `c z²/z⁴` is pointwise nonnegative). -/
theorem G1M0_nonneg (c : ℝ → ℝ) : 0 ≤ G1M0 c := by
  rw [G1M0]
  exact setIntegral_nonneg measurableSet_Ioo
    (fun z _ => div_nonneg (sq_nonneg _) (by positivity))

/-- `C0 ≥ 0`. -/
theorem G1C0_nonneg {α : ℝ} (hα : 0 < α) (m : ℕ) (c : ℝ → ℝ) : 0 ≤ G1C0 α m c := by
  rw [G1C0]
  have h1 := G1M0_nonneg c
  have h2 : (0 : ℝ) < 2 * (2 * G1a α m + 3) := by
    have := G1a_pos hα m; linarith
  have h3 : (0 : ℝ) ≤ 1 / (2 * (2 * G1a α m + 3)) := by positivity
  linarith

/-- `CΦ ≥ 0`. -/
theorem G1CPhi_nonneg (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : 0 ≤ G1CPhi α m c := by
  rw [G1CPhi]; exact sq_nonneg _

/-- `η > 0`. -/
theorem G1eta_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < G1eta α m := by
  rw [G1eta]
  have := G1a_pos hα m
  positivity

/-- `M ≥ 0`. -/
theorem G1M_nonneg {α : ℝ} (hα : 0 < α) (m : ℕ) (c : ℝ → ℝ) : 0 ≤ G1M α m c := by
  rw [G1M]
  have h1 := G1M0_nonneg c
  have h2 := G1eta_pos hα m
  have h3 := G1CPhi_nonneg α m c
  have h4 : (0 : ℝ) < 3 + 2 * G1a α m := by
    have := G1a_pos hα m; linarith
  refine div_nonneg (mul_nonneg (by norm_num) ?_) (le_of_lt h4)
  exact add_nonneg (mul_nonneg (le_of_lt h2) h1) h3

/-- `G1f` is continuous on `(0,∞)`. -/
theorem G1f_continuousOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0)) :
    ContinuousOn (G1f α m c) (Set.Ioi 0) := by
  exact hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))

/-- **Integrability of the inner integrand.**  The standing hypothesis `h0`
(`c z²/z⁴` integrable on `(0,1)`) makes `t ↦ c t t^{a-1}` integrable on `(0,1)`: pointwise,
`|c t| t^{a-1} ≤ |c t|/t² ≤ (c t²/t⁴ + 1)/2` for `0 < t ≤ 1`. -/
theorem G1f_integrableOn {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    IntegrableOn (G1f α m c) (Set.Ioo 0 1) := by
  have h2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 1) :=
    (continuousOn_const.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self
  have hmaj : IntegrableOn (fun t : ℝ => c t ^ 2 / t ^ 4 + 1) (Set.Ioo 0 1) := h0.add h2
  refine Integrable.mono' hmaj
    (((G1f_continuousOn hc).mono Set.Ioo_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioo) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := le_of_lt ht.2
  have ha : 0 < (2 * (m : ℝ) + 5) / α := by positivity
  calc ‖G1f α m c t‖ = |c t| * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
        rw [G1f, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    _ ≤ |c t| * t ^ (-2 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine Real.rpow_le_rpow_of_exponent_ge ht0 ht1 ?_
        linarith
    _ = |c t| / t ^ 2 := by
        rw [Real.rpow_neg (le_of_lt ht0), Real.rpow_two, div_eq_mul_inv]
    _ ≤ c t ^ 2 / t ^ 4 + 1 := by
        have hx : (0 : ℝ) ≤ |c t| / t ^ 2 := div_nonneg (abs_nonneg _) (by positivity)
        have h := G1_two_mul_abs_mul_le (|c t| / t ^ 2) 1
        rw [mul_one, one_pow, abs_of_nonneg hx,
          div_pow, sq_abs, ← pow_mul] at h
        norm_num at h
        linarith [h]

/-- **Fundamental theorem of calculus for `G1A`.** -/
theorem G1A_hasDerivAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hInt : IntegrableOn (G1f α m c) (Set.Ioo 0 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (G1A α m c) (G1f α m c z) z := by
  intro z hz
  have hF : ContinuousOn (G1f α m c) (Set.Ioi 0) := G1f_continuousOn hc
  exact intervalIntegral.integral_hasDerivAt_right (a := 0) (b := z)
    (Work.FTS.PhiStar.Radial.intervalIntegrable_of_Ioi_Ioo hz hF hInt)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hF z hz)
    (hF.continuousAt (Ioi_mem_nhds hz))

/-- **Monotonicity of `∫ c z²/z⁴`**: on any `(x,y) ⊆ (0,1)` the integral is at most `M0`
(the integrand is nonnegative and `Ioc x y ⊆ Ioo 0 1`). -/
theorem G1_csq_mono {c : ℝ → ℝ}
    (h0 : IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ x y : ℝ, 0 < x → x < y → y < 1 → ∫ z in x..y, c z ^ 2 / z ^ 4 ≤ G1M0 c := by
  intro x y hx hxy hy1
  rw [intervalIntegral.integral_of_le hxy.le, G1M0]
  refine setIntegral_mono_set h0 (Filter.Eventually.of_forall (fun z => ?_)) ?_
  · exact div_nonneg (sq_nonneg _) (by positivity)
  · exact Filter.Eventually.of_forall
      (fun z hz => ⟨lt_trans hx hz.1, lt_of_le_of_lt hz.2 hy1⟩)

end Work.FTS.EllExist.Honesty
