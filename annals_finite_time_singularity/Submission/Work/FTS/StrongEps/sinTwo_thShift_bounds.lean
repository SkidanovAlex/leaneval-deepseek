import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.Weights

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-! ## Elementary trigonometric and algebraic helpers

The whole statement reduces to the classical identity `sin (2 arctan x) = 2x / (1 + x²)` together
with the (elementary, but sign-sensitive) inequality

`q · 2t/(1+t²) ≤ 2tq/(1+t²q²) ≤ q⁻¹ · 2t/(1+t²)` for `0 < q ≤ 1` (and its reverse for `q ≥ 1`),

which is `q² ≤ 1` in disguise. -/

/-- **`sin (2·)` at an arctangent**: `sin (2 arctan x) = 2x / (1 + x²)`. -/
theorem sin_two_arctan (x : ℝ) : Real.sin (2 * Real.arctan x) = 2 * x / (1 + x ^ 2) := by
  have hsin : Real.sin (Real.arctan x) = x * Real.cos (Real.arctan x) := by
    have h := Real.tan_arctan x
    rw [Real.tan_eq_sin_div_cos] at h
    field_simp at h
    rw [h, mul_comm]
  rw [Real.sin_two_mul, hsin,
    show (2 : ℝ) * (x * Real.cos (Real.arctan x)) * Real.cos (Real.arctan x)
      = 2 * x * Real.cos (Real.arctan x) ^ 2 from by ring, Real.cos_sq_arctan]
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  field_simp

/-- The algebraic core for the *lower* case `0 < q ≤ 1`: multiplication by `2t/(1+t²) > 0` sends
the factor `min q q⁻¹ = q` to the factor `q · (1+t²)/(1+t²q²)`, which lies between `q` and `q⁻¹`. -/
theorem tan_shift_bounds_le {t q : ℝ} (ht : 0 < t) (hq : 0 < q) (h1 : q ≤ 1) :
    q * (2 * t / (1 + t ^ 2)) ≤ 2 * t * q / (1 + t ^ 2 * q ^ 2) ∧
      2 * t * q / (1 + t ^ 2 * q ^ 2) ≤ q⁻¹ * (2 * t / (1 + t ^ 2)) := by
  have hsq : q ^ 2 ≤ 1 := by nlinarith
  constructor
  · field_simp
    nlinarith [sq_nonneg t]
  · field_simp
    nlinarith [sq_nonneg t]

/-- The algebraic core for the *upper* case `1 ≤ q` (the mirror of `tan_shift_bounds_le`). -/
theorem tan_shift_bounds_ge {t q : ℝ} (ht : 0 < t) (hq : 0 < q) (h1 : 1 ≤ q) :
    q⁻¹ * (2 * t / (1 + t ^ 2)) ≤ 2 * t * q / (1 + t ^ 2 * q ^ 2) ∧
      2 * t * q / (1 + t ^ 2 * q ^ 2) ≤ q * (2 * t / (1 + t ^ 2)) := by
  have hsq : 1 ≤ q ^ 2 := by nlinarith
  constructor
  · field_simp
    nlinarith [sq_nonneg t]
  · field_simp
    nlinarith [sq_nonneg t]

/-- **`sin (2·)` changes by a bounded factor under the `θ`-shift.**  For `θ ∈ (0, π/2)` and every
`p : ℝ`, the shifted angle `thShift θ p = arctan (tan θ * Real.exp (-p))` satisfies
`e^{-|p|} sin (2 θ) ≤ sin (2 (thShift θ p)) ≤ e^{|p|} sin (2 θ)`.
Equivalently `sin (2 (thShift θ p)) / sin (2 θ) = e^{-p} (1 + tan²θ) / (1 + tan²θ · e^{-2p})`.
This is the `p₂`-half of the weight-shift bound for the angular weight `sin (2θ)^{-γ}` of the
weighted spaces `ℋ^k` of the Elgindi project. -/
theorem sinTwo_thShift_bounds {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.exp (-|p|) * Real.sin (2 * θ) ≤ Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ∧
      Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ≤ Real.exp |p| * Real.sin (2 * θ) := by
  have htp : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
  have hqp : 0 < Real.exp (-p) := Real.exp_pos _
  have hsinφ : Real.sin (2 * Work.FTS.StrongEps.thShift θ p)
      = 2 * Real.tan θ * Real.exp (-p) / (1 + Real.tan θ ^ 2 * Real.exp (-p) ^ 2) := by
    simp only [Work.FTS.StrongEps.thShift]
    rw [sin_two_arctan]
    ring
  have hsinθ : Real.sin (2 * θ) = 2 * Real.tan θ / (1 + Real.tan θ ^ 2) := by
    have hθar : θ = Real.arctan (Real.tan θ) :=
      (Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2).symm
    conv_lhs => rw [hθar]
    exact sin_two_arctan _
  have hexp : Real.exp p = (Real.exp (-p))⁻¹ := by rw [Real.exp_neg, inv_inv]
  rw [hsinφ, hsinθ]
  rcases le_total 0 p with hp | hp
  · rw [abs_of_nonneg hp]
    have hq1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    obtain ⟨hlo, hhi⟩ := tan_shift_bounds_le htp hqp hq1
    exact ⟨hlo, by rw [hexp]; exact hhi⟩
  · rw [abs_of_nonpos hp, neg_neg, hexp]
    have hq1 : 1 ≤ Real.exp (-p) := Real.one_le_exp_iff.mpr (by linarith)
    obtain ⟨hlo, hhi⟩ := tan_shift_bounds_ge htp hqp hq1
    exact ⟨hlo, hhi⟩

end Work.FTS.StrongEps
