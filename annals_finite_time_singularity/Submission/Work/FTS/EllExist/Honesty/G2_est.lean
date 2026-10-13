import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllExist.Honesty.RadGreenDefs
import Submission.Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi
import Submission.Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo

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

/-! ## Elementary estimates for the constants of the `z^{s⁺}` estimate

Nothing here is specific to `G2`: we only need `η = 2/(2b-3) > 0` (from `b = 2m/α ≥ 8`), the
nonnegativity of the two integrals `M0 = ∫_{(0,1)} c z²/z⁴` and `H = ∫_1^∞ |c t| t^{-b-1}`, and the
weighted AM–GM inequality `2|XY| ≤ η X² + η⁻¹ Y²`. -/

/-- The AM–GM parameter `η = 2/(2b-3)`, where `b = 2m/α`. -/
private def G2eta (α : ℝ) (m : ℕ) : ℝ := 2 / (2 * (2 * (m : ℝ) / α) - 3)

/-- `H = ∫_{(1,∞)} |c t| · t^{-b-1} dt`, the constant controlling the endpoint `z = 1`. -/
private def G2H (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Ioi 1, |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)

/-- `M0 = ∫_{(0,1)} c z²/z⁴`, the total mass of the density appearing in the hypothesis `h0`. -/
private def G2M0 (c : ℝ → ℝ) : ℝ := ∫ z in Set.Ioo 0 1, c z ^ 2 / z ^ 4

/-- The uniform bound `M = η (η M0 + H²)` of the estimate. -/
private def G2M (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ :=
  G2eta α m * (G2eta α m * G2M0 c + G2H α m c ^ 2)

/-- Young's inequality `2|XY| ≤ X² + Y²`. -/
private lemma G2_two_mul_abs_mul_le (X Y : ℝ) : 2 * |X * Y| ≤ X ^ 2 + Y ^ 2 := by
  have h := sq_nonneg (|X| - |Y|)
  rw [sub_sq, sq_abs, sq_abs] at h
  rw [abs_mul]
  nlinarith [h]

/-- The weighted Young inequality `2|XY| ≤ λ X² + Y²/λ` for `λ > 0` (the AM–GM step). -/
private lemma G2_two_mul_abs_mul_le_mul {l X Y : ℝ} (hl : 0 < l) :
    2 * |X * Y| ≤ l * X ^ 2 + Y ^ 2 / l := by
  have h := G2_two_mul_abs_mul_le (l * X) Y
  rw [abs_mul, abs_mul, abs_of_pos hl, mul_pow] at h
  have h' : l * (2 * |X * Y|) ≤ l * (l * X ^ 2 + Y ^ 2 / l) := by
    have e : l * (l * X ^ 2 + Y ^ 2 / l) = l ^ 2 * X ^ 2 + Y ^ 2 := by
      field_simp
    rw [e, abs_mul]
    nlinarith [h]
  exact le_of_mul_le_mul_left h' hl

/-- `M0 ≥ 0` (the integrand `c z²/z⁴` is a square over a square). -/
private lemma G2M0_nonneg (c : ℝ → ℝ) : 0 ≤ G2M0 c := by
  rw [G2M0]
  exact setIntegral_nonneg measurableSet_Ioo
    (fun z _ => div_nonneg (sq_nonneg _) (by positivity))

/-- `H ≥ 0` (the integrand is nonnegative on `(1,∞)`). -/
private lemma G2H_nonneg (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : 0 ≤ G2H α m c := by
  rw [G2H]
  exact setIntegral_nonneg measurableSet_Ioi
    (fun t ht => mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _))

/-- `η = 2/(2b-3) > 0`, since `b = 2m/α ≥ 8` (`eight_le_two_m_div`). -/
private lemma G2eta_pos (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m) :
    0 < G2eta α m := by
  have h8 := eight_le_two_m_div α hα hα4 m hm
  rw [G2eta]
  have : (0 : ℝ) < 2 * (2 * (m : ℝ) / α) - 3 := by linarith
  positivity

/-- `M ≥ 0`. -/
private lemma G2M_nonneg (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    (c : ℝ → ℝ) : 0 ≤ G2M α m c := by
  have hη : 0 < G2eta α m := G2eta_pos α hα hα4 m hm
  rw [G2M]
  exact mul_nonneg (le_of_lt hη)
    (add_nonneg (mul_nonneg (le_of_lt hη) (G2M0_nonneg c)) (by positivity))

/-! ## The tail integral, its derivative, and the scaled derivative of `G2` -/

/-- `t ↦ c t · t^{-s-1}` is continuous on `(0,∞)` when `c` is. -/
private lemma f2_contOn (s : ℝ) {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0)) :
    ContinuousOn (fun t => c t * t ^ (-s - 1)) (Set.Ioi 0) :=
  hc.mul (continuousOn_id.rpow_const (fun _ ht => Or.inl (ne_of_gt ht)))

/-- The tail integrand `t ↦ c t · t^{-s-1}` is integrable on `(1,∞)` as soon as
`t ↦ |c t| · t^{-s-1}` is: the rpow factor is positive there, so the absolute values agree.  This
is the only use of the decay hypothesis `hinf` in the differentiability statements below. -/
private lemma f2_intOn (s : ℝ) {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-s - 1)) (Set.Ioi 1)) :
    IntegrableOn (fun t => c t * t ^ (-s - 1)) (Set.Ioi 1) := by
  have hmeas : AEStronglyMeasurable (fun t => c t * t ^ (-s - 1))
      (volume.restrict (Set.Ioi 1)) :=
    ((f2_contOn s hc).mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).aestronglyMeasurable
      measurableSet_Ioi
  have hnorm : IntegrableOn (fun t => ‖c t * t ^ (-s - 1)‖) (Set.Ioi 1) :=
    hinf.congr_fun (fun t ht => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _)])
      measurableSet_Ioi
  exact (integrable_norm_iff hmeas).mp hnorm

/-- **FTC for the tail integral** (with the moving base point `z/2`, which avoids any global
integrability assumption on `(0,∞)`): `z ↦ ∫_{t>z} c t t^{-s-1} dt` has derivative
`-c z · z^{-s-1}` for `z > 0`. -/
private lemma tail_deriv (s : ℝ) {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-s - 1)) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      HasDerivAt (fun u => ∫ t in Set.Ioi u, c t * t ^ (-s - 1)) (-(c z * z ^ (-s - 1))) z := by
  intro z hz
  have hz2 : 0 < z / 2 := by linarith
  have hc' : ContinuousOn (fun t => c t * t ^ (-s - 1)) (Set.Ioi (z / 2)) :=
    (f2_contOn s hc).mono (Set.Ioi_subset_Ioi (le_of_lt hz2))
  have hi' : IntegrableOn (fun t => c t * t ^ (-s - 1)) (Set.Ioi (z / 2)) :=
    Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo hz2 (f2_contOn s hc)
      (f2_intOn s hc hinf)
  exact Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi (by linarith) hc' hi'

/-- Scalar algebra for the product rule: for `z > 0` and real `B, C`,
`z·(s z^{s-1} B - z^s C z^{-s-1}) = s z^s B - C`. -/
private lemma scaled_alg {z s : ℝ} (hz : 0 < z) (B C : ℝ) :
    z * (s * z ^ (s - 1) * B + z ^ s * (-(C * z ^ (-s - 1)))) = s * (z ^ s * B) - C := by
  have hA : z * z ^ (s - 1) = z ^ s := by
    have h := Real.rpow_add hz (s - 1) 1
    rw [Real.rpow_one, show s - 1 + 1 = s from by ring] at h
    rw [mul_comm z (z ^ (s - 1))]
    exact h.symm
  have hC : z * z ^ s * z ^ (-s - 1) = 1 := by
    have h := Real.rpow_add hz s (-s - 1)
    rw [show z * z ^ s * z ^ (-s - 1) = z * (z ^ s * z ^ (-s - 1)) from by ring, ← h,
      show s + (-s - 1) = -1 from by ring, Real.rpow_neg_one]
    exact mul_inv_cancel₀ (ne_of_gt hz)
  have e1 : z * (s * z ^ (s - 1) * B) = s * (z ^ s * B) := by
    rw [show z * (s * z ^ (s - 1) * B) = s * (z * z ^ (s - 1)) * B from by ring, hA]
    ring
  have e2 : z * (z ^ s * (-(C * z ^ (-s - 1)))) = -C := by
    rw [show z * (z ^ s * (-(C * z ^ (-s - 1))))
        = -(C * (z * z ^ s * z ^ (-s - 1))) from by ring, hC]
    ring
  rw [mul_add, e1, e2]
  ring

/-- **The (scaled) logarithmic derivative of the `z^{s⁺}` Green term**: `z · Ψ'(z) = s⁺ Ψ(z) - c z`
at every `z > 0`, `s⁺ = 2m/α`, equivalently `HasDerivAt Ψ ((s⁺ Ψ z - c z)/z) z`. -/
private lemma G2_scaled_deriv (α : ℝ) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → HasDerivAt (fun w => G2 α m c w)
      ((2 * (m : ℝ) / α * G2 α m c z - c z) / z) z := by
  intro z hz
  have hzne : z ≠ 0 := ne_of_gt hz
  set s : ℝ := 2 * (m : ℝ) / α with hs
  have hinf' : IntegrableOn (fun t => |c t| * t ^ (-s - 1)) (Set.Ioi 1) := by
    rw [hs]; exact hinf
  have hB := tail_deriv s hc hinf' z hz
  have hp : HasDerivAt (fun u : ℝ => u ^ s) (s * z ^ (s - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hzne)
  have hprod := hp.mul hB
  change HasDerivAt (fun w : ℝ => w ^ s * (∫ t in Set.Ioi w, c t * t ^ (-s - 1)))
    ((s * (G2 α m c z) - c z) / z) z
  have hval : s * z ^ (s - 1) * (∫ t in Set.Ioi z, c t * t ^ (-s - 1))
      + z ^ s * (-(c z * z ^ (-s - 1)))
      = (s * G2 α m c z - c z) / z := by
    have hG : G2 α m c z = z ^ s * (∫ t in Set.Ioi z, c t * t ^ (-s - 1)) := rfl
    rw [hG, eq_div_iff hzne]
    simpa [mul_comm] using scaled_alg hz (∫ t in Set.Ioi z, c t * t ^ (-s - 1)) (c z)
  exact hprod.congr_deriv hval

/-- `G2 α m c` is continuous on `(0,∞)` (it is differentiable there, by `G2_scaled_deriv`). -/
private lemma G2_continuousOn (α : ℝ) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ContinuousOn (fun z => G2 α m c z) (Set.Ioi 0) :=
  fun z hz => ((G2_scaled_deriv α m hc hinf z hz).continuousAt).continuousWithinAt

/-! ## The energy identity on `[x,1]` and the endpoint bound at `z = 1` -/

/-- The quotient `z ↦ Ψ z²/z³` has derivative `((2b-3) Ψ z² - 2 c z Ψ z)/z⁴` whenever
`Ψ'(z) = (b Ψ z - c z)/z`. -/
private lemma u_deriv (b : ℝ) {Ψ : ℝ → ℝ} {c : ℝ → ℝ}
    (hΨ : ∀ z : ℝ, 0 < z → HasDerivAt Ψ ((b * Ψ z - c z) / z) z) :
    ∀ z : ℝ, 0 < z → HasDerivAt (fun z => Ψ z ^ 2 / z ^ 3)
      (((2 * b - 3) * Ψ z ^ 2 - 2 * c z * Ψ z) / z ^ 4) z := by
  intro z hz
  have hzne : z ≠ 0 := ne_of_gt hz
  have h1 : HasDerivAt (fun w : ℝ => Ψ w ^ 2)
      (2 * Ψ z ^ (2 - 1) * ((b * Ψ z - c z) / z)) z := (hΨ z hz).pow 2
  have h2 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ (3 - 1) * 1) z :=
    (hasDerivAt_id z).pow 3
  have h3 := h1.div h2 (pow_ne_zero 3 hzne)
  refine h3.congr_deriv ?_
  have hz3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hzne
  field_simp
  ring

/-- **Energy identity** for `Ψ = G2 α m c` on `[x,1]`, `0 < x < 1`:
`(2b-3) ∫_x^1 Ψ²/z⁴ = 2 ∫_x^1 c z Ψ/z⁴ + Ψ(1)² - Ψ(x)²/x³`. -/
private lemma G2_energy (α : ℝ) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ x : ℝ, 0 < x → x < 1 →
      (2 * (2 * (m : ℝ) / α) - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
        = 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4)
          + G2 α m c 1 ^ 2 - G2 α m c x ^ 2 / x ^ 3 := by
  intro x hx hx1
  set b : ℝ := 2 * (m : ℝ) / α with hb
  have hscaled := G2_scaled_deriv α m hc hinf
  have hscaled' : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => G2 α m c w) ((b * G2 α m c z - c z) / z) z := by
    intro z hz
    have hval : (b * G2 α m c z - c z) / z
        = (2 * (m : ℝ) / α * G2 α m c z - c z) / z := by rw [hb]
    rw [hval]
    exact hscaled z hz
  have hderiv := u_deriv b hscaled'
  have hsub : Set.Icc x 1 ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le hx hz.1
  have hΨc : ContinuousOn (fun z => G2 α m c z) (Set.Icc x 1) := fun z hz =>
    ((hscaled z (hsub hz)).continuousAt).continuousWithinAt
  have hcc : ContinuousOn c (Set.Icc x 1) := hc.mono hsub
  have hz4ne : ∀ z ∈ Set.Icc x 1, z ^ 4 ≠ 0 := fun z hz =>
    pow_ne_zero 4 (ne_of_gt (hsub hz))
  have hinteg : IntervalIntegrable
      (fun z => ((2 * b - 3) * G2 α m c z ^ 2 - 2 * c z * G2 α m c z) / z ^ 4) volume x 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx1.le]
    exact ContinuousOn.div (ContinuousOn.sub
      (continuousOn_const.mul (hΨc.pow 2)) ((continuousOn_const.mul hcc).mul hΨc))
      (continuousOn_id.pow 4) hz4ne
  have hpoint : ∀ z ∈ Set.uIcc x 1,
      HasDerivAt (fun z => G2 α m c z ^ 2 / z ^ 3)
        (((2 * b - 3) * G2 α m c z ^ 2 - 2 * c z * G2 α m c z) / z ^ 4) z := by
    intro z hz
    rw [Set.uIcc_of_le hx1.le] at hz
    exact hderiv z (hsub hz)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hpoint hinteg
  have hI1 : IntervalIntegrable (fun z => G2 α m c z ^ 2 / z ^ 4) volume x 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx1.le]
    exact ContinuousOn.div (hΨc.pow 2) (continuousOn_id.pow 4) hz4ne
  have hI2 : IntervalIntegrable (fun z => c z * G2 α m c z / z ^ 4) volume x 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx1.le]
    exact ContinuousOn.div (hcc.mul hΨc) (continuousOn_id.pow 4) hz4ne
  have hsplit : (∫ z in x..1, ((2 * b - 3) * G2 α m c z ^ 2 - 2 * c z * G2 α m c z) / z ^ 4)
      = (2 * b - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
        - 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4) := by
    have hfun : (fun z => ((2 * b - 3) * G2 α m c z ^ 2 - 2 * c z * G2 α m c z) / z ^ 4)
        = fun z => (2 * b - 3) * (G2 α m c z ^ 2 / z ^ 4)
            - 2 * (c z * G2 α m c z / z ^ 4) := by
      funext z; ring
    rw [hfun, intervalIntegral.integral_sub (hI1.const_mul (2 * b - 3)) (hI2.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hfinal : (2 * b - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
      = 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4)
        + G2 α m c 1 ^ 2 - G2 α m c x ^ 2 / x ^ 3 := by
    have h1 : G2 α m c 1 ^ 2 / 1 ^ 3 = G2 α m c 1 ^ 2 := by norm_num
    rw [hsplit] at hFTC
    linarith [hFTC, h1]
  rw [hb] at hfinal
  exact hfinal

/-- **Endpoint bound at `z = 1`**: `|G2 α m c 1| ≤ H`, because at `z = 1` the prefactor `z^{s⁺}`
equals `1` and the value is the tail integral, which the triangle inequality bounds by `H`. -/
private lemma G2_one_le (α : ℝ) (m : ℕ) {c : ℝ → ℝ}
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    |G2 α m c 1| ≤ G2H α m c := by
  rw [G2H, G2, Real.one_rpow, one_mul]
  refine le_trans (MeasureTheory.abs_integral_le_integral_abs)
    (le_of_eq (MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_))
  intro t ht
  show |c t * t ^ (-(2 * (m : ℝ) / α) - 1)| = |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one ht) _)]

/-- **Monotonicity of the mass integral**: `∫_x^1 c z²/z⁴ ≤ M0` for `0 < x < 1` (the integrand is
nonnegative and `(x,1] ⊆ᵃᵉ (0,1)`). -/
private lemma G2_csq_mono {c : ℝ → ℝ}
    (h0 : IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ x : ℝ, 0 < x → x < 1 →
      (∫ z in x..1, c z ^ 2 / z ^ 4) ≤ G2M0 c := by
  intro x hx hx1
  have hf : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (fun z => c z ^ 2 / z ^ 4) :=
    Filter.Eventually.of_forall (fun z => div_nonneg (sq_nonneg _) (by positivity))
  have hsub : Set.Ioc x 1 \ Set.Ioo (0 : ℝ) 1 ⊆ ({1} : Set ℝ) := by
    intro t ht
    simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_Ioo, Set.mem_singleton_iff] at ht ⊢
    by_cases h : t ≤ 0
    · linarith [ht.1.1, hx, h]
    · have h1 : 0 < t := lt_of_not_ge h
      by_contra hne
      exact ht.2 ⟨h1, lt_of_le_of_ne ht.1.2 hne⟩
  have hst : Set.Ioc x 1 ≤ᵐ[volume] Set.Ioo (0 : ℝ) 1 := by
    rw [ae_le_set]
    exact measure_mono_null hsub (measure_singleton 1)
  rw [G2M0, intervalIntegral.integral_of_le hx1.le]
  exact MeasureTheory.setIntegral_mono_set h0 hf hst


-- ROUTE (the `z → 0` half of the weighted `L²`-honesty of the `z^{s⁺}` Green term of `radGreen`).
-- Let `b := 2*(m:ℝ)/α` (so `b ≥ 8` by `Work.FTS.EllExist.Honesty.eight_le_two_m_div`, from `hα`, `hα4`, `hm`),
-- `f2 t := c t * t^(-b-1)`, `B z := ∫ t in Ioi z, f2 t`, `Ψ := Work.FTS.EllExist.Honesty.G2 α m c`
-- (so `Ψ z = z^b * B z`), `M0 := ∫ z in Ioo 0 1, c z^2/z^4` (a nonnegative real, finite by `h0`), and
-- `H := ∫ t in Ioi 1, |c t| * t^(-b-1)` (a nonnegative real, finite by `hinf`).
--
-- TWO TRAPS: (i) do NOT try to bound `∫ z in z₀..1, t^(2-2b)` by `1/(2b-3)`: since `2-2b ≤ -14 < -1` the
-- true value is `(z₀^(3-2b)-1)/(2b-3) → ∞`, and `|B z|` is indeed unbounded as `z → 0` (e.g. `c t = t²` gives
-- `B z = z^{-6}/6`, yet `Ψ z = z²/6` is perfectly bounded).  (ii) `f2` need NOT be in `L¹(0,∞)` (same
-- example), so `Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi` must be applied with a base point `a < z`,
-- e.g. `a := z/2` (its hypotheses then only need `f2` continuous on `(z/2,∞)` and integrable on
-- `Ioi (z/2)`, which holds because `f2` is continuous on the compact `[z/2,1]` and integrable on `Ioi 1`
-- by `hinf`).
--
-- The uniform bound comes from the energy identity on `[x,1]`:
-- (1) `B` is differentiable on `(0,∞)` with `B' z = -f2 z`, hence `z * deriv Ψ z = b*Ψ z - c z` for `z > 0`
--     (use `b * z^(b-1) * B z + z^b * (-f2 z) = (b*Ψ z - c z)/z`, since `z^(b+1) * f2 z = c z`).
-- (2) `u z := Ψ z^2 / z^3` has `u' z = ((2b-3)*Ψ z^2 - 2*c z*Ψ z)/z^4`; the FTC on `[x,1]` (`0 < x < 1`) gives
--       `(2b-3) * ∫ z in x..1, Ψ z^2/z^4 = 2 * ∫ z in x..1, c z * Ψ z/z^4 + Ψ 1^2 - Ψ x^2/x^3`.
--     Both endpoint terms are harmless: `Ψ x^2/x^3 ≥ 0` is SUBTRACTED, and `|Ψ 1| = |B 1| ≤ H`.
-- (3) AM-GM `2*|c z * Ψ z|/z^4 ≤ η*c z^2/z^4 + η^{-1}*Ψ z^2/z^4` with `η := 2/(2b-3)`, together with
--     `∫ z in x..1, c z^2/z^4 ≤ M0`, gives `((2b-3)/2) * ∫ z in x..1, Ψ^2/z^4 ≤ η*M0 + H^2`, i.e.
--     `∫ z in x..1, Ψ z^2/z^4 ≤ M := 2*(η*M0 + H^2)/(2b-3)` for every `x ∈ (0,1)`.  For the requested
--     interval `(x,y)`, `y < 1`, monotonicity of the integral of the nonnegative integrand gives
--     `∫ z in x..y, Ψ z^2/z^4 ≤ ∫ z in x..1, Ψ z^2/z^4 ≤ M`.
-- (4) Continuity of `Ψ` on `(0,∞)`: product of the continuous `z ↦ z^b` and the differentiable `B`.
theorem G2_est (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x y : ℝ, 0 < x → x < y → y < 1 →
        (∫ z in x..y, Work.FTS.EllExist.Honesty.G2 α m c z ^ 2 / z ^ 4) ≤ M) ∧
      ContinuousOn (fun z => Work.FTS.EllExist.Honesty.G2 α m c z) (Set.Ioi 0) := by
  have hη : 0 < G2eta α m := G2eta_pos α hα hα4 m hm
  refine ⟨⟨G2M α m c, G2M_nonneg α hα hα4 m hm c, ?_⟩, G2_continuousOn α m hc hinf⟩
  intro x y hx hxy hy1
  have hx1 : x < 1 := lt_trans hxy hy1
  have hIn : ∀ z ∈ Set.Icc x 1, (0 : ℝ) < z := fun z hz => lt_of_lt_of_le hx hz.1
  have hsub : Set.Icc x 1 ⊆ Set.Ioi (0 : ℝ) := fun z hz => hIn z hz
  have hΦc : ContinuousOn (fun z => G2 α m c z) (Set.Icc x 1) :=
    (G2_continuousOn α m hc hinf).mono hsub
  have hcc : ContinuousOn c (Set.Icc x 1) := hc.mono hsub
  have hpow : ContinuousOn (fun z : ℝ => z ^ 4) (Set.Icc x 1) := continuousOn_id.pow 4
  have hz4ne : ∀ z ∈ Set.Icc x 1, z ^ 4 ≠ 0 := fun z hz => pow_ne_zero 4 (ne_of_gt (hIn z hz))
  -- the pointwise AM–GM inequality `2|c Ψ|/z⁴ ≤ η c²/z⁴ + η⁻¹ Ψ²/z⁴`
  have hpt : ∀ z ∈ Set.Icc x 1,
      2 * |c z * G2 α m c z / z ^ 4|
        ≤ G2eta α m * (c z ^ 2 / z ^ 4) + (G2eta α m)⁻¹ * (G2 α m c z ^ 2 / z ^ 4) := by
    intro z _
    have h1 : 2 * |c z * G2 α m c z| ≤ G2eta α m * c z ^ 2 + (G2eta α m)⁻¹ * (G2 α m c z) ^ 2 := by
      have h := G2_two_mul_abs_mul_le_mul (hl := hη) (X := c z) (Y := G2 α m c z)
      have e : (G2 α m c z) ^ 2 / G2eta α m = (G2eta α m)⁻¹ * (G2 α m c z) ^ 2 := by
        rw [div_eq_mul_inv, mul_comm]
      linarith [h, e]
    have h2 : 2 * |c z * G2 α m c z / z ^ 4| = 2 * |c z * G2 α m c z| / z ^ 4 := by
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 4)]
      ring
    have h3 : (G2eta α m * c z ^ 2 + (G2eta α m)⁻¹ * (G2 α m c z) ^ 2) / z ^ 4
        = G2eta α m * (c z ^ 2 / z ^ 4) + (G2eta α m)⁻¹ * (G2 α m c z ^ 2 / z ^ 4) := by
      ring
    rw [h2, ← h3]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  -- continuity of the two comparison integrands on `[x,1]`
  have huIcc : Set.uIcc x 1 = Set.Icc x 1 := Set.uIcc_of_le hx1.le
  have hcont1 : ContinuousOn (fun z : ℝ => 2 * |c z * G2 α m c z / z ^ 4|) (Set.uIcc x 1) := by
    rw [huIcc]
    exact continuousOn_const.mul (ContinuousOn.abs (ContinuousOn.div (hcc.mul hΦc) hpow hz4ne))
  have hcont2 : ContinuousOn
      (fun z : ℝ => G2eta α m * (c z ^ 2 / z ^ 4) + (G2eta α m)⁻¹ * (G2 α m c z ^ 2 / z ^ 4))
      (Set.uIcc x 1) := by
    rw [huIcc]
    exact ContinuousOn.add (continuousOn_const.mul (ContinuousOn.div (hcc.pow 2) hpow hz4ne))
      (continuousOn_const.mul (ContinuousOn.div (hΦc.pow 2) hpow hz4ne))
  have hI1 : IntervalIntegrable (fun z : ℝ => 2 * |c z * G2 α m c z / z ^ 4|) volume x 1 :=
    ContinuousOn.intervalIntegrable hcont1
  have hI2 : IntervalIntegrable
      (fun z : ℝ => G2eta α m * (c z ^ 2 / z ^ 4) + (G2eta α m)⁻¹ * (G2 α m c z ^ 2 / z ^ 4))
      volume x 1 := ContinuousOn.intervalIntegrable hcont2
  have hIc : IntervalIntegrable (fun z : ℝ => c z ^ 2 / z ^ 4) volume x 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact ContinuousOn.div (hcc.pow 2) hpow hz4ne
  have hIg : IntervalIntegrable (fun z : ℝ => G2 α m c z ^ 2 / z ^ 4) volume x 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact ContinuousOn.div (hΦc.pow 2) hpow hz4ne
  have hlin : (∫ z in x..1,
        G2eta α m * (c z ^ 2 / z ^ 4) + (G2eta α m)⁻¹ * (G2 α m c z ^ 2 / z ^ 4))
      = G2eta α m * (∫ z in x..1, c z ^ 2 / z ^ 4)
        + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) := by
    rw [intervalIntegral.integral_add (hIc.const_mul (G2eta α m)) (hIg.const_mul (G2eta α m)⁻¹),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hmono_int := intervalIntegral.integral_mono_on hx1.le hI1 hI2 hpt
  have h2I2 : 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4)
      ≤ ∫ z in x..1, 2 * |c z * G2 α m c z / z ^ 4| := by
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (f := fun z : ℝ => c z * G2 α m c z / z ^ 4) hx1.le
    have hle : (∫ z in x..1, c z * G2 α m c z / z ^ 4)
        ≤ ∫ z in x..1, |c z * G2 α m c z / z ^ 4| := le_trans (le_abs_self _) habs
    have hmul : 2 * (∫ z in x..1, |c z * G2 α m c z / z ^ 4|)
        = ∫ z in x..1, 2 * |c z * G2 α m c z / z ^ 4| := by
      rw [intervalIntegral.integral_const_mul]
    linarith
  have hA : 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4)
      ≤ G2eta α m * (∫ z in x..1, c z ^ 2 / z ^ 4)
        + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) :=
    le_trans h2I2 (le_trans hmono_int (le_of_eq hlin))
  have hB : G2eta α m * (∫ z in x..1, c z ^ 2 / z ^ 4) ≤ G2eta α m * G2M0 c :=
    mul_le_mul_of_nonneg_left (G2_csq_mono h0 x hx hx1) (le_of_lt hη)
  have hei := G2_energy α m hc hinf x hx hx1
  have hH2 : G2 α m c 1 ^ 2 ≤ G2H α m c ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (G2_one_le α m hinf) 2
  have hxend : 0 ≤ G2 α m c x ^ 2 / x ^ 3 := div_nonneg (sq_nonneg _) (by positivity)
  have h3 : (2 * (2 * (m : ℝ) / α) - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
      ≤ G2eta α m * G2M0 c + G2H α m c ^ 2
        + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) := by
    calc (2 * (2 * (m : ℝ) / α) - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
        = 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4)
          + G2 α m c 1 ^ 2 - G2 α m c x ^ 2 / x ^ 3 := hei
      _ ≤ 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4) + G2H α m c ^ 2 := by
          linarith [hH2, hxend]
      _ ≤ (G2eta α m * (∫ z in x..1, c z ^ 2 / z ^ 4)
            + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)) + G2H α m c ^ 2 := by
          linarith [hA]
      _ ≤ (G2eta α m * G2M0 c
            + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)) + G2H α m c ^ 2 := by
          linarith [hB]
      _ = G2eta α m * G2M0 c + G2H α m c ^ 2
            + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) := by ring
  have heta : 2 * (2 * (m : ℝ) / α) - 3 - (G2eta α m)⁻¹ = (G2eta α m)⁻¹ := by
    rw [G2eta, inv_div]; ring
  have hcoef : (2 * (2 * (m : ℝ) / α) - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
        - (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
      = (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) := by
    rw [← sub_mul, heta]
  have key : (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
      ≤ G2eta α m * G2M0 c + G2H α m c ^ 2 := by linarith [h3, hcoef]
  have hA1 : (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) ≤ G2M α m c := by
    rw [G2M]
    calc (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
        = G2eta α m * ((G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hη), one_mul]
      _ ≤ G2eta α m * (G2eta α m * G2M0 c + G2H α m c ^ 2) :=
          mul_le_mul_of_nonneg_left key (le_of_lt hη)
  have hmono' : (∫ z in x..y, G2 α m c z ^ 2 / z ^ 4)
      ≤ ∫ z in x..1, G2 α m c z ^ 2 / z ^ 4 := by
    refine intervalIntegral.integral_mono_interval (μ := volume) le_rfl hxy.le hy1.le ?_ hIg
    exact Filter.Eventually.of_forall (fun z => div_nonneg (sq_nonneg _) (by positivity))
  linarith [hA1, hmono']

end Work.FTS.EllExist.Honesty
