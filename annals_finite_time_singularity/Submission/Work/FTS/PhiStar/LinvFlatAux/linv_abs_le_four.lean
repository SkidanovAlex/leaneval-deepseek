import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.LinvFlat.Linv_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.LinvFlatAux.linv_abs_le_four`

The quantitative form of the zero-moment Dirichlet inverse bound, with the *explicit* constant
`4`: for `h : ℝ → ℝ` with `|h| ≤ K` on `(0, π/2)`, `h · sinCos2` integrable on `Iθ` and
`∫_{Iθ} h · sinCos2 = 0`,

  `|Linv h θ| ≤ 4 K`   for every `θ ∈ (0, π/2)`.

`Linv h θ = -(sin²θ cos³θ)⁻¹ ∫_0^θ h · sinCos2 / 2` (`Linv h θ = -μ(θ)⁻¹ ∫_0^θ μ h / sin 2θ`
with `μ = sin²θ cos³θ`, the quotient integrand being `h · sinCos2 / 2` identically since
`sin 2θ = 2 sinθ cosθ`, both sides vanishing where `sin θ cos θ = 0`).  There are two bounds on
the moment `N(θ) = ∫_0^θ h · sinCos2`:

* directly, `|N(θ)| ≤ K ∫_0^θ sinCos2 = K (1 - cos³θ)/3`;
* using the zero-moment hypothesis (`N(π/2) = 0`) and additivity of the interval integral,
  `|N(θ)| = |∫_θ^{π/2} h · sinCos2| ≤ K ∫_θ^{π/2} sinCos2 = K cos³θ/3`.

Splitting at `θ = π/4` and using `cos θ ≥ 1 - 2θ/π ≥ 1/2` for `θ ≤ π/4`
(`Real.one_sub_mul_le_cos`) resp. `sin θ ≥ 2θ/π ≥ 1/2` for `θ ≥ π/4` (`Real.mul_le_sin`) gives
`|Linv h θ| ≤ 4K`.

This is the explicit-constant version of `Work.FTS.PhiStar.LinvFlat.Linv_abs_le` (which is
stated with an existential constant and is proved with the same witness `4`).
-/

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.LinvFlatAux

set_option maxHeartbeats 800000

/-! ## Elementary facts -/

/-- `sinCos2` is nonnegative on the open quadrant. -/
private lemma sinCos2_nonneg {t : ℝ} (ht : t ∈ Set.Ioo 0 (π/2)) :
    0 ≤ Work.Elliptic.sinCos2 t := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2, Real.pi_pos]))
    (sq_nonneg _)

/-- The integrand of `Linv` is `sin θ cos²θ / 2 · h θ` (identically: both sides vanish at the
endpoints, where `sin 2θ = 0`). -/
private lemma integrand_eq (h : ℝ → ℝ) (t : ℝ) :
    Real.sin t ^ 2 * Real.cos t ^ 3 * h t / Work.Construction.s2 t
      = (1 / 2) * (h t * Work.Elliptic.sinCos2 t) := by
  rw [Work.Elliptic.sinCos2, Work.Construction.s2_eq, Real.sin_two_mul]
  by_cases hs : Real.sin t = 0
  · simp [hs]
  · by_cases hc : Real.cos t = 0
    · simp [hc]
    · field_simp

/-- Unfolding of `Linv` in terms of the (finite) integral `∫_0^θ h · sinCos2`. -/
private lemma Linv_eq (h : ℝ → ℝ) (θ : ℝ) :
    Work.FTS.PhiStar.Linv h θ
      = -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ *
          ((1 / 2) * ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t)) := by
  have hint : (∫ θ' in (0 : ℝ)..θ,
        Real.sin θ' ^ 2 * Real.cos θ' ^ 3 * h θ' / Work.Construction.s2 θ')
      = (1 / 2) * ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t := by
    rw [intervalIntegral.integral_congr (fun t _ => integrand_eq h t),
        intervalIntegral.integral_const_mul]
  simp only [Work.FTS.PhiStar.Linv]
  rw [hint]

/-! ## Integrability and the pointwise vs. weight comparison -/

/-- The moment integrand is interval integrable on every subinterval of `[0, π/2]`. -/
private lemma intervalIntegrable_moment {h : ℝ → ℝ}
    (hint : IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π/2) (hab : a ≤ b) :
    IntervalIntegrable (fun t => h t * Work.Elliptic.sinCos2 t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine hint.mono_set ?_
  intro t ht
  exact ⟨le_trans ha ht.1.le, le_trans ht.2 hb⟩

/-- The key comparison: on any subinterval of `[0, π/2]`, `|∫ h · sinCos2| ≤ K ∫ sinCos2`. -/
private lemma interval_bound {h : ℝ → ℝ} {K : ℝ}
    (hbd : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) → |h θ| ≤ K)
    (hint : IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π/2) (hab : a ≤ b) :
    |∫ t in a..b, h t * Work.Elliptic.sinCos2 t| ≤ K * ∫ t in a..b, Work.Elliptic.sinCos2 t := by
  have hf : IntervalIntegrable (fun t => |h t * Work.Elliptic.sinCos2 t|) volume a b :=
    (intervalIntegrable_moment hint ha hb hab).abs
  have hg : IntervalIntegrable (fun t => K * Work.Elliptic.sinCos2 t) volume a b :=
    (continuous_const.mul (by unfold Work.Elliptic.sinCos2; fun_prop)).intervalIntegrable a b
  have hpoint : ∀ x ∈ Set.Ioo a b,
      |h x * Work.Elliptic.sinCos2 x| ≤ K * Work.Elliptic.sinCos2 x := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (π/2) := ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
    have hnn : 0 ≤ Work.Elliptic.sinCos2 x := sinCos2_nonneg hx'
    rw [abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right (hbd x hx') hnn
  calc |∫ t in a..b, h t * Work.Elliptic.sinCos2 t|
      ≤ ∫ t in a..b, |h t * Work.Elliptic.sinCos2 t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, K * Work.Elliptic.sinCos2 t :=
        intervalIntegral.integral_mono_on_of_le_Ioo hab hf hg hpoint
    _ = K * ∫ t in a..b, Work.Elliptic.sinCos2 t := intervalIntegral.integral_const_mul K _

/-! ## The weight integral -/

private lemma hasDerivAt_prim (y : ℝ) :
    HasDerivAt (fun x => -(Real.cos x ^ 3) / 3) (Real.sin y * Real.cos y ^ 2) y := by
  have h1 := (Real.hasDerivAt_cos y).pow 3
  have h2 := h1.const_mul (-(1 / 3) : ℝ)
  convert h2 using 1
  · funext x; simp only [Pi.pow_apply]; ring
  · ring_nf

/-- `∫_a^b sin t cos²t dt = (cos³a - cos³b)/3`. -/
private lemma integral_sinCos2 (a b : ℝ) :
    ∫ t in a..b, Work.Elliptic.sinCos2 t = (Real.cos a ^ 3 - Real.cos b ^ 3) / 3 := by
  have hcont : IntervalIntegrable (fun t => Real.sin t * Real.cos t ^ 2) volume a b :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => -(Real.cos x ^ 3) / 3)
    (f' := fun x => Real.sin x * Real.cos x ^ 2)
    (fun x _ => hasDerivAt_prim x) hcont
  change ∫ t in a..b, Real.sin t * Real.cos t ^ 2 = _
  rw [h]
  ring

/-- The zero-moment hypothesis, transported to the interval `0..π/2`. -/
private lemma moment_zero {h : ℝ → ℝ}
    (hmom : (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∫ t in (0 : ℝ)..(π/2), h t * Work.Elliptic.sinCos2 t = 0 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π/2)] at hmom
  exact hmom

/-! ## The bound -/

theorem linv_abs_le_four {h : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) → |h θ| ≤ K)
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) → |Work.FTS.PhiStar.Linv h θ| ≤ 4 * K := by
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ2 : θ < π/2 := hθ.2
  have hsinpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcospos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩
  have hsinsq : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq θ
  have hden : 0 < Real.sin θ ^ 2 * Real.cos θ ^ 3 :=
    mul_pos (pow_pos hsinpos 2) (pow_pos hcospos 3)
  rw [Linv_eq h θ]
  set J : ℝ := ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t with hJdef
  have habs : |-( (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * ((1 / 2) * J))|
      = (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * |J| := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hden),
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  rw [habs]
  rcases lt_or_ge θ (π/4) with hcase | hcase
  · -- small angles: `|N| ≤ K (1 - cos³θ)/3` and `1 - cos³θ ≤ 3 sin²θ`
    have hc12 : (1 : ℝ)/2 ≤ Real.cos θ := by
      have h := Real.one_sub_mul_le_cos hθ0.le hθ2.le
      have h2 : 2/Real.pi * θ ≤ 1/2 := by
        have hm : 2/Real.pi * θ ≤ 2/Real.pi * (Real.pi/4) :=
          mul_le_mul_of_nonneg_left hcase.le (by positivity)
        have he : 2/Real.pi * (Real.pi/4) = 1/2 := by field_simp; ring
        linarith
      linarith
    have hJ : |J| ≤ K * (1 - Real.cos θ ^ 3) / 3 := by
      have hb := interval_bound hbd hint (a := 0) (b := θ) le_rfl hθ2.le hθ0.le
      have hb2 : K * ∫ t in (0 : ℝ)..θ, Work.Elliptic.sinCos2 t
          = K * (1 - Real.cos θ ^ 3) / 3 := by
        rw [integral_sinCos2 0 θ, Real.cos_zero]
        ring
      rw [hb2] at hb
      rw [hJdef]
      exact hb
    have hres : |J| ≤ K * Real.sin θ ^ 2 := by
      have h1 : (1 - Real.cos θ ^ 3)/3 ≤ Real.sin θ ^ 2 := by
        have hfac : 1 - Real.cos θ ^ 3
            = (1 - Real.cos θ) * (1 + Real.cos θ + Real.cos θ ^ 2) := by ring
        have hle : 1 + Real.cos θ + Real.cos θ ^ 2 ≤ 3 * (1 + Real.cos θ) := by nlinarith
        have hnn : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
        have h3 : 1 - Real.cos θ ^ 3 ≤ 3 * Real.sin θ ^ 2 := by
          calc 1 - Real.cos θ ^ 3
              = (1 - Real.cos θ) * (1 + Real.cos θ + Real.cos θ ^ 2) := hfac
            _ ≤ (1 - Real.cos θ) * (3 * (1 + Real.cos θ)) :=
                mul_le_mul_of_nonneg_left hle hnn
            _ = 3 * Real.sin θ ^ 2 := by rw [hsinsq]; ring
        linarith
      calc |J| ≤ K * (1 - Real.cos θ ^ 3) / 3 := hJ
        _ = K * ((1 - Real.cos θ ^ 3)/3) := by ring
        _ ≤ K * Real.sin θ ^ 2 := mul_le_mul_of_nonneg_left h1 hK
    have step : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * |J|
        ≤ (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.sin θ ^ 2) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    have hfin : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.sin θ ^ 2) ≤ 4*K := by
      have hx : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.sin θ ^ 2)
          = K/(2 * Real.cos θ ^ 3) := by
        field_simp
        try ring
      rw [hx, show (4 : ℝ)*K = K*4 by ring]
      apply mul_le_mul_of_nonneg_left _ hK
      rw [inv_le_iff_one_le_mul₀ (by positivity : (0 : ℝ) < 2 * Real.cos θ ^ 3)]
      have hc3 : (1 : ℝ)/8 ≤ Real.cos θ ^ 3 := by
        have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 : ℝ)/2) hc12 3
        norm_num at hh
        exact hh
      linarith
    linarith
  · -- large angles: the moment condition gives `|N| ≤ K cos³θ/3`
    have hs12 : (1 : ℝ)/2 ≤ Real.sin θ := by
      have h := Real.mul_le_sin hθ0.le hθ2.le
      have h2 : (1 : ℝ)/2 ≤ 2/Real.pi * θ := by
        have hm : 2/Real.pi * (Real.pi/4) ≤ 2/Real.pi * θ :=
          mul_le_mul_of_nonneg_left hcase (by positivity)
        have he : 2/Real.pi * (Real.pi/4) = 1/2 := by field_simp; ring
        linarith
      linarith
    have hJ : |J| ≤ K * Real.cos θ ^ 3 / 3 := by
      have hmom0 : ∫ t in (0 : ℝ)..(π/2), h t * Work.Elliptic.sinCos2 t = 0 := moment_zero hmom
      have hI1 : IntervalIntegrable (fun t => h t * Work.Elliptic.sinCos2 t) volume 0 θ :=
        intervalIntegrable_moment hint le_rfl hθ2.le hθ0.le
      have hI2 : IntervalIntegrable (fun t => h t * Work.Elliptic.sinCos2 t) volume θ (π/2) :=
        intervalIntegrable_moment hint hθ0.le le_rfl hθ2.le
      have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
      have hb := interval_bound hbd hint (a := θ) (b := π/2) hθ0.le le_rfl hθ2.le
      have hb2 : K * ∫ t in θ..(π/2), Work.Elliptic.sinCos2 t
          = K * Real.cos θ ^ 3 / 3 := by
        rw [integral_sinCos2 θ (π/2), Real.cos_pi_div_two]
        ring
      rw [hb2] at hb
      rw [hJdef]
      have heq : ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t
          = -(∫ t in θ..(π/2), h t * Work.Elliptic.sinCos2 t) := by linarith
      rw [heq, abs_neg]
      exact hb
    have step : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * |J|
        ≤ (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.cos θ ^ 3 / 3) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    have hfin : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.cos θ ^ 3 / 3)
        ≤ 4*K := by
      have hx : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.cos θ ^ 3 / 3)
          = K/(6 * Real.sin θ ^ 2) := by
        field_simp
        ring
      rw [hx, show (4 : ℝ)*K = K*4 by ring]
      apply mul_le_mul_of_nonneg_left _ hK
      rw [inv_le_iff_one_le_mul₀ (by positivity : (0 : ℝ) < 6 * Real.sin θ ^ 2)]
      have hs2 : (1 : ℝ)/4 ≤ Real.sin θ ^ 2 := by
        have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 : ℝ)/2) hs12 2
        norm_num at hh
        exact hh
      linarith
    linarith

end Work.FTS.PhiStar.LinvFlatAux
