import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.PhiStar.LinvFlat

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The uniform bound `|Linv h| ≤ 4K` -/

lemma LI_lc_sinCos2_nonneg {t : ℝ} (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Work.Elliptic.sinCos2 t := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le
    (by linarith [ht.2, Real.pi_pos])) (sq_nonneg _)

lemma LI_lc_integrand_eq (h : ℝ → ℝ) (t : ℝ) :
    Real.sin t ^ 2 * Real.cos t ^ 3 * h t / Work.Construction.s2 t
      = (1 / 2) * (h t * Work.Elliptic.sinCos2 t) := by
  rw [Work.Elliptic.sinCos2, Work.Construction.s2_eq, Real.sin_two_mul]
  by_cases hs : Real.sin t = 0
  · simp [hs]
  · by_cases hc : Real.cos t = 0
    · simp [hc]
    · field_simp

lemma LI_lc_Linv_eq (h : ℝ → ℝ) (θ : ℝ) :
    Work.FTS.PhiStar.Linv h θ
      = -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ *
          ((1 / 2) * ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t)) := by
  have hint : (∫ θ' in (0 : ℝ)..θ,
        Real.sin θ' ^ 2 * Real.cos θ' ^ 3 * h θ' / Work.Construction.s2 θ')
      = (1 / 2) * ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t := by
    rw [intervalIntegral.integral_congr (fun t _ => LI_lc_integrand_eq h t),
        intervalIntegral.integral_const_mul]
  simp only [Work.FTS.PhiStar.Linv]
  rw [hint]

lemma LI_lc_intervalIntegrable_moment {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π / 2) (hab : a ≤ b) :
    IntervalIntegrable (fun t => h t * Work.Elliptic.sinCos2 t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine hint.mono_set ?_
  intro t ht
  exact ⟨le_trans ha ht.1.le, le_trans ht.2 hb⟩

lemma LI_lc_interval_bound {h : ℝ → ℝ} {K : ℝ}
    (hbd : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |h θ| ≤ K)
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π / 2) (hab : a ≤ b) :
    |∫ t in a..b, h t * Work.Elliptic.sinCos2 t|
      ≤ K * ∫ t in a..b, Work.Elliptic.sinCos2 t := by
  have hf : IntervalIntegrable (fun t => |h t * Work.Elliptic.sinCos2 t|) volume a b :=
    (LI_lc_intervalIntegrable_moment hint ha hb hab).abs
  have hg : IntervalIntegrable (fun t => K * Work.Elliptic.sinCos2 t) volume a b :=
    (continuous_const.mul (by unfold Work.Elliptic.sinCos2; fun_prop)).intervalIntegrable a b
  have hpoint : ∀ x ∈ Set.Ioo a b,
      |h x * Work.Elliptic.sinCos2 x| ≤ K * Work.Elliptic.sinCos2 x := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
    have hnn : 0 ≤ Work.Elliptic.sinCos2 x := LI_lc_sinCos2_nonneg hx'
    rw [abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right (hbd x hx') hnn
  calc |∫ t in a..b, h t * Work.Elliptic.sinCos2 t|
      ≤ ∫ t in a..b, |h t * Work.Elliptic.sinCos2 t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, K * Work.Elliptic.sinCos2 t :=
        intervalIntegral.integral_mono_on_of_le_Ioo hab hf hg hpoint
    _ = K * ∫ t in a..b, Work.Elliptic.sinCos2 t := intervalIntegral.integral_const_mul K _

lemma LI_lc_hasDerivAt_cos3 (y : ℝ) :
    HasDerivAt (fun x => -(Real.cos x ^ 3) / 3) (Real.sin y * Real.cos y ^ 2) y := by
  have h1 := (Real.hasDerivAt_cos y).pow 3
  have h2 := h1.const_mul (-(1 / 3) : ℝ)
  convert h2 using 1
  · funext x; simp only [Pi.pow_apply]; ring
  · ring_nf

lemma LI_lc_integral_sinCos2 (a b : ℝ) :
    ∫ t in a..b, Work.Elliptic.sinCos2 t = (Real.cos a ^ 3 - Real.cos b ^ 3) / 3 := by
  have hcont : IntervalIntegrable (fun t => Real.sin t * Real.cos t ^ 2) volume a b :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => -(Real.cos x ^ 3) / 3)
    (f' := fun x => Real.sin x * Real.cos x ^ 2)
    (fun x _ => LI_lc_hasDerivAt_cos3 x) hcont
  change ∫ t in a..b, Real.sin t * Real.cos t ^ 2 = _
  rw [h]
  ring

lemma LI_lc_moment_zero {h : ℝ → ℝ}
    (hmom : (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∫ t in (0 : ℝ)..(π / 2), h t * Work.Elliptic.sinCos2 t = 0 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)] at hmom
  exact hmom

/-- The uniform base bound: `|Linv h θ| ≤ 4 K`, with a constant independent of `h` and `K`. -/
lemma LI_lc_abs_le (h : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hbd : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |h θ| ≤ K)
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |Work.FTS.PhiStar.Linv h θ| ≤ 4 * K := by
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ2 : θ < π / 2 := hθ.2
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcospos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩
  have hden : 0 < Real.sin θ ^ 2 * Real.cos θ ^ 3 :=
    mul_pos (pow_pos hsinpos 2) (pow_pos hcospos 3)
  rw [LI_lc_Linv_eq h θ]
  set J : ℝ := ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t with hJdef
  have habs : |-( (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * ((1 / 2) * J))|
      = (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * |J| := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hden),
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  rw [habs]
  by_cases hcase : θ ≤ π / 4
  · -- small angles
    have hJ : |J| ≤ K * (1 - Real.cos θ ^ 3) / 3 := by
      have hb := LI_lc_interval_bound hbd hint (a := 0) (b := θ) le_rfl hθ2.le hθ0.le
      have hb2 : K * ∫ t in (0 : ℝ)..θ, Work.Elliptic.sinCos2 t
          = K * (1 - Real.cos θ ^ 3) / 3 := by
        rw [LI_lc_integral_sinCos2 0 θ, Real.cos_zero]
        ring
      rw [hb2] at hb
      rw [hJdef]
      exact hb
    have hres : |J| ≤ K * Real.sin θ ^ 2 := by
      have h1 : (1 - Real.cos θ ^ 3) / 3 ≤ Real.sin θ ^ 2 := by
        have hs2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq θ
        have hfac : 3 * Real.sin θ ^ 2 - (1 - Real.cos θ ^ 3)
            = (1 - Real.cos θ) * (2 + 2 * Real.cos θ - Real.cos θ ^ 2) := by
          rw [hs2]; ring
        have hn1 : (0 : ℝ) ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
        have hn2 : (0 : ℝ) ≤ 2 + 2 * Real.cos θ - Real.cos θ ^ 2 := by
          nlinarith [hcospos, Real.cos_le_one θ]
        have hnn := mul_nonneg hn1 hn2
        linarith
      calc |J| ≤ K * (1 - Real.cos θ ^ 3) / 3 := hJ
        _ = K * ((1 - Real.cos θ ^ 3) / 3) := by ring
        _ ≤ K * Real.sin θ ^ 2 := mul_le_mul_of_nonneg_left h1 hK
    have hc12 : (1 : ℝ) / 2 ≤ Real.cos θ := by
      have h1 : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos (x := θ)
      have hpi : Real.pi ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
      have h2 : θ ^ 2 / 2 ≤ (1 : ℝ) / 2 := by
        have h3 : θ ^ 2 ≤ (Real.pi / 4) ^ 2 := by nlinarith [hθ0.le, hcase]
        nlinarith [Real.pi_pos]
      linarith
    have hfin : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.sin θ ^ 2) ≤ 4 * K := by
      have hx : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.sin θ ^ 2)
          = K / (2 * Real.cos θ ^ 3) := by
        field_simp [hsinpos.ne', hcospos.ne']
      rw [hx]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.cos θ ^ 3)]
      have hc3 : (1 : ℝ) / 8 ≤ Real.cos θ ^ 3 := by
        have hpp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2) hc12 3
        norm_num at hpp
        exact hpp
      nlinarith [hK, hc3]
    have step : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * |J|
        ≤ (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.sin θ ^ 2) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    linarith [step, hfin]
  · -- large angles
    have hcase' : π / 4 < θ := not_le.mp hcase
    have hJ : |J| ≤ K * Real.cos θ ^ 3 / 3 := by
      have hmom0 : ∫ t in (0 : ℝ)..(π / 2), h t * Work.Elliptic.sinCos2 t = 0 :=
        LI_lc_moment_zero hmom
      have hI1 : IntervalIntegrable (fun t => h t * Work.Elliptic.sinCos2 t) volume 0 θ :=
        LI_lc_intervalIntegrable_moment hint le_rfl hθ2.le hθ0.le
      have hI2 : IntervalIntegrable (fun t => h t * Work.Elliptic.sinCos2 t) volume θ (π / 2) :=
        LI_lc_intervalIntegrable_moment hint hθ0.le le_rfl hθ2.le
      have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
      have hb := LI_lc_interval_bound hbd hint (a := θ) (b := π / 2) hθ0.le le_rfl hθ2.le
      have hb2 : K * ∫ t in θ..(π / 2), Work.Elliptic.sinCos2 t
          = K * Real.cos θ ^ 3 / 3 := by
        rw [LI_lc_integral_sinCos2 θ (π / 2), Real.cos_pi_div_two]
        ring
      rw [hb2] at hb
      rw [hJdef]
      have heq : ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t
          = -(∫ t in θ..(π / 2), h t * Work.Elliptic.sinCos2 t) := by linarith
      rw [heq, abs_neg]
      exact hb
    have hsin12 : (1 : ℝ) / 2 ≤ Real.sin θ := by
      have h1 : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ0.le hθ2.le
      have h2 : (1 : ℝ) / 2 ≤ 2 / Real.pi * θ := by
        rw [show (2 : ℝ) / Real.pi * θ = 2 * θ / Real.pi from by ring,
            le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi)]
        nlinarith [hcase']
      linarith
    have hfin : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.cos θ ^ 3 / 3)
        ≤ 4 * K := by
      have hx : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.cos θ ^ 3 / 3)
          = K / (6 * Real.sin θ ^ 2) := by
        field_simp [hsinpos.ne', hcospos.ne']; ring
      rw [hx]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 6 * Real.sin θ ^ 2)]
      have hs2 : (1 : ℝ) / 4 ≤ Real.sin θ ^ 2 := by
        have hpp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2) hsin12 2
        norm_num at hpp
        exact hpp
      nlinarith [hK, hs2]
    have step : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * |J|
        ≤ (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.cos θ ^ 3 / 3) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    linarith [step, hfin]


end Work.FTS.PhiStar.LinvFlat
