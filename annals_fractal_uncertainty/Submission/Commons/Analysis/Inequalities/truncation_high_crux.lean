import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Commons.Analysis.LogBounds.x_div_one_add_le_log
import Submission.Commons.Analysis.LogBounds.two_mul_sub_div_add_le_log
import Submission.Commons.Analysis.LogBounds.log_seventeen_div_four_le
import Submission.Commons.Analysis.LogBounds.log_two_ge_half
import Submission.Commons.Analysis.Inequalities.three_halves_mul_self_sqrt_le

open Set

namespace Commons.Analysis.Inequalities

/-- For `x ≥ 0`, `2x/(2+x) ≤ log (2+x)`. -/
private theorem two_mul_div_add_two_le_log (x : ℝ) (hx : 0 ≤ x) :
    2 * x / (2 + x) ≤ Real.log (2 + x) := by
  have hy : (1 : ℝ) ≤ 2 + x := by linarith
  have hmain := Commons.Analysis.LogBounds.two_mul_sub_div_add_le_log (2 + x) hy
  have harg : 2 * ((2 + x) - 1) / ((2 + x) + 1) = 2 * (1 + x) / (3 + x) := by ring
  rw [harg] at hmain
  have h2 : 0 ≤ 2 * (1 + x) / (3 + x) - 2 * x / (2 + x) := by
    have e : 2 * (1 + x) / (3 + x) - 2 * x / (2 + x) = 4 / ((3 + x) * (2 + x)) := by
      field_simp
      ring
    rw [e]; positivity
  linarith

/-- For `x ≥ 9/4`, `log (2+x) ≤ sqrt x`. -/
private theorem log_two_add_le_sqrt (x : ℝ) (hx : 9 / 4 ≤ x) :
    Real.log (2 + x) ≤ Real.sqrt x := by
  have hmono : MonotoneOn (fun y => Real.sqrt y - Real.log (2 + y)) (Ici (9 / 4 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · apply ContinuousOn.sub
      · exact Real.continuous_sqrt.continuousOn
      · apply ContinuousOn.log (f := fun y => 2 + y)
        · fun_prop
        · intro y hy; have h : (9 / 4 : ℝ) ≤ y := hy; linarith
    · apply DifferentiableOn.sub
      · apply DifferentiableOn.sqrt differentiableOn_id
        intro y hy
        rw [interior_Ici] at hy
        have hy' : (9 / 4 : ℝ) < y := Set.mem_Ioi.mp hy
        exact ne_of_gt (by linarith : (0 : ℝ) < y)
      · apply DifferentiableOn.log (f := fun y => 2 + y)
        · fun_prop
        · intro y hy
          rw [interior_Ici] at hy
          have hy' : (9 / 4 : ℝ) < y := Set.mem_Ioi.mp hy
          exact ne_of_gt (by linarith : (0 : ℝ) < 2 + y)
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : (9 / 4 : ℝ) < y := Set.mem_Ioi.mp hy
      have hypos : 0 < y := by linarith
      have hderiv : deriv (fun y => Real.sqrt y - Real.log (2 + y)) y
          = 1 / (2 * Real.sqrt y) - 1 / (2 + y) := by
        have h1 : HasDerivAt (fun y => Real.sqrt y) (1 / (2 * Real.sqrt y)) y :=
          Real.hasDerivAt_sqrt (ne_of_gt hypos)
        have h2 : HasDerivAt (fun y => Real.log (2 + y)) (1 / (2 + y)) y := by
          have h0 := (hasDerivAt_id y).const_add (2 : ℝ)
          exact h0.log (by linarith : (2 + y) ≠ 0)
        have h3 : HasDerivAt (fun y => Real.sqrt y - Real.log (2 + y))
            (1 / (2 * Real.sqrt y) - 1 / (2 + y)) y := h1.sub h2
        exact h3.deriv
      rw [hderiv]
      have hle : 2 * Real.sqrt y ≤ 2 + y := by
        nlinarith [sq_nonneg (Real.sqrt y - 1), Real.sq_sqrt (le_of_lt hypos)]
      have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * Real.sqrt y) hle
      linarith
  have hmem9 : (9 / 4 : ℝ) ∈ Ici (9 / 4 : ℝ) := Set.mem_Ici.mpr le_rfl
  have hmemx : x ∈ Ici (9 / 4 : ℝ) := hx
  have hmon := hmono hmem9 hmemx hx
  beta_reduce at hmon
  have h17 := Commons.Analysis.LogBounds.log_seventeen_div_four_le
  have hval : Real.sqrt ((9 : ℝ) / 4) = 3 / 2 := by
    have hsq : ((9 : ℝ) / 4) = (3 / 2) ^ 2 := by norm_num
    rw [hsq, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hden : (2 : ℝ) + 9 / 4 = 17 / 4 := by norm_num
  rw [hval, hden] at hmon
  linarith [hmon, h17]

/-- For `x ≥ 0`, `x * sqrt x * log (2+x) ≤ 1 + x^2`. -/
private theorem self_sqrt_mul_log_le (x : ℝ) (hx : 0 ≤ x) :
    x * Real.sqrt x * Real.log (2 + x) ≤ 1 + x ^ 2 := by
  have hxx : 0 ≤ x * Real.sqrt x := by positivity
  rcases le_or_gt x (9 / 4) with hxl | hxg
  · have hlog17 : Real.log (2 + x) ≤ Real.log (17 / 4) := by
      apply Real.log_le_log (by linarith : (0 : ℝ) < 2 + x)
      linarith
    have hlog32 : Real.log (2 + x) ≤ 3 / 2 :=
      le_trans hlog17 Commons.Analysis.LogBounds.log_seventeen_div_four_le
    have h1 : x * Real.sqrt x * Real.log (2 + x) ≤ x * Real.sqrt x * (3 / 2) :=
      mul_le_mul_of_nonneg_left hlog32 hxx
    have h2 : x * Real.sqrt x * (3 / 2) = (3 / 2) * (x * Real.sqrt x) := by ring
    have h3 : (3 / 2) * (x * Real.sqrt x) ≤ 1 + x ^ 2 :=
      Commons.Analysis.Inequalities.three_halves_mul_self_sqrt_le x hx
    linarith [h1, h2, h3]
  · have hlog : Real.log (2 + x) ≤ Real.sqrt x := log_two_add_le_sqrt x (le_of_lt hxg)
    have h1 : x * Real.sqrt x * Real.log (2 + x) ≤ x * Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hlog hxx
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
    have h2 : x * Real.sqrt x * Real.sqrt x = x ^ 2 := by
      rw [mul_assoc, hsq]; ring
    linarith [h1, h2]

/-- For `x ≥ 0` and `0 < α ≤ 1`: `(log (2+x))^α / 2 ≤ log (2+x) - α x/(2+x)`. -/
private theorem log_rpow_half_le (x : ℝ) (hx : 0 ≤ x) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (Real.log (2 + x)) ^ α / 2 ≤ Real.log (2 + x) - α * (x / (2 + x)) := by
  set L := Real.log (2 + x) with hLdef
  set B := x / (2 + x) with hBdef
  have hLpos : 0 < L := by
    rw [hLdef]; apply Real.log_pos; linarith
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hLB : Real.log 2 ≤ L - B := by
    have h2x : (2 : ℝ) + x = 2 * (1 + x / 2) := by ring
    have hne : (1 + x / 2) ≠ 0 := by positivity
    have hsplit : Real.log (2 + x) = Real.log 2 + Real.log (1 + x / 2) := by
      rw [h2x, Real.log_mul (by norm_num) hne]
    have hhalf : 0 ≤ x / 2 := by linarith
    have hlogineq := Commons.Analysis.LogBounds.x_div_one_add_le_log (x / 2) hhalf
    have hdiv : (x / 2) / (1 + x / 2) = B := by
      rw [hBdef]
      have h1 : (0 : ℝ) < 1 + x / 2 := by linarith
      have h2 : (0 : ℝ) < 2 + x := by linarith
      field_simp
    rw [hdiv] at hlogineq
    rw [hLdef, hsplit]
    linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := Commons.Analysis.LogBounds.log_two_ge_half
  by_cases hL1 : L ≤ 1
  · have hrpow : L ^ α ≤ 1 := Real.rpow_le_one (le_of_lt hLpos) hL1 (le_of_lt hα)
    have hBle : α * B ≤ B := by nlinarith [hα1, hBnn]
    linarith
  · have hL1' : 1 ≤ L := le_of_lt (lt_of_not_ge hL1)
    have hrpow : L ^ α ≤ L := by
      have := Real.rpow_le_rpow_of_exponent_le hL1' hα1
      simpa using this
    have hD' : 2 * (x / (2 + x)) ≤ Real.log (2 + x) := by
      rw [show 2 * (x / (2 + x)) = 2 * x / (2 + x) by ring]
      exact two_mul_div_add_two_le_log x hx
    have h2B : 2 * B ≤ L := by rw [hLdef, hBdef]; exact hD'
    have hBle : α * B ≤ B := by nlinarith [hα1, hBnn]
    nlinarith [hrpow, h2B, hBle, hLpos]

/-- Crux pointwise bound. -/
private theorem self_sqrt_mul_log_rpow_le (x : ℝ) (hx : 0 ≤ x) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) :
    x * Real.sqrt x * (Real.log (2 + x)) ^ (α + 1)
      ≤ 2 * (1 + x ^ 2) * (Real.log (2 + x) - α * (x / (2 + x))) := by
  have hLpos : 0 < Real.log (2 + x) := by apply Real.log_pos; linarith
  have hEp := self_sqrt_mul_log_le x hx
  have hIp := log_rpow_half_le x hx α hα hα1
  have hLpownn : 0 ≤ (Real.log (2 + x)) ^ α := Real.rpow_nonneg (le_of_lt hLpos) α
  have hstep1 : x * Real.sqrt x * Real.log (2 + x) * (Real.log (2 + x)) ^ α
      ≤ (1 + x ^ 2) * (Real.log (2 + x)) ^ α :=
    mul_le_mul_of_nonneg_right hEp hLpownn
  have hstep2 : (Real.log (2 + x)) ^ α ≤ 2 * (Real.log (2 + x) - α * (x / (2 + x))) := by
    linarith
  have hstep3 : (1 + x ^ 2) * (Real.log (2 + x)) ^ α
      ≤ (1 + x ^ 2) * (2 * (Real.log (2 + x) - α * (x / (2 + x)))) :=
    mul_le_mul_of_nonneg_left hstep2 (by positivity)
  have hpow : (Real.log (2 + x)) ^ (α + 1) = (Real.log (2 + x)) ^ α * Real.log (2 + x) := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
  calc x * Real.sqrt x * (Real.log (2 + x)) ^ (α + 1)
      = x * Real.sqrt x * Real.log (2 + x) * (Real.log (2 + x)) ^ α := by rw [hpow]; ring
    _ ≤ (1 + x ^ 2) * (Real.log (2 + x)) ^ α := hstep1
    _ ≤ (1 + x ^ 2) * (2 * (Real.log (2 + x) - α * (x / (2 + x)))) := hstep3
    _ = 2 * (1 + x ^ 2) * (Real.log (2 + x) - α * (x / (2 + x))) := by ring

/-- Derivative of `x ↦ x / (log (2+x))^α` for `x > 0`. -/
private theorem deriv_x_div_log_pow (α x : ℝ) (hx : 0 < x) :
    deriv (fun y : ℝ => y / (Real.log (2 + y)) ^ α) x
      = (Real.log (2 + x) - α * (x / (2 + x))) / (Real.log (2 + x)) ^ (α + 1) := by
  have hLpos : 0 < Real.log (2 + x) := by apply Real.log_pos; linarith
  have hApos : 0 < (Real.log (2 + x)) ^ α := Real.rpow_pos_of_pos hLpos α
  have hL : HasDerivAt (fun y : ℝ => Real.log (2 + y)) (1 / (2 + x)) x := by
    have h0 := (hasDerivAt_id x).const_add (2 : ℝ)
    exact h0.log (by linarith : (2 + x) ≠ 0)
  have hpow : HasDerivAt (fun y : ℝ => (Real.log (2 + y)) ^ α)
      ((1 / (2 + x)) * α * (Real.log (2 + x)) ^ (α - 1)) x :=
    hL.rpow_const (Or.inl (ne_of_gt hLpos))
  have hdiv : HasDerivAt (fun y : ℝ => y / (Real.log (2 + y)) ^ α)
      ((1 * (Real.log (2 + x)) ^ α
          - x * ((1 / (2 + x)) * α * (Real.log (2 + x)) ^ (α - 1)))
        / ((Real.log (2 + x)) ^ α) ^ 2) x :=
    (hasDerivAt_id x).div hpow (ne_of_gt hApos)
  rw [hdiv.deriv]
  have hsub : (Real.log (2 + x)) ^ (α - 1) = (Real.log (2 + x)) ^ α / Real.log (2 + x) := by
    rw [show α - 1 = α + (-1) by ring, Real.rpow_add hLpos, Real.rpow_neg (le_of_lt hLpos),
      Real.rpow_one]
    ring
  have hadd : (Real.log (2 + x)) ^ (α + 1) = (Real.log (2 + x)) ^ α * Real.log (2 + x) := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
  rw [hsub, hadd]
  field_simp

/-- Derivative of `x ↦ log (1 + x^2)`. -/
private theorem deriv_log_one_add_sq (x : ℝ) :
    deriv (fun y : ℝ => Real.log (1 + y ^ 2)) x = 2 * x / (1 + x ^ 2) := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := h1.const_add 1
  have h3 : HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2)) ((2 * x) / (1 + x ^ 2)) x :=
    h2.log (by positivity)
  exact h3.deriv

theorem truncation_high_crux {c₃ α d R t : ℝ}
    (hc₃ : 0 < c₃) (hd : 0 ≤ d) (hα : 0 < α) (hα1 : α ≤ 1)
    (hR : (2 * d / c₃) ^ 2 ≤ R) (hRt : R ≤ t) :
    (d / 2) * Real.log ((1 + t ^ 2) / (1 + R ^ 2))
      ≤ c₃ * (t / (Real.log (2 + t)) ^ α - R / (Real.log (2 + R)) ^ α) := by
  have hR0 : 0 ≤ R := le_trans (sq_nonneg _) hR
  -- d ≤ c₃ * sqrt R / 2
  have hdle : d ≤ c₃ * Real.sqrt R / 2 := by
    have ha : 0 ≤ 2 * d / c₃ := by positivity
    have hs : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
    have hsq : (2 * d / c₃) ^ 2 ≤ (Real.sqrt R) ^ 2 := by rw [Real.sq_sqrt hR0]; exact hR
    have hle : 2 * d / c₃ ≤ Real.sqrt R := by
      have h := (sq_le_sq.mp hsq)
      rwa [abs_of_nonneg ha, abs_of_nonneg hs] at h
    have h2 : 2 * d ≤ Real.sqrt R * c₃ := (div_le_iff₀ hc₃).mp hle
    linarith
  have hmonoF : MonotoneOn
      (fun x => c₃ * (x / (Real.log (2 + x)) ^ α) - (d / 2) * Real.log (1 + x ^ 2))
      (Set.Icc R t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc R t)
    · have hcontA : ContinuousOn (fun x => x / (Real.log (2 + x)) ^ α) (Set.Icc R t) := by
        apply ContinuousOn.div continuousOn_id
        · apply ContinuousOn.rpow_const
          · apply ContinuousOn.log (f := fun x => 2 + x)
            · fun_prop
            · intro x hx; have hx0 : 0 ≤ x := le_trans hR0 hx.1; linarith
          · intro x hx; exact Or.inr (le_of_lt hα)
        · intro x hx
          have hx0 : 0 ≤ x := le_trans hR0 hx.1
          exact ne_of_gt (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) α)
      have hcontB : ContinuousOn (fun x => Real.log (1 + x ^ 2)) (Set.Icc R t) := by
        apply ContinuousOn.log (f := fun x => 1 + x ^ 2)
        · fun_prop
        · intro x hx; positivity
      exact (hcontA.const_mul c₃).sub (hcontB.const_mul (d / 2))
    · rw [interior_Icc]
      have hdiffA : DifferentiableOn ℝ (fun x => x / (Real.log (2 + x)) ^ α) (Set.Ioo R t) := by
        apply DifferentiableOn.div differentiableOn_id
        · apply DifferentiableOn.rpow_const
          · apply DifferentiableOn.log (f := fun x => 2 + x)
            · exact differentiableOn_id.const_add 2
            · intro x hx
              have hx0 : 0 ≤ x := le_trans hR0 (le_of_lt hx.1); linarith
          · intro x hx
            have hx0 : 0 ≤ x := le_trans hR0 (le_of_lt hx.1)
            exact Or.inl (ne_of_gt (Real.log_pos (by linarith)))
        · intro x hx
          have hx0 : 0 ≤ x := le_trans hR0 (le_of_lt hx.1)
          exact ne_of_gt (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) α)
      have hdiffB : DifferentiableOn ℝ (fun x => Real.log (1 + x ^ 2)) (Set.Ioo R t) := by
        apply DifferentiableOn.log (f := fun x => 1 + x ^ 2)
        · exact (differentiableOn_id.pow 2).const_add 1
        · intro x hx; positivity
      exact (hdiffA.const_mul c₃).sub (hdiffB.const_mul (d / 2))
    · intro x hx
      rw [interior_Icc] at hx
      have hxpos : 0 < x := lt_of_le_of_lt hR0 hx.1
      have hLpos : 0 < Real.log (2 + x) := Real.log_pos (by linarith)
      have hg1 : DifferentiableAt ℝ (fun y => y / (Real.log (2 + y)) ^ α) x := by
        apply DifferentiableAt.div differentiableAt_id
        · apply DifferentiableAt.rpow_const
          · apply DifferentiableAt.log (f := fun y => 2 + y)
            · fun_prop
            · linarith
          · exact Or.inl (ne_of_gt hLpos)
        · exact ne_of_gt (Real.rpow_pos_of_pos hLpos α)
      have hg2 : DifferentiableAt ℝ (fun y => Real.log (1 + y ^ 2)) x := by
        apply DifferentiableAt.log (f := fun y => 1 + y ^ 2)
        · fun_prop
        · positivity
      have hderF : deriv (fun y => c₃ * (y / (Real.log (2 + y)) ^ α)
            - (d / 2) * Real.log (1 + y ^ 2)) x
          = c₃ * ((Real.log (2 + x) - α * (x / (2 + x))) / (Real.log (2 + x)) ^ (α + 1))
            - (d / 2) * (2 * x / (1 + x ^ 2)) := by
        have hd1 : DifferentiableAt ℝ (fun y => c₃ * (y / (Real.log (2 + y)) ^ α)) x :=
          hg1.const_mul c₃
        have hd2 : DifferentiableAt ℝ (fun y => (d / 2) * Real.log (1 + y ^ 2)) x :=
          hg2.const_mul (d / 2)
        rw [show (fun y => c₃ * (y / (Real.log (2 + y)) ^ α) - (d / 2) * Real.log (1 + y ^ 2))
              = (fun y => c₃ * (y / (Real.log (2 + y)) ^ α))
                - (fun y => (d / 2) * Real.log (1 + y ^ 2)) from rfl]
        rw [deriv_sub hd1 hd2, deriv_const_mul c₃ hg1, deriv_const_mul (d / 2) hg2,
          deriv_x_div_log_pow α x hxpos, deriv_log_one_add_sq x]
      rw [hderF]
      have hdlex : d ≤ c₃ * Real.sqrt x / 2 := by
        have : Real.sqrt R ≤ Real.sqrt x := Real.sqrt_le_sqrt (le_of_lt hx.1)
        nlinarith [hdle, this, hc₃]
      have hA := self_sqrt_mul_log_rpow_le x (le_of_lt hxpos) α hα hα1
      have hBpos : 0 < 2 * (1 + x ^ 2) := by positivity
      have hDpos : 0 < (Real.log (2 + x)) ^ (α + 1) := Real.rpow_pos_of_pos hLpos (α + 1)
      have hAx : x * Real.sqrt x / (2 * (1 + x ^ 2))
          ≤ (Real.log (2 + x) - α * (x / (2 + x))) / (Real.log (2 + x)) ^ (α + 1) := by
        rw [div_le_div_iff₀ hBpos hDpos]
        linarith [hA]
      have hstep1 : (d / 2) * (2 * x / (1 + x ^ 2)) ≤ c₃ * (x * Real.sqrt x / (2 * (1 + x ^ 2))) := by
        have he : (d / 2) * (2 * x / (1 + x ^ 2)) = d * (x / (1 + x ^ 2)) := by ring
        rw [he]
        have hxnn : 0 ≤ x / (1 + x ^ 2) := by positivity
        have hm := mul_le_mul_of_nonneg_right hdlex hxnn
        have h2 : (c₃ * Real.sqrt x / 2) * (x / (1 + x ^ 2))
            = c₃ * (x * Real.sqrt x / (2 * (1 + x ^ 2))) := by
          field_simp
        linarith [hm, h2]
      have hstep2 : c₃ * (x * Real.sqrt x / (2 * (1 + x ^ 2)))
          ≤ c₃ * ((Real.log (2 + x) - α * (x / (2 + x))) / (Real.log (2 + x)) ^ (α + 1)) :=
        mul_le_mul_of_nonneg_left hAx (le_of_lt hc₃)
      linarith [hstep1, hstep2]
  have hmon := hmonoF ⟨le_rfl, hRt⟩ ⟨hRt, le_rfl⟩ hRt
  beta_reduce at hmon
  have hlog : Real.log ((1 + t ^ 2) / (1 + R ^ 2))
      = Real.log (1 + t ^ 2) - Real.log (1 + R ^ 2) :=
    Real.log_div (by positivity) (by positivity)
  rw [hlog]
  linarith [hmon]

end Commons.Analysis.Inequalities