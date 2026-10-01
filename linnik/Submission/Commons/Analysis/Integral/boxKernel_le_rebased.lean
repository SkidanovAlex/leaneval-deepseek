import Mathlib
import Submission.Commons.Analysis.Integral.arsinh_antideriv_two_sub
import Submission.Commons.Analysis.Real.arsinh_le_log_two_mul_add_inv
import Submission.Commons.Analysis.Real.arsinh_le_self_of_nonneg
import Submission.Commons.Analysis.Real.sqrt_one_sub_le_cubic_sum
import Submission.Commons.Analysis.Real.one_sub_div_sqrt_sq_ge
import Submission.Commons.Analysis.Integral.boxMaj_le_target_kernel_ge_sixth
import Submission.Commons.Analysis.Integral.boxWindow_middle
import Submission.Commons.Analysis.Integral.boxWindow_left_half

open MeasureTheory

namespace Commons.Analysis.Integral

/-! ### Elementary pieces for `boxKernel_le_rebased` -/

/-- The "decay correction": for `0 < b`, `0 ≤ t ≤ τ`, `1 - b/√(b²+t²) ≥ t²/(2(b²+τ²))`. -/
lemma one_sub_div_sqrt_sq_ge' {b τ t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) (htτ : t ≤ τ) :
    1 - b/Real.sqrt (b^2+t^2) ≥ t^2/(2*(b^2+τ^2)) :=
  Commons.Analysis.Real.one_sub_div_sqrt_sq_ge hb ht htτ

/-- The piecewise elementary majorant for `b·arsinh(β/t)/√(b²+t²)`, valid for `0 < β`, `0 < t`. -/
noncomputable def boxMajTerm (b β t : ℝ) : ℝ :=
  if t ≤ β then Real.log ((4*β^2+t^2)/(2*β*t)) * (1 - t^2/(2*(b^2+β^2)))
  else b*β/(t*Real.sqrt (b^2+t^2))

/-- The full majorant for the inner `x`-integral of the box kernel. -/
noncomputable def boxMaj (a b : ℝ) (s : ℝ) : ℝ :=
  boxMajTerm b b |s| + boxMajTerm b a |s|

/-- The Taylor lower bound for the `√`-correction `Q = 1 - √(a²+t²)/√(b²+t²)`. -/
noncomputable def boxQlb (a b s : ℝ) : ℝ :=
  (b^2-a^2)/(2*(b^2+s^2)) + (b^2-a^2)^2/(8*(b^2+s^2)^2) + (b^2-a^2)^3/(16*(b^2+s^2)^3)

/-- `b·arsinh(β/t)/√(b²+t²) ≤ boxMajTerm b β t` for `0 < β`, `0 < t`. -/
lemma arsinh_term_le {b β t : ℝ} (hb : 0 < b) (hβ : 0 < β) (ht : 0 < t) :
    b * Real.arsinh (β/t)/Real.sqrt (b^2+t^2) ≤ boxMajTerm b β t := by
  have hspos : 0 < Real.sqrt (b^2+t^2) := Real.sqrt_pos.mpr (by positivity)
  unfold boxMajTerm
  by_cases h : t ≤ β
  · rw [if_pos h]
    have hx : 0 < β/t := by positivity
    have h1 := Commons.Analysis.Real.arsinh_le_log_two_mul_add_inv hx
    have hlog : 0 ≤ Real.log ((4*β^2+t^2)/(2*β*t)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (β - t), sq_nonneg β, hβ]
    have hlog' : Real.arsinh (β/t) ≤ Real.log ((4*β^2+t^2)/(2*β*t)) := by
      have := h1
      rwa [show (2*(β/t) + (2*(β/t))⁻¹) = (4*β^2+t^2)/(2*β*t) by field_simp; ring] at this
    have h3 : b/Real.sqrt (b^2+t^2) ≤ 1 - t^2/(2*(b^2+β^2)) := by
      have h2 := one_sub_div_sqrt_sq_ge' (b:=b) (τ:=β) (t:=t) hb (le_of_lt ht) h
      linarith
    calc b * Real.arsinh (β/t)/Real.sqrt (b^2+t^2)
        = Real.arsinh (β/t) * (b/Real.sqrt (b^2+t^2)) := by ring
      _ ≤ Real.log ((4*β^2+t^2)/(2*β*t)) * (1 - t^2/(2*(b^2+β^2))) :=
          mul_le_mul hlog' h3 (by positivity) hlog
  · rw [if_neg h]
    have hx : 0 ≤ β/t := by positivity
    have h1 := Commons.Analysis.Real.arsinh_le_self_of_nonneg hx
    calc b * Real.arsinh (β/t)/Real.sqrt (b^2+t^2)
        = b*(Real.arsinh (β/t))/Real.sqrt (b^2+t^2) := by ring
      _ ≤ b*(β/t)/Real.sqrt (b^2+t^2) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hspos)
          exact mul_le_mul_of_nonneg_left h1 hb.le
      _ = b*β/(t*Real.sqrt (b^2+t^2)) := by field_simp

/-- `1 - √(1-u) ≥ u/2 + u²/8 + u³/16` for `u ∈ [0,1]`. -/
lemma one_sub_sqrt_one_sub_ge {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 - Real.sqrt (1-u) ≥ u/2 + u^2/8 + u^3/16 := by
  have := Commons.Analysis.Real.sqrt_one_sub_le_cubic_sum hu0 hu1
  linarith

/-- Pointwise domination of the inner `x`-integral by the majorant, for `b = 2 - a`. -/
lemma inner_le_boxMaj {a s : ℝ} (ha : 0 < a) (ha1 : a < 1) (hs : s ≠ 0) :
    (∫ x in (0:ℝ)..2, (2-x)/(Real.sqrt ((x-a)^2+s^2)*Real.sqrt ((2-a)^2+s^2)))
      ≤ boxMaj a (2-a) s - boxQlb a (2-a) s := by
  have hb : 0 < 2 - a := by linarith
  set t : ℝ := |s| with ht
  have htpos : 0 < t := by rw [ht]; exact abs_pos.mpr hs
  have hs2 : s^2 = t^2 := by rw [ht]; exact (sq_abs s).symm
  have hsplit : (∫ x in (0:ℝ)..2, (2-x)/(Real.sqrt ((x-a)^2+t^2)*Real.sqrt ((2-a)^2+t^2)))
      = (1/Real.sqrt ((2-a)^2+t^2)) * (∫ x in (0:ℝ)..2, (2-x)/Real.sqrt ((x-a)^2+t^2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro x _; field_simp
  have hclosed := arsinh_antideriv_two_sub (a := a) (t := t) htpos
  have hQ : 1 - Real.sqrt (a^2+t^2)/Real.sqrt ((2-a)^2+t^2) ≥
      ((2-a)^2-a^2)/(2*((2-a)^2+t^2)) + ((2-a)^2-a^2)^2/(8*((2-a)^2+t^2)^2)
      + ((2-a)^2-a^2)^3/(16*((2-a)^2+t^2)^3) := by
    have hden : 0 < (2-a)^2+t^2 := by positivity
    have hu0 : 0 ≤ ((2-a)^2-a^2)/((2-a)^2+t^2) := by
      apply div_nonneg _ hden.le; nlinarith
    have hu1 : ((2-a)^2-a^2)/((2-a)^2+t^2) ≤ 1 := by rw [div_le_one hden]; nlinarith
    have hkey := one_sub_sqrt_one_sub_ge (u := ((2-a)^2-a^2)/((2-a)^2+t^2)) hu0 hu1
    have hsq : Real.sqrt (a^2+t^2)/Real.sqrt ((2-a)^2+t^2)
        = Real.sqrt (1 - ((2-a)^2-a^2)/((2-a)^2+t^2)) := by
      rw [← Real.sqrt_div (by positivity),
        show (a^2+t^2)/((2-a)^2+t^2) = 1 - ((2-a)^2-a^2)/((2-a)^2+t^2) by field_simp; ring]
    rw [hsq]
    have he : ((2-a)^2-a^2)/((2-a)^2+t^2)/2 + (((2-a)^2-a^2)/((2-a)^2+t^2))^2/8
        + (((2-a)^2-a^2)/((2-a)^2+t^2))^3/16
        = ((2-a)^2-a^2)/(2*((2-a)^2+t^2)) + ((2-a)^2-a^2)^2/(8*((2-a)^2+t^2)^2)
          + ((2-a)^2-a^2)^3/(16*((2-a)^2+t^2)^3) := by
      field_simp; try ring
    rw [← he]; exact hkey
  have hA : (2-a)*Real.arsinh ((2-a)/t)/Real.sqrt ((2-a)^2+t^2) ≤ boxMajTerm (2-a) (2-a) t :=
    arsinh_term_le hb hb htpos
  have hB : (2-a)*Real.arsinh (a/t)/Real.sqrt ((2-a)^2+t^2) ≤ boxMajTerm (2-a) a t :=
    arsinh_term_le hb ha htpos
  have hexp : (1/Real.sqrt ((2-a)^2+t^2))
        * ((2-a)*(Real.arsinh ((2-a)/t)+Real.arsinh (a/t)) - (Real.sqrt ((2-a)^2+t^2)-Real.sqrt (a^2+t^2)))
      = (2-a)*Real.arsinh ((2-a)/t)/Real.sqrt ((2-a)^2+t^2)
        + (2-a)*Real.arsinh (a/t)/Real.sqrt ((2-a)^2+t^2)
        - (1 - Real.sqrt (a^2+t^2)/Real.sqrt ((2-a)^2+t^2)) := by
    field_simp; try ring
  have hgoal : (∫ x in (0:ℝ)..2, (2-x)/(Real.sqrt ((x-a)^2+t^2)*Real.sqrt ((2-a)^2+t^2)))
      ≤ boxMaj a (2-a) s - boxQlb a (2-a) s := by
    rw [hsplit, hclosed, hexp]
    unfold boxMaj boxQlb
    rw [← ht, hs2]
    linarith
  simpa [hs2] using hgoal

end Commons.Analysis.Integral

namespace Commons.Analysis.Integral

/-- Pointwise domination of the majorant term by an integrable profile. -/
lemma boxMajTerm_le_dom {b γ : ℝ} (hb : 0 < b) (hγ : 0 < γ) :
    ∀ s : ℝ, boxMajTerm b γ (abs s)
      ≤ (max (Real.log (5*γ/2)) (b/γ) + 1) * (1 + abs (Real.log s)) := by
  intro s
  have hK1 : (1:ℝ) ≤ max (Real.log (5*γ/2)) (b/γ) + 1 := by
    have := le_max_right (Real.log (5*γ/2)) (b/γ)
    have hbg : 0 < b/γ := div_pos hb hγ
    linarith
  have hK0 : 0 ≤ max (Real.log (5*γ/2)) (b/γ) + 1 := le_trans zero_le_one hK1
  have hKlog : Real.log (5*γ/2) ≤ max (Real.log (5*γ/2)) (b/γ) + 1 := by
    have := le_max_left (Real.log (5*γ/2)) (b/γ); linarith
  have hKbg : b/γ ≤ max (Real.log (5*γ/2)) (b/γ) + 1 := by
    have := le_max_right (Real.log (5*γ/2)) (b/γ); linarith
  by_cases hs : s = 0
  · subst hs
    simp only [abs_zero]
    have hz : boxMajTerm b γ (0:ℝ) = 0 := by simp [boxMajTerm]
    rw [hz]
    have := abs_nonneg (Real.log (0:ℝ))
    nlinarith [hK0, this]
  · have habs : 0 < abs s := abs_pos.mpr hs
    have hlog_abs : Real.log (abs s) = Real.log s := Real.log_abs s
    have hnn : 0 ≤ boxMajTerm b γ (abs s) := by
      unfold boxMajTerm
      split_ifs with h
      · apply mul_nonneg
        · apply Real.log_nonneg
          rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*γ*abs s)]
          nlinarith [sq_abs s, abs_nonneg s, sq_nonneg γ]
        · rw [sub_nonneg, div_le_one (by positivity)]
          nlinarith [sq_abs s, h, abs_nonneg s, sq_nonneg γ, sq_nonneg b, hb, hγ]
      · positivity
    rw [boxMajTerm]
    by_cases h : abs s ≤ γ
    · rw [if_pos h]
      have hnum : 0 < 4*γ^2 + (abs s)^2 := by positivity
      have hden : 0 < 2*γ*abs s := by positivity
      have hlogeq : Real.log ((4*γ^2+(abs s)^2)/(2*γ*abs s))
          = Real.log (4*γ^2+(abs s)^2) - Real.log (2*γ) - Real.log (abs s) := by
        rw [Real.log_div (ne_of_gt hnum) (ne_of_gt hden),
            Real.log_mul (by positivity) (ne_of_gt habs)]; ring
      have hlogpos : 0 ≤ Real.log (4*γ^2+(abs s)^2) - Real.log (2*γ) - Real.log (abs s) := by
        rw [← hlogeq]; apply Real.log_nonneg
        rw [le_div_iff₀ hden]; nlinarith [sq_abs s, abs_nonneg s, sq_nonneg γ]
      have hfac : (1 - (abs s)^2/(2*(b^2+γ^2))) ≤ 1 := by
        rw [sub_le_iff_le_add, le_add_iff_nonneg_right]; positivity
      have h5 : Real.log (4*γ^2+(abs s)^2) - Real.log (5*γ^2) ≤ 0 := by
        have : Real.log (4*γ^2+(abs s)^2) ≤ Real.log (5*γ^2) := by
          apply Real.log_le_log (by positivity)
          nlinarith [sq_abs s, abs_nonneg s, sq_nonneg (γ - abs s), h, hγ]
        linarith
      have hcsplit : Real.log (5*γ^2) - Real.log (2*γ) = Real.log (5*γ/2) := by
        rw [← Real.log_div (by positivity) (by positivity)]; congr 1; field_simp
      have hneg : -Real.log (abs s) ≤ abs (Real.log s) := by
        rw [hlog_abs]; exact neg_le_abs _
      calc Real.log ((4*γ^2+(abs s)^2)/(2*γ*abs s)) * (1 - (abs s)^2/(2*(b^2+γ^2)))
          ≤ Real.log ((4*γ^2+(abs s)^2)/(2*γ*abs s)) :=
            mul_le_of_le_one_right (by rw [hlogeq]; exact hlogpos) hfac
        _ = (Real.log (4*γ^2+(abs s)^2) - Real.log (5*γ^2))
              + (Real.log (5*γ/2)) + (-Real.log (abs s)) := by rw [hlogeq]; linarith [hcsplit]
        _ ≤ (max (Real.log (5*γ/2)) (b/γ) + 1) * (1 + abs (Real.log s)) := by
            have h2 : 0 ≤ abs (Real.log s) := abs_nonneg _
            nlinarith [hKlog, hK1, hneg,
              mul_nonneg hK0 h2]
    · rw [if_neg h]
      push_neg at h
      have hle2 : b*γ/(abs s*Real.sqrt (b^2+(abs s)^2)) ≤ b/γ := by
        have hs2 : γ^2 ≤ (abs s)^2 := by nlinarith [h, hγ, abs_nonneg s]
        have hsqrt : abs s ≤ Real.sqrt (b^2+(abs s)^2) := by
          nlinarith [Real.sq_sqrt (show 0≤b^2+(abs s)^2 by positivity), abs_nonneg s,
            sq_nonneg b, sq_abs s, Real.sqrt_nonneg (b^2+(abs s)^2)]
        have hX : γ^2 ≤ abs s * Real.sqrt (b^2+(abs s)^2) := by
          nlinarith [hsqrt, abs_nonneg s, hs2,
            mul_nonneg (le_of_lt habs) (Real.sqrt_nonneg (b^2+(abs s)^2))]
        have hone : b*γ/(abs s*Real.sqrt (b^2+(abs s)^2)) ≤ b*γ/γ^2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hX
        have htwo : b*γ/γ^2 = b/γ := by field_simp
        linarith [hone, htwo.le, htwo.ge]
      have h2 : 0 ≤ abs (Real.log s) := abs_nonneg _
      nlinarith [hKbg, h2, hle2, hK0,
        mul_nonneg hK0 (by linarith : (0:ℝ) ≤ 1 + abs (Real.log s))]

/-- The majorant term is interval integrable. -/
lemma intervalIntegrable_boxMajTerm (b γ : ℝ) (hb : 0 < b) (hγ : 0 < γ) (p q : ℝ) :
    IntervalIntegrable (fun s : ℝ => boxMajTerm b γ (abs s)) volume p q := by
  have hg : IntervalIntegrable
      (fun s : ℝ => (max (Real.log (5*γ/2)) (b/γ) + 1) * (1 + abs (Real.log s))) volume p q := by
    have h1 : IntervalIntegrable (fun s : ℝ => abs (Real.log s)) volume p q := by
      exact (intervalIntegral.intervalIntegrable_log' (a:=p) (b:=q)).abs
    have h3 : IntervalIntegrable (fun s : ℝ => (1:ℝ)) volume p q := intervalIntegrable_const
    have := ((h3.add h1)).const_mul (max (Real.log (5*γ/2)) (b/γ) + 1)
    simpa [mul_add] using this
  refine hg.mono_fun' ?_ ?_
  · have hm : Measurable (fun s : ℝ => boxMajTerm b γ (abs s)) := by
      unfold boxMajTerm
      exact Measurable.ite (measurableSet_le measurable_abs measurable_const)
        (by fun_prop) (by fun_prop)
    exact hm.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self
  · filter_upwards with s
    have hnn : 0 ≤ boxMajTerm b γ (abs s) := by
      rcases eq_or_ne s 0 with rfl | hs'
      · simp [boxMajTerm]
      · unfold boxMajTerm
        split_ifs with h
        · apply mul_nonneg
          · apply Real.log_nonneg
            rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*γ*abs s)]
            nlinarith [sq_abs s, abs_nonneg s, sq_nonneg γ]
          · rw [sub_nonneg, div_le_one (by positivity)]
            nlinarith [sq_abs s, h, abs_nonneg s, sq_nonneg γ, sq_nonneg b]
        · positivity
    rw [Real.norm_of_nonneg hnn]
    exact boxMajTerm_le_dom hb hγ s

/-- The full majorant is interval integrable. -/
lemma intervalIntegrable_boxMaj (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (p q : ℝ) :
    IntervalIntegrable (fun s : ℝ => boxMaj a b s) volume p q := by
  unfold boxMaj
  exact (intervalIntegrable_boxMajTerm b b hb hb p q).add
    (intervalIntegrable_boxMajTerm b a hb ha p q)

/-- `boxQlb` is interval integrable (it is continuous). -/
lemma intervalIntegrable_boxQlb (a b : ℝ) (hb : 0 < b) (p q : ℝ) :
    IntervalIntegrable (fun s : ℝ => boxQlb a b s) volume p q := by
  apply ContinuousOn.intervalIntegrable
  intro s _
  exact ContinuousAt.continuousWithinAt
    (by unfold boxQlb; fun_prop (disch := positivity))

/-- The inner `x`-integral is (strongly) measurable in the shift `T`. -/
lemma aestronglyMeasurable_inner (β γ : ℝ) :
    AEStronglyMeasurable (fun T : ℝ => ∫ x in (0:ℝ)..2,
      (2 - x)/(Real.sqrt ((x-β)^2+(T-γ)^2)*Real.sqrt ((2-β)^2+(T-γ)^2))) volume := by
  have hfmeas : Measurable (fun p : ℝ × ℝ =>
      (2 - p.2)/(Real.sqrt ((p.2-β)^2+(p.1-γ)^2)*Real.sqrt ((2-β)^2+(p.1-γ)^2))) := by
    fun_prop
  have h := (hfmeas.stronglyMeasurable.aestronglyMeasurable).integral_prod_right'
    (μ := volume) (ν := volume.restrict (Set.uIoc 0 2))
  simpa only [Function.uncurry_apply_pair, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2),
    Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 2)] using h

/-- The `h`-kernel appearing on the right-hand side of `boxKernel_le_rebased`. -/
noncomputable def boxH (β s : ℝ) : ℝ :=
  (3/2-β)/((3/2-β)^2+s^2) + (1+β)/((1+β)^2+s^2)

/-- Continuity of the target kernel `boxH β`. -/
lemma continuous_boxH {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Continuous (fun s : ℝ => boxH β s) := by
  have h1 : 0 < 3/2 - β := by linarith
  have h2 : 0 < 1 + β := by linarith
  unfold boxH
  apply Continuous.add
  · apply Continuous.div (by fun_prop) (by fun_prop)
    intro s
    have : 0 < (3/2-β)^2 + s^2 := by positivity
    exact ne_of_gt this
  · apply Continuous.div (by fun_prop) (by fun_prop)
    intro s
    have : 0 < (1+β)^2 + s^2 := by positivity
    exact ne_of_gt this

/-- The target kernel `boxH β` is interval integrable. -/
lemma intervalIntegrable_boxH {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (p q : ℝ) :
    IntervalIntegrable (fun s : ℝ => boxH β s) volume p q :=
  (continuous_boxH hβ0 hβ1).intervalIntegrable p q

/-- The even integrand of the window inequality
`(13/5)·boxH β s - boxMaj β (2-β) s + boxQlb β (2-β) s`. -/
noncomputable def winE (β : ℝ) (s : ℝ) : ℝ :=
  (13/5)*boxH β s + boxQlb β (2-β) s - boxMaj β (2-β) s

lemma winE_even (β s : ℝ) : winE β (-s) = winE β s := by
  unfold winE boxH boxQlb boxMaj boxMajTerm
  rw [abs_neg]
  ring_nf

/-- The window integral of `winE` is invariant under `δ ↦ -1-δ` (the integrand is even). -/
lemma winE_window_reflect (β δ : ℝ) :
    (∫ s in δ..δ+1, winE β s) = ∫ s in (-1-δ)..((-1-δ)+1), winE β s := by
  have h := intervalIntegral.integral_comp_neg (a := δ) (b := δ + 1) (winE β)
  rw [show (fun x : ℝ => winE β (-x)) = winE β from funext (winE_even β)] at h
  rw [h]
  congr 1 <;> ring

/-- **Assembly of the window inequality.**  If the even integrand `winE β` is pointwise nonnegative
for `s ≥ 1/6` and has nonnegative unit-window integral on `[-1/6,1/6]` and on `[-1/2,-1/6]`, then
every unit window has nonnegative integral. -/
lemma boxWindow_all_of {β : ℝ}
    (hA : ∀ s : ℝ, 1/6 ≤ s → 0 ≤ winE β s)
    (hB : ∀ δ : ℝ, -1/6 ≤ δ → δ ≤ 1/6 → 0 ≤ ∫ s in δ..δ+1, winE β s)
    (hC : ∀ δ : ℝ, -1/2 ≤ δ → δ ≤ -1/6 → 0 ≤ ∫ s in δ..δ+1, winE β s) :
    ∀ δ : ℝ, 0 ≤ ∫ s in δ..δ+1, winE β s := by
  have hpt : ∀ a : ℝ, 1/6 ≤ a → 0 ≤ ∫ s in a..(a+1), winE β s := by
    intro a ha
    apply intervalIntegral.integral_nonneg (by linarith)
    intro u hu
    exact hA u (by linarith [hu.1])
  intro δ
  rcases le_or_gt δ (-1/2) with h | h
  · -- δ ≤ -1/2
    rw [winE_window_reflect β δ]
    rcases le_or_gt δ (-5/4) with h2 | h2
    · -- δ ≤ -5/4: the reflected window starts at ≥ 1/4
      exact hpt _ (by linarith)
    · -- -5/4 < δ ≤ -1/2, reflected start -1-δ ∈ [-1/2, 1/4]
      rcases le_or_gt (-1-δ) (-1/6) with h3 | h3
      · exact hC _ (by linarith) (by linarith)
      · rcases le_or_gt (-1-δ) (1/6) with h4 | h4
        · exact hB _ (by linarith) (by linarith)
        · exact hpt _ (by linarith)
  · -- δ > -1/2
    rcases le_or_gt δ (-1/6) with h3 | h3
    · exact hC _ (le_of_lt h) h3
    · rcases le_or_gt δ (1/6) with h4 | h4
      · exact hB _ (le_of_lt h3) h4
      · exact hpt _ (le_of_lt h4)

/-- **Window reduction.**  If every unit window of the even difference
`D(s) = (13/5)·boxH β s - boxMaj β (2-β) s + boxQlb β (2-β) s` has nonnegative integral,
then the majorant dominates the target kernel on every unit window (shifted by any `γ`). -/
lemma window_reduction {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hW : ∀ δ : ℝ, 0 ≤ ∫ s in δ..δ+1, winE β s)
    (c γ : ℝ) :
    (∫ T in c..c+1, (boxMaj β (2-β) (T-γ) - boxQlb β (2-β) (T-γ)))
      ≤ (13/5) * (∫ T in c..c+1, boxH β (T-γ)) := by
  have hb : 0 < 2 - β := by linarith
  set δ : ℝ := c - γ with hδ
  have hM : (∫ T in c..c+1, (boxMaj β (2-β) (T-γ) - boxQlb β (2-β) (T-γ)))
      = ∫ s in δ..δ+1, (boxMaj β (2-β) s - boxQlb β (2-β) s) := by
    rw [hδ, intervalIntegral.integral_comp_sub_right
      (fun s : ℝ => boxMaj β (2-β) s - boxQlb β (2-β) s) γ]
    congr 1 <;> ring
  have hH : (∫ T in c..c+1, boxH β (T-γ)) = ∫ s in δ..δ+1, boxH β s := by
    rw [hδ, intervalIntegral.integral_comp_sub_right (fun s : ℝ => boxH β s) γ]
    congr 1 <;> ring
  have hI1 : IntervalIntegrable (fun s : ℝ => boxH β s) volume δ (δ+1) :=
    intervalIntegrable_boxH hβ0 hβ1 δ (δ+1)
  have hI2 : IntervalIntegrable (fun s : ℝ => boxMaj β (2-β) s) volume δ (δ+1) :=
    intervalIntegrable_boxMaj β (2-β) hβ0 hb δ (δ+1)
  have hI3 : IntervalIntegrable (fun s : ℝ => boxQlb β (2-β) s) volume δ (δ+1) :=
    intervalIntegrable_boxQlb β (2-β) hb δ (δ+1)
  have hA : IntervalIntegrable (fun s : ℝ => (13/5) * boxH β s) volume δ (δ+1) :=
    hI1.const_mul (13/5)
  have hE : ∫ s in δ..δ+1, winE β s
      = (13/5) * (∫ s in δ..δ+1, boxH β s) + (∫ s in δ..δ+1, boxQlb β (2-β) s)
        - (∫ s in δ..δ+1, boxMaj β (2-β) s) := by
    unfold winE
    rw [intervalIntegral.integral_sub (hA.add hI3) hI2,
        intervalIntegral.integral_add hA hI3,
        intervalIntegral.integral_const_mul]
  have hMQ : (∫ s in δ..δ+1, (boxMaj β (2-β) s - boxQlb β (2-β) s))
      = (∫ s in δ..δ+1, boxMaj β (2-β) s) - (∫ s in δ..δ+1, boxQlb β (2-β) s) :=
    intervalIntegral.integral_sub hI2 hI3
  have hWδ := hW δ
  rw [hE] at hWδ
  rw [hM, hH, hMQ]
  linarith

theorem boxKernel_le_rebased {c : ℝ} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (γ : ℝ) :
    (∫ T in c..c + 1, ∫ x in 0..2,
        (2 - x) / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2) *
          Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2)))
      ≤ (13 / 5) * (∫ T in c..c + 1,
        ((3 / 2 - β) / ((3 / 2 - β) ^ 2 + (T - γ) ^ 2)
          + (1 + β) / ((1 + β) ^ 2 + (T - γ) ^ 2))) := by
  have hb : 0 < 2 - β := by linarith
  have hH : (∫ T in c..c + 1,
        ((3 / 2 - β) / ((3 / 2 - β) ^ 2 + (T - γ) ^ 2)
          + (1 + β) / ((1 + β) ^ 2 + (T - γ) ^ 2)))
      = ∫ T in c..c+1, boxH β (T-γ) := rfl
  rw [hH]
  -- Pointwise (a.e.) domination of the inner `x`-integral by the elementary majorant.
  have hpt : ∀ T : ℝ, T ≠ γ →
      (∫ x in 0..2, (2 - x) / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2) *
          Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2)))
        ≤ boxMaj β (2-β) (T-γ) - boxQlb β (2-β) (T-γ) :=
    fun T hT => inner_le_boxMaj hβ0 hβ1 (sub_ne_zero.mpr hT)
  -- The majorant is interval integrable.
  have hGint : IntervalIntegrable
      (fun T => boxMaj β (2-β) (T-γ) - boxQlb β (2-β) (T-γ)) volume c (c+1) := by
    have h1 : IntervalIntegrable (fun T : ℝ => boxMaj β (2-β) (T-γ)) volume c (c+1) := by
      have := (intervalIntegrable_boxMaj β (2-β) hβ0 hb (c-γ) (c+1-γ)).comp_sub_right γ
      simpa using this
    have h2 : IntervalIntegrable (fun T : ℝ => boxQlb β (2-β) (T-γ)) volume c (c+1) := by
      have := (intervalIntegrable_boxQlb β (2-β) hb (c-γ) (c+1-γ)).comp_sub_right γ
      simpa using this
    exact h1.sub h2
  -- Monotonicity of the outer interval integral (a.e. pointwise inequality).
  have hmono : (∫ T in c..c + 1, ∫ x in 0..2,
        (2 - x) / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2) *
          Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2)))
      ≤ ∫ T in c..c+1, (boxMaj β (2-β) (T-γ) - boxQlb β (2-β) (T-γ)) := by
    -- `{γ}` is null, so pointwise domination off `γ` is enough.
    have hnull : ∀ᵐ T ∂(volume : Measure ℝ), T ≠ γ := by
      rw [MeasureTheory.ae_iff]
      simpa using measure_singleton γ
    -- The inner `x`-integral is interval integrable, by domination from `hGint`.
    have hFint : IntervalIntegrable
        (fun T => ∫ x in (0:ℝ)..2,
          (2 - x) / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2) *
            Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2))) volume c (c + 1) := by
      refine hGint.mono_fun' ?_ ?_
      · exact (aestronglyMeasurable_inner β γ).mono_measure MeasureTheory.Measure.restrict_le_self
      · have hbad : (volume.restrict (Set.uIoc c (c+1))) ({γ} : Set ℝ) = 0 := by
          rw [MeasureTheory.Measure.restrict_apply (MeasurableSet.singleton γ)]
          exact measure_mono_null Set.inter_subset_left (measure_singleton γ)
        have hne : ∀ᵐ T ∂(volume.restrict (Set.uIoc c (c+1))), T ≠ γ := by
          rw [MeasureTheory.ae_iff]
          simpa using hbad
        refine hne.mono ?_
        intro T hT
        show ‖∫ x in (0:ℝ)..2, (2 - x) / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2) *
              Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2))‖
            ≤ boxMaj β (2-β) (T-γ) - boxQlb β (2-β) (T-γ)
        have hnn : 0 ≤ ∫ x in (0:ℝ)..2,
            (2 - x) / (Real.sqrt ((x - β) ^ 2 + (T - γ) ^ 2) *
              Real.sqrt ((2 - β) ^ 2 + (T - γ) ^ 2)) := by
          apply intervalIntegral.integral_nonneg (by norm_num)
          intro u hu
          exact div_nonneg (by linarith [hu.2])
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        rw [Real.norm_of_nonneg hnn]
        exact hpt T hT
    exact intervalIntegral.integral_mono_ae (by linarith) hFint hGint
      (hnull.mono (fun T hT => hpt T hT))
  -- The central window inequality for the majorant (delegated).
  have hwindow : (∫ T in c..c+1, (boxMaj β (2-β) (T-γ) - boxQlb β (2-β) (T-γ)))
      ≤ (13/5) * (∫ T in c..c+1, boxH β (T-γ)) := by
    refine window_reduction hβ0 hβ1 ?_ c γ
    refine boxWindow_all_of ?_ ?_ ?_
    · -- pointwise nonnegativity for `s ≥ 1/6`
      intro s hs
      have h := boxMaj_le_target_kernel_ge_sixth hβ0 hβ1 hs
      convert h using 1
      simp only [winE, boxH, boxQlb, boxMaj, boxMajTerm,
        abs_of_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1/6) hs)]
      ring_nf
    · -- the middle window range
      intro δ h1 h2
      have h := boxWindow_middle hβ0 hβ1 δ h1 h2
      convert h using 1
      apply intervalIntegral.integral_congr
      intro s _
      simp only [winE, boxH, boxQlb, boxMaj, boxMajTerm]
      ring_nf
    · -- the left window range
      intro δ h1 h2
      have h := boxWindow_left_half hβ0 hβ1 δ h1 h2
      convert h using 1
      apply intervalIntegral.integral_congr
      intro s _
      simp only [winE, boxH, boxQlb, boxMaj, boxMajTerm]
      ring_nf
  linarith [hmono, hwindow]


end Commons.Analysis.Integral
