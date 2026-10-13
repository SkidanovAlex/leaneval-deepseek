/-
Copyright: work module for the Elgindi finite-time singularity project.

# The one-dimensional window Agmon inequality

`Work.FTS.StrongEps.E5Aux.agmon_window`: for `a < b`, `x ∈ [a,b]` and `u` continuous on `[a,b]`
with derivative `u'` there,

  `u x ^ 2 ≤ 2 * ((b-a)⁻¹ * ∫_{a}^{b} u ^ 2 + (b-a) * ∫_{a}^{b} (u') ^ 2)`.

This is the elementary "value controlled by the local `L²`-norm of the function and of its
derivative" estimate (Agmon–Nirenberg in one dimension, in the *window* form): some
`t ∈ [a,b]` has `u t ^ 2 ≤ (1/(b-a)) * ∫_{a}^{b} u ^ 2`, the fundamental theorem of calculus
`u x = u t + ∫_t^x u'` gives `u x ^ 2 ≤ 2 * u t ^ 2 + 2 * (∫_{a}^{b} |u'|) ^ 2`, and
Cauchy–Schwarz gives `(∫_{a}^{b} |u'|) ^ 2 ≤ (b-a) * ∫_{a}^{b} (u') ^ 2`; averaging over the
window `t ∈ [a,b]` makes the estimate unconditional — no vanishing of `u` on the boundary, no
global integrability, no trace hypothesis.  It is the tool that bounds a *point* value of a
slice by the `L²`-norms of the neighbouring window.

Two elementary facts about the radial weight `w(z) = (1+z)²/z²` used by the applications are
recorded as well: monotonicity on `(0,∞)` and `w z ≤ 9 * w (3z/2)`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

/-- **The window Agmon inequality.**  For `a < b`, `x ∈ [a,b]` and a `C¹` function `u` on the
window `[a,b]` (continuity on the closed interval, derivative `u'` on the open interval, `u'`
continuous on the closed interval),

  `u x ^ 2 ≤ 2 * ((b-a)⁻¹ * ∫_{a}^{b} u ^ 2 + (b-a) * ∫_{a}^{b} (u') ^ 2)`. -/
theorem agmon_window {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b)
    {u u' : ℝ → ℝ}
    (hcont : ContinuousOn u (Set.Icc a b)) (hcont' : ContinuousOn u' (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt u (u' y) y) :
    (u x) ^ 2 ≤ 2 * ((b - a)⁻¹ * (∫ y in a..b, (u y) ^ 2)
      + (b - a) * (∫ y in a..b, (u' y) ^ 2)) := by
  have hab' : a ≤ x := hx.1
  have hxb : x ≤ b := hx.2
  have hLpos : 0 < b - a := sub_pos.mpr hab
  have hsubab : Set.uIcc a b ⊆ Set.Icc a b := by rw [Set.uIcc_of_le hab.le]
  have hIabs : IntervalIntegrable (fun s => |u' s|) volume a b :=
    ((hcont'.mono hsubab).intervalIntegrable).abs
  have hIu2 : IntervalIntegrable (fun t => (u t) ^ 2) volume a b :=
    ((hcont.mono hsubab).pow 2).intervalIntegrable
  -- ### the fundamental theorem of calculus on the window
  have hFTC : ∀ t ∈ Set.Icc a b, ∫ s in t..x, u' s = u x - u t := by
    intro t ht
    rcases le_total t x with htx | hxt
    · refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htx ?_ ?_ ?_
      · exact hcont.mono (Set.Icc_subset_Icc ht.1 hxb)
      · intro y hy
        exact hderiv y ⟨lt_of_le_of_lt ht.1 hy.1, lt_of_lt_of_le hy.2 hxb⟩
      · have hsub : Set.uIcc t x ⊆ Set.Icc a b := by
          rw [Set.uIcc_of_le htx]; exact Set.Icc_subset_Icc ht.1 hxb
        exact (hcont'.mono hsub).intervalIntegrable
    · rw [intervalIntegral.integral_symm x t]
      have h1 : ∫ s in x..t, u' s = u t - u x := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxt ?_ ?_ ?_
        · exact hcont.mono (Set.Icc_subset_Icc hab' ht.2)
        · intro y hy
          exact hderiv y ⟨lt_of_le_of_lt hab' hy.1, lt_of_lt_of_le hy.2 ht.2⟩
        · have hsub : Set.uIcc x t ⊆ Set.Icc a b := by
            rw [Set.uIcc_of_le hxt]; exact Set.Icc_subset_Icc hab' ht.2
          exact (hcont'.mono hsub).intervalIntegrable
      rw [h1]; ring
  -- ### the value of `u` at `x` against the window `L¹`-norm of `u'`
  have habs' : ∀ t ∈ Set.Icc a b, |u x - u t| ≤ ∫ s in a..b, |u' s| := by
    intro t ht
    rcases le_total t x with htx | hxt
    · have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) htx
        (f := u') (a := t) (b := x)
      rw [Real.norm_eq_abs] at h1
      have h2 : ∫ s in t..x, |u' s| ≤ ∫ s in a..b, |u' s| := by
        refine intervalIntegral.integral_mono_interval ht.1 htx hxb ?_ hIabs
        exact Filter.Eventually.of_forall fun y => abs_nonneg _
      calc |u x - u t| = |∫ s in t..x, u' s| := by rw [hFTC t ht]
        _ ≤ ∫ s in t..x, |u' s| := h1
        _ ≤ ∫ s in a..b, |u' s| := h2
    · have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hxt
        (f := u') (a := x) (b := t)
      rw [Real.norm_eq_abs] at h1
      have h1' : |u t - u x| ≤ ∫ s in x..t, |u' s| := by
        have hftc2 : ∫ s in x..t, u' s = u t - u x := by
          rw [intervalIntegral.integral_symm t x, hFTC t ht]; ring
        rw [← hftc2]; exact h1
      have h2 : ∫ s in x..t, |u' s| ≤ ∫ s in a..b, |u' s| := by
        refine intervalIntegral.integral_mono_interval hab' hxt ht.2 ?_ hIabs
        exact Filter.Eventually.of_forall fun y => abs_nonneg _
      calc |u x - u t| = |u t - u x| := abs_sub_comm _ _
        _ ≤ ∫ s in x..t, |u' s| := h1'
        _ ≤ ∫ s in a..b, |u' s| := h2
  -- ### the pointwise bound, for every `t` of the window
  have hstep : ∀ t ∈ Set.Icc a b,
      (u x) ^ 2 ≤ 2 * (u t) ^ 2 + 2 * (∫ s in a..b, |u' s|) ^ 2 := by
    intro t ht
    have hsq : (u x) ^ 2 ≤ 2 * (u t) ^ 2 + 2 * ((u x - u t)) ^ 2 := by
      nlinarith [sq_nonneg (u t - (u x - u t))]
    have hsq2 : ((u x - u t)) ^ 2 ≤ (∫ s in a..b, |u' s|) ^ 2 := by
      rw [← sq_abs (u x - u t)]
      exact pow_le_pow_left₀ (abs_nonneg _) (habs' t ht) 2
    linarith [hsq, hsq2]
  -- ### integrate over the window
  have hIntRHS : IntervalIntegrable
      (fun t => 2 * (u t) ^ 2 + 2 * (∫ s in a..b, |u' s|) ^ 2) volume a b :=
    ((hIu2.const_mul 2).add intervalIntegrable_const)
  have hinter : (u x) ^ 2 * (b - a)
      ≤ 2 * (∫ t in a..b, (u t) ^ 2)
        + (b - a) * (2 * (∫ s in a..b, |u' s|) ^ 2) := by
    have h1 := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hIntRHS hstep
    have h2 : ∫ t in a..b, (u x) ^ 2 = (u x) ^ 2 * (b - a) := by
      rw [intervalIntegral.integral_const]; ring
    have h3 : ∫ t in a..b, (2 * (u t) ^ 2 + 2 * (∫ s in a..b, |u' s|) ^ 2)
        = 2 * (∫ t in a..b, (u t) ^ 2)
          + (b - a) * (2 * (∫ s in a..b, |u' s|) ^ 2) := by
      rw [intervalIntegral.integral_add (hIu2.const_mul 2) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      ring
    rwa [h2, h3] at h1
  -- ### Cauchy–Schwarz in the derivative
  have hcs : (∫ s in a..b, |u' s|) ^ 2 ≤ (b - a) * ∫ s in a..b, (u' s) ^ 2 := by
    have h1 := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab.le
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun s => abs (u' s)) continuousOn_const
      (hcont'.abs.mono hsubab)
    set X : ℝ := ∫ s in a..b, abs (u' s) with hXdef
    have hXnn : 0 ≤ X := by
      rw [hXdef]; exact intervalIntegral.integral_nonneg hab.le (fun y _ => abs_nonneg _)
    have hinner : ∫ s in a..b, (fun _ : ℝ => (1 : ℝ)) s * abs (u' s) = X := by
      rw [hXdef]; exact intervalIntegral.integral_congr fun y _ => by rw [one_mul]
    rw [hinner, abs_of_nonneg hXnn] at h1
    have h3 : (∫ s in a..b, (fun _ : ℝ => (1 : ℝ)) s ^ 2) = b - a := by
      rw [intervalIntegral.integral_const]; simp
    have h4 : (∫ s in a..b, (fun s => abs (u' s)) s ^ 2) = ∫ s in a..b, (u' s) ^ 2 := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      rw [sq_abs]
    rw [h3, h4] at h1
    have h6 : 0 ≤ ∫ s in a..b, (u' s) ^ 2 :=
      intervalIntegral.integral_nonneg hab.le (fun y _ => sq_nonneg _)
    have h7 : (0 : ℝ) ≤ b - a := le_of_lt hLpos
    have hP : X ^ 2 ≤ (Real.sqrt (b - a) * Real.sqrt (∫ s in a..b, (u' s) ^ 2)) ^ 2 :=
      pow_le_pow_left₀ hXnn h1 2
    rw [mul_pow, Real.sq_sqrt h7, Real.sq_sqrt h6] at hP
    exact hP
  have hfinal : (u x) ^ 2 * (b - a)
      ≤ 2 * (∫ y in a..b, (u y) ^ 2) + 2 * (b - a) ^ 2 * (∫ y in a..b, (u' y) ^ 2) := by
    have hle : (b - a) * (2 * (∫ s in a..b, |u' s|) ^ 2)
        ≤ (b - a) * (2 * ((b - a) * ∫ s in a..b, (u' s) ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hLpos)
      linarith [hcs]
    linarith [hinter, hle]
  have hEq : (2 * ((b - a)⁻¹ * (∫ y in a..b, (u y) ^ 2)
        + (b - a) * (∫ y in a..b, (u' y) ^ 2))) * (b - a)
      = 2 * (∫ y in a..b, (u y) ^ 2) + 2 * (b - a) ^ 2 * (∫ y in a..b, (u' y) ^ 2) := by
    field_simp
  have hfinal' : (u x) ^ 2 * (b - a) ≤ (2 * ((b - a)⁻¹ * (∫ y in a..b, (u y) ^ 2)
      + (b - a) * (∫ y in a..b, (u' y) ^ 2))) * (b - a) := by
    rw [hEq]; exact hfinal
  exact (mul_le_mul_iff_of_pos_right hLpos).mp hfinal'

/-! ## Elementary facts about the weight `w` -/

/-- The weight `w(z) = (1+z)²/z² = (1 + 1/z)²` is antitone on `(0,∞)`. -/
theorem w_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Work.Spaces.w b ≤ Work.Spaces.w a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : (1 + b) / b = 1 + 1 / b := by field_simp; ring
  have h2 : (1 + a) / a = 1 + 1 / a := by field_simp; ring
  have h3 : (1 : ℝ) + 1 / b ≤ 1 + 1 / a := by
    have h : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
    linarith
  have h4 : 0 ≤ 1 + 1 / b := by positivity
  calc Work.Spaces.w b = ((1 + b) / b) ^ 2 := by rw [Work.Spaces.w]; ring_nf
    _ = (1 + 1 / b) ^ 2 := by rw [h1]
    _ ≤ (1 + 1 / a) ^ 2 := pow_le_pow_left₀ h4 h3 2
    _ = ((1 + a) / a) ^ 2 := by rw [h2]
    _ = Work.Spaces.w a := by rw [Work.Spaces.w]; ring_nf

/-- On the window `[z/2, 3z/2]` the weight at the left end is at most `9` times the weight at
the right end (the minimum of `w` on the window). -/
theorem w_div_w_three_halves_le {z : ℝ} (hz : 0 < z) :
    Work.Spaces.w z ≤ 9 * Work.Spaces.w (3 * z / 2) := by
  have h3 : 0 < 3 * z / 2 := by linarith
  have h1 : 0 < (1 + z) / z := div_pos (by linarith) hz
  have h2 : 0 < (1 + 3 * z / 2) / (3 * z / 2) := div_pos (by linarith) h3
  have hrat : ((1 + z) / z) / ((1 + 3 * z / 2) / (3 * z / 2))
      = 3 * (1 + z) / (2 + 3 * z) := by
    field_simp
  have hA : (1 + z) / z
      = (3 * (1 + z) / (2 + 3 * z)) * ((1 + 3 * z / 2) / (3 * z / 2)) := by
    rw [← hrat]
    exact (div_mul_cancel₀ _ (ne_of_gt h2)).symm
  have hr3 : 3 * (1 + z) / (2 + 3 * z) ≤ 3 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 + 3 * z)]
    linarith
  have hr : (1 + z) / z ≤ 3 * ((1 + 3 * z / 2) / (3 * z / 2)) := by
    rw [hA]
    exact mul_le_mul_of_nonneg_right hr3 (le_of_lt h2)
  calc Work.Spaces.w z = ((1 + z) / z) ^ 2 := by rw [Work.Spaces.w]; ring_nf
    _ ≤ (3 * ((1 + 3 * z / 2) / (3 * z / 2))) ^ 2 := pow_le_pow_left₀ (le_of_lt h1) hr 2
    _ = 9 * ((1 + 3 * z / 2) / (3 * z / 2)) ^ 2 := by ring
    _ = 9 * Work.Spaces.w (3 * z / 2) := by rw [Work.Spaces.w]; ring_nf

/-! ## The weighted form on the window `[z/2, 3z/2]` -/

/-- **The weighted window Agmon inequality.**  For `z > 0` and a `C¹` function `u` on the window
`I_z = [z/2, 3z/2]` (with derivative `u'`),

  `w z ^ 2 * (u z) ^ 2 ≤ 810 / z * (∫_{I_z} (u·w)² + ∫_{I_z} (x·u'·w)²)`.

The point is that the weight `w` can be moved *inside* the two window integrals: on `I_z` one has
`w (3z/2) ≤ w y` (monotonicity, `w_antitone`) and `w z ≤ 9 · w (3z/2)`
(`w_div_w_three_halves_le`), while `x ≥ z/2` supplies the factor `2/z` for the derivative term.
This is the form consumed by the per-`z` slice bounds of the `ℋ⁴`-integrand (the factor `1/z` is
absorbed by `1 + w z ^ 2` in those statements). -/
theorem agmon_weighted_window {z : ℝ} (hz : 0 < z) {u u' : ℝ → ℝ}
    (hcont : ContinuousOn u (Set.Icc (z / 2) (3 * z / 2)))
    (hcont' : ContinuousOn u' (Set.Icc (z / 2) (3 * z / 2)))
    (hderiv : ∀ y ∈ Set.Ioo (z / 2) (3 * z / 2), HasDerivAt u (u' y) y) :
    (Work.Spaces.w z) ^ 2 * (u z) ^ 2
      ≤ 810 / z * ((∫ y in z / 2..3 * z / 2, (u y * Work.Spaces.w y) ^ 2)
          + (∫ y in z / 2..3 * z / 2, (y * u' y * Work.Spaces.w y) ^ 2)) := by
  have hab : z / 2 < 3 * z / 2 := by linarith
  have hL : 3 * z / 2 - z / 2 = z := by ring
  set I1 : ℝ := ∫ y in z / 2..3 * z / 2, (u y * Work.Spaces.w y) ^ 2 with hI1def
  set I2 : ℝ := ∫ y in z / 2..3 * z / 2, (y * u' y * Work.Spaces.w y) ^ 2 with hI2def
  -- the weight is continuous and positive on the window, and minimal at `3z/2`
  have hcontw : ContinuousOn (fun y : ℝ => Work.Spaces.w y) (Set.Icc (z / 2) (3 * z / 2)) := by
    have hfun : (fun y : ℝ => Work.Spaces.w y) = fun y : ℝ => (1 + y) ^ 2 / y ^ 2 := by
      funext y; rw [Work.Spaces.w]
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun y hy => ?_)
    exact pow_ne_zero 2 (ne_of_gt (by linarith [hy.1, hz]))
  have hwpos : ∀ y ∈ Set.Icc (z / 2) (3 * z / 2), 0 < Work.Spaces.w y := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1, hz]
    rw [Work.Spaces.w]
    positivity
  have hmono : ∀ y ∈ Set.Icc (z / 2) (3 * z / 2),
      Work.Spaces.w (3 * z / 2) ≤ Work.Spaces.w y := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1, hz]
    exact w_antitone hy0 hy.2
  have hw32pos : 0 < Work.Spaces.w (3 * z / 2) := by rw [Work.Spaces.w]; positivity
  -- the main (unweighted) window Agmon inequality
  have hmain := agmon_window (x := z) hab ⟨by linarith, by linarith⟩ hcont hcont' hderiv
  rw [hL] at hmain
  -- the two pointwise comparisons on the window
  have hpt1 : ∀ y ∈ Set.Icc (z / 2) (3 * z / 2),
      (Work.Spaces.w (3 * z / 2)) ^ 2 * (u y) ^ 2 ≤ (u y * Work.Spaces.w y) ^ 2 := by
    intro y hy
    have h1 : Work.Spaces.w (3 * z / 2) ≤ Work.Spaces.w y := hmono y hy
    have h2 : (Work.Spaces.w (3 * z / 2)) ^ 2 ≤ (Work.Spaces.w y) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hw32pos) h1 2
    calc (Work.Spaces.w (3 * z / 2)) ^ 2 * (u y) ^ 2
        ≤ (Work.Spaces.w y) ^ 2 * (u y) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = (u y * Work.Spaces.w y) ^ 2 := by ring
  have hpt2 : ∀ y ∈ Set.Icc (z / 2) (3 * z / 2),
      (Work.Spaces.w (3 * z / 2)) ^ 2 * (u' y) ^ 2
        ≤ (2 / z) ^ 2 * (y * u' y * Work.Spaces.w y) ^ 2 := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1, hz]
    have hwy := hwpos y hy
    have h1 : Work.Spaces.w (3 * z / 2) ≤ Work.Spaces.w y := hmono y hy
    have hyinv : (1 / y) ≤ 2 / z := by
      rw [div_le_div_iff₀ hy0 hz]; linarith [hy.1]
    have hinv1 : (1 / Work.Spaces.w y) ≤ 1 / Work.Spaces.w (3 * z / 2) :=
      one_div_le_one_div_of_le hw32pos h1
    have hkey : (u' y) ^ 2 = (1 / y) ^ 2 * (1 / Work.Spaces.w y) ^ 2
        * (y * u' y * Work.Spaces.w y) ^ 2 := by
      field_simp
    have h2 : (1 / y) ^ 2 ≤ (2 / z) ^ 2 := pow_le_pow_left₀ (by positivity) hyinv 2
    have h3 : (1 / Work.Spaces.w y) ^ 2 ≤ (1 / Work.Spaces.w (3 * z / 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hinv1 2
    have h4 : (1 / y) ^ 2 * (1 / Work.Spaces.w y) ^ 2
        ≤ (2 / z) ^ 2 * (1 / Work.Spaces.w (3 * z / 2)) ^ 2 :=
      mul_le_mul h2 h3 (by positivity) (by positivity)
    have h5 := mul_le_mul_of_nonneg_right h4 (sq_nonneg (y * u' y * Work.Spaces.w y))
    calc (Work.Spaces.w (3 * z / 2)) ^ 2 * (u' y) ^ 2
        = (Work.Spaces.w (3 * z / 2)) ^ 2 * ((1 / y) ^ 2
            * (1 / Work.Spaces.w y) ^ 2 * (y * u' y * Work.Spaces.w y) ^ 2) := by rw [hkey]
      _ ≤ (Work.Spaces.w (3 * z / 2)) ^ 2 * ((2 / z) ^ 2
            * (1 / Work.Spaces.w (3 * z / 2)) ^ 2
            * (y * u' y * Work.Spaces.w y) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          calc (1 / y) ^ 2 * (1 / Work.Spaces.w y) ^ 2
                * (y * u' y * Work.Spaces.w y) ^ 2
              = ((1 / y) ^ 2 * (1 / Work.Spaces.w y) ^ 2)
                * (y * u' y * Work.Spaces.w y) ^ 2 := by ring
            _ ≤ ((2 / z) ^ 2 * (1 / Work.Spaces.w (3 * z / 2)) ^ 2)
                * (y * u' y * Work.Spaces.w y) ^ 2 := h5
            _ = (2 / z) ^ 2 * (1 / Work.Spaces.w (3 * z / 2)) ^ 2
                * (y * u' y * Work.Spaces.w y) ^ 2 := by ring
      _ = (2 / z) ^ 2 * (y * u' y * Work.Spaces.w y) ^ 2 := by
          field_simp
  -- the two window integrals
  have hIuu : IntervalIntegrable (fun y : ℝ => (u y) ^ 2) volume (z / 2) (3 * z / 2) :=
    ((hcont.pow 2).mono (le_of_eq (Set.uIcc_of_le hab.le))).intervalIntegrable
  have hIuu' : IntervalIntegrable (fun y : ℝ => (u' y) ^ 2) volume (z / 2) (3 * z / 2) :=
    ((hcont'.pow 2).mono (le_of_eq (Set.uIcc_of_le hab.le))).intervalIntegrable
  have hI1int : IntervalIntegrable (fun y : ℝ => (u y * Work.Spaces.w y) ^ 2) volume
      (z / 2) (3 * z / 2) :=
    (((hcont.mul hcontw).pow 2).mono (le_of_eq (Set.uIcc_of_le hab.le))).intervalIntegrable
  have hI2int : IntervalIntegrable
      (fun y : ℝ => (y * u' y * Work.Spaces.w y) ^ 2) volume (z / 2) (3 * z / 2) := by
    have hcont2 : ContinuousOn (fun y : ℝ => (y * u' y * Work.Spaces.w y) ^ 2)
        (Set.Icc (z / 2) (3 * z / 2)) := by
      refine ContinuousOn.pow ?_ 2
      exact (continuousOn_id.mul hcont').mul hcontw
    exact (hcont2.mono (le_of_eq (Set.uIcc_of_le hab.le))).intervalIntegrable
  have hint1 : (Work.Spaces.w (3 * z / 2)) ^ 2 * (∫ y in z / 2..3 * z / 2, (u y) ^ 2)
      ≤ I1 := by
    rw [hI1def, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (le_of_lt hab) (hIuu.const_mul _) hI1int hpt1
  have hint2 : (Work.Spaces.w (3 * z / 2)) ^ 2 * (∫ y in z / 2..3 * z / 2, (u' y) ^ 2)
      ≤ (2 / z) ^ 2 * I2 := by
    rw [hI2def, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (le_of_lt hab) (hIuu'.const_mul _)
      (hI2int.const_mul _) hpt2
  -- the two window integrals are nonnegative
  have hI1nn : 0 ≤ I1 := by
    rw [hI1def]
    exact intervalIntegral.integral_nonneg (le_of_lt hab) (fun y _ => sq_nonneg _)
  have hI2nn : 0 ≤ I2 := by
    rw [hI2def]
    exact intervalIntegral.integral_nonneg (le_of_lt hab) (fun y _ => sq_nonneg _)
  -- combine
  have hwz : Work.Spaces.w z ≤ 9 * Work.Spaces.w (3 * z / 2) := w_div_w_three_halves_le hz
  have h81 : (Work.Spaces.w z) ^ 2 ≤ 81 * (Work.Spaces.w (3 * z / 2)) ^ 2 := by
    have h0 : 0 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w]; positivity
    have h := pow_le_pow_left₀ h0 hwz 2
    calc (Work.Spaces.w z) ^ 2 ≤ (9 * Work.Spaces.w (3 * z / 2)) ^ 2 := h
      _ = 81 * (Work.Spaces.w (3 * z / 2)) ^ 2 := by ring
  have hstep : (Work.Spaces.w (3 * z / 2)) ^ 2 * (u z) ^ 2
      ≤ 2 / z * I1 + 8 / z * I2 := by
    have h1 : (Work.Spaces.w (3 * z / 2)) ^ 2 * (u z) ^ 2
        ≤ (Work.Spaces.w (3 * z / 2)) ^ 2
          * (2 * (z⁻¹ * (∫ y in z / 2..3 * z / 2, (u y) ^ 2)
            + z * (∫ y in z / 2..3 * z / 2, (u' y) ^ 2))) :=
      mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    have hsplit : (Work.Spaces.w (3 * z / 2)) ^ 2
          * (2 * (z⁻¹ * (∫ y in z / 2..3 * z / 2, (u y) ^ 2)
            + z * (∫ y in z / 2..3 * z / 2, (u' y) ^ 2)))
        = 2 / z * ((Work.Spaces.w (3 * z / 2)) ^ 2
              * (∫ y in z / 2..3 * z / 2, (u y) ^ 2))
          + 2 * z * ((Work.Spaces.w (3 * z / 2)) ^ 2
              * (∫ y in z / 2..3 * z / 2, (u' y) ^ 2)) := by ring
    rw [hsplit] at h1
    have hA : 2 / z * ((Work.Spaces.w (3 * z / 2)) ^ 2
          * (∫ y in z / 2..3 * z / 2, (u y) ^ 2)) ≤ 2 / z * I1 :=
      mul_le_mul_of_nonneg_left hint1 (by positivity)
    have hB : 2 * z * ((Work.Spaces.w (3 * z / 2)) ^ 2
          * (∫ y in z / 2..3 * z / 2, (u' y) ^ 2)) ≤ 2 * z * ((2 / z) ^ 2 * I2) :=
      mul_le_mul_of_nonneg_left hint2 (by linarith)
    have hB' : 2 * z * ((2 / z) ^ 2 * I2) = 8 / z * I2 := by
      field_simp
      ring
    linarith [h1, hA, hB, hB']
  calc (Work.Spaces.w z) ^ 2 * (u z) ^ 2
      ≤ 81 * (Work.Spaces.w (3 * z / 2)) ^ 2 * (u z) ^ 2 := by nlinarith [h81, sq_nonneg (u z)]
    _ = 81 * ((Work.Spaces.w (3 * z / 2)) ^ 2 * (u z) ^ 2) := by ring
    _ ≤ 81 * (2 / z * I1 + 8 / z * I2) := mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ ≤ 810 / z * (I1 + I2) := by
        have e1 : (162:ℝ) / z ≤ 810 / z := div_le_div_of_nonneg_right (by norm_num) hz.le
        have e2 : (648:ℝ) / z ≤ 810 / z := div_le_div_of_nonneg_right (by norm_num) hz.le
        have t1 : 162 / z * I1 ≤ 810 / z * I1 := mul_le_mul_of_nonneg_right e1 hI1nn
        have t2 : 648 / z * I2 ≤ 810 / z * I2 := mul_le_mul_of_nonneg_right e2 hI2nn
        have expand : (81:ℝ) * (2 / z * I1 + 8 / z * I2) = 162 / z * I1 + 648 / z * I2 := by ring
        have expand2 : (810:ℝ) / z * (I1 + I2) = 810 / z * I1 + 810 / z * I2 := by ring
        rw [expand, expand2]
        linarith [t1, t2]

end Work.FTS.StrongEps.E5Aux
