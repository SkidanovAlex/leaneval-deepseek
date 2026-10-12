import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lower bound for `∫_{-R}^{R} |cos (t u)| du`

We prove

`Work.SmallBoxBridge.Kernel.absCosIntervalLower`:

for `t > 0` and `R ≥ 0`, the integral of `|cos (t ·)|` over the symmetric interval
`[-R, R]` dominates the length `R`.

By the substitution `v = t u` (legitimate as `t > 0`) the statement is equivalent to
the scalar inequality `S ≤ ∫ v in (-S)..S, |cos v|` for all `S ≥ 0`, i.e. (by evenness
of `|cos|`) to `S ≤ 2 ∫_0^S |cos v| dv`.

The latter is proved as follows.

* `|cos|` has period `π` and `∫_0^π |cos| = 2`; iterating the resulting shift identity
  gives `∫_0^{r+nπ} |cos| = ∫_0^r |cos| + 2n`.
* Writing `S = r + nπ` with `n = ⌊S/π⌋` and `0 ≤ r < π` it therefore suffices to
  know the base case `r ≤ 2 ∫_0^r |cos|` for `0 ≤ r ≤ π`, which is a one variable
  estimate: on `[0, π/2]` the integral equals `sin r` and Jordan's inequality
  `2r/π ≤ sin r` gives the claim, while on `[π/2, π]` the integral equals `2 - sin r`
  and the claim follows from the elementary bound `2 sin u ≤ 4 - π + u` (`0 ≤ u ≤ π/2`).
-/

namespace Work.SmallBoxBridge.Kernel

namespace AbsCosIntervalAux

open MeasureTheory Set

/-- `|cos|` is periodic with period `π`. -/
lemma periodic_abs_cos : Function.Periodic (fun v : ℝ => |Real.cos v|) Real.pi := by
  intro v
  change |Real.cos (v + Real.pi)| = |Real.cos v|
  rw [Real.cos_add_pi, abs_neg]

/-- `∫_0^{π/2} |cos| = 1`. -/
lemma integral_abs_cos_zero_half : ∫ v in (0 : ℝ)..(Real.pi / 2), |Real.cos v| = 1 := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h : ∫ v in (0 : ℝ)..(Real.pi / 2), |Real.cos v|
      = ∫ v in (0 : ℝ)..(Real.pi / 2), Real.cos v := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at hx
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  rw [h, integral_cos, Real.sin_pi_div_two, Real.sin_zero]
  norm_num

/-- `∫_{π/2}^{π} |cos| = 1`. -/
lemma integral_abs_cos_half_pi : ∫ v in (Real.pi / 2)..Real.pi, |Real.cos v| = 1 := by
  have hle : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have h : ∫ v in (Real.pi / 2)..Real.pi, |Real.cos v|
      = ∫ v in (Real.pi / 2)..Real.pi, -Real.cos v := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at hx
    apply abs_of_nonpos
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi / 2) (y := x)
      (by linarith [Real.pi_pos]) hx.2 hx.1
    rwa [Real.cos_pi_div_two] at hc
  rw [h, intervalIntegral.integral_neg, integral_cos, Real.sin_pi, Real.sin_pi_div_two]
  norm_num

/-- `∫_0^{π} |cos| = 2`. -/
lemma integral_abs_cos_pi : ∫ v in (0 : ℝ)..Real.pi, |Real.cos v| = 2 := by
  have hcont : ∀ a b : ℝ, IntervalIntegrable (fun v : ℝ => |Real.cos v|) volume a b :=
    fun a b => (continuous_abs.comp Real.continuous_cos).intervalIntegrable a b
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hcont 0 (Real.pi / 2)) (hcont (Real.pi / 2) Real.pi)
  rw [← hadj, integral_abs_cos_zero_half, integral_abs_cos_half_pi]
  norm_num

/-- Shifting the upper endpoint by a full period: `∫_0^{x+π} |cos| = ∫_0^x |cos| + 2`. -/
lemma integral_abs_cos_add_pi (x : ℝ) :
    ∫ v in (0 : ℝ)..(x + Real.pi), |Real.cos v| = (∫ v in (0 : ℝ)..x, |Real.cos v|) + 2 := by
  have hcont : ∀ a b : ℝ, IntervalIntegrable (fun v : ℝ => |Real.cos v|) volume a b :=
    fun a b => (continuous_abs.comp Real.continuous_cos).intervalIntegrable a b
  have h := periodic_abs_cos.intervalIntegral_add_eq_add (t := (0 : ℝ)) (s := x) hcont
  rw [h]
  simp only [zero_add]
  rw [integral_abs_cos_pi]

/-- Iterating the shift identity: `∫_0^{r+nπ} |cos| = ∫_0^r |cos| + 2n`. -/
lemma integral_abs_cos_nat (n : ℕ) (r : ℝ) :
    ∫ v in (0 : ℝ)..(r + n * Real.pi), |Real.cos v|
      = (∫ v in (0 : ℝ)..r, |Real.cos v|) + 2 * n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hstep : r + ((k + 1 : ℕ) : ℝ) * Real.pi = (r + (k : ℝ) * Real.pi) + Real.pi := by
      push_cast; ring
    rw [hstep, integral_abs_cos_add_pi, ih]
    push_cast
    ring

/-- The elementary bound `2 sin u ≤ 4 - π + u` on `[0, π/2]`. -/
lemma two_mul_sin_le (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ Real.pi / 2) :
    2 * Real.sin u ≤ 4 - Real.pi + u := by
  have hnum : Real.sqrt 3 + 2 * Real.pi / 3 < 4 := by
    have hpi := Real.pi_lt_d2
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsnn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    nlinarith [hpi, hs, hsnn]
  rcases le_total u (Real.pi / 3) with h | h
  · -- `cos ≥ 1/2` on `[u, π/3]`, hence `sin (π/3) - sin u ≥ (π/3 - u)/2`.
    have hcos : ∀ w ∈ Set.Icc u (Real.pi / 3), (1 / 2 : ℝ) ≤ Real.cos w := by
      intro w hw
      have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := w) (y := Real.pi / 3)
        (by linarith [hu0, hw.1]) (by linarith [Real.pi_pos]) hw.2
      rwa [Real.cos_pi_div_three] at hc
    have hint1 : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume u (Real.pi / 3) :=
      continuous_const.intervalIntegrable _ _
    have hint2 : IntervalIntegrable Real.cos volume u (Real.pi / 3) :=
      Real.continuous_cos.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on h hint1 hint2 hcos
    rw [intervalIntegral.integral_const, smul_eq_mul, integral_cos,
      Real.sin_pi_div_three] at hmono
    nlinarith [hmono, hnum]
  · -- `cos ≤ 1/2` on `[π/3, u]`, hence `sin u - sin (π/3) ≤ (u - π/3)/2`.
    have hcos : ∀ w ∈ Set.Icc (Real.pi / 3) u, Real.cos w ≤ (1 / 2 : ℝ) := by
      intro w hw
      have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi / 3) (y := w)
        (by linarith [Real.pi_pos]) (by linarith [hw.2, hu, Real.pi_pos]) hw.1
      rwa [Real.cos_pi_div_three] at hc
    have hint1 : IntervalIntegrable Real.cos volume (Real.pi / 3) u :=
      Real.continuous_cos.intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume (Real.pi / 3) u :=
      continuous_const.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on h hint1 hint2 hcos
    rw [intervalIntegral.integral_const, smul_eq_mul, integral_cos,
      Real.sin_pi_div_three] at hmono
    nlinarith [hmono, hnum]

/-- Base case of the period reduction: `r ≤ 2 ∫_0^r |cos|` for `0 ≤ r ≤ π`. -/
lemma base_le (r : ℝ) (hr0 : 0 ≤ r) (hrπ : r ≤ Real.pi) :
    r ≤ 2 * ∫ v in (0 : ℝ)..r, |Real.cos v| := by
  rcases le_total r (Real.pi / 2) with hr | hr
  · -- `|cos| = cos` on `[0, r]`, so the integral is `sin r`; use Jordan's inequality.
    have hir : ∫ v in (0 : ℝ)..r, |Real.cos v| = Real.sin r := by
      have h : ∫ v in (0 : ℝ)..r, |Real.cos v| = ∫ v in (0 : ℝ)..r, Real.cos v := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hr0, Set.mem_Icc] at hx
        exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [hx.1], by linarith [hx.2, hr, Real.pi_pos]⟩)
      rw [h, integral_cos, Real.sin_zero]
      ring
    rw [hir]
    have hj := Real.mul_le_sin hr0 hr
    have hpi4 : (1 : ℝ) ≤ 4 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      linarith [Real.pi_lt_four]
    have h1 : r ≤ 4 / Real.pi * r := by
      simpa using mul_le_mul_of_nonneg_right hpi4 hr0
    have h2 : 4 / Real.pi * r ≤ 2 * Real.sin r := by
      have h := mul_le_mul_of_nonneg_left hj (by norm_num : (0 : ℝ) ≤ 2)
      have e : 2 * (2 / Real.pi * r) = 4 / Real.pi * r := by ring
      linarith [h, e]
    linarith [h1, h2]
  · -- `∫_0^r |cos| = 2 - sin r`; the bound `2 sin u ≤ 4 - π + u` with `u = π - r`.
    have hmid : ∫ v in (Real.pi / 2)..r, |Real.cos v| = 1 - Real.sin r := by
      have h : ∫ v in (Real.pi / 2)..r, |Real.cos v| = ∫ v in (Real.pi / 2)..r, -Real.cos v := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hr, Set.mem_Icc] at hx
        apply abs_of_nonpos
        have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi / 2) (y := x)
          (by linarith [Real.pi_pos]) (by linarith [hx.2, hrπ]) hx.1
        rwa [Real.cos_pi_div_two] at hc
      rw [h, intervalIntegral.integral_neg, integral_cos, Real.sin_pi_div_two]
      ring
    have hgr : ∫ v in (0 : ℝ)..r, |Real.cos v| = 2 - Real.sin r := by
      have hcont : ∀ a b : ℝ, IntervalIntegrable (fun v : ℝ => |Real.cos v|) volume a b :=
        fun a b => (continuous_abs.comp Real.continuous_cos).intervalIntegrable a b
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (hcont 0 (Real.pi / 2)) (hcont (Real.pi / 2) r)
      rw [← hadj, integral_abs_cos_zero_half, hmid]
      ring
    rw [hgr]
    have hkey := two_mul_sin_le (Real.pi - r) (by linarith) (by linarith)
    have hsin : Real.sin r = Real.sin (Real.pi - r) := by rw [Real.sin_pi_sub]
    rw [hsin]
    linarith

/-- Evenness: `∫_{-S}^{S} |cos| = 2 ∫_0^S |cos|`. -/
lemma integral_abs_cos_symm (S : ℝ) :
    ∫ v in (-S)..S, |Real.cos v| = 2 * ∫ v in (0 : ℝ)..S, |Real.cos v| := by
  have hcont : ∀ a b : ℝ, IntervalIntegrable (fun v : ℝ => |Real.cos v|) volume a b :=
    fun a b => (continuous_abs.comp Real.continuous_cos).intervalIntegrable a b
  have hneg : ∫ v in (-S)..(0 : ℝ), |Real.cos v| = ∫ v in (0 : ℝ)..S, |Real.cos v| := by
    have hc := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := S)
      (f := fun v => |Real.cos v|)
    rw [neg_zero] at hc
    rw [← hc]
    apply intervalIntegral.integral_congr
    intro x _
    simp [Real.cos_neg]
  have hadj := intervalIntegral.integral_add_adjacent_intervals (hcont (-S) 0) (hcont 0 S)
  rw [← hadj, hneg]
  ring

/-- Scalar core: for `S ≥ 0`, `S ≤ ∫ v in (-S)..S, |cos v|`. -/
lemma le_integral_abs_cos (S : ℝ) (hS : 0 ≤ S) :
    S ≤ ∫ v in (-S)..S, |Real.cos v| := by
  set n : ℕ := ⌊S / Real.pi⌋₊ with hn
  set r : ℝ := S - n * Real.pi with hr
  have hnle : (n : ℝ) * Real.pi ≤ S := by
    have h1 : (n : ℝ) ≤ S / Real.pi := by
      rw [hn]
      exact Nat.floor_le (div_nonneg hS Real.pi_pos.le)
    exact (le_div_iff₀ Real.pi_pos).mp h1
  have hnlt : S < ((n : ℝ) + 1) * Real.pi := by
    have h1 : S / Real.pi < (n : ℝ) + 1 := by
      rw [hn]
      exact Nat.lt_floor_add_one (S / Real.pi)
    exact (div_lt_iff₀ Real.pi_pos).mp h1
  have hr0 : 0 ≤ r := by simp only [hr]; linarith
  have hrπ : r < Real.pi := by simp only [hr]; nlinarith
  have hbase : r ≤ 2 * ∫ v in (0 : ℝ)..r, |Real.cos v| := base_le r hr0 hrπ.le
  have hS2 : S = r + n * Real.pi := by simp only [hr]; ring
  have hdec : ∫ v in (0 : ℝ)..S, |Real.cos v|
      = (∫ v in (0 : ℝ)..r, |Real.cos v|) + 2 * n := by
    rw [hS2, integral_abs_cos_nat]
  rw [integral_abs_cos_symm, hdec]
  have hnpi : (n : ℝ) * Real.pi ≤ 4 * n := by
    have h : (n : ℝ) * Real.pi ≤ (n : ℝ) * 4 :=
      mul_le_mul_of_nonneg_left Real.pi_lt_four.le (Nat.cast_nonneg n)
    linarith
  nlinarith [hbase, hnpi, hS2]

end AbsCosIntervalAux

open AbsCosIntervalAux

theorem absCosIntervalLower (t R : ℝ) (ht : 0 < t) (hR : 0 ≤ R) :
    R ≤ ∫ u in (-R)..R, |Real.cos (t * u)| := by
  have hsub : ∫ u in (-R)..R, |Real.cos (t * u)|
      = t⁻¹ * ∫ v in (-(t * R))..(t * R), |Real.cos v| := by
    rw [intervalIntegral.integral_comp_mul_left (fun v : ℝ => |Real.cos v|) (ne_of_gt ht)]
    simp only [smul_eq_mul]
    rw [show t * (-R) = -(t * R) by ring]
  rw [hsub]
  have hkey := le_integral_abs_cos (t * R) (mul_nonneg ht.le hR)
  have hmul : t⁻¹ * (t * R) ≤ t⁻¹ * ∫ v in (-(t * R))..(t * R), |Real.cos v| :=
    mul_le_mul_of_nonneg_left hkey (inv_nonneg.mpr ht.le)
  have heq : t⁻¹ * (t * R) = R := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht), one_mul]
  linarith [hmul, heq]

end Work.SmallBoxBridge.Kernel
