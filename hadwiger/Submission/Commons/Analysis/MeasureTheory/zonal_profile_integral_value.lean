import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Zonal profile integral value

Evaluates the one-dimensional integral
`∫_{(-1,1)} |t| · (∑_{j≤m} c_j t^{2m-2j} (1-t²)^j) · (1-t²)^((n-3)/2) dt`
in terms of the top coefficient `c_m`, under the three-term recurrence satisfied by the
coefficients of a zonal harmonic profile.

The proof reduces the integral to `∫₀¹ S(u)(1-u)^((n-3)/2) du` by the substitution
`u = t²`, expands the polynomial sum, and evaluates the resulting Beta-type integrals via
an integration-by-parts recursion; the recurrence on the `c_j` makes the sum telescope.
-/

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise BigOperators
open intervalIntegral

namespace Commons.Analysis.MeasureTheory

theorem zpi_integral_pow_mul_one_sub_rpow_succ (a : ℕ) (ha : 1 ≤ a) (γ : ℝ) (hγ : -1 < γ) :
    (γ + 1) * ∫ u in (0 : ℝ)..1, u ^ a * (1 - u) ^ γ
      = (a : ℝ) * ∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (γ + 1) := by
  set s : ℝ := γ + 1 with hs_def
  have hs : 0 < s := by rw [hs_def]; linarith
  have hsne : s ≠ 0 := ne_of_gt hs
  set c : ℝ := -(1/s) with hc_def
  have hu_cont : ContinuousOn (fun x : ℝ => x ^ a) (uIcc 0 1) := by fun_prop
  have hv_cont : ContinuousOn (fun x : ℝ => (1 - x) ^ s * c) (uIcc 0 1) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    exact (continuousOn_const.sub continuousOn_id).rpow_const (fun x _ => Or.inr (le_of_lt hs))
  have huu' : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivWithinAt (fun y : ℝ => y ^ a) ((a : ℝ) * x ^ (a - 1)) (Ioi x) x :=
    fun x _ => (hasDerivAt_pow a x).hasDerivWithinAt
  have hvv' : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivWithinAt (fun y : ℝ => (1 - y) ^ s * c) ((1 - x) ^ γ) (Ioi x) x := by
    intro x hx
    have hx1 : x < 1 := by simpa using hx.2
    have hbase : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have hrp := hbase.rpow_const (p := s) (Or.inl (by linarith))
    have hmul := hrp.mul_const c
    have hval : (-1) * s * (1 - x) ^ (s - 1) * c = (1 - x) ^ γ := by
      rw [hc_def]
      have hss : s - 1 = γ := by rw [hs_def]; ring
      rw [hss]
      field_simp
    rw [hval] at hmul
    exact hmul.hasDerivWithinAt
  have hu'_int : IntervalIntegrable (fun x : ℝ => (a : ℝ) * x ^ (a - 1)) volume (0:ℝ) 1 := by
    apply IntervalIntegrable.const_mul
    exact intervalIntegrable_pow (n := a - 1) (μ := volume) (a := (0:ℝ)) (b := 1)
  have hv'_int : IntervalIntegrable (fun x : ℝ => (1 - x) ^ γ) volume (0:ℝ) 1 := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (1:ℝ)) (b := (0:ℝ)) hγ
    have h2 := h.comp_sub_left 1
    simpa using h2
  have hmain := integral_deriv_mul_eq_sub_of_hasDeriv_right hu_cont hv_cont huu' hvv' hu'_int hv'_int
  have hbound : (fun x : ℝ => x ^ a) 1 * (fun x : ℝ => (1 - x) ^ s * c) 1
      - (fun x : ℝ => x ^ a) 0 * (fun x : ℝ => (1 - x) ^ s * c) 0 = 0 := by
    have h1 : (fun x : ℝ => (1 - x) ^ s * c) 1 = 0 := by
      change ((1:ℝ) - 1) ^ s * c = 0
      rw [show (1:ℝ) - 1 = 0 by norm_num, Real.zero_rpow hsne, zero_mul]
    have h0 : (fun x : ℝ => x ^ a) 0 = 0 := by
      change ((0:ℝ) ^ a) = 0
      exact zero_pow (by omega)
    rw [h1, h0]
    ring
  rw [hbound] at hmain
  have hsplit : (∫ x in (0:ℝ)..1, (fun y : ℝ => (a:ℝ) * y ^ (a-1)) x * (fun y : ℝ => (1 - y) ^ s * c) x
        + (fun y : ℝ => y ^ a) x * (fun y : ℝ => (1 - y) ^ γ) x)
      = (∫ x in (0:ℝ)..1, (fun y : ℝ => (a:ℝ) * y ^ (a-1)) x * (fun y : ℝ => (1 - y) ^ s * c) x)
        + (∫ x in (0:ℝ)..1, (fun y : ℝ => y ^ a) x * (fun y : ℝ => (1 - y) ^ γ) x) := by
    apply intervalIntegral.integral_add
    · apply IntervalIntegrable.mul_continuousOn hu'_int
      exact hv_cont
    · apply IntervalIntegrable.continuousOn_mul hv'_int
      fun_prop
  have hfirst : (∫ x in (0:ℝ)..1, (fun y : ℝ => (a:ℝ) * y ^ (a-1)) x * (fun y : ℝ => (1 - y) ^ s * c) x)
      = ((a:ℝ) * c) * ∫ x in (0:ℝ)..1, x ^ (a - 1) * (1 - x) ^ s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hsecond : (∫ x in (0:ℝ)..1, (fun y : ℝ => y ^ a) x * (fun y : ℝ => (1 - y) ^ γ) x)
      = ∫ x in (0:ℝ)..1, x ^ a * (1 - x) ^ γ := by
    apply intervalIntegral.integral_congr
    intro x _
    rfl
  rw [hsplit, hfirst, hsecond] at hmain
  have hcval : ((a:ℝ) * c) = -((a:ℝ)/s) := by rw [hc_def]; ring
  rw [hcval] at hmain
  have hI2 : (∫ x in (0:ℝ)..1, x ^ a * (1 - x) ^ γ) = ((a:ℝ)/s) * ∫ x in (0:ℝ)..1, x ^ (a - 1) * (1 - x) ^ s := by
    linarith
  have key : s * ∫ x in (0:ℝ)..1, x ^ a * (1 - x) ^ γ
      = (a:ℝ) * ∫ x in (0:ℝ)..1, x ^ (a-1) * (1 - x) ^ s := by
    rw [hI2]; field_simp
  exact key

theorem zpi_integral_abs_mul_comp_sq_Ioo {H : ℝ → ℝ} (hH : IntervalIntegrable H volume (0:ℝ) 1) :
    (∫ t : ℝ in Ioo (-1) 1, |t| * H (t^2)) = ∫ u : ℝ in (0:ℝ)..1, H u := by
  have hf : ContinuousOn (fun x : ℝ => x^2) (uIcc (0:ℝ) 1) := by fun_prop
  have hff' : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
    intro x _
    simpa using hasDerivAt_pow 2 x
  have hf' : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), (0:ℝ) ≤ 2*x := by
    intro x hx
    have : (0:ℝ) < x := by simpa using hx.1
    linarith
  have hcomp : IntervalIntegrable (fun x : ℝ => H (x^2) * (2*x)) volume (0:ℝ) 1 := by
    refine (integrable_comp_mul_deriv_iff_of_deriv_nonneg (a := (0:ℝ)) (b := 1)
      (f := fun x : ℝ => x^2) (f' := fun x : ℝ => 2*x) (g := H) hf hff' hf').mpr ?_
    simpa using hH
  have hsub_pos : ∫ x in (0:ℝ)..1, H (x^2) * (2*x) = ∫ u in (0:ℝ)..1, H u := by
    have h := integral_comp_mul_deriv_of_deriv_nonneg (a := (0:ℝ)) (b := 1)
      (f := fun x : ℝ => x^2) (f' := fun x : ℝ => 2*x) (g := H) hf hff' hf'
    simpa using h
  have hxH : IntervalIntegrable (fun x : ℝ => x * H (x^2)) volume (0:ℝ) 1 :=
    IntervalIntegrable.congr (f := fun x : ℝ => (1/2) * (H (x^2) * (2*x)))
      (g := fun x : ℝ => x * H (x^2)) (by intro x _; ring) (hcomp.const_mul (1/2))
  have hcomp_neg : IntervalIntegrable (fun x : ℝ => H (x^2) * (-(2*x))) volume (-1:ℝ) 0 := by
    have h0 : IntervalIntegrable (fun x : ℝ => H ((0 - x)^2) * (2*(0 - x)))
        volume (0:ℝ) (-1) := by
      simpa using hcomp.comp_sub_left 0
    have h1 : IntervalIntegrable (fun x : ℝ => H (x^2) * (-(2*x))) volume (0:ℝ) (-1) :=
      IntervalIntegrable.congr (f := fun x : ℝ => H ((0 - x)^2) * (2*(0 - x)))
        (g := fun x : ℝ => H (x^2) * (-(2*x))) (by intro x _; ring) h0
    exact h1.symm
  have hsub_neg : ∫ x in (-1:ℝ)..0, H (x^2) * (2*x) = -∫ u in (0:ℝ)..1, H u := by
    have hff'2 : ∀ x ∈ Ioo (min (-1:ℝ) 0) (max (-1:ℝ) 0),
        HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
      intro x _
      simpa using hasDerivAt_pow 2 x
    have hf'2 : ∀ x ∈ Ioo (min (-1:ℝ) 0) (max (-1:ℝ) 0), (2*x) ≤ 0 := by
      intro x hx
      have : x ≤ 0 := le_of_lt (by simpa using hx.2)
      linarith
    have h := integral_comp_mul_deriv_of_deriv_nonpos (a := (-1:ℝ)) (b := 0)
      (f := fun x : ℝ => x^2) (f' := fun x : ℝ => 2*x) (g := H) (by fun_prop) hff'2 hf'2
    rw [show ((-1:ℝ)^2) = 1 by norm_num, show ((0:ℝ)^2) = 0 by norm_num] at h
    rw [show (∫ u in (1:ℝ)..0, H u) = -∫ u in (0:ℝ)..1, H u from
      intervalIntegral.integral_symm (a := (0:ℝ)) (b := 1)] at h
    exact h
  have hpos : ∫ t in (0:ℝ)..1, |t| * H (t^2) = (1/2) * ∫ u in (0:ℝ)..1, H u := by
    calc ∫ t in (0:ℝ)..1, |t| * H (t^2)
        = ∫ t in (0:ℝ)..1, t * H (t^2) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht0 : (0:ℝ) ≤ t := by
            have hmem : t ∈ Icc (0:ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
            exact hmem.1
          show |t| * H (t^2) = t * H (t^2)
          rw [abs_of_nonneg ht0]
      _ = ∫ t in (0:ℝ)..1, (1/2) * (H (t^2) * (2*t)) := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
      _ = (1/2) * ∫ t in (0:ℝ)..1, H (t^2) * (2*t) := by
          rw [intervalIntegral.integral_const_mul]
      _ = (1/2) * ∫ u in (0:ℝ)..1, H u := by rw [hsub_pos]
  have hneg : ∫ t in (-1:ℝ)..0, |t| * H (t^2) = (1/2) * ∫ u in (0:ℝ)..1, H u := by
    calc ∫ t in (-1:ℝ)..0, |t| * H (t^2)
        = ∫ t in (-1:ℝ)..0, (-t) * H (t^2) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht0 : t ≤ 0 := by
            have hmem : t ∈ Icc (-1:ℝ) 0 := by
              simpa [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)] using ht
            exact hmem.2
          show |t| * H (t^2) = (-t) * H (t^2)
          rw [abs_of_nonpos ht0]
      _ = ∫ t in (-1:ℝ)..0, (1/2) * (H (t^2) * (-(2*t))) := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
      _ = (1/2) * ∫ t in (-1:ℝ)..0, H (t^2) * (-(2*t)) := by
          rw [intervalIntegral.integral_const_mul]
      _ = (1/2) * (∫ t in (-1:ℝ)..0, -(H (t^2) * (2*t))) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro t _
          ring
      _ = (1/2) * (-∫ t in (-1:ℝ)..0, H (t^2) * (2*t)) := by
          rw [intervalIntegral.integral_neg]
      _ = (1/2) * ∫ u in (0:ℝ)..1, H u := by rw [hsub_neg]; ring
  have hFpos : IntervalIntegrable (fun t : ℝ => |t| * H (t^2)) volume (0:ℝ) 1 :=
    IntervalIntegrable.congr (f := fun x : ℝ => x * H (x^2))
      (g := fun t : ℝ => |t| * H (t^2))
      (by
        intro x hx
        have hx0 : (0:ℝ) ≤ x := by
          have hmem : x ∈ Ioc (0:ℝ) 1 := by simpa [uIoc_of_le zero_le_one] using hx
          exact hmem.1.le
        simp only
        rw [abs_of_nonneg hx0]) hxH
  have hFneg : IntervalIntegrable (fun t : ℝ => |t| * H (t^2)) volume (-1:ℝ) 0 := by
    have hhalf : IntervalIntegrable (fun t : ℝ => (-t) * H (t^2)) volume (-1:ℝ) 0 :=
      IntervalIntegrable.congr (f := fun t : ℝ => (1/2) * (H (t^2) * (-(2*t))))
        (g := fun t : ℝ => (-t) * H (t^2)) (by intro t _; ring) (hcomp_neg.const_mul (1/2))
    refine IntervalIntegrable.congr (f := fun t : ℝ => (-t) * H (t^2))
      (g := fun t : ℝ => |t| * H (t^2)) ?_ hhalf
    intro x hx
    have hx0 : x ≤ 0 := by
      have hmem : x ∈ Ioc (-1:ℝ) 0 := by simpa [uIoc_of_le (by norm_num : (-1:ℝ) ≤ 0)] using hx
      exact hmem.2
    simp only
    rw [abs_of_nonpos hx0]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hFneg hFpos
  have hIoo : (∫ t : ℝ in Ioo (-1) 1, |t| * H (t^2))
      = ∫ t : ℝ in (-1:ℝ)..1, |t| * H (t^2) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  rw [hIoo, ← hsplit, hneg, hpos]
  ring

theorem zpi_telescope (m : ℕ) (T : ℕ → ℝ)
    (hrel : ∀ j : ℕ, j < m →
      (2 * (m : ℝ) - 2 * (j : ℝ) - 1) * T j + (2 * (j : ℝ) + 2) * T (j + 1) = 0) :
    (2 * (m : ℝ) - 1) * (∑ j ∈ Finset.range (m + 1), T j) + T m = 0 := by
  have hsum : (∑ j ∈ Finset.range m,
      ((2 * (m : ℝ) - 2 * (j : ℝ) - 1) * T j + (2 * (j : ℝ) + 2) * T (j + 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact hrel j (Finset.mem_range.mp hj)
  rw [Finset.sum_add_distrib] at hsum
  have hreindex : (∑ j ∈ Finset.range m, (2 * (j : ℝ) + 2) * T (j + 1))
      = ∑ k ∈ Finset.range (m + 1), (2 * (k : ℝ)) * T k := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have h0 : (∑ j ∈ Finset.range m, (2 * (m : ℝ) - 2 * (j : ℝ) - 1) * T j)
      + (∑ k ∈ Finset.range (m + 1), (2 * (k : ℝ)) * T k) = 0 := by
    rw [← hreindex]; exact hsum
  have h1 : (∑ k ∈ Finset.range (m + 1), (2 * (k : ℝ)) * T k)
      = (∑ k ∈ Finset.range m, (2 * (k : ℝ)) * T k) + 2 * (m : ℝ) * T m := by
    rw [Finset.sum_range_succ]
  have h2 : (∑ j ∈ Finset.range m, (2 * (m : ℝ) - 2 * (j : ℝ) - 1) * T j)
      + (∑ k ∈ Finset.range m, (2 * (k : ℝ)) * T k)
      = (2 * (m : ℝ) - 1) * (∑ k ∈ Finset.range m, T k) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hkey : (2 * (m : ℝ) - 1) * (∑ k ∈ Finset.range m, T k) + 2 * (m : ℝ) * T m = 0 := by
    rw [h1] at h0
    have h0' := h0
    rw [show (∑ j ∈ Finset.range m, (2 * (m : ℝ) - 2 * (j : ℝ) - 1) * T j)
          + ((∑ k ∈ Finset.range m, (2 * (k : ℝ)) * T k) + 2 * (m : ℝ) * T m)
        = ((∑ j ∈ Finset.range m, (2 * (m : ℝ) - 2 * (j : ℝ) - 1) * T j)
          + (∑ k ∈ Finset.range m, (2 * (k : ℝ)) * T k)) + 2 * (m : ℝ) * T m from by ring,
      h2] at h0'
    exact h0'
  have hgoal : (2 * (m : ℝ) - 1) * (∑ k ∈ Finset.range (m + 1), T k) + T m
      = (2 * (m : ℝ) - 1) * (∑ k ∈ Finset.range m, T k) + 2 * (m : ℝ) * T m := by
    rw [Finset.sum_range_succ]
    ring
  rw [hgoal, hkey]

theorem zonal_profile_integral_value
    (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (c : ℕ → ℝ)
    (hrec : ∀ j : ℕ, j < m →
      c j * (((2 * m - 2 * j : ℕ) : ℝ) * ((2 * m - 2 * j - 1 : ℕ) : ℝ))
        + c (j + 1) * ((2 * (j + 1) * (n + 2 * (j + 1) - 3) : ℕ) : ℝ) = 0) :
    (∫ t : ℝ in Set.Ioo (-1) 1,
        |t| * (∑ j ∈ Finset.range (m + 1), c j * t ^ (2 * m - 2 * j) * (1 - t ^ 2) ^ j)
          * (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2))
      = - c m / ((2 * (m : ℝ) - 1) * (m + ((n : ℝ) - 1) / 2)) := by
  set β : ℝ := ((n : ℝ) - 3) / 2 with hβdef
  have hβ : -1 < β := by
    rw [hβdef]
    have h2n : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let S : ℝ → ℝ := fun u => ∑ j ∈ Finset.range (m + 1), c j * u ^ (m - j) * (1 - u) ^ j
  let H : ℝ → ℝ := fun u => S u * (1 - u) ^ β
  let K : ℕ → ℝ := fun j => ∫ u in (0:ℝ)..1, u ^ (m - j) * (1 - u) ^ (β + (j : ℝ))
  -- Step 1: rewrite the integrand
  have hstep1 : (∫ t : ℝ in Set.Ioo (-1) 1,
        |t| * (∑ j ∈ Finset.range (m + 1), c j * t ^ (2 * m - 2 * j) * (1 - t ^ 2) ^ j)
          * (1 - t ^ 2) ^ β)
      = ∫ t : ℝ in Set.Ioo (-1) 1, |t| * H (t^2) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t _
    have hsum : (∑ j ∈ Finset.range (m + 1), c j * t ^ (2 * m - 2 * j) * (1 - t ^ 2) ^ j)
        = S (t^2) := by
      simp only [S]
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ m := by
        have : j < m + 1 := Finset.mem_range.mp hj
        omega
      have hexp : 2 * m - 2 * j = 2 * (m - j) := by omega
      rw [hexp, pow_mul]
    show |t| * (∑ j ∈ Finset.range (m + 1), c j * t ^ (2 * m - 2 * j) * (1 - t ^ 2) ^ j)
        * (1 - t ^ 2) ^ β = |t| * H (t ^ 2)
    rw [hsum]
    simp only [H]
    ring
  -- Step 2: substitution
  have hHint : IntervalIntegrable H volume (0:ℝ) 1 := by
    have h1 : IntervalIntegrable (fun u : ℝ => (1 - u) ^ β) volume (0:ℝ) 1 := by
      have h := intervalIntegral.intervalIntegrable_rpow' (a := (1:ℝ)) (b := (0:ℝ)) hβ
      simpa using h.comp_sub_left 1
    have h2 : ContinuousOn S (uIcc (0:ℝ) 1) := by
      have : Continuous S := by
        simp only [S]
        apply continuous_finsetSum
        intro j _
        fun_prop
      exact this.continuousOn
    simpa only [H] using h1.continuousOn_mul h2
  have hstep2 : (∫ t : ℝ in Set.Ioo (-1) 1, |t| * H (t^2)) = ∫ u in (0:ℝ)..1, H u :=
    zpi_integral_abs_mul_comp_sq_Ioo hHint
  -- Step 3: expand
  have hstep3 : (∫ u in (0:ℝ)..1, H u) = ∑ j ∈ Finset.range (m + 1), c j * K j := by
    have hexp : (∫ u in (0:ℝ)..1, H u)
        = ∫ u in (0:ℝ)..1,
            ∑ j ∈ Finset.range (m + 1), c j * u ^ (m - j) * (1 - u) ^ j * (1 - u) ^ β := by
      apply intervalIntegral.integral_congr
      intro u _
      simp only [H, S, Finset.sum_mul]
    rw [hexp, intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      have h2 : (∫ u in (0:ℝ)..1, u ^ (m - j) * (1 - u) ^ j * (1 - u) ^ β) = K j := by
        show (∫ u in (0:ℝ)..1, u ^ (m - j) * (1 - u) ^ j * (1 - u) ^ β)
          = ∫ u in (0:ℝ)..1, u ^ (m - j) * (1 - u) ^ (β + (j : ℝ))
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ x : ℝ, x ≠ 1 := by
          rw [MeasureTheory.ae_iff]
          rw [show {a : ℝ | ¬a ≠ 1} = {1} from by ext a; simp]
          exact measure_singleton 1
        filter_upwards [hne] with x hx hmem
        have hxle : x ≤ 1 := by
          have hmem' : x ∈ Ioc (0:ℝ) 1 := by simpa [uIoc_of_le zero_le_one] using hmem
          exact hmem'.2
        have hlt : x < 1 := lt_of_le_of_ne hxle hx
        have hpos : (0:ℝ) < 1 - x := by linarith
        have hkey : (1 - x) ^ (β + (j:ℝ)) = (1 - x) ^ β * (1 - x) ^ (j:ℝ) :=
          Real.rpow_add hpos β (j:ℝ)
        rw [hkey, Real.rpow_natCast (1 - x) j]
        ring
      rw [show (∫ u in (0:ℝ)..1, c j * u ^ (m - j) * (1 - u) ^ j * (1 - u) ^ β)
          = c j * ∫ u in (0:ℝ)..1, u ^ (m - j) * (1 - u) ^ j * (1 - u) ^ β from by
        rw [show (fun u : ℝ => c j * u ^ (m - j) * (1 - u) ^ j * (1 - u) ^ β)
            = fun u : ℝ => c j * (u ^ (m - j) * (1 - u) ^ j * (1 - u) ^ β) from by
          funext u; ring]
        rw [intervalIntegral.integral_const_mul]]
      rw [h2]
    · intro j _
      refine IntervalIntegrable.continuousOn_mul
        (f := fun u : ℝ => (1 - u) ^ β)
        (g := fun u : ℝ => c j * u ^ (m - j) * (1 - u) ^ j) ?_ ?_
      · have h := intervalIntegral.intervalIntegrable_rpow' (a := (1:ℝ)) (b := (0:ℝ)) hβ
        simpa using h.comp_sub_left 1
      · fun_prop
  -- Step 4: recurrence and telescoping
  have hKrec : ∀ j : ℕ, j < m →
      (β + (j : ℝ) + 1) * K j = (((m - j : ℕ)) : ℝ) * K (j + 1) := by
    intro j hj
    have hjm : j ≤ m := by omega
    have h1 : 1 ≤ m - j := by omega
    have hmain := zpi_integral_pow_mul_one_sub_rpow_succ (m - j) h1 (β + (j : ℝ)) (by linarith)
    have e1 : m - j - 1 = m - (j + 1) := by omega
    rw [e1] at hmain
    show (β + (j : ℝ) + 1) * (∫ u in (0:ℝ)..1, u ^ (m - j) * (1 - u) ^ (β + (j : ℝ)))
        = (((m - j : ℕ)) : ℝ)
          * ∫ u in (0:ℝ)..1, u ^ (m - (j + 1)) * (1 - u) ^ (β + ((j + 1 : ℕ) : ℝ))
    rw [show β + ((j + 1 : ℕ) : ℝ) = β + (j:ℝ) + 1 from by push_cast; ring]
    exact hmain
  have hTrel : ∀ j : ℕ, j < m →
      (2 * (m : ℝ) - 2 * (j : ℝ) - 1) * (c j * K j)
        + (2 * (j : ℝ) + 2) * (c (j + 1) * K (j + 1)) = 0 := by
    intro j hj
    have hjm : j ≤ m := by omega
    have hPpos : (0:ℝ) < β + (j : ℝ) + 1 := by linarith
    have hKj := hKrec j hj
    have hQ : (((m - j : ℕ)) : ℝ) = (m : ℝ) - (j : ℝ) := by rw [Nat.cast_sub hjm]
    have hKdiv : K j = ((m : ℝ) - (j : ℝ)) * K (j + 1) / (β + (j : ℝ) + 1) := by
      rw [eq_div_iff (ne_of_gt hPpos), mul_comm, hKj, hQ]
    have hrec_clean : c j * ((2 * (m : ℝ) - 2 * (j : ℝ)) * (2 * (m : ℝ) - 2 * (j : ℝ) - 1))
        + c (j + 1) * (2 * ((j : ℝ) + 1) * ((n : ℝ) + 2 * ((j : ℝ) + 1) - 3)) = 0 := by
      have h := hrec j hj
      have e1 : ((2 * m - 2 * j : ℕ) : ℝ) = 2 * (m : ℝ) - 2 * (j : ℝ) := by
        rw [Nat.cast_sub (by omega : 2 * j ≤ 2 * m)]
        push_cast
        ring
      have e2 : ((2 * m - 2 * j - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 2 * (j : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * m - 2 * j), e1]
        push_cast
        ring
      have e3 : ((2 * (j + 1) * (n + 2 * (j + 1) - 3) : ℕ) : ℝ)
          = 2 * ((j : ℝ) + 1) * ((n : ℝ) + 2 * ((j : ℝ) + 1) - 3) := by
        rw [Nat.cast_mul]
        congr 1
        · push_cast; ring
        · rw [Nat.cast_sub (by omega : 3 ≤ n + 2 * (j + 1))]
          push_cast
          ring
      rw [e1, e2, e3] at h
      exact h
    have hbracket : (2 * (m : ℝ) - 2 * (j : ℝ) - 1) * ((m : ℝ) - (j : ℝ)) * c j
        + 2 * (β + (j : ℝ) + 1) * ((j : ℝ) + 1) * c (j + 1) = 0 := by
      have h := hrec_clean
      rw [hβdef]
      have e3 : (n : ℝ) + 2 * ((j : ℝ) + 1) - 3 = (n : ℝ) + 2 * (j : ℝ) - 1 := by ring
      rw [e3] at h
      linear_combination (1/2) * h
    rw [hKdiv]
    have hfac : (2 * (m : ℝ) - 2 * (j : ℝ) - 1)
          * (c j * (((m : ℝ) - (j : ℝ)) * K (j + 1) / (β + (j : ℝ) + 1)))
        + (2 * (j : ℝ) + 2) * (c (j + 1) * K (j + 1))
        = K (j + 1) / (β + (j : ℝ) + 1)
          * ((2 * (m : ℝ) - 2 * (j : ℝ) - 1) * ((m : ℝ) - (j : ℝ)) * c j
            + 2 * (β + (j : ℝ) + 1) * ((j : ℝ) + 1) * c (j + 1)) := by
      field_simp
    rw [hfac, hbracket, mul_zero]
  have htel := zpi_telescope m (fun j => c j * K j) hTrel
  have hKm : K m = 1 / (β + (m : ℝ) + 1) := by
    show (∫ u in (0:ℝ)..1, u ^ (m - m) * (1 - u) ^ (β + (m : ℝ))) = 1 / (β + (m : ℝ) + 1)
    have hmm : m - m = 0 := by omega
    rw [hmm]
    simp only [pow_zero, one_mul]
    have hcomp := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1) (d := 1)
      (f := fun x : ℝ => x ^ (β + (m : ℝ)))
    rw [hcomp]
    simp only [sub_self, sub_zero]
    rw [integral_rpow (Or.inl (by linarith : -1 < β + (m : ℝ)))]
    rw [Real.one_rpow, Real.zero_rpow (by linarith : β + (m : ℝ) + 1 ≠ 0)]
    ring
  have hsum : (∑ j ∈ Finset.range (m + 1), c j * K j) = - c m * K m / (2 * (m : ℝ) - 1) := by
    have hne : (2 * (m : ℝ) - 1) ≠ 0 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h]; norm_num
      · have hm1 : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast h
        intro hh; linarith
    have h2 : (2 * (m : ℝ) - 1) * (∑ j ∈ Finset.range (m + 1), c j * K j) = - c m * K m := by
      linarith [htel]
    rw [eq_div_iff hne, mul_comm]
    exact h2
  rw [hstep1, hstep2, hstep3, hsum, hKm, hβdef]
  field_simp
  ring


end Commons.Analysis.MeasureTheory