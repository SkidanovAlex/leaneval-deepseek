import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs
import Submission.Work.OddRadon.Chapter
import Submission.Work.OddCurve.LowSlope.radon_data_interface
import Submission.Work.OddCurve.LowSlope.sphereArea_eq_ballVol
import Submission.Work.OddCurve.LowSlope.refConst_eq_inertia

/-!
# The Radon data of the semicircle (the ball's second moments)

`Work.OddRadon.radonProfile (2n+1) γ c` is the one-variable spherical Radon transform with the
real exponent `(2n+1)/2 - 2 = n - 3/2`.  In this file we compute it for the *quadratic* profile
`γ u = u²` — i.e. for the second moment `w ↦ w₁²` of the unit ball — and find the closed value

`radonProfile (2n+1) (·)² c = (2n+2) · |B^{2n-1}| · ballInertiaConst n · c²`.

The whole content is one-dimensional.  Writing `K = ∫_{-1}^{1} u² (1-u²)^{n-1} / √(1-u²) du` for
the singular integral that is the data, the statement reduces (via `radonProfile_eq_natpow` and
`|S^{m}| = (m+1)|B^{m+1}|`) to the identity

`(2n-1) K = (2n+2) ballInertiaConst n`,

whose proof is the elementary integration by parts with the primitive `u (1-u²)^{n-1} √(1-u²)`:
its derivative is `(1-u²)^{n-1}√(1-u²) - (2n-1) u² (1-u²)^{n-1}/√(1-u²)` and vanishes at `±1`.
Splitting the first piece pointwise as `u²(1-u²)^{n-1}√(1-u²) + (1-u²)^n √(1-u²)` and using the
already-established `refConst n = (2n+1) ballInertiaConst n` gives the claim.

The integrability of the singular integrand `u²(1-u²)^{n-1}/√(1-u²)` is obtained by dominating it
by `√(1-u²)⁻¹`, whose interval-integrability is Mathlib's
`Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- `x^k √x = x^(k + 1/2)` for `x ≥ 0`. -/
private lemma pow_mul_sqrt_eq_rpow' {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x ^ k * Real.sqrt x = x ^ ((k : ℝ) + 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x k]
  exact (Real.rpow_add' hx (by positivity)).symm

/-- **Integrability of the singular integrand of `K`.** -/
private lemma intervalIntegrable_sq_pow_div_sqrt (n : ℕ) :
    IntervalIntegrable (fun u : ℝ => u ^ 2 * (1 - u ^ 2) ^ (n - 1) / Real.sqrt (1 - u ^ 2))
      volume (-1) 1 := by
  have hb : IntervalIntegrable (fun x : ℝ => √(1 - x ^ 2)⁻¹) volume (-1 : ℝ) 1 :=
    Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  have hbase : IntervalIntegrable (fun x : ℝ => (Real.sqrt (1 - x ^ 2))⁻¹) volume (-1 : ℝ) 1 := by
    simpa only [Real.sqrt_inv] using hb
  have hg : ContinuousOn (fun u : ℝ => u ^ 2 * (1 - u ^ 2) ^ (n - 1)) (Set.uIcc (-1 : ℝ) 1) := by
    fun_prop
  have h := hbase.continuousOn_mul hg
  simpa only [div_eq_mul_inv] using h

/-- The derivative of the primitive `u ↦ u (1-u²)^{n-1} √(1-u²)`. -/
private lemma hasDerivAt_prim (n : ℕ) (hn : 1 ≤ n) {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun u : ℝ => u * ((1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2)))
      ((1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2)
        - (2 * (n : ℝ) - 1) *
            (u ^ 2 * (1 - u ^ 2) ^ (n - 1) / Real.sqrt (1 - u ^ 2))) u := by
  have h1pos : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have h1ne : (1 : ℝ) - u ^ 2 ≠ 0 := ne_of_gt h1pos
  have hbase : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (0 - 2 * u) u := by
    have h := (hasDerivAt_const (x := u) (c := (1 : ℝ))).sub ((hasDerivAt_id u).pow 2)
    have hfun : ((fun _ : ℝ => (1 : ℝ)) - id ^ 2) = fun y : ℝ => 1 - y ^ 2 := by
      funext y; simp
    rw [hfun] at h
    simpa using h
  set a : ℝ := (((n - 1 : ℕ) : ℝ) + 1 / 2) with hadef
  have hin : HasDerivAt (fun y : ℝ => (1 - y ^ 2) ^ a)
      (a * (1 - u ^ 2) ^ (a - 1) * (0 - 2 * u)) u := by
    have hf : HasDerivAt (fun x : ℝ => x ^ a) (a * (1 - u ^ 2) ^ (a - 1)) (1 - u ^ 2) :=
      Real.hasDerivAt_rpow_const (Or.inl h1ne)
    simpa only [Function.comp_def] using HasDerivAt.comp u hf hbase
  have hnat : HasDerivAt (fun y : ℝ => (1 - y ^ 2) ^ (n - 1) * Real.sqrt (1 - y ^ 2))
      (a * (1 - u ^ 2) ^ (a - 1) * (0 - 2 * u)) u := by
    refine hin.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hu] with y hy
    have hy1 : 0 ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    rw [hadef]
    exact pow_mul_sqrt_eq_rpow' hy1 (n - 1)
  have hG : HasDerivAt (fun y : ℝ => y * ((1 - y ^ 2) ^ (n - 1) * Real.sqrt (1 - y ^ 2)))
      (1 * ((1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2))
        + u * (a * (1 - u ^ 2) ^ (a - 1) * (0 - 2 * u))) u :=
    (hasDerivAt_id u).mul hnat
  refine hG.congr_deriv ?_
  have hpow : (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2) = (1 - u ^ 2) ^ a := by
    rw [hadef]
    exact pow_mul_sqrt_eq_rpow' h1pos.le (n - 1)
  have hpow' : (1 - u ^ 2) ^ (n - 1) / Real.sqrt (1 - u ^ 2) = (1 - u ^ 2) ^ (a - 1) := by
    have hm : (1 - u ^ 2) ^ (n - 1) / Real.sqrt (1 - u ^ 2)
        = (1 - u ^ 2) ^ (((n - 1 : ℕ) : ℝ) - 1 / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (1 - u ^ 2) (n - 1), ← Real.rpow_sub h1pos]
    rw [hm, hadef,
      show (((n - 1 : ℕ) : ℝ) + 1 / 2) - 1 = (((n - 1 : ℕ) : ℝ) - 1 / 2) by ring]
  have ha2 : 2 * a = 2 * (n : ℝ) - 1 := by
    rw [hadef]
    push_cast [Nat.cast_sub hn]
    ring
  rw [hpow, mul_div_assoc, hpow', ← ha2]
  ring

/-- The one-dimensional identity behind the semicircle data:
`(2n-1) ∫ u² (1-u²)^{n-1}/√(1-u²) = (2n+2) ballInertiaConst n`. -/
private lemma key_integral (n : ℕ) (hn : 1 ≤ n) :
    (2 * (n : ℝ) - 1) *
        (∫ u in (-1 : ℝ)..1, u ^ 2 * (1 - u ^ 2) ^ (n - 1) / Real.sqrt (1 - u ^ 2))
      = (2 * (n : ℝ) + 2) * ballInertiaConst n := by
  set K : ℝ := ∫ u in (-1 : ℝ)..1, u ^ 2 * (1 - u ^ 2) ^ (n - 1) / Real.sqrt (1 - u ^ 2) with hK
  set J : ℝ := ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2) with hJ
  have hKint : IntervalIntegrable
      (fun u : ℝ => u ^ 2 * (1 - u ^ 2) ^ (n - 1) / Real.sqrt (1 - u ^ 2)) volume (-1 : ℝ) 1 :=
    intervalIntegrable_sq_pow_div_sqrt n
  have hJint : IntervalIntegrable
      (fun u : ℝ => (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2)) volume (-1 : ℝ) 1 :=
    (by fun_prop : Continuous (fun u : ℝ => (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2))
      ).intervalIntegrable (-1) 1
  have hprim : ContinuousOn
      (fun u : ℝ => u * ((1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2))) (Set.Icc (-1 : ℝ) 1) := by
    fun_prop
  have hint_deriv : IntervalIntegrable
      (fun u : ℝ => (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2)
        - (2 * (n : ℝ) - 1) * (u ^ 2 * (1 - u ^ 2) ^ (n - 1) / Real.sqrt (1 - u ^ 2)))
      volume (-1 : ℝ) 1 :=
    hJint.sub (hKint.const_mul _)
  have hFTC : (∫ u in (-1 : ℝ)..1, ((1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2)
      - (2 * (n : ℝ) - 1) * (u ^ 2 * (1 - u ^ 2) ^ (n - 1) / Real.sqrt (1 - u ^ 2)))) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hprim
      (fun u hu => hasDerivAt_prim n hn hu) hint_deriv]
    simp
  have h1 : J - (2 * (n : ℝ) - 1) * K = 0 := by
    have h := hFTC
    rw [intervalIntegral.integral_sub hJint (hKint.const_mul _),
      intervalIntegral.integral_const_mul] at h
    rw [← hJ, ← hK] at h
    exact h
  have hJsplit : J = ballInertiaConst n + Work.OddCurve.refConst n := by
    have hpt : (fun u : ℝ => (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2))
        = fun u : ℝ => u ^ 2 * (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2)
            + (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2) := by
      funext u
      have hpoweq : (1 - u ^ 2) ^ n = (1 - u ^ 2) ^ (n - 1) * (1 - u ^ 2) := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpoweq]; ring
    rw [hJ, hpt, intervalIntegral.integral_add
      ((by fun_prop : Continuous
        (fun u : ℝ => u ^ 2 * (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2))
        ).intervalIntegrable (-1) 1)
      ((by fun_prop : Continuous
        (fun u : ℝ => (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2))
        ).intervalIntegrable (-1) 1)]
    simp only [ballInertiaConst, Work.OddCurve.refConst_def]
  have hJval : J = (2 * (n : ℝ) + 2) * ballInertiaConst n := by
    rw [hJsplit, refConst_eq_inertia n hn]
    ring
  have h2 : (2 * (n : ℝ) - 1) * K = J := by linarith [h1]
  rw [h2, hJval]

theorem radonProfile_data_semicircle (n : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2) c
      = (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) * ballInertiaConst n * c ^ 2 := by
  rw [radonProfile_eq_natpow n hn (fun u : ℝ => u ^ 2) hc]
  have hci : (∫ ν in (-1 : ℝ)..1, (1 - ν ^ 2) ^ (n - 1) * (c * ν) ^ 2 / Real.sqrt (1 - ν ^ 2))
      = c ^ 2 * ∫ ν in (-1 : ℝ)..1, ν ^ 2 * (1 - ν ^ 2) ^ (n - 1) / Real.sqrt (1 - ν ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun ν _ => ?_)
    ring
  rw [hci]
  have hsphere := sphereArea_eq_ballVol (2 * n - 2)
  have hbcast : 2 * n - 2 + 1 = 2 * n - 1 := by omega
  have hcast : (((2 * n - 2 : ℕ) : ℝ) + 1) = 2 * (n : ℝ) - 1 := by
    have h2 : 2 * n - 2 = 2 * (n - 1) := by omega
    rw [h2, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hn]
    ring
  rw [hsphere, hbcast, hcast]
  have hKval := key_integral n hn
  rw [show (2 * (n : ℝ) - 1) * ballVol (2 * n - 1) *
      (c ^ 2 * (∫ ν in (-1 : ℝ)..1, ν ^ 2 * (1 - ν ^ 2) ^ (n - 1) / Real.sqrt (1 - ν ^ 2)))
      = (ballVol (2 * n - 1) * c ^ 2) *
        ((2 * (n : ℝ) - 1) *
          (∫ ν in (-1 : ℝ)..1, ν ^ 2 * (1 - ν ^ 2) ^ (n - 1) / Real.sqrt (1 - ν ^ 2)))
      from by ring]
  rw [hKval]
  ring

end

end Work.OddCurve.LowSlope
