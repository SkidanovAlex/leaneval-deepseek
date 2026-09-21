import Mathlib
import Submission.Work.OddCurve.Defs

/-!
# Derivative of `u ↦ (max (R u) 0) ^ n * √(max (R u) 0)`

The map `x ↦ (max x 0) ^ p` (real power) is differentiable at **every** real `x` as soon as
`p > 1`: away from `0` it agrees with `x ^ p` (on `(0, ∞)`) or is locally constant (on `(-∞, 0)`),
and at `0` the derivative is `0` because `p > 1` — this is the content of
`Work.OddCurve.hasDerivAt_max_zero_rpow`.  Note that `p > 1` is sharp: for `p = 1` the map is
`max · 0`, which is not differentiable at `0`.

Composing with `R` and using `x ^ n * √x = x ^ (n + 1/2)` for `x ≥ 0`
(`Work.OddCurve.pow_mul_sqrt_eq_rpow`) gives the derivative of `u ↦ (max (R u) 0) ^ n * √R u⁺`,
which is the integrand of the moment equations `(A)`, `(B)` of the odd case
(`Work.OddCurve.momentA`, `Work.OddCurve.momentB`) as a function of the slope.
-/

namespace Work.OddCurve

noncomputable section

open Filter
open scoped Topology

/-- **The elementary powers identity.**  For `x ≥ 0` and `n : ℕ`, `x ^ n * √x = x ^ (n + 1/2)`.
(This is the identity that turns the radicand expression `R ^ n * √R` of the moment equations into
a single real power.) -/
lemma pow_mul_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.sqrt x = x ^ ((n : ℝ) + 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x n]
  exact (Real.rpow_add' hx (by positivity)).symm

/-- **`x ↦ (max x 0) ^ p` is differentiable everywhere when `p > 1`**, with derivative
`p * (max x 0) ^ (p - 1)`.

The three geometric cases: for `x < 0` the map is locally constant `0 ^ p = 0` (so the displayed
derivative is `p * 0 ^ (p-1) = 0` because `p - 1 ≠ 0`); for `x > 0` it agrees near `x` with `y ^ p`;
and at `x = 0` the two one-sided derivatives both vanish (the right-hand one because `p > 1` forces
`(0^p)' = p * 0 ^ (p-1) = 0`), so the one-sided statements glue along `(-∞, 0] ∪ [0, ∞) = ℝ`. -/
lemma hasDerivAt_max_zero_rpow {p : ℝ} (hp : 1 < p) (v : ℝ) :
    HasDerivAt (fun x : ℝ => (max x 0) ^ p) (p * (max v 0) ^ (p - 1)) v := by
  have hpm1 : p - 1 ≠ 0 := by linarith
  rcases lt_trichotomy v 0 with hv | hv | hv
  · -- `v < 0`: the map is locally the constant `0 ^ p`.
    have hev : (fun x : ℝ => (max x 0) ^ p) =ᶠ[𝓝 v] (fun _ => (0 : ℝ) ^ p) := by
      filter_upwards [isOpen_Iio.mem_nhds hv] with x hx
      rw [max_eq_right (le_of_lt hx)]
    have h := (hasDerivAt_const v ((0 : ℝ) ^ p)).congr_of_eventuallyEq hev
    rw [max_eq_right (le_of_lt hv), Real.zero_rpow hpm1, mul_zero]
    exact h
  · -- `v = 0`: glue the one-sided derivatives.
    subst hv
    have hbase : HasDerivAt (fun x : ℝ => x ^ p) 0 0 := by
      have h := Real.hasDerivAt_rpow_const (x := 0) (p := p) (Or.inr hp.le)
      rwa [Real.zero_rpow hpm1, mul_zero] at h
    have hIci : HasDerivWithinAt (fun x : ℝ => (max x 0) ^ p) 0 (Set.Ici 0) 0 := by
      have hev : (fun x : ℝ => x ^ p) =ᶠ[𝓝[Set.Ici 0] 0] (fun x : ℝ => (max x 0) ^ p) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        rw [max_eq_left hx]
      exact (hev.hasDerivWithinAt_iff (by simp)).mp hbase.hasDerivWithinAt
    have hIic : HasDerivWithinAt (fun x : ℝ => (max x 0) ^ p) 0 (Set.Iic 0) 0 := by
      have hev : (fun _ : ℝ => (0 : ℝ) ^ p) =ᶠ[𝓝[Set.Iic 0] 0] (fun x : ℝ => (max x 0) ^ p) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        rw [max_eq_right hx]
      exact (hev.hasDerivWithinAt_iff (by simp)).mp
        (hasDerivAt_const (0 : ℝ) _).hasDerivWithinAt
    have hunion := hIic.union hIci
    rw [Set.Iic_union_Ici] at hunion
    have h0 : HasDerivAt (fun x : ℝ => (max x 0) ^ p) 0 0 := hunion.hasDerivAt univ_mem
    rw [show p * (max (0 : ℝ) 0) ^ (p - 1) = 0 by
      rw [max_eq_right le_rfl, Real.zero_rpow hpm1, mul_zero]]
    exact h0
  · -- `v > 0`: the map agrees near `v` with `y ^ p`.
    have hev : (fun x : ℝ => (max x 0) ^ p) =ᶠ[𝓝 v] (fun x => x ^ p) := by
      filter_upwards [isOpen_Ioi.mem_nhds hv] with x hx
      rw [max_eq_left (le_of_lt hx)]
    have h := (Real.hasDerivAt_rpow_const (x := v) (p := p)
      (Or.inl (ne_of_gt hv))).congr_of_eventuallyEq hev
    rw [max_eq_left (le_of_lt hv)]
    exact h

/-- **The derivative of the moment integrand in the slope.**  For `n ≥ 1` and any differentiable
`R` at `s`,

`d/du [(max (R u) 0) ^ n * √(max (R u) 0)] = (n + 1/2) * (max (R s) 0) ^ (n - 1) * √(max (R s) 0) * R'`.

The `max · 0` is what makes the statement hold also where the radicand `R` is non-positive: there
the integrand is locally constant (in the chord-curve application `R` is `rad h f · t`, which is
negative outside the section, and `0` at its endpoints). -/
theorem hasDerivAt_max_pow_sqrt {n : ℕ} (hn : 1 ≤ n) {R : ℝ → ℝ} {s R' : ℝ}
    (hR : HasDerivAt R R' s) :
    HasDerivAt (fun u : ℝ => (max (R u) 0) ^ n * Real.sqrt (max (R u) 0))
      (((n : ℝ) + 1 / 2) * (max (R s) 0) ^ (n - 1) * Real.sqrt (max (R s) 0) * R') s := by
  have hp : (1 : ℝ) < (n : ℝ) + 1 / 2 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- The composite with `x ↦ (max x 0) ^ (n + 1/2)`.
  have hcomp : HasDerivAt (fun u : ℝ => (max (R u) 0) ^ ((n : ℝ) + 1 / 2))
      ((((n : ℝ) + 1 / 2) * (max (R s) 0) ^ ((n : ℝ) + 1 / 2 - 1)) * R') s :=
    (hasDerivAt_max_zero_rpow (p := (n : ℝ) + 1 / 2) hp (R s)).comp s hR
  -- Rewrite the function along the pointwise identity `x ^ n * √x = x ^ (n + 1/2)`.
  have hfun : (fun u : ℝ => (max (R u) 0) ^ n * Real.sqrt (max (R u) 0)) =
      (fun u : ℝ => (max (R u) 0) ^ ((n : ℝ) + 1 / 2)) :=
    funext fun u => pow_mul_sqrt_eq_rpow (le_max_right _ _) n
  have hmain := hcomp.congr_of_eventuallyEq (Eventually.of_forall fun u => congrFun hfun u)
  refine hmain.congr_deriv ?_
  -- Rewrite the derivative value: `(n + 1/2) - 1 = (n - 1) + 1/2`.
  have hexp : (n : ℝ) + 1 / 2 - 1 = ((n - 1 : ℕ) : ℝ) + 1 / 2 := by
    rw [Nat.cast_sub hn]; ring
  have hpow : (max (R s) 0) ^ ((n : ℝ) + 1 / 2 - 1)
      = (max (R s) 0) ^ (n - 1) * Real.sqrt (max (R s) 0) := by
    rw [hexp, ← Real.rpow_natCast (max (R s) 0) (n - 1), Real.sqrt_eq_rpow,
      Real.rpow_add' (le_max_right _ _) (by positivity)]
  rw [hpow]
  ring

end

end Work.OddCurve
