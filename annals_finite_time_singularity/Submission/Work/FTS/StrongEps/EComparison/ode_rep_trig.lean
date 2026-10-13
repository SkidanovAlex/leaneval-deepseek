import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Solutions of `U'' + a U' + b U = 0` when the characteristic roots are complex

If `b - a²/4 = ω²` with `ω > 0`, the characteristic polynomial `X² + aX + b` of the ODE
`U'' + a U' + b U = 0` has the two conjugate complex roots `-a/2 ± iω`, so every `C²`
solution must have the form

`U t = exp (-(a t / 2)) (A cos (ω t) + B sin (ω t))`.

The proof here is elementary and avoids any ODE uniqueness theory: multiplying `U` by
`exp (a t / 2)` reduces the equation to the harmonic oscillator `V'' + ω² V = 0`, whose
"energy" `(V')² + ω² V²` is constant (its derivative is `2 V' (V'' + ω² V) = 0`).  Energy
zero then forces `V ≡ 0`, which gives uniqueness for two solutions with the same value and
derivative at `0`; a linear combination of `cos` and `sin` matching those two data is
constructed explicitly.

## Main result

* `Work.FTS.StrongEps.EComparison.ode_rep_trig`
-/

namespace Work.FTS.StrongEps.EComparison

/-- **Energy equality for the harmonic oscillator.**  If `Y'' + ω² Y = 0` on `ℝ` (with `Y`
twice differentiable in the sense that `deriv Y` is differentiable), then the energy
`(Y')² + ω² Y²` is constant. -/
lemma osc_energy_const {ω : ℝ} {Y : ℝ → ℝ} (hY1 : Differentiable ℝ Y)
    (hY2 : Differentiable ℝ (deriv Y)) (hode : ∀ t, deriv (deriv Y) t + ω ^ 2 * Y t = 0) :
    ∀ t, (deriv Y t) ^ 2 + ω ^ 2 * (Y t) ^ 2 = (deriv Y 0) ^ 2 + ω ^ 2 * (Y 0) ^ 2 := by
  have hdiff : Differentiable ℝ (fun t => (deriv Y t) ^ 2 + ω ^ 2 * (Y t) ^ 2) :=
    (hY2.pow 2).add ((hY1.pow 2).const_mul (ω ^ 2))
  have hzero : ∀ t, deriv (fun t => (deriv Y t) ^ 2 + ω ^ 2 * (Y t) ^ 2) t = 0 := by
    intro t
    have h1 : HasDerivAt (fun s => (deriv Y s) ^ 2) (2 * deriv Y t * deriv (deriv Y) t) t := by
      convert (hY2 t).hasDerivAt.pow 2 using 1
      ring
    have h2 : HasDerivAt (fun s => ω ^ 2 * (Y s) ^ 2) (ω ^ 2 * (2 * Y t * deriv Y t)) t := by
      convert ((hY1 t).hasDerivAt.pow 2).const_mul (ω ^ 2) using 1
      ring
    have h3 := h1.add h2
    convert h3.deriv using 1
    rw [show deriv (deriv Y) t = -(ω ^ 2 * Y t) by linarith [hode t]]
    ring
  intro t
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

/-- **Vanishing from zero initial data.**  If `D'' + ω² D = 0` with `ω ≠ 0` and
`D 0 = D' 0 = 0`, then `D ≡ 0`.  (The two derivatives are supplied as functions `D1`, `D2`
realising `deriv D = D1` and `deriv D1 = D2`.) -/
lemma osc_eq_zero_of_ode {ω : ℝ} (hω : 0 < ω) {D D1 D2 : ℝ → ℝ}
    (h1 : ∀ t, HasDerivAt D (D1 t) t) (h2 : ∀ t, HasDerivAt D1 (D2 t) t)
    (hode : ∀ t, D2 t + ω ^ 2 * D t = 0) (h0 : D 0 = 0) (h0' : D1 0 = 0) :
    ∀ t, D t = 0 := by
  have hD1 : deriv D = D1 := funext fun t => (h1 t).deriv
  have h1' : deriv D1 = D2 := funext fun t => (h2 t).deriv
  have hDdiff : Differentiable ℝ D := fun t => (h1 t).differentiableAt
  have hD1diff : Differentiable ℝ (deriv D) := by
    rw [hD1]; exact fun t => (h2 t).differentiableAt
  have hD2 : deriv (deriv D) = D2 := by rw [hD1, h1']
  have henergy : ∀ t, (deriv D t) ^ 2 + ω ^ 2 * (D t) ^ 2 =
      (deriv D 0) ^ 2 + ω ^ 2 * (D 0) ^ 2 :=
    osc_energy_const hDdiff hD1diff (fun t => by rw [hD2]; exact hode t)
  have hzero0 : (deriv D 0) ^ 2 + ω ^ 2 * (D 0) ^ 2 = 0 := by
    have hz : deriv D 0 = 0 := by rw [hD1]; exact h0'
    rw [hz, h0]; norm_num
  intro t
  have h := henergy t
  rw [hzero0] at h
  have hz : ω ^ 2 * (D t) ^ 2 = 0 := by
    nlinarith [sq_nonneg (deriv D t), sq_nonneg (D t), sq_nonneg ω, hω]
  have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hω)
  have hDt2 : (D t) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hω2
  exact mul_self_eq_zero.mp (by simpa [pow_two] using hDt2)

/-- **Representation of a solution of `Y'' + ω² Y = 0`.**  The linear combination of `cos`
and `sin` that matches `Y` and `Y'` at `0` is `Y` itself. -/
lemma osc_eq_sin_cos_of_hasderiv {ω : ℝ} (hω : 0 < ω) {Y Y1 Y2 : ℝ → ℝ}
    (h1 : ∀ t, HasDerivAt Y (Y1 t) t) (h2 : ∀ t, HasDerivAt Y1 (Y2 t) t)
    (hode : ∀ t, Y2 t + ω ^ 2 * Y t = 0) :
    ∀ t, Y t = Y 0 * Real.cos (ω * t) + (Y1 0 / ω) * Real.sin (ω * t) := by
  let T : ℝ → ℝ := fun t => Y 0 * Real.cos (ω * t) + (Y1 0 / ω) * Real.sin (ω * t)
  let T1 : ℝ → ℝ := fun t => (Y 0 * (-ω)) * Real.sin (ω * t) + ((Y1 0 / ω) * ω) * Real.cos (ω * t)
  let T2 : ℝ → ℝ :=
    fun t => (Y 0 * (-ω)) * (Real.cos (ω * t) * ω) + ((Y1 0 / ω) * ω) * (-Real.sin (ω * t) * ω)
  have hT1 : ∀ t, HasDerivAt T (T1 t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => ω * s) ω t := by simpa using (hasDerivAt_id t).const_mul ω
    have h := ((hlin.cos).const_mul (Y 0)).add ((hlin.sin).const_mul (Y1 0 / ω))
    convert h using 1
    ring
  have hT2 : ∀ t, HasDerivAt T1 (T2 t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => ω * s) ω t := by simpa using (hasDerivAt_id t).const_mul ω
    exact ((hlin.sin).const_mul (Y 0 * (-ω))).add ((hlin.cos).const_mul ((Y1 0 / ω) * ω))
  have hTode : ∀ t, T2 t + ω ^ 2 * T t = 0 := by
    intro t; simp only [T, T2]; ring
  let D : ℝ → ℝ := fun t => Y t - T t
  let D1 : ℝ → ℝ := fun t => Y1 t - T1 t
  let D2 : ℝ → ℝ := fun t => Y2 t - T2 t
  have hD_has : ∀ t, HasDerivAt D (D1 t) t := fun t => (h1 t).sub (hT1 t)
  have hD1_has : ∀ t, HasDerivAt D1 (D2 t) t := fun t => (h2 t).sub (hT2 t)
  have hDode : ∀ t, D2 t + ω ^ 2 * D t = 0 := by
    intro t
    have hY := hode t
    have hT := hTode t
    simp only [D, D2]
    linarith
  have hD0 : D 0 = 0 := by
    simp only [D, T]
    norm_num
  have hD10 : D1 0 = 0 := by
    simp only [D1, T1, mul_zero, Real.sin_zero, Real.cos_zero, mul_one, mul_zero]
    rw [div_mul_cancel₀ _ (ne_of_gt hω)]
    ring
  have hzero := osc_eq_zero_of_ode hω hD_has hD1_has hDode hD0 hD10
  intro t
  have ht := hzero t
  simp only [D, T] at ht
  linarith

theorem ode_rep_trig {a b ω : ℝ} (hω : 0 < ω) (hb : b - a ^ 2 / 4 = ω ^ 2)
    {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hode : ∀ t, deriv (deriv U) t + a * deriv U t + b * U t = 0) :
    ∃ A B : ℝ, ∀ t, U t = Real.exp (-(a * t / 2)) * (A * Real.cos (ω * t) + B * Real.sin (ω * t)) := by
  have hU1 : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hU2 : Differentiable ℝ (deriv U) := hU.differentiable_deriv_two
  have hb' : a ^ 2 / 4 + ω ^ 2 = b := by linarith
  -- `V = exp (a·/2) · U` solves the harmonic oscillator equation with frequency `ω`
  let V : ℝ → ℝ := fun s => Real.exp (a * s / 2) * U s
  let V1 : ℝ → ℝ := fun s => Real.exp (a * s / 2) * (deriv U s + a / 2 * U s)
  let V2 : ℝ → ℝ :=
    fun s => Real.exp (a * s / 2) * (deriv (deriv U) s + a * deriv U s + a ^ 2 / 4 * U s)
  have hV1 : ∀ t, HasDerivAt V (V1 t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => a * s / 2) (a / 2) t := by
      simpa using ((hasDerivAt_id t).const_mul a).div_const 2
    have h := (hlin.exp).mul (hU1 t).hasDerivAt
    convert h using 1
    ring
  have hV2 : ∀ t, HasDerivAt V1 (V2 t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => a * s / 2) (a / 2) t := by
      simpa using ((hasDerivAt_id t).const_mul a).div_const 2
    have hW : HasDerivAt (fun s : ℝ => deriv U s + a / 2 * U s)
        (deriv (deriv U) t + a / 2 * deriv U t) t :=
      (hU2 t).hasDerivAt.add ((hU1 t).hasDerivAt.const_mul (a / 2))
    have h := (hlin.exp).mul hW
    convert h using 1
    ring
  have hVode : ∀ t, V2 t + ω ^ 2 * V t = 0 := by
    intro t
    have hb2 : deriv (deriv U) t + a * deriv U t + (a ^ 2 / 4 + ω ^ 2) * U t = 0 := by
      rw [hb']; exact hode t
    simp only [V, V2]
    rw [show Real.exp (a * t / 2) * (deriv (deriv U) t + a * deriv U t + a ^ 2 / 4 * U t)
        + ω ^ 2 * (Real.exp (a * t / 2) * U t)
        = Real.exp (a * t / 2) * (deriv (deriv U) t + a * deriv U t + (a ^ 2 / 4 + ω ^ 2) * U t)
        from by ring]
    rw [hb2, mul_zero]
  have htrig := osc_eq_sin_cos_of_hasderiv hω hV1 hV2 hVode
  -- read off the representation of `U` from the one of `V`
  refine ⟨Real.exp (a * 0 / 2) * U 0,
    (Real.exp (a * 0 / 2) * (deriv U 0 + a / 2 * U 0)) / ω, fun t => ?_⟩
  have ht : Real.exp (a * t / 2) * U t
      = (Real.exp (a * 0 / 2) * U 0) * Real.cos (ω * t)
        + ((Real.exp (a * 0 / 2) * (deriv U 0 + a / 2 * U 0)) / ω) * Real.sin (ω * t) :=
    htrig t
  have hexp : Real.exp (-(a * t / 2)) * Real.exp (a * t / 2) = 1 := by
    rw [← Real.exp_add, show -(a * t / 2) + a * t / 2 = 0 by ring, Real.exp_zero]
  rw [← ht, ← mul_assoc, hexp, one_mul]

end Work.FTS.StrongEps.EComparison
