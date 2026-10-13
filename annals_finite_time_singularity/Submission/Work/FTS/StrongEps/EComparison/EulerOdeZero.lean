import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EComparison.not_integrable_two_exp
import Submission.Work.FTS.StrongEps.EComparison.not_integrable_poly_exp
import Submission.Work.FTS.StrongEps.EComparison.not_integrable_exp_trig
import Submission.Work.FTS.StrongEps.EComparison.ode_rep_distinct
import Submission.Work.FTS.StrongEps.EComparison.ode_rep_double
import Submission.Work.FTS.StrongEps.EComparison.ode_rep_trig

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-- Multiplying a solution of the constant-coefficient equation `X'' + aX' + bX = 0` by the
exponential `t ↦ exp (c * t)` gives a solution of `Y'' + (a - 2c)Y' + (b - a c + c²)Y = 0`. -/
lemma mul_exp_ode {a b c : ℝ} {X : ℝ → ℝ} (hX : ContDiff ℝ 2 X)
    (hode : ∀ t, deriv (deriv X) t + a * deriv X t + b * X t = 0) :
    ∀ t, deriv (deriv (fun t => X t * Real.exp (c * t))) t
      + (a - 2*c) * deriv (fun t => X t * Real.exp (c*t)) t
      + (b - a*c + c^2) * (X t * Real.exp (c*t)) = 0 := by
  have hg : ∀ s, HasDerivAt (fun t => Real.exp (c*t)) (c * Real.exp (c*s)) s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => c*t) c s := by
      simpa using (hasDerivAt_id s).const_mul c
    simpa [mul_comm] using h1.exp
  have hg2 : ∀ s, HasDerivAt (fun t => c * Real.exp (c*t)) (c * (c * Real.exp (c*s))) s := by
    intro s
    simpa using (hg s).const_mul c
  have hd1 : ∀ s, deriv (fun t => X t * Real.exp (c*t)) s
      = deriv X s * Real.exp (c*s) + X s * (c * Real.exp (c*s)) := by
    intro s
    exact (((hX.differentiable (by norm_num)).differentiableAt.hasDerivAt).mul (hg s)).deriv
  have hd2 : ∀ s, deriv (deriv (fun t => X t * Real.exp (c*t))) s
      = (deriv (deriv X) s * Real.exp (c*s) + deriv X s * (c*Real.exp (c*s)))
        + (deriv X s * (c*Real.exp (c*s)) + X s * (c*(c*Real.exp (c*s)))) := by
    intro s
    have hfun : deriv (fun t => X t * Real.exp (c*t))
        = fun t => deriv X t * Real.exp (c*t) + X t * (c * Real.exp (c*t)) := funext hd1
    rw [hfun]
    have hA : HasDerivAt (fun t => deriv X t * Real.exp (c*t))
        (deriv (deriv X) s * Real.exp (c*s) + deriv X s * (c*Real.exp (c*s))) s :=
      (((hX.differentiable_deriv_two).differentiableAt).hasDerivAt).mul (hg s)
    have hB : HasDerivAt (fun t => X t * (c * Real.exp (c*t)))
        (deriv X s * (c*Real.exp (c*s)) + X s * (c*(c*Real.exp (c*s)))) s :=
      ((hX.differentiable (by norm_num)).differentiableAt.hasDerivAt).mul (hg2 s)
    exact (hA.add hB).deriv
  intro t
  rw [hd2 t, hd1 t]
  linear_combination (Real.exp (c * t)) * hode t

/-- **Vanishing of `L²` solutions of a constant-coefficient second order equation.** If `U` is `C²`
on `ℝ`, solves `U'' + a U' + b U = 0` and is square-integrable, then `U ≡ 0`.

Proof by the classical classification of solutions, with `D = a² - 4b`:
* `D > 0`: `U = c₁ e^{r₁t} + c₂ e^{r₂t}` with the two distinct real roots, and such a combination
  is never `L²` on `ℝ` unless it vanishes;
* `D = 0`: `U = (c₁ + c₂t) e^{rt}`, same conclusion;
* `D < 0`: `U = e^{-at/2}(A cos ωt + B sin ωt)` with `ω > 0`, and `e^{ct}(A cos ωt + B sin ωt)²`
  is never integrable on `ℝ` when `ω ≠ 0` unless `A = B = 0`. -/
lemma ode_lin2_L2_eq_zero {a b : ℝ} {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hode : ∀ t, deriv (deriv U) t + a * deriv U t + b * U t = 0)
    (hint : MeasureTheory.Integrable (fun t => (U t) ^ 2)) : ∀ t, U t = 0 := by
  rcases lt_trichotomy (a ^ 2 - 4 * b) 0 with hD | hD | hD
  · -- `D < 0` : oscillatory solutions
    obtain ⟨hb, hω⟩ : b - a^2/4 = (Real.sqrt (b - a^2/4))^2 ∧ 0 < Real.sqrt (b - a^2/4) := by
      have h1 : 0 < b - a^2/4 := by nlinarith
      exact ⟨(Real.sq_sqrt (le_of_lt h1)).symm, Real.sqrt_pos.2 h1⟩
    obtain ⟨A, B, hAB⟩ := ode_rep_trig hω hb hU hode
    have hI : MeasureTheory.Integrable (fun t => Real.exp ((-a) * t)
        * (A * Real.cos (Real.sqrt (b - a^2/4) * t)
            + B * Real.sin (Real.sqrt (b - a^2/4) * t)) ^ 2) := by
      refine hint.congr ?_
      filter_upwards with t
      rw [hAB t, mul_pow]
      have hexp : Real.exp (-(a * t / 2)) ^ 2 = Real.exp ((-a) * t) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      rw [hexp]
    obtain ⟨hA, hB⟩ := not_integrable_exp_trig (by positivity : Real.sqrt (b - a^2/4) ≠ 0) hI
    intro t
    rw [hAB t, hA, hB]; ring
  · -- `D = 0` : double root
    have ha : a = -2 * (-a/2) := by ring
    have hb : b = (-a/2)^2 := by nlinarith
    obtain ⟨c1, c2, h12⟩ := ode_rep_double ha hb hU hode
    have hI : MeasureTheory.Integrable (fun t => ((c1 + c2 * t) * Real.exp ((-a/2) * t)) ^ 2) := by
      refine hint.congr ?_
      filter_upwards with t
      rw [h12 t]
    obtain ⟨hc1, hc2⟩ := not_integrable_poly_exp (r := -a/2) hI
    intro t
    rw [h12 t, hc1, hc2]; ring
  · -- `D > 0` : two distinct real roots
    set s := Real.sqrt (a^2 - 4*b) with hsdef
    have hsq : s ^ 2 = a^2 - 4*b := Real.sq_sqrt (le_of_lt hD)
    set r1 := (-a + s)/2 with hr1
    set r2 := (-a - s)/2 with hr2
    have hsum : r1 + r2 = -a := by rw [hr1, hr2]; ring
    have hprod : r1 * r2 = b := by rw [hr1, hr2]; nlinarith
    have hlt : r2 < r1 := by rw [hr1, hr2]; linarith [Real.sqrt_pos.2 hD]
    obtain ⟨c1, c2, h12⟩ := ode_rep_distinct hsum hprod (ne_of_gt hlt) hU hode
    have hI : MeasureTheory.Integrable (fun t => (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2) := by
      refine hint.congr ?_
      filter_upwards with t
      rw [h12 t]
    obtain ⟨hc1, hc2⟩ := not_integrable_two_exp hlt hI
    intro t
    rw [h12 t, hc1, hc2]; ring

theorem EulerOdeZero {p q ν : ℝ} (hν : 0 < ν) {V : ℝ → ℝ} (hV : ContDiffOn ℝ 2 V (Set.Ioi 0))
    (hode : ∀ z ∈ Set.Ioi 0, z ^ 2 * deriv (deriv V) z + p * z * deriv V z + q * V z = 0)
    (hint : MeasureTheory.IntegrableOn (fun z => (V z) ^ 2 * z ^ ((-1 : ℝ) - ν)) (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi 0, V z = 0 := by
  have hνpos : 0 < ν := hν
  -- Step 1: substitute `z = exp t`.
  have hWcd : ContDiff ℝ 2 (fun t => V (Real.exp t)) := by
    rw [← contDiffOn_univ]
    exact hV.comp ((Real.contDiff_exp.contDiffOn).of_le le_top) (fun t _ => Real.exp_pos t)
  have hW1 : ∀ t, deriv (fun s => V (Real.exp s)) t = deriv V (Real.exp t) * Real.exp t := by
    intro t
    exact (((hV.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos t))).differentiableAt
      (by norm_num)).hasDerivAt.comp t (Real.hasDerivAt_exp t)).deriv
  have hW2 : ∀ t, deriv (deriv (fun s => V (Real.exp s))) t
      = deriv (deriv V) (Real.exp t) * Real.exp t * Real.exp t + deriv V (Real.exp t) * Real.exp t := by
    intro t
    have h1 : deriv (fun s => V (Real.exp s)) = fun s => deriv V (Real.exp s) * Real.exp s := by
      funext s; exact hW1 s
    have hdVd : DifferentiableAt ℝ (deriv V) (Real.exp t) :=
      ((hV.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos t))).derivWithin (m := 1)
        (by norm_num)).differentiableAt (by norm_num)
    rw [h1]
    exact (((hdVd.hasDerivAt).comp t (Real.hasDerivAt_exp t)).mul (Real.hasDerivAt_exp t)).deriv
  have hodeW : ∀ t, deriv (deriv (fun s => V (Real.exp s))) t
      + (p - 1) * deriv (fun s => V (Real.exp s)) t + q * V (Real.exp t) = 0 := by
    intro t
    rw [hW2 t, hW1 t]
    have h1 := hode (Real.exp t) (Real.exp_pos t)
    linear_combination h1
  -- Step 2: absorb the weight `z ^ (-ν)`, i.e. multiply by `exp (-(ν/2) ·)` in the `t` variable.
  have hY := mul_exp_ode (a := p - 1) (b := q) (c := -ν/2) hWcd hodeW
  have hUode : ∀ t, deriv (deriv (fun s => V (Real.exp s) * Real.exp ((-ν/2)*s))) t
      + (p - 1 + ν) * deriv (fun s => V (Real.exp s) * Real.exp ((-ν/2)*s)) t
      + (ν^2/4 + (p-1)*ν/2 + q) * (V (Real.exp t) * Real.exp ((-ν/2)*t)) = 0 := by
    intro t
    have h := hY t
    rw [show (p-1) - 2*(-ν/2) = p - 1 + ν by ring,
        show q - (p-1)*(-ν/2) + (-ν/2)^2 = ν^2/4 + (p-1)*ν/2 + q by ring] at h
    exact h
  have hUcd : ContDiff ℝ 2 (fun s => V (Real.exp s) * Real.exp ((-ν/2)*s)) :=
    hWcd.mul (by fun_prop)
  -- Step 3: transport the integrability hypothesis to the `t` variable.
  have hbase : MeasureTheory.Integrable (fun t => (V (Real.exp t))^2 * Real.exp (-(ν*t))) := by
    have h := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Set.univ) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Real.exp_injective.injOn) (fun z => (V z)^2 * z^((-1:ℝ)-ν)))
    have him : Real.exp '' (Set.univ : Set ℝ) = Set.Ioi 0 := by
      rw [Set.image_univ]; exact Real.range_exp
    rw [him] at h
    have h2 := h.1 hint
    rw [MeasureTheory.integrableOn_univ] at h2
    refine h2.congr ?_
    filter_upwards with x
    rw [Real.abs_exp, smul_eq_mul]
    have hpow : Real.exp x ^ ((-1:ℝ) - ν) = Real.exp (-(ν*x)) / Real.exp x := by
      rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp,
        show x * (-1 - ν) = -(ν*x) - x by ring, Real.exp_sub]
    rw [hpow, show Real.exp x * (V (Real.exp x)^2 * (Real.exp (-(ν*x)) / Real.exp x))
        = V (Real.exp x)^2 * (Real.exp x * (Real.exp (-(ν*x)) / Real.exp x)) by ring]
    field_simp
  have hUint : MeasureTheory.Integrable (fun s => (V (Real.exp s) * Real.exp ((-ν/2)*s))^2) := by
    refine hbase.congr ?_
    filter_upwards with s
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    congr 1
    push_cast
    ring
  -- Step 4: an `L²` solution of the constant-coefficient equation vanishes identically.
  have hzero : ∀ t, V (Real.exp t) * Real.exp ((-ν/2)*t) = 0 :=
    ode_lin2_L2_eq_zero hUcd hUode hUint
  intro z hz
  have h := hzero (Real.log z)
  rw [Real.exp_log hz] at h
  exact (mul_eq_zero.mp h).resolve_right (Real.exp_ne_zero _)

end Work.FTS.StrongEps.EComparison
