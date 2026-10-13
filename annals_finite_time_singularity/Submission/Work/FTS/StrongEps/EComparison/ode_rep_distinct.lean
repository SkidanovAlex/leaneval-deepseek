import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.FTS.StrongEps.EComparison

/-- `deriv (fun s => exp (c * s)) t = c * exp (c * t)`. -/
private lemma hasDerivAt_exp_const_mul (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (c * s)) (c * Real.exp (c * t)) t := by
  have hlin : HasDerivAt (fun s : ℝ => c * s) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have h := hlin.exp
  rwa [show Real.exp (c * t) * c = c * Real.exp (c * t) by ring] at h

/-- A function satisfying `f' = c * f` is `t ↦ f 0 * exp (c * t)`. -/
private lemma eq_exp_const_mul_of_deriv_eq {c : ℝ} {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h : ∀ t, deriv f t = c * f t) (t : ℝ) : f t = f 0 * Real.exp (c * t) := by
  have hgdiff : Differentiable ℝ (fun s : ℝ => f s * Real.exp ((-c) * s)) := by fun_prop
  have hg0 : ∀ s, deriv (fun x : ℝ => f x * Real.exp ((-c) * x)) s = 0 := by
    intro s
    have h1 : HasDerivAt (fun x : ℝ => Real.exp ((-c) * x)) ((-c) * Real.exp ((-c) * s)) s :=
      hasDerivAt_exp_const_mul (-c) s
    have h2 : HasDerivAt f (c * f s) s := by
      have hh := (hf.differentiableAt (x := s)).hasDerivAt
      rwa [h s] at hh
    have h3 : HasDerivAt (fun x : ℝ => f x * Real.exp ((-c) * x))
        (c * f s * Real.exp ((-c) * s) + f s * ((-c) * Real.exp ((-c) * s))) s := h2.mul h1
    rw [h3.deriv]
    ring
  have hgc := is_const_of_deriv_eq_zero hgdiff hg0 t 0
  simp only [mul_zero, Real.exp_zero, mul_one] at hgc
  have hexp : Real.exp ((-c) * t) * Real.exp (c * t) = 1 := by
    rw [← Real.exp_add, show (-c) * t + c * t = 0 by ring, Real.exp_zero]
  calc f t = f t * (Real.exp ((-c) * t) * Real.exp (c * t)) := by rw [hexp, mul_one]
    _ = (f t * Real.exp ((-c) * t)) * Real.exp (c * t) := by rw [mul_assoc]
    _ = f 0 * Real.exp (c * t) := by rw [hgc]

/-- Solutions of the second order equation `U'' + a U' + b U = 0` with characteristic
polynomial splitting into two *distinct* real roots `r1 ≠ r2`, `r1 + r2 = -a`, `r1 * r2 = b`,
are linear combinations of `exp (r1 * ·)` and `exp (r2 * ·)`.

Proof: `F := U * exp (-r1 * ·)` satisfies `F' = G` with
`G := exp (-r1 * ·) * (U' - r1 * U)`, and the equation gives `G' = (r2 - r1) * G`.  Hence
`G = G 0 * exp ((r2 - r1) * ·)` (by `eq_exp_const_mul_of_deriv_eq`), and then
`F - (G 0 / (r2 - r1)) * exp ((r2 - r1) * ·)` has vanishing derivative, i.e. is constant. -/
theorem ode_rep_distinct {a b r1 r2 : ℝ} (hs : r1 + r2 = -a) (hp : r1 * r2 = b) (hne : r1 ≠ r2)
    {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hode : ∀ t, deriv (deriv U) t + a * deriv U t + b * U t = 0) :
    ∃ c1 c2 : ℝ, ∀ t, U t = c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t) := by
  have hdU : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hdU' : Differentiable ℝ (deriv U) := hU.differentiable_deriv_two
  have ha : a = -(r1 + r2) := by linarith
  have hb : b = r1 * r2 := hp.symm
  have hne' : (r2 - r1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  -- `F' = G`
  have hFderiv : deriv (fun s : ℝ => U s * Real.exp ((-r1) * s))
      = fun s : ℝ => Real.exp ((-r1) * s) * (deriv U s - r1 * U s) := by
    funext t
    have h1 : HasDerivAt (fun x : ℝ => Real.exp ((-r1) * x)) ((-r1) * Real.exp ((-r1) * t)) t :=
      hasDerivAt_exp_const_mul (-r1) t
    have h2 : HasDerivAt U (deriv U t) t := (hdU.differentiableAt (x := t)).hasDerivAt
    have h3 : HasDerivAt (fun x : ℝ => U x * Real.exp ((-r1) * x))
        (deriv U t * Real.exp ((-r1) * t) + U t * ((-r1) * Real.exp ((-r1) * t))) t := h2.mul h1
    rw [h3.deriv]
    ring
  -- `G' = (r2 - r1) * G`
  have hGderiv : ∀ t, deriv (fun s : ℝ => Real.exp ((-r1) * s) * (deriv U s - r1 * U s)) t
      = (r2 - r1) * (Real.exp ((-r1) * t) * (deriv U t - r1 * U t)) := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => Real.exp ((-r1) * x)) ((-r1) * Real.exp ((-r1) * t)) t :=
      hasDerivAt_exp_const_mul (-r1) t
    have h2 : HasDerivAt (fun x : ℝ => deriv U x - r1 * U x)
        (deriv (deriv U) t - r1 * deriv U t) t :=
      ((hdU'.differentiableAt (x := t)).hasDerivAt).sub
        (((hdU.differentiableAt (x := t)).hasDerivAt).const_mul r1)
    have h3 : HasDerivAt (fun x : ℝ => Real.exp ((-r1) * x) * (deriv U x - r1 * U x))
        (((-r1) * Real.exp ((-r1) * t)) * (deriv U t - r1 * U t)
          + Real.exp ((-r1) * t) * (deriv (deriv U) t - r1 * deriv U t)) t := h1.mul h2
    rw [h3.deriv]
    have hdd : deriv (deriv U) t = -(a * deriv U t + b * U t) := by
      have := hode t
      linarith
    rw [hdd, ha, hb]
    ring
  have hGdiff : Differentiable ℝ (fun s : ℝ => Real.exp ((-r1) * s) * (deriv U s - r1 * U s)) := by
    fun_prop
  have hGrep : ∀ t, Real.exp ((-r1) * t) * (deriv U t - r1 * U t)
      = (deriv U 0 - r1 * U 0) * Real.exp ((r2 - r1) * t) := by
    have h := eq_exp_const_mul_of_deriv_eq hGdiff hGderiv
    intro t
    have ht := h t
    simpa using ht
  set K : ℝ := (deriv U 0 - r1 * U 0) / (r2 - r1) with hK
  have hKmul : K * (r2 - r1) = deriv U 0 - r1 * U 0 := by
    rw [hK, div_mul_cancel₀ _ hne']
  have hFdiff : Differentiable ℝ (fun s : ℝ => U s * Real.exp ((-r1) * s)) := by fun_prop
  have hHdiff : Differentiable ℝ (fun s : ℝ => U s * Real.exp ((-r1) * s)
      - K * Real.exp ((r2 - r1) * s)) := by fun_prop
  have hHderiv : ∀ t, deriv (fun s : ℝ => U s * Real.exp ((-r1) * s)
      - K * Real.exp ((r2 - r1) * s)) t = 0 := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => U x * Real.exp ((-r1) * x))
        (Real.exp ((-r1) * t) * (deriv U t - r1 * U t)) t := by
      have hh := (hFdiff.differentiableAt (x := t)).hasDerivAt
      rwa [hFderiv] at hh
    have h2 : HasDerivAt (fun x : ℝ => K * Real.exp ((r2 - r1) * x))
        (K * ((r2 - r1) * Real.exp ((r2 - r1) * t))) t :=
      (hasDerivAt_exp_const_mul (r2 - r1) t).const_mul K
    have h3 : HasDerivAt (fun x : ℝ => U x * Real.exp ((-r1) * x) - K * Real.exp ((r2 - r1) * x))
        (Real.exp ((-r1) * t) * (deriv U t - r1 * U t)
          - K * ((r2 - r1) * Real.exp ((r2 - r1) * t))) t := h1.sub h2
    rw [h3.deriv, hGrep t, ← mul_assoc, hKmul]
    ring
  have hHconst : ∀ t, U t * Real.exp ((-r1) * t) - K * Real.exp ((r2 - r1) * t) = U 0 - K := by
    intro t
    have h := is_const_of_deriv_eq_zero hHdiff hHderiv t 0
    simpa using h
  refine ⟨U 0 - K, K, ?_⟩
  intro t
  have h1 := hHconst t
  have hEt : Real.exp ((-r1) * t) * Real.exp (r1 * t) = 1 := by
    rw [← Real.exp_add, show (-r1) * t + r1 * t = 0 by ring, Real.exp_zero]
  have hEc : Real.exp ((r2 - r1) * t) * Real.exp (r1 * t) = Real.exp (r2 * t) := by
    rw [← Real.exp_add, show (r2 - r1) * t + r1 * t = r2 * t by ring]
  have h2 : U t * Real.exp ((-r1) * t) = (U 0 - K) + K * Real.exp ((r2 - r1) * t) := by linarith
  calc U t = U t * (Real.exp ((-r1) * t) * Real.exp (r1 * t)) := by rw [hEt, mul_one]
    _ = (U t * Real.exp ((-r1) * t)) * Real.exp (r1 * t) := by rw [mul_assoc]
    _ = ((U 0 - K) + K * Real.exp ((r2 - r1) * t)) * Real.exp (r1 * t) := by rw [h2]
    _ = (U 0 - K) * Real.exp (r1 * t) + K * Real.exp (r2 * t) := by
          rw [add_mul, mul_assoc, hEc]

end Work.FTS.StrongEps.EComparison
