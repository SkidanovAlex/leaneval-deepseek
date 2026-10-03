import Mathlib
import ChallengeDeps
import Submission.Work.Param.Basic

/-!
# PARAM: the critical orbit as a polynomial in the parameter

For the parameter disc argument (`Work.Param.false_of_critical_orbit_tendsto`) we need the map
`t ↦ (Tc (cOfLam t))^[n] 0` to be (the evaluation of) a polynomial in `t`, together with the
elementary evaluation facts

* `(G n).eval t = (Tc (cOfLam t))^[n] 0`   (`G_eval`),
* `(G n).eval 2 = 0`                        (`G_eval_two`, since `cOfLam 2 = 0` and `0` is fixed
  for `Tc 0`),
* `(P n).eval t = (Tc (cOfLam t))^[n] 0 - t / 2`  where `P n = G n - X/2` (`P_eval`),
* `(P n).eval 2 = -1`                       (`P_eval_two`).

We also introduce the closed sets `Z n = {t | (P n).eval t = 0}`, which are the parameter sets on
which the critical orbit has already reached the fixed point `t/2` at time `n`.
-/

namespace Work.Param

open MandelDim Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

/-- `cOfLam` as a polynomial: `X/2 - X²/4`. -/
def cOfLamP : Polynomial ℂ :=
  Polynomial.C (1 / 2) * Polynomial.X - Polynomial.C (1 / 4) * Polynomial.X ^ 2

@[simp]
theorem cOfLamP_eval (t : ℂ) : cOfLamP.eval t = cOfLam t := by
  simp [cOfLamP, cOfLam]; ring

/-- The polynomial `G n` whose value at `t` is the `n`-th point of the critical orbit of
`Tc (cOfLam t)`: `G 0 = 0` and `G (n+1) = (G n)² + cOfLamP`. -/
def G : ℕ → Polynomial ℂ
  | 0 => 0
  | n + 1 => G n ^ 2 + cOfLamP

@[simp] theorem G_zero : G 0 = 0 := rfl

@[simp] theorem G_succ (n : ℕ) : G (n + 1) = G n ^ 2 + cOfLamP := rfl

/-- `(G n).eval t` is the `n`-th point of the critical orbit of `Tc (cOfLam t)`. -/
theorem G_eval (n : ℕ) (t : ℂ) : (G n).eval t = (Tc (cOfLam t))^[n] 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [G_succ, Polynomial.eval_add, Polynomial.eval_pow, ih, cOfLamP_eval,
      Function.iterate_succ_apply']
    simp only [Tc]

/-- At the parameter `t = 2` (i.e. `c = 0`) the critical orbit is identically `0`. -/
theorem G_eval_two (n : ℕ) : (G n).eval 2 = 0 := by
  rw [G_eval]
  have h2 : cOfLam (2 : ℂ) = 0 := by simp [cOfLam]; norm_num
  rw [h2]
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih]; simp [Tc]

/-- `P n = G n - X/2`, so that `(P n).eval t = (Tc (cOfLam t))^[n] 0 - t/2`. -/
def P (n : ℕ) : Polynomial ℂ := G n - Polynomial.C (1 / 2) * Polynomial.X

@[simp]
theorem P_eval (n : ℕ) (t : ℂ) :
    (P n).eval t = (Tc (cOfLam t))^[n] 0 - t / 2 := by
  simp [P, Polynomial.eval_sub, Polynomial.eval_mul, G_eval]; ring

/-- At `t = 2` the polynomial `P n` takes the value `-1`. -/
theorem P_eval_two (n : ℕ) : (P n).eval 2 = -1 := by
  rw [P_eval, ← G_eval n 2, G_eval_two n]; norm_num

/-- `Z n` is the set of parameters in the `n`-th "hitting set": the critical orbit of `Tc (cOfLam t)`
has reached the fixed point `t/2` at time `n`.  Equivalently `(P n).eval t = 0`. -/
def Z (n : ℕ) : Set ℂ := {t | (P n).eval t = 0}

@[simp]
theorem Z_iff (n : ℕ) (t : ℂ) : t ∈ Z n ↔ (Tc (cOfLam t))^[n] 0 = t / 2 := by
  simp [Z, P_eval, sub_eq_zero]

theorem isClosed_Z (n : ℕ) : IsClosed (Z n) := by
  have : Z n = {t : ℂ | (P n).eval t = (fun _ => (0 : ℂ)) t} := by ext t; simp [Z]
  rw [this]
  exact isClosed_eq (P n).continuous continuous_const

end

end Work.Param
