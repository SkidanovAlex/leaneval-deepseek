import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Ift.Basic
import Submission.Work.WilE9.Ift.jc_eval_eq

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical Topology Filter
namespace Work.WilE9.Ift
open WilkiesDesign WilkiesDesign.E

/-- **The chain rule along a line through a solution.**  The directional derivative at `t = 0` of
`t ↦ eaEval c P (x + t eᵢ, y (x + t eᵢ))` is the `xᵢ`-partial of `P` along the solution plus, for
each fibre coordinate, the partial in that direction times the `l`-th coordinate of the first
derivative of `y` in the direction `eᵢ`.

This is the single calculation performed at every step of the `iftP` recursion, separated from the
Cramer/adjugate bookkeeping in `deriv_eaEval_solution`. -/
theorem deriv_line_eaEval {n q r : ℕ} (c : EAChain (n + q) r) (P : EAPoly (n + q) r)
    (y : (Fin n → ℝ) → (Fin q → ℝ)) (x : Fin n → ℝ) (i : Fin n)
    (hy : HasFDerivAt y (fderiv ℝ y x) x) :
    deriv (fun t : ℝ => eaEval c P
        (Fin.append (x + t • Pi.single i 1) (y (x + t • Pi.single i 1)))) 0
      = eaEval c (eaD c (Fin.castAdd q i) P) (Fin.append x (y x))
        + ∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) P) (Fin.append x (y x)) *
            (fderiv ℝ y x (Pi.single i 1)) l := by
  classical
  -- The chain rule at `x`, and the derivative of the line `t ↦ x + t • eᵢ`.
  have hchain := chain_rule c P y x hy
  have hline : HasDerivAt (fun t : ℝ => x + t • (Pi.single i 1 : Fin n → ℝ))
      (Pi.single i 1 : Fin n → ℝ) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin n → ℝ)
    simpa using h.const_add x
  -- The chain rule, with the base point written as the value of the line at `0`.
  have hchain' : HasFDerivAt (fun x' : Fin n → ℝ => eaEval c P (Fin.append x' (y x')))
      ((∑ i' : Fin n, (eaEval c (eaD c (Fin.castAdd q i') P) (Fin.append x (y x))) •
          (ContinuousLinearMap.proj i' : (Fin n → ℝ) →L[ℝ] ℝ))
        + (∑ l : Fin q, (eaEval c (eaD c (Fin.natAdd n l) P) (Fin.append x (y x))) •
            ((ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ y x))))
      ((fun t : ℝ => x + t • (Pi.single i 1 : Fin n → ℝ)) 0) := by
    rw [show (fun t : ℝ => x + t • (Pi.single i 1 : Fin n → ℝ)) 0 = x from by simp]
    exact hchain
  -- Compose with the line; the derivative is the linear part applied to `eᵢ`.
  have hcomp := HasFDerivAt.comp_hasDerivAt
    (f := fun t : ℝ => x + t • (Pi.single i 1 : Fin n → ℝ)) 0 hchain' hline
  have hderiv : deriv (fun t : ℝ => eaEval c P
      (Fin.append (x + t • (Pi.single i 1 : Fin n → ℝ))
        (y (x + t • (Pi.single i 1 : Fin n → ℝ))))) 0
      = ((∑ i' : Fin n, (eaEval c (eaD c (Fin.castAdd q i') P) (Fin.append x (y x))) •
          (ContinuousLinearMap.proj i' : (Fin n → ℝ) →L[ℝ] ℝ))
        + (∑ l : Fin q, (eaEval c (eaD c (Fin.natAdd n l) P) (Fin.append x (y x))) •
            ((ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ y x))))
          (Pi.single i 1 : Fin n → ℝ) := hcomp.deriv
  rw [hderiv]
  -- Only the `i`-th term of the base sum survives, since `Pi.single i 1` vanishes elsewhere.
  have hsum1 : (∑ i' : Fin n,
      (eaEval c (eaD c (Fin.castAdd q i') P) (Fin.append x (y x))) *
        (Pi.single i 1 : Fin n → ℝ) i')
      = eaEval c (eaD c (Fin.castAdd q i) P) (Fin.append x (y x)) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [hsum1]

/-- **The chain rule along a solution.**  If `y` solves `F(x,y)=0` near `x` (fibre Jacobian
invertible) and is differentiable there, then for every EA polynomial `P` the directional
derivative at `t = 0` of `t ↦ eaEval c P (x + t eᵢ, y (x + t eᵢ))` is the `xᵢ`-partial of `P`
along the solution plus, for each fibre coordinate, the partial in that direction times the
first derivative `jc_{l i}/Q` of `y`.  This is the single calculation performed at every step
of the `iftP` recursion.

The ingredients are `Work.WilE9.Ift.fderiv_eaEval_append` (chain rule) and
`Work.WilE9.Ift.jc_eval_eq` (`∂_{x_i} y_l = jc_{l i}/Q`); both modules exist in the tree and may
be imported. -/
theorem deriv_eaEval_solution {n q r : ℕ} (c : WilkiesDesign.E.EAChain (n + q) r)
    (F : Fin q → WilkiesDesign.E.EAPoly (n + q) r) (y : (Fin n → ℝ) → (Fin q → ℝ))
    (x : Fin n → ℝ) (i : Fin n) (P : WilkiesDesign.E.EAPoly (n + q) r)
    (hy : HasFDerivAt y (fderiv ℝ y x) x) (hs : Work.WilE9.IsSoln c F y x)
    (hQ : WilkiesDesign.E.eaEval c (Work.WilE9.jQ c F) (Fin.append x (y x)) ≠ 0) :
    deriv (fun t : ℝ => WilkiesDesign.E.eaEval c P
        (Fin.append (x + t • Pi.single i 1) (y (x + t • Pi.single i 1)))) 0 =
      WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.castAdd q i) P) (Fin.append x (y x))
        + ∑ l : Fin q,
            (WilkiesDesign.E.eaEval c (Work.WilE9.jc c F l i) (Fin.append x (y x)) /
              WilkiesDesign.E.eaEval c (Work.WilE9.jQ c F) (Fin.append x (y x))) *
            WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.natAdd n l) P)
              (Fin.append x (y x)) := by
  classical
  -- `Q · ∂_{x_i} y_l = jc_{l i}`, so the fibre term of the chain rule is the `jc`-term.
  have hjc (l : Fin q) : (fderiv ℝ y x (Pi.single i 1)) l
      = eaEval c (jc c F l i) (Fin.append x (y x))
        / eaEval c (jQ c F) (Fin.append x (y x)) := by
    rw [jc_eval_eq c F y x i l hy hs]
    exact (mul_div_cancel_right₀ ((fderiv ℝ y x (Pi.single i 1)) l) hQ).symm
  rw [deriv_line_eaEval c P y x i hy]
  have hsum : (∑ l : Fin q, eaEval c (eaD c (Fin.natAdd n l) P) (Fin.append x (y x)) *
        (fderiv ℝ y x (Pi.single i 1)) l)
      = ∑ l : Fin q, (eaEval c (jc c F l i) (Fin.append x (y x)) /
            eaEval c (jQ c F) (Fin.append x (y x))) *
          eaEval c (eaD c (Fin.natAdd n l) P) (Fin.append x (y x)) := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hjc l]
    exact mul_comm _ _
  rw [hsum]

end Work.WilE9.Ift
