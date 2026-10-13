import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The derivative of `θ ↦ sin(2θ)²`. -/
private lemma hasDerivAt_sin_two_sq (θ : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.sin (2 * τ) ^ 2)
      (4 * Real.sin (2 * θ) * Real.cos (2 * θ)) θ := by
  have h1 : HasDerivAt (fun τ : ℝ => Real.sin (2 * τ)) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    have hval : Real.cos (2 * θ) * (2 * 1) = 2 * Real.cos (2 * θ) := by ring
    rw [hval] at h
    exact h
  have h2 : HasDerivAt (fun τ : ℝ => Real.sin (2 * τ) ^ 2)
      (2 * Real.sin (2 * θ) ^ (2 - 1) * (2 * Real.cos (2 * θ))) θ := h1.pow 2
  have h3 : 2 * Real.sin (2 * θ) ^ (2 - 1) * (2 * Real.cos (2 * θ))
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
    norm_num
    ring
  rw [h3] at h2
  exact h2

/-- The derivative of `θ ↦ P.eval (cos (2θ))`. -/
private lemma hasDerivAt_poly_cos (P : Polynomial ℝ) (θ : ℝ) :
    HasDerivAt (fun τ : ℝ => P.eval (Real.cos (2 * τ)))
      (P.derivative.eval (Real.cos (2 * θ)) * (-2 * Real.sin (2 * θ))) θ := by
  have hcos : HasDerivAt (fun τ : ℝ => Real.cos (2 * τ)) (-2 * Real.sin (2 * θ)) θ := by
    have h := (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    have hval : -Real.sin (2 * θ) * (2 * 1) = -2 * Real.sin (2 * θ) := by ring
    rw [hval] at h
    exact h
  exact (P.hasDerivAt (Real.cos (2 * θ))).comp θ hcos

/-- **The divisibility of `D_θ^j (sin²2θ)` by `sin²2θ`.**  Every iterate is of the form
`sin²2θ · q_j(cos 2θ)` with `q_j` a real polynomial (whence the vanishing order `sin²`). -/
private lemma exists_poly_div (j : ℕ) : ∃ P : Polynomial ℝ, ∀ θ : ℝ,
    Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ
      = Real.sin (2 * θ) ^ 2 * P.eval (Real.cos (2 * θ)) := by
  induction j with
  | zero => exact ⟨1, fun θ => by simp⟩
  | succ j ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨Polynomial.C 4 * Polynomial.X * P
        - Polynomial.C 2 * (Polynomial.C 1 - Polynomial.X ^ 2) * Polynomial.derivative P,
      fun θ => ?_⟩
    have heval : (Polynomial.C 4 * Polynomial.X * P
          - Polynomial.C 2 * (Polynomial.C 1 - Polynomial.X ^ 2) * Polynomial.derivative P).eval
            (Real.cos (2 * θ))
        = 4 * Real.cos (2 * θ) * P.eval (Real.cos (2 * θ))
          - 2 * (1 - Real.cos (2 * θ) ^ 2) * P.derivative.eval (Real.cos (2 * θ)) := by
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_pow]
      try ring
    have hd : deriv (fun τ : ℝ => Real.sin (2 * τ) ^ 2 * P.eval (Real.cos (2 * τ))) θ
        = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) * P.eval (Real.cos (2 * θ))
          + Real.sin (2 * θ) ^ 2
            * (P.derivative.eval (Real.cos (2 * θ)) * (-2 * Real.sin (2 * θ))) :=
      ((hasDerivAt_sin_two_sq θ).mul (hasDerivAt_poly_cos P θ)).deriv
    have hstep : Work.Elliptic.Dth1Iter (j + 1) (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ
        = Real.sin (2 * θ)
            * deriv (fun τ : ℝ => Real.sin (2 * τ) ^ 2 * P.eval (Real.cos (2 * τ))) θ := by
      rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1]
      exact congrArg (fun g : ℝ → ℝ => Real.sin (2 * θ) * deriv g θ) (funext hP)
    rw [heval, hstep, hd]
    have hpy : Real.sin (2 * θ) ^ 2 = 1 - Real.cos (2 * θ) ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq (2 * θ)]
    have hcol : Real.sin (2 * θ)
          * (4 * Real.sin (2 * θ) * Real.cos (2 * θ) * P.eval (Real.cos (2 * θ))
            + Real.sin (2 * θ) ^ 2
              * (P.derivative.eval (Real.cos (2 * θ)) * (-2 * Real.sin (2 * θ))))
        = Real.sin (2 * θ) ^ 2
          * (4 * Real.cos (2 * θ) * P.eval (Real.cos (2 * θ))
            - 2 * Real.sin (2 * θ) ^ 2 * P.derivative.eval (Real.cos (2 * θ))) := by
      ring
    rw [hcol, hpy]
    try ring

/-- Bound for the polynomial factor on `[-1,1]`. -/
private lemma abs_eval_le_sum_abs_coeff (P : Polynomial ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |P.eval x| ≤ ∑ n ∈ Finset.range (P.natDegree + 1), |P.coeff n| := by
  rw [Polynomial.eval_eq_sum_range]
  calc |∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * x ^ i|
      ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul, abs_pow]
        have hxi : |x| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
        calc |P.coeff i| * |x| ^ i ≤ |P.coeff i| * 1 :=
              mul_le_mul_of_nonneg_left hxi (abs_nonneg _)
          _ = |P.coeff i| := mul_one _

theorem Dth1Iter_sin_sq_bdd (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ,
      (Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
        ≤ C * (Real.sin (2 * θ)) ^ 4 := by
  obtain ⟨P, hP⟩ := exists_poly_div j
  refine ⟨max 1 ((∑ n ∈ Finset.range (P.natDegree + 1), |P.coeff n|) ^ 2), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · intro θ
    have hb := abs_eval_le_sum_abs_coeff P (x := Real.cos (2 * θ)) (Real.abs_cos_le_one (2 * θ))
    have hsq : (P.eval (Real.cos (2 * θ))) ^ 2
        ≤ (∑ n ∈ Finset.range (P.natDegree + 1), |P.coeff n|) ^ 2 := by
      rw [← sq_abs (P.eval (Real.cos (2 * θ)))]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [hP θ]
    have hmain : (Real.sin (2 * θ) ^ 2 * P.eval (Real.cos (2 * θ))) ^ 2
        = (Real.sin (2 * θ)) ^ 4 * (P.eval (Real.cos (2 * θ))) ^ 2 := by ring
    rw [hmain]
    have hmul : (Real.sin (2 * θ)) ^ 4 * (P.eval (Real.cos (2 * θ))) ^ 2
        ≤ (Real.sin (2 * θ)) ^ 4
          * (∑ n ∈ Finset.range (P.natDegree + 1), |P.coeff n|) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h4 : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ 4 := by positivity
    have hfin : (Real.sin (2 * θ)) ^ 4
          * (∑ n ∈ Finset.range (P.natDegree + 1), |P.coeff n|) ^ 2
        ≤ max 1 ((∑ n ∈ Finset.range (P.natDegree + 1), |P.coeff n|) ^ 2)
          * (Real.sin (2 * θ)) ^ 4 := by
      have hle := le_max_right (1 : ℝ) ((∑ n ∈ Finset.range (P.natDegree + 1), |P.coeff n|) ^ 2)
      nlinarith [h4, hle, sq_nonneg (∑ n ∈ Finset.range (P.natDegree + 1), |P.coeff n|)]
    linarith

end Work.FTS.EllipticEst.TT
