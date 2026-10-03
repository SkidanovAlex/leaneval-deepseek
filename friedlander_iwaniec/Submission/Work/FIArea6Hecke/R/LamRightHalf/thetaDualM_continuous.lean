/-
# `Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaDualM_continuous`

Continuity of the weight-`m` dual theta series `thetaDualM d χ m w = Σ_ξ ĝ(ξ)(ξ₁+iξ₂)^m
e^{-π|ξ|²w}` on `(0,∞)`, assuming only the size bound `‖χ‖ ≤ 1`.  Generalises
`R/continuousOn_thetaDual` (the case `m = 0`): the extra monomial factor `(ξ₁+iξ₂)^m` is dominated
by `(1+|ξ|²)^m`, which is summable against the Gaussian `e^{-π|ξ|²a}` on every half-line `(a,∞)`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.LamRightHalf.Defs
import Submission.Work.FIArea6Hecke.R.continuousOn_thetaDual

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The polynomial version of the Gaussian domination: for `a > 0` and `m : ℕ`,
`ξ ↦ (1+|ξ|²)^m·e^{-π|ξ|²a}` is summable over `ℤ²`. -/
lemma summable_poly_gauss (m : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun p : ℤ × ℤ => (1 + ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) ^ m *
      Real.exp (-(Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * a)))) := by
  have h := Work.FIArea5.S16.summable_int_prod_exp_neg_sq_add (c := Real.pi * a)
    (by positivity) 0 m
  refine h.congr (fun p => ?_)
  have h1 : -(Real.pi * a) * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)
      + 0 * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)
      = -(Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * a)) := by ring
  rw [h1, mul_comm]
  ring_nf

/-- Continuity of `thetaDualM` on each half-line `(a,∞)`, `a > 0`. -/
theorem continuousOn_thetaDualM_Ioi (d : ℕ) {chi : GaussianInt → ℂ}
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (thetaDualM d chi m) (Set.Ioi a) := by
  set U : ℤ × ℤ → ℝ := fun ξ => ((4 * d : ℕ) : ℝ) ^ 2 *
      ((1 + ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2)) ^ m *
        Real.exp (-(Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * a)))) with hU
  have hmaj : Summable U := by
    rw [hU]
    exact (summable_poly_gauss m ha).mul_left _
  refine continuousOn_tsum (u := U) ?_ hmaj ?_
  · intro ξ
    have hcont : Continuous (fun w : ℝ => Complex.exp
        (((-(Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w)) : ℝ) : ℂ))) := by fun_prop
    exact ((continuous_const.mul continuous_const).mul hcont).continuousOn
  · intro ξ w hw
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal]
    have hsa : (0 : ℝ) ≤ (ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 := by positivity
    have hw' : a < w := hw
    have hexp : Real.exp (-(Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w)))
        ≤ Real.exp (-(Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * a))) := by
      apply Real.exp_le_exp.mpr
      have h1 : ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * a
          ≤ ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w :=
        mul_le_mul_of_nonneg_left (le_of_lt hw') hsa
      nlinarith [Real.pi_pos]
    calc ‖Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩‖ *
            ‖(((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) ^ m)‖ *
              Real.exp (-(Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w)))
        ≤ ((4 * d : ℕ) : ℝ) ^ 2 * (1 + ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2)) ^ m *
              Real.exp (-(Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w))) := by
          refine mul_le_mul (mul_le_mul (thetaDualGaussBound_aux d hchi _)
            (norm_pow_le_one_add_gnorm ξ m) (norm_nonneg _) (by positivity))
            le_rfl (Real.exp_pos _).le (by positivity)
      _ ≤ ((4 * d : ℕ) : ℝ) ^ 2 * (1 + ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2)) ^ m *
              Real.exp (-(Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * a))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = U ξ := by rw [hU]; ring

/-- **Continuity of the weight-`m` dual theta series on `(0,∞)`.** -/
theorem thetaDualM_continuous (d : ℕ) {chi : GaussianInt → ℂ}
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (m : ℕ) :
    ContinuousOn (thetaDualM d chi m) (Set.Ioi 0) := by
  intro w hw
  have hw0 : (0 : ℝ) < w := hw
  have hhalf : (0 : ℝ) < w / 2 := by linarith
  have hcont : ContinuousOn (thetaDualM d chi m) (Set.Ioi (w / 2)) :=
    continuousOn_thetaDualM_Ioi d hchi m hhalf
  have hmem : Set.Ioi (w / 2) ∈ nhds w :=
    isOpen_Ioi.mem_nhds (show w / 2 < w from by linarith)
  exact (hcont.continuousAt hmem).continuousWithinAt

end

end Work.FIArea6Hecke.R
