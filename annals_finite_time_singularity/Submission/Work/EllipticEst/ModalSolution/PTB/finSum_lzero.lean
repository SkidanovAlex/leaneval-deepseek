import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.PTB

/--
`Lzero` on a finite linear combination of the Gegenbauer modes: the operator is a *linear*
differential operator, so it distributes over the finite sum, and each mode is an eigenfunction
(`eFam_Lzero`): `Lzero e_m = lam m • e_m`.

The `z`-argument is irrelevant (the summands do not depend on it); the proof reuses the
finite-sum differentiation lemmas of `Work.FTS.PhiStar.Series.psiTrunc_solves`
(`pthIter_two_sum_sep`, `pth_tan_sum_sep`), which are the `b m : ℝ → ℝ` version of the needed
identities with constant coefficients `b m = fun _ => a m`. -/
theorem finSum_lzero (a : ℕ → ℝ) (s : Finset ℕ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero
        (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ
      = ∑ m ∈ s,
          Work.FTS.PhiStar.Gegenbauer.lam m * a m
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  -- the angular modes are `C³`
  have he : ∀ m ∈ s, ∀ θ' : ℝ,
      DifferentiableAt ℝ (Work.FTS.PhiStar.Gegenbauer.eFam m) θ' := fun m _ θ' =>
    ((Work.FTS.PhiStar.Series.contDiff_eFam m).differentiable (by norm_num)).differentiableAt
  have he1 : ∀ m ∈ s,
      DifferentiableAt ℝ (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ := fun m _ =>
    ((ContDiff.deriv' (n := 2) (Work.FTS.PhiStar.Series.contDiff_eFam m)).differentiable
      (by norm_num)).differentiableAt
  -- the two derivative identities for the finite sum
  have hpthId : Work.Spaces.pthIter 2
        (fun z' θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ
      = ∑ m ∈ s, a m * deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ := by
    show Work.Spaces.pthIter 2 (fun z' θ' => ∑ m ∈ s,
        (fun _ : ℝ => a m) z' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ = _
    exact Work.FTS.PhiStar.Series.pthIter_two_sum_sep s (fun m _ => a m)
      Work.FTS.PhiStar.Gegenbauer.eFam z θ he he1
  have htanId : Work.Spaces.pth
        (fun z' θ' => Real.tan θ' * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ')) z θ
      = ∑ m ∈ s, a m * deriv (fun θ' : ℝ =>
          Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ := by
    show Work.Spaces.pth (fun z' θ' => Real.tan θ' * (∑ m ∈ s,
        (fun _ : ℝ => a m) z' * Work.FTS.PhiStar.Gegenbauer.eFam m θ')) z θ = _
    exact Work.FTS.PhiStar.Series.pth_tan_sum_sep s (fun m _ => a m)
      Work.FTS.PhiStar.Gegenbauer.eFam z θ hθ (fun m hm => he m hm θ)
  -- unfold `Lzero` on the (z-independent) sum
  have hLzeroId : Work.Elliptic.Lzero
        (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ
      = -(∑ m ∈ s, a m * deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ)
        + (∑ m ∈ s, a m * deriv (fun θ' : ℝ =>
            Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ)
        - 6 * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
    show -(Work.Spaces.pthIter 2
          (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ)
        + Work.Spaces.pth (fun z θ' => Real.tan θ'
            * (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ') z θ
        - 6 * (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ = _
    rw [hpthId, htanId]
  rw [hLzeroId]
  -- distribute the linear combination into the sum
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  -- the single-mode eigenrelation `Lzero e_m = lam m • e_m`
  have hLam : deriv (fun θ' : ℝ => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
      - deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ
      - 6 * Work.FTS.PhiStar.Gegenbauer.eFam m θ
      = Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
    have h2 : -(deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ)
        + deriv (fun t : ℝ => Real.tan t * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
        - 6 * Work.FTS.PhiStar.Gegenbauer.eFam m θ
        = Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
      have h4 := congrFun
        (Work.FTS.EllipticEst.Lzero1_eq_Lzero (Work.FTS.PhiStar.Gegenbauer.eFam m) z) θ
      rw [Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hθ z] at h4
      simpa only [Work.FTS.EllipticEst.Lzero1] using h4
    linarith [h2]
  have hdist : -(a m * deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ)
        + a m * deriv (fun θ' : ℝ => Real.tan θ' *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
        - 6 * (a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      = a m * (deriv (fun θ' : ℝ => Real.tan θ' *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
          - deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ
          - 6 * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by ring
  rw [hdist, hLam]
  ring

end Work.EllipticEst.ModalSolution.PTB
