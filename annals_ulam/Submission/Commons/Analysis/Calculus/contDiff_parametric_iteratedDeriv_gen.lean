import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

open scoped ContDiff

/-- The partial derivative in the second variable of a smooth function on `P × ℝ` is smooth. -/
private lemma contDiff_deriv_snd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {G : P → ℝ → ℝ} (hG : ContDiff ℝ ∞ (fun p : P × ℝ => G p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : P × ℝ => deriv (fun v : ℝ => G p.1 v) p.2) := by
  let H : P × ℝ → ℝ := fun p => G p.1 p.2
  have hH : ContDiff ℝ ∞ H := hG
  have hfderiv : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  have hconst : ContDiff ℝ ∞ (fun _ : P × ℝ => ((0, 1) : P × ℝ)) := contDiff_const
  have hmain : ContDiff ℝ ∞ (fun p : P × ℝ => (fderiv ℝ H p) ((0, 1) : P × ℝ)) :=
    hfderiv.clm_apply hconst
  rw [← contDiffOn_univ] at hmain ⊢
  refine hmain.congr ?_
  intro p _
  have hdiffH_at : DifferentiableAt ℝ H (p.1, p.2) :=
    (hH.differentiable (by simp)).differentiableAt
  have hφdiff : DifferentiableAt ℝ (fun v : ℝ => (p.1, v)) p.2 :=
    (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt
  have hφfderiv : fderiv ℝ (fun v : ℝ => (p.1, v)) p.2 = ContinuousLinearMap.inr ℝ P ℝ :=
    (hasFDerivAt_prodMk_right p.1 p.2).fderiv
  have hfd : fderiv ℝ (fun v : ℝ => H (p.1, v)) p.2 =
      (fderiv ℝ H (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ P ℝ) := by
    rw [fderiv_fun_comp p.2 hdiffH_at hφdiff, hφfderiv]
  change deriv (fun v : ℝ => H (p.1, v)) p.2 = (fderiv ℝ H p) ((0, 1) : P × ℝ)
  calc
    deriv (fun v : ℝ => H (p.1, v)) p.2
        = (fderiv ℝ (fun v : ℝ => H (p.1, v)) p.2) 1 := by
          rw [fderiv_apply_one_eq_deriv]
    _ = ((fderiv ℝ H (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ P ℝ)) 1 := by
          rw [hfd]
    _ = (fderiv ℝ H p) ((0, 1) : P × ℝ) := by
          simp

lemma contDiff_parametric_iteratedDeriv_gen {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {G : P → ℝ → ℝ} (hG : ContDiff ℝ ∞ (fun q : P × ℝ => G q.1 q.2)) (k : ℕ) :
    ContDiff ℝ ∞ (fun q : P × ℝ => iteratedDeriv k (fun u : ℝ => G q.1 u) q.2) := by
  induction k with
  | zero =>
      simpa [iteratedDeriv_zero] using hG
  | succ k ih =>
      have hstep : ContDiff ℝ ∞ (fun p : P × ℝ =>
          deriv (fun v : ℝ => iteratedDeriv k (fun t : ℝ => G p.1 t) v) p.2) :=
        contDiff_deriv_snd (G := fun x v => iteratedDeriv k (fun t : ℝ => G x t) v) (by
          simpa using ih)
      rw [← contDiffOn_univ] at hstep ⊢
      refine hstep.congr ?_
      intro p _
      rw [iteratedDeriv_succ]

end Commons.Analysis.Calculus