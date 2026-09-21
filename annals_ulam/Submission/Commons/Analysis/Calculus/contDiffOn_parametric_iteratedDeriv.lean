import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

open Filter
open scoped Topology

private lemma contDiffOn_deriv_snd
    {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => G p.1 p.2) U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => deriv (fun v : ℝ => G p.1 v) p.2) U := by
  let H : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => G p.1 p.2
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H U := hG
  have hfderiv : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ H) U :=
    hH.fderiv_of_isOpen hU (by simp)
  have hconst : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) U :=
    contDiffOn_const
  have hmain : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ H p) ((0, 1) : ℝ × ℝ)) U :=
    hfderiv.clm_apply hconst
  refine hmain.congr ?_
  intro p hp
  have hdiff : DifferentiableAt ℝ H p := by
    have hdiffOn : DifferentiableOn ℝ H U := hH.differentiableOn (by simp)
    exact hdiffOn.differentiableAt (hU.mem_nhds hp)
  have hdiffH_at : DifferentiableAt ℝ H (p.1, p.2) := by
    simpa using hdiff
  have hφdiff : DifferentiableAt ℝ (fun v : ℝ => (p.1, v)) p.2 :=
    (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt
  have hφfderiv : fderiv ℝ (fun v : ℝ => (p.1, v)) p.2 =
      ContinuousLinearMap.inr ℝ ℝ ℝ :=
    (hasFDerivAt_prodMk_right p.1 p.2).fderiv
  have hfd : fderiv ℝ (fun v : ℝ => H (p.1, v)) p.2 =
      (fderiv ℝ H (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) := by
    rw [fderiv_fun_comp p.2 hdiffH_at hφdiff, hφfderiv]
  change deriv (fun v : ℝ => H (p.1, v)) p.2 = (fderiv ℝ H p) ((0, 1) : ℝ × ℝ)
  calc
    deriv (fun v : ℝ => H (p.1, v)) p.2
        = (fderiv ℝ (fun v : ℝ => H (p.1, v)) p.2) 1 := by
          rw [fderiv_apply_one_eq_deriv]
    _ = ((fderiv ℝ H (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) 1 := by
          rw [hfd]
    _ = (fderiv ℝ H p) ((0, 1) : ℝ × ℝ) := by
          simp

lemma contDiffOn_parametric_iteratedDeriv
    {k : ℕ} {F : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => F p.1 p.2) U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => iteratedDeriv k (fun v : ℝ => F p.1 v) p.2) U := by
  induction k with
  | zero =>
      simpa [iteratedDeriv_zero] using hF
  | succ k ih =>
      have hprev : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun p : ℝ × ℝ => iteratedDeriv k (fun v : ℝ => F p.1 v) p.2) U := ih
      let G : ℝ → ℝ → ℝ := fun x v => iteratedDeriv k (fun t : ℝ => F x t) v
      have hprevG : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => G p.1 p.2) U := by
        simpa [G] using hprev
      have hstep : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun p : ℝ × ℝ =>
            deriv (fun v : ℝ => iteratedDeriv k (fun t : ℝ => F p.1 t) v) p.2) U := by
        simpa [G] using contDiffOn_deriv_snd hU hprevG
      refine hstep.congr ?_
      intro p hp
      rw [iteratedDeriv_succ]

end Commons.Analysis.Calculus