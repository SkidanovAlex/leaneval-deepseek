import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.LogCoord
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.contDiff_logPull

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The two slots of `fderiv (logPull g)`

In the log coordinates `(s, ζ) = (log z, log tan θ)` the pull-back
`logPull g (s, ζ) = g (e^s) (arctan (e^ζ))` of a profile `g` has
the two directional derivatives

  `∂_s (logPull g) = D_z g (e^s) (arctan (e^ζ))`,
  `∂_ζ (logPull g) = D_θ g (e^s) (arctan (e^ζ)) / 2`,

which is the statement below.  The factor `1/2` is
`∂_ζ (arctan (e^ζ)) = e^ζ/(1 + e^{2ζ}) = sin (2 arctan (e^ζ)) / 2`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts

open scoped Real Topology

/-- The `θ`-slice of a function that is `C^∞` on the open quadrant is differentiable at every
interior angle, with derivative the `θ`-partial `pth`.  (The `θ`-analogue of
`Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice`.) -/
private lemma hasDerivAt_thslice {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ :=
  ((hF.curry_θ hz).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt

theorem fderiv_logPull_slots {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
        (ContinuousLinearMap.inl ℝ ℝ ℝ (1 : ℝ))
      = Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))
    ∧ fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
        (ContinuousLinearMap.inr ℝ ℝ ℝ (1 : ℝ))
      = Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2 := by
  have hgS : Work.FTS.EllipticEst.SmoothOpen g := Work.FTS.EllipticEst.smoothOpen_of_forall hg
  have hmem : Real.arctan (Real.exp y.2) ∈ Set.Ioo 0 (π / 2) :=
    ⟨Real.arctan_pos.mpr (Real.exp_pos y.2), Real.arctan_lt_pi_div_two _⟩
  -- `logPull g` is smooth (it is `C^n` for every `n`), hence differentiable everywhere.
  have hdiff : DifferentiableAt ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y :=
    ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.contDiff_logPull hg
      1).differentiable (by simp)).differentiableAt
  have hL : HasFDerivAt (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
      (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y) y := hdiff.hasFDerivAt
  constructor
  · -- first slot: the direction `(1,0)`, i.e. the `s = log z` derivative
    have hA : HasDerivAt (fun s : ℝ => (s, y.2)) (1, 0) y.1 := by
      simpa using (hasDerivAt_id y.1).prodMk (hasDerivAt_const (c := y.2) (x := y.1))
    have c1 := HasFDerivAt.comp_hasDerivAt_of_eq
      (l := Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
      (l' := fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y) (y := y)
      (f := fun s : ℝ => (s, y.2)) (f' := (1, 0)) (x := y.1) hL hA (by rfl)
    -- the same derivative, computed with the chain rule
    have c2 : HasDerivAt ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
        ∘ (fun s : ℝ => (s, y.2)))
        (Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))) y.1 := by
      have hslice := hgS.hasDerivAt_slice hmem (Real.exp_pos y.1)
      have hderiv : Work.Spaces.pz g (Real.exp y.1) (Real.arctan (Real.exp y.2)) * Real.exp y.1
          = Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2)) := by
        simp only [Work.Spaces.Dz]; ring
      rw [← hderiv]
      exact hslice.comp y.1 (Real.hasDerivAt_exp y.1)
    simpa only [ContinuousLinearMap.inl_apply] using c1.unique c2
  · -- second slot: the direction `(0,1)`, i.e. the `ζ = log tan θ` derivative
    have hA : HasDerivAt (fun s : ℝ => (y.1, s)) (0, 1) y.2 := by
      simpa using (hasDerivAt_const (c := y.1) (x := y.2)).prodMk (hasDerivAt_id y.2)
    have c1 := HasFDerivAt.comp_hasDerivAt_of_eq
      (l := Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
      (l' := fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y) (y := y)
      (f := fun s : ℝ => (y.1, s)) (f' := (0, 1)) (x := y.2) hL hA (by rfl)
    have c2 : HasDerivAt ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
        ∘ (fun s : ℝ => (y.1, s)))
        (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2) y.2 := by
      have hslice := hasDerivAt_thslice hgS (Real.exp_pos y.1) hmem
      -- `∂_ζ (arctan (e^ζ)) = e^ζ / (1 + e^{2ζ})`
      have hinner : HasDerivAt (fun s : ℝ => Real.arctan (Real.exp s))
          (1 / (1 + (Real.exp y.2) ^ 2) * Real.exp y.2) y.2 :=
        (Real.hasDerivAt_arctan (Real.exp y.2)).comp y.2 (Real.hasDerivAt_exp y.2)
      have hcomp := hslice.comp y.2 hinner
      -- the trigonometric form of the same scalar
      have hsc : Real.sin (2 * Real.arctan (Real.exp y.2)) / 2
          = Real.exp y.2 / (1 + (Real.exp y.2) ^ 2) := by
        rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
        have h1 : (0:ℝ) < 1 + (Real.exp y.2)^2 := by positivity
        have hs : Real.sqrt (1 + (Real.exp y.2)^2) ≠ 0 := by positivity
        field_simp
        rw [Real.sq_sqrt h1.le]
      have hderiv : Work.Spaces.pth g (Real.exp y.1) (Real.arctan (Real.exp y.2))
            * (1 / (1 + (Real.exp y.2) ^ 2) * Real.exp y.2)
          = Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2 := by
        have h1 : (1:ℝ) / (1 + (Real.exp y.2) ^ 2) * Real.exp y.2
            = Real.exp y.2 / (1 + (Real.exp y.2) ^ 2) := by
          rw [div_mul_eq_mul_div, one_mul]
        rw [h1, ← hsc]
        simp only [Work.Spaces.Dth]
        ring
      rw [hderiv] at hcomp
      exact hcomp
    simpa only [ContinuousLinearMap.inr_apply] using c1.unique c2

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts
