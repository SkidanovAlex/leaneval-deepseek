import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.STSigma

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

theorem dzIterSumConstMul {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ) (F : ι → ℝ → ℝ → ℝ)
    (hF : ∀ k ∈ s, Work.FTS.EllipticEst.SmoothOpen (F k)) (j : ℕ) :
    Set.EqOn
      (Function.uncurry (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)))
      (Function.uncurry (fun z θ => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z θ))
      Work.FTS.EllipticEst.Q0 := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
    intro p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    -- the two functions agree at level `j` on the open quadrant, hence so do their `z`-slices
    have hpz : Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ
        = Work.Spaces.pz (fun z θ => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z θ) z θ :=
      Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ1⟩)
    -- the summand slices are differentiable at `z`
    have hdiff : ∀ k ∈ s, DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter j (F k) z' θ) z := by
      intro k hk
      have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j (F k)) :=
        (hF k hk).DzIter j
      exact ((h1.curry_z ⟨hθ, hθ1⟩).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hz)
    -- `∂_z` of the sum is the sum of the `∂_z`'s (the coefficients depend on `θ` only)
    have hpz2 : Work.Spaces.pz
          (fun z θ => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z θ) z θ
        = ∑ k ∈ s, c k θ * Work.Spaces.pz (Work.Spaces.DzIter j (F k)) z θ := by
      show deriv (fun z' => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z' θ) z = _
      rw [show (fun z' => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z' θ)
            = ∑ k ∈ s, (fun z' => c k θ * Work.Spaces.DzIter j (F k) z' θ) from by
          funext z'
          rw [Finset.sum_apply]]
      rw [deriv_sum (fun k hk => (hdiff k hk).const_mul (c k θ))]
      exact Finset.sum_congr rfl fun k hk => deriv_const_mul_field (c k θ)
    show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ
        = ∑ k ∈ s, c k θ * Work.Spaces.DzIter (j + 1) (F k) z θ
    rw [show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ
          = z * Work.Spaces.pz
              (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ from rfl,
      hpz, hpz2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [show Work.Spaces.DzIter (j + 1) (F k) z θ
          = z * Work.Spaces.pz (Work.Spaces.DzIter j (F k)) z θ from rfl]
    ring

end Work.FTS.EllSol.VopAux
