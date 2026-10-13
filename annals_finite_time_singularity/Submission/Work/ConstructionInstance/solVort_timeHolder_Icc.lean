import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.ConstructionInstance.lam_pos_le_on_Icc
import Submission.Work.ConstructionInstance.timeHolderOnBall_of_timeDeriv_le_Icc
import Submission.Work.ConstructionInstance.timeDeriv_selfSimVort_le_Icc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The time-Hölder regularity of the constructed vorticity on the physical strip `[0,S]`.**

`Reduced.solVort_timeHolder` delivers the same statement for the *two-sided* window
`window S = Icc (-1) (S+1)`, which is legitimate only for strips with `S + 1 < T` (a window
straddling `T` cannot carry a uniform constant, finding E).  The challenge's regularity clause is
phrased on the *one-sided* strip `Icc 0 S`, `S < T`, so it needs the version where the mean value
theorem is applied to the convex set `Icc 0 S` itself: on that strip the modulation `λ̄` is
bounded below by a positive `m` (it is positive and continuous on `preWindow T = Ioo (-2) T`, and
`Icc 0 S` is a compact interval inside it), whence the weighted box
`λ̄(t)²‖∂ₜω‖ ≤ K(20p + Cg + Cg')` of `bddDt_selfSimVort` becomes the unweighted bound
`‖∂ₜω‖ ≤ K(20p + Cg + Cg')/m² =: Λ`; the mean value theorem then gives
`‖ω z t - ω z τ‖ ≤ Λ|t - τ| ≤ Λ·max S 1·|t - τ|^α` for `t, τ ∈ Icc 0 S`.

The three ingredients are `lam_pos_le_on_Icc`, `timeDeriv_selfSimVort_le_Icc` (the unweighted
`∂ₜ`-bound on the strip) and the mean value theorem on `Icc 0 S`
(`timeHolderOnBall_of_timeDeriv_le_Icc`); the differentiability of the slices is
`hasDerivAt_selfSimVort_slice`. -/
theorem solVort_timeHolder_Icc {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ S ∈ Set.Ioo (0 : ℝ) P.T, ∃ H : ℝ, 0 ≤ H ∧
      ∀ z ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) P.R,
        ∀ t ∈ Set.Icc 0 S, ∀ τ ∈ Set.Icc 0 S,
          ‖Work.ConstructionInstance.solVort P z t - Work.ConstructionInstance.solVort P z τ‖
            ≤ H * |t - τ| ^ (α : ℝ) := by
  intro S hS
  have hS0 : 0 ≤ S := le_of_lt hS.1
  have hST : S < P.T := hS.2
  have hp : 0 < profExp α := profExp_pos P.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [P.hα13]
  have hα1 : (α : ℝ) ≤ 1 := by linarith [P.hα13]
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ P.Cg := le_trans (abs_nonneg _) (bdd_g P 0 0 le_rfl hI0)
  have hCg' : 0 ≤ P.Cg' := by simpa using P.hg2 0 0 le_rfl hI0
  -- the strip `Icc 0 S` sits inside the half-window on which the `λ̄`-data is stated
  have hsub : Set.Icc (0 : ℝ) S ⊆ preWindow P.T :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- a uniform positive lower bound for the modulation on the strip
  obtain ⟨m, hmpos, hmle⟩ := lam_pos_le_on_Icc hS0 hST P.hlam P.hlamdif
  -- the resulting unweighted bound `Λ` on `∂ₜω`
  set Λ : ℝ := P.K * (20 * profExp α + P.Cg + P.Cg') / m ^ 2 with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    exact div_nonneg (mul_nonneg P.hK (by linarith)) (by positivity)
  -- differentiability of every time slice on the strip
  have hdiff : ∀ z ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) P.R,
      ∀ s ∈ Set.Icc 0 S,
        HasDerivAt (fun t => solVort P z t)
          (FiniteTimeSingularity.timeDeriv (solVort P) z s) s := by
    intro z _hz s hs
    exact hasDerivAt_selfSimVort_slice (p := profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) P.hgdiff P.hlam P.hlamdif (hsub hs) z
  -- the uniform bound on `∂ₜω` on the strip
  have hbd : ∀ z ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) P.R,
      ∀ s ∈ Set.Icc 0 S, ‖FiniteTimeSingularity.timeDeriv (solVort P) z s‖ ≤ Λ := by
    intro z _hz s hs
    exact timeDeriv_selfSimVort_le_Icc (p := profExp α) hp hp1 (bdd_g P) P.hg2 P.hgdiff
      P.hK P.hlam P.hlamdif P.hlamd hmpos hsub hmle hs z
  obtain ⟨H, hH0, hH⟩ := timeHolderOnBall_of_timeDeriv_le_Icc (α := (α : ℝ)) (Λ := Λ)
    (R := P.R) (S := S) (ω := solVort P) hS0 P.hα hα1 hΛ hdiff hbd
  exact ⟨H, hH0, hH⟩

end Work.ConstructionInstance
