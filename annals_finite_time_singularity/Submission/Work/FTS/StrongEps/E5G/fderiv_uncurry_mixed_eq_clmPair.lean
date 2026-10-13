import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E5Aux3.contDiffOn_two_of_jetLim
import Submission.Work.FTS.StrongEps.E5Aux.clmPairAPI

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false

/-- The `D_z`-slot is `z` times the plain `z`-derivative of the slot: this is the definitional
identity `mixed (j+1) i u = Dz (mixed j i u)`. -/
theorem mixed_succ_left_eq (u : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed (j + 1) i u z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed j i u) z θ := rfl

/-- **The Fréchet derivative of an uncurried mixed slot.**  On the open quadrant, for
`u ∈ C^∞`, the derivative of `p ↦ D_z^j D_θ^i u (p.1, p.2)` is the pair of the next slots,
divided by the factors `z` resp. `sin(2θ)` carried by the operators `D_z`, `D_θ`. -/
theorem fderiv_uncurry_mixed_eq_clmPair {u : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen u)
    (j i : ℕ) {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    fderiv ℝ (Function.uncurry (Work.Spaces.mixed j i u)) p
      = Work.FTS.StrongEps.E5Aux.clmPair
          (Work.Spaces.mixed (j + 1) i u p.1 p.2 / p.1,
           Work.Spaces.mixed j (i + 1) u p.1 p.2 / Real.sin (2 * p.2)) := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed j i u)) p :=
    (((hsm.mixed j i).forall 2).differentiableOn (by norm_num)).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  rw [Work.FTS.StrongEps.E5Aux.fderiv_uncurry_eq_clmPair hdiff]
  have hpz : Work.Spaces.pz (Work.Spaces.mixed j i u) p.1 p.2
      = Work.Spaces.mixed (j + 1) i u p.1 p.2 / p.1 := by
    have h : Work.Spaces.mixed (j + 1) i u p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.mixed j i u) p.1 p.2 :=
      mixed_succ_left_eq u j i p.1 p.2
    rw [h, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  have hpth : Work.Spaces.pth (Work.Spaces.mixed j i u) p.1 p.2
      = Work.Spaces.mixed j (i + 1) u p.1 p.2 / Real.sin (2 * p.2) :=
    Work.FTS.StrongEps.E5Aux3.pth_mixed_eq hsm j i p hp
  rw [hpz, hpth]

end Work.FTS.StrongEps.E5G
