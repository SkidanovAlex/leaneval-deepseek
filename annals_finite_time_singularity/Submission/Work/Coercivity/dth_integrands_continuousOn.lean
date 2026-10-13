import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.SmoothCompact_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- On the open box `(0,R) × (0,π/2)` all four integrands appearing in the
`D_θ`-coercivity estimate (the `z`-integration by parts of `∫∫ L(D_θ f)·D_θ f·w²·sin^{-γ}`)
are jointly continuous in `(z,θ)`.

Each integrand is a product of continuous factors: the derivatives are
`ContDiffOn` in a neighbourhood of the quadrant (hence continuous on the box),
`w(z)²` is continuous for `z > 0`, and `sin(2θ)^{-γ}` is continuous for
`0 < θ < π/2` because there `sin(2θ) > 0`. -/
theorem dth_integrands_continuousOn (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) (R : ℝ) (hR : 0 < R) :
    ContinuousOn (Function.uncurry (fun z θ => L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))) (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))
    ∧ ContinuousOn (Function.uncurry (fun z θ => (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ)) (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))
    ∧ ContinuousOn (Function.uncurry (fun z θ => (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))) (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))
    ∧ ContinuousOn (Function.uncurry (fun z θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2)) (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
  set Q : Set (ℝ × ℝ) := Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2) with hQ
  -- `Q` sits inside the open neighbourhood of the quadrant on which `f` is smooth
  have hQ_nbh : Q ⊆ Spaces.nbhU := by
    rw [hQ]
    exact Set.prod_mono (fun z hz => show (-1 : ℝ) < z from by linarith [hz.1])
      (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
  -- `sin(2θ) > 0` throughout the angular interval
  have hsin_pos : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  -- continuity of the derivative factors
  have hcontDth : ContinuousOn (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2) Q :=
    ((Spaces.SmoothNbhd.Dth hsm).continuousOn).mono hQ_nbh
  have hcontDthDth : ContinuousOn (fun p : ℝ × ℝ => Spaces.Dth (Spaces.Dth f) p.1 p.2) Q :=
    ((Spaces.SmoothNbhd.Dth (Spaces.SmoothNbhd.Dth hsm)).continuousOn).mono hQ_nbh
  have hcontpz : ContinuousOn (fun p : ℝ × ℝ => Spaces.pz (Spaces.Dth f) p.1 p.2) Q :=
    ((Spaces.SmoothNbhd.pz (Spaces.SmoothNbhd.Dth hsm)).continuousOn).mono hQ_nbh
  -- continuity of `𝓛(D_θ f)`
  have hcontLDth : ContinuousOn (fun p : ℝ × ℝ => L (Spaces.Dth f) p.1 p.2) Q := by
    have hexp : (fun p : ℝ × ℝ => L (Spaces.Dth f) p.1 p.2)
        = fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 + p.1 * Spaces.pz (Spaces.Dth f) p.1 p.2
            - 2 * Spaces.Dth f p.1 p.2 / (1 + p.1) := by
      funext p
      rw [L, Spaces.Dz]
    rw [hexp]
    refine (hcontDth.add (continuousOn_fst.mul hcontpz)).sub ?_
    exact ContinuousOn.div (hcontDth.const_mul 2) (continuousOn_const.add continuousOn_fst)
      (fun p hp => by have hz : 0 < p.1 := hp.1.1; intro h; linarith)
  -- continuity of the radial weight `w`
  have hcont_w : ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1) Q := by
    simp only [Spaces.w]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt hp.1.1)
  have hcont_w_sq : ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1 ^ 2) Q := hcont_w.pow 2
  -- continuity of the angular weight `sin(2θ)^{-γ}`
  have hcont_sin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) Q :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsin_pos p.2 hp.2)))
  -- continuity of `z ↦ 3/(1+z)`
  have hcont_den : ContinuousOn (fun p : ℝ × ℝ => (3 : ℝ) / (1 + p.1)) Q :=
    ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_fst)
      (fun p hp => by have hz : 0 < p.1 := hp.1.1; intro h; linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((hcontLDth.mul hcontDth).mul hcont_w_sq).mul hcont_sin
  · exact ((hcont_den.mul hcont_sin).mul hcontDthDth).mul hcontDth
  · exact ((hcontDth.pow 2).mul hcont_w_sq).mul hcont_sin
  · exact hcont_sin.mul (hcontDth.pow 2)

end Work.Coercivity
