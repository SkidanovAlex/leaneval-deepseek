import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves.SolFire

/-- `z ∂_z` is a *local* operator: `pz f` at a point of the open quadrant `z > 0`,
`0 < θ < π/2` depends only on the values of `f` on that open quadrant. -/
private lemma pz_congr_of_agreeOnQ {f f' : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ := by
  rw [Work.Spaces.pz]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact h z' θ hz' hθ hθ2

/-- `∂_θ` is a *local* operator: `pth f` at a point of the open quadrant `z > 0`,
`0 < θ < π/2` depends only on the values of `f` on that open quadrant. -/
private lemma pth_congr_of_agreeOnQ {f f' : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ := by
  rw [Work.Spaces.pth]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ, hθ2⟩] with θ' hθ'
  exact h z θ' hz hθ'.1 hθ'.2

theorem LGammaT_congr_of_agreeOnQ {α : ℝ} {f f' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Coercivity.LGammaT α f z θ = Work.Coercivity.LGammaT α f' z θ := by
  have hf : f z θ = f' z θ := h z θ hz hθ hθ2
  have hpz : Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ := pz_congr_of_agreeOnQ hz hθ hθ2 h
  have hpt : Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ := pth_congr_of_agreeOnQ hz hθ hθ2 h
  have hLz : Work.Coercivity.L12f f z = Work.Coercivity.L12f f' z :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_of_lt hz) h
  have hTr : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Coercivity.Transport f z' θ' = Work.Coercivity.Transport f' z' θ' := by
    intro z' θ' hz' hθ' hθ2'
    simp only [Work.Coercivity.Transport, Work.Spaces.Dth, pth_congr_of_agreeOnQ hz' hθ' hθ2' h]
  have hL0 : Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
      = Work.Coercivity.L12f (Work.Coercivity.Transport f') 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl 0) hTr
  simp only [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.L,
    Work.Coercivity.Proj]
  rw [hL0, hLz, hf]
  simp only [Work.Coercivity.Transport, Work.Spaces.Dth, Work.Spaces.Dz, hpz, hpt]

end Work.FTS_FinalLeaves.SolFire
