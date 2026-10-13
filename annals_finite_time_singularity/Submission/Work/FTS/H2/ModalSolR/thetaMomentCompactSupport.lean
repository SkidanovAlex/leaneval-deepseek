import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.EllipticEst.ModalSolution.box_of_compactSupport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

/-- `box_of_compactSupport` in the form used below: a `φ` with compact support contained in the
open quadrant `Q0` vanishes identically in `z` outside some compact interval `[a,b]` with
`0 < a`. -/
private theorem exists_vanishing_interval {φ : ℝ → ℝ → ℝ}
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ z : ℝ, z ∉ Set.Icc a b → ∀ θ : ℝ, φ z θ = 0 := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  refine ⟨a, b, ha, hab, fun z hz θ => ?_⟩
  have hz' : z ∉ Set.Ioo a b := fun h => hz ⟨le_of_lt h.1, le_of_lt h.2⟩
  by_cases hθ : θ ∈ Set.Ioo c d
  · exact hbox (z, θ) (fun hp => hz' hp.1)
  · exact hbox (z, θ) (fun hp => hθ hp.2)

theorem thetaMomentCompactSupport {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) (m : ℕ) :
    HasCompactSupport (fun z => ∫ θ in Work.Spaces.Iθ,
        φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ∧
      tsupport (fun z => ∫ θ in Work.Spaces.Iθ,
        φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ⊆ Set.Ioi 0 := by
  obtain ⟨a, b, ha, hab, hvanish⟩ := exists_vanishing_interval hφc hφs
  -- the angular moment vanishes for every `z` outside the compact interval `[a,b]`
  have key : ∀ z : ℝ, z ∉ Set.Icc a b →
      (∫ θ in Work.Spaces.Iθ, φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        = 0 := by
    intro z hz
    have hfun : (fun θ : ℝ => φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        = fun _ => (0 : ℝ) := by
      funext θ
      rw [hvanish z hz θ]
      ring
    rw [hfun]
    simp
  refine ⟨?_, ?_⟩
  · exact HasCompactSupport.intro' isCompact_Icc isClosed_Icc fun z hz => key z hz
  · have hsupp : Function.support
        (fun z => ∫ θ in Work.Spaces.Iθ,
          φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ⊆ Set.Icc a b := by
      intro z hz
      by_contra h
      exact (Function.mem_support.mp hz) (key z h)
    intro z hz
    have h1 : z ∈ Set.Icc a b := closure_minimal hsupp isClosed_Icc hz
    exact lt_of_lt_of_le ha h1.1

end Work.FTS.H2.ModalSolR
