import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.VopGen.truncHonest
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoBnds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.truncSlots`

The five slot facts consumed by the truncation half `VopGen.TruncStmt`, obtained from the engine
`slotFacts` and the pointwise dominations of `VopGen.truncFacts`.
-/
noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopGen

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces (HkSq HkMem HkIntegrand HkIntegrand_nonneg w Iz Iθ)

local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Aof" => Work.FTS.EllipticEst.H2W.Aof

/-- The uncurried form of a smooth function is continuous on the open quadrant. -/
theorem smoothOpen_continuousOn {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ContinuousOn (Function.uncurry F) Q0 :=
  (hF.forall 1).continuousOn

variable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}

/-- **The pure radial `j`-slot facts** of `A = z²∂_z²Ψ`, `j ≤ 2`. -/
theorem slotFacts_pure (hα1 : α ≤ 1) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (j : ℕ) (hj : j ≤ 2) :
    (∀ᵐ z ∂(volume.restrict Iz),
        IntegrableOn (fun θ => (Work.Spaces.DzIter j (Aof Ψ) z θ) ^ 2 * (w z) ^ 2
          * sgm α θ) Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Iθ, (Work.Spaces.DzIter j (Aof Ψ) z θ) ^ 2 * (w z) ^ 2
          * sgm α θ) Iz ∧
      IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter j (Aof Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2
          * sgm α p.2) (Iz ×ˢ Iθ) ∧
      (∫ p in Iz ×ˢ Iθ, (Work.Spaces.DzIter j (Aof Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
        = ∫ z in Iz, ∫ θ in Iθ, (Work.Spaces.DzIter j (Aof Ψ) z θ) ^ 2 * (w z) ^ 2
          * sgm α θ) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine slotFacts hα1 h.memA ?_ ?_
  · exact smoothOpen_continuousOn ((Work.FTS.EllipticEst.Prop.aofSmoothOpen hΨ).DzIter j)
  · intro z θ hz hθ hlt
    exact dom_pure hα1 z θ j hj hz hθ hlt

/-- **The `(1,1)`-slot facts** of `A = z²∂_z²Ψ`. -/
theorem slotFacts_mixed11 (hα1 : α ≤ 1) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    (∀ᵐ z ∂(volume.restrict Iz),
        IntegrableOn (fun θ => (Work.Spaces.pth (Work.Spaces.Dz (Aof Ψ)) z θ) ^ 2 * (w z) ^ 2
          * sgm α θ) Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Iθ, (Work.Spaces.pth (Work.Spaces.Dz (Aof Ψ)) z θ) ^ 2
          * (w z) ^ 2 * sgm α θ) Iz ∧
      IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.Dz (Aof Ψ)) p.1 p.2) ^ 2
          * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) ∧
      (∫ p in Iz ×ˢ Iθ, (Work.Spaces.pth (Work.Spaces.Dz (Aof Ψ)) p.1 p.2) ^ 2 * (w p.1) ^ 2
          * sgm α p.2
        = ∫ z in Iz, ∫ θ in Iθ, (Work.Spaces.pth (Work.Spaces.Dz (Aof Ψ)) z θ) ^ 2 * (w z) ^ 2
          * sgm α θ) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine slotFacts hα1 h.memA ?_ ?_
  · exact smoothOpen_continuousOn ((Work.FTS.EllipticEst.Prop.aofSmoothOpen hΨ).Dz.pth)
  · intro z θ hz hθ hlt
    exact dom_mixed11 hα1 hΨ z θ hz hθ hlt

/-- **The level-`0` slot facts** for an honest, smooth function `B`. -/
theorem slotFacts_zero (hα1 : α ≤ 1) {B : ℝ → ℝ → ℝ} (hB : HkMem α 0 B)
    (hBs : Work.FTS.EllipticEst.SmoothOpen B) :
    (∀ᵐ z ∂(volume.restrict Iz),
        IntegrableOn (fun θ => (B z θ) ^ 2 * (w z) ^ 2 * sgm α θ) Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Iθ, (B z θ) ^ 2 * (w z) ^ 2 * sgm α θ) Iz ∧
      IntegrableOn (fun p : ℝ × ℝ => (B p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) ∧
      (∫ p in Iz ×ˢ Iθ, (B p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
        = ∫ z in Iz, ∫ θ in Iθ, (B z θ) ^ 2 * (w z) ^ 2 * sgm α θ) := by
  refine slotFacts hα1 hB (smoothOpen_continuousOn hBs) ?_
  intro z θ hz hθ hlt
  exact dom_zero hα1 z θ hz hθ hlt

/-- **The angular slot facts** of `A = z²∂_z²Ψ` (`∂_θ²A`). -/
theorem slotFacts_ang (hα1 : α ≤ 1) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    (∀ᵐ z ∂(volume.restrict Iz),
        IntegrableOn (fun θ => (Work.Spaces.pthIter 2 (Aof Ψ) z θ) ^ 2 * (w z) ^ 2
          * sgm α θ) Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Iθ, (Work.Spaces.pthIter 2 (Aof Ψ) z θ) ^ 2 * (w z) ^ 2
          * sgm α θ) Iz ∧
      IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pthIter 2 (Aof Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2
          * sgm α p.2) (Iz ×ˢ Iθ) ∧
      (∫ p in Iz ×ˢ Iθ, (Work.Spaces.pthIter 2 (Aof Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
        = ∫ z in Iz, ∫ θ in Iθ, (Work.Spaces.pthIter 2 (Aof Ψ) z θ) ^ 2 * (w z) ^ 2
          * sgm α θ) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine slotFacts_zero hα1 (Work.FTS.EllipticEst.Prop.HkMem_zero_pthIter2_Ab h) ?_
  exact ((Work.FTS.EllipticEst.Prop.aofSmoothOpen hΨ).pth).pth

/-- **The `(1,2)`-slot facts** of `A = z²∂_z²Ψ` (`∂_θ²(D_z A)`). -/
theorem slotFacts_ddz (hα1 : α ≤ 1) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    (∀ᵐ z ∂(volume.restrict Iz),
        IntegrableOn (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Aof Ψ)) z θ) ^ 2
          * (w z) ^ 2 * sgm α θ) Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Aof Ψ)) z θ) ^ 2
          * (w z) ^ 2 * sgm α θ) Iz ∧
      IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Aof Ψ)) p.1 p.2) ^ 2
          * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) ∧
      (∫ p in Iz ×ˢ Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Aof Ψ)) p.1 p.2) ^ 2
          * (w p.1) ^ 2 * sgm α p.2
        = ∫ z in Iz, ∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Aof Ψ)) z θ) ^ 2
          * (w z) ^ 2 * sgm α θ) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine slotFacts_zero hα1 (hkMem_pth2_Dz_AofGen h) ?_
  exact ((Work.FTS.EllipticEst.Prop.aofSmoothOpen hΨ).Dz.pth).pth

end Work.FTS.ClassC.VopGen
