import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.Defs
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.rayPt_iterate
import Submission.Work.ELRig.exists_local_angle_at_lift
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.sideFlipChart_crossing
import Submission.Work.ELRig.sideFlip_at_ray
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

/-- **The side flips exactly at a transversal crossing.**  At a point `s₀` which is crossed
transversally by the horizontal line through `L.γ₁ s₀` (i.e. the imaginary part of `γ₁` changes
sign strictly at `s₀`), the two points `L.γ₁ s₀ ± t` of that line are sent by `Ψ` to the two
*opposite* sides of the `α`-pair `P` — and conversely.

The proof straightens the ray `R(α₁)` by the Böttcher chart `sideFlipChart` (which sends `R(α₁)`
to the real axis and `L.γ₁ s₀` to `1`): both the "crossing" and the "side flip" become the
statement that the imaginary part of the chart changes sign along the horizontal line, so the two
fronts of the biconditional are literally the same. -/
theorem side_flip_at_crossing {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P)
    {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R)
    (hsimple : ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      L.γ₁ s₀ + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
      L.γ₁ s₀ - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) :
    ((∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₁ s).im < (L.γ₁ s₀).im) ∧
        (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₁ s₀).im < (L.γ₁ s).im)) ∨
      (∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₁ s₀).im < (L.γ₁ s).im) ∧
        (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₁ s).im < (L.γ₁ s₀).im))) ↔
    (∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      (fl.Ψ (L.γ₁ s₀ + t) ∈ Work.EL.pairSide P ↔
        ¬ (fl.Ψ (L.γ₁ s₀ - t) ∈ Work.EL.pairSide P))) := by
  rw [sideFlip_at_ray d fl L P hPa hPb hPy hside hre hsimple]
  exact sideFlipChart_crossing d fl L hre hsimple

end Work.ELRig
