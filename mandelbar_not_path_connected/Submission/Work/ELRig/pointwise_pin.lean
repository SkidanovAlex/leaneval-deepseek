import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.rayCylLift_far_left_pin

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

/-- **Pointwise pin.**  A point of the first lift `L.γ₁` that already lies in the far-left half
plane `{w : ℂ | w.re < -L.R}` is the `Ψ`-preimage *within that half plane* of its own ray point
`rayPt α₁ (L.τ u)`.

The argument is the one of `rayCylLift_far_left_pin`, but with the explicit witness `L.γ₁ u` in
place of the "far enough left" index `sstar`: by hypothesis `L.γ₁ u` lies in the half plane
`{w : ℂ | w.re < -L.R}`, so `rayPt α₁ (L.τ u) = fl.Ψ (L.γ₁ u)` is in the image of `fl.Ψ` on that
half plane (`L.hΨ₁`), and `Function.invFunOn` picks a point of the half plane
(`Function.invFunOn_mem`) with image `rayPt α₁ (L.τ u)` (`Function.invFunOn_eq`).  Both that point
and `L.γ₁ u` lie in `{w | w.re < -L.R}`, where `fl.Ψ` is injective by `L.hinj`; hence they are
equal. -/
theorem pointwise_pin {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {u : ℝ} (hu : (L.γ₁ u).re < -L.R) :
    L.γ₁ u = Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R}
      (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u)) := by
  have hwit : ∃ w ∈ {w : ℂ | w.re < -L.R},
      fl.Ψ w = Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u) :=
    ⟨L.γ₁ u, hu, L.hΨ₁ u⟩
  have hmem : Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R}
      (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u)) ∈ {w : ℂ | w.re < -L.R} :=
    Function.invFunOn_mem hwit
  have heq : fl.Ψ (L.γ₁ u) = fl.Ψ (Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R}
      (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u))) := by
    rw [L.hΨ₁ u, Function.invFunOn_eq hwit]
  exact L.hinj hu hmem heq

end Work.ELRig
