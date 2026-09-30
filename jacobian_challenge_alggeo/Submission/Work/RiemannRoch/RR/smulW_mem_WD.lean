import Mathlib
import Submission.Work.RiemannRoch.Differentials

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.RiemannRoch.RR

universe u

theorem smulW_mem_WD {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    {f : C.functionField} (hf : f ≠ 0) {ω : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)}
    {D : C.Div} (hω : ω ∈ Work.RiemannRoch.Curve.WD C D) :
    Work.RiemannRoch.Curve.smulW C f ω ∈ Work.RiemannRoch.Curve.WD C (D + C.div f) := by
  rw [Work.RiemannRoch.Curve.mem_WD_iff] at hω ⊢
  intro a ha
  rw [Work.RiemannRoch.Curve.smulW_apply]
  refine hω (Work.RiemannRoch.Curve.mulAdele C f a) ?_
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp ha
  rw [map_add]
  refine Submodule.add_mem_sup (Work.RiemannRoch.Curve.mulAdele_mem_Asub C D f ha₁) ?_
  rw [← Work.RiemannRoch.Curve.comap_diagK_mulAdele C hf] at ha₂
  exact ha₂

end Work.RiemannRoch.RR
