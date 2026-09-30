import Mathlib
import Submission.Work.RiemannRoch.Differentials

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.RiemannRoch.RR

/-- Multiplication by a nonzero rational function is a bijective endomorphism of the adèle
space, so it can be cancelled on the right: precomposition with `mulAdele C f` kills no
nonzero functional. -/
theorem smulW_eq_zero_iff {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    {f : C.functionField} (hf : f ≠ 0) (ω : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)) :
    Work.RiemannRoch.Curve.smulW C f ω = 0 ↔ ω = 0 := by
  constructor
  · intro h
    ext a
    obtain ⟨b, hb⟩ := Work.RiemannRoch.Curve.mulAdele_surjective C hf a
    have hb0 : Work.RiemannRoch.Curve.smulW C f ω b = 0 := by
      simpa using congrArg (fun φ : Module.Dual k (Work.RiemannRoch.Curve.Adeles C) => φ b) h
    simpa [Work.RiemannRoch.Curve.smulW_apply, hb] using hb0
  · rintro rfl
    simp [Work.RiemannRoch.Curve.smulW]

end Work.RiemannRoch.RR
