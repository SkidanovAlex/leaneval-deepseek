import Mathlib
import Submission.Work.Charts.RochData_exists_effective_of_genus_le_deg
import Submission.Work.CurveBasics.Order.deg_div

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.JacFinal

universe u

theorem rr7_of_rochData {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (R : Work.Charts.RochData C) :
    ∀ {F : Type u} [Field F] [Algebra K F] (A : Work.GCBasics.Dv C F),
      (R.g : ℤ) ≤ Work.GCBasics.Ddeg C F A →
      ∃ E : Work.GCBasics.Dv C F, E.IsEffective ∧
        Work.GCBasics.Ddeg C F E = Work.GCBasics.Ddeg C F A ∧
        Work.GCBasics.LinEquiv C A E := by
  intro F _ _ A h
  -- RR7: a divisor of degree at least the genus is linearly equivalent to an effective one.
  obtain ⟨E, hEeff, hLE⟩ :=
    Work.Charts.RochData_exists_effective_of_genus_le_deg (C := C) R A h
  refine ⟨E, hEeff, ?_, hLE⟩
  -- LinEquiv preserves the degree: the difference is a principal divisor, of degree zero.
  rw [Work.GCBasics.linEquiv_def] at hLE
  obtain ⟨f, _hfne, hfdiv⟩ := hLE
  have h0 : Work.GCBasics.Ddeg C F (A - E) = 0 := by
    rw [← hfdiv]
    exact Work.CurveBasics.Order.deg_div (Work.CurveBasics.Curve.baseChange C F) f
  rw [map_sub] at h0
  linarith

end Work.JacFinal
