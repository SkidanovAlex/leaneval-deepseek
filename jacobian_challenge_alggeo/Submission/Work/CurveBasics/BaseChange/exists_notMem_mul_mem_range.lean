import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.BaseChange

theorem exists_notMem_mul_mem_range {A R K : Type*} [CommRing A] [CommRing R] [Field K]
    [Algebra A R] [Algebra R K] [Algebra A K] [IsScalarTower A R K]
    (m : Ideal A) [m.IsPrime] [IsLocalization.AtPrime R m] (f : K)
    (hf : f ∈ (algebraMap R K).range) :
    ∃ s : A, s ∉ m ∧ f * algebraMap A K s ∈ (algebraMap A K).range := by
  obtain ⟨r, hr⟩ := hf
  obtain ⟨x, hx⟩ := IsLocalization.surj (m.primeCompl : Submonoid A) r
  refine ⟨x.2.1, ?_, x.1, ?_⟩
  · exact x.2.2
  · have h2 : (algebraMap R K) r * algebraMap A K (x.2 : A) = algebraMap R K ((algebraMap A R) x.1) := by
      rw [IsScalarTower.algebraMap_apply A R K (x.2 : A), ← map_mul, hx]
    rw [← hr, h2]
    exact IsScalarTower.algebraMap_apply A R K x.1

end Work.CurveBasics.BaseChange
