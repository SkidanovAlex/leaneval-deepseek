import Submission.Work.SSGRoute.E1aClean.BaseChangeSquare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # First wiring step of the level-change square

The square's proof begins by replacing `z` by a `PhiE`-generator, which is legitimate because `PhiE`
is surjective with no finiteness hypotheses.  This file records that step as a standalone lemma, so
the queued prover can start from it, and so that the step's *spelling* is verified without touching
`BaseChangeSquare.lean` (which sits in the delegation's `depends_on` and must stay green). -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

/-- **Step 1 of the square's proof**: every `z` in the source of `ExtChain.e1cMap` is the image of a
`PhiE`-generator, so the square may be proved on generators. -/
theorem e1cMap_eq_of_PhiE_generator (L : IntermediateField k K)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (z : CategoryTheory.Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK k K) 1) :
    ∃ w : CategoryTheory.Abelian.Ext
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) R)
        (SSGRoute.PTExt.unitsK k K) 0,
      Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K) R
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) R w)
        = Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K) R z := by
  obtain ⟨w, hw⟩ := Work.SSGRoute.ExtChain.E1cGeneric.PhiE_surjective (k := k) (Ω := Ω) (K := K) R z
  exact ⟨w, by rw [hw]⟩

end

end Work.SSGRoute.E1aClean
