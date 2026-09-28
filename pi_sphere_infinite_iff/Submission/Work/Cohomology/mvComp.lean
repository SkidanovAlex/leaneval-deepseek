import Mathlib
import Submission.Work.Cohomology.SmallSES

/-!
# The Mayer–Vietoris sequence is a complex

This file proves `mvComp`: the composite of the two maps of the Mayer–Vietoris sequence

`C_*(U ∩ V) --mvLeft--> C_*(U) ⊞ C_*(V) --mvRight--> C^{U,V}_*(X)`

is zero.  Concretely, `mvLeft` sends a chain `z` to the pair `(z, z)` (the two chains viewed in
`X` through the inclusions `U ↪ X`, `V ↪ X`), while `mvRight` sends `(a, b)` to `a - b` (the
chain maps `smallOfU`, `smallOfV` induced by those inclusions, the second one with a sign).
Hence the composite is `z - z = 0`.

The verification is purely functorial.  The two composites

`toSSet.map (inclUVU) ≫ smallLiftU`  and  `toSSet.map (inclUVV) ≫ smallLiftV`

are equal: after composing with the inclusion of the small subcomplex into the singular
simplicial set of `X` (a monomorphism), both are the simplicial map induced by the inclusion
`U ∩ V ↪ X`.  Applying the simplicial chain complex functor and combining with
`biprod.lift_desc` gives the result.

## Main results

* `mvComp` — the Mayer–Vietoris sequence is a complex.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- The two inclusions `U ∩ V ↪ U ↪ X` and `U ∩ V ↪ V ↪ X` are the same map, namely the
inclusion of `U ∩ V` in `X`. -/
theorem inclUVU_comp_inclUX (U V : Set X) :
    inclUVU U V ≫ inclUX U = inclUVV U V ≫ inclVX V := by
  apply TopCat.hom_ext
  ext x
  simp [inclUVU, inclUX, inclUVV, inclVX]

/-- The simplicial maps `Simp(U ∩ V) ⟶ small(U,V)` obtained from `smallLiftU` and `smallLiftV`
agree: both send a simplex of `U ∩ V` to the corresponding (small) singular simplex of `X`. -/
theorem smallLiftU_comp_inclUVU (U V : Set X) :
    TopCat.toSSet.map (inclUVU U V) ≫ smallLiftU U V
      = TopCat.toSSet.map (inclUVV U V) ≫ smallLiftV U V := by
  apply (cancel_mono (smallSubcomplex U V).ι).1
  rw [smallLiftU, smallLiftV, Category.assoc, Category.assoc, SSet.Subcomplex.lift_ι,
    SSet.Subcomplex.lift_ι]
  rw [← Functor.map_comp, ← Functor.map_comp, inclUVU_comp_inclUX]

/-- At the level of simplicial chains the two composites `C_*(U ∩ V) ⟶ C^{U,V}_*(X)` obtained
by first mapping into the chains of `U` (resp. of `V`) and then applying `smallOfU` (resp.
`smallOfV`) agree. -/
theorem chainSmallOfU_comp_inclUVU (U V : Set X) :
    SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ) ≫ smallOfU U V
      = SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ) ≫
          smallOfV U V := by
  dsimp only [smallOfU, smallOfV]
  rw [← Functor.map_comp, ← Functor.map_comp, smallLiftU_comp_inclUVU]

/-- **The Mayer–Vietoris sequence is a complex**: the composite of `mvLeft` and `mvRight` is
zero. -/
theorem mvComp {X : TopCat} (U V : Set X) :
    CategoryTheory.CategoryStruct.comp (mvLeft U V) (mvRight U V) = 0 := by
  rw [mvLeft, mvRight, biprod.lift_desc, Preadditive.comp_neg, chainSmallOfU_comp_inclUVU]
  simp

end

end Work.Cohomology
