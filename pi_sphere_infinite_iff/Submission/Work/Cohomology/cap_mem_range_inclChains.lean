import Mathlib
import Submission.Work.Cohomology.cap_natural
import Submission.Work.Cohomology.exists_capH
import Submission.Work.Cohomology.pd_good

/-!
# The cap product preserves the chains of a subspace

If a chain `β` of degree `k + m` on `M` already lies in the image of the inclusion of the chains of
a subspace `S ⊆ M`, then so does `β ⌢ φ` for every degree `k` cochain `φ` on `M`.

This is the naturality of the cap product (`cap_natural`) applied to the map of simplicial sets
induced by the inclusion `S ↪ M`:

  `incl_*(β' ⌢ incl*φ) = (incl_* β') ⌢ φ`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

theorem cap_mem_range_inclChains {M : TopCat} (S : Set M) (k m : ℕ)
    (φ : Cochain ℤ (TopCat.toSSet.obj M) k) {β : (singularChains ℤ M).X (k + m)}
    (hβ : β ∈ LinearMap.range ((inclChains M S).f (k + m)).hom) :
    cap ℤ (TopCat.toSSet.obj M) φ m β ∈ LinearMap.range ((inclChains M S).f m).hom := by
  obtain ⟨β', hβ'⟩ := hβ
  refine ⟨cap ℤ (TopCat.toSSet.obj (TopCat.of S))
    (φ.comp (((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl M S))
      (ModuleCat.of ℤ ℤ)).f k).hom)) m β', ?_⟩
  rw [← hβ']
  exact cap_natural ℤ (TopCat.toSSet.map (subtypeIncl M S)) φ β'

end

end Work.Cohomology
