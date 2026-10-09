import Mathlib
import Submission.Work.CohomologicallyTrivial.ptorsion_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The complex `0 → pX → X → X/pX → 0` is short exact

For any morphism `f : A ⟶ B` in an abelian category, the canonical complex

`0 → Abelian.image f → B → cokernel f → 0`

built out of the abelian image inclusion and the cokernel projection is short exact. Indeed the
image inclusion is by definition the kernel of the cokernel projection, so the composite
`image.ι f ≫ cokernel.π (image.ι f)` vanishes by the cokernel condition, and both maps are
(`kernel.ι` hence mono, `cokernel.π` hence epi).

Since `pSubRepIncl p X` and `pQuotRepProj p X` are exactly `Abelian.image.ι (p • 𝟙 X)` and
`cokernel.π (p • 𝟙 X)`, this applies verbatim with `f = p • 𝟙 X` in `Rep ℤ G`.
-/

namespace Work.CohomologicallyTrivial

open CategoryTheory Limits

/-- General fact: for any `f : A ⟶ B` in an abelian category, the complex
`0 → Abelian.image f → B → cokernel f → 0` is short exact. -/
lemma image_ι_cokernel_π_shortExact {C : Type*} [Category C] [Abelian C] {A B : C} (f : A ⟶ B) :
    (ShortComplex.mk (Abelian.image.ι f) (cokernel.π f)
      (Abelian.image_ι_comp_eq_zero (cokernel.condition f))).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  simp

theorem pShortComplex_shortExact {G : Type} [Group G] (p : ℕ) (X : Rep.{0, 0, 0} ℤ G) :
    (Work.CohomologicallyTrivial.pShortComplex p X).ShortExact := by
  exact image_ι_cokernel_π_shortExact (C := Rep.{0, 0, 0} ℤ G) (p • 𝟙 X)

end Work.CohomologicallyTrivial
