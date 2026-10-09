import Mathlib
import Submission.Work.SSGRoute.ExtChain.subsingleton_ext_fpRegular
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ExtChain.FreeCover
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

/-- **`Ext^{≥1}` vanishes in a free first variable.**

`Rep.free Coeff G ι` is the representation on `ι →₀ Coeff[G]`, the free `ℤ[G]`-module on `ι`, hence
projective (`Rep.free_projective`, which needs *no* finiteness hypothesis); therefore
`Ext^{≥1}_G(Rep.free Coeff G ι, A) = 0` for every coefficient `A`, by
`Abelian.Ext.subsingleton_of_projective` (the engine also behind the on-disk
`ExtChain.subsingleton_ext_fpRegular`).

This is the shared brick of the dévissage in the coefficient `E`: the two-term resolution
`0 → ℤ[G]^n --p--> ℤ[G]^n → N_E → 0` of the base case
(`ExtChain.subsingleton_ext_dualMod_regular`) has both outer terms free, and `Ext^{≥2}` of a
direct sum of such terms is assembled from this vanishing componentwise; the snake step of the
induction uses it in the same way. -/
theorem subsingleton_ext_free_firstVariable (G : Type) [Group G]
    (ι : Type) (A : Rep.{0} SSGRoute.PTExt.Coeff G) (r : ℕ) (hr : 1 ≤ r) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0} (Rep.free SSGRoute.PTExt.Coeff G ι) A r) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  haveI : CategoryTheory.Projective (Rep.free SSGRoute.PTExt.Coeff G ι) :=
    Rep.free_projective (k := SSGRoute.PTExt.Coeff) (G := G) (α := ι)
  exact CategoryTheory.Abelian.Ext.subsingleton_of_projective _ A n

end Work.SSGRoute.ExtChain
