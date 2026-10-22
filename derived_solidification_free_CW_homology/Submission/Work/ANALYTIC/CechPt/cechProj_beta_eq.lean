import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechTermDefs

/-!
# The binary expansion of the Čech nerve terms

For every `p` and every `j : Fin (p + 1)` the two composites

`cechTerm p --cechProj p j--> cantor --beta--> [0,1]`

are equal, because all coordinates of a point of `cechTerm p` have the same binary expansion
(`cechTerm_apply_eq`).  Consequently `cechTerm p` is a cone over the `(p+1)`-fold fibre product
`C ×_[0,1] ⋯ ×_[0,1] C`, i.e. it maps to the `p`-th term of the Čech nerve of `beta`.

The proof uses the Yoneda lemma for the (subcanonical) coherent topology on `LightProfinite`:
morphisms out of the sheaf-yoneda `toCondensed (cechTerm p)` are detected by their value on the
identity, and the value of `toCondensed.map u ≫ beta` on the identity is `binExp ∘ u`.
-/

open CategoryTheory Limits LightProfinite LightCondensed

namespace Work.ANALYTIC.CechPt

theorem cechProj_beta_eq (p : ℕ) (j : Fin (p + 1)) :
    CategoryTheory.CategoryStruct.comp
        (lightProfiniteToLightCondSet.map (Work.ANALYTIC.CechPt.cechProj p j))
        Work.ANALYTIC.CechPt.beta =
      CategoryTheory.CategoryStruct.comp
        (lightProfiniteToLightCondSet.map (Work.ANALYTIC.CechPt.cechProj p 0))
        Work.ANALYTIC.CechPt.beta := by
  -- We work with `beta` retyped along the definitional equality `lightProfiniteToLightCondSet =
  -- (coherentTopology LightProfinite).yoneda`, so that the Yoneda lemmas apply syntactically.
  let b : lightProfiniteToLightCondSet.obj cantor ⟶ intervalCond := beta
  change lightProfiniteToLightCondSet.map (cechProj p j) ≫ b =
    lightProfiniteToLightCondSet.map (cechProj p 0) ≫ b
  -- Yoneda: it suffices to compare the values on the identity of `cechTerm p`.
  apply (GrothendieckTopology.yonedaEquiv (coherentTopology LightProfinite.{0})).injective
  erw [GrothendieckTopology.yonedaEquiv_comp (J := coherentTopology LightProfinite.{0})
        (lightProfiniteToLightCondSet.map (cechProj p j)) b,
      GrothendieckTopology.yonedaEquiv_comp (J := coherentTopology LightProfinite.{0})
        (lightProfiniteToLightCondSet.map (cechProj p 0)) b,
      GrothendieckTopology.yonedaEquiv_yoneda_map,
      GrothendieckTopology.yonedaEquiv_yoneda_map]
  -- The two values are the continuous maps `binExp ∘ cechProj p j` and `binExp ∘ cechProj p 0`.
  change binExpHom.hom.comp (cechProj p j).hom.hom =
    binExpHom.hom.comp (cechProj p 0).hom.hom
  apply ContinuousMap.ext
  intro s
  simp only [ContinuousMap.comp_apply]
  -- All coordinates of `s` have the same binary expansion.
  exact cechTerm_apply_eq p s j 0

end Work.ANALYTIC.CechPt
