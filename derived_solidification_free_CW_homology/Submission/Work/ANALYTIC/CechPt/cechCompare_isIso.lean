import Mathlib
import Submission.Work.ANALYTIC.CechPt.LevelModelDefs
import Submission.Work.ANALYTIC.CechPt.exists_cechTerm_lift
import Submission.Work.ANALYTIC.CechPt.toCondensedMap_beta_eq_iff
import Submission.Work.ANALYTIC.CechPt.eq_of_cechProj_eq
import Submission.Work.ANALYTIC.CechPt.isIso_of_yoneda_bijective

/-!
# The comparison map `ℤ[C_p] ⟶ C^•_[0,1](p)` is an isomorphism

`cechTerm p` is the light profinite set of `(p+1)`-tuples of points of the Cantor set with a
common binary expansion, i.e. the `p`-th term of the Čech nerve of the binary expansion
`beta : C ⟶ [0,1]` presented as an honest profinite set.  The comparison map
`cechCompare p : toCondensed (cechTerm p) ⟶ (cechNerve beta).obj (op ⦋p⦌)` is the map induced by
the coordinate projections; here we prove that it is an isomorphism.

The proof tests `cechCompare p` against all light profinite test objects `S`
(`isIso_of_yoneda_bijective`):

* injectivity: the coordinate projections out of `cechTerm p` are jointly injective
  (`eq_of_cechProj_eq`), and they are recovered from `cechCompare p` by
  `cechCompare_π`;
* surjectivity: a map `c : toCondensed S ⟶ (cechNerve beta).obj (op ⦋p⦌)` is a cone of maps
  `u j : S ⟶ C` with a common binary expansion (the base compatibility, transported along
  `WidePullback.π_arrow` and read off with `toCondensedMap_beta_eq_iff`), so the universal
  property `exists_cechTerm_lift` produces a lift through `cechCompare p`, checked on the
  projections with `WidePullback.hom_ext`.

Some of the terms below are only type-correct up to unfolding the definition of the Čech nerve
(`Arrow.cechNerve`), which `rw` does not perform; hence the `erw` steps.
-/

open CategoryTheory Limits LightProfinite LightCondensed

namespace Work.ANALYTIC.CechPt

theorem cechCompare_isIso (p : ℕ) :
    CategoryTheory.IsIso (Work.ANALYTIC.CechPt.cechCompare p) := by
  apply isIso_of_yoneda_bijective
  intro S
  constructor
  · -- injectivity: `cechCompare p` remembers all the coordinate projections
    intro a b hab
    have h : lightProfiniteToLightCondSetFullyFaithful.preimage a =
        lightProfiniteToLightCondSetFullyFaithful.preimage b := by
      apply eq_of_cechProj_eq p
      intro j
      apply lightProfiniteToLightCondSetFullyFaithful.map_injective
      have h1 : a ≫ lightProfiniteToLightCondSet.map (cechProj p j) =
          b ≫ lightProfiniteToLightCondSet.map (cechProj p j) := by
        have h2 := congrArg
          (fun t => t ≫ WidePullback.π (fun _ : Fin (p + 1) => beta) j) hab
        erw [Category.assoc, Category.assoc, cechCompare_π] at h2
        exact h2
      rw [Functor.map_comp, Functor.map_comp,
        Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage]
      exact h1
    calc a = lightProfiniteToLightCondSet.map
          (lightProfiniteToLightCondSetFullyFaithful.preimage a) :=
          (Functor.FullyFaithful.map_preimage _ a).symm
      _ = lightProfiniteToLightCondSet.map
          (lightProfiniteToLightCondSetFullyFaithful.preimage b) := by rw [h]
      _ = b := Functor.FullyFaithful.map_preimage _ b
  · -- surjectivity: a cone out of `S` descends to `cechTerm p` by its universal property
    intro c
    let u : Fin (p + 1) → (S ⟶ cantor) := fun j =>
      lightProfiniteToLightCondSetFullyFaithful.preimage
        (c ≫ WidePullback.π (fun _ : Fin (p + 1) => beta) j)
    have hu : ∀ j, lightProfiniteToLightCondSet.map (u j) =
        c ≫ WidePullback.π (fun _ : Fin (p + 1) => beta) j := fun j =>
      Functor.FullyFaithful.map_preimage _ _
    -- all the `u j` have the same binary expansion, by the base compatibility of `c`
    obtain ⟨u', hu'⟩ := exists_cechTerm_lift p S u (fun s i j =>
      (toCondensedMap_beta_eq_iff (u i) (u j)).mp (by
        show lightProfiniteToLightCondSet.map (u i) ≫ beta =
          lightProfiniteToLightCondSet.map (u j) ≫ beta
        rw [hu i, hu j]
        erw [Category.assoc, Category.assoc, WidePullback.π_arrow, WidePullback.π_arrow]) s)
    refine ⟨lightProfiniteToLightCondSet.map u', ?_⟩
    refine WidePullback.hom_ext (fun _ : Fin (p + 1) => beta) _ _ ?_ ?_
    · -- on the projections
      intro j
      erw [Category.assoc, cechCompare_π, ← Functor.map_comp, hu' j, hu j]
      rfl
    · -- on the base
      erw [Category.assoc, cechCompare_base, ← Category.assoc, ← Functor.map_comp, hu' 0, hu 0,
        Category.assoc, WidePullback.π_arrow]
      rfl

end Work.ANALYTIC.CechPt
