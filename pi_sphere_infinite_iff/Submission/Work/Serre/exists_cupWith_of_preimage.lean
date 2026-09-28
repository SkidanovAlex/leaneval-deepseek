import Mathlib
-- (The declarations this file needs (`Work.Serre.EulerFibreRange`,
-- `Work.Serre.thomIsoCylFibreRange_of_eulerFibreRange`, `isZero_coh_of_ratAcyclic`, …) were moved
-- to the upstream module `Submission.Work.Serre.EulerFibreRoot`; importing *that* instead of
-- `Submission.Work.Serre.thomIsoCylFibreRange` removes the import edge that made the target of
-- `thomIsoCylFibreRange.lean` unprovable (build cycle).  See
-- `Submission/Work/Serre/TICFR_SESSION_NOTES.md`, FINDING 1.)
import Submission.Work.Serre.EulerFibreRoot
import Submission.Work.Serre.Engine
import Submission.Work.Cohomology.cupNaturalH

namespace Work.Serre

/-- **Naturality of the cup product with a class, in the form used for base change.**

For a continuous map `g : Γ → B`, a degree-`(r+1)` class `e` on `B` whose pullback is `eΓ`
(`hPe`), and a degree-`m` class `x` on `B`, the pullback of `x ⌣ e` is `g^*x ⌣ eΓ`:

  `g^*(x ⌣ e) = g^*(x) ⌣ eΓ`.

This is `Work.Cohomology.cupNaturalH` (naturality of the Alexander–Whitney product, which is the
product used by `Work.Serre.ratCup`/`Work.Serre.cupWith` definitionally) together with the
hypothesis `hPe` identifying the pullback of `e`. -/
theorem cupWith_CohMap_apply {B Γ : Type} [TopologicalSpace B] [TopologicalSpace Γ]
    (g : C(Γ, B)) (r m : ℕ)
    (e : ratCoh (TopCat.of B) (r + 1)) (eΓ : ratCoh (TopCat.of Γ) (r + 1))
    (hPe : (ModuleCat.Hom.hom (Work.Thom.CohMap g ℚ (r + 1))) e = eΓ)
    (x : ratCoh (TopCat.of B) m) :
    (ModuleCat.Hom.hom (Work.Thom.CohMap g ℚ (m + (r + 1))))
        (cupWith (TopCat.of B) (r + 1) e m x) =
      cupWith (TopCat.of Γ) (r + 1) eΓ m
        ((ModuleCat.Hom.hom (Work.Thom.CohMap g ℚ m)) x) := by
  exact (Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom g) m (r + 1) x e).trans
    (congrArg (fun z => (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Γ)) m (r + 1))
      ((ModuleCat.Hom.hom (Work.Thom.CohMap g ℚ m)) x) z) hPe)

/-- **Base change of `cupWith` along a cohomology isomorphism.**

If `g^* : H^{m+r+1}(B;ℚ) → H^{m+r+1}(Γ;ℚ)` is injective (here: an isomorphism, `hIso`), then the
cup product with `e` on `B` is the transfer of the cup product with `eΓ = g^*e` on `Γ`:

  `(⌣ e) = (g^*)^{-1} ∘ (⌣ eΓ) ∘ g^*`

as linear maps `H^m(B;ℚ) → H^{m+r+1}(B;ℚ)`.  The proof is `cupWith_CohMap_apply` (which computes
`g^* ∘ (⌣ e)`) together with `g^* ∘ (g^*)^{-1} = id`. -/
theorem cupWith_eq_inv_comp_CohMap {B Γ : Type} [TopologicalSpace B] [TopologicalSpace Γ]
    (g : C(Γ, B)) (r m : ℕ)
    (e : ratCoh (TopCat.of B) (r + 1)) (eΓ : ratCoh (TopCat.of Γ) (r + 1))
    (hPe : (ModuleCat.Hom.hom (Work.Thom.CohMap g ℚ (r + 1))) e = eΓ)
    (hIso : CategoryTheory.IsIso (Work.Thom.CohMap g ℚ (m + (r + 1)))) :
    cupWith (TopCat.of B) (r + 1) e m =
      (ModuleCat.Hom.hom
          (CategoryTheory.asIso (Work.Thom.CohMap g ℚ (m + (r + 1)))).inv).comp
        ((cupWith (TopCat.of Γ) (r + 1) eΓ m).comp
          (ModuleCat.Hom.hom (Work.Thom.CohMap g ℚ m))) := by
  have hinj : Function.Injective
      ⇑(ModuleCat.Hom.hom (Work.Thom.CohMap g ℚ (m + (r + 1)))) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (Work.Thom.CohMap g ℚ (m + (r + 1)))).mp hIso |>.1
  apply LinearMap.ext
  intro x
  exact hinj ((cupWith_CohMap_apply g r m e eΓ hPe x).trans
    (CategoryTheory.Iso.inv_hom_id_apply
      (CategoryTheory.asIso (Work.Thom.CohMap g ℚ (m + (r + 1))))
      (cupWith (TopCat.of Γ) (r + 1) eΓ m
        ((ModuleCat.Hom.hom (Work.Thom.CohMap g ℚ m)) x))).symm)

/-- Base change of an Euler class along a map that is a rational cohomology isomorphism in the
range: from an Euler class on `Γ` whose cup product is an isomorphism for `m + r + 1 ≤ N + 1`, and
the isomorphism of `g^* : H^k(B;ℚ) → H^k(Γ;ℚ)` for `k ≤ N+1`, produce an Euler class on `B` with
the same property. -/
theorem exists_cupWith_of_preimage {B Γ : Type} [TopologicalSpace B] [TopologicalSpace Γ]
    (g : C(Γ, B)) (r N : ℕ) (hr : 1 ≤ r)
    (hiso : ∀ k : ℕ, k ≤ N + 1 → CategoryTheory.IsIso (Work.Thom.CohMap g ℚ k))
    (eΓ : Work.Thom.Coh ℚ (r + 1) Γ)
    (hΓ : ∀ m : ℕ, m + r + 1 ≤ N + 1 →
      CategoryTheory.IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of Γ) (r + 1) eΓ m))) :
    ∃ e : Work.Thom.Coh ℚ (r + 1) B, ∀ m : ℕ, m + r + 1 ≤ N + 1 →
      CategoryTheory.IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of B) (r + 1) e m)) := by
  by_cases hrN : r + 1 ≤ N + 1
  · -- the non-vacuous case: `g^*` is an isomorphism in the degree `r + 1` of the class, and the
    -- class `e := (g^*)^{-1} eΓ` has the required property because `⌣ e` is the conjugate of
    -- `⌣ eΓ` by the two cohomology isomorphisms `g^*`.
    have hPiso : CategoryTheory.IsIso (Work.Thom.CohMap g ℚ (r + 1)) := hiso (r + 1) hrN
    let e : ratCoh (TopCat.of B) (r + 1) :=
      (CategoryTheory.asIso (Work.Thom.CohMap g ℚ (r + 1))).inv eΓ
    have hPe : (ModuleCat.Hom.hom (Work.Thom.CohMap g ℚ (r + 1))) e = eΓ :=
      CategoryTheory.Iso.inv_hom_id_apply
        (CategoryTheory.asIso (Work.Thom.CohMap g ℚ (r + 1))) eΓ
    refine ⟨e, fun m hm => ?_⟩
    have hIm : CategoryTheory.IsIso (Work.Thom.CohMap g ℚ m) := hiso m (by omega)
    have hImr : CategoryTheory.IsIso (Work.Thom.CohMap g ℚ (m + (r + 1))) :=
      hiso (m + (r + 1)) (by omega)
    -- the three factors of the base-change identity are bijective
    have hA : Function.Bijective ⇑(ModuleCat.Hom.hom
        (CategoryTheory.asIso (Work.Thom.CohMap g ℚ (m + (r + 1)))).inv) :=
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective
        (CategoryTheory.asIso (Work.Thom.CohMap g ℚ (m + (r + 1)))).inv).mp
        (CategoryTheory.Iso.isIso_inv _)
    have hB : Function.Bijective (cupWith (TopCat.of Γ) (r + 1) eΓ m) :=
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective
        (ModuleCat.ofHom (cupWith (TopCat.of Γ) (r + 1) eΓ m))).mp (hΓ m hm)
    have hC : Function.Bijective ⇑(ModuleCat.Hom.hom (Work.Thom.CohMap g ℚ m)) :=
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective
        (Work.Thom.CohMap g ℚ m)).mp (hIm)
    -- hence so is `⌣ e = (g^*)^{-1} ∘ (⌣ eΓ) ∘ g^*`
    have hbij : Function.Bijective (cupWith (TopCat.of B) (r + 1) e m) :=
      (cupWith_eq_inv_comp_CohMap g r m e eΓ hPe hImr).symm ▸ ((hA.comp hB).comp hC)
    exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) e m))).mpr hbij
  · -- if `r + 1 > N + 1` the required property is vacuous, and any class (e.g. `0`) works.
    refine ⟨0, fun m hm => ?_⟩
    omega

end Work.Serre
