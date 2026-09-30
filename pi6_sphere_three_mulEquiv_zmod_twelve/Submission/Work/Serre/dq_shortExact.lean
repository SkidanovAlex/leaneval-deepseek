import Mathlib
import Submission.Work.Serre.RatMVDefs
import Submission.Work.Cohomology.dualComplex_acyclic_of_acyclic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `dqMap` carries short exact sequences to short exact sequences

`Work.Serre.dqMap φ` is the transpose of the base change to `ℚ` of a morphism of `ℤ`-chain
complexes: `dqMap φ : DQ D ⟶ DQ C` for `φ : C ⟶ D`, where
`DQ C = dualComplex ℚ (IntRatCM.obj C)`.

Both operations involved are exact: the base change `IntRatF = ModuleCat.extendScalars (ℤ → ℚ)` is
flat (so `IntRatCM` preserves finite limits and colimits), and over a field the dual
`Hom_ℚ(-, ℚ)` of a short exact sequence of vector spaces is short exact, because every linear
functional on a subspace extends to the whole space.  Consequently, for a short exact sequence of
`ℤ`-chain complexes `0 → A --f--> B --g--> C → 0` the transposed sequence
`0 → DQ C --dqMap g--> DQ B --dqMap f--> DQ A → 0` is again short exact.

The proof is degreewise: a short complex of (co)chain complexes over an abelian category is short
exact iff it is so in every degree (`HomologicalComplex.shortExact_iff_degreewise_shortExact`), and
in each degree the statement reduces to the exactness of the transpose over the field `ℚ`
(`Work.Cohomology.range_dualMap_of_range_eq_ker`, `LinearMap.dualMap_injective_of_surjective`,
`LinearMap.dualMap_surjective_of_injective`).
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The `n`-th component of `dqMap φ` is the transpose of the `n`-th component of `IntRatCM.map φ`. -/
private theorem dqMap_f_hom {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) (n : ℕ) :
    ModuleCat.Hom.hom ((dqMap φ).f n)
      = (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.map φ).f n)).dualMap := rfl

set_option linter.style.haveILetI false in
set_option maxHeartbeats 2000000 in
theorem dq_shortExact {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat Int) Nat)} (hS : S.ShortExact) (hfg : CategoryTheory.CategoryStruct.comp (Work.Serre.dqMap S.g) (Work.Serre.dqMap S.f) = 0) : (CategoryTheory.ShortComplex.mk (Work.Serre.dqMap S.g) (Work.Serre.dqMap S.f) hfg).ShortExact := by
  -- exactness of the functors involved
  haveI : PreservesFiniteLimits Work.StemsB.IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits Work.StemsB.IntRatF := inferInstance
  haveI : PreservesFiniteLimits Work.StemsB.IntRatCM := inferInstance
  haveI : PreservesFiniteColimits Work.StemsB.IntRatCM := inferInstance
  -- base change of the short exact sequence
  have hSCM : (S.map Work.StemsB.IntRatCM).ShortExact := hS.map_of_exact Work.StemsB.IntRatCM
  -- it suffices to check short exactness in every degree
  refine (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (ShortComplex.mk (Work.Serre.dqMap S.g) (Work.Serre.dqMap S.f) hfg)).mpr (fun i => ?_)
  have hdeg : ((S.map Work.StemsB.IntRatCM).map
      (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) i)).ShortExact :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact (S.map Work.StemsB.IntRatCM)).mp
      hSCM) i
  -- the three degreewise inputs, read off from `hdeg`
  have hinjF : Function.Injective
      (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.map S.f).f i)) := by
    have h := hdeg.moduleCat_injective_f
    simp only [ShortComplex.map_f] at h
    exact h
  have hsurjG : Function.Surjective
      (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.map S.g).f i)) := by
    have h := hdeg.moduleCat_surjective_g
    simp only [ShortComplex.map_g] at h
    exact h
  have hExactQ : LinearMap.range (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.map S.f).f i))
      = LinearMap.ker (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.map S.g).f i)) := by
    have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hdeg.exact
    simp only [ShortComplex.map_f, ShortComplex.map_g] at h
    exact h
  -- in every degree the degreewise short complex is the transpose of a short exact one
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr ?_
    show LinearMap.range (ModuleCat.Hom.hom ((Work.Serre.dqMap S.g).f i))
      = LinearMap.ker (ModuleCat.Hom.hom ((Work.Serre.dqMap S.f).f i))
    rw [dqMap_f_hom, dqMap_f_hom]
    exact Work.Cohomology.range_dualMap_of_range_eq_ker ℚ hExactQ
  · show Mono ((Work.Serre.dqMap S.g).f i)
    refine (ModuleCat.mono_iff_injective _).mpr ?_
    change Function.Injective ((ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.map S.g).f i)).dualMap)
    exact LinearMap.dualMap_injective_of_surjective hsurjG
  · show Epi ((Work.Serre.dqMap S.f).f i)
    refine (ModuleCat.epi_iff_surjective _).mpr ?_
    change Function.Surjective ((ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.map S.f).f i)).dualMap)
    exact LinearMap.dualMap_surjective_of_injective hinjF

end

end Work.Serre
