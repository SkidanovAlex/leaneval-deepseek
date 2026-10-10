import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.CFTLib.HR.isCyclotomic_onePlace_real
import Submission.NK.HR2.transferStepOnePlace
import Submission.Work.SSGRoute.eb_arch_crux
import Submission.Work.SSGRoute.eb_locUnits_resToGal
import Submission.Work.SSGRoute.phi1_level_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `hβ` step of the archimedean case of `brauer_single_place` (E8', piece P4)

Local triviality of `res_{E/M}(inf_E a)` at every place of `E`, where `a ∈ H²(Gal(L/k), Lˣ)` is
locally trivial outside the `Gal(L/k)`-orbit of an infinite place `w₀` and `M` is totally complex.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.SSGRoute

/-- **Local triviality of the restriction of the inflation, at every place of `E`** (the `hβ` step
of the archimedean case of `brauer_single_place`, E8' piece P4).

In a tower of number fields `k ⊆ L ⊆ E` with `k ⊆ M ⊆ E`, if `M` is totally complex and the class
`a ∈ H²(Gal(L/k), Lˣ)` is locally trivial at every place of `L` outside the `Gal(L/k)`-orbit of the
infinite place `w₀`, then the restriction to `Gal(E/M)` of the inflation of `a` to `E` is locally
trivial at *every* place of `E`.

* at an infinite place of `E`, `Work.SSGRoute.eb_arch_crux` kills every class (the place of `M`
  below is complex, since `M` is totally complex);
* at a finite place, the place of `L` below it is finite, hence outside the orbit of `w₀`, and
  `NK.HR2.locUnits_inflation_eq_zero_of_loc_eq_zero` together with the restriction–locality square
  `Work.SSGRoute.eb_locUnits_resToGal` concludes. -/
theorem eb_arch_beta_local {k L M E : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Field M] [NumberField M] [Field E] [NumberField E] [Algebra k L] [Algebra k M] [Algebra k E]
    [Algebra L E] [Algebra M E] [IsScalarTower k L E] [IsScalarTower k M E]
    [FiniteDimensional k L] [FiniteDimensional k M] [FiniteDimensional k E]
    [IsGalois k L] [IsGalois k M] [IsGalois k E] [FiniteDimensional M E] [IsGalois M E]
    (w₀ : NumberField.InfinitePlace L) (a : groupCohomology (NK.HassePrinciple.unitsRep k L) 2)
    (h : ∀ w : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • NK.GlobalCFT.Place.ofInfinite w₀ ≠ w) →
        (NK.HassePrinciple.locUnits k L w).hom a = 0)
    (hM : ∀ W : NumberField.InfinitePlace M, W.IsComplex) (ŵ : NK.GlobalCFT.Place E) :
    (NK.HassePrinciple.locUnits M E ŵ).hom
      ((NK.NUV2.ChebAux.Transfer.resToGal k M E).hom
        ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a)) = 0 := by
  rcases ŵ with ŵ' | q
  · -- archimedean place: the crux kills every class
    exact eb_arch_crux (k := k) (M := M) (E := E) ŵ'
      (hM (ŵ'.comap (algebraMap M E)))
      ((NK.NUV2.ChebAux.Transfer.resToGal k M E).hom
        ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a))
  · -- finite place
    -- the place of `L` below
    let qL : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) :=
      ⟨q.asIdeal.under (NumberField.RingOfIntegers L), inferInstance,
        Ideal.under_ne_bot _ q.ne_bot⟩
    let s : NK.GlobalCFT.Place L := NK.GlobalCFT.Place.ofFinite qL
    have hs : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) s :=
      NK.GlobalCFT.Place.liesOver_ofFinite (Ideal.over_under q.asIdeal)
    -- `s` is finite, hence outside the orbit of `w₀`
    have hnot : ∀ σ : L ≃ₐ[k] L, σ • NK.GlobalCFT.Place.ofInfinite w₀ ≠ s := by
      rw [Work.SSGRoute.not_liesOver_iff_not_mem_orbit k L
        (NK.GlobalCFT.Place.ofInfinite w₀)
        (NK.GlobalCFT.Place.ofInfinite (w₀.comap (algebraMap k L)))
        (NK.GlobalCFT.Place.liesOver_ofInfinite
          (NK.GlobalCFT.Norm.liesOver_comap_self w₀))]
      intro hlies
      exact NK.GlobalCFT.Place.not_isFinite_ofInfinite (w₀.comap (algebraMap k L))
        ((NK.GlobalCFT.Place.isFinite_of_liesOver hlies).mp
          (NK.GlobalCFT.Place.isFinite_ofFinite qL))
    have hsa : (NK.HassePrinciple.locUnits k L s).hom a = 0 := h s hnot
    have hE : (NK.HassePrinciple.locUnits k E (NK.GlobalCFT.Place.ofFinite q)).hom
        ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a) = 0 :=
      NK.HR2.locUnits_inflation_eq_zero_of_loc_eq_zero (K := k) (L := L) (E := E) a s
        (NK.GlobalCFT.Place.ofFinite q) hs hsa
    rw [Work.SSGRoute.eb_locUnits_resToGal (k := k) (M := M) (E := E)
      (NK.GlobalCFT.Place.ofFinite q)
      ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a)]
    rw [hE]
    first
      | exact map_zero _
      | simpa using map_zero _
      | exact LinearMap.map_zero _
      | simp
      | rw [map_zero]

end Work.SSGRoute
