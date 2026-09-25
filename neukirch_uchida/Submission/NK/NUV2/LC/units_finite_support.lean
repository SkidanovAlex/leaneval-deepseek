import Mathlib
import Submission.NK.HassePrinciple.locUnits_compatible
import Submission.NK.HassePrinciple.exists_level_of_h2
import Submission.NK.HassePrinciple.HBNIdeleProof
import Submission.NK.CFTLib.tateCohomology_neg_one_idele_of_isUnramified
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
import Submission.NK.NUV2.LC.localUnitsSubRep_subsingleton_unramified

/-!
# Finite support of the localisation `H²(Gal(L/K), Lˣ) → ∏_w H²(Γ_w, L_wˣ)` — WORK IN PROGRESS

This module is **not** part of the deliverable: it records the two auxiliary statements into which
[UFS] of `NOTES_finite_support_loc_twist.md` splits, with the main theorem reduced to them.
It is **sorry-free**: the local input `NK.NUV2.LC.localUnitsSubRep_subsingleton_unramified`
(the `CoeffInt` unramified local vanishing) is proved in
`Submission/Work/NUV2/LC/localUnitsSubRep_subsingleton_unramified.lean` and imported here.

* `exists_level_of_h2` puts the image of `a` in `H²(Γ, 𝕀_L)` at a finite Galois-stable level `S₀`;
* `ideleLoc_level_comp_U` + `locUnits_compatible` say that for `w ∉ S₀` the `w`-component of
  `locUnits a` lies in the image of `localUnitsIncl : H²(Γ_w, 𝒪_wˣ) ⟶ H²(Γ_w, L_wˣ)`;
* at an unramified finite place `H²(Γ_w, 𝒪_wˣ) = 0` (Commons, transported along
  `GlobalCFTdeep.Herbrand.localUnitsUnitsEquiv` and `decompositionSubgroupIsoLocalGalois`).
-/

open scoped NumberField
open IsDedekindDomain

namespace NK.NUV2.LC

open NK.HassePrinciple

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **For `w ∉ S₀` the localisation lies in the image of `H²(Γ_w, 𝒪_wˣ)`.**

`locUnits_eq_unitsToIdeleH2_comp` identifies `locUnits a w` with `ideleLoc (unitsToIdeleH2 a) w`,
`haS` replaces `unitsToIdeleH2 a` by the image of the level class `aS`, and
`ideleLoc_level_comp_U S w hw` factors the composite through `localUnitsIncl`. -/
theorem locUnits_mem_range_of_level
    {S : NK.HassePrinciple.GStableSet K L} (a : groupCohomology (unitsRep K L) 2)
    (aS : groupCohomology (levelRep K L S) 2)
    (haS : (groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) (levelIncl K L S) 2).hom aS =
      (unitsToIdeleH2 K L).hom a)
    {w : NK.GlobalCFT.Place L} (hw : w ∉ S.carrier) :
    ∃ y : groupCohomology (localUnitsSubRep (K := K) (L := L) w) 2,
      (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
        (localUnitsIncl (K := K) (L := L) w) 2).hom y = (locUnits K L w).hom a := by
  refine ⟨(groupCohomology.coindIso (k := CoeffInt.{0})
      (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep (K := K) (L := L) w) 2).hom
    ((h2map (orbitCoindMapU (K := K) (L := L) w)).hom
      ((h2map (projOrbitUnitsHom (K := K) (L := L) S (orbitStable K L w))).hom
        ((h2map (levelToOutsideHom (K := K) (L := L) S)).hom aS))), ?_⟩
  have hcomp := congrArg
    (fun (f : groupCohomology (levelRep K L S) 2 ⟶ groupCohomology (localUnitsRep K L w) 2) =>
      f.hom aS) (NK.HassePrinciple.ideleLoc_level_comp_U (K := K) (L := L) S w hw)
  simp only [CategoryTheory.comp_apply] at hcomp
  have hloc : (locUnits K L w).hom a = (ideleLoc K L w).hom ((unitsToIdeleH2 K L).hom a) := by
    have h := congrArg
      (fun (f : groupCohomology (unitsRep K L) 2 ⟶ groupCohomology (localUnitsRep K L w) 2) =>
        f.hom a) (NK.HassePrinciple.locUnits_eq_unitsToIdeleH2_comp (K := K) (L := L) w)
    simpa only [CategoryTheory.comp_apply] using h
  rw [hloc, ← haS]
  exact hcomp.symm

/-- The finite set of places that are either archimedean or finitely ramified. -/
noncomputable def badPlaces : Set (NK.GlobalCFT.Place L) :=
  (fun q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) =>
      NK.GlobalCFT.Place.ofFinite q) ''
      {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) |
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1} ∪
    (fun v : NumberField.InfinitePlace L => NK.GlobalCFT.Place.ofInfinite v) '' Set.univ

theorem badPlaces_finite : (badPlaces (K := K) (L := L)).Finite := by
  refine Set.Finite.union (Set.Finite.image _ ?_) (Set.Finite.image _ Set.finite_univ)
  exact Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one

theorem mem_badPlaces_iff {w : NK.GlobalCFT.Place L} :
    w ∈ badPlaces (K := K) (L := L) ↔
      (∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
          w = NK.GlobalCFT.Place.ofFinite q ∧
            q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1) ∨
        (∃ v : NumberField.InfinitePlace L, w = NK.GlobalCFT.Place.ofInfinite v) := by
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨q, hq, rfl⟩ := h
      exact Or.inl ⟨q, rfl, hq⟩
    · obtain ⟨v, -, rfl⟩ := h
      exact Or.inr ⟨v, rfl⟩
  · rintro (⟨q, rfl, hq⟩ | ⟨v, rfl⟩)
    · exact Or.inl ⟨q, hq, rfl⟩
    · exact Or.inr ⟨v, Set.mem_univ v, rfl⟩

/-- **Finite support of the units localisation** (the [UFS] milestone of
`NUV2/LC/NOTES_finite_support_loc_twist.md`): for a class of `H²(Gal(L/K), Lˣ) = Br(L/K)`, the
localisation into the local fields vanishes at all but finitely many places.

* `ā := unitsToIdeleH2 a`; `exists_level_of_h2 ā` gives a finite Galois-stable `S₀` and
  `aS : H²(Γ, levelRep S₀)` with `levelIncl aS = ā`;
* `locUnits_eq_unitsToIdeleH2_comp` gives `locUnits a w = ideleLoc ā w`;
* `ideleLoc_level_comp_U` (with `w ∉ S₀`) factors that through `localUnitsIncl`, giving
  `locUnits_mem_range_of_level`;
* outside `S₀ ∪ badPlaces`, a place is `ofFinite q` with `e(q|Q) = 1`, so the source of
  `localUnitsIncl` is a subsingleton
  (`localUnitsSubRep_subsingleton_of_ramificationIdx_eq_one`). -/
theorem units_finite_support (a : groupCohomology (unitsRep K L) 2) :
    {w : NK.GlobalCFT.Place L | (locUnits K L w).hom a ≠ 0}.Finite := by
  classical
  set ā : groupCohomology (ideleRep K L) 2 := (unitsToIdeleH2 K L).hom a with hā
  obtain ⟨S₀, hS₀fin, aS, haS⟩ := NK.HassePrinciple.exists_level_of_h2 ā
  refine Set.Finite.subset (hS₀fin.union (badPlaces_finite (K := K) (L := L))) ?_
  intro w hw
  by_contra hwS
  rw [Set.mem_union, not_or] at hwS
  obtain ⟨hwS₀, hwbad⟩ := hwS
  rw [mem_badPlaces_iff] at hwbad
  push Not at hwbad
  cases w with
  | inl v => exact hwbad.2 v rfl
  | inr q =>
    have he : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := hwbad.1 q rfl
    have hwq : NK.GlobalCFT.Place.ofFinite q ∉ S₀.carrier := hwS₀
    obtain ⟨y, hy⟩ := locUnits_mem_range_of_level (S := S₀) (w := NK.GlobalCFT.Place.ofFinite q)
      a aS haS hwq
    haveI : Subsingleton (groupCohomology
        (localUnitsSubRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q)) 2) :=
      localUnitsSubRep_subsingleton_unramified (K := K) (L := L) q he
    exact hw (by rw [← hy, Subsingleton.elim y 0, map_zero])

end NK.NUV2.LC
