import Mathlib
import Submission.Work.Thom.localThom_union
import Submission.Work.Thom.Coh_zero_cover_injective_gen
import Submission.Work.Thom.localThomMap_pdCohMap

namespace Work.Thom

open Work.TangentClasses CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## Auxiliary lemmas -/

/-- Transporting a homology class along an equality of degrees commutes with `homologyMap`. -/
theorem homologyMap_cast {R : Type} [CommRing R] {K L : CochainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) {a b : ℕ} (h : a = b) (x : K.homology a) :
    (HomologicalComplex.homologyMap φ b).hom (h ▸ x)
      = h ▸ ((HomologicalComplex.homologyMap φ a).hom x) := by
  cases h
  rfl

/-- The degree cast `n → 0 + n` commutes with the restriction map `pdCohMap`. -/
theorem pdCohMap_cast (X : TopCat) (A U W : Set X) (hWU : W ⊆ U) (n : ℕ)
    (x : Work.Cohomology.pdCohSub X A U n) :
    (Work.Cohomology.pdCohMap X A U W hWU (0 + n)).hom ((Nat.zero_add n).symm ▸ x)
      = (Nat.zero_add n).symm ▸ ((Work.Cohomology.pdCohMap X A U W hWU n).hom x) := by
  unfold Work.Cohomology.pdCohMap
  exact homologyMap_cast _ (Nat.zero_add n).symm x

/-- The unit class `1 ∈ H⁰` acts trivially: `localThomMap` on it is the class itself (up to the
degree cast `0 + n = n`). -/
theorem localThomMap_oneH_zero (Z : RealBundle B F ι) (n : ℕ) (W : Set B)
    (τ : PieceCoh Z W n) :
    localThomMap Z n W τ 0 (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥W)))
      = (Nat.zero_add n).symm ▸ τ := by
  rw [localThomMap_apply, CohMap_oneH, mixedCupC_oneH_zero]

/-- **The core computation**: if `u` is a preimage of the transported class
`(Nat.zero_add n).symm ▸ τ'` under the local Thom map of `τ` over `P`, and `τ'` and `τ` agree after
restriction to `V`, then the restriction of `u` to `V` is the unit class. -/
theorem pdIncl_choice_eq_oneH (Z : RealBundle B F ι) (n : ℕ) {P V : Set B} (hVP : V ⊆ P)
    (τ τ' : PieceCoh Z P n)
    (hτk : Function.Injective (localThomMap Z n V
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' P) (Z.proj ⁻¹' V) (Set.preimage_mono hVP) n).hom τ) 0))
    (hag : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' P) (Z.proj ⁻¹' V) (Set.preimage_mono hVP) n).hom τ'
        = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' P) (Z.proj ⁻¹' V) (Set.preimage_mono hVP) n).hom τ)
    (u : Work.Thom.Coh ℤ 0 ↥P)
    (hu : Work.Thom.localThomMap Z n P τ 0 u = (Nat.zero_add n).symm ▸ τ') :
    (Work.Thom.CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B) P V hVP)) ℤ 0).hom u
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥V)) := by
  classical
  have h3 := congrArg ModuleCat.Hom.hom
    (Work.Thom.localThomMap_pdCohMap Z n hVP τ 0)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom] at h3
  have h4 := LinearMap.congr_fun h3 u
  simp only [LinearMap.comp_apply] at h4
  have hR : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' P) (Z.proj ⁻¹' V) (Set.preimage_mono hVP) (0 + n)).hom
        ((Nat.zero_add n).symm ▸ τ')
      = (Nat.zero_add n).symm ▸ ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
          (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' P) (Z.proj ⁻¹' V)
          (Set.preimage_mono hVP) n).hom τ) := by
    rw [Work.Thom.pdCohMap_cast]
    exact congrArg (fun w : PieceCoh Z V n => (Nat.zero_add n).symm ▸ w) hag
  rw [hu, hR] at h4
  refine hτk ?_
  rw [Work.Thom.localThomMap_oneH_zero]
  exact h4

/-! ## The main lemma -/

/-- **Two local Thom classes over a piece which agree on an open cover are equal.**

PROOF ROUTE.  Use
`Work.Thom.localThomMap_pdCohMap` (from `Submission/Work/Thom/localThomMap_pdCohMap.lean`): for
`W ⊆ U` and any `ρ : PieceCoh Z U m`,
`CohMap (pdIncl U W ·) ℤ k ≫ localThomMap over W of ((pdCohMap …).hom ρ) = localThomMap over U of ρ ≫ pdCohMap … (k+n)`.
Use `Work.Thom.Coh_zero_cover_injective_gen` (from
`Submission/Work/Thom/Coh_zero_cover_injective_gen.lean`) for the degree-`0` step.
Write `φ := localThomMap Z n P τ 0 : Coh ℤ 0 ↥P → PieceCoh Z P (0+n)` (bijective by `hτ`),
`τ'' := (Nat.zero_add n).symm ▸ τ'` and `u := φ⁻¹(τ'')` (e.g. `Classical.choose (hτ.2 τ'')`), so
`φ u = τ''`.
1. Show `u = 1` (`1 = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥P))`) via
`Coh_zero_cover_injective_gen` for the cover of `↥P` by the open sets
`V' k := (Subtype.val : ↥P → B) ⁻¹' V k` (`k ∈ S`).  It suffices to show
`(CohMap (subtypeMap (V' k)) ℤ 0).hom (u - 1) = 0` for `k ∈ S`.
* Pass from `subtypeMap (V' k)` to the `pdIncl` pullback: as continuous maps
`subtypeMap (V' k) = (pdIncl P (V k) (hVsub k)).comp ((Work.Cohomology.luSubHomeo (hVsub k)).symm)`
(`luSubHomeo`, `luSubHomeo_symm_apply` in `Submission/Work/Thom/localThomUnionAux.lean`);
prove by `ContinuousMap.ext` + `Subtype.ext`, turn it into a composition with
`Work.Thom.CohMap_comp`, and use `Work.Cohomology.bijective_CohMap_homeomorph`
(`Submission/Work/Thom/localThom_union.lean`) to discard the bijective `luSubHomeo`-factor.
So it suffices to prove `(CohMap (pdIncl P (V k) (hVsub k)) ℤ 0).hom u = 1` (use that `CohMap`
is `ℤ`-linear and `Work.Thom.CohMap_oneH`).
* Get that from `hτk k hk` and `localThomMap_pdCohMap` at `k = 0`, `U := P`, `W := V k`, `ρ := τ`,
applied to `x := (CohMap (pdIncl P (V k) (hVsub k)) ℤ 0).hom u`.  Its left-hand side is
`φ^k(u|_{V k})`; its right-hand side is the restriction of `φ u = τ''`, and
`(pdCohMap … (0+n)).hom τ'' = (zero_add n).symm ▸ ((pdCohMap … n).hom τ')` (commutation of a
degree cast with `pdCohMap`; prove by `cases` on `Nat.zero_add n`) `= (zero_add n).symm ▸
((pdCohMap … n).hom τ)` by `hag`.  Meanwhile
`localThomMap Z n (V k) ((pdCohMap … n).hom τ) 0 1 = (zero_add n).symm ▸ ((pdCohMap … n).hom τ)`
by `Work.Thom.CohMap_oneH` and `Work.Thom.mixedCupC_oneH_zero`.  Hence
`(CohMap (pdIncl P (V k) (hVsub k)) ℤ 0).hom u = 1`.
2. Conclude `φ u = φ 1 = (zero_add n).symm ▸ τ`, so `τ'' = (zero_add n).symm ▸ τ`, and cancel the
degree cast to get `τ' = τ`. -/
theorem localThom_eq_of_cover {ι' : Type} (Z : RealBundle B F ι) (n : ℕ)
    {P : Set B} (V : ι' → Set B) (hVopen : ∀ k, IsOpen (V k)) (hVsub : ∀ k, V k ⊆ P)
    (S : Finset ι') (hcov : P ⊆ ⋃ k ∈ (S : Set ι'), V k)
    (τ τ' : Work.Thom.PieceCoh Z P n)
    (hτ : Function.Bijective (Work.Thom.localThomMap Z n P τ 0))
    (hτk : ∀ k ∈ S, Function.Injective (Work.Thom.localThomMap Z n (V k)
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' P) (Z.proj ⁻¹' (V k)) (Set.preimage_mono (hVsub k)) n).hom τ) 0))
    (hag : ∀ k ∈ S, (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
          (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' P) (Z.proj ⁻¹' (V k))
          (Set.preimage_mono (hVsub k)) n).hom τ'
        = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' P) (Z.proj ⁻¹' (V k)) (Set.preimage_mono (hVsub k)) n).hom τ) :
    τ' = τ := by
  classical
  set oneHP : Work.Thom.Coh ℤ 0 ↥P :=
    Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥P)) with honeHP
  obtain ⟨u, hu⟩ := hτ.2 ((Nat.zero_add n).symm ▸ τ')
  have key : u = oneHP := by
    have hcov' : ∀ x : ↥P, ∃ j : {k : ι' // k ∈ S},
        x ∈ (Subtype.val : ↥P → B) ⁻¹' V j.1 := by
      intro x
      have hx : (x : B) ∈ ⋃ k ∈ (S : Set ι'), V k := hcov x.2
      simp only [Set.mem_iUnion] at hx
      obtain ⟨k, hk, hxk⟩ := hx
      exact ⟨⟨k, hk⟩, hxk⟩
    have hV' : ∀ j : {k : ι' // k ∈ S},
        IsOpen ((Subtype.val : ↥P → B) ⁻¹' V j.1) :=
      fun j => (hVopen j.1).preimage continuous_subtype_val
    have hper : ∀ j : {k : ι' // k ∈ S},
        (Work.Thom.CohMap (Work.Thom.subtypeMap ((Subtype.val : ↥P → B) ⁻¹' V j.1)) ℤ 0).hom
          (u - oneHP) = 0 := by
      intro j
      have hsub : Work.Thom.subtypeMap ((Subtype.val : ↥P → B) ⁻¹' V j.1)
          = (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B) P (V j.1) (hVsub j.1))).comp
              ((Work.Cohomology.luSubHomeo (X := B) (hVsub j.1)).symm
                : C(↥((Subtype.val : ↥P → B) ⁻¹' V j.1), ↥(V j.1))) := by
        apply ContinuousMap.ext
        intro y
        apply Subtype.ext
        rfl
      have hzu : (Work.Thom.CohMap
            (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B) P (V j.1) (hVsub j.1)))
            ℤ 0).hom u
          = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥(V j.1))) :=
        Work.Thom.pdIncl_choice_eq_oneH Z n (hVsub j.1) τ τ' (hτk j.1 j.2) (hag j.1 j.2) u hu
      have hz : (Work.Thom.CohMap
          (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B) P (V j.1) (hVsub j.1)))
          ℤ 0).hom (u - oneHP) = 0 := by
        rw [honeHP, map_sub, hzu, Work.Thom.CohMap_oneH, sub_self]
      rw [hsub, Work.Thom.CohMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero]
    exact eq_of_sub_eq_zero (Work.Thom.Coh_zero_cover_injective_gen
      (fun j : {k : ι' // k ∈ S} => (Subtype.val : ↥P → B) ⁻¹' V j.1)
      hV' hcov' (u - oneHP) hper)
  have hfin : (Nat.zero_add n).symm ▸ τ' = (Nat.zero_add n).symm ▸ τ := by
    rw [← hu, key, honeHP]
    exact Work.Thom.localThomMap_oneH_zero Z n P τ
  have h3 := hfin
  rw [eqRec_eq_cast, eqRec_eq_cast] at h3
  exact (cast_inj _).mp h3

end Work.Thom
