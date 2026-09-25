import Mathlib
import Submission.NK.NUV2.LC.RouteB.stabilizerOfFiniteEqValuationSubring
import Submission.NK.NUV2.LC.finiteSupportTwistDefs
import Submission.NK.HassePrinciple.localInclHom_eq_restriction
import Submission.NK.HassePrinciple.map_levelRestrict_stabSubgroup

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace NK.NUV2.LC.RouteB

open scoped Pointwise

open NK.BrauerHasse

/-! ## Auxiliary level-group computations

`NK.HassePrinciple.levelGroupRestrictHom V L : LevelGroup V L →* Gal(L/K)` is the descent of the
restriction map `Gal(K'/K) →* Gal(L/K)` along the quotient `↥V ↠ LevelGroup V L = V/(V ∩ Gal(K'/L))`.
We record its range and its injectivity, together with the commutation with the local inclusion
`localInclHom ⊤ A L : (D_A)/(D_A ∩ Gal(K'/L)) →* LevelGroup ⊤ L`. -/

section generic

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The range of the restriction map on a level group is the image of the subgroup under the
restriction to the level. -/
lemma range_levelGroupRestrictHom (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    (NK.HassePrinciple.levelGroupRestrictHom V L).range =
      V.map (NK.HassePrinciple.levelRestrict L) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (L.fixingSubgroup.subgroupOf V) y
    refine Subgroup.mem_map.mpr ⟨(v : Gal(K'/K)), v.2, ?_⟩
    rw [QuotientGroup.mk'_apply]
    exact (NK.HassePrinciple.levelGroupRestrictHom_mk V L v).symm
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨QuotientGroup.mk ⟨g, hg⟩, NK.HassePrinciple.levelGroupRestrictHom_mk V L ⟨g, hg⟩⟩

/-- The restriction map on a level group is injective: its kernel is exactly the subgroup by which
the level group is quotiented. -/
lemma injective_levelGroupRestrictHom (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (NK.HassePrinciple.levelGroupRestrictHom V L) := by
  exact (QuotientGroup.injective_lift_iff (L.fixingSubgroup.subgroupOf V)
    (NK.HassePrinciple.levelRestrictHom V L) _).mpr
    (NK.HassePrinciple.levelRestrictHom_ker V L).symm

/-- The restriction map on the level group of `⊤` commutes with the inclusion of the local level
group of a place: on the class of `w ∈ D_A` both sides are the restriction of `w` to `L`. -/
lemma comp_localInclHom_levelGroupRestrictHom (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    (NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L).comp
        (NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A L)
      = NK.HassePrinciple.levelGroupRestrictHom (⊤ ⊓ NK.BrauerHasse.stabSubgroup A) L := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H u =>
    simp only [MonoidHom.comp_apply, NK.BrauerHasse.localInclHom, QuotientGroup.map_mk,
      NK.HassePrinciple.levelGroupRestrictHom_mk, Subgroup.coe_inclusion]

end generic

/-- **The decomposition-group restriction at a level is bijective.**

Let `A` be a place of a separable closure `K'` of a number field `K` over a finite prime, and let `L`
be a finite Galois level with the place `q` of `↥L` cut out by `A`
(`hA : A.1.comap (algebraMap ↥L K') = 𝒪_{L,q}`).  Then the image of the decomposition group
`W = ⊤ ⊓ D_A` of `A` in `Gal(↥L/K)` is exactly the decomposition group (stabiliser) `Γ_q` of `q`,
and the composite `levelGroupEquivTop L ∘ localInclHom ⊤ A.1 L` is a bijection onto `Γ_q`.

Concretely: there is a `MulEquiv e : LocalLevelGroup ⊤ A.1 L ≃* Γ_q` whose underlying map sends the
class of `w ∈ W` to the restriction of `w` to `L` (i.e. `levelGroupEquivTop L (localInclHom ⊤ A.1 L x)`).

Route.  (`LocalLevelGroup ⊤ A.1 L = ↥(⊤ ⊓ D_A) ⧸ ...` and `localInclHom ⊤ A.1 L` are the subgroup
quotient maps.)  Injectivity: `levelGroupEquivTop L` is an isomorphism and
`NK.HassePrinciple.levelInclHom_injective`/`NK.BrauerHasse.localInclHom` is injective.  Surjectivity
onto `Γ_q`: given `τ ∈ Γ_q`, use
`Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois` (with base `K`,
`E = K'`, `N = ↥L`, using `A.1.comap (algebraMap K K') ≠ ⊤`, which follows from `hA` since
`A.1.comap (algebraMap K K') = (A.1.comap (algebraMap ↥L K')).comap (algebraMap K ↥L)` and
`valuationSubringAtPrime_ne_top`) to lift `τ` to `σ ∈ D_A ⊆ Gal(K'/K)`.  For the membership part
(the image of `W` lands in `Γ_q`): `σ ∈ D_A` fixes the valuation ring `A.1`, hence its restriction
to `L` fixes `A.1.comap (algebraMap ↥L K') = 𝒪_{L,q}`, i.e. lies in the stabiliser of `q`
(`NK.NUV2.LC.RouteB.smul_valuationSubringAtPrime`,
`Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul`).  Finally build the `MulEquiv` by
`MulEquiv.ofBijective` of the codRestriction of `levelGroupEquivTop L ∘ localInclHom ⊤ A.1 L` to
`Γ_q`.  Reviewers' hint: the subgroup equality `(⊤ ⊓ D_A).map (levelRestrict L) = Γ_q` is on disk as
`NK.HassePrinciple.map_levelRestrict_stabSubgroup` combined with
`NK.NUV2.LC.RouteB.stabilizerOfFiniteEqValuationSubring` — use them rather than re-deriving. -/
theorem decompRestrict_bij {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (A : NK.BrauerTwist.OverFinitePrime K K')
    (L : FiniteGaloisIntermediateField K K')
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(L : IntermediateField K K')))
    (hA : A.1.comap (algebraMap ↥(L : IntermediateField K K') K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        ↥(L : IntermediateField K K') q) :
    ∃ (e : NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/K)) A.1 L ≃*
        MulAction.stabilizer Gal(↥(L : IntermediateField K K')/K)
          (NK.GlobalCFT.Place.ofFinite q)),
      ∀ x : NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/K)) A.1 L,
        (e x : Gal(↥(L : IntermediateField K K')/K)) =
          NK.NUV2.LC.levelGroupEquivTop L
            (NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A.1 L x) := by
  -- The decomposition group of `A` and the stabiliser `Γ_q` of `q`, as subgroups of `Gal(K'/K)`
  -- resp. of `Gal(↥L/K)`.
  let D : Subgroup Gal(K'/K) := NK.BrauerHasse.stabSubgroup A.1
  let Γ : Subgroup Gal(↥(L : IntermediateField K K')/K) :=
    MulAction.stabilizer Gal(↥(L : IntermediateField K K')/K) (NK.GlobalCFT.Place.ofFinite q)
  -- The restriction map on the local level group of `A`.
  let f : NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/K)) A.1 L →*
      Gal(↥(L : IntermediateField K K')/K) :=
    NK.HassePrinciple.levelGroupRestrictHom (⊤ ⊓ D) L
  -- Its range is the image of the decomposition group, i.e. the decomposition group of `q`.
  have hsub : (⊤ ⊓ D).map (NK.HassePrinciple.levelRestrict L) = Γ := by
    dsimp only [D, Γ]
    rw [top_inf_eq]
    rw [NK.HassePrinciple.map_levelRestrict_stabSubgroup A.1 L, hA]
    exact (NK.NUV2.LC.RouteB.stabilizerOfFiniteEqValuationSubring q).symm
  have hrange : f.range = Γ := by
    dsimp only [f]
    rw [range_levelGroupRestrictHom]
    exact hsub
  have hmem : ∀ x, f x ∈ Γ := fun x => by rw [← hrange]; exact ⟨x, rfl⟩
  -- Injectivity of the restriction map (its kernel is the subgroup quotiented out).
  have hinj : Function.Injective f := injective_levelGroupRestrictHom (⊤ ⊓ D) L
  have hinj' : Function.Injective (f.codRestrict Γ hmem) :=
    fun a b hab => hinj (congrArg Subtype.val hab)
  have hsurj' : Function.Surjective (f.codRestrict Γ hmem) := by
    intro y
    have hy : (y : Gal(↥(L : IntermediateField K K')/K)) ∈ f.range := by
      rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let e : NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/K)) A.1 L ≃*
      MulAction.stabilizer Gal(↥(L : IntermediateField K K')/K)
        (NK.GlobalCFT.Place.ofFinite q) :=
    MulEquiv.ofBijective (f.codRestrict Γ hmem) ⟨hinj', hsurj'⟩
  refine ⟨e, ?_⟩
  intro x
  have h1 : (e x : Gal(↥(L : IntermediateField K K')/K)) = f x := rfl
  rw [h1, NK.NUV2.LC.levelGroupEquivTop_apply]
  show f x = (NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L).comp
      (NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A.1 L) x
  rw [show (NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L).comp
      (NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A.1 L) = f from
      comp_localInclHom_levelGroupRestrictHom A.1 L]

end NK.NUV2.LC.RouteB
