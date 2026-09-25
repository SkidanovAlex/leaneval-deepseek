import Mathlib
import Submission.NK.NUV2.LC.RouteB.RouteBSetup
import Submission.NK.NUV2.LC.RouteB.kummerMap_locUnits
import Submission.NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot
import Submission.NK.NUV2.LC.finiteSupportTwistDefs
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.Placement
import Submission.NK.HassePrinciple.levelInclHom_injective
import Submission.NK.HassePrinciple.map_levelRestrict_stabSubgroup
import Submission.NK.HassePrinciple.localInclHom_eq_restriction
import Submission.NK.NUV2.LC.RouteB.stabilizerOfFiniteEqValuationSubring
import Submission.NK.NUV2.LC.RouteB.mapIsoCompMapRes

namespace NK.NUV2.LC.RouteB

set_option linter.unusedSimpArgs false

open CategoryTheory

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The place-theoretic input: the local level group is the decomposition group of `q` -/

/-- **The local level group of `q` is the decomposition subgroup of `q`.**  For the full absolute
group `(⊤ : Subgroup Gal(K'/K))` and a place `A` of `K'` cutting out the prime `q` of `↥L`
(hypothesis `hA`), the local level group `D_A/(D_A ⊓ Gal(K'/L))` is identified, through the level
dictionary `levelGroupEquivTop`, with the stabiliser of the place `Place.ofFinite q` in
`Gal(↥L/K)`. -/
theorem localLevelGroup_equiv_stabilizer
    (A : NK.BrauerTwist.OverFinitePrime K K')
    (L : FiniteGaloisIntermediateField K K')
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hA : A.1.comap (algebraMap ↥L K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L q) :
    ∃ e₀ : NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/K)) A.1 L ≃*
        MulAction.stabilizer (↥L ≃ₐ[K] ↥L) (NK.GlobalCFT.Place.ofFinite q),
      ∀ x, (e₀ x : ↥L ≃ₐ[K] ↥L) =
        (NK.NUV2.LC.levelGroupEquivTop (K := K) (K' := K') L)
          (NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A.1 L x) := by
  classical
  set f := NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A.1 L with hf
  set e := NK.NUV2.LC.levelGroupEquivTop (K := K) (K' := K') L with he
  set G₀ : Subgroup (↥L ≃ₐ[K] ↥L) :=
    MulAction.stabilizer (↥L ≃ₐ[K] ↥L) (NK.GlobalCFT.Place.ofFinite q) with hG₀
  -- membership of the image in `G₀`
  have hmem : ∀ x : NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/K)) A.1 L,
      e (f x) ∈ G₀ := by
    intro x
    rw [hG₀, NK.NUV2.LC.RouteB.stabilizerOfFiniteEqValuationSubring q]
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [hf, he, NK.NUV2.LC.levelGroupEquivTop_apply]
      simp only [NK.BrauerHasse.localInclHom, QuotientGroup.map_mk, MonoidHom.id_apply,
        NK.HassePrinciple.levelGroupRestrictHom_mk, Subgroup.coe_inclusion]
      have hu : (u : Gal(K'/K)) ∈ NK.BrauerHasse.stabSubgroup A.1 := u.2.2
      have h1 : NK.HassePrinciple.levelRestrict L (u : Gal(K'/K)) ∈
          (NK.BrauerHasse.stabSubgroup A.1).map (NK.HassePrinciple.levelRestrict L) :=
        Subgroup.mem_map_of_mem _ hu
      rw [NK.HassePrinciple.map_levelRestrict_stabSubgroup A.1 L, hA] at h1
      exact h1
  have hinj : Function.Injective (fun x => e (f x)) := fun a b hab =>
    NK.HassePrinciple.levelInclHom_injective (U := (⊤ : Subgroup Gal(K'/K)))
      (V := (⊤ : Subgroup Gal(K'/K)) ⊓ NK.BrauerHasse.stabSubgroup A.1) inf_le_left L
      (e.injective hab)
  have hsurj : ∀ y : G₀, ∃ x, e (f x) = (y : ↥L ≃ₐ[K] ↥L) := by
    intro y
    have hy : (y : ↥L ≃ₐ[K] ↥L) ∈ NK.HassePrinciple.valuationStab
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L q) := by
      have h1 : (y : ↥L ≃ₐ[K] ↥L) ∈ MulAction.stabilizer (↥L ≃ₐ[K] ↥L)
          (NK.GlobalCFT.Place.ofFinite q) := y.2
      rwa [NK.NUV2.LC.RouteB.stabilizerOfFiniteEqValuationSubring q] at h1
    have hy2 : (y : ↥L ≃ₐ[K] ↥L) ∈ (NK.BrauerHasse.stabSubgroup A.1).map
        (NK.HassePrinciple.levelRestrict L) := by
      rw [NK.HassePrinciple.map_levelRestrict_stabSubgroup A.1 L, hA]
      exact hy
    obtain ⟨σ, hσ, hσy⟩ := Subgroup.mem_map.mp hy2
    refine ⟨QuotientGroup.mk (⟨σ, ⟨Subgroup.mem_top σ, hσ⟩⟩ :
      ↥((⊤ : Subgroup Gal(K'/K)) ⊓ NK.BrauerHasse.stabSubgroup A.1)), ?_⟩
    rw [hf, he, NK.NUV2.LC.levelGroupEquivTop_apply]
    simp only [NK.BrauerHasse.localInclHom, QuotientGroup.map_mk, MonoidHom.id_apply,
      NK.HassePrinciple.levelGroupRestrictHom_mk, Subgroup.coe_inclusion]
    exact hσy
  refine ⟨MulEquiv.ofBijective (MonoidHom.codRestrict (e.toMonoidHom.comp f) G₀ hmem)
    ⟨fun a b hab => hinj (Subtype.ext_iff.mp hab), fun y => ?_⟩, fun x => rfl⟩
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, Subtype.ext hx⟩

/-! ## Step 1: the fine localisation in the `μ_p` level model -/

/-- If the `Z/p`-level localisation of `c` vanishes, then so does the `μ_p`-level localisation:
the comparison `levelCompareRoot` transports the trivial-coefficient cohomology of the local level
group to the `μ_p`-cohomology of the same group, and `H2congr_map` identifies the two restrictions
up to this comparison. -/
theorem map_localInclHom_eq_zero_of_locLevel_eq_zero
    (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (L : FiniteGaloisIntermediateField K K')
    (c : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) L)
    (A : NK.BrauerTwist.OverFinitePrime K K')
    (h : NK.BrauerHasse.locLevel p (⊤ : Subgroup Gal(K'/K)) A.1 L
      ((NK.NUV2.ABHN.levelCompareRoot p hζ (⊤ : Subgroup Gal(K'/K)) L) c) = 0) :
    (groupCohomology.map (NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A.1 L)
      (𝟙 (Rep.res (NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A.1 L)
        (NK.HassePrinciple.muLevelRep p (⊤ : Subgroup Gal(K'/K)) L))) 2).hom c = 0 := by
  classical
  set f := NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A.1 L with hf
  set B : Rep NK.HassePrinciple.CoeffInt (NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L) :=
    NK.HassePrinciple.muLevelRep p (⊤ : Subgroup Gal(K'/K)) L with hB
  set B' : Rep (NK.BrauerHasse.Coeff p) (NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L) :=
    NK.NUV2.ABHN.trivLevelRep p (⊤ : Subgroup Gal(K'/K)) L with hB'
  set u : B.V ≃+ B'.V := NK.NUV2.ABHN.muAddEquiv p ζ hζ L with hu
  have he₀ : ∀ (g : NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L) (y : B.V),
      u ((B.ρ g) y) = (B'.ρ g) (u y) :=
    fun g y => NK.NUV2.ABHN.muAddEquiv_equivariance p hζ (⊤ : Subgroup Gal(K'/K)) L g y
  have he₁ : ∀ (g : NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/K)) A.1 L)
      (y : (Rep.res f B).V), u (((Rep.res f B).ρ g) y) = ((Rep.res f B').ρ g) (u y) :=
    fun g y => NK.NUV2.ABHN.muAddEquiv_equivariance p hζ (⊤ : Subgroup Gal(K'/K)) L (f g) y
  have hφψ : ∀ x : B.V,
      u ((Rep.Hom.hom (𝟙 (Rep.res f B))) x) = (Rep.Hom.hom (𝟙 (Rep.res f B'))) (u x) :=
    fun x => rfl
  have hmap := NK.IndecomposedDeep.H2congr_map (f := f)
    (k := NK.HassePrinciple.CoeffInt) (k' := NK.BrauerHasse.Coeff p)
    (A := B) (B := Rep.res f B) (A' := B') (B' := Rep.res f B')
    (𝟙 (Rep.res f B)) (𝟙 (Rep.res f B')) u u he₀ he₁ hφψ c
  have hzero : (groupCohomology.map f (𝟙 (Rep.res f B')) 2).hom
      (NK.IndecomposedDeep.H2congr u he₀ c) = 0 := h
  rw [hzero] at hmap
  exact (NK.IndecomposedDeep.H2congrEquiv (A := Rep.res f B) (B := Rep.res f B') u he₁).injective
    (hmap.trans (NK.IndecomposedDeep.H2congr_zero (A := Rep.res f B) (B := Rep.res f B') u he₁).symm)

/-! ## Step 2: the restriction to the decomposition group of `q` -/

/-- The restriction of `muTransport p L c` to the decomposition group of the place `q` vanishes
whenever the local level restriction of `c` vanishes.  This is the place-theoretic transport of
Step 1 along the identification `localLevelGroup_equiv_stabilizer`. -/
theorem muTransport_restrict_eq_zero
    (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (L : FiniteGaloisIntermediateField K K')
    (c : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) L)
    (A : NK.BrauerTwist.OverFinitePrime K K')
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hA : A.1.comap (algebraMap ↥L K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L q)
    (hc : (groupCohomology.map (NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A.1 L)
      (𝟙 (Rep.res (NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A.1 L)
        (NK.HassePrinciple.muLevelRep p (⊤ : Subgroup Gal(K'/K)) L))) 2).hom c = 0) :
    (groupCohomology.map
      (MulAction.stabilizer (↥L ≃ₐ[K] ↥L) (NK.GlobalCFT.Place.ofFinite q)).subtype
      (𝟙 (Rep.res (MulAction.stabilizer (↥L ≃ₐ[K] ↥L)
        (NK.GlobalCFT.Place.ofFinite q)).subtype
        (NK.HassePrinciple.muRep p K ↥L))) 2).hom
      (NK.NUV2.LC.RouteB.muTransport p L c) = 0 := by
  classical
  obtain ⟨e₀, he₀⟩ := localLevelGroup_equiv_stabilizer (K := K) (K' := K') A L q hA
  set f := NK.BrauerHasse.localInclHom (⊤ : Subgroup Gal(K'/K)) A.1 L with hf
  let e : NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L ≃* (↥L ≃ₐ[K] ↥L) :=
    NK.NUV2.LC.levelGroupEquivTop (K := K) (K' := K') L
  let e' : (NK.HassePrinciple.muLevelRep p (⊤ : Subgroup Gal(K'/K)) L).V ≃ₗ[
      NK.HassePrinciple.CoeffInt] (NK.HassePrinciple.muRep p K ↥L).V :=
    LinearEquiv.refl NK.HassePrinciple.CoeffInt (Additive ↥(rootsOfUnity p ↥L))
  -- the coordinate computation behind `muTransport`
  have hcoord : ∀ (g : NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L)
      (y : (NK.HassePrinciple.muLevelRep p (⊤ : Subgroup Gal(K'/K)) L).V),
      e' ((NK.HassePrinciple.muLevelRep p (⊤ : Subgroup Gal(K'/K)) L).ρ g y) =
        (NK.HassePrinciple.muRep p K ↥L).ρ (e g) (e' y) := by
    intro g y
    induction g using QuotientGroup.induction_on with
    | H v => rfl
  have hev : ∀ (g : NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L),
      e'.toLinearMap ∘ₗ (NK.HassePrinciple.muLevelRep p (⊤ : Subgroup Gal(K'/K)) L).ρ g =
        (NK.HassePrinciple.muRep p K ↥L).ρ (e g) ∘ₗ e'.toLinearMap :=
    fun g => LinearMap.ext (fun y => hcoord g y)
  have he'' : ∀ x : NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/K)) A.1 L,
      e'.toLinearMap ∘ₗ (Rep.res f (NK.HassePrinciple.muLevelRep p (⊤ : Subgroup Gal(K'/K)) L)).ρ x =
        (Rep.res (MulAction.stabilizer (↥L ≃ₐ[K] ↥L) (NK.GlobalCFT.Place.ofFinite q)).subtype
          (NK.HassePrinciple.muRep p K ↥L)).ρ (e₀ x) ∘ₗ e'.toLinearMap := by
    intro x
    refine LinearMap.ext (fun y => ?_)
    change e' (((NK.HassePrinciple.muLevelRep p (⊤ : Subgroup Gal(K'/K)) L).ρ (f x)) y) =
      (NK.HassePrinciple.muRep p K ↥L).ρ
        (((MulAction.stabilizer (↥L ≃ₐ[K] ↥L) (NK.GlobalCFT.Place.ofFinite q)).subtype (e₀ x)))
        (e' y)
    rw [show ((MulAction.stabilizer (↥L ≃ₐ[K] ↥L) (NK.GlobalCFT.Place.ofFinite q)).subtype (e₀ x))
        = e (f x) from he₀ x]
    exact hcoord (f x) y
  have heq : ∀ x : (Rep.res f (NK.HassePrinciple.muLevelRep p
        (⊤ : Subgroup Gal(K'/K)) L)).V, e' x = e' x := fun x => rfl
  have hsq := NK.NUV2.LC.RouteB.mapIsoCompMapRes
    (k := NK.HassePrinciple.CoeffInt)
    (A := NK.HassePrinciple.muRep p K ↥L)
    (B := NK.HassePrinciple.muLevelRep p (⊤ : Subgroup Gal(K'/K)) L)
    e e' hev f
    (MulAction.stabilizer (↥L ≃ₐ[K] ↥L) (NK.GlobalCFT.Place.ofFinite q)).subtype e₀ he₀
    e' he'' heq 2
  have hsq' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hsq) c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq'
  rw [show (ModuleCat.Hom.hom (groupCohomology.mapIso e e' hev 2).hom) c
      = NK.NUV2.LC.RouteB.muTransport p L c from
      (NK.NUV2.LC.RouteB.muTransport_apply p L c).symm, hc, map_zero] at hsq'
  exact hsq'

/-- **The localisation dictionary, easy direction (crux of Route B).**

`K` number field, `K'` a separable closure, `p` a prime, `ζ : K` a primitive `p`-th root (so
`μ_p(L) ≅ Z/p` at every level), `L` a finite Galois level, `A` a place of `K'` over a finite prime
of `K` whose induced prime of `↥L` is `q`, `c ∈ H²(LevelGroup ⊤ L, μ_p(L))`.  If the *fine* level
localisation of `c` vanishes (equivalently, via the coefficient comparison
`NK.NUV2.ABHN.levelCompareRoot`, the Z/p class `(levelCompareRoot p hζ ⊤ L) c` dies on the local level
group `D_A/(D_A ⊓ Gal(K'/L))`), then the localisation of the Kummer image of `c` in the
number-field cohomology `H²(Gal(↥L/K), ↥Lˣ)` vanishes.

## Proof route (ingredients all on disk)

1. `NK.NUV2.ABHN.levelCompareRoot p hζ ⊤ L` is `H2congrEquiv (muAddEquiv p ζ hζ L)
   (muAddEquiv_equivariance p hζ ⊤ L)`, and
   `NK.BrauerHasse.locLevel p ⊤ A L = H2.map (localInclHom ⊤ A L) (trivHom _)`.
2. `NK.IndecomposedDeep.H2congr_map` (naturality of `H2congr` under `H2.map`, with identity
   coefficients at the source and `trivHom` at the target) turns the hypothesis into
   `H2congr (muAddEquiv at the local level group) (H2.map (localInclHom ⊤ A L) (muLevelRestrictCoeff p ⊤ A L) c) = 0`,
   where `muLevelRestrictCoeff p V A L : Rep.res (localInclHom V A L) (muLevelRep p V L) ⟶
   muLevelRep p (V ⊓ D_A) L` is the identity of the coefficient module `μ_p(L)`; `H2congr` being
   injective, the hypothesis yields `H2.map (localInclHom ⊤ A L) (muLevelRestrictCoeff p ⊤ A L) c = 0`.
   CAUTION: `muLevelRestrictCoeff` lives in `Submission/Work/NUV2/LC/hbnPT/Defs.lean`, which it is
   FORBIDDEN to import here (`NK.NUV2.ABHN.levelCompareRoot` collides: that file pulls
   `NK.NUV2.ABHN.h2Twist_muColim_equiv`, the present statement needs
   `NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot`); copy the 10-line definition locally.
3. `NK.NUV2.LC.RouteB.muTransport` intertwines that restriction with the restriction to the
   decomposition group of `q`: identify the local level group `D_A/(D_A ⊓ Gal(K'/L))`, inside
   `Gal(↥L/K)`, with `MulAction.stabilizer (↥L ≃ₐ[K] ↥L) (Place.ofFinite q)` using
   `NK.HassePrinciple.levelEquiv` (with `levelAlpha`/`levelEquiv_apply_coe`),
   `NK.HassePrinciple.map_levelRestrict_stabSubgroup` and
   `NK.NUV2.LC.RouteB.stabilizerOfFiniteEqValuationSubring`; the transport is
   `NK.NUV2.LC.RouteB.mapIsoCompMapRes` applied to the `mapIso`-definition of `muTransport`
   (`NK.NUV2.LC.RouteB.muTransport_apply`).  Get
   `H2.map (stabilizer.subtype) (𝟙 _) (muTransport p L c) = 0`.  The place-theoretic input is `hA`;
   the ready-made asset is `NK.NUV2.LC.RouteB.levelGroupEquiv_symm_mem_range_localInclHom`
   (stated for general `V`, hence for `⊤`).
4. `NK.NUV2.LC.RouteB.kummerMap_locUnits` (already proved) converts 3 into
   `(locUnits K ↥L (Place.ofFinite q)).hom (kummerMap p K ↥L (muTransport p L c)) = 0`.
5. `NK.NUV2.LC.RouteB.kummerMap_transport` (proved in `RouteBSetup.lean`) rewrites
   `kummerMap p K ↥L (muTransport p L c)` as `unitsTransportK L (kummerLevel p ⊤ L c)`. -/
theorem locUnits_kummerLevel_eq_zero_of_locLevel_eq_zero
    {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) [NeZero p] (hp : p.Prime) (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (L : FiniteGaloisIntermediateField K K')
    (c : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p (⊤ : Subgroup Gal(K'/K)) L)
    (A : NK.BrauerTwist.OverFinitePrime K K')
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers
      ↥(L : IntermediateField K K')))
    (hA : A.1.comap (algebraMap ↥(L : IntermediateField K K') K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        ↥(L : IntermediateField K K') q)
    (h : NK.BrauerHasse.locLevel p (⊤ : Subgroup Gal(K'/K)) A.1 L
      ((NK.NUV2.ABHN.levelCompareRoot p hζ (⊤ : Subgroup Gal(K'/K)) L) c) = 0) :
    (NK.HassePrinciple.locUnits K ↥(L : IntermediateField K K')
      (NK.GlobalCFT.Place.ofFinite q)).hom
      ((NK.NUV2.LC.RouteB.unitsTransportK (K := K) (K' := K') L)
        ((NK.HassePrinciple.kummerLevel p (⊤ : Subgroup Gal(K'/K)) L).hom c)) = 0 := by
  have hc := map_localInclHom_eq_zero_of_locLevel_eq_zero (K := K) (K' := K') p hζ L c A h
  have h2 := muTransport_restrict_eq_zero (K := K) (K' := K') p hζ L c A q hA hc
  rw [NK.NUV2.LC.RouteB.kummerMap_transport p L c]
  exact NK.NUV2.LC.RouteB.kummerMap_locUnits (F := K)
    (L := ↥(L : IntermediateField K K')) p (NK.GlobalCFT.Place.ofFinite q)
    (NK.NUV2.LC.RouteB.muTransport p L c) h2

end NK.NUV2.LC.RouteB
