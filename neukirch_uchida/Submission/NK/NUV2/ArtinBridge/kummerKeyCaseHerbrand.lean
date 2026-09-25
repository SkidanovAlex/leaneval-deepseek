import Mathlib
import Submission.NK.GlobalCFT.Cohomology
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.GlobalCFTdeep.Existence
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.exists_goodS
import Submission.NK.GlobalCFTdeep.SecondInequality.exists_finset_place_idealClassMap
import Submission.NK.CFTLib.Existence.index_kummerE_sup_principal
import Submission.NK.NUV2.ArtinBridge.exists_finset_forall_localUnits_imp_mem
import Submission.NK.NUV2.ArtinBridge.kummerE_le_of_open_le
import Submission.NK.NUV2.ArtinBridge.ramificationIdx_eq_one_kummerSUnitField
import Submission.NK.NUV2.ArtinBridge.KummerSUnitField
import Submission.NK.NUV2.ArtinBridge.KummerSUnitFieldInfinite
import Submission.NK.NUV2.ArtinBridge.finiteDimensional_kummerSUnitField
import Submission.NK.NUV2.ArtinBridge.finrank_kummerSUnitField
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerField_ramificationIdx_eq_one_of_unit
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormInfinite_surjective_of_mem_localPow
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow_mem_localNormInfinite
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField

/-!
# The key case of Takagi's existence theorem, in Herbrand form

`NK.NUV2.ArtinBridge.kummerKeyCase` (Milne, *CFT*, Lemma 9.3) is proved there using the
abelian index formula `[C_K : N_{L/K}C_L] = [L : K]`, which in this workspace is available
unconditionally only from the global fundamental class
(`NK.CFTLib.Existence.index_eq_finrank_of_isAbelian`).

The present file records the same argument *modulo* the abelian index formula, taken in its
Herbrand form `NK.GlobalCFT.HerbrandQuotient K L`: this is exactly the input produced by the
first inequality of class field theory (Milne, *CFT*, Theorem 4.3), and it is the form in which
the key case is consumed by `NK.NUV2.ArtinBridge.takagiExistence`.

The proof is an adaptation of `NK.NUV2.ArtinBridge.kummerKeyCase`, with the single use of
`index_eq_finrank_of_isAbelian` replaced by `index_eq_finrank_of_abelian_of_herbrand`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT

/-! ## The existence of the Kummer `S`-field with `E_S ≤ N_{L/K}𝕀_L`

This is the existence half of `NK.NUV2.ArtinBridge.exists_kummerField_kummerE_le_normImage`,
assembled here from the (already proved) inputs of the colleagues: the ramification statement
`ramificationIdx_eq_one_kummerSUnitField` (unramified outside `S`) and the archimedean statement
`localPow_mem_localNormInfinite_kummerSUnitField`.  The field is the Kummer `S`-field
`L = K(U(S)^{1/p})`, and the containment is
`NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp`.
-/

/-- Every finite place outside `S` is unramified in the Kummer `S`-field. -/
private theorem kcHerbrand_localUnits_mem_normImage {K : Type} [Field K] [NumberField K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] {p : ℕ} (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    [FiniteDimensional K ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S)]
    [NumberField ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S)]
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S) :
    ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (∃ q : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S)),
        q.asIdeal.LiesOver Q.asIdeal ∧
          q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1) →
      NK.GlobalCFT.Place.ofFinite Q ∈ S := by
  intro Q hQ
  by_contra hQS
  obtain ⟨q, hq, hram⟩ := hQ
  exact hram (NK.NUV2.ArtinBridge.ramificationIdx_eq_one_kummerSUnitField
    (K := K) (Ω := Ω) hp hζ S hSinf hSp Q hQS q hq)

/-- **Existence of a finite abelian extension of degree `p ^ |S|` with `E_S ≤ N_{L/K}𝕀_L`.**

For `K` a number field containing a primitive `p`-th root of unity and `S` a finite set of places
containing all archimedean places and all places above `p`, the Kummer `S`-field
`L = K(U(S)^{1/p})` has degree `p ^ |S|` over `K` and `E_S = kummerE p S ∅ ≤ N_{L/K}𝕀_L`. -/
theorem exists_kummerSUnitField_kummerE_le_normImage {K : Type} [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L) (_ : IsMulCommutative (L ≃ₐ[K] L)),
      Module.finrank K L = p ^ S.card ∧
        NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅ ≤
          NK.GlobalCFT.Idele.normImage K L := by
  let Ω := SeparableClosure K
  haveI hfd : FiniteDimensional K ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S) :=
    NK.NUV2.ArtinBridge.finiteDimensional_kummerSUnitField (K := K) (Ω := Ω) hp hζ S hSinf
  haveI hnf : NumberField ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField _
  have hgal : IsGalois K ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S) :=
    NK.NUV2.ArtinBridge.isGalois_kummerSUnitField (K := K) (Ω := Ω) (S := S) (p := p) hp hζ
  have hcomm : IsMulCommutative
      (↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S) ≃ₐ[K]
        ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S)) :=
    NK.NUV2.ArtinBridge.isMulCommutative_kummerSUnitField (K := K) (Ω := Ω) (S := S) (p := p)
      hp hζ
  have hexp : ∀ σ : ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S) ≃ₐ[K]
      ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S), σ ^ p = 1 :=
    NK.NUV2.ArtinBridge.pow_algEquiv_eq_one_kummerSUnitField (K := K) (Ω := Ω) (S := S)
      (p := p) hp hζ
  have hdeg : Module.finrank K ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S) = p ^ S.card :=
    NK.NUV2.ArtinBridge.finrank_kummerSUnitField (K := K) (Ω := Ω) hp hζ S hSinf
  have hInf : ∀ (v : NumberField.InfinitePlace K)
      (w : NumberField.InfinitePlace ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S))
      [w.LiesOver v],
      ∀ x ∈ NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow (K := K) p
        (NK.GlobalCFT.Place.ofInfinite v),
      ∃ u : w.Completionˣ, NK.GlobalCFT.Place.localNormInfinite w v u = x :=
    fun v w _ x hx => NK.NUV2.ArtinBridge.localPow_mem_localNormInfinite_kummerSUnitField
      (K := K) (Ω := Ω) hp hζ S v w x hx
  have hram := kcHerbrand_localUnits_mem_normImage (K := K) (Ω := Ω) hp hζ S hSinf hSp
  have hle : NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅ ≤
      NK.GlobalCFT.Idele.normImage K ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S) :=
    NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
      (K := K) (L := ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S)) hp hexp S hSinf hram hInf
  exact ⟨↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S), inferInstance, hnf, inferInstance, hfd,
    hgal, hcomm, hdeg, hle⟩

/-- **A subgroup with the same index as a containing subgroup is equal to it.**  If `H ≤ K` and
`[G : H] = [G : K] ≠ 0`, then `H = K`. -/
private theorem eqOfLeOfIndexEq {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K)
    (hidx : H.index = K.index) (hne : H.index ≠ 0) : H = K := by
  have hrel : H.relIndex K = 1 := by
    have hmul := Subgroup.relIndex_mul_index h
    rw [hidx] at hmul
    have hKpos : 0 < K.index := by rw [← hidx]; exact Nat.pos_of_ne_zero hne
    exact Nat.eq_of_mul_eq_mul_right hKpos (by rw [hmul, one_mul])
  have htop : H.subgroupOf K = ⊤ := by
    rw [← Subgroup.index_eq_one, ← Subgroup.relIndex]
    exact hrel
  exact le_antisymm h (Subgroup.subgroupOf_eq_top.mp htop)

/-- **The key case of Takagi's existence theorem** (Milne, *CFT*, Lemma 9.3), modulo the abelian
index formula in Herbrand form: over a number field `K` containing a primitive `p`-th root of
unity, every open subgroup of index `p` of the idèle class group contains the norm group of a
finite abelian extension. -/
theorem kummerKeyCaseHerbrand
    (hh : ∀ {K' L' : Type} [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']
      [FiniteDimensional K' L'] [IsGalois K' L'] [IsMulCommutative (L' ≃ₐ[K'] L')],
      NK.GlobalCFT.HerbrandQuotient K' L')
    (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (ζ : K)
    (hζ : IsPrimitiveRoot ζ p) (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K))
    (hV : V.FiniteIndex) (hopen : IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K)))
    (hidx : V.index = p) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L) (_ : IsMulCommutative (L ≃ₐ[K] L)),
      NK.GlobalCFT.Idele.normClassSubgroup K L ≤ V := by
  classical
  have hp : p.Prime := Fact.out (p := p.Prime)
  -- ### the preimage `U` of `V` in the idèle group
  let U : Subgroup 𝕀[K] := V.comap (IdeleClassGroup.mk K)
  have hUmk : Subgroup.map (IdeleClassGroup.mk K) U = V :=
    Subgroup.map_comap_eq_self (fun x _ => IdeleClassGroup.mk_surjective K x)
  have hUopen : IsOpen (U : Set 𝕀[K]) := by
    have hcont : Continuous (IdeleClassGroup.mk K) := QuotientGroup.continuous_mk
    exact hopen.preimage hcont
  -- ### a finite set of places giving a congruence subgroup inside `U`
  obtain ⟨F₀, hF₀⟩ := NK.NUV2.ArtinBridge.exists_finset_forall_localUnits_imp_mem (K := K) U hUopen
  -- ### a finite set of places whose idèles generate the class group
  obtain ⟨S₁, hS₁inf, hS₁gen⟩ :=
    NK.GlobalCFTdeep.SecondInequality.exists_finset_place_idealClassMap (K := K)
  -- ### the places above `p`
  have hBfin : {q : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ q.asIdeal}.Finite :=
    NK.GlobalCFTdeep.SecondInequality.KummerCase.finite_setOf_prime_mem_ringOfIntegers (K := K) hp
  let B : Finset (Place K) := hBfin.toFinset.image Place.ofFinite
  let S : Finset (Place K) := F₀ ∪ S₁ ∪ B
  have hF₀S : F₀ ⊆ S := fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hSinf : ∀ w : InfinitePlace K, Place.ofInfinite w ∈ S := fun w =>
    Finset.mem_union_left B
      (Finset.mem_union_right F₀ (hS₁inf (Place.ofInfinite w) (Place.isInfinite_ofInfinite w)))
  have hS₀S : S₁ ⊆ S := fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hSp : ∀ q : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ q.asIdeal → Place.ofFinite q ∈ S :=
    fun q hq => Finset.mem_union_right (F₀ ∪ S₁)
      (Finset.mem_image_of_mem _ (hBfin.mem_toFinset.mpr hq))
  -- ### `𝕀_K = Kˣ · 𝕀_{K,S}`
  have hSgen : (⊤ : Subgroup 𝕀[K]) =
      NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFTdeep.TIdeles (S : Set (Place K)) :=
    NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles (S : Set (Place K)) (by
      intro c
      obtain ⟨u, hu, huc⟩ := hS₁gen c
      exact ⟨u, NK.GlobalCFTdeep.SecondInequality.TIdeles_mono hS₀S hu, huc⟩)
  -- ### the Kummer field of the `S`-units, and Milne's local input
  obtain ⟨L, hFL, hNL, hAL, hfdL, hGalL, hcommL, hfrL, hLE⟩ :=
    NK.NUV2.ArtinBridge.exists_kummerSUnitField_kummerE_le_normImage (K := K) hp hζ S hSinf hSp
  refine ⟨L, hFL, hNL, hAL, hfdL, hGalL, hcommL, ?_⟩
  letI : Field L := hFL
  letI : NumberField L := hNL
  letI : Algebra K L := hAL
  letI : FiniteDimensional K L := hfdL
  letI : IsGalois K L := hGalL
  -- ### `𝕀_K^p ≤ U`
  have hpow : ∀ x : 𝕀[K], x ^ p ∈ U := by
    intro x
    show IdeleClassGroup.mk K (x ^ p) ∈ V
    have hm : IdeleClassGroup.mk K (x ^ p) = (IdeleClassGroup.mk K x) ^ p := map_pow _ x p
    rw [hm]
    have := Subgroup.pow_index_mem V (IdeleClassGroup.mk K x)
    rwa [hidx] at this
  -- ### `E_S ≤ U`
  have hE : NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅ ≤ U :=
    NK.NUV2.ArtinBridge.kummerE_le_of_open_le S F₀ U hF₀ hF₀S hpow
  -- ### the principal idèles are in `U`
  have hP : NK.GlobalCFT.Idele.principalSubgroup K ≤ U := by
    intro x hx
    show IdeleClassGroup.mk K x ∈ V
    have hker : (IdeleClassGroup.mk K).ker = NK.GlobalCFT.Idele.principalSubgroup K := by
      show (QuotientGroup.mk' (NK.GlobalCFT.Idele.principalSubgroup K)).ker =
        NK.GlobalCFT.Idele.principalSubgroup K
      rw [QuotientGroup.ker_mk']
    have hx1 : IdeleClassGroup.mk K x = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hx
    rw [hx1]
    exact V.one_mem
  -- ### `Kˣ · E_S ≤ V`
  have hSBV : Subgroup.map (IdeleClassGroup.mk K)
      (NK.GlobalCFT.Idele.principalSubgroup K ⊔
        NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅) ≤ V := by
    rw [← hUmk]
    exact Subgroup.map_mono (sup_le hP hE)
  -- ### `Kˣ · E_S ≤ N_{L/K} C_L`
  have hSBN : Subgroup.map (IdeleClassGroup.mk K)
      (NK.GlobalCFT.Idele.principalSubgroup K ⊔
        NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅) ≤
      NK.GlobalCFT.Idele.normClassSubgroup K L := by
    rw [NK.GlobalCFT.Idele.normClassSubgroup]
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    obtain ⟨a, ha, e, he, rfl⟩ := Subgroup.mem_sup.mp hx
    have hker : (IdeleClassGroup.mk K).ker = NK.GlobalCFT.Idele.principalSubgroup K := by
      show (QuotientGroup.mk' (NK.GlobalCFT.Idele.principalSubgroup K)).ker =
        NK.GlobalCFT.Idele.principalSubgroup K
      rw [QuotientGroup.ker_mk']
    have ha1 : IdeleClassGroup.mk K a = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact ha
    change IdeleClassGroup.mk K (a * e) ∈ Subgroup.map (IdeleClassGroup.mk K)
      (NK.GlobalCFT.Idele.normImage K L)
    rw [map_mul, ha1, one_mul]
    exact Subgroup.mem_map_of_mem _ (hLE he)
  -- ### the two index computations
  have hidxE : (Subgroup.map (IdeleClassGroup.mk K)
      (NK.GlobalCFT.Idele.principalSubgroup K ⊔
        NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅)).index =
      p ^ S.card :=
    NK.CFTLib.Existence.index_kummerE_sup_principal K p hζ S hSinf hSp hSgen
  have hidxN : (NK.GlobalCFT.Idele.normClassSubgroup K L).index = p ^ S.card := by
    rw [NK.GlobalCFTdeep.index_eq_finrank_of_abelian_of_herbrand (K := K) (L := L)
      (hh (K' := K) (L' := L)), hfrL]
  -- ### equality of the two index-`p^{|S|}` subgroups
  have heq : NK.GlobalCFT.Idele.normClassSubgroup K L =
      Subgroup.map (IdeleClassGroup.mk K)
        (NK.GlobalCFT.Idele.principalSubgroup K ⊔
          NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅) :=
    (eqOfLeOfIndexEq hSBN (by rw [hidxE, hidxN])
      (by rw [hidxE]; exact pow_ne_zero _ hp.ne_zero)).symm
  rw [heq]
  exact hSBV

end NK.NUV2.ArtinBridge
