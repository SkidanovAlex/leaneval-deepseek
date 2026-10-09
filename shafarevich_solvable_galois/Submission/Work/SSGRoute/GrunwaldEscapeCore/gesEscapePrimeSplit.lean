import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.step4_y_escape_v2.ChebotarevSplit
import Submission.Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split
import Submission.Work.SSGRoute.exists_mem_closure_decomp_mul_mem_fixingSubgroup
import Submission.Work.SSGRoute.step4_y_escape_v2.RayClass
import Submission.Work.SSGRoute.ges_escape_aux
import Submission.Work.SSGRoute.finiteIndex_gesU
import Submission.Work.SSGRoute.EscapeCoreLib.classField_stable_open_finiteIndex
import Submission.Work.SSGRoute.EscapeCoreLib.baseChange_over_K
import Submission.Work.SSGRoute.EscapeCoreLib.isGalois_comap
import Submission.Work.SSGRoute.frobeniusClass_realisation_below
import Submission.Work.SSGRoute.ssg8Chebotarev
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.NK.CFTLib.Existence.artinMapOfARL
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHomType
import Submission.NK.Chebotarev.FrobRestriction
import Submission.NK.Chebotarev.FrobeniusOne
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.GrunwaldEscapeCore

open scoped NumberField
open NK.GlobalCFT

/-! ## The abelian class field, inside `Ω`, of an open finite-index subgroup of `C_K` -/

/-- **The abelian class field of an open finite-index subgroup, inside `Ω`.**

For an open finite-index subgroup `U ≤ C_↥K` there is an *abelian* finite Galois extension
`M / ↥K` inside `Ω` with `N_{M/↥K} C_M = U`.  The existence theorem of global class field theory
supplies the abstract extension and its maximal abelian subextension; the abelian class field of
`U` is an intermediate field of the latter, and abelianness is transported into `Ω`. -/
theorem exists_abelian_classField_inside
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (U : Subgroup (IdeleClassGroup ↥K)) (hUfin : U.FiniteIndex)
    (hUopen : IsOpen (U : Set (IdeleClassGroup ↥K))) :
    ∃ (M : IntermediateField ↥K Ω) (_ : FiniteDimensional ↥K M) (_ : IsGalois ↥K M)
      (_ : NumberField ↥M) (_ : IsMulCommutative (↥M ≃ₐ[↥K] ↥M)),
      Idele.normClassSubgroup ↥K ↥M = U := by
  classical
  haveI : U.FiniteIndex := hUfin
  have hpos : 0 < U.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨L, hFL, hNL, hAL, hfdL, hgalL, hNormL, _hdegL⟩ :=
    Work.SSGRoute.CFTSide.classField_exists_of_index (K := ↥K) U.index hpos U hUfin hUopen rfl
  letI : Field L := hFL
  letI : NumberField L := hNL
  letI : Algebra ↥K L := hAL
  letI : FiniteDimensional ↥K L := hfdL
  haveI : IsGalois ↥K L := hgalL
  obtain ⟨A, hAgal, hAcomm, hAle⟩ :=
    Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
      NK.CFTLib.fundamentalClassElement (K := ↥K) (L := L) U (le_of_eq hNormL)
  haveI : IsGalois ↥K ↥A := hAgal
  haveI : IsMulCommutative (↥A ≃ₐ[↥K] ↥A) := hAcomm
  haveI : NumberField ↥A := NumberField.of_module_finite ↥K ↥A
  obtain ⟨E, hEgal, hEnorm, _⟩ :=
    NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index
      NK.CFTLib.artinReciprocityIdeal_proved NK.CFTLib.fundamentalClassElement
      (K := ↥K) (L := ↥A) U hAle
  haveI : IsGalois ↥K ↥E := hEgal
  haveI : NumberField ↥E := NumberField.of_module_finite ↥K ↥E
  have hcommE : ∀ a b : ↥E ≃ₐ[↥K] ↥E, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥E) (E := ↥A) a
    obtain ⟨y, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥E) (E := ↥A) b
    rw [← map_mul, ← map_mul, mul_comm' x y]
  haveI : IsMulCommutative (↥E ≃ₐ[↥K] ↥E) := IsMulCommutative.of_comm hcommE
  haveI : Algebra.IsAlgebraic ↥K ↥E := Algebra.IsAlgebraic.of_finite ↥K ↥E
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  let ι : ↥E →ₐ[↥K] Ω := IsAlgClosed.lift
  let M : IntermediateField ↥K Ω := ι.fieldRange
  let φ : ↥E ≃ₐ[↥K] ↥M := ι.equivFieldRange
  haveI hfdM : FiniteDimensional ↥K ↥M :=
    FiniteDimensional.of_injective φ.symm.toLinearEquiv.toLinearMap φ.symm.injective
  haveI hgalM : IsGalois ↥K ↥M := IsGalois.of_algEquiv φ
  haveI hnfM : NumberField ↥M := NumberField.of_module_finite ↥K ↥M
  haveI hcommM : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) :=
    IsMulCommutative.of_comm (fun a b => by
      obtain ⟨x, rfl⟩ := (AlgEquiv.autCongr φ).surjective a
      obtain ⟨y, rfl⟩ := (AlgEquiv.autCongr φ).surjective b
      rw [← map_mul, ← map_mul, mul_comm'])
  refine ⟨M, hfdM, hgalM, hnfM, hcommM, ?_⟩
  rw [show Idele.normClassSubgroup ↥K ↥M = Idele.normClassSubgroup ↥K ↥E from
      SetLike.ext fun x => Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv φ.symm x,
    hEnorm]

/-! ## The idèlic Artin isomorphism with its Frobenius values -/

/-- **The idèlic Artin isomorphism of an abelian extension, with the Frobenius values.**

For a finite abelian extension `L / K` of number fields there is a finite set `Bad` of primes of
`K` (the primes containing the conductor) and an isomorphism
`C_K ⧸ N_{L/K}C_L ≃* Gal(L/K)` (with the Frobenius normalisation) such that every prime outside
`Bad` is unramified and its idèle class is sent to its Frobenius element. -/
theorem exists_artinIso_frobAtPrime {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] :
    ∃ (Bad : Finset (NK.Chebotarev.PrimeIdeal K))
      (Θ : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L ≃* (L ≃ₐ[K] L)),
      (∀ 𝔮 ∉ Bad, ∀ Q : NK.Chebotarev.PrimeIdeal L, Q.asIdeal.LiesOver 𝔮.asIdeal →
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) ∧
      (∀ 𝔮 ∉ Bad, Θ (QuotientGroup.mk' (Idele.normClassSubgroup K L)
          (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮))) =
        NK.Chebotarev.frobAtPrime 𝔮) := by
  classical
  obtain ⟨m, hm, art, hram, hprinc, hnorm, hfrob, hsurj⟩ :=
    NK.CFTLib.Existence.exists_ideleArtinMap_of_arl
      NK.CFTLib.artinReciprocityIdeal_proved (K := K) (L := L)
  have hker : Idele.principalSubgroup K ≤ art.ker := by
    rintro x ⟨a, rfl⟩
    exact MonoidHom.mem_ker.mpr (hprinc a)
  obtain ⟨e, he⟩ := NK.CFTLib.Existence.exists_artinIso_of_ideleArtin
    NK.CFTLib.fundamentalClassElement art hker hnorm hsurj
  have hm0 : (m : NumberField.RingOfIntegers K) ≠ 0 := by exact_mod_cast hm.ne'
  have hspan0 : Ideal.span {(m : NumberField.RingOfIntegers K)} ≠ 0 := by
    rw [Ne]
    intro h
    exact hm0 (Ideal.span_singleton_eq_bot.mp h)
  have hfin : ({𝔮 : NK.Chebotarev.PrimeIdeal K |
      (m : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal} : Set _).Finite := by
    refine (Ideal.finite_factors (R := NumberField.RingOfIntegers K) (I :=
      Ideal.span {(m : NumberField.RingOfIntegers K)}) hspan0).subset ?_
    intro 𝔮 h𝔮
    show 𝔮.asIdeal ∣ Ideal.span {(m : NumberField.RingOfIntegers K)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h𝔮
  have hmem_toFinset : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K,
      𝔮 ∈ hfin.toFinset ↔ (m : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal := by
    intro 𝔮
    simp
  refine ⟨hfin.toFinset, e, ?_, ?_⟩
  · intro 𝔮 h𝔮 Q hQ
    refine hram 𝔮 ?_ Q hQ
    intro hcon
    exact h𝔮 ((hmem_toFinset 𝔮).mpr hcon)
  · intro 𝔮 h𝔮
    rw [he (NK.HeckeL.ideleOfPrime K 𝔮)]
    refine hfrob 𝔮 ?_
    intro hcon
    exact h𝔮 ((hmem_toFinset 𝔮).mpr hcon)

/-! ## A finite Galois container inside `Ω`, over `↥K` and over `k` -/

/-- **A finite Galois container.**

For a finite Galois `K/k` inside `Ω` and a finite Galois `M/↥K` inside `Ω` there is a finite Galois
extension `E/k` inside `Ω` whose carrier contains both `K` and `M` (so that Čebotarev applies over
the base field `k`, and `E` also carries a `↥K`-algebra structure given by the inclusion). -/
theorem exists_galois_container
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] :
    ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧ IsGalois k E ∧ NumberField ↥E ∧
      (K : Set Ω) ⊆ (E : Set Ω) ∧ (M : Set Ω) ⊆ (E : Set Ω) := by
  classical
  haveI : FiniteDimensional k ↥M := FiniteDimensional.trans k ↥K ↥M
  haveI : IsScalarTower k ↥M Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  let E₀ : IntermediateField k Ω := IntermediateField.normalClosure k ↥M Ω
  haveI : FiniteDimensional k ↥E₀ := inferInstance
  haveI : Normal k ↥E₀ := inferInstance
  haveI : IsGalois k ↥E₀ := inferInstance
  have hMe : (M : Set Ω) ⊆ (E₀ : Set Ω) := by
    intro x hx
    exact AlgHom.fieldRange_le_normalClosure (IsScalarTower.toAlgHom k ↥M Ω)
      (AlgHom.mem_fieldRange.mpr ⟨⟨x, hx⟩, rfl⟩)
  have hKe : (K : Set Ω) ⊆ (E₀ : Set Ω) := by
    intro x hx
    exact hMe (M.algebraMap_mem ⟨x, hx⟩)
  exact ⟨E₀, inferInstance, inferInstance, NumberField.of_module_finite k ↥E₀, hKe, hMe⟩

/-! ## The Frobenius at the prime below, in the abelian extension `M/↥K` -/

/-- **The Frobenius transfer.**

Let `k ⊆ ↥K ⊆ ↥M` be number fields, `E/k` a finite Galois extension with `↥K`- and `↥M`-algebra
structures making the obvious diagram commute (`IsScalarTower` throughout), `c ∈ Gal(M/↥K)` and
`g ∈ Gal(E/k)` such that `g` fixes `↥K` pointwise and restricts to `c` on `↥M`.

If `P` is a prime of `𝓞 E` over a prime `𝔭` of `k` at which `g` is an arithmetic Frobenius element,
and if the inertia degree of the `↥K`-prime below `P` over `𝔭` is one (i.e. the `k`-prime below `P`
has residue degree one in `K`, which holds in particular when it splits completely in `K`), then
`c` is an arithmetic Frobenius element, in the abelian extension `↥M/↥K`, at the `↥K`-prime below
`P`.

This is the step that converts the Čebotarev information at the level of a Galois closure over `k`
into the idèle-class information at the level of `M/↥K`; it is the `(L₁, L₂) = (K, K)` case of
the design's step 5. -/
theorem isFrobAtPrime_of_isFrobAt_inertiaDeg_eq_one
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M]
    (E : Type*) [Field E] [NumberField E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E]
    [Algebra ↥K E] [IsScalarTower k ↥K E] [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [Algebra ↥M E] [IsScalarTower k ↥M E]
    [IsScalarTower ↥K ↥M E]
    (c : ↥M ≃ₐ[↥K] ↥M) (g : E ≃ₐ[k] E)
    (hgK : ∀ x : ↥K, g (algebraMap ↥K E x) = algebraMap ↥K E x)
    (hgM : ∀ y : ↥M, g (algebraMap ↥M E y) = algebraMap ↥M E (c y))
    (P : NK.Chebotarev.PrimeIdeal E) (𝔭 : NK.Chebotarev.PrimeIdeal k)
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal)
    (hf : (P.under (NumberField.RingOfIntegers ↥K)).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) = 1)
    (hFrob : NK.Chebotarev.IsFrobAt P g) :
    NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥M)
      (P.under (NumberField.RingOfIntegers ↥K)) c := by
  classical
  -- (1) the `↥K`-algebra automorphism `ρ` of `E` underlying `g`
  let ρ : E ≃ₐ[↥K] E := { g with commutes' := hgK }
  -- (2) the two `galRestrict`s agree (they only see the underlying function)
  have hgal : ∀ x : NumberField.RingOfIntegers E,
      ((galRestrict (NumberField.RingOfIntegers ↥K) ↥K E (NumberField.RingOfIntegers E)) ρ) x =
        ((galRestrict (NumberField.RingOfIntegers k) k E (NumberField.RingOfIntegers E)) g) x := by
    intro x
    refine IsIntegralClosure.algebraMap_injective (NumberField.RingOfIntegers E)
      (NumberField.RingOfIntegers k) E ?_
    rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
    rfl
  -- (3) the two moduli agree, because the residue degree of the `↥K`-prime below `P` is one
  have hcard : Nat.card (NumberField.RingOfIntegers ↥K ⧸
      (P.under (NumberField.RingOfIntegers ↥K)).asIdeal) =
      Nat.card (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) := by
    have hlies : (P.under (NumberField.RingOfIntegers ↥K)).asIdeal.LiesOver 𝔭.asIdeal := by
      refine Ideal.LiesOver.mk ?_
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under, ← hP.over]
    have h := NK.CFTLib.Arl.cardQuot_pow_inertiaDeg_eq (K := k) (L := ↥K) hlies
    rw [hf, pow_one] at h
    exact h.symm
  -- (4) `g` is a Frobenius element at `P` also for the base field `↥K`
  have hFrobρ : NK.Chebotarev.IsFrobAt P ρ := by
    rw [NK.Chebotarev.isFrobAt_def] at hFrob ⊢
    rw [← hP.over] at hFrob
    intro x
    rw [hgal x, ← IsDedekindDomain.HeightOneSpectrum.under_asIdeal
      (NumberField.RingOfIntegers ↥K) P, hcard]
    exact hFrob x
  -- (5) descend to the normal subfield `↥M`
  have hres :=
    NK.Chebotarev.IsFrobAtRestrictNormalHomType (K := ↥K) (E := ↥M) (M := E) P ρ hFrobρ
  -- (6) the restriction of `ρ` to `↥M` is `c`
  have hρc : (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := E) ↥M) ρ = c := by
    refine AlgEquiv.ext (fun y => ?_)
    refine RingHom.injective (algebraMap ↥M E) ?_
    rw [show ((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := E) ↥M) ρ) = ρ.restrictNormal ↥M from
      rfl, AlgEquiv.restrictNormal_commutes]
    exact hgM y
  -- (7) conclude
  refine ⟨P.under (NumberField.RingOfIntegers ↥M), ?_, ?_⟩
  · refine Ideal.LiesOver.mk ?_
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal (NumberField.RingOfIntegers ↥M) P,
      IsDedekindDomain.HeightOneSpectrum.under_asIdeal (NumberField.RingOfIntegers ↥K) P,
      Ideal.under_under]
  · rwa [hρc] at hres

/-! ## Čebotarev for an arbitrary finite Galois level over `k` -/

/-- **Čebotarev with a finite set of primes avoided, for an arbitrary finite Galois extension.**

This is `Work.SSGRoute.exists_isFrobAtPrime_notMem_density` with the finite level given as an
arbitrary finite Galois `k`-algebra `E` rather than as an intermediate field of `Ω` (the density
statement `NK.ChebotarevGeneral.ChebotarevDensity` is stated for bare types, so the proof is the
same). -/
theorem exists_isFrobAtPrime_notMem_of_isGalois {k E : Type} [Field k] [NumberField k]
    [Field E] [NumberField E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E]
    (Bad : Set (NK.Chebotarev.PrimeIdeal k)) (hBad : Bad.Finite) (g : E ≃ₐ[k] E) :
    ∃ p : NK.Chebotarev.PrimeIdeal k, p ∉ Bad ∧
      NK.Chebotarev.IsFrobAtPrime (K := k) (L := E) p g := by
  classical
  have hdens : NumberField.Set.HasDirichletDensity
      (NK.ChebotarevGeneral.frobSet (K := k) (N := E) g)
      (NK.ChebotarevGeneral.frobDensity (K := k) (N := E) g) :=
    Work.SSGRoute.chebotarev_density_general k E g
  haveI : Nonempty ↥(Subgroup.centralizer ({g} : Set (E ≃ₐ[k] E))) :=
    ⟨1, Subgroup.one_mem _⟩
  have hpos : 0 < NK.ChebotarevGeneral.frobDensity (K := k) (N := E) g := by
    rw [NK.ChebotarevGeneral.frobDensity]
    refine one_div_pos.mpr ?_
    exact_mod_cast Nat.card_pos
  by_contra hcon
  push_neg at hcon
  have hsub : NK.ChebotarevGeneral.frobSet (K := k) (N := E) g ⊆ Bad := by
    intro p hp
    by_contra hpBad
    exact hcon p hpBad hp
  have hzn : NumberField.Set.HasDirichletDensity
      (NK.ChebotarevGeneral.frobSet (K := k) (N := E) g) 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_subset
      (Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite hBad) hsub
  rw [NumberField.Set.HasDirichletDensity] at hdens hzn
  exact absurd (tendsto_nhds_unique hdens hzn) hpos.ne'

/-! **The escape prime with the split condition.**

For a finite Galois extension `K/k` of number fields inside `Ω`, a finite set `T` of finite places
of `Ω` (all of them above primes in `T'`) and any class `x` of the idèle class group of `K`, there
is a prime `𝔮 ∉ T'` of `K` whose class satisfies `[𝔮] · x ∈ U = gesU K p T'` and which is the
prime of `K` below a finite place `Q` of `Ω` that is completely split in `K` over `k` and is not
`K`-conjugate to any element of `T`.

Route.  Let `M` be the class field of `U` inside `Ω` (`N_{M/K} C_M = U`, `M/K` finite abelian, hence
`M/k` finite), and let `M̃` be the normal closure of `M` over `k` (so `M̃/k` is finite Galois and
`M̃ ⊇ K`).  Let `c ∈ Gal(M/K) ≅ C_K/U` be the element corresponding to `x⁻¹` (idèlic Artin map with
Frobenius normalisation).  By Galois theory there is `τ : Ω ≃ₐ[k] Ω` with `τ(M) = M`, `τ|_M = c` and
`τ|_K = 1` (any `σ ∈ Gal(M/k)` extends to `M̃/k`, and `c|_K = 1`).  Apply
`Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split` with `L := M̃`, `N := K` and this `τ`: it
produces a finite place `B` avoiding a prescribed finite set, unramified in `M̃`, completely split in
`K` over `k`, together with `σ ∈ decomp k B` with `σ|_{M̃} = τ|_{M̃}`.  Since `K ⊆ M ⊆ M̃`, the
element `σ` lies in `Gal(Ω/K)` and `σ|_M = c`, so the `K`-prime `𝔮` below `B` has Frobenius `c` in
the abelian extension `M/K`, i.e. its idèle class lies in the coset `x⁻¹U`; take `Q := B`.  The
dictionary "the idèlic Artin map sends the class of a prime to its Frobenius element" is the Frobenius
normalisation of `NK.CFTLib.Existence.exists_ideleArtinMap_of_arl` /
`NK.CFTLib.Existence.exists_artinIso_of_ideleArtin` (as used in
`Submission/Work/SSGRoute/step4_y_escape_v2/RayClass.lean`), and the inside-`Ω` class field is
obtained from the abstract existence result as in
`Submission/Work/SSGRoute/CycLevel/levelData_of_abstract_level.lean`; the relation between the
decomposition group of a place of `Ω` and the Frobenius in `Gal(M/K)` is
`Submission/Work/SSGRoute/exists_mem_closure_decomp_mul_mem_fixingSubgroup.lean`
(`decomp_map_le_stabilizer_of_comap_eq`, `stabilizer_le_decomp_map_of_comap_eq`,
`exists_primeIdeal_comap_eq`).  This is the `(L₁, L₂) = (K, K)` case of the design's step 5:
the orthogonality ("the Artin symbol acts trivially on `M ∩ (L₁ ⊔ L₂)`") is automatic because
`L₁ ⊔ L₂ = K ⊆ M`.  The hypothesis `hc : NK.Reconstruct.ChebotarevDensityInput k Ω` of
`chebotarev_frobenius_split` is derivable (`NK.Reconstruct.chebotarevDensityInput_of_artinReciprocity`
plus `NK.CFTLib.artinReciprocityIdeal_proved`); `Work.SSGRoute.ssg8Chebotarev.exists_isFrobAtPrime_notMem_density`
is unconditional if preferred. -/
theorem gesEscapePrimeSplit (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (x : NK.GlobalCFT.IdeleClassGroup ↥K) :
    ∃ (Q : ValuationSubring Ω) (𝔮 : NK.Chebotarev.PrimeIdeal ↥K),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k K Q ∧ 𝔮 ∉ T' ∧
      Q.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮) * x ∈
        Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K p T' := by
  classical
  -- ## Step 1: the subgroup `U`
  have hUopen : IsOpen ((gesU ↥K p T') : Set (IdeleClassGroup ↥K)) :=
    Work.SSGRoute.isOpen_gesU (K := ↥K) (p := p) (Fact.out) T'
  have hUfin : (gesU ↥K p T').FiniteIndex := Work.SSGRoute.finiteIndex_gesU ↥K p T'
  -- ## Step 2: the abelian class field of `U` inside `Ω`
  obtain ⟨M, hMfd, hMgal, hMnf, hMcomm, hMnorm⟩ :=
    exists_abelian_classField_inside K (gesU ↥K p T') hUfin hUopen
  haveI : FiniteDimensional ↥K M := hMfd
  haveI : IsGalois ↥K M := hMgal
  haveI : NumberField ↥M := hMnf
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hMcomm
  -- ## Step 3: the Artin isomorphism and its Frobenius values
  obtain ⟨BadM, Θ, hBadM_unr, hBadM_frob⟩ := exists_artinIso_frobAtPrime (K := ↥K) (L := ↥M)
  -- the class corresponding to `x` (its inverse is the Frobenius to be realised)
  let c : ↥M ≃ₐ[↥K] ↥M :=
    (Θ (QuotientGroup.mk' (Idele.normClassSubgroup ↥K ↥M) x))⁻¹
  -- ## Step 4: a finite Galois container containing `K` and `M`
  obtain ⟨E₀, hE₀fd, hE₀gal, hE₀nf, hKE₀, hME₀⟩ := exists_galois_container K M
  -- the `↥K`-algebra structure on `↥E₀` (given by the inclusion), and the `↥M`-one
  let iK : ↥K →+* ↥E₀ :=
    { toFun := fun y => ⟨(y : Ω), hKE₀ y.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  letI : Algebra ↥K ↥E₀ := iK.toAlgebra
  let iM : ↥M →+* ↥E₀ :=
    { toFun := fun y => ⟨(y : Ω), hME₀ y.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  letI : Algebra ↥M ↥E₀ := iM.toAlgebra
  haveI hSTKM : IsScalarTower k ↥K ↥E₀ :=
    IsScalarTower.of_algebraMap_eq (fun z => Subtype.ext rfl)
  haveI hSTMM : IsScalarTower k ↥M ↥E₀ :=
    IsScalarTower.of_algebraMap_eq (fun z => Subtype.ext rfl)
  haveI hSTKMM : IsScalarTower ↥K ↥M ↥E₀ :=
    IsScalarTower.of_algebraMap_eq (fun z => Subtype.ext rfl)
  haveI hE₀fdK : FiniteDimensional ↥K ↥E₀ :=
    Module.Finite.of_restrictScalars_finite k ↥K ↥E₀
  haveI hE₀galK : IsGalois ↥K ↥E₀ := IsGalois.tower_top_of_isGalois k ↥K ↥E₀
  haveI : NumberField ↥E₀ := hE₀nf
  -- ## Step 5: the prescribed Frobenius element of `Gal(E₀/k)`
  haveI : Normal k ↥E₀ := inferInstance
  let ck : ↥M ≃ₐ[k] ↥M := c.restrictScalars k
  let g : ↥E₀ ≃ₐ[k] ↥E₀ := ck.liftNormal ↥E₀
  have hgM : ∀ y : ↥M, g (algebraMap ↥M ↥E₀ y) = algebraMap ↥M ↥E₀ (c y) := by
    intro y
    rw [AlgEquiv.liftNormal_commutes]
    rfl
  have hgK : ∀ y : ↥K, g (algebraMap ↥K ↥E₀ y) = algebraMap ↥K ↥E₀ y := by
    intro y
    have hy : algebraMap ↥K ↥E₀ y = algebraMap ↥M ↥E₀ (algebraMap ↥K ↥M y) :=
      Subtype.ext rfl
    rw [hy, AlgEquiv.liftNormal_commutes]
    rw [show ck ((algebraMap ↥K ↥M) y) = (algebraMap ↥K ↥M) y from AlgEquiv.commutes c y]
  -- ## Step 6: the primes of `k` to be avoided
  set Bad : Set (NK.Chebotarev.PrimeIdeal k) :=
    {𝔭 | (∃ 𝔮 ∈ T', 𝔮.asIdeal.LiesOver 𝔭.asIdeal) ∨
      (∃ 𝔮 ∈ BadM, 𝔮.asIdeal.LiesOver 𝔭.asIdeal) ∨
      (∃ Q : NK.Chebotarev.PrimeIdeal ↥K, Q.asIdeal.LiesOver 𝔭.asIdeal ∧
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1)} with hBaddef
  have hBadfin : Bad.Finite := by
    rw [hBaddef]
    have h1 : ({𝔭 : NK.Chebotarev.PrimeIdeal k |
        ∃ 𝔮 ∈ T', 𝔮.asIdeal.LiesOver 𝔭.asIdeal} : Set _).Finite := by
      refine ((T'.image (fun 𝔮 : NK.Chebotarev.PrimeIdeal ↥K =>
        𝔮.under (NumberField.RingOfIntegers k))).finite_toSet).subset ?_
      rintro 𝔭 ⟨𝔮, h𝔮, hlies⟩
      exact Finset.mem_image.mpr ⟨𝔮, h𝔮, IsDedekindDomain.HeightOneSpectrum.ext (by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]; exact hlies.over.symm)⟩
    have h2 : ({𝔭 : NK.Chebotarev.PrimeIdeal k |
        ∃ 𝔮 ∈ BadM, 𝔮.asIdeal.LiesOver 𝔭.asIdeal} : Set _).Finite := by
      refine ((BadM.image (fun 𝔮 : NK.Chebotarev.PrimeIdeal ↥K =>
        𝔮.under (NumberField.RingOfIntegers k))).finite_toSet).subset ?_
      rintro 𝔭 ⟨𝔮, h𝔮, hlies⟩
      exact Finset.mem_image.mpr ⟨𝔮, h𝔮, IsDedekindDomain.HeightOneSpectrum.ext (by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]; exact hlies.over.symm)⟩
    have h3 : ({𝔭 : NK.Chebotarev.PrimeIdeal k |
        ∃ Q : NK.Chebotarev.PrimeIdeal ↥K, Q.asIdeal.LiesOver 𝔭.asIdeal ∧
          Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1} : Set _).Finite :=
      Work.SSGRoute.FrobBelow.finite_setOf_primeUnder_ramified (k := k) (Ω := Ω) K
    refine (h1.union (h2.union h3)).subset ?_
    rintro 𝔭 (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- ## Step 7: Čebotarev
  obtain ⟨𝔭, h𝔭Bad, hFrobPrime⟩ :=
    exists_isFrobAtPrime_notMem_of_isGalois (k := k) (E := ↥E₀) Bad hBadfin g
  obtain ⟨P, hPlies, hPFrob⟩ := hFrobPrime
  have h𝔭Bad1 : ¬ (∃ 𝔮 ∈ T', 𝔮.asIdeal.LiesOver 𝔭.asIdeal) := by
    intro h
    exact h𝔭Bad (by rw [hBaddef]; exact Or.inl h)
  have h𝔭Bad2 : ¬ (∃ 𝔮 ∈ BadM, 𝔮.asIdeal.LiesOver 𝔭.asIdeal) := by
    intro h
    exact h𝔭Bad (by rw [hBaddef]; exact Or.inr (Or.inl h))
  have h𝔭Bad3 : ∀ Q : NK.Chebotarev.PrimeIdeal ↥K, Q.asIdeal.LiesOver 𝔭.asIdeal →
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    intro Q hQ
    by_contra hne
    exact h𝔭Bad (by rw [hBaddef]; exact Or.inr (Or.inr ⟨Q, hQ, hne⟩))
  -- the `↥K`-prime below `P`
  set 𝔮 : NK.Chebotarev.PrimeIdeal ↥K := P.under (NumberField.RingOfIntegers ↥K) with h𝔮def
  have h𝔮lies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    rw [h𝔮def, IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    exact hPlies.over
  have h𝔮T' : 𝔮 ∉ T' := fun hmem => h𝔭Bad1 ⟨𝔮, hmem, h𝔮lies⟩
  have h𝔮BadM : 𝔮 ∉ BadM := fun hmem => h𝔭Bad2 ⟨𝔮, hmem, h𝔮lies⟩
  have h𝔮unr : 𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := h𝔭Bad3 𝔮 h𝔮lies
  -- ## Step 8: the Frobenius of the `↥K`-prime below `P` is trivial, so its residue degree is one
  have hresK : NK.Chebotarev.IsFrobAt (P.under (NumberField.RingOfIntegers ↥K))
      (AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E₀) ↥K g) :=
    NK.Chebotarev.IsFrobAtRestrictNormalHomType (K := k) (E := ↥K) (M := ↥E₀) P g hPFrob
  have hresK1 : NK.Chebotarev.IsFrobAt (P.under (NumberField.RingOfIntegers ↥K))
      (1 : ↥K ≃ₐ[k] ↥K) := by
    have h1 : AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E₀) ↥K g = 1 := by
      refine AlgEquiv.ext (fun y => ?_)
      refine RingHom.injective (algebraMap ↥K ↥E₀) ?_
      rw [show AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E₀) ↥K g = g.restrictNormal ↥K from
        rfl, AlgEquiv.restrictNormal_commutes]
      simp only [AlgEquiv.one_apply]
      exact hgK y
    rwa [h1] at hresK
  have hf : (P.under (NumberField.RingOfIntegers ↥K)).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) = 1 :=
    (NK.Chebotarev.IsFrobAt_eq_one_iff_inertiaDeg_eq_one h𝔮lies h𝔮unr).mp hresK1
  -- ## Step 9: the Frobenius transfer
  have hFrob𝔮 : NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥M) 𝔮 c :=
    isFrobAtPrime_of_isFrobAt_inertiaDeg_eq_one (k := k) (Ω := Ω) K M ↥E₀ c g hgK hgM
      P 𝔭 hPlies hf hPFrob
  -- ## Step 10: identify `frobAtPrime 𝔮` with `c`
  have hunrM : ∀ Q : NK.Chebotarev.PrimeIdeal ↥M, Q.asIdeal.LiesOver 𝔮.asIdeal →
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K) = 1 :=
    fun Q hQ => hBadM_unr 𝔮 h𝔮BadM Q hQ
  have hfrob : NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮 = c :=
    (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq (fun a b => mul_comm' a b) 𝔮 hunrM c).mp
      hFrob𝔮
  -- ## Step 11: the idèle class condition
  have hclass : IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮) * x ∈ gesU ↥K p T' := by
    have h1 : Θ (QuotientGroup.mk' (Idele.normClassSubgroup ↥K ↥M)
        (IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮))) =
        (Θ (QuotientGroup.mk' (Idele.normClassSubgroup ↥K ↥M) x))⁻¹ := by
      rw [hBadM_frob 𝔮 h𝔮BadM, hfrob]
    have h2 : (QuotientGroup.mk' (Idele.normClassSubgroup ↥K ↥M)
        (IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮))) *
        (QuotientGroup.mk' (Idele.normClassSubgroup ↥K ↥M) x) = 1 := by
      apply Θ.injective
      rw [map_mul, h1, map_one, inv_mul_cancel]
    have h3 : IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮) * x ∈
        Idele.normClassSubgroup ↥K ↥M := by
      have h4 : QuotientGroup.mk' (Idele.normClassSubgroup ↥K ↥M)
          (IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮) * x) = 1 := by
        rw [map_mul]
        exact h2
      exact (QuotientGroup.eq_one_iff _).mp (by simpa using h4)
    rwa [hMnorm] at h3
  -- ## Step 12: the place `Q`
  haveI : Algebra.IsAlgebraic ↥K Ω := Algebra.IsAlgebraic.tower_top (K := k) ↥K
  obtain ⟨Q, hQcomap⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
      (K := ↥K) (K' := Ω) 𝔮
  have hQfin : SSGRoute.IsFinPlace k Q :=
    Work.SSGRoute.FrobBelow.isFinPlace_of_comap_valuationSubringAtPrime (k := k) K Q 𝔮 hQcomap
  -- `Q` is completely split in `K` over `k`: the decomposition group of its `k`-prime in `K/k`
  -- is the decomposition group of `𝔮`, which is trivial because the Frobenius at `𝔮` is trivial.
  have hQsplit : SSGRoute.IsSplitIn k K Q := by
    haveI : IsGalois k ↥K := inferInstance
    have hbridge := Work.SSGRoute.FrobBelow.map_res_decomp_eq_stabilizer_valuationRing
      (k := k) (Ω := Ω) K Q hQfin 𝔮 hQcomap
    have hdec := NK.ChebotarevGeneral.decompositionSubgroup_eq_zpowers_of_isFrobAt
      (K := k) (N := ↥K) 𝔮 (1 : ↥K ≃ₐ[k] ↥K) h𝔮unr hresK1
    have hstab : MulAction.stabilizer (↥K ≃ₐ[k] ↥K)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro g hg
      rw [MulAction.mem_stabilizer_iff] at hg
      rw [show (⊥ : Subgroup (↥K ≃ₐ[k] ↥K)) = Subgroup.zpowers (1 : ↥K ≃ₐ[k] ↥K)
        from Subgroup.zpowers_one_eq_bot.symm, ← hdec]
      exact (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
        𝔮 g).mp hg
    intro σ hσ
    have hmem : SSGRoute.res k K σ ∈ (SSGRoute.decomp k Q).map (SSGRoute.res k K) :=
      Subgroup.mem_map_of_mem _ hσ
    rw [hbridge, hstab] at hmem
    rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker]
    simpa using hmem
  -- the avoidance clause: `K`-conjugates lie over the same `↥K`-prime
  have hQnotT : ∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q := by
    intro A hA hconj
    obtain ⟨τ, hτ, hτQ⟩ := hconj
    obtain ⟨𝔭A, h𝔭AT', hAcomap⟩ := hTbelow A hA
    have hcomap : (τ • A).comap (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
      let τK : Ω ≃ₐ[↥K] Ω := (IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩
      have hsmul : τK • A = τ • A := by
        apply ValuationSubring.ext
        intro y
        rw [ValuationSubring.mem_smul_pointwise_iff_exists,
          ValuationSubring.mem_smul_pointwise_iff_exists]
        constructor
        · rintro ⟨s, hs, hys⟩
          exact ⟨s, hs, by rw [← hys, AlgEquiv.smul_def, AlgEquiv.smul_def,
            show (⇑τK) = ⇑τ from rfl]⟩
        · rintro ⟨s, hs, hys⟩
          exact ⟨s, hs, by rw [← hys, AlgEquiv.smul_def, AlgEquiv.smul_def,
            show (⇑τK) = ⇑τ from rfl]⟩
      have hcom :=
        Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap (K := ↥K) (K' := Ω) A τK
      rwa [hsmul] at hcom
    have : 𝔮 = 𝔭A := by
      apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
      rw [← hQcomap, ← hτQ, hcomap, hAcomap]
    exact h𝔭Bad1 ⟨𝔮, by rw [this]; exact h𝔭AT', h𝔮lies⟩
  exact ⟨Q, 𝔮, hQfin, hQsplit, h𝔮T', hQcomap, hQnotT, hclass⟩

end Work.SSGRoute.GrunwaldEscapeCore
