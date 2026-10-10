import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.EscapeCoreLib.escapePrimeFrobAtPrime
import Submission.Work.SSGRoute.EscapeCoreLib.memGesUOfIsFrobAtPrime
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesEscapePrimeSplit
import Submission.Work.SSGRoute.n4_halpha_fix

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute
open scoped NumberField

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The escape prime from the orthogonality.**  A fresh, compilable copy of
`Work.SSGRoute.step4_y_escape_v2.escapePrime_of_orthogonality` (`Submission/Work/SSGRoute/step4_y_escape_v2/EscapePrimeOrth.lean`,
statement at lines 37-57), kept in this lane so that consumers do not have to import a module that
currently does not elaborate.

**Prover's note (read this first).**  That file already contains a *complete* 26 KB proof of
exactly this statement; it is not a `sorry`, it simply fails to compile (12 errors at lines
176-348: two `rewrite` "pattern not found" at 176/185/255, one `instance` failure at 242, an
`assumption` failure at 289, two `Unknown constant Subsemiring.coe_inclusion` at 297/303, an
application type mismatch at 307 involving `isFrobAtPrime_of_isFrobAt_inertiaDeg_eq_one`
(the conclusion there is about `P.under (𝓞 ↥K)` while `hf` is stated for `𝔮 = P.under ...`; use
`h𝔮def`/`show`), a `No goals to be solved` at 317 and a `rfl` type mismatch at 348).
**The fastest route is to COPY that proof into this file and repair those errors** (reading a
colleague's file is fine; editing it is not).  The already-proved ingredients it uses are
`GrunwaldEscapeCore.gesEscapePrimeSplit`, `GrunwaldEscapeCore.exists_artinIso_frobAtPrime`,
`GrunwaldEscapeCore.isFrobAtPrime_of_isFrobAt_inertiaDeg_eq_one`,
`GrunwaldEscapeCore.exists_mem_fixingSubgroup_smul_eq_of_comap_eq`,
`EscapeCoreLib.galoisLevel_and_tau_of_orthogonality`,
`EscapeCoreLib.mem_of_forall_linearMap_eq_zero`,
`Work.SSGRoute.ssg8Chebotarev.exists_isFrobAtPrime_notMem_density`,
`Work.SSGRoute.exists_split_place_avoiding`, and the CFT step
`Work.SSGRoute.N4Escape.restrictNormalHom_artinMap_kills_normClassSubgroup_of_modulus`
(`Submission/Work/SSGRoute/n4_halpha_fix.lean`) that turns `horth` into `hαfix`.
The `Subsemiring.coe_inclusion` occurrences should simply be deleted from the `simp only` lists
(the underlying function of `Subsemiring.inclusion`'s `toAlgebra` is `rfl`-equal to the coercion). -/
theorem escapePrimeKfresh
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [IsMulCommutative (↥M ≃ₐ[↥K] ↥M)]
    (U' : Subgroup (NK.GlobalCFT.IdeleClassGroup ↥K))
    (hMnorm : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M = U')
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N]
    (N' : IntermediateField ↥K Ω) [FiniteDimensional ↥K N'] [IsGalois ↥K N'] [NumberField ↥N']
    (hKN : K ≤ N) (hNN' : (N' : Set Ω) = (N : Set Ω))
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (x : NK.GlobalCFT.IdeleClassGroup ↥K)
    (horth : x ∈ U' ⊔ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N') :
    ∃ (Q : ValuationSubring Ω) (𝔮 : NK.Chebotarev.PrimeIdeal ↥K),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k N Q ∧ 𝔮 ∉ T' ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ A ∈ T, ¬ SSGRoute.IsConjPlace k A Q) ∧
      Q.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
      NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮) * x ∈ U' := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Normal k Ω := IsAlgClosure.normal k Ω
  haveI hnumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  have hcomm : ∀ a b : (↥M ≃ₐ[↥K] ↥M), a * b = b * a := fun a b => mul_comm' a b
  -- ## 1. the idèlic Artin map of `M/↥K` with its modulus and its iso `Θ`
  obtain ⟨m, hm, hramIn, hprinc⟩ := NK.CFTLib.artinReciprocityIdeal_proved ↥K ↥M hcomm
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust ↥K m hm
  obtain ⟨art, hagree, hprincipal, hfrob, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := ↥K) (L := ↥M) hcomm m hm hramIn hprinc
      U hU hadj
  have hnorm_art : ∀ y : NK.GlobalCFT.Idele ↥M,
      art (NK.GlobalCFT.Idele.normIdeleHom ↥K ↥M y) = 1 := by
    intro y
    rw [hagree (NK.GlobalCFT.Idele.normIdeleHom ↥K ↥M y)]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := ↥K) (L := ↥M) hcomm m hm hramIn
      hprinc U hU hadj (NK.NUV2.ARL.normAdjustment (K := ↥K) (L := ↥M) m hm hramIn U hU) y
  have hPle : NK.GlobalCFT.Idele.principalSubgroup ↥K ≤ art.ker := by
    intro z hz
    obtain ⟨a, rfl⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hz
    exact MonoidHom.mem_ker.mpr (hprincipal a)
  obtain ⟨Θ, hΘ⟩ := NK.CFTLib.Existence.exists_artinIso_of_ideleArtin
    NK.CFTLib.fundamentalClassElement art hPle hnorm_art hsurj
  -- ## 2. the bad primes of the modulus, and the Frobenius normalisation of `Θ`
  have hm0 : (m : 𝓞 ↥K) ≠ 0 := by exact_mod_cast hm.ne'
  have hspan0 : Ideal.span {(m : 𝓞 ↥K)} ≠ 0 := by
    rw [Ne]
    intro h
    exact hm0 (Ideal.span_singleton_eq_bot.mp h)
  have hfin : ({𝔮 : NK.Chebotarev.PrimeIdeal ↥K | (m : 𝓞 ↥K) ∈ 𝔮.asIdeal} : Set _).Finite := by
    refine (Ideal.finite_factors (R := 𝓞 ↥K) (I := Ideal.span {(m : 𝓞 ↥K)}) hspan0).subset ?_
    intro 𝔮 h𝔮
    show 𝔮.asIdeal ∣ Ideal.span {(m : 𝓞 ↥K)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h𝔮
  let BadM : Finset (NK.Chebotarev.PrimeIdeal ↥K) := hfin.toFinset
  have hBadMmem : ∀ 𝔮, 𝔮 ∈ BadM ↔ (m : 𝓞 ↥K) ∈ 𝔮.asIdeal := fun 𝔮 =>
    Set.Finite.mem_toFinset hfin
  have hΘfrob : ∀ 𝔮 ∉ BadM,
      Θ (QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M)
        (NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮))) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮 := by
    intro 𝔮 h𝔮
    rw [hΘ (NK.HeckeL.ideleOfPrime ↥K 𝔮),
      hfrob 𝔮 (fun hcon => h𝔮 ((hBadMmem 𝔮).mpr hcon))]
  have hunrM : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, (m : 𝓞 ↥K) ∉ 𝔮.asIdeal →
      ∀ Q : NK.Chebotarev.PrimeIdeal ↥M, Q.asIdeal.LiesOver 𝔮.asIdeal →
        Q.asIdeal.ramificationIdx (𝓞 ↥K) = 1 := by
    intro 𝔮 h𝔮 Q hQ
    letI hMSA : MulSemiringAction (↥M ≃ₐ[↥K] ↥M) (𝓞 ↥M) :=
      IsIntegralClosure.MulSemiringAction (𝓞 ↥K) ↥K ↥M (𝓞 ↥M)
    haveI hGG : IsGaloisGroup (↥M ≃ₐ[↥K] ↥M) (𝓞 ↥K) (𝓞 ↥M) :=
      IsGaloisGroup.of_isFractionRing (↥M ≃ₐ[↥K] ↥M) (𝓞 ↥K) (𝓞 ↥M) ↥K ↥M
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 ↥K) (B := 𝓞 ↥M) 𝔮.asIdeal
      Q.asIdeal (↥M ≃ₐ[↥K] ↥M)]
    exact hramIn 𝔮 h𝔮
  -- ## 3. the class `c = Θ(x)⁻¹` and the orthogonality `hαfix`
  let c : ↥M ≃ₐ[↥K] ↥M :=
    (Θ (QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M) x))⁻¹
  -- the intermediate field `M ⊓ N'` of `↥M`
  let E' : IntermediateField ↥K ↥M := N'.comap M.val
  haveI hfdE : FiniteDimensional ↥K ↥E' :=
    FiniteDimensional.of_injective (IntermediateField.val E').toLinearMap
      (fun a b h => Subtype.ext h)
  haveI hnfE : NumberField ↥E' := NumberField.of_module_finite ↥K ↥E'
  haveI hnormFix : E'.fixingSubgroup.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    have h1 : g * n * g⁻¹ = n := by
      rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]
    rwa [h1]
  haveI hgalE : IsGalois ↥K ↥E' := by
    haveI hff : IsGalois ↥K ↥(IntermediateField.fixedField E'.fixingSubgroup) :=
      IsGalois.of_fixedField_normal_subgroup (K := ↥K) (L := ↥M) E'.fixingSubgroup
    have heq : IntermediateField.fixedField E'.fixingSubgroup = E' :=
      IsGalois.fixedField_fixingSubgroup (F := ↥K) (E := ↥M) E'
    exact heq ▸ hff
  haveI hnormalE : Normal ↥K ↥E' := IsGalois.to_normal
  -- the embedding `↥E' → ↥N'` along `Ω`, and the tower of norm subgroups
  let emb : ↥E' →+* ↥N' :=
    { toFun := fun y => ⟨(y : Ω), y.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  letI : Algebra ↥E' ↥N' := emb.toAlgebra
  haveI htowE'N' : IsScalarTower ↥K ↥E' ↥N' :=
    IsScalarTower.of_algebraMap_eq (fun z => Subtype.ext (by
      show ((algebraMap ↥K ↥E' z : ↥E') : Ω) = ((algebraMap ↥K ↥N' z : ↥N') : Ω)
      rw [show ((algebraMap ↥K ↥E' z : ↥E') : Ω) = algebraMap ↥K Ω z from
            (IsScalarTower.algebraMap_apply ↥K ↥M Ω z).symm,
          show ((algebraMap ↥K ↥N' z : ↥N') : Ω) = algebraMap ↥K Ω z from
            (IsScalarTower.algebraMap_apply ↥K ↥N' Ω z).symm]))
  haveI hfdE'N' : FiniteDimensional ↥E' ↥N' :=
    Module.Finite.of_restrictScalars_finite ↥K ↥E' ↥N'
  -- the orthogonality through the CFT step
  obtain ⟨u, hu, n, hn, hun⟩ := Subgroup.mem_sup.mp horth
  have hu' : u ∈ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M := hMnorm.symm ▸ hu
  have hnE' : n ∈ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥E' :=
    NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower (K := ↥K) (L := ↥E') (M := ↥N') hn
  obtain ⟨nIdele, hnIdele⟩ := NK.GlobalCFT.IdeleClassGroup.mk_surjective ↥K n
  have hres :=
    Work.SSGRoute.N4Escape.restrictNormalHom_artinMap_kills_normClassSubgroup_of_modulus
      (K := ↥K) (L := ↥M) m hm hramIn hprinc E' art hprincipal hnorm_art hfrob n hnE' nIdele
      hnIdele
  -- `Θ(x) = art nIdele`
  have hΘx : Θ (QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M) x) =
      art nIdele := by
    have hu1 : QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M) u = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hu'
    have hxn : QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M) x =
        QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M) n := by
      rw [← hun, map_mul, hu1, one_mul]
    rw [hxn, ← hnIdele]
    exact hΘ nIdele
  have hcfix : c ∈ E'.fixingSubgroup := by
    have hmemKer : art nIdele ∈ E'.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker E', MonoidHom.mem_ker]
      exact hres
    show (Θ (QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M) x))⁻¹ ∈
      E'.fixingSubgroup
    rw [hΘx]
    exact Subgroup.inv_mem _ hmemKer
  have hαfix : ∀ z : ↥M, ((z : Ω) ∈ N) → ((c z : ↥M) : Ω) = (z : Ω) := by
    intro z hz
    have hzN' : (z : Ω) ∈ N' := hNN'.ge hz
    have hzE : z ∈ E' := hzN'
    have hcz : c z = z := (IntermediateField.mem_fixingSubgroup_iff E' c).mp hcfix z hzE
    rw [hcz]
  -- ## 4. the finite Galois container and the `k`-automorphism `τ` fixing `N`
  obtain ⟨L, hLd, hLg, τ, hKL, hMLk, hNL, hτN, hτM⟩ :=
    Work.SSGRoute.EscapeCoreLib.galoisLevel_and_tau_of_orthogonality K M N hKN c hαfix
  haveI : FiniteDimensional k L := hLd
  haveI : IsGalois k L := hLg
  haveI hnumL : NumberField ↥L := NumberField.of_module_finite k ↥L
  -- ## 5. Čebotarev in `L/k` (unconditional), with the prime of `𝓞 L` exposed
  set g : ↥L ≃ₐ[k] ↥L := SSGRoute.res k L τ with hg
  set Bad : Set (NK.Chebotarev.PrimeIdeal k) :=
    {𝔭 | ∃ 𝔮 ∈ T', 𝔮.asIdeal.LiesOver 𝔭.asIdeal} ∪
    {𝔭 | ∃ 𝔮 ∈ BadM, 𝔮.asIdeal.LiesOver 𝔭.asIdeal} ∪
    {𝔭 | ∃ C : NK.Chebotarev.PrimeIdeal ↥K, C.asIdeal.LiesOver 𝔭.asIdeal ∧
      C.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1} ∪
    {𝔭 | ∃ C : NK.Chebotarev.PrimeIdeal ↥N, C.asIdeal.LiesOver 𝔭.asIdeal ∧
      C.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1} with hBaddef
  have hBadfin : Bad.Finite := by
    rw [hBaddef]
    have h1 : ({𝔭 : NK.Chebotarev.PrimeIdeal k |
        ∃ 𝔮 ∈ T', 𝔮.asIdeal.LiesOver 𝔭.asIdeal} : Set _).Finite := by
      refine ((T'.image (fun 𝔮 : NK.Chebotarev.PrimeIdeal ↥K =>
        𝔮.under (NumberField.RingOfIntegers k))).finite_toSet).subset ?_
      rintro 𝔭 ⟨𝔮, h𝔮, hlies⟩
      exact Finset.mem_image.mpr ⟨𝔮, h𝔮, IsDedekindDomain.HeightOneSpectrum.ext (by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
        exact hlies.over.symm)⟩
    have h2 : ({𝔭 : NK.Chebotarev.PrimeIdeal k |
        ∃ 𝔮 ∈ BadM, 𝔮.asIdeal.LiesOver 𝔭.asIdeal} : Set _).Finite := by
      refine ((BadM.image (fun 𝔮 : NK.Chebotarev.PrimeIdeal ↥K =>
        𝔮.under (NumberField.RingOfIntegers k))).finite_toSet).subset ?_
      rintro 𝔭 ⟨𝔮, h𝔮, hlies⟩
      exact Finset.mem_image.mpr ⟨𝔮, h𝔮, IsDedekindDomain.HeightOneSpectrum.ext (by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
        exact hlies.over.symm)⟩
    have h3 : ({𝔭 : NK.Chebotarev.PrimeIdeal k |
        ∃ C : NK.Chebotarev.PrimeIdeal ↥K, C.asIdeal.LiesOver 𝔭.asIdeal ∧
          C.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1} : Set _).Finite :=
      Work.SSGRoute.FrobBelow.finite_setOf_primeUnder_ramified (k := k) (Ω := Ω) K
    have h4 : ({𝔭 : NK.Chebotarev.PrimeIdeal k |
        ∃ C : NK.Chebotarev.PrimeIdeal ↥N, C.asIdeal.LiesOver 𝔭.asIdeal ∧
          C.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1} : Set _).Finite :=
      Work.SSGRoute.FrobBelow.finite_setOf_primeUnder_ramified (k := k) (Ω := Ω) N
    exact ((h1.union h2).union h3).union h4
  obtain ⟨𝔭, h𝔭Bad, hFrobPrime⟩ :=
    Work.SSGRoute.exists_isFrobAtPrime_notMem_density Bad hBadfin L g
  obtain ⟨P, hPlies, hPFrob⟩ := hFrobPrime
  have h𝔭Bad1 : ¬ (∃ 𝔮 ∈ T', 𝔮.asIdeal.LiesOver 𝔭.asIdeal) := by
    intro h
    exact h𝔭Bad (by rw [hBaddef]; exact Or.inl (Or.inl (Or.inl h)))
  have h𝔭Bad2 : ¬ (∃ 𝔮 ∈ BadM, 𝔮.asIdeal.LiesOver 𝔭.asIdeal) := by
    intro h
    exact h𝔭Bad (by rw [hBaddef]; exact Or.inl (Or.inl (Or.inr h)))
  have h𝔭Bad3 : ∀ C : NK.Chebotarev.PrimeIdeal ↥K, C.asIdeal.LiesOver 𝔭.asIdeal →
      C.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    intro C hC
    by_contra hne
    exact h𝔭Bad (by rw [hBaddef]; exact Or.inl (Or.inr ⟨C, hC, hne⟩))
  have h𝔭Bad4 : ∀ C : NK.Chebotarev.PrimeIdeal ↥N, C.asIdeal.LiesOver 𝔭.asIdeal →
      C.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    intro C hC
    by_contra hne
    exact h𝔭Bad (by rw [hBaddef]; exact Or.inr ⟨C, hC, hne⟩)
  -- ## 5'. the `↥K`- and `↥M`-algebra structures on `↥L`, needed already for `P.under`
  have hKLset : (K : Set Ω) ⊆ (L : Set Ω) := hKL
  have hNLset : (N : Set Ω) ⊆ (L : Set Ω) := hNL
  have hMk : (M.restrictScalars k : Set Ω) = (M : Set Ω) :=
    IntermediateField.coe_restrictScalars k (E := M)
  have hMLset : (M : Set Ω) ⊆ (L : Set Ω) := fun z hz => hMLk (hMk.ge hz)
  letI : Algebra ↥K ↥L := (Subsemiring.inclusion hKLset).toAlgebra
  haveI htowKLk : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htowKLΩ : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hfdKL : FiniteDimensional ↥K ↥L := Module.Finite.of_restrictScalars_finite k ↥K ↥L
  haveI hgalKL : IsGalois ↥K ↥L := IsGalois.tower_top_of_isGalois k ↥K ↥L
  letI : Algebra ↥M ↥L := (Subsemiring.inclusion hMLset).toAlgebra
  haveI htowMLΩ : IsScalarTower ↥M ↥L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htowkML : IsScalarTower k ↥M ↥L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htowKML : IsScalarTower ↥K ↥M ↥L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hfdML : FiniteDimensional ↥M ↥L := Module.Finite.of_restrictScalars_finite k ↥M ↥L
  -- ## 6. the `↥K`-prime below `P`
  set 𝔮 : NK.Chebotarev.PrimeIdeal ↥K := P.under (NumberField.RingOfIntegers ↥K) with h𝔮def
  have h𝔮lies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    rw [h𝔮def, IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    exact hPlies.over
  have h𝔮T' : 𝔮 ∉ T' := fun hmem => h𝔭Bad1 ⟨𝔮, hmem, h𝔮lies⟩
  have h𝔮BadM : 𝔮 ∉ BadM := fun hmem => h𝔭Bad2 ⟨𝔮, hmem, h𝔮lies⟩
  have h𝔮unr : 𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := h𝔭Bad3 𝔮 h𝔮lies
  -- the `↥K`-Frobenius at `P` is trivial, because `τ` fixes `N ⊇ K`
  have hτKfix : ∀ z : ↥K, τ (z : Ω) = (z : Ω) := by
    have hmemN : τ ∈ N.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker N]
      exact MonoidHom.mem_ker.mpr hτN
    have hmemK : τ ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff] at hmemN ⊢
      exact fun z hz => hmemN z (hKN hz)
    exact fun z => (IntermediateField.mem_fixingSubgroup_iff K τ).mp hmemK z z.2
  have hfrobK : NK.Chebotarev.IsFrobAt (K := k) (L := ↥K) 𝔮 (1 : ↥K ≃ₐ[k] ↥K) := by
    have h := NK.Chebotarev.IsFrobAtRestrictNormalHomType (K := k) (E := ↥K) (M := ↥L) P g
      hPFrob
    have hres : AlgEquiv.restrictNormalHom ↥K g = 1 := by
      refine AlgEquiv.ext (fun z => ?_)
      refine RingHom.injective (algebraMap ↥K ↥L) ?_
      rw [show AlgEquiv.restrictNormalHom ↥K g = g.restrictNormal ↥K from rfl,
        AlgEquiv.restrictNormal_commutes]
      simp only [AlgEquiv.one_apply]
      refine Subtype.ext ?_
      rw [hg]
      simp only [SSGRoute.res, AlgEquiv.restrictNormalHom_apply]
      exact hτKfix z
    rw [hres] at h
    rwa [h𝔮def]
  have hf : 𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 1 :=
    (NK.Chebotarev.IsFrobAt_eq_one_iff_inertiaDeg_eq_one h𝔮lies h𝔮unr).mp hfrobK
  -- ## 7. the Frobenius transfer: `c` is a Frobenius at `𝔮`
  have hgK : ∀ z : ↥K, g (algebraMap ↥K ↥L z) = algebraMap ↥K ↥L z := by
    intro z
    refine Subtype.ext ?_
    rw [hg]
    simp only [SSGRoute.res, AlgEquiv.restrictNormalHom_apply]
    exact hτKfix z
  have hgM : ∀ z : ↥M, g (algebraMap ↥M ↥L z) = algebraMap ↥M ↥L (c z) := by
    intro z
    refine Subtype.ext ?_
    rw [hg]
    simp only [SSGRoute.res, AlgEquiv.restrictNormalHom_apply]
    exact hτM z
  have hf' : (P.under (NumberField.RingOfIntegers ↥K)).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) = 1 := by
    rw [← h𝔮def]
    exact hf
  have hFrob𝔮 : NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥M) 𝔮 c := by
    rw [h𝔮def]
    exact Work.SSGRoute.GrunwaldEscapeCore.isFrobAtPrime_of_isFrobAt_inertiaDeg_eq_one
      (k := k) (Ω := Ω) K M ↥L c g hgK hgM P 𝔭 hPlies hf' hPFrob
  have hfrobEq : NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮 = c :=
    (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm 𝔮
      (fun Q hQ => hunrM 𝔮 (fun hcon => h𝔮BadM ((hBadMmem 𝔮).mpr hcon)) Q hQ) c).mp hFrob𝔮
  -- ## 8. the idèle class membership
  have hmem : NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮) * x ∈ U' := by
    have h1 : Θ (QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M)
        (NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮))) =
        (Θ (QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M) x))⁻¹ := by
      rw [hΘfrob 𝔮 h𝔮BadM, hfrobEq]
    have h2 : QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M)
        (NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮)) *
        QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M) x = 1 := by
      apply Θ.injective
      rw [map_mul, h1, map_one, inv_mul_cancel]
    have h3 : NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮) * x ∈
        NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M := by
      have h4 : QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M)
          (NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮) * x) = 1 := by
        rw [map_mul]
        exact h2
      exact (QuotientGroup.eq_one_iff _).mp (by simpa using h4)
    rwa [hMnorm] at h3
  -- ## 9. a place `Q` above `P`, and the split condition in `N`
  obtain ⟨Q, hQcomapL⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
      (K := ↥L) (K' := Ω) P
  have hliesK : P.asIdeal.LiesOver 𝔮.asIdeal := by
    rw [h𝔮def, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    exact ⟨rfl⟩
  have hQcomapK : Q.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 := by
    have h1 : Q.comap (algebraMap ↥K Ω) =
        (Q.comap (algebraMap ↥L Ω)).comap (algebraMap ↥K ↥L) :=
      (ValuationSubring.comap_comap Q (algebraMap ↥L Ω) (algebraMap ↥K ↥L)).symm
    rw [h1, hQcomapL,
      Commons.RingTheory.Valuation.comap_valuationSubringAtPrime 𝔮 P hliesK]
  have hQfin : SSGRoute.IsFinPlace k Q :=
    Work.SSGRoute.FrobBelow.isFinPlace_of_comap_valuationSubringAtPrime (k := k) K Q 𝔮 hQcomapK
  letI : Algebra ↥N ↥L := (Subsemiring.inclusion hNLset).toAlgebra
  haveI htowNLk : IsScalarTower k ↥N ↥L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htowNLΩ : IsScalarTower ↥N ↥L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hfdNL : FiniteDimensional ↥N ↥L := Module.Finite.of_restrictScalars_finite k ↥N ↥L
  have hQsplit : SSGRoute.IsSplitIn k N Q := by
    have hBN : Q.comap (algebraMap ↥N Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N
          (P.under (NumberField.RingOfIntegers ↥N)) := by
      have hliesN : P.asIdeal.LiesOver (P.under (NumberField.RingOfIntegers ↥N)).asIdeal := by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
        exact ⟨rfl⟩
      have h1 : Q.comap (algebraMap ↥N Ω) =
          (Q.comap (algebraMap ↥L Ω)).comap (algebraMap ↥N ↥L) :=
        (ValuationSubring.comap_comap Q (algebraMap ↥L Ω) (algebraMap ↥N ↥L)).symm
      rw [h1, hQcomapL,
        Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
          (P.under (NumberField.RingOfIntegers ↥N)) P hliesN]
    have hliesN' : (P.under (NumberField.RingOfIntegers ↥N)).asIdeal.LiesOver 𝔭.asIdeal := by
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      refine ⟨?_⟩
      rw [Ideal.under_under]
      exact hPlies.over
    have he_N : (P.under (NumberField.RingOfIntegers ↥N)).asIdeal.ramificationIdx
        (NumberField.RingOfIntegers k) = 1 := h𝔭Bad4 _ hliesN'
    have hfrobN : NK.Chebotarev.IsFrobAt (K := k) (L := ↥N)
        (P.under (NumberField.RingOfIntegers ↥N)) (SSGRoute.res k N τ) := by
      have h := NK.Chebotarev.IsFrobAtRestrictNormalHomType (K := k) (E := ↥N) (M := ↥L) P g
        hPFrob
      have hcompat := IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply ↥N ↥L (F := k)
        (K₃ := Ω) τ
      have hres : AlgEquiv.restrictNormalHom ↥N g = AlgEquiv.restrictNormalHom ↥N τ := by
        rw [hg]
        exact hcompat.symm
      rw [show SSGRoute.res k N τ = AlgEquiv.restrictNormalHom ↥N τ from rfl, ← hres]
      exact h
    have hdec : Submission.NeukirchUchida.Local.decompositionSubgroup (K := k)
        (P.under (NumberField.RingOfIntegers ↥N)) = ⊥ := by
      rw [NK.ChebotarevGeneral.decompositionSubgroup_eq_zpowers_of_isFrobAt (K := k) (N := ↥N)
        (P.under (NumberField.RingOfIntegers ↥N)) (SSGRoute.res k N τ) he_N hfrobN, hτN]
      exact Subgroup.zpowers_one_eq_bot
    have hQneN : Q.comap (algebraMap ↥N Ω) ≠ ⊤ := by
      rw [hBN]
      exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := ↥N) _
    have hbridgeN := Work.SSGRoute.map_res_decomp_eq_stabilizer_valuationRing
      (k := k) (Ω := Ω) N Q (show Q.comap (algebraMap k Ω) ≠ ⊤ from hQfin)
      (P.under (NumberField.RingOfIntegers ↥N)) hBN
    have hstab : MulAction.stabilizer (↥N ≃ₐ[k] ↥N)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N
          (P.under (NumberField.RingOfIntegers ↥N))) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro z hz
      rw [Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup,
        hdec] at hz
      exact hz
    rw [SSGRoute.IsSplitIn]
    intro δ hδ
    rw [← IntermediateField.restrictNormalHom_ker N, MonoidHom.mem_ker]
    have hmem1 : SSGRoute.res k N δ ∈ (SSGRoute.decomp k Q).map (SSGRoute.res k N) :=
      Subgroup.mem_map_of_mem _ hδ
    rw [hbridgeN, hstab] at hmem1
    simpa using hmem1
  -- ## 10. the avoidance clause
  have hQne : Q.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    rw [hQcomapK]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := ↥K) 𝔮
  have hQnotT : ∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q := by
    intro A hA hconj
    obtain ⟨σ, hσ, hσQ⟩ := hconj
    obtain ⟨𝔭A, h𝔭AT', hAcomap⟩ := hTbelow A hA
    have hcomap : (σ • A).comap (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
      let σK : Ω ≃ₐ[↥K] Ω := (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩
      have hsmul : σK • A = σ • A := by
        apply ValuationSubring.ext
        intro y
        rw [ValuationSubring.mem_smul_pointwise_iff_exists,
          ValuationSubring.mem_smul_pointwise_iff_exists]
        constructor
        · rintro ⟨s, hs, hys⟩
          exact ⟨s, hs, by rw [← hys, AlgEquiv.smul_def, AlgEquiv.smul_def,
            show (⇑σK) = ⇑σ from rfl]⟩
        · rintro ⟨s, hs, hys⟩
          exact ⟨s, hs, by rw [← hys, AlgEquiv.smul_def, AlgEquiv.smul_def,
            show (⇑σK) = ⇑σ from rfl]⟩
      have hcom :=
        Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap (K := ↥K) (K' := Ω) A σK
      rwa [hsmul] at hcom
    have : 𝔮 = 𝔭A := by
      apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
      rw [← hQcomapK, ← hσQ, hcomap, hAcomap]
    exact h𝔭Bad1 ⟨𝔮, by rw [this]; exact h𝔭AT', h𝔮lies⟩
  -- ## 10'. the strengthened, `k`-level avoidance clause
  have hQcomapk : Q.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 := by
    have h1 : Q.comap (algebraMap k Ω) =
        (Q.comap (algebraMap ↥L Ω)).comap (algebraMap k ↥L) :=
      (ValuationSubring.comap_comap Q (algebraMap ↥L Ω) (algebraMap k ↥L)).symm
    rw [h1, hQcomapL,
      Commons.RingTheory.Valuation.comap_valuationSubringAtPrime 𝔭 P hPlies]
  have hQnotTk : ∀ A ∈ T, ¬ SSGRoute.IsConjPlace k A Q := by
    intro A hA hconj
    obtain ⟨ρ, hρ⟩ := hconj
    obtain ⟨𝔭A, h𝔭AT', hAcomap⟩ := hTbelow A hA
    -- `A = ρ⁻¹ • Q`, so the `k`-prime of `A` is the `k`-prime of `Q`, namely `𝔭`
    have hAk : A.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 := by
      have hAsmul : A = ρ⁻¹ • Q := by rw [← hρ, inv_smul_smul]
      rw [hAsmul,
        Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap (K := k) (K' := Ω) Q ρ⁻¹,
        hQcomapk]
    -- hence the `↥K`-prime `𝔭A` of `A` lies over `𝔭`, contradicting `h𝔭Bad1`
    have hcmp1 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭A).comap
        (algebraMap k ↥K) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
          (𝔭A.under (NumberField.RingOfIntegers k)) :=
      Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
        (𝔭A.under (NumberField.RingOfIntegers k)) 𝔭A (by
          rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
          exact ⟨rfl⟩)
    have hcmp2 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭A).comap
        (algebraMap k ↥K) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 := by
      rw [← hAcomap, ← hAk]
      exact (ValuationSubring.comap_comap A (algebraMap ↥K Ω) (algebraMap k ↥K)).symm
    have heq : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
        (𝔭A.under (NumberField.RingOfIntegers k)) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 :=
      hcmp1.symm.trans hcmp2
    have hunder : 𝔭A.under (NumberField.RingOfIntegers k) = 𝔭 :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := k) heq
    have hlies : 𝔭A.asIdeal.LiesOver 𝔭.asIdeal :=
      ⟨by rw [← IsDedekindDomain.HeightOneSpectrum.under_asIdeal, hunder]⟩
    exact h𝔭Bad1 ⟨𝔭A, h𝔭AT', hlies⟩
  exact ⟨Q, 𝔮, hQfin, hQsplit, h𝔮T', hQnotT, hQnotTk, hQcomapK, hmem⟩

end Work.SSGRoute.ZDataTwo
