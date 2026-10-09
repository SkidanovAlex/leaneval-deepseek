import Mathlib
import Submission.Work.SSGRoute.ZDataMup.AxIsAdmImports
import Submission.Work.SSGRoute.ZDataMup.onePlace_mem_normImage_of_mem_sup_abelian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

/-! ## Auxiliary lemmas for `isAdmissible_of_artinKillsPrincipal` -/

/-- **`ramificationIdxIn = 1` at the primes outside `(M)` is the `IsUnramified` form.** -/
lemma isAdm_isUnramified_of_notMem
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (M : ℕ)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (p : NK.Chebotarev.PrimeIdeal K) (hp : (M : NumberField.RingOfIntegers K) ∉ p.asIdeal) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p := by
  intro P hP
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : P.asIdeal.LiesOver p.asIdeal := hP
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L)
    p.asIdeal P.asIdeal (Gal(L/K))]
  exact hram p hp

/-- **The index of `Kˣ · N_{L/K}𝕀_L` in `𝕀_K` is `[L:K]`** for a cyclic extension. -/
lemma isAdm_index_principalSupNorm
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    (NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L).index
      = Module.finrank K L :=
  (NK.CFTLib.ArtinReciprocityIdeal.index_principalSubgroup_sup_normImage
      (K := K) (L := L) 1).trans
    (NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := K) (L := L))

/-- **The cyclic norm-index inequality at a modulus where the Artin symbol kills the principal
ray**: `[I(m) : P(m)·𝔑(m)] = [L:K]`.

`P(m)·𝔑(m) ⊆ ker Ψ` (`hprinc` together with `normRayLeKer`), `[I(m) : ker Ψ] = [L:K]`
(surjectivity of the Artin symbol on `I(m)`), and `[I(m) : P(m)·𝔑(m)] ≤ [L:K]` unconditionally
(`indexPrincipalRaySupNormRayLe`). -/
lemma isAdm_index_rayNorm_of_artinKillsPrincipal
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m) :
    ((NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).subgroupOf
      (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m)).index
      = Module.finrank K L := by
  classical
  haveI : IsMulCommutative (Gal(L/K)) := IsMulCommutative.of_comm hcomm
  let hc : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  let f : NK.CFTLib.ArtinReciprocityIdeal.Frac K →* Gal(L/K) :=
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hc
  let I : Subgroup (NK.CFTLib.ArtinReciprocityIdeal.Frac K) :=
    NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m
  let PN : Subgroup (NK.CFTLib.ArtinReciprocityIdeal.Frac K) :=
    NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRay K L m
  have hPNker : PN ≤ f.ker := sup_le
    (NK.CFTLib.ArtinReciprocityIdeal.principalRay_le_ker_of_artinKillsPrincipal
      (K := K) (L := L) m hm hram hprinc)
    (fun A hA => MonoidHom.mem_ker.mpr
      (NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer K L m hm hram A hA))
  have hmap : I.map f = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨A, hAσ⟩ :=
      NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime (K := K) (L := L) m hm hram σ
    exact Subgroup.mem_map.mpr ⟨(A : NK.CFTLib.ArtinReciprocityIdeal.Frac K), A.2,
      by simpa only [f, hc, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] using hAσ⟩
  have hcardI : f.ker.relIndex I = Nat.card (Gal(L/K)) := by
    rw [Subgroup.relIndex_ker I f, hmap]
    exact Nat.card_congr (Subgroup.topEquiv (G := Gal(L/K))).toEquiv
  have hJrelI : (f.ker ⊓ I).relIndex I = Module.finrank K L := by
    rw [Subgroup.inf_relIndex_right f.ker I, hcardI, IsGalois.card_aut_eq_finrank K L]
  have hle : PN ⊓ I ≤ f.ker ⊓ I := fun A hA => ⟨hPNker hA.1, hA.2⟩
  have hIdxPNInf : (PN ⊓ I).relIndex I ≤ (f.ker ⊓ I).relIndex I := by
    rw [Subgroup.inf_relIndex_right PN I, Subgroup.inf_relIndex_right f.ker I, hcardI,
      IsGalois.card_aut_eq_finrank K L]
    exact NK.CFTLib.ArtinReciprocityIdeal.indexPrincipalRaySupNormRayLe K L m hm
  have hPNne : (PN ⊓ I).relIndex I ≠ 0 := by
    haveI hfin : (NK.GlobalCFT.Idele.principalSubgroup K ⊔
        NK.GlobalCFT.Idele.normImage K L).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by
        rw [NK.CFTLib.ArtinReciprocityIdeal.index_principalSubgroup_sup_normImage
          (K := K) (L := L) 1]
        exact NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := K) (L := L))
    haveI hkerfin : (NK.CFTLib.ArtinReciprocityIdeal.theta K L m hm).ker.FiniteIndex :=
      Subgroup.finiteIndex_of_le
        (NK.CFTLib.ArtinReciprocityIdeal.principalSubgroup_sup_normImage_le_ker
          (K := K) (L := L) m hm)
    rw [Subgroup.inf_relIndex_right PN I]
    rw [show PN.relIndex I = ((NK.CFTLib.ArtinReciprocityIdeal.rayNorm K L m).subgroupOf
          (NK.CFTLib.ARL.Icoprime K m)).index from by
      show ((NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
            NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).subgroupOf
          (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m)).index
        = ((NK.CFTLib.ArtinReciprocityIdeal.rayNorm K L m).subgroupOf
          (NK.CFTLib.ARL.Icoprime K m)).index
      rw [NK.CFTLib.ArtinReciprocityIdeal.principalRay_eq_ARL,
        NK.CFTLib.ArtinReciprocityIdeal.normRay_eq_normIdeals,
        NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup_eq_Icoprime]
      rfl]
    rw [NK.CFTLib.ArtinReciprocityIdeal.index_rayNorm_eq_ker_index (K := K) (L := L) m hm]
    exact Subgroup.FiniteIndex.index_ne_zero
  have hEqPN : (PN ⊓ I).relIndex I = (f.ker ⊓ I).relIndex I :=
    le_antisymm hIdxPNInf (Subgroup.relIndex_le_of_le_left hle hPNne)
  have hgoal : PN.relIndex I = Module.finrank K L := by
    rw [show PN.relIndex I = (PN ⊓ I).relIndex I from
        (Subgroup.inf_relIndex_right PN I).symm, hEqPN, hJrelI]
  show (PN.subgroupOf I).index = Module.finrank K L
  exact hgoal

/-- **The index of the kernel of `θ` is `[L:K]`** whenever the Artin symbol kills the principal ray
at the modulus `m`. -/
lemma isAdm_kerTheta_index
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m) :
    (NK.CFTLib.ArtinReciprocityIdeal.theta K L m hm).ker.index = Module.finrank K L := by
  have h1 : ((NK.CFTLib.ArtinReciprocityIdeal.rayNorm K L m).subgroupOf
        (NK.CFTLib.ARL.Icoprime K m)).index
      = (NK.CFTLib.ArtinReciprocityIdeal.theta K L m hm).ker.index :=
    NK.CFTLib.ArtinReciprocityIdeal.index_rayNorm_eq_ker_index (K := K) (L := L) m hm
  have h2 : ((NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).subgroupOf
      (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m)).index = Module.finrank K L :=
    isAdm_index_rayNorm_of_artinKillsPrincipal hcomm m hm hram hprinc
  have h3 : ((NK.CFTLib.ArtinReciprocityIdeal.rayNorm K L m).subgroupOf
        (NK.CFTLib.ARL.Icoprime K m)).index
      = ((NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).subgroupOf
      (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m)).index := by
    rw [NK.CFTLib.ArtinReciprocityIdeal.principalRay_eq_ARL,
      NK.CFTLib.ArtinReciprocityIdeal.normRay_eq_normIdeals,
      NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup_eq_Icoprime]
    rfl
  exact h1.symm.trans (h3.trans h2)

/-- **`ker θ = Kˣ · N_{L/K}𝕀_L`** whenever the Artin symbol kills the principal ray at the modulus
`m`. -/
lemma isAdm_kerTheta_eq
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m) :
    (NK.CFTLib.ArtinReciprocityIdeal.theta K L m hm).ker
      = NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L := by
  have hle : NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L ≤
      (NK.CFTLib.ArtinReciprocityIdeal.theta K L m hm).ker :=
    NK.CFTLib.ArtinReciprocityIdeal.principalSubgroup_sup_normImage_le_ker
      (K := K) (L := L) m hm
  have hIdx : (NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L).index
      = (NK.CFTLib.ArtinReciprocityIdeal.theta K L m hm).ker.index :=
    (isAdm_index_principalSupNorm (K := K) (L := L)).trans
      ((isAdm_kerTheta_index hcomm m hm hram hprinc).symm)
  have h0 : 0 < (NK.CFTLib.ArtinReciprocityIdeal.theta K L m hm).ker.index := by
    rw [isAdm_kerTheta_index hcomm m hm hram hprinc]
    exact Module.finrank_pos (R := K) (M := L)
  have hrel : (NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L).relIndex
      (NK.CFTLib.ArtinReciprocityIdeal.theta K L m hm).ker = 1 := by
    refine Nat.eq_of_mul_eq_mul_right h0 ?_
    rw [Subgroup.relIndex_mul_index hle, hIdx, one_mul]
  refine le_antisymm ?_ hle
  exact Subgroup.relIndex_eq_one.mp hrel

/-- **A congruence unit at a single finite place lies in the kernel of `θ`.** -/
lemma isAdm_onePlace_mem_ker_theta
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (m : ℕ) (hm : 0 < m)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (Q.adicCompletion K)ˣ)
    (hu : u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q))
    (hc : NK.CFTLib.Arl.CongrAt Q m u) :
    NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u ∈
      (NK.CFTLib.ArtinReciprocityIdeal.theta K L m hm).ker := by
  rw [MonoidHom.mem_ker, NK.CFTLib.ArtinReciprocityIdeal.theta_apply]
  have hcong : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u ∈
      NK.CFTLib.Arl.congruenceSubgroup K m := by
    refine ⟨?_, ?_⟩
    · intro 𝔭 h𝔭
      by_cases h : 𝔭 = Q
      · subst h
        simpa only [NK.HassePrinciple.onePlace_apply_self, NK.CFTLib.Arl.CongrAt] using hc
      · rw [NK.HassePrinciple.onePlace_apply_ne (v := NK.GlobalCFT.Place.ofFinite 𝔭)
          (w := NK.GlobalCFT.Place.ofFinite Q) (by simpa using h)]
        exact NK.CFTLib.Arl.congrAt_one 𝔭 m
    · intro w
      rw [NK.HassePrinciple.onePlace_apply_ne
        (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w Q)]
      exact NK.CFTLib.Arl.posAtReal_one w
  have hint : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u ∈
      NK.GlobalCFT.Idele.integralIdeles K := by
    rw [NK.GlobalCFT.Idele.mem_integralIdeles]
    intro v hv
    obtain ⟨Q', rfl⟩ := NK.GlobalCFT.Place.isFinite_iff.mp hv
    by_cases h : Q' = Q
    · subst h
      rw [NK.HassePrinciple.onePlace_apply_self]
      exact hu
    · rw [NK.HassePrinciple.onePlace_apply_ne (by simpa using h)]
      exact Subgroup.one_mem _
  have hid : NK.GlobalCFT.Idele.idealOf
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u) = 1 :=
    (NK.GlobalCFT.Idele.idealOf_eq_one_iff _).mpr hint
  have hidu : NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u) = 1 := by
    rw [NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom_apply]
    exact Units.ext (by rw [Units.val_mk0, hid, Units.val_one])
  have hx1 : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u *
        NK.GlobalCFT.Idele.principalIdele K 1
      = NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u := by
    rw [map_one, mul_one]
  have h1 := NK.CFTLib.ArtinReciprocityIdeal.thetaFun_eq_mk (K := K) (L := L) m hm
    (x := NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u) (c := 1)
    (by simpa using hcong)
  rw [h1, hx1, hidu, map_one]

/-- **A one-place idèle whose local component is not a local norm is outside
`Kˣ · N_{L/K}𝕀_L`.** -/
lemma isAdm_onePlace_not_mem_sup
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (Q.adicCompletion K)ˣ)
    (hu : u ∉ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite Q)) :
    NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u ∉
      (NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L) := by
  intro hmem
  apply hu
  have hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a := by
    intro a b
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
    obtain ⟨m₁, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨m₂, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    rw [← zpow_add, ← zpow_add, add_comm m₁ m₂]
  refine (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L)
    (NK.GlobalCFT.Place.ofFinite Q) u).mp ?_
  refine onePlace_mem_normImage_of_mem_sup_abelian (K := K) (L := L) hcomm ?_
  rw [sup_comm]
  exact hmem

/-- **A congruence unit is a local unit.** -/
lemma isAdm_mem_localUnits_of_congr
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (m : ℕ)
    (hmem : (m : 𝓞 K) ∈ Q.asIdeal) (u : (Q.adicCompletion K)ˣ)
    (hc : NK.CFTLib.Arl.CongrAt Q m u) :
    u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q) := by
  rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  have hlt : Valued.v ((u : Q.adicCompletion K) - 1) < 1 :=
    lt_of_le_of_lt hc (NK.CFTLib.Arl.val_natCast_lt_one Q m hmem)
  have h := Valuation.map_add_eq_of_lt_left (v := Valued.v)
    (x := (1 : Q.adicCompletion K)) (y := (u : Q.adicCompletion K) - 1) (by simpa using hlt)
  simpa using h

/-- For a **cyclic** extension of number fields, the ideal-theoretic reciprocity law at a modulus
`M` forces `M` to be *admissible*: every unit which is `≡ 1 mod M` at a prime `𝔭 | (M)` is a local
norm.  Equivalently, the exponent of `M` at each ramified prime is at least the conductor exponent.

Proof route (as in `NOTES_conductorDrop_plan.md`, item 1): choose a canonical modulus `c`
(`exists_admissible`), let `θ_v = art ∘ onePlace_v` be the local factors with the product formula
(`Work.SSGRoute.ZSplit.localFactor_kernel_reciprocity`); use weak approximation
(`Work.SSGRoute.ZDataMup.weakApprox_pos_numberField`) to build an integral totally positive `a`
with `a ≡ u mod 𝔭^N` for a prescribed local unit `u` and `a ≡ 1 mod 𝔮^{...}` at the other primes
dividing `(M)`; `hprinc` gives `artinSym (a) = 1`, the product formula gives `θ_𝔭(a_𝔭) = 1`, hence
`a_𝔭 ∈ N` and `u ∈ N` as `u/a ∈ U^{(N)}`; at an unramified `𝔭 | (M)` the conclusion is automatic
(local units of an unramified local extension are norms). -/
theorem isAdmissible_of_artinKillsPrincipal
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (M : ℕ) (hM : 0 < M)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L M) :
    NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L M := by
  classical
  have hram' : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (M : NumberField.RingOfIntegers K) ∈ p.asIdeal := by
    intro p hp
    by_contra hmem
    exact hp (isAdm_isUnramified_of_notMem M hram p hmem)
  have hker := isAdm_kerTheta_eq hcomm M hM hram' hprinc
  intro 𝔭 h𝔭 𝔮 h𝔮 u hu
  by_contra huN
  have huLoc : u ∉ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite 𝔭) := by
    intro hmem
    exact huN (by
      rw [NK.CFTLib.IdeleHasse.range_localNormFinite_eq_localNormSubgroup (K := K) (L := L) 𝔭 𝔮 h𝔮]
      exact hmem)
  have hnotV := isAdm_onePlace_not_mem_sup (K := K) (L := L) 𝔭 u huLoc
  have hmemKer : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) u ∈
      (NK.CFTLib.ArtinReciprocityIdeal.theta K L M hM).ker :=
    isAdm_onePlace_mem_ker_theta M hM 𝔭 u
      (isAdm_mem_localUnits_of_congr 𝔭 M h𝔭 u hu) hu
  rw [hker] at hmemKer
  exact hnotV hmemKer

end Work.SSGRoute.ZDataMup
