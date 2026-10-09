import Mathlib
import Submission.NK.CFTLib.Existence.arl_helpers
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.Existence.res_inf_le_ker_res_of_auxiliary
import Submission.NK.CFTLib.ArtinReciprocityIdeal.AbelianReduction
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one
import Submission.NK.CFTLib.Arl.sum_ramificationIdx_mul_inertiaDeg_primesOverFinite
import Submission.NK.CFTLib.Existence.count_idealOf_ideleInclusion
import Submission.NK.CFTLib.Existence.ideleInclusion_congruenceSubgroup
import Submission.NK.NUV2.ARL.normAdjustment
import Submission.NK.Chebotarev.AbelianChebotarevOfLFunctions
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable

/-!
# Components of the proof of `NK.CFTLib.Existence.arl_invariants`

This module collects the verified components of the arithmetic input `NK.CFTLib.Existence.arl_invariants`
(the Verlagerung input of Route B): the Galois-theoretic bookkeeping for the complementary pair
`(Msub, Nsub)`, the per-prime Frobenius product computation (an improvement of
`NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one` where the unramifiedness hypothesis is at
`𝔭` in `E/K` rather than in `M/K`), and the computation of the Artin symbol of an extended ideal.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped NumberField Pointwise nonZeroDivisors
open NumberField IntermediateField IsDedekindDomain

namespace NK.CFTLib.Arl

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
  [FiniteDimensional K Ω] [IsGalois K Ω]

/-- `|Msub| = |Gal(L/K)|`. -/
lemma card_Msub_eq (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hdisj : fixedField Msub ⊓ fixedField Nsub = ⊥)
    (hsup : fixedField Msub ⊔ fixedField Nsub = ⊤) :
    Nat.card ↥Msub = Nat.card Gal(L/K) := by
  have hcard := NK.CFTLib.Existence.card_mul_card_eq Msub Nsub hdisj hsup
  have hG : Nat.card Gal(Ω/K) = Nat.card ↥Nsub * Nat.card (Gal(Ω/K) ⧸ Nsub) := by
    rw [← Subgroup.index_eq_card]; exact (Subgroup.card_mul_index Nsub).symm
  have key : Nat.card ↥Nsub * Nat.card ↥Msub
      = Nat.card ↥Nsub * Nat.card (Gal(Ω/K) ⧸ Nsub) := by
    rw [mul_comm (Nat.card ↥Nsub), hcard, hG]
  have h1 : Nat.card ↥Msub = Nat.card (Gal(Ω/K) ⧸ Nsub) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos key
  rw [h1, hN]

/-- The exponent of `Gal(Ω/K)` divides `n`. -/
lemma pow_card_eq_one (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hdisj : fixedField Msub ⊓ fixedField Nsub = ⊥)
    (hsup : fixedField Msub ⊔ fixedField Nsub = ⊤) :
    ∀ g : Gal(Ω/K), g ^ Nat.card Gal(L/K) = 1 := by
  have hMN : Msub ⊔ Nsub = ⊤ := NK.CFTLib.Existence.sup_eq_top_of_fixedField_inf_eq_bot Msub Nsub hdisj
  have hMiN : Msub ⊓ Nsub = ⊥ := NK.CFTLib.Existence.inf_eq_bot_of_fixedField_sup_eq_top Msub Nsub hsup
  have hcardN : Nat.card ↥Nsub = Nat.card Gal(L/K) :=
    (NK.CFTLib.Existence.card_nsub_eq_card_quotient Msub Nsub hdisj hsup).trans hM
  have hcardM : Nat.card ↥Msub = Nat.card Gal(L/K) := card_Msub_eq Msub Nsub hN hdisj hsup
  intro g
  have hg : g ∈ (Msub : Set Gal(Ω/K)) * (Nsub : Set Gal(Ω/K)) := by
    rw [← Subgroup.mul_normal Msub Nsub, hMN]; trivial
  obtain ⟨m, hm, n, hn, rfl⟩ := Set.mem_mul.mp hg
  have hcomm : Commute m n := Subgroup.commute_of_normal_of_disjoint _ _
    (inferInstance : Msub.Normal) (inferInstance : Nsub.Normal)
    (disjoint_iff_inf_le.mpr (by rw [hMiN])) m n hm hn
  rw [hcomm.mul_pow]
  have hm1 : m ^ Nat.card Gal(L/K) = 1 := by
    have h : (⟨m, hm⟩ : ↥Msub) ^ Nat.card ↥Msub = 1 := pow_card_eq_one'
    rw [hcardM] at h
    simpa using Subtype.ext_iff.mp h
  have hn1 : n ^ Nat.card Gal(L/K) = 1 := by
    have h : (⟨n, hn⟩ : ↥Nsub) ^ Nat.card ↥Nsub = 1 := pow_card_eq_one'
    rw [hcardN] at h
    simpa using Subtype.ext_iff.mp h
  rw [hm1, hn1, mul_one]



/-- The product of the Frobenius elements of `E/L₀` at the primes of `L₀` above a prime `𝔭` of `K`
which is unramified in `E/K`, raised to the ramification indices, is trivial. -/
theorem prod_frobAtPrime_pow_eq_one_of_unramified {K E : Type} [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (L₀ M : IntermediateField K E) [IsGalois K ↥L₀] [IsGalois K ↥M]
    [IsMulCommutative Gal(↥M/K)]
    (hdisj : L₀ ⊓ M = ⊥) (hsup : L₀ ⊔ M = ⊤)
    (hcard : Nat.card Gal(↥L₀/K) = Nat.card Gal(↥M/K))
    (hexp : ∀ σ : Gal(↥M/K), σ ^ Module.finrank K ↥L₀ = 1)
    (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (hunr : ∀ 𝔓 : NK.Chebotarev.PrimeIdeal E,
      𝔓.asIdeal.LiesOver 𝔭.asIdeal → 𝔓.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (List.map (fun 𝔮 => (NK.Chebotarev.frobAtPrime (K := ↥L₀) (L := E) 𝔮) ^
      (𝔮.asIdeal.ramificationIdx (𝓞 K)))
      (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L₀) 𝔭).toList).prod = 1 := by
  classical
  haveI hfdL0 : FiniteDimensional K ↥L₀ := IsGalois.finiteDimensional_of_finite K ↥L₀
  haveI hfdM : FiniteDimensional K ↥M := IsGalois.finiteDimensional_of_finite K ↥M
  refine NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one L₀ M hdisj hsup hexp 𝔭 ?_ ?_
  · -- `𝔭` is unramified in `M/K`
    intro Q hQ
    obtain ⟨𝔓, h𝔓⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := ↥M) (L := E) Q
    haveI h𝔓Q : 𝔓.asIdeal.LiesOver Q.asIdeal := h𝔓
    haveI hQ𝔭 : Q.asIdeal.LiesOver 𝔭.asIdeal := hQ
    have h𝔓𝔭 : 𝔓.asIdeal.LiesOver 𝔭.asIdeal :=
      Ideal.LiesOver.trans 𝔓.asIdeal Q.asIdeal 𝔭.asIdeal
    have h1 : 𝔓.asIdeal.ramificationIdx (𝓞 K) = 1 := hunr 𝔓 h𝔓𝔭
    have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 ↥M) (T := 𝓞 E)
      Q.asIdeal 𝔓.asIdeal
    rw [h1] at htower
    exact (mul_eq_one.mp htower.symm).1
  · -- `E/L₀` is unramified above `𝔭`
    intro 𝔮 h𝔮 𝔔 h𝔔
    have h𝔮𝔭 : 𝔮.asIdeal.LiesOver 𝔭.asIdeal :=
      (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := ↥L₀) (Q := 𝔭) (q := 𝔮)).mp h𝔮
    haveI h𝔔𝔮 : 𝔔.asIdeal.LiesOver 𝔮.asIdeal := h𝔔
    haveI h𝔮𝔭' : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := h𝔮𝔭
    have h𝔓𝔭 : 𝔔.asIdeal.LiesOver 𝔭.asIdeal :=
      Ideal.LiesOver.trans 𝔔.asIdeal 𝔮.asIdeal 𝔭.asIdeal
    have h1 : 𝔔.asIdeal.ramificationIdx (𝓞 K) = 1 := hunr 𝔔 h𝔓𝔭
    have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 ↥L₀) (T := 𝓞 E)
      𝔮.asIdeal 𝔔.asIdeal
    rw [h1] at htower
    exact (mul_eq_one.mp htower.symm).2


/-- Powers of a list of pairwise commuting elements factor out. -/
lemma List.prod_map_zpow {G ι : Type*} [Group G] (l : List ι) (f : ι → G)
    (hcomm : ∀ a b : G, a * b = b * a) (v : ℤ) :
    (l.map (fun x => f x ^ v)).prod = ((l.map f).prod) ^ v := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ih]
      have hc : Commute (f a) ((l.map f).prod) := hcomm _ _
      exact (hc.mul_zpow v).symm

/-- **The Artin symbol of the extended ideal.** -/
theorem artinSym_idealOf_ideleInclusion_eq_one {K L E : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [Field E] [NumberField E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    [FiniteDimensional L E] [IsGalois L E]
    (hcomm : ∀ a b : Gal(E/L), a * b = b * a)
    (u : NK.GlobalCFT.Place L → NK.GlobalCFT.Place K)
    (hu : ∀ w : NK.GlobalCFT.Place L, w.LiesOver (u w))
    (φ : NK.GlobalCFT.Idele K →* NK.GlobalCFT.Idele L)
    (hφ : ∀ (x : NK.GlobalCFT.Idele K) (w : NK.GlobalCFT.Place L),
      φ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (M : ℕ)
    (hterm : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, (M : 𝓞 K) ∉ 𝔭.asIdeal →
      (List.map (fun 𝔮 : NK.Chebotarev.PrimeIdeal L =>
          (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^
            (𝔮.asIdeal.ramificationIdx (𝓞 K)))
        (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭).toList).prod = 1)
    (x : NK.GlobalCFT.Idele K)
    (hMsupp : ∀ 𝔮 ∈ (exps (NK.GlobalCFT.Idele.idealOf (φ x))).support,
      (M : 𝓞 K) ∉ (𝔮.under (𝓞 K)).asIdeal) :
    artinSym hcomm (NK.GlobalCFT.Idele.idealOf (φ x)) = 1 := by
  classical
  letI : CommMonoid Gal(E/L) := galCommMonoid hcomm
  set A := NK.GlobalCFT.Idele.idealOf (φ x) with hA
  have hunfold : artinSym hcomm A
      = ∏ 𝔮 ∈ (exps A).support,
          (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^ ((exps A) 𝔮) := by
    rw [artinSym]
    exact Finsupp.prod_of_support_subset _ le_rfl _ (fun i _ => zpow_zero _)
  rw [hunfold]
  -- group the product over `L` by the prime of `K` below
  rw [← Finset.prod_fiberwise_of_maps_to
    (s := (exps A).support)
    (t := (exps A).support.image (fun 𝔮 : NK.Chebotarev.PrimeIdeal L => 𝔮.under (𝓞 K)))
    (g := fun 𝔮 : NK.Chebotarev.PrimeIdeal L => 𝔮.under (𝓞 K))
    (f := fun 𝔮 => (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^ ((exps A) 𝔮))
    (fun i hi => Finset.mem_image_of_mem _ hi)]
  refine Finset.prod_eq_one ?_
  rintro 𝔭 h𝔭
  obtain ⟨𝔮₀, h𝔮₀s, h𝔮₀u⟩ := Finset.mem_image.mp h𝔭
  have hM𝔭 : (M : 𝓞 K) ∉ 𝔭.asIdeal := by
    rw [← h𝔮₀u]
    exact hMsupp 𝔮₀ h𝔮₀s
  set v : ℤ := FractionalIdeal.count K 𝔭 (NK.GlobalCFT.Idele.idealOf x) with hv
  have hfib : (exps A).support.filter (fun 𝔮 : NK.Chebotarev.PrimeIdeal L => 𝔮.under (𝓞 K) = 𝔭)
      ⊆ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭 := by
    intro 𝔮 h𝔮
    rw [Finset.mem_filter] at h𝔮
    rw [NK.GlobalCFT.Place.mem_primesOverFinite]
    exact Ideal.LiesOver.mk (by
      rw [← h𝔮.2, IsDedekindDomain.HeightOneSpectrum.under_asIdeal])
  have hprod : (∏ 𝔮 ∈ (exps A).support.filter
        (fun 𝔮 : NK.Chebotarev.PrimeIdeal L => 𝔮.under (𝓞 K) = 𝔭),
        (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^ ((exps A) 𝔮))
      = ∏ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭,
          (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^ ((exps A) 𝔮) := by
    refine (Finset.prod_subset
      (f := fun 𝔮 : NK.Chebotarev.PrimeIdeal L =>
        (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^ ((exps A) 𝔮)) hfib ?_)
    intro 𝔮 h𝔮T h𝔮S
    have hzero : (exps A) 𝔮 = 0 := by
      by_contra hne
      apply h𝔮S
      rw [Finset.mem_filter]
      refine ⟨(Finsupp.mem_support_iff).mpr hne, ?_⟩
      have hlies := (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L)
        (Q := 𝔭) (q := 𝔮)).mp h𝔮T
      refine IsDedekindDomain.HeightOneSpectrum.ext ?_
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      exact hlies.over.symm
    rw [hzero, zpow_zero]
    rfl
  rw [hprod]
  have hcount : ∀ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭,
      (exps A) 𝔮 = (𝔮.asIdeal.ramificationIdx (𝓞 K) : ℤ) * v := by
    intro 𝔮 h𝔮
    have hlies := (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L)
      (Q := 𝔭) (q := 𝔮)).mp h𝔮
    rw [NK.CFTLib.Arl.exps_apply]
    exact NK.CFTLib.Existence.count_idealOf_ideleInclusion u hu φ hφ x 𝔭 𝔮 hlies
  rw [Finset.prod_congr rfl (fun 𝔮 h𝔮 => by rw [hcount 𝔮 h𝔮, zpow_mul])]
  rw [← Finset.prod_map_toList
    (f := fun 𝔮 : NK.Chebotarev.PrimeIdeal L =>
      ((NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^
        ((𝔮.asIdeal.ramificationIdx (𝓞 K) : ℤ))) ^ v)]
  refine (show (List.map (fun 𝔮 : NK.Chebotarev.PrimeIdeal L =>
          ((NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^
            ((𝔮.asIdeal.ramificationIdx (𝓞 K) : ℤ))) ^ v)
        (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭).toList).prod
      = ((List.map (fun 𝔮 : NK.Chebotarev.PrimeIdeal L =>
          (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^
            ((𝔮.asIdeal.ramificationIdx (𝓞 K) : ℤ)))
        (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭).toList).prod) ^ v
    from NK.CFTLib.Arl.List.prod_map_zpow _ _ hcomm v).trans ?_
  simp only [zpow_natCast]
  rw [hterm 𝔭 hM𝔭, one_zpow]
  rfl



/-! ## Galois-theoretic data for the complementary pair -/

/-- The exponential structure of `Ω/K`. -/
lemma galois_data (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hdisj : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥)
    (hsup : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤) :
    Nat.card ↥Nsub = Nat.card Gal(L/K) ∧
    Nat.card ↥Msub = Nat.card Gal(L/K) ∧
    (∀ g : Gal(Ω/K), g ^ Nat.card Gal(L/K) = 1) ∧
    Msub ⊔ Nsub = ⊤ ∧ Msub ⊓ Nsub = ⊥ :=
  ⟨(NK.CFTLib.Existence.card_nsub_eq_card_quotient Msub Nsub hdisj hsup).trans hM,
   card_Msub_eq Msub Nsub hN hdisj hsup,
   pow_card_eq_one Msub Nsub hN hM hdisj hsup,
   NK.CFTLib.Existence.sup_eq_top_of_fixedField_inf_eq_bot Msub Nsub hdisj,
   NK.CFTLib.Existence.inf_eq_bot_of_fixedField_sup_eq_top Msub Nsub hsup⟩

/-- `Gal(Ω/L') ≅ Nsub` for `L' = fixedField Nsub`. -/
lemma galois_fixedField_equiv (Nsub : Subgroup Gal(Ω/K)) [Nsub.Normal] :
    Nonempty (Gal(Ω/↥(IntermediateField.fixedField Nsub)) ≃* ↥Nsub) :=
  ⟨(IntermediateField.subgroupEquivAlgEquiv Nsub).symm⟩

/-- `Gal(M'/K)` is commutative for `M' = fixedField Msub`, when `Gal(Ω/K)/Msub` is cyclic. -/
lemma isMulCommutative_fixedField (Msub : Subgroup Gal(Ω/K)) [Msub.Normal]
    (hcyc : IsCyclic (Gal(Ω/K) ⧸ Msub)) :
    IsMulCommutative Gal(↥(IntermediateField.fixedField Msub)/K) := by
  haveI : IsCyclic Gal(↥(IntermediateField.fixedField Msub)/K) :=
    (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient Msub)).mp hcyc
  exact IsCyclic.isMulCommutative

/-! ## The modulus enlargement: a prime ramified in `Ω/K` divides `N(𝔡_{Ω/K})` -/

/-- A prime of `K` ramified in `Ω/K` divides the different-number `N(𝔡_{Ω/K})`. -/
lemma absNorm_differentIdeal_mem_of_ramified {p : NK.Chebotarev.PrimeIdeal K}
    (hp : Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) ≠ 1) :
    ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 Ω)) : ℕ) : 𝓞 K) ∈ p.asIdeal := by
  by_contra hmem
  exact hp (NK.CFTLib.ramificationIdxIn_eq_one_of_absNorm_differentIdeal_notMem p hmem)

lemma absNorm_differentIdeal_pos :
    0 < Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 Ω)) := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  exact differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 Ω) (Ideal.absNorm_eq_zero_iff.mp h0)

end NK.CFTLib.Arl
