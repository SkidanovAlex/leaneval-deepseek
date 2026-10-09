import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.indexIdealCoprimeLeNormClassIndex
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.NUV2.ARL.localUnits_le_imageLocalNormFinite_of_ramificationIdx_eq_one
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
import Submission.NK.CFTLib.ArtinReciprocityIdeal.integral_congr_pos_mem_normImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lang's norm index in ideal form (the lower bound)

This module proves `NK.CFTLib.ArtinReciprocityIdeal.langCyclicRelIndex_proved`:

    `[L : K] ≤ [I^S(m) : P(m)·𝔑(m)]`

for a finite **cyclic** extension `L / K` of number fields and a modulus `m > 0` which is
admissible (`IsAdmissible`) and divisible by all the primes ramified in `L / K`.  This is the
*lower* bound half of Lang's norm index formula (`Lang, ANT, X §2`); the upper bound
`≤ [L : K]` is `NK.CFTLib.ArtinReciprocityIdeal.indexPrincipalRaySupNormRayLe` /
`NK.CFTLib.ARL.index_principalRay_sup_normIdeals_le`.

## Route

The proof works on the idèle side, through the map
`theta : 𝕀 K →* (fractional ideals of K) ⧸ P(m)·𝔑(m)`, `x ↦ (x·(b))` for `b ∈ Kˣ` chosen so that
`x·(b) ≡ 1 mod m` (`NK.CFTLib.ArtinReciprocityIdeal.theta`).  The idèle–ideal dictionary says
that

* `(theta).ker ⊇ Kˣ·N_{L/K} 𝕀_L` — already on disk
  (`principalSubgroup_sup_normImage_le_ker`), and
* `(theta).ker ⊆ Kˣ·N_{L/K} 𝕀_L` when `(m)` is admissible and kills all ramification — this is
  `theta_ker_le` below, the heart of the argument.

Then `[I^S(m) : P(m)·𝔑(m)] = (theta).ker.index = [𝕀_K : Kˣ·N_{L/K}𝕀_L] = [C_K : N C_L] = [L : K]`,
the last equality being `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic` (the reciprocity law for
cyclic extensions).

`theta_ker_le` is proved by running the standard local–global analysis: if `x ∈ (theta).ker` and
`idealOf (x·(b)) = (a)·N_{L/K}(y)`-ideal, then `z := x·(b)·(a)⁻¹·N_{L/K}(y)⁻¹` is an integral idèle
which is a local norm at every place — away from `(m)` because `L/K` is unramified there and `z` is
a local unit, at the primes dividing `(m)` because `z·N_{L/K}(y) ≡ 1 mod m` and `(m)` is admissible,
and at the archimedean places by positivity.  Hasse's norm theorem in the form
`NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm` (locally a norm at every place ⟹ a norm of an
idèle) then puts `z` in `N_{L/K} 𝕀_L`, so `x ∈ Kˣ·N_{L/K}𝕀_L`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped NumberField.LiesOver
open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## 1.  A congruence-norm statement -/

/-- `normIdeleFun` is multiplicative in the idèle. -/
lemma normIdeleFun_mul' (y₁ y₂ : Idele L) (v : Place K) :
    Idele.normIdeleFun K L (y₁ * y₂) v =
      Idele.normIdeleFun K L y₁ v * Idele.normIdeleFun K L y₂ v := by
  rw [← Idele.normIdeleHom_apply, map_mul, Idele.mul_apply, Idele.normIdeleHom_apply,
    Idele.normIdeleHom_apply]

/-- **A congruence-norm statement**: an integral idèle `z` whose product with an idèlic norm
`N_{L/K}(y)` is congruent to `1` modulo `m` at the primes dividing `(m)` and positive at the real
places is itself an idèlic norm. -/
theorem mem_normImage_of_congruence_mul_norm [IsGalois K L] [IsCyclic (Gal(L/K))] {m : ℕ}
    (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m)
    (z : Idele K) (y : Idele L) (hz : z.idealOf = 1)
    (hcong : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      NK.CFTLib.Arl.CongrAt 𝔭 m
        (z (Place.ofFinite 𝔭) * Idele.normIdeleFun K L y (Place.ofFinite 𝔭)))
    (hpos : ∀ w : InfinitePlace K, NK.CFTLib.Arl.PosAtReal w
      (z (Place.ofInfinite w) * Idele.normIdeleFun K L y (Place.ofInfinite w))) :
    z ∈ Idele.normImage K L := by
  classical
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm (K := K) (L := L) z]
  intro v
  rcases v with v | Q
  · -- archimedean
    obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v :=
      InfinitePlace.comap_surjective v
    have hwl : w.LiesOver v := (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w v).mpr hw
    haveI : w.LiesOver v := hwl
    have hdef : Place.localNormInfinite w v
        = Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) := rfl
    have hmem : z (Place.ofInfinite v) * Idele.normIdeleFun K L y (Place.ofInfinite v) ∈
        (Place.localNormInfinite w v).range := by
      rw [hdef]
      rcases v.isReal_or_isComplex with hvR | hvC
      · rcases w.isReal_or_isComplex with hwR | hwC
        · rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real hvR hwR]
          exact Subgroup.mem_top _
        · refine NK.GlobalCFTdeep.NormIndex.localNormInfinite_posSubgroup_le_range_of_real_complex
            hvR hwC ?_
          rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
          exact hpos v hvR
      · have hwC : w.IsComplex :=
          NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
        rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex hvC hwC]
        exact Subgroup.mem_top _
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
    refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
      (Place.ofInfinite w) u * y⁻¹, ?_⟩
    have h1 : Idele.normIdeleFun K L
          (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofInfinite w) u * y⁻¹)
          (Place.ofInfinite v)
        = Place.localNormInfinite w v u * (Idele.normIdeleFun K L y (Place.ofInfinite v))⁻¹ := by
      rw [normIdeleFun_mul', Idele.normIdeleFun_inv_apply,
        NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite v w u]
    rw [h1, hu]
    group
  · -- nonarchimedean
    obtain ⟨q, hq⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
    by_cases hmQ : (m : 𝓞 K) ∈ Q.asIdeal
    · obtain ⟨u, hu⟩ := hadm Q hmQ q hq
        (z (Place.ofFinite Q) * Idele.normIdeleFun K L y (Place.ofFinite Q)) (hcong Q hmQ)
      refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
        (Place.ofFinite q) u * y⁻¹, ?_⟩
      have h1 : Idele.normIdeleFun K L
            (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofFinite q) u * y⁻¹)
            (Place.ofFinite Q)
          = Place.localNormFinite q Q hq u * (Idele.normIdeleFun K L y (Place.ofFinite Q))⁻¹ := by
        rw [normIdeleFun_mul', Idele.normIdeleFun_inv_apply,
          NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q hq u]
      rw [h1, hu]
      group
    · have hunr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q := by
        by_contra h
        exact hmQ (hram Q h)
      have hzQ : z (Place.ofFinite Q) ∈ Place.localUnits K (Place.ofFinite Q) :=
        Idele.mem_integralIdeles.mp ((Idele.idealOf_eq_one_iff z).mp hz) (Place.ofFinite Q)
          (Place.isFinite_ofFinite Q)
      obtain ⟨u, -, hu⟩ :=
        NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
          Q q hq (hunr q hq) (z (Place.ofFinite Q)) hzQ
      refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofFinite q) u, ?_⟩
      rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q hq u,
        hu]

/-! ## 2.  The norm subgroup and the coprimality of `P(m)·𝔑(m)` -/

/-- A fractional ideal of `L` coprime to `m` has relative norm in the group of ideals of `K`
coprime to `m`. -/
lemma relNormUnit_mem_Icoprime (m : ℕ) {A : (FractionalIdeal (𝓞 L)⁰ L)ˣ}
    (hA : A ∈ NK.CFTLib.ARL.Icoprime L m) :
    NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A ∈ NK.CFTLib.ARL.Icoprime K m := by
  rw [NK.CFTLib.ARL.mem_Icoprime] at hA ⊢
  intro 𝔭 h𝔭
  rw [show ((NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = NK.CFTLib.ARL.relNormFI (K := K) (L := L)
          (A : FractionalIdeal (𝓞 L)⁰ L) from rfl,
    NK.CFTLib.ARL.count_relNormFI, NK.CFTLib.ARL.relNormExp]
  refine Finset.sum_eq_zero (fun 𝔮 h𝔮 => ?_)
  haveI hLO : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := (Place.mem_primesOverFinite).mp h𝔮
  have hmq : (m : 𝓞 L) ∈ 𝔮.asIdeal := by
    have h1 : algebraMap (𝓞 K) (𝓞 L) (m : 𝓞 K) ∈ 𝔮.asIdeal :=
      (Ideal.mem_of_liesOver (p := 𝔭.asIdeal) (P := 𝔮.asIdeal) (m : 𝓞 K)).mp h𝔭
    simpa using h1
  rw [hA 𝔮 hmq, mul_zero]

/-- Every element of `𝔑(m)` is the relative norm of an ideal of `L` coprime to `m`. -/
theorem exists_relNormUnit_of_mem_normIdeals (m : ℕ) {𝔫 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : 𝔫 ∈ NK.CFTLib.ARL.normIdeals K L m) :
    ∃ A ∈ NK.CFTLib.ARL.Icoprime L m, NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A = 𝔫 := by
  have hle : NK.CFTLib.ARL.normIdeals K L m ≤
      (NK.CFTLib.ARL.Icoprime L m).map (NK.CFTLib.ARL.relNormUnit (K := K) (L := L)) := by
    rw [NK.CFTLib.ARL.normIdeals]
    refine (Subgroup.closure_le _).mpr ?_
    rintro A ⟨𝔅, rfl⟩
    obtain ⟨hI, hcop⟩ := 𝔅.2
    refine Subgroup.mem_map.mpr ⟨Units.mk0 ((𝔅.1 : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) (by
      rw [FractionalIdeal.coeIdeal_ne_zero]; exact hI), ?_, ?_⟩
    · rw [NK.CFTLib.ARL.mem_Icoprime]
      intro 𝔓 h𝔓
      rw [Units.val_mk0]
      by_contra hc
      exact hcop 𝔓 h𝔓 ((count_ne_zero_iff_dvd (K := L) hI 𝔓).mp hc)
    · refine Units.ext ?_
      simp only [Units.val_mk0]
      exact NK.CFTLib.ARL.relNormFI_coeIdeal (K := K) (L := L) 𝔅.1 hI
  obtain ⟨A, hA, hAeq⟩ := Subgroup.mem_map.mp (hle h)
  exact ⟨A, hA, hAeq⟩

/-- **The first conjunct**: `P(m)·𝔑(m) ⊆ I(m)`. -/
theorem principalRay_sup_normRay_le_idealCoprimeGroup (m : ℕ) :
    (NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay K L m) ≤
      NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m := by
  rw [NK.CFTLib.ArtinReciprocityIdeal.principalRay_eq_ARL,
    NK.CFTLib.ArtinReciprocityIdeal.normRay_eq_normIdeals,
    NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup_eq_Icoprime]
  refine sup_le ?_ ?_
  · intro A hA
    obtain ⟨a, haU, rfl⟩ := Subgroup.mem_map.mp hA
    rw [NK.CFTLib.ARL.mem_Icoprime]
    intro 𝔭 h𝔭
    rw [NK.CFTLib.ARL.unitsToIdealUnits_coe, ← Idele.idealOf_principalIdele]
    exact NK.CFTLib.ARL.count_idealOf_eq_zero_of_congruence (Subgroup.mem_comap.mp haU) 𝔭 h𝔭
  · intro 𝔫 h𝔫
    obtain ⟨A, hA, rfl⟩ := exists_relNormUnit_of_mem_normIdeals (K := K) (L := L) m h𝔫
    exact relNormUnit_mem_Icoprime (K := K) (L := L) m hA

/-! ## 3.  The kernel of `θ` -/

/-- **The kernel of `θ` is contained in `Kˣ · 𝔑`** (the idèle–ideal dictionary, Milne Prop. 4.6). -/
theorem theta_ker_le [IsGalois K L] [IsCyclic (Gal(L/K))] (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m) :
    (NK.CFTLib.ArtinReciprocityIdeal.theta K L m hm).ker ≤
      Idele.principalSubgroup K ⊔ Idele.normImage K L := by
  classical
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  -- the adjusted idèle `xb = x·(b)`
  have hxb : x * Idele.principalIdele K (adjId K m hm x) ∈
      NK.CFTLib.Arl.congruenceSubgroup K m := adjId_spec (K := K) m hm x
  have hmem : IdeleClassGroup.idealOfUnitHom K
      (x * Idele.principalIdele K (adjId K m hm x)) ∈ rayNorm K L m := by
    have h := hx
    rw [show (theta K L m hm) x = QuotientGroup.mk' (rayNorm K L m)
        (IdeleClassGroup.idealOfUnitHom K
          (x * Idele.principalIdele K (adjId K m hm x))) from rfl] at h
    rw [QuotientGroup.mk'_apply] at h
    exact (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨𝔭, h𝔭P, 𝔫, h𝔫N, hprod⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨a, haU, haEq⟩ := Subgroup.mem_map.mp h𝔭P
  have haU' : Idele.principalIdele K a ∈ NK.CFTLib.Arl.congruenceSubgroup K m :=
    Subgroup.mem_comap.mp haU
  obtain ⟨A, hA, hAeq⟩ := exists_relNormUnit_of_mem_normIdeals (K := K) (L := L) m h𝔫N
  obtain ⟨y, -, hyA⟩ := NK.CFTLib.ARL.exists_idealOf_eq_of_mem_Icoprime (K := L) (m := m) hm ⟨A, hA⟩
  have hyid : Idele.idealOf y = (A : FractionalIdeal (𝓞 L)⁰ L) := by
    have h := congrArg (fun u : (FractionalIdeal (𝓞 L)⁰ L)ˣ =>
      (u : FractionalIdeal (𝓞 L)⁰ L)) hyA
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0] at h
    exact h
  have hNy : Idele.idealOf (Idele.normIdeleHom K L y) = (𝔫 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [NK.CFTLib.ARL.idealOf_normIdeleHom, hyid]
    rw [show NK.CFTLib.ARL.relNormFI (K := K) (L := L) (A : FractionalIdeal (𝓞 L)⁰ L)
        = ((NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A :
            (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) from rfl, hAeq]
  -- the integral idèle `z`
  set xb : Idele K := x * Idele.principalIdele K (adjId K m hm x) with hxbdef
  have hxb' : xb ∈ NK.CFTLib.Arl.congruenceSubgroup K m := hxb
  set z : Idele K := xb * (Idele.principalIdele K a)⁻¹ * (Idele.normIdeleHom K L y)⁻¹ with hzdef
  have hzU : IdeleClassGroup.idealOfUnitHom K z = 1 := by
    have h𝔞 : IdeleClassGroup.idealOfUnitHom K xb = 𝔭 * 𝔫 := by
      rw [hxbdef, ← hprod]
    have hNyU : IdeleClassGroup.idealOfUnitHom K (Idele.normIdeleHom K L y) = 𝔫 := by
      refine Units.ext ?_
      rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0, hNy]
    rw [hzdef, map_mul, map_mul, map_inv, map_inv,
      NK.CFTLib.ARL.idealOfUnitHom_principalIdele, haEq, h𝔞, hNyU]
    rw [mul_assoc 𝔭 𝔫 𝔭⁻¹, mul_comm 𝔫 𝔭⁻¹, ← mul_assoc 𝔭 𝔭⁻¹ 𝔫, mul_inv_cancel, one_mul,
      mul_inv_cancel]
  have hz : z.idealOf = 1 := by
    have h := congrArg (fun u : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
      (u : FractionalIdeal (𝓞 K)⁰ K)) hzU
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0, Units.val_one] at h
    exact h
  have hzw : ∀ v : Place K, z v * Idele.normIdeleFun K L y v
      = (xb * (Idele.principalIdele K a)⁻¹) v := by
    intro v
    rw [hzdef]
    simp only [Idele.mul_apply, Idele.inv_apply, Idele.normIdeleHom_apply]
    group
  have hcong : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      NK.CFTLib.Arl.CongrAt 𝔭 m
        (z (Place.ofFinite 𝔭) * Idele.normIdeleFun K L y (Place.ofFinite 𝔭)) := by
    intro 𝔭 h𝔭
    rw [hzw (Place.ofFinite 𝔭)]
    exact (Subgroup.mul_mem _ hxb' (Subgroup.inv_mem _ haU')).1 𝔭 h𝔭
  have hpos : ∀ w : InfinitePlace K, NK.CFTLib.Arl.PosAtReal w
      (z (Place.ofInfinite w) * Idele.normIdeleFun K L y (Place.ofInfinite w)) := by
    intro w
    rw [hzw (Place.ofInfinite w)]
    exact (Subgroup.mul_mem _ hxb' (Subgroup.inv_mem _ haU')).2 w
  have hznorm : z ∈ Idele.normImage K L :=
    mem_normImage_of_congruence_mul_norm (K := K) (L := L) hm hram hadm z y hz hcong hpos
  -- assembly
  have hxb_decomp : xb = z * Idele.normIdeleHom K L y * Idele.principalIdele K a := by
    rw [hzdef]
    group
  have hxb_mem : xb ∈ Idele.principalSubgroup K ⊔ Idele.normImage K L := by
    rw [hxb_decomp]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hznorm) ?_)
      (Subgroup.mem_sup_left (Idele.mem_principalSubgroup.mpr ⟨a, rfl⟩))
    refine Subgroup.mem_sup_right ?_
    rw [Idele.normImage_eq_range]
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  have hx_eq : x = xb * (Idele.principalIdele K (adjId K m hm x))⁻¹ := by
    rw [hxbdef]
    group
  rw [hx_eq]
  exact Subgroup.mul_mem _ hxb_mem
    (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Idele.mem_principalSubgroup.mpr ⟨_, rfl⟩)))

/-! ## 4.  The main statement -/

/-- **Lang's norm index in ideal form** (Lang, *Algebraic Number Theory*, Ch. IX §5, as used in
Ch. X §2): for a finite cyclic extension `L / K` of number fields and a modulus `m > 0` divisible by
all the primes ramified in `L / K` and admissible, the subgroup `P(m) ⊔ 𝔑(m)` of the group
`I^S(m) = idealCoprimeGroup K m` of fractional ideals coprime to `(m)` is contained in `I^S(m)` and
has relative index at least `[L : K]`:

  `[L : K] ≤ (principalRay K m ⊔ normRay K L m).relIndex (idealCoprimeGroup K m)`,

where `principalRay K m = P(m)` is the group of principal ideals `(a)` with `a ≡ 1 mod (m)` and
totally positive, and `normRay K L m = 𝔑(m)` is the group generated by the relative norms
`N_{L/K}(𝔮)` of the ideals `𝔮` of `L` coprime to `(m)`.

This is the *lower* bound half of the conductor index computation; the upper bound `≤ [L:K]` is
Milne, *CFT*, Theorem 4.9, formalised in this directory as `indexPrincipalRaySupNormRayLe`.  The two
together, with the surjectivity `[I^S(m) : ker ψ] = [L:K]` of the ideal-theoretic Artin symbol, give
`ker ψ = P(m)·𝔑(m)`, hence the conductor result `artinKillsPrincipal_cyclic` and then the
ideal-theoretic reciprocity law `NK.CFTLib.ArtinReciprocityIdeal` — the single missing input of
global class field theory in this workspace.

**Route.**  Work on the idèle side; the cyclic index formula
`NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic` is unconditional:
`[C_K : N_{L/K}C_L] = [L:K]`.  The ideals coprime to `(m)` correspond to idèles by
`NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists` (with the weak-approximation
adjustment `NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust`), and this dictionary identifies
`I^S(m) ⧸ (P(m)·𝔑(m))` with the idèle quotient `𝕀_K ⧸ (Kˣ·W_m·N_{L/K}𝕀_L)`, where `W_m` is the
subgroup of idèles that are units away from `(m)` and congruent to `1` at the primes dividing `(m)`.
The hypotheses give `W_m ⊆ N_{L/K}𝕀_L`: away from `(m)` every local unit is a local norm because
`L/K` is unramified there (`hram`), and at the primes dividing `(m)` the admissibility `hadm`
supplies the congruence/conductor level; Hasse's norm principle for cyclic extensions then upgrades
these local conditions to `Kˣ·W_m·N_{L/K}𝕀_L = Kˣ·N_{L/K}𝕀_L`.  Hence
`[I^S(m) : P(m)·𝔑(m)] = [𝕀_K : Kˣ·N_{L/K}𝕀_L] = [L:K]`, which is the claimed lower bound. -/
theorem langCyclicRelIndex_proved (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L/K))] (m : ℕ)
    (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m) :
    (NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay K L m) ≤
      NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m ∧
    Module.finrank K L ≤ (NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).relIndex
      (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m) := by
  have hker_le : (theta K L m hm).ker ≤ Idele.principalSubgroup K ⊔ Idele.normImage K L :=
    theta_ker_le (K := K) (L := L) m hm hram hadm
  have hker_ge : Idele.principalSubgroup K ⊔ Idele.normImage K L ≤ (theta K L m hm).ker :=
    principalSubgroup_sup_normImage_le_ker (K := K) (L := L) m hm
  have hker_eq : (theta K L m hm).ker =
      Idele.principalSubgroup K ⊔ Idele.normImage K L := le_antisymm hker_le hker_ge
  refine ⟨principalRay_sup_normRay_le_idealCoprimeGroup (K := K) (L := L) m, ?_⟩
  calc Module.finrank K L
      = (Idele.normClassSubgroup K L).index :=
        (NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := K) (L := L)).symm
    _ = (Idele.principalSubgroup K ⊔ Idele.normImage K L).index :=
        (index_principalSubgroup_sup_normImage (K := K) (L := L) m).symm
    _ = (theta K L m hm).ker.index := by rw [hker_eq]
    _ = ((rayNorm K L m).subgroupOf (NK.CFTLib.ARL.Icoprime K m)).index :=
        (index_rayNorm_eq_ker_index (K := K) (L := L) m hm).symm
    _ = ((NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).subgroupOf
          (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m)).index := by
        rw [rayNorm, NK.CFTLib.ArtinReciprocityIdeal.principalRay_eq_ARL,
          NK.CFTLib.ArtinReciprocityIdeal.normRay_eq_normIdeals,
          NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup_eq_Icoprime]
    _ ≤ (NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).relIndex
          (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m) := le_of_eq rfl

end NK.CFTLib.ArtinReciprocityIdeal
