import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.NodeS37.henselUnitSquare
import Submission.Work.SSGRoute.NodeS37.isSquare_mk_of_rho_smul_sub_mem
import Submission.Work.SSGRoute.NodeS37.isSquare_residue_of_isSquare_mk
import Submission.Work.SSGRoute.NodeS37.localDichotomy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

/-- **The place `A` and its `↥K`-linear restriction.**  If `g` acts on `↥K` as `ρ`, then the
valuation ring of `g • A` pulled back to `↥K` is the image under `ρ` of the valuation ring of `A`
pulled back to `↥K`. -/
theorem comap_smul_eq_smul_comap {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) (ρ : K ≃ₐ[k] K)
    (hg : ∀ x : K, g (x : Ω) = (ρ x : Ω)) :
    (g • A).comap (algebraMap K Ω) = ρ • (A.comap (algebraMap K Ω)) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap]
  have h1 : g⁻¹ • (algebraMap K Ω x) = algebraMap K Ω (ρ⁻¹ • x) := by
    rw [AlgEquiv.smul_def]
    have h2 : g ((algebraMap K Ω) (ρ⁻¹ • x)) = algebraMap K Ω x := by
      change g ((↑(ρ⁻¹ • x) : Ω)) = algebraMap K Ω x
      rw [hg]
      simp
    rw [← h2]
    exact AlgEquiv.symm_apply_apply g ((algebraMap K Ω) (ρ⁻¹ • x))
  rw [h1]

/-- **`hunram` forces `ρ` to act nontrivially on the residue field `𝓞_K/𝔭`.**

`¬ IsRamifiedIn k K A` says the inertia of the place `A` (in `Gal(Ω/k)`) is contained in
`Gal(Ω/K)`, i.e. the extension `K/k` is unramified at `𝔭`.  Hence `Ideal.inertia` of `Gal(K/k)`
at `𝔭` is trivial, so the nontrivial element `ρ` is not in it: some `y` in `𝓞_K` has
`ρ y - y ≢ 0 (mod 𝔭)`. -/
theorem exists_rho_smul_sub_notMem {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hunram : ¬ SSGRoute.IsRamifiedIn k K A) :
    ∃ y : NumberField.RingOfIntegers ↥K, ρ • y - y ∉ 𝔭.asIdeal := by
  -- identify the given prime with the level prime of `A` at the level `K`
  have hlev : Work.SSGRoute.levelPrime k Ω A hA K = 𝔭 :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (by rw [← NK.Reconstruct.primeOfLevel_spec A K (NK.Reconstruct.comap_level_ne_top hA K), h𝔭])
  -- `hunram` gives ramification index one over `k`
  have hram : 𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    rw [← hlev]
    exact Work.SSGRoute.ZDataTwo.ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn
      k Ω K A hA hunram
  -- hence the inertia subgroup of `Gal(↥K/k)` at `𝔭` is trivial
  haveI : (𝔭.asIdeal.under (NumberField.RingOfIntegers k)).IsPrime := inferInstance
  have hbot : Ideal.inertia (↥K ≃ₐ[k] ↥K) 𝔭.asIdeal = ⊥ :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      (𝔭.asIdeal.under (NumberField.RingOfIntegers k)) 𝔭.asIdeal).mpr hram
  by_contra hcon
  push_neg at hcon
  have hmem : ρ ∈ Ideal.inertia (↥K ≃ₐ[k] ↥K) 𝔭.asIdeal := hcon
  rw [hbot] at hmem
  exact hρ1 (Subgroup.mem_bot.mp hmem)

/-- **The local squareness of a `ρ`-fixed element of even valuation.**

If `a ∈ Kˣ` is fixed by the involution `ρ ≠ 1` and its `𝔭`-adic valuation is a square, and `𝔭` is
the (unramified, non-dyadic) prime below the `ρ`-fixed place `A`, then the image of `a` in the
completion `K_𝔭` is a square. -/
theorem localImage_isSquare {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1)
    (a : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (hfixA : Work.SSGRoute.ZDataMup.galLift K ρ • A = A)
    (hunram : ¬ SSGRoute.IsRamifiedIn k K A)
    (hafix : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a = a)
    (heven : ∃ d : (↥K)ˣ, IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (a : ↥K)
      = (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (d : ↥K)) ^ 2) :
    ∃ c : (𝔭.adicCompletion ↥K)ˣ,
      Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom a = c ^ 2 := by
  classical
  -- ### the fixed field `L₀ = ↥K^ρ`
  let L₀ : IntermediateField k ↥K := IntermediateField.fixedField (Subgroup.zpowers ρ)
  haveI hL₀NF : NumberField ↥L₀ := inferInstance
  have hρmem : ρ ∈ Subgroup.zpowers ρ := Subgroup.mem_zpowers ρ
  -- `ρ` fixes `a`
  have hρa : ρ (a : ↥K) = (a : ↥K) := by
    have h1 : Units.map ρ.toRingEquiv.toMonoidHom a = a := by
      have h2' := hafix
      rw [Work.SSGRoute.H9.conjUnit, Work.SSGRoute.ZDataMup.galLift_spec] at h2'
      exact h2'
    have h2'' := congrArg (fun z : (↥K)ˣ => (z : ↥K)) h1
    simpa using h2''
  have haL₀ : (a : ↥K) ∈ L₀ := by
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    let H : Subgroup (↥K ≃ₐ[k] ↥K) :=
      { carrier := {x | x (a : ↥K) = (a : ↥K)}
        one_mem' := rfl
        mul_mem' := fun {x y} hx hy => by
          show (x * y) (a : ↥K) = (a : ↥K)
          rw [AlgEquiv.mul_apply, hy, hx]
        inv_mem' := fun {x} hx => by
          have h2 := AlgEquiv.symm_apply_apply x (a : ↥K)
          rw [show x (a : ↥K) = (a : ↥K) from hx] at h2
          exact h2 }
    exact Subgroup.zpowers_le.mpr (show ρ ∈ H from hρa) hf
  -- `ρ` fixes `L₀` pointwise
  have hρL₀ : ∀ x : ↥L₀, ρ (algebraMap ↥L₀ ↥K x) = algebraMap ↥L₀ ↥K x :=
    fun x => (IntermediateField.mem_fixedField_iff (Subgroup.zpowers ρ) x.1).mp x.2 ρ hρmem
  -- `ρ` as an `↥L₀`-algebra automorphism
  let ρL : ↥K ≃ₐ[↥L₀] ↥K :=
    AlgEquiv.ofBijective
      ({ ρ.toRingEquiv.toRingHom with commutes' := hρL₀ } : ↥K →ₐ[↥L₀] ↥K)
      ⟨ρ.injective, ρ.surjective⟩
  have hρLne : ρL ≠ 1 := by
    intro h
    refine hρ1 (AlgEquiv.ext fun x => ?_)
    have h2 := DFunLike.congr_fun h x
    change ρ x = x at h2
    simpa using h2
  -- `[↥K : ↥L₀] = 2`
  have hfinL₀ : Module.finrank ↥L₀ ↥K = 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers,
      orderOf_eq_prime (p := 2) hρ2 hρ1]
  haveI hFD₀ : FiniteDimensional ↥L₀ ↥K :=
    FiniteDimensional.of_finrank_pos (by rw [hfinL₀]; norm_num)
  haveI hGal₀ : IsGalois ↥L₀ ↥K := by
    refine IsGalois.of_card_aut_eq_finrank ↥L₀ ↥K ?_
    have hle : Nat.card (↥K ≃ₐ[↥L₀] ↥K) ≤ 2 := by
      have h := AlgEquiv.card_le (F := ↥L₀) (K := ↥K)
      rw [Nat.card_eq_fintype_card]
      simpa [hfinL₀] using h
    have hge : 2 ≤ Nat.card (↥K ≃ₐ[↥L₀] ↥K) := by
      haveI : Nontrivial (↥K ≃ₐ[↥L₀] ↥K) := ⟨⟨ρL, 1, hρLne⟩⟩
      rw [Nat.card_eq_fintype_card]
      exact Nat.succ_le_of_lt Fintype.one_lt_card
    omega
  -- ### the prime `𝔮₀` of `𝓞 L₀` below `𝔭`
  let 𝔮₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L₀) :=
    { asIdeal := 𝔭.asIdeal.under (NumberField.RingOfIntegers ↥L₀)
      isPrime := inferInstance
      ne_bot := Ideal.under_ne_bot (A := NumberField.RingOfIntegers ↥L₀) 𝔭.ne_bot }
  have h𝔮₀ : 𝔭.asIdeal.LiesOver 𝔮₀.asIdeal := Ideal.LiesOver.mk rfl
  -- ### step (ii): the ramification index of `𝔭` over `𝔮₀` is `1`
  have hcardG : Nat.card (↥K ≃ₐ[↥L₀] ↥K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hfinL₀]
  haveI hFinH : Finite ↥(Ideal.inertia (↥K ≃ₐ[↥L₀] ↥K) 𝔭.asIdeal) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  have hρL_not_mem : ρL ∉ Ideal.inertia (↥K ≃ₐ[↥L₀] ↥K) 𝔭.asIdeal := by
    intro hmem
    obtain ⟨y, hy⟩ := exists_rho_smul_sub_notMem ρ hρ1 A hA 𝔭 h𝔭 hunram
    refine hy ?_
    have h := hmem y
    have hsmul : (ρL • y : NumberField.RingOfIntegers ↥K) = ρ • y := rfl
    rwa [hsmul] at h
  have hbotL : Ideal.inertia (↥K ≃ₐ[↥L₀] ↥K) 𝔭.asIdeal = ⊥ := by
    rw [Subgroup.eq_bot_iff_card]
    have hle : Nat.card ↥(Ideal.inertia (↥K ≃ₐ[↥L₀] ↥K) 𝔭.asIdeal) ≤ 2 := by
      have h := Nat.card_le_card_of_injective
        (Subtype.val : ↥(Ideal.inertia (↥K ≃ₐ[↥L₀] ↥K) 𝔭.asIdeal) → (↥K ≃ₐ[↥L₀] ↥K))
        Subtype.val_injective
      rwa [hcardG] at h
    have hne : Nat.card ↥(Ideal.inertia (↥K ≃ₐ[↥L₀] ↥K) 𝔭.asIdeal) ≠ 2 := by
      intro h2
      have htop : Ideal.inertia (↥K ≃ₐ[↥L₀] ↥K) 𝔭.asIdeal = ⊤ :=
        (Subgroup.card_eq_iff_eq_top _).mp (h2.trans hcardG.symm)
      exact hρL_not_mem (htop ▸ Subgroup.mem_top ρL)
    have hpos : 0 < Nat.card ↥(Ideal.inertia (↥K ≃ₐ[↥L₀] ↥K) 𝔭.asIdeal) :=
      Nat.card_pos
    omega
  have he1 : 𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥L₀) = 1 :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      𝔮₀.asIdeal 𝔭.asIdeal).mp hbotL
  have he1' : 𝔮₀.asIdeal.ramificationIdx' 𝔭.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx 𝔮₀.asIdeal 𝔭.asIdeal 𝔮₀.ne_bot]
    exact he1
  -- ### step (iii): a `ρ`-fixed element with the valuation of `d`
  obtain ⟨d, hd⟩ := heven
  have hd_ne : IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (d : ↥K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero d)
  obtain ⟨x, hx⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective ↥L₀ 𝔮₀
    (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (d : ↥K))
  have hlies := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver ↥K 𝔮₀ 𝔭 x
  first | rw [he1', pow_one] at hlies | rw [he1, pow_one] at hlies
  have hxval : IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭
      (algebraMap ↥L₀ ↥K x) = IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (d : ↥K) :=
    hlies.symm.trans hx
  -- ### step (iv): the unit `u = a / x²`
  have hx_ne : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx
    exact hd_ne hx.symm
  have hxK_ne : (algebraMap ↥L₀ ↥K x) ≠ 0 :=
    fun h0 => hx_ne ((algebraMap ↥L₀ ↥K).injective (by rw [h0, map_zero]))
  let u : ↥K := (a : ↥K) / (algebraMap ↥L₀ ↥K x) ^ 2
  have huval : IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 u = 1 := by
    rw [show u = (a : ↥K) / (algebraMap ↥L₀ ↥K x) ^ 2 from rfl, map_div₀, map_pow,
      hxval, hd]
    exact div_self (pow_ne_zero 2 hd_ne)
  have hu_fixed : ρ u = u := by
    rw [show u = (a : ↥K) / (algebraMap ↥L₀ ↥K x) ^ 2 from rfl, map_div₀, map_pow, hρa,
      hρL₀ x]
  -- ### step (v): `ρ` preserves the prime `𝔭` and its valuation
  have hρD : ρ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := k) 𝔭 := by
    refine (Commons.NumberTheory.NumberField.Completion.smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup
      𝔭 ρ).mp ?_
    have h1 : A.comap (algebraMap ↥K Ω) = ρ • (A.comap (algebraMap ↥K Ω)) := by
      rw [← comap_smul_eq_smul_comap A (Work.SSGRoute.ZDataMup.galLift K ρ) ρ
        (fun y => Work.SSGRoute.H9.galLift_apply_coe ρ y), hfixA]
    rw [h𝔭] at h1
    exact h1.symm
  have hρval : ∀ y : ↥K, IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (ρ y) =
      IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 y :=
    fun y => Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_preserves_valuation
      (K := k) (L := ↥K) (w := 𝔭) hρD y
  -- ### step (vi): an integral lift `r` of `u` with `ρ • r - r ∈ 𝔭`
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer
    (R := NumberField.RingOfIntegers ↥K) (K := ↥K) 𝔭 (le_of_eq huval)
    (Units.mk0 (1 : WithZero (Multiplicative ℤ)) one_ne_zero)
  rw [Units.val_mk0] at hr
  have hrmem : ρ • r - r ∈ 𝔭.asIdeal := by
    refine (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (R := NumberField.RingOfIntegers ↥K) (K := ↥K) 𝔭 (ρ • r - r)).mp ?_
    have hv : (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭)
        (ρ (r : ↥K) - (r : ↥K)) < 1 := by
      have hsplit : ρ (r : ↥K) - (r : ↥K) =
          ρ ((r : ↥K) - (u : ↥K)) + ((u : ↥K) - (r : ↥K)) := by
        rw [map_sub, hu_fixed]; ring
      rw [hsplit]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [hρval]; exact hr
      · rw [show (u : ↥K) - (r : ↥K) =
            -(algebraMap (NumberField.RingOfIntegers ↥K) ↥K r - (u : ↥K)) from by ring,
          Valuation.map_neg]
        exact hr
    convert hv using 1
    congr 1
  have hsqr : IsSquare (Ideal.Quotient.mk 𝔭.asIdeal r) :=
    isSquare_mk_of_rho_smul_sub_mem ρ hρ1 hρ2 A hA 𝔭 h𝔭 hfixA hunram r hrmem
  -- ### step (vii): Hensel in the completion
  have hmemU : algebraMap ↥K (𝔭.adicCompletion ↥K) u ∈ 𝔭.adicCompletionIntegers ↥K := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, valued_adicCompletion_eq 𝔭 u]
    exact le_of_eq huval
  let U : 𝔭.adicCompletionIntegers ↥K := ⟨algebraMap ↥K (𝔭.adicCompletion ↥K) u, hmemU⟩
  have hU_mem : U - algebraMap (NumberField.RingOfIntegers ↥K) (𝔭.adicCompletionIntegers ↥K) r ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers ↥K) := by
    rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one]
    have hcoe : ((U - algebraMap (NumberField.RingOfIntegers ↥K) (𝔭.adicCompletionIntegers ↥K) r :
        𝔭.adicCompletionIntegers ↥K) : 𝔭.adicCompletion ↥K) =
        algebraMap ↥K (𝔭.adicCompletion ↥K)
          ((u : ↥K) - algebraMap (NumberField.RingOfIntegers ↥K) ↥K r) := by
      rw [map_sub]
      rfl
    rw [hcoe, valued_adicCompletion_eq 𝔭 ((u : ↥K) - algebraMap (NumberField.RingOfIntegers ↥K) ↥K r)]
    rw [show (u : ↥K) - algebraMap (NumberField.RingOfIntegers ↥K) ↥K r =
        -(algebraMap (NumberField.RingOfIntegers ↥K) ↥K r - (u : ↥K)) from by ring, Valuation.map_neg]
    exact hr
  have hsq_res : IsSquare (IsLocalRing.residue (𝔭.adicCompletionIntegers ↥K) U) :=
    isSquare_residue_of_isSquare_mk 𝔭 U r hU_mem hsqr
  have hUisUnit : IsUnit U := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    have hmem : U ∈ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers ↥K) :=
      (IsLocalRing.residue_eq_zero_iff U).mp h0
    rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one]
      at hmem
    rw [show ((U : 𝔭.adicCompletionIntegers ↥K) : 𝔭.adicCompletion ↥K) =
        algebraMap ↥K (𝔭.adicCompletion ↥K) (u : ↥K) from rfl, valued_adicCompletion_eq 𝔭 u,
      huval] at hmem
    exact lt_irrefl 1 hmem
  have h2unit : IsUnit (2 : 𝔭.adicCompletionIntegers ↥K) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem2
    have hlt2 : (𝔭.adicCompletionIntegers ↥K).valuation
        ((2 : 𝔭.adicCompletionIntegers ↥K) : 𝔭.adicCompletion ↥K) < 1 :=
      (ValuationSubring.valuation_lt_one_iff (𝔭.adicCompletionIntegers ↥K)
        (2 : 𝔭.adicCompletionIntegers ↥K)).mp hmem2
    have hcoe : ((2 : 𝔭.adicCompletionIntegers ↥K) : 𝔭.adicCompletion ↥K) =
        algebraMap ↥K (𝔭.adicCompletion ↥K) (2 : ↥K) := by
      rw [map_ofNat]; rfl
    rw [hcoe] at hlt2
    exact h2 ((adic_valuation_lt_one_iff A 𝔭 h𝔭 (2 : ↥K) two_ne_zero).mpr hlt2)
  obtain ⟨c, hc⟩ := exists_sq_of_residue_isSquare 𝔭 h2unit (IsUnit.unit hUisUnit) (by
    rw [IsUnit.unit_spec]; exact hsq_res)
  have hc' : (c : 𝔭.adicCompletion ↥K) ^ 2 =
      algebraMap ↥K (𝔭.adicCompletion ↥K) (u : ↥K) := by
    rw [hc]; rfl
  -- ### step (viii): assembly
  have hu_ne : u ≠ 0 := by
    intro h0
    have h : (0 : WithZero (Multiplicative ℤ)) = 1 := by simpa [h0] using huval
    exact zero_ne_one h
  have hxa : (a : ↥K) = (algebraMap ↥L₀ ↥K x) ^ 2 * u := by
    show (a : ↥K) = (algebraMap ↥L₀ ↥K x) ^ 2 * ((a : ↥K) / (algebraMap ↥L₀ ↥K x) ^ 2)
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hxK_ne)]
  refine ⟨Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K))
      (Units.mk0 (algebraMap ↥L₀ ↥K x) hxK_ne) * c, Units.ext ?_⟩
  rw [Units.coe_map, Units.val_pow_eq_pow_val, Units.val_mul, Units.coe_map, Units.val_mk0,
    mul_pow, hc', hxa, map_mul, map_pow]
  first | rfl | ring


theorem inertSquareOfRhoFixed {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1)
    (a : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (hfixA : Work.SSGRoute.ZDataMup.galLift K ρ • A = A)
    (hunram : ¬ SSGRoute.IsRamifiedIn k K A)
    (hafix : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a = a)
    (heven : ∃ d : (↥K)ˣ, IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (a : ↥K)
      = (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (d : ↥K)) ^ 2) :
    ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a u = 0 := by
  exact killsLocalGroup_of_localSquare (K := K) ζ hζ hζK a A hA 𝔭 h𝔭
    (localImage_isSquare ρ hρ1 hρ2 a A hA 𝔭 h𝔭 h2 hfixA hunram hafix heven)

end Work.SSGRoute.NodeS37
