import Mathlib.Tactic.Have
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.count_map_eq_ramificationIdx_mul_count
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.localNormFinite_sub_one_le_of_val
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.spanUnit_mem_principalRayId_of_mem_congruenceSubgroupId
import Submission.Work.SSGRoute.ZDataMup.IdPort.Adjust
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.IdealModulusKernel

open NK.CFTLib.ArtinReciprocityIdeal
open Work.SSGRoute.ZDataMup.IdPort
open Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain



open NK.GlobalCFT NK.CFTLib.ArtinReciprocityIdeal


theorem exists_idealOf_eq_of_mem_idealCoprimeGroupId
    {K : Type} [Field K] [NumberField K]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    (𝔞 : NK.CFTLib.ArtinReciprocityIdeal.Frac K)
    (h𝔞 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪 𝔞) :
    ∃ x : NK.GlobalCFT.Idele K,
      x ∈ NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K 𝔪 ∧
        NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K x = 𝔞 := by
  classical
  set f : HeightOneSpectrum (𝓞 K) → ℤ :=
    fun 𝔭 => FractionalIdeal.count K 𝔭 (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hf_def
  have hf : ∀ᶠ 𝔭 in Filter.cofinite, f 𝔭 = 0 :=
    FractionalIdeal.finite_factors (K := K) (I := (𝔞 : FractionalIdeal (𝓞 K)⁰ K))
  refine ⟨IdeleClassGroup.ideleOfFun K f hf, ?_, ?_⟩
  · rw [mem_congruenceSubgroupId]
    constructor
    · intro 𝔭 h𝔭
      have hf0 : f 𝔭 = 0 := by
        rw [hf_def]
        exact h𝔞 𝔭 ((dvdPrime_iff_one_le_count h𝔪 𝔭).mpr h𝔭)
      have hx1 : IdeleClassGroup.ideleOfFun K f hf (Place.ofFinite 𝔭) = 1 := by
        apply Units.ext
        change ((IdeleClassGroup.unifUnit K 𝔭 ^ (f 𝔭) : (𝔭.adicCompletion K)ˣ) :
          𝔭.adicCompletion K) = 1
        rw [hf0, zpow_zero]
        rfl
      rw [hx1]
      exact congrAtId_one 𝔭 𝔪
    · intro w
      exact NK.CFTLib.Arl.posAtReal_one w
  · refine Units.ext ?_
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0]
    exact IdeleClassGroup.fractionalIdeal_eq_of_count_eq (Idele.idealOf_ne_zero _) 𝔞.ne_zero
      (fun 𝔭 => by rw [IdeleClassGroup.count_idealOf_ideleOfFun])




set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField nonZeroDivisors WithZero NumberField.LiesOver
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum



open NK.GlobalCFT

theorem normIdeleHom_mem_congruenceSubgroupId
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    {x : NK.GlobalCFT.Idele L}
    (hx : x ∈ NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId L
      (Ideal.map (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) 𝔪)) :
    NK.GlobalCFT.Idele.normIdeleHom K L x ∈
      NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K 𝔪 := by
  classical
  obtain ⟨hxfin, hxinf⟩ := NK.CFTLib.ArtinReciprocityIdeal.mem_congruenceSubgroupId.mp hx
  have hmap_ne_bot : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪 ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot h𝔪
  rw [NK.CFTLib.ArtinReciprocityIdeal.mem_congruenceSubgroupId]
  refine ⟨?_, ?_⟩
  · -- ## the finite places
    intro 𝔭 h𝔭
    -- the level `c = count K 𝔭 𝔪` of the congruence condition at `𝔭`, as a natural number
    set c : ℕ := (FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (𝓞 K)⁰ K)).toNat with hc
    have hc_nonneg : 0 ≤ FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (𝓞 K)⁰ K) :=
      le_trans zero_le_one h𝔭
    have hc_cast : (c : ℤ) = FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (𝓞 K)⁰ K) :=
      Int.toNat_of_nonneg hc_nonneg
    -- a uniformizer `π` of `K_𝔭` and the level element `y = π ^ c`
    obtain ⟨π, hπval, -⟩ :=
      Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one 𝔭
    set y : 𝔭.adicCompletionIntegers K := π ^ c with hy
    have hyval : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (y : 𝔭.adicCompletion K) = WithZero.exp (-(c : ℤ)) := by
      rw [hy,
        show ((π ^ c : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)
            = (π : 𝔭.adicCompletion K) ^ c from by push_cast; ring,
        Valuation.map_pow, hπval, ← WithZero.exp_nsmul]
      congr 1
      simp
    have hy_ne : y ≠ 0 := by
      intro h
      have h2 : (WithZero.exp (-(c : ℤ)) : WithZero (Multiplicative ℤ)) = 0 := by
        rw [← hyval, h]
        simp
      exact WithZero.exp_ne_zero h2
    -- unfold the `𝔭`-component of the norm
    rw [NK.CFTLib.ArtinReciprocityIdeal.CongrAtId, NK.GlobalCFT.Idele.normIdeleHom_apply,
      NK.GlobalCFT.Idele.normIdeleFun_ofFinite, Units.coe_prod, Finset.attach_eq_univ]
    set a : {q' : HeightOneSpectrum (𝓞 L) // q' ∈ Place.primesOverFinite (K := K) (L := L) 𝔭} →
        𝔭.adicCompletion K := fun q' => ((Place.localNormFinite q'.1 𝔭
          ((Place.mem_primesOverFinite (K := K) (L := L) (Q := 𝔭) (q := q'.1)).mp q'.2)
          (x (Place.ofFinite q'.1)) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) - 1 with ha
    have hprod : (∏ q' : {q' : HeightOneSpectrum (𝓞 L) //
        q' ∈ Place.primesOverFinite (K := K) (L := L) 𝔭}, (1 + a q'))
        = ∏ q' : {q' : HeightOneSpectrum (𝓞 L) //
            q' ∈ Place.primesOverFinite (K := K) (L := L) 𝔭},
          ((Place.localNormFinite q'.1 𝔭
            ((Place.mem_primesOverFinite (K := K) (L := L) (Q := 𝔭) (q := q'.1)).mp q'.2)
            (x (Place.ofFinite q'.1)) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) := by
      refine Finset.prod_congr rfl fun q' _ => ?_
      rw [ha]
      ring
    rw [← hprod]
    refine NK.CFTLib.Arl.val_prod_one_add_sub_one_le
      (v := (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ))))
      Finset.univ a (NK.CFTLib.ArtinReciprocityIdeal.exp_neg_count_lt_one 𝔭 𝔪 h𝔭) ?_
    -- each local factor `N_{L_{q'}/K_𝔭}(x_{q'})` is `≡ 1` modulo the level of `𝔪` at `𝔭`
    intro q' _
    have hq' : q'.1.asIdeal.LiesOver 𝔭.asIdeal :=
      (Place.mem_primesOverFinite (K := K) (L := L) (Q := 𝔭) (q := q'.1)).mp q'.2
    -- the local congruence hypothesis at `q'`, from `hx`
    have hDvd : NK.CFTLib.ArtinReciprocityIdeal.DvdPrime
        (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪) q'.1 := by
      have h1 : 𝔪 ≤ 𝔭.asIdeal :=
        (NK.CFTLib.ArtinReciprocityIdeal.dvdPrime_iff_one_le_count h𝔪 𝔭).mpr h𝔭
      refine le_trans (Ideal.map_mono h1) ?_
      rw [Ideal.map_le_iff_le_comap,
        Ideal.LiesOver.over (p := 𝔭.asIdeal) (P := q'.1.asIdeal)]
    have hcountL : 1 ≤ FractionalIdeal.count L q'.1
        ((Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪 : Ideal (𝓞 L)) :
          FractionalIdeal (𝓞 L)⁰ L) :=
      (NK.CFTLib.ArtinReciprocityIdeal.dvdPrime_iff_one_le_count (K := L) hmap_ne_bot q'.1).mp hDvd
    have hxq := hxfin q'.1 hcountL
    -- the value of the level element `y` inside `L_{q'}` is the level of `𝔪` at `q'`
    have hmapval : Valued.v (R := q'.1.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 q'.1 hq' (y : 𝔭.adicCompletion K))
        = WithZero.exp (-(((q'.1.asIdeal.ramificationIdx (𝓞 K) : ℤ)) *
            FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (𝓞 K)⁰ K))) := by
      rw [Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow, hyval,
        ← WithZero.exp_nsmul]
      congr 1
      rw [hc_cast]
      simp [nsmul_eq_mul]
    have hu : Valued.v (R := q'.1.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (((x (Place.ofFinite q'.1) : (q'.1.adicCompletion L)ˣ) : q'.1.adicCompletion L) - 1) ≤
        Valued.v (R := q'.1.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 q'.1 hq' (y : 𝔭.adicCompletion K)) := by
      rw [hmapval]
      refine le_trans hxq (le_of_eq ?_)
      rw [count_map_eq_ramificationIdx_mul_count 𝔭 q'.1 hq' 𝔪 h𝔪]
    have hlocal := localNormFinite_sub_one_le_of_val 𝔭 q'.1 hq' y hy_ne
      (x (Place.ofFinite q'.1)) hu
    rw [hyval] at hlocal
    rw [← hc_cast]
    exact hlocal
  · -- ## the archimedean places
    intro w
    let f : {w' : InfinitePlace L // w' ∈ Place.fiberInfinite (K := K) (L := L) w} →
        (w.Completion)ˣ := fun w' => by
      letI : w'.1.LiesOver w :=
        (Place.mem_fiberInfinite (K := K) (L := L) (v := w) (w := w'.1)).mp w'.2
      exact Place.localNormInfinite w'.1 w (x (Place.ofInfinite w'.1))
    have hgoal : (Idele.normIdeleHom K L x) (Place.ofInfinite w)
        = ∏ w' : {w' : InfinitePlace L // w' ∈ Place.fiberInfinite (K := K) (L := L) w}, f w' := by
      rw [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofInfinite, Finset.attach_eq_univ]
    rw [hgoal]
    refine NK.CFTLib.Arl.posAtReal_prod Finset.univ f ?_
    intro w' _
    letI : w'.1.LiesOver w :=
      (Place.mem_fiberInfinite (K := K) (L := L) (v := w) (w := w'.1)).mp w'.2
    exact NK.CFTLib.Arl.posAtReal_localNormInfinite w w'.1 (x (Place.ofInfinite w'.1)) (hxinf w'.1)



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain



open NK.GlobalCFT NK.CFTLib.ArtinReciprocityIdeal


theorem normIdeals_le_normRayId_of_span_le_aux
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (M : ℕ) (hM : 0 < M)
    (hle : Ideal.span {(M : NumberField.RingOfIntegers K)} ≤ 𝔪) :
    NK.CFTLib.ARL.normIdeals K L M ≤
      NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
  classical
  rw [NK.CFTLib.ARL.normIdeals, Subgroup.closure_le]
  rintro A ⟨𝔅, rfl⟩
  refine Subgroup.subset_closure ⟨𝔅.1, 𝔅.2.1, ?_, ?_⟩
  · -- the ideal `𝔅.1` is coprime to `𝔪𝓞 L`
    intro 𝔓 h𝔓
    have hMmem : (M : 𝓞 L) ∈ 𝔓.asIdeal := by
      have h1 : (M : 𝓞 K) ∈ 𝔪 := hle (Ideal.subset_span (Set.mem_singleton _))
      have h2 : algebraMap (𝓞 K) (𝓞 L) (M : 𝓞 K) ∈ 𝔓.asIdeal :=
        h𝔓 (Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) h1)
      rwa [map_natCast] at h2
    have hndvd : ¬ 𝔓.asIdeal ∣ 𝔅.1 := 𝔅.2.2 𝔓 hMmem
    have h1 : ¬ (1 ≤ FractionalIdeal.count L 𝔓 (𝔅.1 : FractionalIdeal (𝓞 L)⁰ L)) :=
      fun h => hndvd
        ((dvdPrime_iff_dvd' (𝔪 := 𝔅.1) (𝔭 := 𝔓)).mp
          ((dvdPrime_iff_one_le_count 𝔅.2.1 𝔓).mpr h))
    have h2 : 0 ≤ FractionalIdeal.count L 𝔓 (𝔅.1 : FractionalIdeal (𝓞 L)⁰ L) :=
      FractionalIdeal.count_coe_nonneg L 𝔓 𝔅.1
    show FractionalIdeal.count L 𝔓
      ((idealUnit 𝔅.1 𝔅.2.1 : Frac L) : FractionalIdeal (𝓞 L)⁰ L) = 0
    rw [show ((idealUnit 𝔅.1 𝔅.2.1 : Frac L) : FractionalIdeal (𝓞 L)⁰ L)
        = (𝔅.1 : FractionalIdeal (𝓞 L)⁰ L) from rfl]
    omega
  · -- the two `Units` have the same underlying fractional ideal
    apply Units.ext
    rfl


theorem idealOfUnitHom_normIdeleHom_mem_normRayId_aux
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (M : ℕ) (hM : 0 < M)
    (hle : Ideal.span {(M : NumberField.RingOfIntegers K)} ≤ 𝔪)
    {y : NK.GlobalCFT.Idele L}
    (hy : y ∈ NK.CFTLib.Arl.congruenceSubgroup L M) :
    NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K (NK.GlobalCFT.Idele.normIdeleHom K L y) ∈
      NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
  classical
  have hA : ∀ 𝔓 : HeightOneSpectrum (𝓞 L), (M : 𝓞 L) ∈ 𝔓.asIdeal →
      FractionalIdeal.count L 𝔓 (Units.mk0 (NK.GlobalCFT.Idele.idealOf y)
        (NK.GlobalCFT.Idele.idealOf_ne_zero y) : FractionalIdeal (𝓞 L)⁰ L) = 0 := by
    intro 𝔓 h𝔓
    rw [Units.val_mk0]
    exact NK.CFTLib.ARL.count_idealOf_eq_zero_of_congruence hy 𝔓 h𝔓
  have hmemN := NK.CFTLib.ARL.relNormUnit_mem_normIdeals (K := K) (L := L) M
    (A := Units.mk0 (NK.GlobalCFT.Idele.idealOf y)
      (NK.GlobalCFT.Idele.idealOf_ne_zero y)) hA
  have hmemR := normIdeals_le_normRayId_of_span_le_aux 𝔪 M hM hle hmemN
  convert hmemR using 1
  apply Units.ext
  simp only [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0, NK.CFTLib.ARL.relNormUnit]
  exact NK.CFTLib.ARL.idealOf_normIdeleHom y

theorem idealOf_mem_principalRayId_sup_normRayId
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    {y : NK.GlobalCFT.Idele L} {β : Kˣ} {z : NK.GlobalCFT.Idele K}
    (hz : z ∈ NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K 𝔪)
    (hzy : z = NK.GlobalCFT.Idele.normIdeleHom K L y *
      NK.GlobalCFT.Idele.principalIdele K β) :
    NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K z ∈
      NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
  classical
  -- The natural modulus `M = absNorm 𝔪` satisfies `(M) ⊆ 𝔪`, hence `U(M) ≤ U(𝔪)`.
  have hMpos : 0 < Ideal.absNorm 𝔪 :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨𝔪, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using h𝔪)⟩
  have hle : Ideal.span {(Ideal.absNorm 𝔪 : 𝓞 K)} ≤ 𝔪 :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.absNorm_mem 𝔪))
  -- Step 1: adjust `y` in `L` so that `y' = y · (d) ∈ U(M)`.
  obtain ⟨d, hd⟩ := NK.CFTLib.ARL.exists_adjust_congruenceSubgroup L (Ideal.absNorm 𝔪) hMpos y
  set y' : NK.GlobalCFT.Idele L := y * NK.GlobalCFT.Idele.principalIdele L d with hy'def
  have hd' : y' ∈ NK.CFTLib.Arl.congruenceSubgroup L (Ideal.absNorm 𝔪) := hd
  -- Step 2: `N y' ∈ U(M) ⊆ U(𝔪)`.
  have hNyM : NK.GlobalCFT.Idele.normIdeleHom K L y' ∈
      NK.CFTLib.Arl.congruenceSubgroup K (Ideal.absNorm 𝔪) :=
    NK.CFTLib.Arl.normIdeleHom_mem_congruenceSubgroup (K := K) (L := L) (Ideal.absNorm 𝔪) hMpos hd'
  have hNy'mem : NK.GlobalCFT.Idele.normIdeleHom K L y' ∈
      NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K 𝔪 := by
    have h1 : NK.GlobalCFT.Idele.normIdeleHom K L y' ∈
        NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K
          (Ideal.span {(Ideal.absNorm 𝔪 : 𝓞 K)}) := by
      rwa [← IdPort.congruenceSubgroup_eq_congruenceSubgroupId
        (K := K) hMpos]
    exact IdPort.congruenceSubgroupId_mono
      (IdPort.span_nat_ne_bot hMpos) hle h1
  -- Step 3: the leftover principal idèle `β / N(d)` is congruent to `1` modulo `𝔪`.
  have hNy'_eq : NK.GlobalCFT.Idele.normIdeleHom K L y' =
      NK.GlobalCFT.Idele.normIdeleHom K L y *
        NK.GlobalCFT.Idele.principalIdele K (Units.map (Algebra.norm K) d) := by
    rw [hy'def, map_mul, NK.GlobalCFT.Idele.normIdeleHom_principalIdele]
  have hprinc : NK.GlobalCFT.Idele.principalIdele K (β / Units.map (Algebra.norm K) d) =
      z * (NK.GlobalCFT.Idele.normIdeleHom K L y')⁻¹ := by
    rw [hzy, hNy'_eq, map_div]
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hprinc_mem : NK.GlobalCFT.Idele.principalIdele K (β / Units.map (Algebra.norm K) d) ∈
      NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K 𝔪 := by
    rw [hprinc]
    exact Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hNy'mem)
  have hray : NK.CFTLib.ArtinReciprocityIdeal.spanUnit (K := K)
      (β / Units.map (Algebra.norm K) d) ∈
      NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 :=
    spanUnit_mem_principalRayId_of_mem_congruenceSubgroupId 𝔪 h𝔪 _ hprinc_mem
  -- Step 4: `idealOf (N y') ∈ 𝔑(𝔪)`.
  have hnorm : NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K
      (NK.GlobalCFT.Idele.normIdeleHom K L y') ∈
      NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 :=
    idealOfUnitHom_normIdeleHom_mem_normRayId_aux 𝔪 (Ideal.absNorm 𝔪) hMpos hle hd'
  -- Step 5: assemble `z = N y' · (β / N d)`.
  have hz_split : z = NK.GlobalCFT.Idele.normIdeleHom K L y' *
      NK.GlobalCFT.Idele.principalIdele K (β / Units.map (Algebra.norm K) d) := by
    rw [hprinc]
    simp
  have hkey : NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K z =
      NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K (NK.GlobalCFT.Idele.normIdeleHom K L y') *
        NK.CFTLib.ArtinReciprocityIdeal.spanUnit (K := K) (β / Units.map (Algebra.norm K) d) := by
    rw [hz_split, map_mul, IdPort.idealOfUnitHom_principalIdele']
    rfl
  rw [hkey]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hnorm) (Subgroup.mem_sup_left hray)




set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain



open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]


lemma spanUnitHom_mem_rayNormClId {𝔪 : Ideal (𝓞 K)} {γ : Kˣ}
    (hγ : Idele.principalIdele K γ ∈ congruenceSubgroupId K 𝔪) :
    spanUnitHom K γ ∈ IdPort.rayNormClId K L 𝔪 :=
  Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩)


lemma mk'_rayNormClId_mul_spanUnit {𝔪 : Ideal (𝓞 K)} {γ : Kˣ}
    (hγ : Idele.principalIdele K γ ∈ congruenceSubgroupId K 𝔪) (𝔞 : Frac K) :
    QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪) (𝔞 * spanUnitHom K γ)
      = QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪) 𝔞 := by
  have hmk : QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪) (spanUnitHom K γ) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (spanUnitHom_mem_rayNormClId (K := K) hγ)
  rw [map_mul, hmk, ← map_one (QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪)), ← map_mul, mul_one]


lemma thetaIdFun_norm_eq_one {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (y : Idele L) :
    IdPort.thetaIdFun (K := K) (L := L) 𝔪 h𝔪 (Idele.normIdeleHom K L y) = 1 := by
  have hmem : IdeleClassGroup.idealOfUnitHom K (Idele.normIdeleHom K L y *
      Idele.principalIdele K (IdPort.adjId 𝔪 h𝔪 (Idele.normIdeleHom K L y))) ∈ IdPort.rayNormClId K L 𝔪 := by
    rw [IdPort.rayNormClId, principalRayClId_eq_principalRayId h𝔪]
    exact idealOf_mem_principalRayId_sup_normRayId
      (K := K) (L := L) 𝔪 h𝔪 (IdPort.adjId_spec h𝔪 _) rfl
  rw [IdPort.thetaIdFun]
  exact (QuotientGroup.eq_one_iff _).mpr hmem


lemma thetaId_norm_eq_one {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (y : Idele L) :
    IdPort.thetaId K L 𝔪 h𝔪 (Idele.normIdeleHom K L y) = 1 := by
  rw [IdPort.thetaId_apply]
  exact thetaIdFun_norm_eq_one (K := K) (L := L) h𝔪 y


lemma principalSubgroup_sup_normImage_le_ker_thetaId {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (Idele.principalSubgroup K ⊔ Idele.normImage K L) ≤ (IdPort.thetaId K L 𝔪 h𝔪).ker := by
  rw [Idele.normImage_eq_range]
  refine sup_le ?_ ?_
  · rintro x ⟨α, rfl⟩
    exact IdPort.principalSubgroup_le_ker_thetaId (K := K) (L := L) h𝔪 ⟨α, rfl⟩
  · rintro x ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    exact thetaId_norm_eq_one (K := K) (L := L) h𝔪 y


lemma thetaId_range {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (IdPort.thetaId K L 𝔪 h𝔪).range
      = (idealCoprimeGroupId 𝔪).map (QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (IdPort.adjId 𝔪 h𝔪 x)), ?_, ?_⟩
    · refine (mem_idealCoprimeGroupId_iff
        (K := K) 𝔪 (IdeleClassGroup.idealOfUnitHom K
          (x * Idele.principalIdele K (IdPort.adjId 𝔪 h𝔪 x)))).mpr ?_
      intro 𝔭 h𝔭
      exact count_idealOf_eq_zero_of_congruenceId (IdPort.adjId_spec h𝔪 x) 𝔭
        ((dvdPrime_iff_one_le_count h𝔪 𝔭).mp h𝔭)
    · rw [IdPort.thetaId_apply]
      rfl
  · rintro ⟨𝔞, h𝔞, rfl⟩
    obtain ⟨z, hz, hzide⟩ :=
      exists_idealOf_eq_of_mem_idealCoprimeGroupId
        (K := K) 𝔪 h𝔪 𝔞
        ((mem_idealCoprimeGroupId_iff 𝔪 𝔞).mp
          h𝔞)
    have hzadj : Idele.principalIdele K (IdPort.adjId 𝔪 h𝔪 z) ∈ congruenceSubgroupId K 𝔪 :=
      mem_congruenceSubgroupId_of_mul_eq (x := z * Idele.principalIdele K (IdPort.adjId 𝔪 h𝔪 z))
        (y := z) (IdPort.adjId_spec h𝔪 z) hz (γ := IdPort.adjId 𝔪 h𝔪 z) rfl
    refine ⟨z, ?_⟩
    rw [IdPort.thetaId_apply, IdPort.thetaIdFun_eq_mk (K := K) (L := L) h𝔪 (x := z)
      (c := IdPort.adjId 𝔪 h𝔪 z) (IdPort.adjId_spec h𝔪 z)]
    rw [show IdeleClassGroup.idealOfUnitHom K (z * Idele.principalIdele K (IdPort.adjId 𝔪 h𝔪 z))
        = IdeleClassGroup.idealOfUnitHom K z * spanUnitHom K (IdPort.adjId 𝔪 h𝔪 z) by
      rw [map_mul, idealOfUnitHom_principalIdele']]
    rw [hzide]
    exact mk'_rayNormClId_mul_spanUnit (K := K) (L := L) hzadj 𝔞


lemma index_rayNormId_eq_ker_index {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    ((IdPort.rayNormClId K L 𝔪).subgroupOf (idealCoprimeGroupId 𝔪)).index
      = (IdPort.thetaId K L 𝔪 h𝔪).ker.index := by
  have hfker : ((QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪)).comp
        (idealCoprimeGroupId 𝔪).subtype).ker
      = (IdPort.rayNormClId K L 𝔪).subgroupOf (idealCoprimeGroupId 𝔪) := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h1 : ((IdPort.rayNormClId K L 𝔪).subgroupOf (idealCoprimeGroupId 𝔪)).index
      = Nat.card ((idealCoprimeGroupId 𝔪) ⧸ ((QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪)).comp
              (idealCoprimeGroupId 𝔪).subtype).ker) := by
    rw [Subgroup.index_eq_card, hfker]
  have h2 : (IdPort.thetaId K L 𝔪 h𝔪).ker.index = Nat.card (IdPort.thetaId K L 𝔪 h𝔪).range := by
    rw [Subgroup.index_eq_card]
    have hker'' : (IdPort.thetaId K L 𝔪 h𝔪).rangeRestrict.ker = (IdPort.thetaId K L 𝔪 h𝔪).ker := by
      ext x
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [← hker'']
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (IdPort.thetaId K L 𝔪 h𝔪).rangeRestrict
      (fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩)).toEquiv
  have h3 : Nat.card ((idealCoprimeGroupId 𝔪) ⧸
        ((QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪)).comp
          (idealCoprimeGroupId 𝔪).subtype).ker)
      = Nat.card (IdPort.thetaId K L 𝔪 h𝔪).range := by
    have hsurj : Function.Surjective (((QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪)).comp
        (idealCoprimeGroupId 𝔪).subtype).rangeRestrict) :=
      fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩
    have hrange : ((QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪)).comp
        (idealCoprimeGroupId 𝔪).subtype).range = (IdPort.thetaId K L 𝔪 h𝔪).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype,
        ← thetaId_range (K := K) (L := L) h𝔪]
    have hker' : ((QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪)).comp
        (idealCoprimeGroupId 𝔪).subtype).rangeRestrict.ker
        = ((QuotientGroup.mk' (IdPort.rayNormClId K L 𝔪)).comp
            (idealCoprimeGroupId 𝔪).subtype).ker := by
      ext x
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [← hker', Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
      hrange]
  rw [h1, h3, h2]




/-! ## The index inequality -/

/-- **The index of `Kˣ · N_{L/K} 𝕀 L` in `𝕀 K` is the index of the idèlic norm class
subgroup.**  Both are the cardinality of the ray class group `C_K ⧸ N_{L/K} C_L`. -/
lemma index_principalSubgroup_sup_normImage' (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    (NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L).index =
      (NK.GlobalCFT.Idele.normClassSubgroup K L).index := by
  rw [Subgroup.index_eq_card]
  exact (NK.GlobalCFTdeep.SecondInequality.index_normClassSubgroup_eq_card_rayClassGroup
    (K := K) (L := L)).symm

/-- **The index of `P(𝔪)·𝔑(𝔪)` in `I(𝔪)` is at most the idèlic norm index.** -/
theorem indexLeIdId {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥) :
    Nat.card (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪 ⧸
        (NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪).subgroupOf
          (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪))
      ≤ (NK.GlobalCFT.Idele.normClassSubgroup K L).index := by
  classical
  have hR : IdPort.rayNormClId K L 𝔪 =
      NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
    rw [IdPort.rayNormClId,
      NK.CFTLib.ArtinReciprocityIdeal.principalRayClId_eq_principalRayId h𝔪]
  rw [← hR]
  have hker : (NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L) ≤
      (IdPort.thetaId K L 𝔪 h𝔪).ker :=
    principalSubgroup_sup_normImage_le_ker_thetaId (K := K) (L := L) h𝔪
  haveI hVfin : (NK.GlobalCFT.Idele.principalSubgroup K ⊔
      NK.GlobalCFT.Idele.normImage K L).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by
      rw [index_principalSubgroup_sup_normImage' K L]
      exact NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := K) (L := L))
  calc Nat.card (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪 ⧸
          (IdPort.rayNormClId K L 𝔪).subgroupOf
            (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪))
      = ((IdPort.rayNormClId K L 𝔪).subgroupOf
            (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪)).index :=
        (Subgroup.index_eq_card _).symm
    _ = (IdPort.thetaId K L 𝔪 h𝔪).ker.index :=
        index_rayNormId_eq_ker_index (K := K) (L := L) h𝔪
    _ ≤ (NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.normImage K L).index :=
        Subgroup.index_antitone hker
    _ = (NK.GlobalCFT.Idele.normClassSubgroup K L).index :=
        index_principalSubgroup_sup_normImage' K L

end Work.SSGRoute.ZDataMup.IdealModulusKernel
