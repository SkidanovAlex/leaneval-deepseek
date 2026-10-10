import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E7cC.exists_level_unramified_p_dvd_inertiaDeg
import Submission.Work.SSGRoute.Sha2Lib.exists_mem_stabilizer_restrictNormalHom_eq
import Submission.Work.SSGRoute.Sha2Lib.exists_unramified_inert_cyclic_level
import Submission.Work.SSGRoute.Sha2Lib.inertia_eq_bot_of_sup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open scoped IntermediateField NumberField

set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-! ## A spelling shim for the finite place of a nonzero prime

The requested statement of `exists_unramified_character_with_p_dvd_residueDeg` is written with the
token sequence `NK.GlobalCFT.place ofFinite q'`, which is a slip for the constructor
`NK.GlobalCFT.Place.ofFinite q'` (the identifier `NK.GlobalCFT.place` does not otherwise exist in
the workspace, so the requested text is unreadable as written).  The two declarations below give
that exact token sequence its intended meaning, so that the theorem can be stated *verbatim* as
requested.  They are definitionally transparent: `NK.GlobalCFT.place ofFinite q'` is
`NK.GlobalCFT.Place.ofFinite q'`, the ordinary finite place attached to `q'`. -/

/-- The finite place attached to a nonzero prime ideal of a number field.  This is the shim that
makes the requester's spelling `NK.GlobalCFT.place ofFinite q` readable; it is
`NK.GlobalCFT.Place.ofFinite q`. -/
def _root_.ofFinite {K : Type*} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : NK.GlobalCFT.Place K :=
  NK.GlobalCFT.Place.ofFinite q

/-- Application shim: `NK.GlobalCFT.place f q` is `f q`.  Named so that the requester's spelling
`NK.GlobalCFT.place ofFinite q` resolves to `NK.GlobalCFT.Place.ofFinite q`. -/
def _root_.NK.GlobalCFT.place {K : Type*} [Field K] [NumberField K]
    (f : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.GlobalCFT.Place K := f q

theorem exists_unramified_character_with_p_dvd_residueDeg (p : ℕ) [Fact p.Prime] (k K : Type)
    [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L)),
      q'.asIdeal.LiesOver q.asIdeal ∧
      q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
      p ∣ q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ∧
      ∃ χ : (↥L ≃ₐ[k] ↥L) →* Multiplicative (ZMod p),
        (∀ σ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' σ → χ σ = 1) ∧
        (∃ σ : ↥L ≃ₐ[k] ↥L,
          σ ∈ SSGRoute.PTExt.decompK (NK.GlobalCFT.place ofFinite q') ∧ χ σ ≠ 1) := by
  classical
  haveI hp : p.Prime := Fact.out
  haveI hΩchar : CharZero Ω :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  -- ## the finite place `Q` of `k` below `q`
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    ⟨q.asIdeal.under (NumberField.RingOfIntegers k), inferInstance,
      Ideal.under_ne_bot _ q.ne_bot⟩
  have hQlies : q.asIdeal.LiesOver Q.asIdeal := Ideal.over_under q.asIdeal
  haveI : q.asIdeal.LiesOver Q.asIdeal := hQlies
  -- ## the residue cardinality `N` of `q` and the cyclotomic exponent `m`
  haveI hFinq : Finite (NumberField.RingOfIntegers K ⧸ q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
  haveI hFintq : Fintype (NumberField.RingOfIntegers K ⧸ q.asIdeal) := Fintype.ofFinite _
  let N : ℕ := Nat.card (NumberField.RingOfIntegers K ⧸ q.asIdeal)
  have hN2 : 2 ≤ N := by
    rw [show N = Nat.card (NumberField.RingOfIntegers K ⧸ q.asIdeal) from rfl,
      Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  let m : ℕ := N ^ p - 1
  have hmpos : 0 < m := by
    have h1 : 1 < N ^ p := Nat.one_lt_pow hp.ne_zero (by omega)
    rw [show m = N ^ p - 1 from rfl]; omega
  haveI hmne : NeZero m := ⟨hmpos.ne'⟩
  -- ## the cyclotomic level `k⟮ζ⟯`
  obtain ⟨ζ, hζ⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := Ω) (n := m)
  let L₀ : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hCyc₀ : IsCyclotomicExtension ({m} : Set ℕ) k ↥L₀ :=
    Work.SSGRoute.E7cC.isCyclotomicExtension_adjoin_primitiveRoot (K := k) hζ
  haveI hfdL₀ : FiniteDimensional k ↥L₀ := IsCyclotomicExtension.finiteDimensional {m} k ↥L₀
  haveI hgalL₀ : IsGalois k ↥L₀ := IsCyclotomicExtension.isGalois {m} k ↥L₀
  haveI hnfL₀ : NumberField ↥L₀ := NumberField.of_module_finite k ↥L₀
  -- ## the witness level `M₀`
  obtain ⟨M₀, hnfM₀, hfdM₀, hgalM₀, hcycM₀, hcardM₀, hlocM₀⟩ :=
    exists_unramified_inert_cyclic_level p k Ω Q
  -- ## `K` as a `k`-level, the `k`-level `Lk` and the `K`-level `L`
  let Kf : IntermediateField k Ω := (IsScalarTower.toAlgHom k K Ω).fieldRange
  haveI hfdKf : FiniteDimensional k Kf :=
    LinearEquiv.finiteDimensional
      (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K Ω)).toLinearEquiv
  haveI hgalKf : IsGalois k Kf :=
    IsGalois.of_algEquiv (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K Ω))
  haveI hnfKf : NumberField ↥Kf := NumberField.of_module_finite k ↥Kf
  let Lk : IntermediateField k Ω := Kf ⊔ L₀ ⊔ M₀
  haveI hfdLk : FiniteDimensional k Lk := IntermediateField.finiteDimensional_sup _ _
  haveI hgalLk : IsGalois k Lk := inferInstance
  haveI hnfLk : NumberField ↥Lk := NumberField.of_module_finite k ↥Lk
  have hKfLk : Kf ≤ Lk := le_trans le_sup_left le_sup_left
  let L : IntermediateField K Ω :=
    Lk.toSubfield.toIntermediateField (fun x => by
      have hx : algebraMap K Ω x ∈ Kf := by
        have h1 : algebraMap K Ω x
            = (((IsScalarTower.toAlgHom k K Ω).equivFieldRange x : ↥Kf) : Ω) := by
          rw [AlgHom.equivFieldRange_apply_coe, IsScalarTower.toAlgHom_apply]
        rw [h1]
        exact ((IsScalarTower.toAlgHom k K Ω).equivFieldRange x).2
      exact hKfLk hx)
  have hLrestrict : L.restrictScalars k = Lk := by
    show (Lk.toSubfield.toIntermediateField _).restrictScalars k = Lk
    ext x; exact Iff.rfl
  have eL : ↥Lk ≃ₐ[k] ↥L := (IntermediateField.equivOfEq hLrestrict).symm
  haveI hgalL : IsGalois k ↥L := IsGalois.of_algEquiv eL
  haveI hfdL : FiniteDimensional k ↥L := LinearEquiv.finiteDimensional eL.toLinearEquiv
  haveI hnfL : NumberField ↥L := NumberField.of_module_finite k ↥L
  -- ## a prime `q'` of `𝓞 ↥L` over `q`
  haveI hfdKL : FiniteDimensional K ↥L := FiniteDimensional.right k K ↥L
  haveI hgalKL : IsGalois K ↥L := IsGalois.tower_top_of_isGalois k K ↥L
  obtain ⟨q', hq'lies⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := ↥L) q
  haveI : q'.asIdeal.LiesOver q.asIdeal := hq'lies
  -- ## the residue characteristic `ℓ` of `q` does not divide the cyclotomic exponent `m`
  let ℓ : ℕ := ringChar (NumberField.RingOfIntegers K ⧸ q.asIdeal)
  have hℓdvdN : ℓ ∣ N := by
    show ℓ ∣ Nat.card (NumberField.RingOfIntegers K ⧸ q.asIdeal)
    exact ringChar.dvd (by rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _)
  have hℓ1 : ℓ ≠ 1 := by
    intro h
    have h1 : ((1 : ℕ) : (NumberField.RingOfIntegers K ⧸ q.asIdeal)) = 0 :=
      (ringChar.spec (NumberField.RingOfIntegers K ⧸ q.asIdeal) 1).mpr (by rw [← h])
    rw [Nat.cast_one] at h1
    exact one_ne_zero h1
  have hℓm : ¬ ℓ ∣ m := by
    intro hdiv
    have hqd : ℓ ∣ N ^ p := dvd_pow hℓdvdN hp.ne_zero
    have h2 : ℓ ∣ N ^ p - (N ^ p - 1) := Nat.dvd_sub hqd hdiv
    rw [Nat.sub_sub_self (Nat.one_le_pow p N (by omega))] at h2
    exact hℓ1 (Nat.dvd_one.mp h2)
  have hmpq : ((m : ℕ) : NumberField.RingOfIntegers K) ∉ q.asIdeal := by
    intro hmem
    have h2 : ((m : ℕ) : NumberField.RingOfIntegers K ⧸ q.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk q.asIdeal) m]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact hℓm (ringChar.dvd h2)
  have hmpQ : ((m : ℕ) : NumberField.RingOfIntegers k) ∉ Q.asIdeal := by
    intro hmem
    apply hmpq
    have h1 : ((m : ℕ) : NumberField.RingOfIntegers k) ∈
        q.asIdeal.under (NumberField.RingOfIntegers k) := by
      rw [← hQlies.over]; exact hmem
    rw [Ideal.mem_under] at h1
    simpa using h1
  -- ## the sub-levels `M₀` and `L₀` inside `L`, and the primes of `𝓞 ↥L` below `q'`
  have hM₀Lk : M₀ ≤ Lk := le_sup_right
  let ψM : ↥M₀ →ₐ[k] ↥L := eL.toAlgHom.comp (IntermediateField.inclusion hM₀Lk)
  letI : Algebra ↥M₀ ↥L := ψM.toRingHom.toAlgebra
  haveI hST_M1 : IsScalarTower k ↥M₀ ↥L :=
    IsScalarTower.of_algebraMap_eq fun x => (ψM.commutes x).symm
  let wM : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M₀) :=
    ⟨q'.asIdeal.under (NumberField.RingOfIntegers ↥M₀), inferInstance,
      Ideal.under_ne_bot _ q'.ne_bot⟩
  have hwMlies : q'.asIdeal.LiesOver wM.asIdeal := Ideal.over_under q'.asIdeal
  have hq'Q : q'.asIdeal.LiesOver Q.asIdeal :=
    Ideal.LiesOver.trans q'.asIdeal q.asIdeal Q.asIdeal
  haveI : q'.asIdeal.LiesOver wM.asIdeal := hwMlies
  haveI : q'.asIdeal.LiesOver Q.asIdeal := hq'Q
  have hwMQ : wM.asIdeal.LiesOver Q.asIdeal :=
    Ideal.LiesOver.tower_bot q'.asIdeal wM.asIdeal Q.asIdeal
  have hunrM : wM.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 :=
    (hlocM₀ wM hwMQ).1
  have hfM : wM.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = p :=
    (hlocM₀ wM hwMQ).2
  have hL₀Lk : L₀ ≤ Lk := le_trans le_sup_right le_sup_left
  let ψL : ↥L₀ →ₐ[k] ↥L := eL.toAlgHom.comp (IntermediateField.inclusion hL₀Lk)
  letI : Algebra ↥L₀ ↥L := ψL.toRingHom.toAlgebra
  haveI hST_L1 : IsScalarTower k ↥L₀ ↥L :=
    IsScalarTower.of_algebraMap_eq fun x => (ψL.commutes x).symm
  let wL : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L₀) :=
    ⟨q'.asIdeal.under (NumberField.RingOfIntegers ↥L₀), inferInstance,
      Ideal.under_ne_bot _ q'.ne_bot⟩
  have hwLlies : q'.asIdeal.LiesOver wL.asIdeal := Ideal.over_under q'.asIdeal
  haveI : q'.asIdeal.LiesOver wL.asIdeal := hwLlies
  have hwLQ : wL.asIdeal.LiesOver Q.asIdeal :=
    Ideal.LiesOver.tower_bot q'.asIdeal wL.asIdeal Q.asIdeal
  have hunrL : wL.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    have h := NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := k) (Ω := ↥L₀) m Q hmpQ
    exact h wL hwLQ
  -- ## `e(q' | q) = 1`, from the triviality of the inertia subgroup of `L/K` at `q'`
  have hIbot : Ideal.inertia (↥L ≃ₐ[K] ↥L) q'.asIdeal = ⊥ :=
    inertia_eq_bot_of_sup L M₀ L₀ (by rw [hLrestrict]) q q' hq'lies wM hwMlies hunrM wL hwLlies hunrL
  have he : q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      q.asIdeal q'.asIdeal).mp hIbot
  refine ⟨L, hnfL, hfdL, hgalL, q', hq'lies, he, ?_, ?_⟩
  · -- ## `p ∣ f(q' | q)` : the reduction of `ζ` is a primitive `m`-th root of unity in `κ(q')`
    have hdvdP : ∀ n : ℕ, (n : NumberField.RingOfIntegers ↥L) ∈ q'.asIdeal → ℓ ∣ n := by
      intro n hn
      have h1 : (n : NumberField.RingOfIntegers K) ∈
          q'.asIdeal.under (NumberField.RingOfIntegers K) := by
        rw [Ideal.mem_under, map_natCast]; exact hn
      rw [← hq'lies.over] at h1
      have h2 : ((n : ℕ) : NumberField.RingOfIntegers K ⧸ q.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk q.asIdeal) n]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr h1
      exact ringChar.dvd h2
    have hζL₀ : ζ ∈ L₀ :=
      IntermediateField.subset_adjoin k ({ζ} : Set Ω) (Set.mem_singleton ζ)
    have hle1 : L₀ ≤ Kf ⊔ L₀ := le_sup_right
    have hle2 : Kf ⊔ L₀ ≤ Lk := le_sup_left
    have hζLk : ζ ∈ Lk := hle2 (hle1 hζL₀)
    let ζLk : ↥Lk := ⟨ζ, hζLk⟩
    have hζLk_prim : IsPrimitiveRoot ζLk m :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp (by
        rw [show ((ζLk : ↥Lk) : Ω) = ζ from rfl]; exact hζ)
    let ζL : ↥L := eL ζLk
    have hζprim : IsPrimitiveRoot ζL m :=
      hζLk_prim.map_of_injective (f := (eL : ↥Lk →* ↥L)) eL.injective
    have hint : IsIntegral ℤ ζL := hζprim.isIntegral hmpos
    obtain ⟨ζO, hζOeq⟩ := (IsIntegralClosure.isIntegral_iff
      (A := NumberField.RingOfIntegers ↥L) (R := ℤ) (B := ↥L)).mp hint
    have hζO : IsPrimitiveRoot ζO m := by
      have h1 : IsPrimitiveRoot ((ζO : ↥L)) m := by
        rw [show ((ζO : ↥L)) = ζL from hζOeq]; exact hζprim
      exact IsPrimitiveRoot.coe_submonoidClass_iff.mp h1
    have hpri : IsPrimitiveRoot (Ideal.Quotient.mk q'.asIdeal ζO :
        NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L q') m :=
      Work.SSGRoute.isPrimitiveRoot_quotient_mk q'.asIdeal hmpos hdvdP hℓm hζO
    let κ := NK.CFTLib.IdeleHasse.Descent.ResidueFieldOf ↥L q'
    have hNcard : Nat.card κ = N ^ q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
      have h := Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg q q' hq'lies
      rwa [show Nat.card (NumberField.RingOfIntegers K ⧸ q.asIdeal) = N from rfl] at h
    have hm_dvd : m ∣ Nat.card κ - 1 := by
      have hη0 : (Ideal.Quotient.mk q'.asIdeal ζO : κ) ≠ 0 := by
        intro h0
        have h1 := hpri.1
        rw [h0, zero_pow hmpos.ne'] at h1
        exact one_ne_zero h1.symm
      let u : κˣ := Units.mk0 (Ideal.Quotient.mk q'.asIdeal ζO : κ) hη0
      have hu : (u : κ) = (Ideal.Quotient.mk q'.asIdeal ζO : κ) := rfl
      have huo : orderOf u = m := by
        rw [← orderOf_units, hu]; exact hpri.eq_orderOf.symm
      have h := orderOf_dvd_natCard u
      rwa [huo, Nat.card_units] at h
    refine Work.SSGRoute.dvd_of_pow_sub_one_dvd_pow_sub_one N p
      (q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) hN2 hp.pos ?_
    rw [← hNcard]
    exact hm_dvd
  · -- ## the unramified character `χ : Gal(L/k) →* Multiplicative (ZMod p)`
    let θ : (↥M₀ ≃ₐ[k] ↥M₀) ≃* Multiplicative (ZMod p) := by
      have h2 := zmodCyclicMulEquiv (G := ↥M₀ ≃ₐ[k] ↥M₀) hcycM₀
      rw [hcardM₀] at h2
      exact h2.symm
    let χ : (↥L ≃ₐ[k] ↥L) →* Multiplicative (ZMod p) :=
      θ.toMonoidHom.comp (AlgEquiv.restrictNormalHom ↥M₀)
    refine ⟨χ, ?_, ?_⟩
    · -- `χ` kills the inertia at `q'`: an inertial element restricts trivially to the unramified
      -- level `M₀`
      intro σ hσ
      have h2 : AlgEquiv.restrictNormalHom ↥M₀ σ = 1 :=
        restrictNormalHom_eq_one_of_isInertiaAt (k := k) (E := ↥M₀) (L := ↥L)
          q' wM hwMlies hunrM σ hσ
      show χ σ = 1
      rw [show χ σ = θ (AlgEquiv.restrictNormalHom ↥M₀ σ) from rfl, h2, map_one]
    · -- `χ` is nontrivial on the decomposition group of the place of `q'`
      have hstab : MulAction.stabilizer (↥M₀ ≃ₐ[k] ↥M₀) wM.asIdeal = ⊤ := by
        haveI : wM.asIdeal.LiesOver Q.asIdeal := hwMQ
        refine Subgroup.eq_top_of_card_eq _ ?_
        rw [Ideal.card_stabilizer_eq (p := Q.asIdeal) (P := wM.asIdeal),
          Ideal.ramificationIdxIn_eq_ramificationIdx Q.asIdeal wM.asIdeal (↥M₀ ≃ₐ[k] ↥M₀),
          Ideal.inertiaDegIn_eq_inertiaDeg Q.asIdeal wM.asIdeal (↥M₀ ≃ₐ[k] ↥M₀),
          hunrM, hfM, one_mul, hcardM₀]
      have hplace : MulAction.stabilizer (↥M₀ ≃ₐ[k] ↥M₀) (NK.GlobalCFT.Place.ofFinite wM)
          = MulAction.stabilizer (↥M₀ ≃ₐ[k] ↥M₀) wM.asIdeal := by
        ext σ
        rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
          NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj,
          IsDedekindDomain.HeightOneSpectrum.ext_iff,
          NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
        rw [Ideal.pointwise_smul_def]
        exact Iff.rfl
      obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ↥M₀ ≃ₐ[k] ↥M₀, σ₀ ≠ 1 := by
        haveI : Fintype (↥M₀ ≃ₐ[k] ↥M₀) := Fintype.ofFinite _
        have h1 : 1 < Fintype.card (↥M₀ ≃ₐ[k] ↥M₀) := by
          rw [← Nat.card_eq_fintype_card, hcardM₀]; exact hp.one_lt
        obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card h1 1
        exact ⟨b, hb⟩
      have hσ₀mem : σ₀ ∈ MulAction.stabilizer (↥M₀ ≃ₐ[k] ↥M₀)
          (NK.GlobalCFT.Place.ofFinite wM) := by
        rw [hplace, hstab]; exact Subgroup.mem_top σ₀
      obtain ⟨τ, hτ, hτres⟩ := exists_mem_stabilizer_restrictNormalHom_eq
        (NK.GlobalCFT.Place.ofFinite q') (NK.GlobalCFT.Place.ofFinite wM)
        (NK.GlobalCFT.Place.liesOver_ofFinite hwMlies) σ₀ hσ₀mem
      refine ⟨τ, ?_, ?_⟩
      · -- `τ` lies in the decomposition group of the place of `q'`
        rw [SSGRoute.PTExt.decompK]
        exact hτ
      · rw [show χ τ = θ (AlgEquiv.restrictNormalHom ↥M₀ τ) from rfl, hτres]
        exact fun h1 => hσ₀ (θ.injective (by rw [h1, map_one]))

end Work.SSGRoute.Sha2Lib
