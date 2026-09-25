import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow_mem_localNormFinite
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow_mem_localNormInfinite
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormInfinite_surjective_of_mem_localPow
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Prelude
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.mem_adicCompletionIntegers_of_pow_eq_unit
import Submission.NK.GlobalCFTdeep.SecondInequality.localIndex_finite_notMem
import Submission.NK.LocalReciprocity.LocalSetup
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
import Submission.NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank
import Submission.NK.GlobalCFTdeep.SecondInequality.pow_mem_normGroup_adicCompletion
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_kummerAdjoin
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
import Submission.NK.UchidaKummer.Defs
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.NK.GlobalCFTdeep.Herbrand.index_normGroup_completion_eq_finrank

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT
open Polynomial

/-- **At a finite place `Q ∈ S` at which `b` is a local `p`-th power, the local norm is onto.**

`K` is a number field containing a primitive `p`-th root of unity `ζ`, `Ω` a separable closure of
`K`, `b ∈ Kˣ` and `L = NK.LocalAnabelian.kummerField p b`.  If `b` is a `p`-th power in the
completion `K_Q`, then the local extension `L_q/K_Q` is trivial for every prime `q` of `L` above
`Q` (the local Kummer dichotomy `NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff`), so
the local norm `N_{L_q/K_Q}` is an isomorphism and in particular surjective. -/
theorem localNormFinite_surjective_of_mem_localPow
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (b : Kˣ)
    [FiniteDimensional K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    [NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hbQ : Idele.principalIdele K b (Place.ofFinite Q) ∈ localPow (K := K) p (Place.ofFinite Q))
    (q : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (x : (Q.adicCompletion K)ˣ) :
    ∃ u : (q.adicCompletion ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b))ˣ,
      Place.localNormFinite q Q hq u = x := by
  obtain ⟨c, hc⟩ := hbQ
  have hc' : algebraMap K (Q.adicCompletion K) (b : K) = (c : (Q.adicCompletion K)) ^ p := by
    have h := congrArg (fun u : (Q.adicCompletion K)ˣ => (u : Q.adicCompletion K)) hc
    simpa [Idele.principalIdele_apply, Units.coe_map] using h.symm
  have hdich := (NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff (K := K) (K' := Ω) p hp
      hζ b (NK.LocalAnabelian.kummerField (K' := Ω) p b) rfl Q).mpr ⟨c, hc'⟩
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  have hdeg : NK.UchidaKummer.localDeg q Q = 1 := hdich q hq
  have hfr : Module.finrank (Q.adicCompletion K)
      (q.adicCompletion ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)) = 1 := by
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        Q q hq, ← NK.UchidaKummer.localDeg]
    exact hdeg
  haveI hfree : Module.Free (Q.adicCompletion K)
      (q.adicCompletion ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)) :=
    Module.Free.of_divisionRing _ _
  refine ⟨Units.map (algebraMap (Q.adicCompletion K)
    (q.adicCompletion ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b))) x, ?_⟩
  rw [show Place.localNormFinite q Q hq = Units.map (Algebra.norm (Q.adicCompletion K)) from rfl]
  refine Units.ext ?_
  change Algebra.norm (Q.adicCompletion K)
    (algebraMap (Q.adicCompletion K)
      (q.adicCompletion ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)) (x : Q.adicCompletion K))
    = (x : Q.adicCompletion K)
  rw [Algebra.norm_algebraMap, hfr, pow_one]

/-- If a unit of the local integers at `Q` is not a `p`-th power in `K_Q^×`, then its residue is
not a `p`-th power in the residue field. -/
theorem not_exists_pow_residue_of_not_exists_pow
    {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (Q : HeightOneSpectrum (𝓞 K)) (hQ : (p : 𝓞 K) ∉ Q.asIdeal)
    {u : (Q.adicCompletionIntegers K)ˣ}
    (h : ∀ c : (Q.adicCompletion K)ˣ,
      (c : Q.adicCompletion K) ^ p ≠ (u : Q.adicCompletion K)) :
    ∀ c : IsLocalRing.ResidueField (Q.adicCompletionIntegers K),
      c ^ p ≠ IsLocalRing.residue (Q.adicCompletionIntegers K)
        (u : Q.adicCompletionIntegers K) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hresu : IsLocalRing.residue (Q.adicCompletionIntegers K)
      (u : Q.adicCompletionIntegers K) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (R := Q.adicCompletionIntegers K)
      (u : Q.adicCompletionIntegers K)).mpr u.isUnit
  haveI hhens : HenselianLocalRing (Q.adicCompletionIntegers K) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
      (R := 𝓞 K) (K := K) Q
  have hunit : IsUnit (p : Q.adicCompletionIntegers K) :=
    NK.GlobalCFTdeep.SecondInequality.isUnit_natCast_adicCompletionIntegers_of_notMem Q hQ
  intro c hc
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hc
    exact hresu hc.symm
  have hmem : Units.map ((IsLocalRing.residue (Q.adicCompletionIntegers K)).toMonoidHom) u ∈
      (powMonoidHom p).range := by
    refine ⟨Units.mk0 c hcne, ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map]
    exact hc
  obtain ⟨u', hu'⟩ := Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow p hunit u hmem
  refine h (Units.map (↑(algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K))) u') ?_
  rw [Units.coe_map, ← map_pow]
  have hu'' : u' ^ p = u := by simpa [powMonoidHom_apply] using hu'
  rw [show (↑u' : Q.adicCompletionIntegers K) ^ p = (u : Q.adicCompletionIntegers K) from by
    rw [← Units.val_pow_eq_pow_val, hu'']]
  rfl


/-- **The inertia degree of the maximal ideal of the completed integers of `L` over that of `K`
equals the global inertia degree.** -/
theorem inertiaDeg_maximalIdeal_adicCompletionIntegers_eq
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
      RingHom.toAlgebra (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q q hq)
    (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).inertiaDeg
      (Q.adicCompletionIntegers K) = q.asIdeal.inertiaDeg (𝓞 K) := by
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q q hq)
  haveI hlies : (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).LiesOver
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers Q q hq
  letI hFS : Field ((q.adicCompletionIntegers L) ⧸
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L))
  letI hFR : Field ((Q.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
  obtain ⟨eS⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists q
  obtain ⟨eQ⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists Q
  haveI hfinS : Finite ((q.adicCompletionIntegers L) ⧸
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) :=
    (eS.toEquiv.finite_iff).mpr (Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q)
  haveI hfinQ : Finite ((Q.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
    (eQ.toEquiv.finite_iff).mpr (Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q)
  haveI hmod : Module.Finite ((Q.adicCompletionIntegers K) ⧸
        IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
      ((q.adicCompletionIntegers L) ⧸ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) :=
    Module.finite_iff_finite.mpr inferInstance
  have hcardS : Nat.card ((q.adicCompletionIntegers L) ⧸
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L))
      = Nat.card ((Q.adicCompletionIntegers K) ⧸
          IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) ^
        (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).inertiaDeg
          (Q.adicCompletionIntegers K) := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L))]
    exact Module.natCard_eq_pow_finrank
  have hcardG : Nat.card ((q.adicCompletionIntegers L) ⧸
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L))
      = Nat.card ((Q.adicCompletionIntegers K) ⧸
          IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) ^
        (q.asIdeal.inertiaDeg (𝓞 K)) :=
    Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
      K L Q q hq
  haveI : Fintype ((Q.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := Fintype.ofFinite _
  have hA2 : 1 < Nat.card ((Q.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  exact le_antisymm
    ((Nat.pow_le_pow_iff_right hA2).mp (le_of_eq (hcardS.symm.trans hcardG)))
    ((Nat.pow_le_pow_iff_right hA2).mp (le_of_eq (hcardG.symm.trans hcardS)))

/-- **The Kummer extension of a local unit is unramified.** -/
theorem ramificationIdx_eq_one_of_mem_localUnits
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (b : Kˣ)
    [FiniteDimensional K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    [NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    [IsGalois K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    (hcard : Nat.card (↥(NK.LocalAnabelian.kummerField (K' := Ω) p b) ≃ₐ[K]
      ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)) = p)
    (Q : HeightOneSpectrum (𝓞 K))
    (hQ : (p : 𝓞 K) ∉ Q.asIdeal)
    (hb : Idele.principalIdele K b (Place.ofFinite Q) ∈ Place.localUnits K (Place.ofFinite Q)) :
    ∀ q : HeightOneSpectrum (𝓞 ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)),
      q.asIdeal.LiesOver Q.asIdeal → q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  classical
  intro q hq
  let Lf : IntermediateField K Ω := NK.LocalAnabelian.kummerField (K' := Ω) p b
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  haveI hST : IsScalarTower K (Q.adicCompletion K) (q.adicCompletion ↥Lf) :=
    Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion (K := K) (L := ↥Lf) Q q hq
  -- `b` is a local unit at `Q`
  have hbval : Valued.v (algebraMap K (Q.adicCompletion K) (b : K)) = 1 := by
    have h := hb
    rw [Idele.principalIdele_apply] at h
    rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one] at h
    simpa [Units.coe_map] using h
  by_cases hcase : ∃ c : (Q.adicCompletion K)ˣ,
      algebraMap K (Q.adicCompletion K) (b : K) = (c : Q.adicCompletion K) ^ p
  · -- **Case 1**: `b` is a `p`-th power in `K_Q`; the local extension is trivial
    have hloc := (NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
      (K := K) (K' := Ω) p hp hζ b Lf rfl Q).mpr hcase
    have h1 : q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K) = 1 := hloc q hq
    exact Nat.eq_one_of_mul_eq_one_right h1
  · -- **Case 2**: the residue-field argument
    obtain ⟨α, hα⟩ :=
      NK.UchidaKummer.Kummer.exists_pow_eq_algebraMap_of_isSepClosure (k := K) (K' := Ω) p hp hζ b
    have hαL : α ∈ NK.LocalAnabelian.kummerField (K' := Ω) p b :=
      NK.LocalAnabelian.mem_kummerField_of_pow_eq hα
    have hα' : (⟨α, hαL⟩ : ↥Lf) ^ p = algebraMap K ↥Lf (b : K) := by
      apply Subtype.ext
      change α ^ p = algebraMap K Ω (b : K)
      exact hα
    -- `b`'s image in the completed integers, as a unit
    have hb' : algebraMap K (Q.adicCompletion K) (b : K) ∈ Q.adicCompletionIntegers K :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K Q).mpr
        (le_of_eq hbval)
    let b' : Q.adicCompletionIntegers K := ⟨algebraMap K (Q.adicCompletion K) (b : K), hb'⟩
    have hunit : IsUnit b' := by
      rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      exact hbval
    let u : (Q.adicCompletionIntegers K)ˣ := hunit.unit
    have hu_coe : (u : Q.adicCompletion K) = algebraMap K (Q.adicCompletion K) (b : K) := by
      rw [IsUnit.unit_spec]
    -- the image of the root in the completed integers of `L`
    have hθmem : algebraMap ↥Lf (q.adicCompletion ↥Lf) (⟨α, hαL⟩ : ↥Lf)
        ∈ q.adicCompletionIntegers ↥Lf :=
      mem_adicCompletionIntegers_of_pow_eq_unit p hp Q q hq hbval hα'
    let θ : q.adicCompletionIntegers ↥Lf :=
      ⟨algebraMap ↥Lf (q.adicCompletion ↥Lf) (⟨α, hαL⟩ : ↥Lf), hθmem⟩
    -- the algebra structures
    let ρ : Q.adicCompletionIntegers K →+* q.adicCompletionIntegers ↥Lf :=
      ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers ↥Lf)
        (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2)
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers ↥Lf) :=
      RingHom.toAlgebra ρ
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion ↥Lf) :=
      RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype)
    haveI : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers ↥Lf)
        (q.adicCompletion ↥Lf) :=
      Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletionIntegers_adicCompletion
        Q q hq
    -- comparison of the two algebra structures on `L_q` over `K`
    have hrel : (algebraMap ↥Lf (q.adicCompletion ↥Lf) (⟨α, hαL⟩ : ↥Lf)) ^ p
        = (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
            (algebraMap K (Q.adicCompletion K) (b : K)) := by
      have h1 : (algebraMap ↥Lf (q.adicCompletion ↥Lf) (⟨α, hαL⟩ : ↥Lf)) ^ p
          = algebraMap ↥Lf (q.adicCompletion ↥Lf) (algebraMap K ↥Lf (b : K)) := by
        rw [show (algebraMap ↥Lf (q.adicCompletion ↥Lf) (⟨α, hαL⟩ : ↥Lf)) ^ p
            = algebraMap ↥Lf (q.adicCompletion ↥Lf) ((⟨α, hαL⟩ : ↥Lf) ^ p) from
          (map_pow (algebraMap ↥Lf (q.adicCompletion ↥Lf)) (⟨α, hαL⟩ : ↥Lf) p).symm, hα']
      rw [h1]
      rw [show algebraMap ↥Lf (q.adicCompletion ↥Lf) (algebraMap K ↥Lf (b : K))
          = ((algebraMap K ↥Lf (b : K)) : q.adicCompletion ↥Lf) from
        congrFun (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (v := q)
          (S := ↥Lf) (K := ↥Lf)) (algebraMap K ↥Lf (b : K))]
      rw [← Commons.RingTheory.Henselian.adicCompletionMap_apply Q q hq (b : K)]
      rw [show ((b : K) : Q.adicCompletion K) = algebraMap K (Q.adicCompletion K) (b : K) from
        (congrFun (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (v := Q)
          (S := K) (K := K)) (b : K)).symm]
    have hRS : (algebraMap (q.adicCompletionIntegers ↥Lf) (q.adicCompletion ↥Lf))
        (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers ↥Lf) u)
        = (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
            ((u : Q.adicCompletionIntegers K) : Q.adicCompletion K) := by
      rw [← IsScalarTower.algebraMap_apply (R := Q.adicCompletionIntegers K)
        (S := q.adicCompletionIntegers ↥Lf) (A := q.adicCompletion ↥Lf) u]
      rfl
    have haev : Polynomial.aeval θ (Polynomial.X ^ p - Polynomial.C
        (u : Q.adicCompletionIntegers K)) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      apply Subtype.ext
      show ((θ : q.adicCompletionIntegers ↥Lf) : q.adicCompletion ↥Lf) ^ p
        - ((algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers ↥Lf)
            (u : Q.adicCompletionIntegers K) : q.adicCompletionIntegers ↥Lf) :
              q.adicCompletion ↥Lf) = 0
      rw [show ((algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers ↥Lf)
            (u : Q.adicCompletionIntegers K) : q.adicCompletionIntegers ↥Lf) :
              q.adicCompletion ↥Lf)
          = (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
              ((u : Q.adicCompletionIntegers K) : Q.adicCompletion K) from hRS]
      rw [show ((θ : q.adicCompletionIntegers ↥Lf) : q.adicCompletion ↥Lf) ^ p
          = (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
              (algebraMap K (Q.adicCompletion K) (b : K)) from hrel]
      rw [show (((u : Q.adicCompletionIntegers K)) : Q.adicCompletion K)
          = algebraMap K (Q.adicCompletion K) (b : K) from hu_coe, sub_self]
    -- the residue of `u` is not a `p`-th power
    have hres' : ∀ c : IsLocalRing.ResidueField (Q.adicCompletionIntegers K),
        c ^ p ≠ IsLocalRing.residue (Q.adicCompletionIntegers K)
          (u : Q.adicCompletionIntegers K) :=
      not_exists_pow_residue_of_not_exists_pow hp Q hQ (u := u) (fun c hc => by
        refine hcase ⟨c, ?_⟩
        rw [← hu_coe]
        exact hc.symm)
    -- the residue degree bound
    have hfp : p ≤ q.asIdeal.inertiaDeg (𝓞 K) := by
      haveI hliesM : (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ↥Lf)).LiesOver
          (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
        Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
          Q q hq
      letI : Field ((q.adicCompletionIntegers ↥Lf) ⧸
          IsLocalRing.maximalIdeal (q.adicCompletionIntegers ↥Lf)) :=
        Ideal.Quotient.field (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ↥Lf))
      letI : Field ((Q.adicCompletionIntegers K) ⧸
          IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
        Ideal.Quotient.field (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
      obtain ⟨eS⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists q
      haveI : Finite ((q.adicCompletionIntegers ↥Lf) ⧸
          IsLocalRing.maximalIdeal (q.adicCompletionIntegers ↥Lf)) :=
        (eS.toEquiv.finite_iff).mpr
          (Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q)
      have h := Commons.NumberTheory.NumberField.Completion.natDegree_le_inertiaDeg_of_aeval_eq_zero
        (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ↥Lf))
        (Polynomial.X ^ p - Polynomial.C (u : Q.adicCompletionIntegers K))
        (Polynomial.X ^ p - Polynomial.C (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) (u : Q.adicCompletionIntegers K)))
        (Polynomial.monic_X_pow_sub_C (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
          (u : Q.adicCompletionIntegers K)) hp.ne_zero)
        (by
          rw [X_pow_sub_C_irreducible_iff_of_prime hp]
          intro c hc
          exact hres' c hc)
        (by simp) θ haev
      have hdeg : (Polynomial.X ^ p - Polynomial.C (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
          (u : Q.adicCompletionIntegers K))).natDegree = p :=
        Polynomial.natDegree_X_pow_sub_C
      rw [hdeg] at h
      rwa [← inertiaDeg_maximalIdeal_adicCompletionIntegers_eq (K := K) (L := ↥Lf) Q q hq]
    -- `e * f ≤ [L : K] = p`
    have hfin : Module.finrank K ↥Lf = p := by
      rw [← IsGalois.card_aut_eq_finrank K ↥Lf, hcard]
    have hef : q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K) ≤ p := by
      rw [Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        Q q hq]
      exact le_trans
        (Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank Q q hq)
        (le_of_eq hfin)
    have hepos : 0 < q.asIdeal.ramificationIdx (𝓞 K) := Ideal.ramificationIdx_pos q.asIdeal (𝓞 K)
    have hfpos : 0 < q.asIdeal.inertiaDeg (𝓞 K) := lt_of_lt_of_le hp.pos hfp
    have h1 : q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K)
        ≤ q.asIdeal.inertiaDeg (𝓞 K) := le_trans hef hfp
    have h2 : q.asIdeal.ramificationIdx (𝓞 K) ≤ 1 :=
      Nat.le_of_mul_le_mul_right (by simpa using h1) hfpos
    omega

/-- **Milne, CFT VII §6, Prop. 6.10(a): the local norm computation.**

`K` is a number field containing a primitive `p`-th root of unity `ζ`, `Ω` is a separable closure
of `K`, `b ∈ Kˣ`, and `L = NK.LocalAnabelian.kummerField p b ⊆ Ω` is the Kummer extension of `b`
(degree `p` over `K`, cf. `NK.GlobalCFTdeep.SecondInequality.isGalois_kummerField`,
`finiteDimensional_kummerField` and `NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank`).
`S`, `T` are disjoint finite sets of places such that all infinite places lie in `S`, all primes
over `p` lie in `S ∪ T`, `b` is a local `p`-th power at the places of `S`, and `b` is a local unit
outside `S ∪ T`.

The conclusion is that the subgroup of `𝕀 K` given by "`p`-th powers at the places of `T`, local
units outside `S ∪ T` and no condition at the places of `S`" — this is exactly
`kummerE p T S` (note the order of the arguments!) — is contained in the idèlic norm subgroup
`N_{L/K} 𝕀 L = Idele.normImage K ↥L`.

Route (Milne's proof of 6.10(a); the local inputs are all on disk):
* `v ∈ S`: `hbS` says `b ∈ K_v^{×p}`, so the local extension `K_v(b^{1/p})/K_v` is trivial and
  every element of `K_vˣ` is a local norm.  For finite `v` use the local Kummer dichotomy
  `NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff` together with
  `Commons...finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg`,
  `Commons...finrank_adicCompletion_le_finrank`, `IsGalois.card_aut_eq_finrank` and
  `Algebra.norm_algebraMap` (the extension is trivial, so `N` is the identity); for infinite `v`
  the extension is trivial for the same reason and (again) `N` is surjective.
* `v ∈ T`: the local degree divides `[L:K] = p`, hence every `p`-th power is a local norm:
  `NK.GlobalCFTdeep.SecondInequality.pow_mem_normGroup_adicCompletion`, whose hypothesis
  `Nat.card (L ≃ₐ[K] L) = p` is available as `hcard`, and
  `NK.LocalReciprocity.index_normGroup_eq_finrank` for the local norm index.
* `v ∉ S ∪ T`: `v ∤ p` (by `hSp`) and `b` is a local unit (by `hbu`), so `L/K` is unramified at
  `v` and every local unit is a norm:
  `Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one`.
  The unramifiedness can be obtained as in
  `Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg`: a unit
  of the local integer ring whose residue is a `p`-th power is already a `p`-th power
  (`Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow`, `p` is a unit at `v`), so
  either `b` is a local `p`-th power (trivial local extension) or the reduction of `X^p - b` is
  irreducible of degree `p`, which forces residue degree `p` and hence ramification index `1`
  (`Commons...natDegree_le_inertiaDeg_of_aeval_eq_zero` for the residue-degree lower bound).
* Assembly into an idèle of `L`: the helper lemmas `placeUnder`, `singleIdele`,
  `normIdeleFun_singleIdele_ofFinite`, `normIdeleFun_singleIdele_ofInfinite`, `yValueAt`,
  `yValue`, `yValue_pickW`, `yValue_mem_localUnits_pickW`, `finite_yValue_not_mem_localUnits`
  and `localNormFinite_units_surjective_of_ramificationIdx_eq_one` in
  `KummerCase/kummerE_le_normImage.lean` are exactly the tools for this (they were built for
  Milne 6.4 and apply verbatim here); finish with `Idele.mem_normImage`. -/
theorem kummerE_le_normImage_of_kummerData
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (b : Kˣ)
    [FiniteDimensional K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    [NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    [IsGalois K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    (hcard : Nat.card (↥(NK.LocalAnabelian.kummerField (K' := Ω) p b) ≃ₐ[K]
      ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)) = p)
    (S T : Finset (NK.GlobalCFT.Place K)) (hST : Disjoint S T)
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ q.asIdeal →
        NK.GlobalCFT.Place.ofFinite q ∈ S ∨ NK.GlobalCFT.Place.ofFinite q ∈ T)
    (hbS : ∀ v ∈ S, NK.GlobalCFT.Idele.principalIdele K b v ∈
      NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow (K := K) p v)
    (hbu : ∀ v : NK.GlobalCFT.Place K, v ∉ S → v ∉ T →
      NK.GlobalCFT.Idele.principalIdele K b v ∈ NK.GlobalCFT.Place.localUnits K v) :
    NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p T S ≤
      NK.GlobalCFT.Idele.normImage K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b) := by
  intro x hx
  classical
  rw [Idele.mem_normImage]
  rw [mem_kummerE] at hx
  obtain ⟨hxT, hxU⟩ := hx
  let L := ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)
  -- ### The local data: a place of `L` above each place of `K`, and a local preimage
  have hhex : ∀ v : Place K, ∃ (w : Place L) (u : (Place.localField L w)ˣ),
      Place.LiesOver w v ∧ Idele.normIdeleFun K L (singleIdele w u) v = x v ∧
        (v ∉ S → v ∉ T → u ∈ Place.localUnits L w) := by
    intro v
    cases v with
    | inl v' =>
        -- infinite place: it lies in `S`, where the local extension is trivial
        obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v' :=
          InfinitePlace.comap_surjective v'
        have hwl : w.LiesOver v' := (Norm.liesOver_iff_comap_eq w v').mpr hw
        haveI : w.LiesOver v' := hwl
        obtain ⟨u, hu⟩ := localNormInfinite_surjective_of_mem_localPow (K := K) (Ω := Ω) hp hζ b
          w v' (hbS (Place.ofInfinite v') (hSinf v')) (x (Place.ofInfinite v'))
        exact ⟨Place.ofInfinite w, u, Place.liesOver_ofInfinite hwl,
          by rw [normIdeleFun_singleIdele_ofInfinite v' w u]; exact hu,
          fun hvS _ => absurd (hSinf v') hvS⟩
    | inr Q =>
        obtain ⟨q, hq⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
          (K := K) (L := L) Q
        by_cases hQS : Place.ofFinite Q ∈ S
        · -- `Q ∈ S`: `b` is a local `p`-th power, so the local extension is trivial
          obtain ⟨u, hu⟩ := localNormFinite_surjective_of_mem_localPow (K := K) (Ω := Ω) hp hζ b Q
            (hbS (Place.ofFinite Q) hQS) q hq (x (Place.ofFinite Q))
          exact ⟨Place.ofFinite q, u, Place.liesOver_ofFinite hq,
            by rw [normIdeleFun_singleIdele_ofFinite Q q hq u]; exact hu,
            fun h _ => absurd hQS h⟩
        · by_cases hQT : Place.ofFinite Q ∈ T
          · -- `Q ∈ T`: `x` is a `p`-th power at `Q`, hence a local norm
            obtain ⟨u, hu⟩ := localPow_mem_localNormFinite (K := K) (L := L) hp hcard Q q hq
              (hxT (Place.ofFinite Q) hQT)
            exact ⟨Place.ofFinite q, u, Place.liesOver_ofFinite hq,
              by rw [normIdeleFun_singleIdele_ofFinite Q q hq u]; exact hu,
              fun _ h => absurd hQT h⟩
          · -- `Q ∉ S ∪ T`: `x` is a local unit and the local extension is unramified
            have hpQ : (p : 𝓞 K) ∉ Q.asIdeal := by
              intro hpQ
              rcases hSp Q hpQ with h | h
              · exact hQS h
              · exact hQT h
            have he1 : q.asIdeal.ramificationIdx (𝓞 K) = 1 :=
              ramificationIdx_eq_one_of_mem_localUnits (K := K) (Ω := Ω) hp hζ b hcard Q hpQ
                (hbu (Place.ofFinite Q) hQS hQT) q hq
            obtain ⟨u, hu, hunorm⟩ :=
              localNormFinite_units_surjective_of_ramificationIdx_eq_one Q q hq he1
                (x (Place.ofFinite Q)) (hxU (Place.ofFinite Q) hQT hQS)
            exact ⟨Place.ofFinite q, u, Place.liesOver_ofFinite hq,
              by rw [normIdeleFun_singleIdele_ofFinite Q q hq u]; exact hunorm,
              fun _ _ => hu⟩
  choose g hval hlies hnorm hunit using hhex
  -- ### The idèle of `L` realising the norms
  have hyeventually : ∀ᶠ w in Filter.cofinite, yValue g hval w ∈ Place.localUnits L w :=
    Filter.eventually_cofinite.mpr
      (finite_yValue_not_mem_localUnits (S := S) (T' := T) hlies hunit)
  let y : Idele L := ⟨yValue g hval, hyeventually⟩
  refine ⟨y, fun v => ?_⟩
  have hsingle : ∀ w : Place L, Place.LiesOver w v →
      y w = singleIdele (g v) (hval v) w := by
    intro w hw
    by_cases h : w = g v
    · rw [h, show y (g v) = yValue g hval (g v) from rfl, yValue_pickW hlies v,
        singleIdele_apply_self]
    · rw [show y w = yValue g hval w from rfl, yValue_eq_one_of_liesOver_ne hw h,
        singleIdele_apply_of_ne (w' := w) h (hval v)]
  rw [← hnorm v]
  exact (normIdeleFun_congr_of_liesOver hsingle).symm

end NK.GlobalCFTdeep.SecondInequality.KummerCase
