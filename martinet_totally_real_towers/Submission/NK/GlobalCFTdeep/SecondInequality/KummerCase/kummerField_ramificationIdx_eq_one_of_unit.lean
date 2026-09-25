import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Prelude
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.mem_adicCompletionIntegers_of_pow_eq_unit
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.le_inertiaDeg_of_pow_eq_adicCompletionIntegers
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.exists_unit_adicCompletionIntegers_of_mem_localUnits
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_kummerAdjoin
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
import Submission.NK.UchidaKummer.Defs

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical NumberField
open IsDedekindDomain

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- **The Kummer extension of a local unit is unramified.**

Let `K` be a number field with a primitive `p`-th root of unity `ζ` (`p` prime), `Ω` a separable
closure of `K`, `b ∈ Kˣ` and `L = kummerField p b ⊆ Ω`.  Let `Q` be a prime of `𝓞 K` with `p ∉ Q`
and with `b` a local unit at `Q` (equivalently `v_Q(b) = 0`).  Then every prime of `𝓞 L` above `Q`
is unramified over `Q`.

If `b` is a `p`-th power in `K_Qˣ` the local extension is trivial
(`NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff`).  Otherwise `[L : K] = p`, and the
reduction of a `p`-th root of `b` (a unit of `𝒪 L` at `q`, by
`mem_adicCompletionIntegers_of_pow_eq_unit`) generates a residue field extension of degree `p`
(`le_inertiaDeg_of_pow_eq_adicCompletionIntegers`).  Then
`e · f = [L_q : K_Q] ≤ [L : K] = p ≤ f` forces `e = 1`. -/
theorem kummerField_ramificationIdx_eq_one_of_unit
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (b : Kˣ)
    [FiniteDimensional K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    [NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : (p : NumberField.RingOfIntegers K) ∉ Q.asIdeal)
    (hb : NK.GlobalCFT.Idele.principalIdele K b (NK.GlobalCFT.Place.ofFinite Q) ∈
      NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q)) :
    ∀ q : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)),
      q.asIdeal.LiesOver Q.asIdeal →
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
  classical
  intro q hq
  let Lf : IntermediateField K Ω := NK.LocalAnabelian.kummerField (K' := Ω) p b
  -- ## A chosen `p`-th root of `b` inside `L = kummerField p b`
  obtain ⟨α, hα⟩ :=
    NK.UchidaKummer.Kummer.exists_pow_eq_algebraMap_of_isSepClosure (k := K) (K' := Ω) p hp hζ b
  have hαL : α ∈ NK.LocalAnabelian.kummerField (K' := Ω) p b :=
    NK.LocalAnabelian.mem_kummerField_of_pow_eq hα
  have hα' : (⟨α, hαL⟩ : ↥Lf) ^ p = algebraMap K ↥Lf (b : K) := by
    apply Subtype.ext
    change (α : Ω) ^ p = algebraMap K Ω (b : K)
    exact hα
  -- ## `b` is a local unit at `Q`: its image in the completed integers is a unit
  obtain ⟨u, hu_coe, hbval⟩ := exists_unit_adicCompletionIntegers_of_mem_localUnits b Q hb
  have hppos : 0 < p := hp.pos
  by_cases hcase : ∃ c : (Q.adicCompletion K)ˣ,
      algebraMap K (Q.adicCompletion K) (b : K) = (c : Q.adicCompletion K) ^ p
  · -- ## Case 1: `b` is a `p`-th power in `K_Q`; the local extension is trivial
    have hloc := (NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
      (K := K) (K' := Ω) p hp hζ b Lf rfl Q).mpr hcase
    have h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := hloc q hq
    exact Nat.eq_one_of_mul_eq_one_right h1
  · -- ## Case 2: `b` is not a `p`-th power in `K_Q`
    have hbnotpow : b ∉ NK.LocalAnabelian.powSubgroup p K := by
      intro hmem
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
      rw [powMonoidHom_apply] at hy
      refine hcase ⟨Units.map (algebraMap K (Q.adicCompletion K)) y, ?_⟩
      rw [Units.coe_map, ← map_pow]
      exact congrArg (algebraMap K (Q.adicCompletion K)) (by
        rw [← Units.val_pow_eq_pow_val, hy])
    have hfin : Module.finrank K ↥Lf = p :=
      (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω) p hp hζ b
        hbnotpow).2
    -- ## the image of the root in the completed integers of `L`
    have hθmem : algebraMap ↥Lf (q.adicCompletion ↥Lf) (⟨α, hαL⟩ : ↥Lf) ∈
        q.adicCompletionIntegers ↥Lf :=
      mem_adicCompletionIntegers_of_pow_eq_unit (K := K) (L := ↥Lf) p hp Q q hq (b := b) hbval hα'
    let θ : q.adicCompletionIntegers ↥Lf :=
      ⟨algebraMap ↥Lf (q.adicCompletion ↥Lf) (⟨α, hαL⟩ : ↥Lf), hθmem⟩
    -- ## the algebra structure on the completed integers
    let ρ : Q.adicCompletionIntegers K →+* q.adicCompletionIntegers ↥Lf :=
      ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers ↥Lf)
        (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2)
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers ↥Lf) :=
      RingHom.toAlgebra ρ
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion ↥Lf) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    haveI hST : IsScalarTower K (Q.adicCompletion K) (q.adicCompletion ↥Lf) :=
      Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
        (K := K) (L := ↥Lf) Q q hq
    have hlies : Ideal.LiesOver (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ↥Lf))
        (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
      Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
        (K := K) (L := ↥Lf) Q q hq
    have hθ : θ ^ p = algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers ↥Lf) u := by
      apply Subtype.ext
      change (algebraMap ↥Lf (q.adicCompletion ↥Lf) (⟨α, hαL⟩ : ↥Lf)) ^ p
        = (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
            ((u : (Q.adicCompletionIntegers K)ˣ) : Q.adicCompletion K)
      rw [← map_pow, hα']
      rw [← IsScalarTower.algebraMap_apply K ↥Lf (q.adicCompletion ↥Lf) (b : K)]
      rw [IsScalarTower.algebraMap_apply K (Q.adicCompletion K) (q.adicCompletion ↥Lf) (b : K)]
      congr 1
      exact hu_coe.symm
    have hnot : ∀ c : (Q.adicCompletion K)ˣ,
        (c : Q.adicCompletion K) ^ p ≠ (u : Q.adicCompletion K) := by
      intro c hc
      refine hcase ⟨c, ?_⟩
      rw [hc]
      exact hu_coe.symm
    -- ## the residue degree bound
    have hfp : p ≤ q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
      le_inertiaDeg_of_pow_eq_adicCompletionIntegers (K := K) (L := ↥Lf) p hp Q q hq hQ hlies u
        θ hθ hnot
    -- ## `e · f ≤ [L : K] = p`
    have hle : Module.finrank (Q.adicCompletion K) (q.adicCompletion ↥Lf) ≤ Module.finrank K ↥Lf :=
      Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
        (K := K) (L := ↥Lf) Q q hq
    have hmul := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := K) (L := ↥Lf) Q q hq
    have hef : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ≤ p := by
      rw [hmul]
      exact hle.trans_eq hfin
    -- ## `e ≥ 1`
    have hepos : 0 < q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) := by
      haveI hmf : Module.Finite (Q.adicCompletion K) (q.adicCompletion ↥Lf) :=
        Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
          (K := K) (L := ↥Lf) Q q hq
      by_contra h
      have h0 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 0 :=
        Nat.eq_zero_of_not_pos h
      have hpos : 0 < Module.finrank (Q.adicCompletion K) (q.adicCompletion ↥Lf) :=
        Module.finrank_pos
      rw [← hmul, h0, zero_mul] at hpos
      exact lt_irrefl 0 hpos
    -- ## arithmetic
    have hfle : q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ≤
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
          q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
      Nat.le_mul_of_pos_left _ hepos
    have hf0 : 0 < q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by omega
    have hprod : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)
        = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by omega
    refine Nat.mul_right_cancel hf0 ?_
    rw [one_mul]
    exact hprod

end NK.GlobalCFTdeep.SecondInequality.KummerCase
