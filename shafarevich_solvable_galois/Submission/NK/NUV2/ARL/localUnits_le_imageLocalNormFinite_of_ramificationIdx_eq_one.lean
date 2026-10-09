import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.Place
import Submission.NK.NUV2.ARL.CommonsBridge
import Submission.NK.NUV2.ArtinBridge.continuous_algebraNorm
import Submission.NK.NUV2.ARL.traceSurjectiveUnramified
import Submission.NK.NUV2.ARL.normResidueUnramified
import Submission.Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField WithZero
open Finset Polynomial

set_option maxHeartbeats 1600000

namespace NK.NUV2.ARL


section Matrix

theorem det_mem_pow {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (I : Ideal R) (M : Matrix n n R) (hM : ∀ i j, M i j ∈ I) :
    M.det ∈ I ^ Fintype.card n := by
  classical
  rw [Matrix.det_apply']
  refine Ideal.sum_mem _ (fun σ _ => ?_)
  refine Ideal.mul_mem_left _ _ ?_
  have hprod : ∀ s : Finset n, ∏ i ∈ s, M (σ i) i ∈ I ^ s.card := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
        exact Ideal.mul_mem_mul (hM (σ a) a) ih
  have h := hprod (Finset.univ : Finset n)
  simpa [Finset.card_univ] using h

theorem det_one_add_sub_one_sub_trace_mem_sq {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (I : Ideal R) (M : Matrix n n R) (hM : ∀ i j, M i j ∈ I) :
    (1 + M).det - 1 - M.trace ∈ I ^ 2 := by
  classical
  set Q : Polynomial R := (1 + (Polynomial.X : Polynomial R) • M.map (Polynomial.C : R →+* R[X])).det.divX.divX with hQdef
  have hmain : (1 + M).det = 1 + M.trace + Q.eval 1 := by
    have h := Matrix.det_one_add_smul (1 : R) M
    simpa [hQdef, one_smul] using h
  have hQ : Q.eval 1 ∈ I ^ 2 := by
    rw [Polynomial.eval_eq_sum_range]
    refine Ideal.sum_mem _ (fun k _ => ?_)
    rw [one_pow, mul_one]
    rw [hQdef, Polynomial.coeff_divX, Polynomial.coeff_divX]
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    refine Ideal.sum_mem _ (fun s hs => ?_)
    have hscard : s.card = k + 2 := (Finset.mem_powersetCard.mp hs).2
    have hd := det_mem_pow I (M.submatrix (Subtype.val : s → n) (Subtype.val : s → n))
      (fun i j => hM (Subtype.val i) (Subtype.val j))
    rw [Fintype.card_coe, hscard] at hd
    exact Ideal.pow_le_pow_right (by omega : 2 ≤ k + 2) hd
  rw [hmain]
  have : (1 + M.trace + Q.eval 1) - 1 - M.trace = Q.eval 1 := by ring
  rw [this]
  exact hQ

end Matrix

section Entries

def matIdeal {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) : Ideal (Matrix ι ι R) where
  carrier := {M | ∀ i j, M i j ∈ I}
  zero_mem' := by intro i j; simp
  add_mem' := by intro a b ha hb i j; exact I.add_mem (ha i j) (hb i j)
  smul_mem' := by
    intro a x hx
    rw [smul_eq_mul]
    intro i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem I (fun k _ => Ideal.mul_mem_left I (a i k) (hx k j))

theorem leftMulMatrix_algebraMap_apply {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (r : R) (i j : ι) :
    (Algebra.leftMulMatrix b) (algebraMap R S r) i j = r * (if i = j then 1 else 0) := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, ← Algebra.smul_def, map_smul, Module.Basis.repr_self]
  by_cases h : i = j
  · subst h
    rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, if_pos rfl]
  · rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne h, smul_zero, if_neg h, mul_zero]

theorem leftMulMatrix_mem_of_mem_map {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (I : Ideal R) {t : S}
    (ht : t ∈ Ideal.map (algebraMap R S) I) (i j : ι) :
    (Algebra.leftMulMatrix b) t i j ∈ I := by
  have hle : Ideal.map (algebraMap R S) I ≤ Ideal.comap (Algebra.leftMulMatrix b).toRingHom (matIdeal I) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr i j
    change (Algebra.leftMulMatrix b) (algebraMap R S r) i j ∈ I
    rw [leftMulMatrix_algebraMap_apply]
    rcases eq_or_ne i j with h | h
    · rw [if_pos h, mul_one]; exact hr
    · rw [if_neg h, mul_zero]; exact I.zero_mem
  exact (Ideal.mem_comap.mp (hle ht)) i j

end Entries

section Estimate

theorem val_norm_sub_one_sub_trace_le_local {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (n : ℕ) (hn : 1 ≤ n) (t : q.adicCompletionIntegers L)
    (ht : t ∈ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ^ n) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((Algebra.norm (Q.adicCompletion K))
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (1 + t)) - 1
        - (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L))
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) t))
      ≤ (WithZero.exp (-((2 * n : ℕ) : ℤ)) : WithZero (Multiplicative ℤ)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hfree : Module.Free (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers Q q hq
  haveI hfin : Module.Finite (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers Q q hq
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hST : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletionIntegers_adicCompletion Q q hq
  haveI hST2 : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  classical
  let b := Module.Free.chooseBasis (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
  have hmax : Ideal.map (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
    have h := Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow Q q hq
    rw [hunr, pow_one] at h
    exact h
  have htmap : t ∈ Ideal.map (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L))
      ((IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) ^ n) := by
    rw [Ideal.map_pow, hmax]
    exact ht
  have hentry : ∀ i j, (Algebra.leftMulMatrix b) t i j ∈
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) ^ n :=
    fun i j => leftMulMatrix_mem_of_mem_map b _ htmap i j
  have hM : (Algebra.norm (Q.adicCompletionIntegers K)) (1 + t) - 1
      - (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)) t ∈
      ((IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) ^ n) ^ 2 := by
    have h1 : (Algebra.norm (Q.adicCompletionIntegers K)) (1 + t) =
        ((Algebra.leftMulMatrix b) (1 + t)).det := Algebra.norm_eq_matrix_det b (1 + t)
    have h2 : (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)) t =
        ((Algebra.leftMulMatrix b) t).trace := Algebra.trace_eq_matrix_trace b t
    have h3 : (Algebra.leftMulMatrix b) (1 + t) = 1 + (Algebra.leftMulMatrix b) t := by
      rw [map_add, map_one]
    rw [h1, h2, h3]
    exact det_one_add_sub_one_sub_trace_mem_sq _ _ hentry
  have hnorm : (Algebra.norm (Q.adicCompletion K))
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (1 + t)) =
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        ((Algebra.norm (Q.adicCompletionIntegers K)) (1 + t)) := by
    rw [← Algebra.intNorm_eq_norm (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)]
    exact (Algebra.algebraMap_intNorm (A := Q.adicCompletionIntegers K) (K := Q.adicCompletion K) (L := q.adicCompletion L) (B := q.adicCompletionIntegers L) (1 + t)).symm
  have htrace : (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L))
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) t) =
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        ((Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)) t) := by
    rw [← Algebra.intTrace_eq_trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)]
    exact (Algebra.algebraMap_intTrace (A := Q.adicCompletionIntegers K) (K := Q.adicCompletion K) (L := q.adicCompletion L) (B := q.adicCompletionIntegers L) t).symm
  have hkey : (Algebra.norm (Q.adicCompletion K))
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (1 + t)) - 1
      - (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L))
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) t)
      = algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        ((Algebra.norm (Q.adicCompletionIntegers K)) (1 + t) - 1
          - (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)) t) := by
    rw [hnorm, htrace, map_sub, map_sub, map_one]
  rw [hkey]
  have hmem : (Algebra.norm (Q.adicCompletionIntegers K)) (1 + t) - 1
      - (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)) t ∈
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) ^ (2 * n) := by
    have := hM
    rwa [← pow_mul, Nat.mul_comm] at this
  have hval := (Commons.RingTheory.Henselian.mem_pow_maximalIdeal_iff Q (2 * n)
      ((Algebra.norm (Q.adicCompletionIntegers K)) (1 + t) - 1
        - (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)) t)).mp hmem
  have hunif : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q)) = WithZero.exp (-1) :=
    Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one Q
  rw [hunif] at hval
  refine hval.trans ?_
  rw [← WithZero.exp_nsmul]
  congr 1
  simp

end Estimate








section TraceStep

theorem exists_trace_eq_of_val_le_local {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (n : ℕ) (d : Q.adicCompletion K)
    (hd : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) d
        ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ))) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ s : q.adicCompletionIntegers L,
      Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) = d ∧
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s)
        ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hST : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletionIntegers_adicCompletion Q q hq
  haveI hST2 : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  set π : Q.adicCompletionIntegers K :=
    Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q with hπdef
  have hπval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((π : Q.adicCompletion K)) = WithZero.exp (-1) :=
    Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one Q
  have hπne : ((π : Q.adicCompletion K)) ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hπval
    exact WithZero.exp_ne_zero (a := (-1 : ℤ)) hπval.symm
  have hpow : ((WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ))) ^ n
      = (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  have hinv : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((π : Q.adicCompletion K)) ^ n)⁻¹ = (WithZero.exp ((n : ℤ)) : WithZero (Multiplicative ℤ)) := by
    rw [Valuation.map_inv, Valuation.map_pow, hπval, hpow, ← WithZero.exp_neg]
    congr 1
    simp
  have hd'val : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((((π : Q.adicCompletion K)) ^ n)⁻¹ * d) ≤ 1 := by
    rw [Valuation.map_mul, hinv]
    calc (WithZero.exp ((n : ℤ)) : WithZero (Multiplicative ℤ)) *
          Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) d
        ≤ (WithZero.exp ((n : ℤ)) : WithZero (Multiplicative ℤ)) *
            (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := mul_le_mul' le_rfl hd
      _ = 1 := by rw [← WithZero.exp_add]; simp
  set d' : Q.adicCompletionIntegers K := ⟨(((π : Q.adicCompletion K)) ^ n)⁻¹ * d, hd'val⟩ with hd'def
  obtain ⟨s, hs⟩ := traceSurjectiveUnramified Q q hq hunr d'
  have hs' : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
      (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s)
      = (((π : Q.adicCompletion K)) ^ n)⁻¹ * d := hs
  refine ⟨(π ^ n) • s, ?_, ?_⟩
  · have hcoe : algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) ((π ^ n) • s)
        = algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (((π : Q.adicCompletion K)) ^ n)
          * algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s := by
      rw [Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
          (q.adicCompletion L) (π ^ n),
        IsScalarTower.algebraMap_apply (Q.adicCompletionIntegers K) (Q.adicCompletion K)
          (q.adicCompletion L) (π ^ n), map_pow]
      rfl
    rw [hcoe, ← Algebra.smul_def]
    rw [(Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)).map_smul]
    rw [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
    rw [hs']
    exact mul_inv_cancel_left₀ (pow_ne_zero n hπne) d
  · have hcoe : algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) ((π ^ n) • s)
        = algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (((π : Q.adicCompletion K)) ^ n)
          * algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s := by
      rw [Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
          (q.adicCompletion L) (π ^ n),
        IsScalarTower.algebraMap_apply (Q.adicCompletionIntegers K) (Q.adicCompletion K)
          (q.adicCompletion L) (π ^ n), map_pow]
      rfl
    have hπLval : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (((π : Q.adicCompletion K)) ^ n))
        = (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
      rw [map_pow, Valuation.map_pow]
      have h1 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) ((π : Q.adicCompletion K)))
          = (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) := by
        rw [show algebraMap (Q.adicCompletion K) (q.adicCompletion L)
              = ⇑(Commons.RingTheory.Henselian.adicCompletionMap Q q hq) from rfl]
        rw [Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq,
          hunr, pow_one, hπval]
      rw [h1, hpow]
    rw [hcoe, Valuation.map_mul, hπLval]
    calc (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) *
          Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s)
        ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) * 1 :=
          mul_le_mul' le_rfl s.2
      _ = (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := mul_one _

end TraceStep



section Newton

theorem newtonStep_local {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (z : Q.adicCompletion K) (hz : Valued.v z = 1)
    (n : ℕ) (hn : 1 ≤ n) (x : q.adicCompletionIntegers L) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Valued.v (Algebra.norm (Q.adicCompletion K)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) - z)
        ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) →
    ∃ x' : q.adicCompletionIntegers L,
      Valued.v (Algebra.norm (Q.adicCompletion K)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x') - z)
        ≤ (WithZero.exp (-(((n + 1 : ℕ) : ℤ))) : WithZero (Multiplicative ℤ)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hST : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletionIntegers_adicCompletion Q q hq
  haveI hST2 : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  classical
  intro hx
  have hpow : ((WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ))) ^ n
      = (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  set Nx : Q.adicCompletion K := Algebra.norm (Q.adicCompletion K)
    (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) with hNxdef
  have hNz : Valued.v (Nx - z) ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := hx
  have hNxval : Valued.v Nx = 1 := by
    have hlt : Valued.v (Nx - z) < Valued.v z := by
      rw [hz, ← WithZero.exp_zero]
      exact lt_of_le_of_lt hNz (WithZero.exp_lt_exp.mpr (by omega : (-(n : ℤ)) < 0))
    have h := Valuation.map_add_eq_of_lt_right (Valued.v) (x := Nx - z) (y := z) hlt
    have h2 : Nx - z + z = Nx := by ring
    rw [h2] at h
    exact h.trans hz
  have hNxne : Nx ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hNxval
    exact zero_ne_one hNxval
  set c : Q.adicCompletion K := (z - Nx) / Nx with hcdef
  have hcv : Valued.v c ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
    rw [hcdef, Valuation.map_div, hNxval, div_one]
    rw [show z - Nx = -(Nx - z) by ring, Valuation.map_neg]
    exact hNz
  obtain ⟨t, ht, htval⟩ := exists_trace_eq_of_val_le_local Q q hq hunr n c hcv
  have hunif : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)
        (Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q)) = WithZero.exp (-1) :=
    Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one q
  have htmem : t ∈ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ^ n := by
    rw [Commons.RingTheory.Henselian.mem_pow_maximalIdeal_iff q n t, hunif, hpow]
    exact htval
  refine ⟨x * (1 + t), ?_⟩
  set w : Q.adicCompletion K := Algebra.norm (Q.adicCompletion K)
      (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) ((1 + t : q.adicCompletionIntegers L) : q.adicCompletionIntegers L))
      - 1 - Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (t : q.adicCompletionIntegers L)) with hwdef
  have hw : Valued.v w ≤ (WithZero.exp (-(((2 * n : ℕ)) : ℤ)) : WithZero (Multiplicative ℤ)) := by
    rw [hwdef]
    exact val_norm_sub_one_sub_trace_le_local Q q hq hunr n hn t htmem
  have hN1t : Algebra.norm (Q.adicCompletion K)
      (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) ((1 + t : q.adicCompletionIntegers L) : q.adicCompletionIntegers L))
      = 1 + c + w := by
    rw [hwdef, ht]
    ring
  have hgoal : Algebra.norm (Q.adicCompletion K)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)
          ((x * (1 + t) : q.adicCompletionIntegers L) : q.adicCompletionIntegers L)) - z
      = Nx * w := by
    rw [map_mul, map_mul, ← hNxdef, hN1t, hcdef]
    field_simp
    ring
  rw [hgoal, Valuation.map_mul, hNxval, one_mul]
  exact hw.trans (WithZero.exp_le_exp.mpr (by omega))

end Newton

section Finite

theorem exists_norm_close_local {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (z : Q.adicCompletion K) (hz : Valued.v z = 1) (n : ℕ) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ x : q.adicCompletionIntegers L,
      Valued.v (Algebra.norm (Q.adicCompletion K)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) - z)
        ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  have hP : ∀ m : ℕ, 1 ≤ m → ∃ x : q.adicCompletionIntegers L,
      Valued.v (Algebra.norm (Q.adicCompletion K)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) - z)
        ≤ (WithZero.exp (-(m : ℤ)) : WithZero (Multiplicative ℤ)) := by
    intro m hm
    refine Nat.le_induction ?base ?step m hm
    · simpa using normResidueUnramified Q q hq hunr z hz
    · intro k hk ih
      exact newtonStep_local Q q hq hunr z hz k hk ih.choose ih.choose_spec
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    obtain ⟨x, hx⟩ := hP 1 le_rfl
    exact ⟨x, hx.trans (WithZero.exp_le_exp.mpr (by norm_num))⟩
  · exact hP n hpos

end Finite

section Ball

theorem isClosed_val_le_exp_neg {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    IsClosed {y : Q.adicCompletion K |
      Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) y
        ≤ (WithZero.exp (-(n : ℤ)) : Zstar0)} := by
  set π : Q.adicCompletionIntegers K :=
    Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q with hπdef
  have hπval : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
      ((π : Q.adicCompletion K)) = WithZero.exp (-1) :=
    Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one Q
  have hπne : ((π : Q.adicCompletion K)) ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hπval
    exact WithZero.exp_ne_zero (a := (-1 : ℤ)) hπval.symm
  have hpow : ((WithZero.exp (-1 : ℤ) : Zstar0)) ^ n = (WithZero.exp (-(n : ℤ)) : Zstar0) := by
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  have hπn : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
      (((π : Q.adicCompletion K)) ^ n) = (WithZero.exp (-(n : ℤ)) : Zstar0) := by
    rw [Valuation.map_pow, hπval, hpow]
  have hinv : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
      ((((π : Q.adicCompletion K)) ^ n)⁻¹) = (WithZero.exp ((n : ℤ)) : Zstar0) := by
    rw [Valuation.map_inv, hπn, ← WithZero.exp_neg]
    congr 1
    simp
  have hset : {y : Q.adicCompletion K | Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) y
        ≤ (WithZero.exp (-(n : ℤ)) : Zstar0)}
      = (fun z => (((π : Q.adicCompletion K)) ^ n) * z)
          '' (Valued.integer (Q.adicCompletion K) : Set (Q.adicCompletion K)) := by
    ext y
    constructor
    · intro hy
      refine ⟨((((π : Q.adicCompletion K)) ^ n))⁻¹ * y, ?_, ?_⟩
      · change Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
          (((((π : Q.adicCompletion K)) ^ n))⁻¹ * y) ≤ 1
        rw [Valuation.map_mul, hinv]
        calc (WithZero.exp ((n : ℤ)) : Zstar0) *
              Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) y
            ≤ (WithZero.exp ((n : ℤ)) : Zstar0) *
                (WithZero.exp (-(n : ℤ)) : Zstar0) := mul_le_mul' le_rfl hy
          _ = 1 := by rw [← WithZero.exp_add]; simp
      · exact mul_inv_cancel_left₀ (pow_ne_zero n hπne) y
    · rintro ⟨z, hz, rfl⟩
      change Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        ((((π : Q.adicCompletion K)) ^ n) * z) ≤ (WithZero.exp (-(n : ℤ)) : Zstar0)
      rw [Valuation.map_mul, hπn]
      calc (WithZero.exp (-(n : ℤ)) : Zstar0) *
            Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) z
          ≤ (WithZero.exp (-(n : ℤ)) : Zstar0) * 1 := mul_le_mul' le_rfl hz
        _ = (WithZero.exp (-(n : ℤ)) : Zstar0) := mul_one _
  rw [hset]
  exact (Homeomorph.isClosed_image
    (Homeomorph.mulLeft₀ (((π : Q.adicCompletion K)) ^ n) (pow_ne_zero n hπne))).mpr
    (Valued.isClosed_integer (Q.adicCompletion K))

end Ball

section Main

theorem continuous_algebraNorm_adicCompletion {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Continuous (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L → Q.adicCompletion K) := by
  letI nf : NontriviallyNormedField (Q.adicCompletion K) :=
    Valued.toNontriviallyNormedField (Q.adicCompletion K) (WithZero (Multiplicative ℤ))
  letI alg : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  haveI hcs : ContinuousSMul (Q.adicCompletion K) (q.adicCompletion L) :=
    continuousSMul_of_algebraMap (Q.adicCompletion K) (q.adicCompletion L) (by
      rw [RingHom.algebraMap_toAlgebra]
      exact Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq)
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  exact NK.NUV2.ArtinBridge.continuous_algebraNorm (𝕜 := Q.adicCompletion K) (A := q.adicCompletion L)

theorem localUnits_le_imageLocalNormFinite_of_ramificationIdx_eq_one {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    ∀ a ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q),
      ∃ u ∈ NK.GlobalCFT.Place.localUnits L (NK.GlobalCFT.Place.ofFinite q),
        NK.GlobalCFT.Place.localNormFinite q Q hq u = a := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hST : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletionIntegers_adicCompletion Q q hq
  haveI hST2 : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI hcomp : CompactSpace (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers L q
  haveI hlies : Ideal.LiesOver (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers Q q hq
  haveI hfree : Module.Free (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers Q q hq
  haveI hfin : Module.Finite (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers Q q hq
  haveI hint : Algebra.IsIntegral (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Algebra.IsIntegral.of_finite _ _
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  intro a ha
  have hav : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) (a : Q.adicCompletion K) = 1 :=
    (NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one (K := K) (q := Q)).mp ha
  set f : q.adicCompletionIntegers L → Q.adicCompletion K := fun x =>
    Algebra.norm (Q.adicCompletion K)
      (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x)
      - (a : Q.adicCompletion K) with hfdef
  have hfcont : Continuous f := by
    rw [hfdef]
    refine ((continuous_algebraNorm_adicCompletion Q q hq).comp ?_).sub continuous_const
    exact continuous_subtype_val
  set T : ℕ → Set (q.adicCompletionIntegers L) := fun n =>
    {x | Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) (f x)
      ≤ (WithZero.exp (-(n : ℤ)) : Zstar0)} with hTdef
  have hclosed : ∀ n, IsClosed (T n) := by
    intro n
    rw [hTdef]
    exact (isClosed_val_le_exp_neg Q n).preimage hfcont
  have hnonempty : ∀ n, (T n).Nonempty := by
    intro n
    obtain ⟨x, hx⟩ := exists_norm_close_local Q q hq hunr (a : Q.adicCompletion K) hav n
    exact ⟨x, by rw [hTdef, hfdef]; exact hx⟩
  have hnested : ∀ n, T (n + 1) ⊆ T n := by
    intro n x hx
    rw [hTdef] at hx ⊢
    exact hx.trans (WithZero.exp_le_exp.mpr (by simp))
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hnested
    hnonempty (isCompact_univ.of_isClosed_subset (hclosed 0) (Set.subset_univ _)) hclosed
  have hxmem : ∀ n, x ∈ T n := fun n => Set.mem_iInter.mp hx n
  have hfx : f x = 0 := by
    refine Commons.NumberTheory.NumberField.Completion.eq_zero_of_forall_val_le_exp_neg (Valued.v) ?_
    intro n
    have h := hxmem n
    rw [hTdef] at h
    exact h
  have hNx : Algebra.norm (Q.adicCompletion K)
      (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) = (a : Q.adicCompletion K) := by
    have h := hfx
    rw [hfdef] at h
    exact sub_eq_zero.mp h
  have hxval : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
      (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) = 1 := by
    by_contra hne
    have hle1 : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) ≤ 1 := x.2
    have hlt : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) < 1 :=
      lt_of_le_of_ne hle1 hne
    have hle : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x)
        ≤ WithZero.exp (-1) :=
      (Commons.NumberTheory.NumberField.Completion.le_exp_neg_one_iff).mpr hlt
    have hunifq : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)
          (Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q)) = WithZero.exp (-1) :=
      Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one q
    have hxmem' : x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
      have h2 : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) ≤
          (Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)
              (Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q))) ^ 1 := by
        rw [pow_one, hunifq]
        exact hle
      have h3 := (Commons.RingTheory.Henselian.mem_pow_maximalIdeal_iff q 1 x).mpr (by simpa using h2)
      rwa [pow_one] at h3
    have hmax : Ideal.map (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L))
        (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) =
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
      have h := Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow Q q hq
      rw [hunr, pow_one] at h
      exact h
    have hloc : IsLocalHom (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)) := by
      refine ⟨fun c hc => ?_⟩
      by_contra hcu
      have hcK : c ∈ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
        rw [IsLocalRing.mem_maximalIdeal]
        exact hcu
      have hmap : algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) c ∈
          IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
        rw [← hmax]
        exact Ideal.mem_map_of_mem _ hcK
      exact (IsLocalRing.notMem_maximalIdeal.mpr hc) hmap
    haveI := hloc
    have hres : IsLocalRing.residue (Q.adicCompletionIntegers K)
        (Algebra.norm (Q.adicCompletionIntegers K) x) = 0 := by
      rw [← Commons.RingTheory.Norm.residue_norm_eq (R := Q.adicCompletionIntegers K)
          (S := q.adicCompletionIntegers L) hmax x,
        (IsLocalRing.residue_eq_zero_iff _).mpr hxmem', Algebra.norm_zero]
    have hmemK : Algebra.norm (Q.adicCompletionIntegers K) x ∈
        IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) :=
      (IsLocalRing.residue_eq_zero_iff _).mp hres
    have hunifK : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
          (Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q)) = WithZero.exp (-1) :=
      Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one Q
    have hvalK : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
          (Algebra.norm (Q.adicCompletionIntegers K) x)) ≤ WithZero.exp (-1) := by
      have hmemK' : (Algebra.norm (Q.adicCompletionIntegers K) x) ∈
          (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) ^ 1 := by simpa using hmemK
      have h := (Commons.RingTheory.Henselian.mem_pow_maximalIdeal_iff Q 1
        (Algebra.norm (Q.adicCompletionIntegers K) x)).mp hmemK'
      rwa [pow_one, hunifK] at h
    have hnorm : algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (Algebra.norm (Q.adicCompletionIntegers K) x) = (a : Q.adicCompletion K) := by
      rw [← Algebra.intNorm_eq_norm (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)]
      rw [Algebra.algebraMap_intNorm (A := Q.adicCompletionIntegers K) (K := Q.adicCompletion K)
        (L := q.adicCompletion L) (B := q.adicCompletionIntegers L) x]
      exact hNx
    rw [hnorm, hav] at hvalK
    exact absurd hvalK (by rw [← WithZero.exp_zero]; exact not_le.mpr (WithZero.exp_lt_exp.mpr (by norm_num)))
  have hxne : algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hxval
    exact zero_ne_one hxval
  refine ⟨Units.mk0 (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) hxne, ?_, ?_⟩
  · rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
    exact hxval
  · rw [show NK.GlobalCFT.Place.localNormFinite q Q hq
        = Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)
        from rfl]
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_mk0]
    exact hNx

end Main


end NK.NUV2.ARL
