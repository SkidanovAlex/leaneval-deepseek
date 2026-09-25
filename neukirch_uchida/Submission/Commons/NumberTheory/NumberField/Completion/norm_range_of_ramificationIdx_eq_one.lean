import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
import Submission.Commons.RingTheory.Norm.residue_norm_eq
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one

open scoped NumberField WithZero
open IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- If `q` lies over `Q` with ramification index one, the induced map of adic completions
preserves the valuation. -/
lemma val_adicCompletionMap_eq_of_ramificationIdx_eq_one
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (x : Q.adicCompletion K) :
    Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq x) =
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x := by
  rw [val_adicCompletionMap_eq_pow Q q hq x, hunr, pow_one]

/-- If `q` lies over `Q` with ramification index one, the local degree equals the inertia
degree. -/
lemma finrank_adicCompletion_eq_inertiaDeg_of_ramificationIdx_eq_one
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    @Module.finrank (Q.adicCompletion K) (q.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)).toModule =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  rw [← finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq, hunr, one_mul]

/-! ## The product expansion estimate -/

/-- In a field `F` with a valuation `w` with values in a linearly ordered commutative group with
zero `Γ₀`, if all the `a i` (`i ∈ s`) have `w (a i) ≤ δ` where `δ ≤ 1`, then the "higher order"
part of the product `∏ i ∈ s, (1 + a i)` is bounded by `δ * δ`:

`w (∏ i ∈ s, (1 + a i) - 1 - ∑ i ∈ s, a i) ≤ δ * δ`.

In other words `∏ i ∈ s, (1 + a i) = 1 + ∑ i ∈ s, a i + O (δ * δ)`. -/
theorem prod_one_add_sub_one_sub_sum_le {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {F : Type*} [Field F] (w : Valuation F Γ₀) {ι : Type*} (s : Finset ι) (a : ι → F) (δ : Γ₀)
    (hδ : δ ≤ 1) (ha : ∀ i ∈ s, w (a i) ≤ δ) :
    w (∏ i ∈ s, (1 + a i) - 1 - ∑ i ∈ s, a i) ≤ δ * δ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have ha' : ∀ i ∈ t, w (a i) ≤ δ := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have ih' : w (∏ i ∈ t, (1 + a i) - 1 - ∑ i ∈ t, a i) ≤ δ * δ := ih ha'
    have hwj : w (a j) ≤ δ := ha j (Finset.mem_insert_self j t)
    have hS : w (∑ i ∈ t, a i) ≤ δ := Valuation.map_sum_le w ha'
    have h1aj : w (1 + a j) ≤ 1 :=
      Valuation.map_add_le w (le_of_eq (Valuation.map_one w)) (le_trans hwj hδ)
    have hident : (1 + a j) * (∏ i ∈ t, (1 + a i)) - 1 - (a j + ∑ i ∈ t, a i)
        = a j * (∑ i ∈ t, a i) + (∏ i ∈ t, (1 + a i) - 1 - ∑ i ∈ t, a i) * (1 + a j) := by
      ring
    rw [hident]
    refine Valuation.map_add_le w ?_ ?_
    · rw [Valuation.map_mul]
      exact le_trans (mul_le_mul' hwj hS) (by simp)
    · calc w ((∏ i ∈ t, (1 + a i) - 1 - ∑ i ∈ t, a i) * (1 + a j))
          = w (∏ i ∈ t, (1 + a i) - 1 - ∑ i ∈ t, a i) * w (1 + a j) :=
              Valuation.map_mul w _ _
        _ ≤ (δ * δ) * 1 := mul_le_mul' ih' h1aj
        _ = δ * δ := by simp

/-! ## The norm expansion to second order -/

/-- For `y` in the `q`-adic completion of `L` with `v y ≤ exp (-1)`, the difference
`N (1 + y) - 1 - Tr y` is of order `(v y)^2`. -/
lemma val_norm_sub_one_sub_trace_le
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ y : q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y ≤
          (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) →
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (Algebra.norm (Q.adicCompletion K) (1 + y) - 1 -
            Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) y) ≤
        (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y) *
          (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  have hvalemb : ∀ z : Q.adicCompletion K,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z) =
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) z := by
    intro z
    rw [RingHom.algebraMap_toAlgebra, val_adicCompletionMap_eq_pow Q q hq z, hunr, pow_one]
  intro y hy
  have hval : ∀ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (σ y) =
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y :=
    fun σ => val_algEquiv_adicCompletion Q q hq σ y
  have key : algebraMap (Q.adicCompletion K) (q.adicCompletion L)
      (Algebra.norm (Q.adicCompletion K) (1 + y) - 1 -
        Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) y) =
      (∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, (1 + σ y)) - 1 -
        ∑ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, σ y := by
    have h1 := Algebra.norm_eq_prod_automorphisms (Q.adicCompletion K) (1 + y)
    have h2 := trace_eq_sum_automorphisms (K := Q.adicCompletion K)
      (L := q.adicCompletion L) (x := y)
    have h3 : (∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, σ (1 + y)) =
        ∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, (1 + σ y) :=
      Finset.prod_congr rfl fun σ _ => by rw [map_add, map_one]
    rw [map_sub, map_sub, map_one, h1, h2, h3]
  have hgoal : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (Algebra.norm (Q.adicCompletion K) (1 + y) - 1 -
        Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) y) =
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        ((∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, (1 + σ y)) - 1 -
          ∑ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, σ y) := by
    rw [← hvalemb, key]
  have hδ1 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y ≤ 1 :=
    le_trans hy (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by norm_num))
  have ha : ∀ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (σ y) ≤
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y :=
    fun σ => le_of_eq (hval σ)
  calc Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (Algebra.norm (Q.adicCompletion K) (1 + y) - 1 -
          Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) y)
      = Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          ((∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, (1 + σ y)) - 1 -
            ∑ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, σ y) := hgoal
    _ ≤ Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y *
          Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y :=
        prod_one_add_sub_one_sub_sum_le _ Finset.univ _ _ hδ1 (fun σ _ => ha σ)

/-! ## Surjectivity of the trace on the rings of integers -/

section TraceSurj
attribute [local instance] Ideal.Quotient.field

/-- If `q` lies over `Q` with ramification index one, the trace of `L_q / K_Q` maps the ring of
integers of `L_q` onto the ring of integers of `K_Q`. -/
lemma trace_adicCompletionIntegers_surjective_of_ramificationIdx_eq_one
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ c : Q.adicCompletionIntegers K, ∃ s : q.adicCompletionIntegers L,
      Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s)
      = (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) c : Q.adicCompletion K) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (adicCompletionMapIntegers Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hfree : Module.Free (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    module_free_adicCompletionIntegers Q q hq
  haveI hfin : Module.Finite (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    module_finite_adicCompletionIntegers Q q hq
  haveI hST : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) := isScalarTower_adicCompletionIntegers_adicCompletion Q q hq
  haveI hST2 : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K)
      (q.adicCompletion L) := IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : IsFractionRing (Q.adicCompletionIntegers K) (Q.adicCompletion K) := inferInstance
  haveI : IsFractionRing (q.adicCompletionIntegers L) (q.adicCompletion L) := inferInstance
  have hmax : Ideal.map (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
    have h := map_maximalIdeal_eq_maximalIdeal_pow Q q hq
    rw [hunr, pow_one] at h
    exact h
  have trace_eq : ∀ x : q.adicCompletionIntegers L,
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
          (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x) =
      Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) := by
    intro x
    rw [← Algebra.intTrace_eq_trace (A := Q.adicCompletionIntegers K)
      (B := q.adicCompletionIntegers L)]
    exact Algebra.algebraMap_intTrace (A := Q.adicCompletionIntegers K)
      (B := q.adicCompletionIntegers L) (K := Q.adicCompletion K) (L := q.adicCompletion L) x
  let J : Ideal (q.adicCompletionIntegers L) :=
    Ideal.map (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
  have hJ : J = IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := hmax
  haveI : J.IsMaximal := by rw [hJ]; infer_instance
  haveI hfK : Finite (Q.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := by
    obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists Q
    haveI : Finite (𝓞 K ⧸ Q.asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q
    exact Finite.of_equiv (𝓞 K ⧸ Q.asIdeal) e.symm.toEquiv
  haveI hfL : Finite (q.adicCompletionIntegers L ⧸ J) := by
    obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists q
    haveI : Finite (𝓞 L ⧸ q.asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
    exact Finite.of_equiv (𝓞 L ⧸ q.asIdeal) (e.symm.trans (Ideal.quotEquivOfEq hJ).symm).toEquiv
  haveI : Module.Finite (Q.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) (q.adicCompletionIntegers L ⧸ J) :=
    Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (Q.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) (q.adicCompletionIntegers L ⧸ J) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : PerfectField (Q.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := PerfectField.ofFinite
  have hT : ∀ c : Q.adicCompletionIntegers K, ∃ x : q.adicCompletionIntegers L,
      Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x - c ∈
        IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
    intro c
    obtain ⟨ybar, hy⟩ := Algebra.trace_surjective
      (Q.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
      (q.adicCompletionIntegers L ⧸ J)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) c)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective ybar
    refine ⟨x, ?_⟩
    have hkey : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) c := by
      rw [← Algebra.trace_quotient_mk (R := Q.adicCompletionIntegers K)
        (S := q.adicCompletionIntegers L) x, hy]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hkey, sub_self]
  have hunit : ∃ (t : (Q.adicCompletionIntegers K)ˣ) (x₀ : q.adicCompletionIntegers L),
      Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x₀ =
        (t : Q.adicCompletionIntegers K) := by
    obtain ⟨x, hx⟩ := hT 1
    have hu : IsUnit (Algebra.trace (Q.adicCompletionIntegers K)
        (q.adicCompletionIntegers L) x) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      have h1 : (1 : Q.adicCompletionIntegers K) ∈
          IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
        have := (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).sub_mem hmem hx
        simpa using this
      exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one h1
    exact ⟨hu.unit, x, (IsUnit.unit_spec hu).symm⟩
  have hsurjR : ∀ c : Q.adicCompletionIntegers K, ∃ x : q.adicCompletionIntegers L,
      Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x = c := by
    obtain ⟨t, x₀, ht⟩ := hunit
    intro c
    refine ⟨(c * ((t⁻¹ : (Q.adicCompletionIntegers K)ˣ) : Q.adicCompletionIntegers K)) • x₀, ?_⟩
    rw [map_smul, ht, smul_eq_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mul_one]
  intro c
  obtain ⟨x, hx⟩ := hsurjR c
  exact ⟨x, by rw [← trace_eq x, hx]⟩

end TraceSurj

/-! ## The trace step with a valuation bound -/

section TraceStep

/-- If `q / Q` is unramified and `v d ≤ exp (-n)` for an element `d` of `K_Q`, then `d` is the
trace of an element of the ring of integers of `L_q` whose valuation is also `≤ exp (-n)`. -/
lemma exists_trace_eq_of_val_le
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ (n : ℕ) (d : Q.adicCompletion K),
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) d ≤
          (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) →
      ∃ s : q.adicCompletionIntegers L,
        Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) = d ∧
          Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) ≤
            (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (adicCompletionMapIntegers Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hST2 : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K)
      (q.adicCompletion L) := IsScalarTower.of_algebraMap_eq fun r => rfl
  obtain ⟨π, hπval, hπmax⟩ := exists_uniformizer_adicCompletionIntegers Q
  intro n d hd
  have hπne : (π : Q.adicCompletion K) ≠ 0 := by
    intro h0
    have h := hπval
    rw [h0, Valuation.map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  have hpowneg : (((WithZero.exp (-1 : ℤ)) : WithZero (Multiplicative ℤ))) ^ n =
      (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_nsmul]
    norm_num
  have hpowinv : ((((WithZero.exp (-1 : ℤ)) : WithZero (Multiplicative ℤ)))⁻¹) ^ n =
      (WithZero.exp (n : ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [show (((WithZero.exp (-1 : ℤ)) : WithZero (Multiplicative ℤ)))⁻¹ =
        (WithZero.exp (1 : ℤ) : WithZero (Multiplicative ℤ)) by rw [← WithZero.exp_neg]; norm_num,
      ← WithZero.exp_nsmul]
    norm_num
  have hc : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((π : Q.adicCompletion K))⁻¹ ^ n * d) ≤ 1 := by
    rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_inv, hπval, hpowinv]
    calc (WithZero.exp ((n : ℤ)) : WithZero (Multiplicative ℤ)) *
          Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) d
        ≤ (WithZero.exp ((n : ℤ)) : WithZero (Multiplicative ℤ)) *
            (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) :=
          mul_le_mul_of_nonneg_left hd zero_le
      _ = 1 := by rw [← WithZero.exp_add]; simp
  let c : Q.adicCompletionIntegers K :=
    ⟨(π : Q.adicCompletion K)⁻¹ ^ n * d,
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) (K := K)
        (v := Q)).mpr hc⟩
  obtain ⟨s, hs⟩ :=
    trace_adicCompletionIntegers_surjective_of_ramificationIdx_eq_one Q q hq hunr c
  haveI hST1 : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) := isScalarTower_adicCompletionIntegers_adicCompletion Q q hq
  have hvalemb : ∀ z : Q.adicCompletion K,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z) =
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) z := by
    intro z
    rw [RingHom.algebraMap_toAlgebra,
      val_adicCompletionMap_eq_of_ramificationIdx_eq_one Q q hq hunr z]
  have hcoe : algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) ((π ^ n) • s) =
      algebraMap (Q.adicCompletion K) (q.adicCompletion L) ((π : Q.adicCompletion K) ^ n) *
        algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s := by
    rw [Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
        (q.adicCompletion L) (π ^ n)]
    congr 1
  have hsn : algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) c =
      (π : Q.adicCompletion K)⁻¹ ^ n * d := rfl
  refine ⟨(π ^ n) • s, ?_, ?_⟩
  · rw [hcoe]
    have htr : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) ((π : Q.adicCompletion K) ^ n) *
          algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) =
        (π : Q.adicCompletion K) ^ n *
          Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) := by
      rw [← Algebra.smul_def, map_smul, Algebra.smul_def]
      simp
    rw [htr, hs, hsn, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hπne), one_mul]
  · rw [hcoe, Valuation.map_mul, hvalemb, Valuation.map_pow, hπval, hpowneg]
    calc (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) *
          Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s)
        ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) * 1 :=
          mul_le_mul_of_nonneg_left s.2 zero_le
      _ = (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := mul_one _

end TraceStep

/-! ## The residue step: units of `K_Q` are norms modulo the maximal ideal -/

section ResidueStep

/-- For `g` a unit of the ring of integers of `K_Q` there is an element `s` of the ring of
integers of `L_q` whose norm is congruent to `g` modulo the maximal ideal. -/
lemma exists_norm_sub_mem_maximalIdeal
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ g : Q.adicCompletion K,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) g = 1 →
      ∃ s : q.adicCompletionIntegers L,
        Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) - g) ≤
          (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (adicCompletionMapIntegers Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hfree : Module.Free (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    module_free_adicCompletionIntegers Q q hq
  haveI hfin : Module.Finite (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    module_finite_adicCompletionIntegers Q q hq
  haveI hST : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) := isScalarTower_adicCompletionIntegers_adicCompletion Q q hq
  haveI hST2 : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K)
      (q.adicCompletion L) := IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : IsFractionRing (Q.adicCompletionIntegers K) (Q.adicCompletion K) := inferInstance
  haveI : IsFractionRing (q.adicCompletionIntegers L) (q.adicCompletion L) := inferInstance
  have hmax : Ideal.map (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
    have h := map_maximalIdeal_eq_maximalIdeal_pow Q q hq
    rw [hunr, pow_one] at h
    exact h
  have norm_eq : ∀ x : q.adicCompletionIntegers L,
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
          (Algebra.norm (Q.adicCompletionIntegers K) x) =
      Algebra.norm (Q.adicCompletion K)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) := by
    intro x
    rw [← Algebra.intNorm_eq_norm (A := Q.adicCompletionIntegers K)
      (B := q.adicCompletionIntegers L)]
    exact Algebra.algebraMap_intNorm (A := Q.adicCompletionIntegers K)
      (B := q.adicCompletionIntegers L) (K := Q.adicCompletion K) (L := q.adicCompletion L) x
  intro g hg
  let gR : Q.adicCompletionIntegers K :=
    ⟨g, (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) (K := K)
      (v := Q)).mpr (le_of_eq hg)⟩
  have hgunit : IsUnit gR :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (R := 𝓞 K) (K := K) (v := Q)).mpr hg
  haveI hfR : Finite (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) := by
    obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists Q
    haveI : Finite (𝓞 K ⧸ Q.asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q
    exact Finite.of_equiv (𝓞 K ⧸ Q.asIdeal) e.symm.toEquiv
  haveI hfS : Finite (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) := by
    obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists q
    haveI : Finite (𝓞 L ⧸ q.asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
    exact Finite.of_equiv (𝓞 L ⧸ q.asIdeal) e.symm.toEquiv
  obtain ⟨b, hb⟩ := FiniteField.unitsMap_norm_surjective
    (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))
    (IsLocalRing.ResidueField (q.adicCompletionIntegers L))
    (Units.map (IsLocalRing.residue (Q.adicCompletionIntegers K)).toMonoidHom hgunit.unit)
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := q.adicCompletionIntegers L)
    (b : IsLocalRing.ResidueField (q.adicCompletionIntegers L))
  have hxunit : IsUnit x := (IsLocalRing.residue_ne_zero_iff_isUnit x).mp (by rw [hx]; exact b.ne_zero)
  have hb' : Algebra.norm (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))
        (IsLocalRing.residue (q.adicCompletionIntegers L) x) =
      IsLocalRing.residue (Q.adicCompletionIntegers K) gR := by
    have h1 : (Algebra.norm (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)))
        (b : IsLocalRing.ResidueField (q.adicCompletionIntegers L)) =
        IsLocalRing.residue (Q.adicCompletionIntegers K) (hgunit.unit :
          Q.adicCompletionIntegers K) := by
      have := congrArg (fun u : (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))ˣ =>
        (u : IsLocalRing.ResidueField (Q.adicCompletionIntegers K))) hb
      simpa [Units.coe_map] using this
    rw [hx]
    simpa [IsUnit.unit_spec] using h1
  have hres : Algebra.norm (Q.adicCompletionIntegers K) x - gR ∈
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, (Commons.RingTheory.Norm.residue_norm_eq hmax x).symm,
      hb', sub_self]
  refine ⟨x, ?_⟩
  have hfield : Algebra.norm (Q.adicCompletion K)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) - g =
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (Algebra.norm (Q.adicCompletionIntegers K) x - gR) := by
    rw [map_sub, norm_eq]
    rfl
  rw [hfield, Commons.NumberTheory.NumberField.Completion.le_exp_neg_one_iff]
  exact (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
    Q (Algebra.norm (Q.adicCompletionIntegers K) x - gR)).mp hres

example (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) : True := by
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (adicCompletionMapIntegers Q q hq)
  haveI hfree : Module.Free (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    module_free_adicCompletionIntegers Q q hq
  haveI hfin : Module.Finite (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    module_finite_adicCompletionIntegers Q q hq
  haveI hfR : Finite (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) := by
    obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists Q
    haveI : Finite (𝓞 K ⧸ Q.asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q
    exact Finite.of_equiv (𝓞 K ⧸ Q.asIdeal) e.symm.toEquiv
  haveI hfS : Finite (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) := by
    obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists q
    haveI : Finite (𝓞 L ⧸ q.asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
    exact Finite.of_equiv (𝓞 L ⧸ q.asIdeal) e.symm.toEquiv
  have key := FiniteField.unitsMap_norm_surjective
    (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))
    (IsLocalRing.ResidueField (q.adicCompletionIntegers L))
  trivial

end ResidueStep

/-- In a field with a valuation with values in `ℤᵐ⁰`, a nonzero element has a value of the form
`exp k` with `k : ℤ`; hence an element whose value is at most `exp (-n)` for every `n` vanishes. -/
lemma eq_zero_of_forall_val_le_exp_neg {F : Type*} [Field F]
    (w : Valuation F Zstar0) {z : F} (h : ∀ n : ℕ, w z ≤ (WithZero.exp (-(n : ℤ)) : Zstar0)) :
    z = 0 := by
  by_contra hne
  have hvne : w z ≠ 0 := (Valuation.ne_zero_iff w).mpr hne
  set k : ℤ := (w z).log with hk
  have hv : w z = WithZero.exp k := (WithZero.exp_log hvne).symm
  have h1 : (-k : ℤ) ≤ (Int.toNat (-k) : ℤ) := Int.self_le_toNat (-k)
  have hcon := h (Int.toNat (-k) + 1)
  rw [hv, WithZero.exp_le_exp] at hcon
  have h2 : -(((Int.toNat (-k) + 1 : ℕ) : ℤ)) = -((Int.toNat (-k) : ℤ)) - 1 := by
    push_cast
    ring
  rw [h2] at hcon
  omega

/-! ## The Newton iteration: principal units are norms -/

section Newton

/-- For `u` in `K_Q` with `v (u - 1) ≤ exp (-1)` (a principal unit), `u` is the norm of an
element of `L_q`.  The proof is a Newton iteration for the norm map: the derivative of
`y ↦ N (1 + y)` at `0` is the trace, which is surjective on the rings of integers. -/
lemma exists_norm_eq_of_sub_one_mem_maximalIdeal
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ u : Q.adicCompletion K,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) (u - 1) ≤
        (WithZero.exp (-1 : ℤ) : Zstar0) →
      ∃ x : q.adicCompletion L, Algebra.norm (Q.adicCompletion K) x = u := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (adicCompletionMapIntegers Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hST1 : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) := isScalarTower_adicCompletionIntegers_adicCompletion Q q hq
  haveI hST2 : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K)
      (q.adicCompletion L) := IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  have hvalemb : ∀ z : Q.adicCompletion K,
      Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z) =
      Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) z := by
    intro z
    rw [RingHom.algebraMap_toAlgebra,
      val_adicCompletionMap_eq_of_ramificationIdx_eq_one Q q hq hunr z]
  -- membership in the powers of the maximal ideal via the valuation
  have hmem_pow : ∀ (k : ℕ) (y : q.adicCompletionIntegers L),
      y ∈ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ^ k ↔
        Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) y) ≤
          (WithZero.exp (-(k : ℤ)) : Zstar0) := by
    intro k y
    have hexp : (((WithZero.exp (-1 : ℤ)) : Zstar0)) ^ k =
        (WithZero.exp (-(k : ℤ)) : Zstar0) := by
      rw [← WithZero.exp_nsmul]
      norm_num
    have huf : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)
          (Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q)) =
        (WithZero.exp (-1 : ℤ) : Zstar0) :=
      Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one q
    rw [Commons.RingTheory.Henselian.mem_pow_maximalIdeal_iff, huf, hexp]
  -- the norm of an element of norm `1` again has norm `1`
  have hnorm_one : ∀ z : q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0) z = 1 →
      Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (Algebra.norm (Q.adicCompletion K) z) = 1 := by
    intro z hz
    have h1 := val_norm_adicCompletion_eq_pow Q q hq z
    rw [hvalemb, hz, one_pow] at h1
    exact h1
  -- elements of `1 + 𝔪` have norm one
  have hnorm_one_of : ∀ z : q.adicCompletionIntegers L,
      z - 1 ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) →
      Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) z) = 1 := by
    intro z hz
    have hz1 : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (z - 1)) ≤
        (WithZero.exp (-1 : ℤ) : Zstar0) := by
      have h := (hmem_pow 1 (z - 1)).mp (by simpa using hz)
      simpa using h
    have hz2 : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) z) ≤ 1 := by
      have h2 : algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) z =
          algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (z - 1) + 1 := by
        rw [map_sub, map_one, sub_add_cancel]
      rw [h2]
      calc Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (z - 1) + 1)
          ≤ max (Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
                (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (z - 1)))
              (Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0) (1 : q.adicCompletion L)) :=
            Valuation.map_add_le _ (le_max_left _ _) (le_max_right _ _)
        _ ≤ max (WithZero.exp (-1 : ℤ)) 1 := by
            refine max_le_max hz1 ?_
            exact le_of_eq (Valuation.map_one _)
        _ = 1 := max_eq_right (by
            rw [← WithZero.exp_zero]
            exact WithZero.exp_le_exp.mpr (by norm_num))
    refine le_antisymm hz2 ?_
    by_contra hlt
    rw [not_le] at hlt
    have hkey : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0) (1 : q.adicCompletion L) < 1 := by
      have h := Valuation.map_add_le (v := (Valued.v : Valuation (q.adicCompletion L) Zstar0))
        (x := (1 : q.adicCompletion L) -
          algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) z)
        (y := algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) z)
        (le_max_left _ _) (le_max_right _ _)
      rw [sub_add_cancel] at h
      refine lt_of_le_of_lt h (max_lt ?_ hlt)
      have hneg : (1 : q.adicCompletion L) - algebraMap (q.adicCompletionIntegers L)
          (q.adicCompletion L) z =
          -(algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (z - 1)) := by
        rw [map_sub, map_one]
        ring
      rw [hneg, Valuation.map_neg]
      exact lt_of_le_of_lt hz1 (by
        rw [← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by norm_num))
    rw [Valuation.map_one] at hkey
    exact absurd hkey (lt_irrefl (1 : Zstar0))
  intro u hu
  -- the Newton step
  have hstep : ∀ (m : ℕ) (x : q.adicCompletionIntegers L),
      (x - 1 ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) →
      Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (Algebra.norm (Q.adicCompletion K)
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) - u) ≤
        (WithZero.exp (-((m + 1 : ℕ) : ℤ)) : Zstar0) →
      ∃ x' : q.adicCompletionIntegers L,
        (x' - 1 ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ∧
        (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
          (Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x') - u) ≤
          (WithZero.exp (-((m + 2 : ℕ) : ℤ)) : Zstar0)) ∧
        (x' - x ∈ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ^ (m + 1)) := by
    intro m x hx1 hxerr
    have hvx := hnorm_one_of x hx1
    have hNx := hnorm_one _ hvx
    set Nx := Algebra.norm (Q.adicCompletion K)
      (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) with hNxdef
    have hNx0 : Nx ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hNx
      exact zero_ne_one hNx
    set d : Q.adicCompletion K := (u - Nx) / Nx with hddef
    have hdval : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) d ≤
        (WithZero.exp (-((m + 1 : ℕ) : ℤ)) : Zstar0) := by
      rw [hddef, Valuation.map_div, hNx, div_one]
      rw [show u - Nx = -(Nx - u) by ring, Valuation.map_neg]
      exact hxerr
    obtain ⟨s, hs, hsval⟩ := exists_trace_eq_of_val_le Q q hq hunr (m + 1) d hdval
    have hle1 : (WithZero.exp (-((m + 1 : ℕ) : ℤ)) : Zstar0) ≤
        (WithZero.exp (-1 : ℤ) : Zstar0) :=
      WithZero.exp_le_exp.mpr (by push_cast; omega)
    refine ⟨x * (1 + s), ?_, ?_, ?_⟩
    · -- `1 + 𝔪` is preserved
      have hs1 : s ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
        have h := (hmem_pow 1 s).mpr (le_trans hsval hle1)
        simpa using h
      have hmem : x * (1 + s) - 1 = (x - 1) + x * s := by ring
      rw [hmem]
      exact (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).add_mem hx1
        (Ideal.mul_mem_left _ _ hs1)
    · -- the error improves
      have hw : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) ≤
          (WithZero.exp (-1 : ℤ) : Zstar0) := le_trans hsval hle1
      have hrho := val_norm_sub_one_sub_trace_le Q q hq hunr
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) hw
      have htr : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) = d := hs
      have hNd : Nx * d = u - Nx := by
        rw [hddef, mul_div_cancel₀ _ hNx0]
      have hkey : Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (x * (1 + s))) - u =
          Nx * (Algebra.norm (Q.adicCompletion K)
                (1 + algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) - 1 -
              Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
                (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s)) := by
        have h1 : algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (x * (1 + s)) =
            algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x *
              (1 + algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) := by
          rw [map_mul, map_add, map_one]
        rw [h1, map_mul, htr]
        rw [mul_sub, mul_sub, mul_one, hNd]
        ring
      rw [hkey, Valuation.map_mul, hNx, one_mul]
      refine le_trans hrho ?_
      calc Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
              (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) *
            Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
              (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s)
          ≤ (WithZero.exp (-((m + 1 : ℕ) : ℤ)) : Zstar0) *
            (WithZero.exp (-((m + 1 : ℕ) : ℤ)) : Zstar0) :=
            mul_le_mul hsval hsval zero_le zero_le
        _ = (WithZero.exp (-((m + 1 : ℕ) : ℤ) + -((m + 1 : ℕ) : ℤ)) : Zstar0) :=
            (WithZero.exp_add _ _).symm
        _ ≤ (WithZero.exp (-((m + 2 : ℕ) : ℤ)) : Zstar0) :=
            WithZero.exp_le_exp.mpr (by push_cast; omega)
    · -- the increment
      have hmem : x * (1 + s) - x = x * s := by ring
      rw [hmem]
      exact Ideal.mul_mem_left _ _ ((hmem_pow (m + 1) s).mpr hsval)
  -- the next element of the sequence, together with the invariant
  have hex : ∀ (m : ℕ) (x : q.adicCompletionIntegers L), ∃ x' : q.adicCompletionIntegers L,
      ((x - 1 ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) →
        (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
          (Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) - u) ≤
          (WithZero.exp (-((m + 1 : ℕ) : ℤ)) : Zstar0)) →
        (x' - 1 ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ∧
        (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
          (Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x') - u) ≤
          (WithZero.exp (-((m + 2 : ℕ) : ℤ)) : Zstar0)) ∧
        (x' - x ∈ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ^ (m + 1))) := by
    intro m x
    by_cases h : (x - 1 ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ∧
        (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
          (Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) - u) ≤
          (WithZero.exp (-((m + 1 : ℕ) : ℤ)) : Zstar0))
    · exact ⟨Classical.choose (hstep m x h.1 h.2),
        fun _ _ => Classical.choose_spec (hstep m x h.1 h.2)⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  let next : ℕ → q.adicCompletionIntegers L → q.adicCompletionIntegers L := fun m x =>
    Classical.choose (hex m x)
  let seq : ℕ → q.adicCompletionIntegers L := fun m => Nat.rec 1 next m
  have hnext : ∀ m : ℕ, seq (m + 1) = Classical.choose (hex m (seq m)) := fun m => rfl
  have hseq : ∀ m : ℕ,
      (seq m - 1 ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ∧
      (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (Algebra.norm (Q.adicCompletion K)
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq m)) - u) ≤
        (WithZero.exp (-((m + 1 : ℕ) : ℤ)) : Zstar0)) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [seq]
      · have h1 : Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)
              (1 : q.adicCompletionIntegers L)) = 1 := by rw [map_one, map_one]
        rw [show seq 0 = (1 : q.adicCompletionIntegers L) from rfl, h1,
          show (1 : Q.adicCompletion K) - u = -(u - 1) by ring, Valuation.map_neg]
        simpa using hu
    | succ m ih =>
      have h := Classical.choose_spec (hex m (seq m)) ih.1 ih.2
      exact ⟨by rw [hnext m]; exact h.1, by rw [hnext m]; exact h.2.1⟩
  have hseq_one : ∀ m : ℕ, seq m - 1 ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) :=
    fun m => (hseq m).1
  have hseq_err : ∀ m : ℕ,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (Algebra.norm (Q.adicCompletion K)
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq m)) - u) ≤
        (WithZero.exp (-((m + 1 : ℕ) : ℤ)) : Zstar0) :=
    fun m => (hseq m).2
  have hseq_incr : ∀ m : ℕ, seq (m + 1) - seq m ∈
      (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ^ (m + 1) := by
    intro m
    have h := Classical.choose_spec (hex m (seq m)) (hseq m).1 (hseq m).2
    rw [hnext m]
    exact h.2.2
  -- the sequence is compatible for the adic topology
  have hsm : ∀ m n : ℕ, m ≤ n → seq m - seq n ∈
      (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ^ m := by
    intro m n hmn
    induction n with
    | zero =>
      rw [show m = 0 from by omega]
      simp
    | succ n ih =>
      by_cases hmn' : m ≤ n
      · have h1 : seq m - seq (n + 1) = (seq m - seq n) - (seq (n + 1) - seq n) := by ring
        rw [h1]
        exact (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ m).sub_mem (ih hmn')
          (Ideal.pow_le_pow_right (by omega) (hseq_incr n))
      · rw [show m = n + 1 from by omega]
        simp
  -- the limit
  obtain ⟨xL, hxL⟩ := (Commons.RingTheory.Henselian.isPrecomplete_adicCompletionIntegers
    (R := 𝓞 L) (K := L) q).prec' seq (fun {m n : ℕ} hmn => by
      rw [SModEq.sub_mem]
      simpa [Ideal.smul_eq_mul] using hsm m n hmn)
  refine ⟨algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) xL, ?_⟩
  -- `N (emb xL) = u`
  have hLmem : ∀ n : ℕ, xL - seq n ∈
      (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ^ n := by
    intro n
    have h := hxL n
    rw [SModEq.sub_mem] at h
    have h' : seq n - xL ∈ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ^ n := by
      simpa [Ideal.smul_eq_mul] using h
    rw [show xL - seq n = -(seq n - xL) by ring]
    exact neg_mem h'
  have hconv : ∀ n : ℕ,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (Algebra.norm (Q.adicCompletion K)
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) xL) - u) ≤
        (WithZero.exp (-((n : ℤ))) : Zstar0) := by
    intro n
    have hvx : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1))) = 1 :=
      hnorm_one_of _ (hseq_one (n + 1))
    have hx0 : algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1)) ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hvx
      exact one_ne_zero hvx.symm
    have hδ : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (xL - seq (n + 1))) ≤
        (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) :=
      (hmem_pow (n + 1) _).mp (hLmem (n + 1))
    set w : q.adicCompletion L :=
      algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (xL - seq (n + 1)) /
        algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1)) with hwdef
    have hw : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0) w ≤
        (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) := by
      rw [hwdef, Valuation.map_div, hvx, div_one]
      exact hδ
    have hw1 : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0) w ≤
        (WithZero.exp (-1 : ℤ) : Zstar0) :=
      le_trans hw (WithZero.exp_le_exp.mpr (by push_cast; omega))
    have hfact : algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) xL =
        algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1)) * (1 + w) := by
      rw [hwdef, map_sub]
      field_simp
      ring
    have hNx : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (Algebra.norm (Q.adicCompletion K)
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1)))) = 1 :=
      hnorm_one _ hvx
    have hrho := val_norm_sub_one_sub_trace_le Q q hq hunr w hw1
    have htr : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) w) ≤
        (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) := by
      have h1 : algebraMap (Q.adicCompletion K) (q.adicCompletion L)
          (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) w) =
          ∑ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, σ w :=
        trace_eq_sum_automorphisms (K := Q.adicCompletion K)
          (L := q.adicCompletion L) (x := w)
      rw [← hvalemb, h1]
      refine le_trans (Valuation.map_sum_le _ (fun σ _ => ?_)) hw
      rw [val_algEquiv_adicCompletion Q q hq σ w]
    -- the factorisation of the difference of the norms
    have hsplit : Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) xL) -
          Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1))) =
        Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1))) *
          Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) w +
        Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1))) *
          (Algebra.norm (Q.adicCompletion K) (1 + w) - 1 -
            Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) w) := by
      rw [hfact, map_mul]
      ring
    have hcmp : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) xL) -
          Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1)))) ≤
        (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) := by
      rw [hsplit]
      refine le_trans (Valuation.map_add_le _ (le_max_left _ _) (le_max_right _ _)) (max_le ?_ ?_)
      · calc Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
              (Algebra.norm (Q.adicCompletion K)
                  (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1))) *
                Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) w)
            = Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
                (Algebra.norm (Q.adicCompletion K)
                  (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1)))) *
              Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
                (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) w) :=
              Valuation.map_mul _ _ _
          _ ≤ 1 * (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) :=
              mul_le_mul (le_of_eq hNx) htr zero_le zero_le
          _ = (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) := one_mul _
      · calc Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
              (Algebra.norm (Q.adicCompletion K)
                  (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1))) *
                (Algebra.norm (Q.adicCompletion K) (1 + w) - 1 -
                  Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) w))
            = Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
                (Algebra.norm (Q.adicCompletion K)
                  (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1)))) *
              Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
                (Algebra.norm (Q.adicCompletion K) (1 + w) - 1 -
                  Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) w) :=
              Valuation.map_mul _ _ _
          _ ≤ 1 * (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) := by
              refine mul_le_mul (le_of_eq hNx) ?_ zero_le zero_le
              refine le_trans hrho ?_
              calc (Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0) w) *
                    Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0) w
                  ≤ (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) *
                    (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) :=
                    mul_le_mul hw hw zero_le zero_le
                _ = (WithZero.exp (-((n + 1 : ℕ) : ℤ) + -((n + 1 : ℕ) : ℤ)) : Zstar0) :=
                    (WithZero.exp_add _ _).symm
                _ ≤ (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) :=
                    WithZero.exp_le_exp.mpr (by push_cast; omega)
          _ = (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) := one_mul _
    -- combine with the error at level `n + 1`
    calc Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
          (Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) xL) - u)
        ≤ max (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
              (Algebra.norm (Q.adicCompletion K)
                  (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) xL) -
                Algebra.norm (Q.adicCompletion K)
                  (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1)))))
            (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
              (Algebra.norm (Q.adicCompletion K)
                (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1))) - u)) := by
          rw [show Algebra.norm (Q.adicCompletion K)
              (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) xL) - u =
              (Algebra.norm (Q.adicCompletion K)
                  (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) xL) -
                Algebra.norm (Q.adicCompletion K)
                  (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1)))) +
              (Algebra.norm (Q.adicCompletion K)
                (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) (seq (n + 1))) - u)
            by ring]
          exact Valuation.map_add_le _ (le_max_left _ _) (le_max_right _ _)
      _ ≤ max (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0)
            (WithZero.exp (-((n + 1 : ℕ) : ℤ)) : Zstar0) :=
          max_le_max hcmp (le_trans (hseq_err (n + 1))
            (WithZero.exp_le_exp.mpr (by push_cast; omega)))
      _ ≤ (WithZero.exp (-((n : ℤ))) : Zstar0) := by
          rw [max_self]
          exact WithZero.exp_le_exp.mpr (by push_cast; omega)
  have hzero : Algebra.norm (Q.adicCompletion K)
      (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) xL) - u = 0 :=
    eq_zero_of_forall_val_le_exp_neg (Valued.v : Valuation (Q.adicCompletion K) Zstar0) hconv
  exact sub_eq_zero.mp hzero

end Newton


theorem norm_range_of_ramificationIdx_eq_one {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ y : Q.adicCompletion K,
      (∃ x : q.adicCompletion L, Algebra.norm (Q.adicCompletion K) x = y) ↔
      ∃ z : Q.adicCompletion K,
        Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) y =
          (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) z) ^
            (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  have hvalemb : ∀ z : Q.adicCompletion K,
      Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z) =
      Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) z := by
    intro z
    rw [RingHom.algebraMap_toAlgebra,
      val_adicCompletionMap_eq_of_ramificationIdx_eq_one Q q hq hunr z]
  have hfne : q.asIdeal.inertiaDeg (𝓞 K) ≠ 0 := (Ideal.inertiaDeg_pos q.asIdeal (𝓞 K)).ne'
  -- the norm formula with the inertia degree
  have hfin : ∀ x : q.adicCompletion L,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
          (Algebra.norm (Q.adicCompletion K) x) =
        (Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0) x) ^
          (q.asIdeal.inertiaDeg (𝓞 K)) := by
    intro x
    have h1 := val_norm_adicCompletion_eq_pow Q q hq x
    rw [finrank_adicCompletion_eq_inertiaDeg_of_ramificationIdx_eq_one Q q hq hunr] at h1
    rw [← hvalemb, h1]
  intro y
  constructor
  · -- norms have value in the subgroup of `f`-th powers
    rintro ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := Commons.RingTheory.Henselian.adicCompletion_valued_surjective Q
      (Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0) x)
    exact ⟨z, by rw [hfin x, hz]⟩
  · -- elements whose value is an `f`-th power are norms
    rintro ⟨z, hz⟩
    by_cases hy : y = 0
    · refine ⟨0, ?_⟩
      rw [hy, Algebra.norm_zero]
    have hvy0 : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) y ≠ 0 :=
      (Valuation.ne_zero_iff (Valued.v : Valuation (Q.adicCompletion K) Zstar0)).mpr hy
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_pow hfne] at hz
      exact hvy0 hz
    set w : q.adicCompletion L := algebraMap (Q.adicCompletion K) (q.adicCompletion L) z with hwdef
    have hNw : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (Algebra.norm (Q.adicCompletion K) w) =
        Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) y := by
      rw [hfin w, hwdef, hvalemb, hz]
    have hNw0 : Algebra.norm (Q.adicCompletion K) w ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hNw
      exact hvy0 hNw.symm
    set u : Q.adicCompletion K := y / Algebra.norm (Q.adicCompletion K) w with hudef
    have hu : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) u = 1 := by
      rw [hudef, Valuation.map_div, hNw, div_self hvy0]
    -- the residue step
    obtain ⟨s, hs⟩ := exists_norm_sub_mem_maximalIdeal Q q hq hunr u hu
    have hNs : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
        (Algebra.norm (Q.adicCompletion K)
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s)) = 1 := by
      have hle1 : (WithZero.exp (-1 : ℤ) : Zstar0) ≤ 1 := by
        rw [← WithZero.exp_zero]
        exact WithZero.exp_le_exp.mpr (by norm_num)
      have h1 : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
          (Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s)) ≤ 1 := by
        have h := Valuation.map_add_le (v := (Valued.v : Valuation (Q.adicCompletion K) Zstar0))
          (x := Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) - u)
          (y := u) (le_trans hs hle1) (le_of_eq hu)
        rw [sub_add_cancel] at h
        exact h
      refine le_antisymm h1 ?_
      by_contra hlt
      rw [not_le] at hlt
      have h2 : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) u < 1 := by
        have h := Valuation.map_add_le (v := (Valued.v : Valuation (Q.adicCompletion K) Zstar0))
          (x := u - Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s))
          (y := Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s))
          (le_max_left _ _) (le_max_right _ _)
        rw [sub_add_cancel] at h
        refine lt_of_le_of_lt h (max_lt ?_ hlt)
        rw [show u - Algebra.norm (Q.adicCompletion K)
              (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) =
            -(Algebra.norm (Q.adicCompletion K)
              (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) - u) by ring,
          Valuation.map_neg]
        exact lt_of_le_of_lt hs (by
          rw [← WithZero.exp_zero]
          exact WithZero.exp_lt_exp.mpr (by norm_num))
      rw [hu] at h2
      exact absurd h2 (lt_irrefl (1 : Zstar0))
    have hNs0 : Algebra.norm (Q.adicCompletion K)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hNs
      exact one_ne_zero hNs.symm
    -- the remaining principal unit
    set u' : Q.adicCompletion K :=
      u / Algebra.norm (Q.adicCompletion K)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) with hu'def
    have hu' : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) (u' - 1) ≤
        (WithZero.exp (-1 : ℤ) : Zstar0) := by
      have hd : u' - 1 = (u - Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s)) /
            Algebra.norm (Q.adicCompletion K)
              (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) := by
        rw [hu'def]
        field_simp
      rw [hd, Valuation.map_div, hNs, div_one,
        show u - Algebra.norm (Q.adicCompletion K)
              (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) =
            -(Algebra.norm (Q.adicCompletion K)
              (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) - u) by ring,
        Valuation.map_neg]
      exact hs
    obtain ⟨x₁, hx₁⟩ := exists_norm_eq_of_sub_one_mem_maximalIdeal Q q hq hunr u' hu'
    refine ⟨w * algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s * x₁, ?_⟩
    have hmain : Algebra.norm (Q.adicCompletion K)
        (w * algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s * x₁) = y := by
      rw [map_mul, map_mul, hx₁, hu'def, hudef]
      field_simp
    exact hmain

end Commons.NumberTheory.NumberField.Completion
