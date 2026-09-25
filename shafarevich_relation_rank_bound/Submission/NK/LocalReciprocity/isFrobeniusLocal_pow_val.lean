import Mathlib
import Submission.NK.LocalReciprocity.LocalSetup

/-!
# Powers of the local Frobenius

Let `L / K` be a finite Galois extension of number fields, `Q` a finite place of `K` and `q` a
place of `L` above `Q`.  The canonical Frobenius of the local extension `L_q / K_Q` is the
`K_Q`-automorphism `σ` of `L_q = q.adicCompletion L` acting on the ring of integers by
`σ x ≡ x ^ #k_Q (mod 𝔪)` (`NK.LocalReciprocity.IsFrobeniusLocal`).

This file proves that the `m`-th power of such a `σ` acts by the `#k_Q ^ m`-th power map modulo
`𝔪`, i.e. that the congruence is compatible with iteration:
`σ ^ m (x) ≡ x ^ (#k_Q ^ m) (mod 𝔪)` for every integral `x`.  This is the statement that the
"Frobenius congruence" sees the group law: it says that the assignment `m ↦ σ ^ m` respects the
exponentiation of the residue field Frobenius, and hence that the order of `σ` is the order of
the Frobenius on the residue field (cf. `orderOf_eq_inertiaDeg_of_isFrobeniusLocal`).

The proof is the obvious congruence induction.  Write `q = #k_Q`.  Given
`v (σ^m x - x ^ (q^m)) < 1`, put `y = σ^m x`, which is again integral because every
`K_Q`-automorphism of `L_q` preserves the ring of integers
(`Commons.NumberTheory.NumberField.Completion.algEquiv_mem_adicCompletionIntegers_iff_adicCompletion`).
Then
`σ^(m+1) x - x ^ (q^(m+1)) = (σ y - y^q) + (y^q - (x ^ (q^m))^q)`,
where the first summand has valuation `< 1` by the Frobenius condition applied to `y`, and the
second because `y ≡ x ^ (q^m) (mod 𝔪)` and the `q`-th power map preserves congruences modulo the
maximal ideal (`y^q - (x^(q^m))^q` is divisible by `y - x^(q^m)`).  Both summands lie in the
maximal ideal, and the valuation of a sum of two elements of the maximal ideal is `< 1`.

The hypothesis `[FiniteDimensional K L]` is not used in the argument beyond the import of the
integrality statement, but it is part of the setting. -/

namespace NK.LocalReciprocity

theorem isFrobeniusLocal_pow_val {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [hq : q.asIdeal.LiesOver Q.asIdeal]
    (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
    (h : NK.LocalReciprocity.IsFrobeniusLocal Q q σ) (m : ℕ) :
    ∀ x : q.adicCompletionIntegers L,
      Valued.v ((σ ^ m) (x : q.adicCompletion L) -
        (x : q.adicCompletion L) ^ ((NK.LocalReciprocity.residueCard K Q) ^ m)) < 1 := by
  classical
  -- Every `K_Q`-algebra automorphism of `L_q` preserves the ring of integers.
  have hpres : ∀ (τ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (y : q.adicCompletion L),
      τ y ∈ q.adicCompletionIntegers L ↔ y ∈ q.adicCompletionIntegers L :=
    fun τ y =>
      Commons.NumberTheory.NumberField.Completion.algEquiv_mem_adicCompletionIntegers_iff_adicCompletion
        Q q hq τ y
  -- The maximal ideal of the ring of integers is the open unit ball.
  have hmem_iff : ∀ z : q.adicCompletionIntegers L,
      z ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ↔
        Valued.v (z : q.adicCompletion L) < (1 : Zstar0) :=
    fun z =>
      Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one q z
  -- The iterates of `σ` preserve the ring of integers.
  have hpow : ∀ (m : ℕ) (x : q.adicCompletionIntegers L),
      (σ ^ m) (x : q.adicCompletion L) ∈ q.adicCompletionIntegers L := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', AlgEquiv.mul_apply]
      exact (hpres σ _).mpr (ih x)
  induction m with
  | zero =>
    intro x
    simp
  | succ m ih =>
    intro x
    -- `y = σ^m x`, again integral
    let y : q.adicCompletionIntegers L := ⟨(σ ^ m) (x : q.adicCompletion L), hpow m x⟩
    -- the induction hypothesis at level `m`
    have h1 : (y - x ^ (residueCard K Q ^ m) : q.adicCompletionIntegers L) ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
      refine (hmem_iff _).mpr ?_
      simpa [y] using ih x
    -- the Frobenius condition applied to `y`
    have h2 : ((⟨σ (y : q.adicCompletion L), (hpres σ _).mpr y.2⟩ : q.adicCompletionIntegers L)
        - y ^ residueCard K Q) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
      refine (hmem_iff _).mpr ?_
      simpa [y] using h y
    -- the `q`-th power map preserves congruence modulo the maximal ideal
    have h3 : (y ^ residueCard K Q - (x ^ (residueCard K Q ^ m)) ^ residueCard K Q :
        q.adicCompletionIntegers L) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
      obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow y (x ^ (residueCard K Q ^ m)) (residueCard K Q)
      rw [ht]
      exact Ideal.mul_mem_right t _ h1
    -- sum of the two congruent terms
    have h4 : ((⟨σ (y : q.adicCompletion L), (hpres σ _).mpr y.2⟩ : q.adicCompletionIntegers L)
        - (x ^ (residueCard K Q ^ m)) ^ residueCard K Q :
        q.adicCompletionIntegers L) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
      have hsum := Ideal.add_mem (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) h2 h3
      rwa [sub_add_sub_cancel] at hsum
    have hfin : Valued.v (σ ((σ ^ m) (x : q.adicCompletion L)) -
        ((x : q.adicCompletion L) ^ (residueCard K Q ^ m)) ^ (residueCard K Q)) < 1 := by
      simpa [y] using (hmem_iff _).mp h4
    rw [show ((σ ^ (m + 1)) (x : q.adicCompletion L) -
        (x : q.adicCompletion L) ^ (residueCard K Q ^ (m + 1)))
        = (σ ((σ ^ m) (x : q.adicCompletion L)) -
        ((x : q.adicCompletion L) ^ (residueCard K Q ^ m)) ^ (residueCard K Q)) by
          rw [pow_succ', AlgEquiv.mul_apply, pow_succ, pow_mul]]
    exact hfin

end NK.LocalReciprocity
