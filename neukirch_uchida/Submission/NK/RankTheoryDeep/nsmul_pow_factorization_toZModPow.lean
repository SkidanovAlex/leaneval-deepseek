import Mathlib
import Submission.NK.Reconstruct.card_dvd_of_isPGroup_quotient_adicUnits

open scoped nonZeroDivisors
set_option linter.style.haveILetI false

namespace NK.RankTheoryDeep

/-- **The `ℓ`-part of the residue field units kills every `ℓ`-adic character of the local units.**

Let `K` be a number field, `Q` a finite place of `K` whose residue field `𝓞_K ⧸ Q` has
characteristic `p`, and let `ℓ ≠ p` be a prime, `m : ℕ` and `f : 𝒪_Qˣ → ℤ/ℓ^m` an arbitrary
homomorphism (`𝒪_Qˣ = (Q.adicCompletionIntegers K)ˣ` the local units, viewed as an abstract
group via `Additive`).  Then `ℓ ^ v_ℓ(#(𝓞_K ⧸ Q) - 1)` annihilates every value of `f`.

Proof.  `f` factors through its image `P`, a finite subgroup of `ℤ/ℓ^m`, hence a finite
`ℓ`-group.  Every finite `ℓ`-group quotient of `𝒪_Qˣ` has order dividing `q - 1`, where
`q = #(𝓞_K ⧸ Q)`: this is
`NK.Reconstruct.card_dvd_of_isPGroup_quotient_adicUnits` (proved via Hensel: `1 + 𝔪` is
`ℓ`-divisible when `p ≠ ℓ`).  As `P` is an `ℓ`-group, `#P = ℓ^j` divides both `ℓ^m` and `q - 1`,
so `j ≤ v_ℓ(q - 1)` and `ℓ^j ∣ ℓ^v` with `v = v_ℓ(q - 1)`.  Since `ℓ^j` annihilates `P` (Lagrange,
`pow_card_eq_one'`), so does `ℓ^v`, and `f b ∈ P`.  The residue field is nontrivial
(`CharP _ p` with `p` prime gives `1 ≠ 0`), and `ℤ`-finite, so `q ≥ 2` and `q - 1 ≠ 0`, which is
what makes `v_ℓ(q - 1)` meaningful. -/
theorem nsmul_pow_factorization_toZModPow {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
    (hres : CharP (NumberField.RingOfIntegers K ⧸ Q.asIdeal) p) (hne : p ≠ ℓ)
    (m : ℕ) (f : Additive (Q.adicCompletionIntegers K)ˣ →+ ZMod (ℓ ^ m))
    (b : Additive (Q.adicCompletionIntegers K)ˣ) :
    (ℓ ^ (Nat.card (NumberField.RingOfIntegers K ⧸ Q.asIdeal) - 1).factorization ℓ) • f b = 0 := by
  classical
  set N := Nat.card (NumberField.RingOfIntegers K ⧸ Q.asIdeal) with hN
  -- The residue field is finite, hence has positive cardinality.
  have hNpos : 0 < N := by
    have hmem : Q.asIdeal ∈ nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr Q.ne_bot
    have h : 0 < Ideal.absNorm Q.asIdeal :=
      Ideal.absNorm_pos_of_nonZeroDivisors
        (⟨Q.asIdeal, hmem⟩ : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)))
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hN] at h
    exact h
  -- It has characteristic `p`, a prime, so it is nontrivial.
  have hNne1 : N ≠ 1 := by
    intro h1
    have hsub : Subsingleton (NumberField.RingOfIntegers K ⧸ Q.asIdeal) :=
      (Nat.card_eq_one_iff_unique.mp (by rw [← hN]; exact h1)).1
    have hzero : ((1 : ℕ) : NumberField.RingOfIntegers K ⧸ Q.asIdeal) = 0 := by
      rw [Nat.cast_one]; exact Subsingleton.elim _ _
    have : CharP (NumberField.RingOfIntegers K ⧸ Q.asIdeal) p := hres
    exact (Fact.out : p.Prime).not_dvd_one ((CharP.cast_eq_zero_iff _ p 1).mp hzero)
  have hN2 : 2 ≤ N := (Nat.two_le_iff N).mpr ⟨hNpos.ne', hNne1⟩
  have hn : N - 1 ≠ 0 := by omega
  -- `f` as a multiplicative homomorphism, so that the group-theoretic criterion applies.
  let g : (Q.adicCompletionIntegers K)ˣ →* Multiplicative (ZMod (ℓ ^ m)) :=
    { toFun := fun a => Multiplicative.ofAdd (f (Additive.ofMul a))
      map_one' := by simp
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (f (Additive.ofMul (a * b))) =
          Multiplicative.ofAdd (f (Additive.ofMul a)) * Multiplicative.ofAdd (f (Additive.ofMul b))
        rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl, map_add]
        rfl }
  have hPZ : IsPGroup ℓ (Multiplicative (ZMod (ℓ ^ m))) := by
    intro x
    refine ⟨m, ?_⟩
    have hx : x = Multiplicative.ofAdd x.toAdd := rfl
    rw [hx, ← ofAdd_nsmul]
    have hzero : (ℓ ^ m) • x.toAdd = 0 := by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hzero]
    rfl
  haveI : Finite g.range := inferInstance
  have hP : IsPGroup ℓ g.range := hPZ.to_subgroup g.range
  -- The order of the image divides `#(𝓞_K ⧸ Q) - 1`.
  have hdiv : Nat.card g.range ∣ N - 1 := by
    have h := NK.Reconstruct.card_dvd_of_isPGroup_quotient_adicUnits Q hres hne hP
      g.rangeRestrict (MonoidHom.rangeRestrict_surjective g)
    rwa [← hN] at h
  obtain ⟨j, hj⟩ := hP.exists_card_eq
  have hjdvd : ℓ ^ j ∣ N - 1 := by rw [← hj]; exact hdiv
  have hpow_ne : ℓ ^ j ≠ 0 := pow_ne_zero j (Fact.out : ℓ.Prime).ne_zero
  -- So `j ≤ v_ℓ(N - 1)`, the exponent in the statement.
  have hjle : j ≤ (N - 1).factorization ℓ := by
    have hfl : (ℓ ^ j).factorization ≤ (N - 1).factorization :=
      (Nat.factorization_le_iff_dvd hpow_ne hn).mpr hjdvd
    have h2 := (Finsupp.le_def.mp hfl) ℓ
    rwa [Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self (Fact.out : ℓ.Prime),
      smul_eq_mul, mul_one] at h2
  -- `ℓ^j` annihilates the image, hence `f b`.
  have hkill : ℓ ^ j • f b = 0 := by
    have hgb : g (Additive.ofMul.symm b) = Multiplicative.ofAdd (f b) := by
      simp [g]
    have hmem : g (Additive.ofMul.symm b) ∈ g.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h1 : (⟨g (Additive.ofMul.symm b), hmem⟩ : g.range) ^ (ℓ ^ j) = 1 := by
      have h := pow_card_eq_one' (x := (⟨g (Additive.ofMul.symm b), hmem⟩ : g.range))
      rwa [hj] at h
    have h1' : (Multiplicative.ofAdd (f b)) ^ (ℓ ^ j) = 1 := by
      have h := congrArg (Subtype.val) h1
      rw [Subgroup.coe_pow, Subtype.coe_mk, hgb, Subgroup.coe_one] at h
      exact h
    have h2 : Multiplicative.ofAdd (ℓ ^ j • f b) = Multiplicative.ofAdd 0 := by
      rw [ofAdd_nsmul, h1']
      rfl
    exact (Equiv.injective Multiplicative.ofAdd) h2
  obtain ⟨c, hc⟩ := pow_dvd_pow ℓ hjle
  calc (ℓ ^ ((N - 1).factorization ℓ)) • f b = (ℓ ^ j * c) • f b := by rw [hc]
    _ = c • (ℓ ^ j • f b) := mul_nsmul _ _ _
    _ = c • 0 := by rw [hkill]
    _ = 0 := nsmul_zero c

end NK.RankTheoryDeep
