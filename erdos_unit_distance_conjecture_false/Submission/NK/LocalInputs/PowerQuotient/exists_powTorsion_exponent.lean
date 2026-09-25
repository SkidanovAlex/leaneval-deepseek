import Mathlib
import Submission.Commons.NumberTheory.NumberField.charZero_adicCompletion
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists

open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalInputs.PowerQuotient

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {K : Type*} [Field K] [NumberField K]
variable {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}

/-- An element `< 1` of the discrete value group `ℤᵐ⁰` is `≤ exp (-1)`. -/
lemma lt_one_le_exp_neg_one {y : WithZero (Multiplicative ℤ)} (hy : y < 1) :
    y ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hy0 : y = 0
  · rw [hy0]; exact zero_le
  · have h1 : WithZero.exp (WithZero.log y) < WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_log hy0, WithZero.exp_zero]; exact hy
    have hlog : WithZero.log y < 0 := WithZero.exp_lt_exp.mp h1
    calc y = WithZero.exp (WithZero.log y) := (WithZero.exp_log hy0).symm
      _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)

/-- If `x ^ n = 1` with `n ≠ 0`, then `x` lies in the valuation ring of the completion. -/
lemma val_le_one_of_pow_eq_one {x : 𝔭.adicCompletion K} {n : ℕ} (hn : n ≠ 0)
    (hx : x ^ n = 1) : Valued.v (R := 𝔭.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ)) x ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hpow : 1 < (Valued.v (R := 𝔭.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ)) x) ^ n := one_lt_pow' h hn
  rw [← Valuation.map_pow, hx, Valuation.map_one] at hpow
  exact lt_irrefl 1 hpow

/-- **A `p`-power root of unity in the `𝔭`-adic completion is congruent to `1`
modulo the maximal ideal.**  Indeed, its reduction to the residue field (of characteristic `p`)
is a `p ^ m`-th root of unity, hence equals `1` because `X ^ (p^m) - 1 = (X - 1) ^ (p^m)`
in characteristic `p`. -/
lemma val_one_sub_lt_one_of_pow_eq_one {p : ℕ} (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    {x : 𝔭.adicCompletion K} (hx : ∃ m : ℕ, x ^ p ^ m = 1) :
    Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (1 - x) < 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hx
  have hxle : Valued.v (R := 𝔭.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ)) x ≤ 1 :=
    val_le_one_of_pow_eq_one (pow_ne_zero m hp.ne_zero) hm
  have hxmem : x ∈ 𝔭.adicCompletionIntegers K :=
    (mem_adicCompletionIntegers (R := NumberField.RingOfIntegers K) (K := K)
      (v := 𝔭)).mpr hxle
  have hzpow : (⟨x, hxmem⟩ : 𝔭.adicCompletionIntegers K) ^ p ^ m = 1 := by
    apply Subtype.ext
    push_cast
    exact hm
  have hresz : IsLocalRing.residue (𝔭.adicCompletionIntegers K)
      (⟨x, hxmem⟩ : 𝔭.adicCompletionIntegers K) = 1 := by
    have h1 : (IsLocalRing.residue (𝔭.adicCompletionIntegers K)
        (⟨x, hxmem⟩ : 𝔭.adicCompletionIntegers K)) ^ p ^ m = 1 := by
      rw [← map_pow, hzpow, map_one]
    have h2 : (IsLocalRing.residue (𝔭.adicCompletionIntegers K)
        (⟨x, hxmem⟩ : 𝔭.adicCompletionIntegers K) - 1) ^ p ^ m = 0 := by
      rw [sub_pow_char_pow, h1, one_pow, sub_self]
    have h3 : IsLocalRing.residue (𝔭.adicCompletionIntegers K)
        (⟨x, hxmem⟩ : 𝔭.adicCompletionIntegers K) - 1 = 0 :=
      (pow_eq_zero_iff (pow_ne_zero m hp.ne_zero)).mp h2
    exact sub_eq_zero.mp h3
  have hmem : (⟨x, hxmem⟩ : 𝔭.adicCompletionIntegers K) - 1 ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, hresz, sub_self]
  have hlt : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((⟨x, hxmem⟩ : 𝔭.adicCompletionIntegers K) - 1 : 𝔭.adicCompletionIntegers K) :
        𝔭.adicCompletion K) < 1 :=
    (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
      𝔭 _).mp hmem
  have hcast : (((⟨x, hxmem⟩ : 𝔭.adicCompletionIntegers K) - 1 :
      𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) = x - 1 := by
    push_cast
    rfl
  rw [hcast] at hlt
  have : (1 : 𝔭.adicCompletion K) - x = -(x - 1) := by ring
  rw [this, Valuation.map_neg]
  exact hlt

/-- **The bound on the order of a `p`-power root of unity.**

If `e` is the (normalised) valuation of `p` in the completion, `v p = exp (-e)`, and
`x` is a primitive `p ^ j`-th root of unity (`j ≥ 1`), then `j ≤ e`.

Indeed `Φ_{p^j}(X) = ∏_{μ}(X - μ)` over the primitive `p^j`-th roots of unity evaluates at `X = 1`
to `Φ_{p^j}(1) = p`, so taking valuations gives
`exp (-e) = ∏_μ v (1 - μ) ≤ exp (-1) ^ φ(p^j) = exp (-φ(p^j))`,
whence `φ(p^j) ≤ e`; and `j ≤ φ(p^j) = (p-1) p^{j-1}`. -/
lemma le_exp_of_isPrimitiveRoot {p e : ℕ} (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (he : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (p : 𝔭.adicCompletion K) = WithZero.exp (-(e : ℤ)))
    {j : ℕ} (hj : 1 ≤ j) {x : 𝔭.adicCompletion K} (hx : IsPrimitiveRoot x (p ^ j)) :
    j ≤ e := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpj_pos : 0 < p ^ j := pow_pos hp.pos j
  -- The cyclotomic product identity, evaluated at `X = 1`.
  have hprod : ∏ μ ∈ primitiveRoots (p ^ j) (𝔭.adicCompletion K), (1 - μ) =
      (p : 𝔭.adicCompletion K) := by
    have hcyc := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hx
    have h1 : Polynomial.eval (1 : 𝔭.adicCompletion K)
        (Polynomial.cyclotomic (p ^ j) (𝔭.adicCompletion K)) = (p : 𝔭.adicCompletion K) := by
      rw [show p ^ j = p ^ (j - 1 + 1) from by rw [Nat.sub_add_cancel hj]]
      exact Polynomial.eval_one_cyclotomic_prime_pow (R := 𝔭.adicCompletion K) (p := p) (j - 1)
    rw [hcyc] at h1
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      at h1
    exact h1
  -- Each factor has valuation at most `exp (-1)`.
  have hfactor : ∀ μ ∈ primitiveRoots (p ^ j) (𝔭.adicCompletion K),
      Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (1 - μ) ≤
        WithZero.exp (-1 : ℤ) := by
    intro μ hμ
    refine lt_one_le_exp_neg_one ?_
    refine val_one_sub_lt_one_of_pow_eq_one hp hres ⟨j, ?_⟩
    exact ((mem_primitiveRoots (k := p ^ j) hpj_pos).mp hμ).pow_eq_one
  -- The valuation of the product.
  have hval_prod : ∏ μ ∈ primitiveRoots (p ^ j) (𝔭.adicCompletion K),
      Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (1 - μ) =
        WithZero.exp (-(e : ℤ)) := by
    rw [← map_prod (Valued.v (R := 𝔭.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ))) (fun μ => 1 - μ)
      (primitiveRoots (p ^ j) (𝔭.adicCompletion K)), hprod, he]
  have hle : ∏ μ ∈ primitiveRoots (p ^ j) (𝔭.adicCompletion K),
      Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (1 - μ) ≤
      ∏ _μ ∈ primitiveRoots (p ^ j) (𝔭.adicCompletion K), WithZero.exp (-1 : ℤ) := by
    refine Finset.prod_le_prod₀ (fun μ _ => zero_le) (fun μ hμ => hfactor μ hμ)
  have hconst : ∏ _μ ∈ primitiveRoots (p ^ j) (𝔭.adicCompletion K),
      WithZero.exp (-1 : ℤ) =
      WithZero.exp (-((primitiveRoots (p ^ j) (𝔭.adicCompletion K)).card : ℤ)) := by
    rw [Finset.prod_const, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hcard_le : (primitiveRoots (p ^ j) (𝔭.adicCompletion K)).card ≤ e := by
    have hkey : WithZero.exp (-(e : ℤ)) ≤
        WithZero.exp (-((primitiveRoots (p ^ j) (𝔭.adicCompletion K)).card : ℤ)) := by
      rw [← hval_prod, ← hconst]
      exact hle
    have := WithZero.exp_le_exp.mp hkey
    omega
  have hcard : (primitiveRoots (p ^ j) (𝔭.adicCompletion K)).card = (p ^ j).totient :=
    IsPrimitiveRoot.card_primitiveRoots hx
  have htot : (p ^ j).totient = (p - 1) * p ^ (j - 1) := by
    rw [show p ^ j = p ^ (j - 1 + 1) from by rw [Nat.sub_add_cancel hj], Nat.mul_comm]
    exact Nat.totient_prime_pow_succ hp (j - 1)
  have hjb : j ≤ (p - 1) * p ^ (j - 1) := by
    have h1 : j ≤ 2 ^ (j - 1) := by
      have h2 := Nat.lt_two_pow_self (n := j - 1)
      omega
    have h2 : 2 ^ (j - 1) ≤ p ^ (j - 1) := Nat.pow_le_pow_left hp.two_le (j - 1)
    have h3 : p ^ (j - 1) ≤ (p - 1) * p ^ (j - 1) := by
      have hle : 1 ≤ p - 1 := by have := hp.two_le; omega
      calc p ^ (j - 1) = 1 * p ^ (j - 1) := (one_mul _).symm
        _ ≤ (p - 1) * p ^ (j - 1) := Nat.mul_le_mul_right _ hle
    linarith
  calc j ≤ (p - 1) * p ^ (j - 1) := hjb
    _ = (p ^ j).totient := htot.symm
    _ = (primitiveRoots (p ^ j) (𝔭.adicCompletion K)).card := hcard.symm
    _ ≤ e := hcard_le

theorem exists_powTorsion_exponent {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    ∃ N : ℕ, ∀ ζ : (𝔭.adicCompletion K)ˣ, (∃ m : ℕ, ζ ^ p ^ m = 1) → ζ ^ p ^ N = 1 := by
  classical
  haveI : CharZero (𝔭.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
  -- `p` is not a unit of the ring of integers of the completion
  have hres0 : IsLocalRing.residue (𝔭.adicCompletionIntegers K)
      (p : 𝔭.adicCompletionIntegers K) = 0 := by
    rw [map_natCast, CharP.cast_eq_zero]
  have hpmem : (p : 𝔭.adicCompletionIntegers K) ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) :=
    (IsLocalRing.residue_eq_zero_iff _).mp hres0
  have hvplt : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (p : 𝔭.adicCompletion K) < 1 := by
    have h := (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
      𝔭 (p : 𝔭.adicCompletionIntegers K)).mp hpmem
    simpa using h
  have hp0 : (p : 𝔭.adicCompletion K) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact hp.ne_zero
  have hvne : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (p : 𝔭.adicCompletion K) ≠ 0 :=
    fun h => hp0 ((Valuation.zero_iff (Valued.v (R := 𝔭.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ)))).mp h)
  -- the normalised valuation of `p`, as `exp (-t)` with `t < 0`
  set t : ℤ := WithZero.log (Valued.v (R := 𝔭.adicCompletion K)
    (Γ₀ := WithZero (Multiplicative ℤ)) (p : 𝔭.adicCompletion K)) with ht
  have hvpt : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (p : 𝔭.adicCompletion K) = WithZero.exp t := (WithZero.exp_log hvne).symm
  have htneg : t < 0 := by
    have h1 : WithZero.exp t < WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_zero, ← hvpt]; exact hvplt
    exact WithZero.exp_lt_exp.mp h1
  have htoNat : ((-t).toNat : ℤ) = -t := Int.toNat_of_nonneg (by omega)
  have he : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (p : 𝔭.adicCompletion K) = WithZero.exp (-(((-t).toNat : ℕ) : ℤ)) := by
    rw [hvpt, htoNat, neg_neg]
  refine ⟨(-t).toNat, ?_⟩
  intro ζ hζ
  obtain ⟨m, hm⟩ := hζ
  have hm' : ((ζ : 𝔭.adicCompletion K) ^ p ^ m) = 1 := by
    have h := congrArg (fun u : (𝔭.adicCompletion K)ˣ => (u : 𝔭.adicCompletion K)) hm
    simpa using h
  have hdvd : orderOf ((ζ : 𝔭.adicCompletion K)) ∣ p ^ m :=
    orderOf_dvd_iff_pow_eq_one.mpr hm'
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    simp only [pow_zero] at hjeq
    have h1 : (ζ : 𝔭.adicCompletion K) = 1 := orderOf_eq_one_iff.mp hjeq
    have h1u : ζ = 1 := Units.ext h1
    rw [h1u, one_pow]
  · have hprim : IsPrimitiveRoot ((ζ : 𝔭.adicCompletion K)) (p ^ j) :=
      IsPrimitiveRoot.iff_orderOf.mpr hjeq
    have hje : j ≤ (-t).toNat := le_exp_of_isPrimitiveRoot hp hres he hjpos hprim
    have hdvd2 : p ^ j ∣ p ^ (-t).toNat := Nat.pow_dvd_pow p hje
    have hpow1 : ((ζ : 𝔭.adicCompletion K)) ^ p ^ (-t).toNat = 1 :=
      (hprim.pow_eq_one_iff_dvd (p ^ (-t).toNat)).mpr hdvd2
    exact Units.ext (by simpa using hpow1)

end

end NK.LocalInputs.PowerQuotient
