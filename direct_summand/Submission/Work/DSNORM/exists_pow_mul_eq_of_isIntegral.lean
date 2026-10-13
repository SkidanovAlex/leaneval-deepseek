import Mathlib

/-!
# Denominators of an integral element of the fraction field

Let `A` be a domain, `K = FractionRing A` its fraction field, and `a b : A` with `b ≠ 0`.
If `a / b ∈ K` is integral over `A`, then `a / b` lies in the `A`-submodule
`b ^ (-(N - 1)) • A ⊆ K` for some `N > 0`: equivalently

`∃ N > 0, ∀ n, ∃ u : A, b ^ (N - 1) * a ^ n = b ^ n * u`.

Concretely, if `p : A[X]` is a monic polynomial of degree `N` with `p (a / b) = 0`, then every
power `(a / b) ^ n` lies in the `A`-span of `1, a / b, …, (a / b) ^ (N - 1)`, and
`b ^ (N - 1) * (a / b) ^ i = b ^ (N - 1 - i) * a ^ i` for `i < N`, which gives the bound.

The auxiliary lemma `pow_natDegree_eq_neg_sum_of_aeval_eq_zero` records the recurrence
`x ^ p.natDegree = -∑_{i < p.natDegree} p.coeff i • x ^ i` coming from `p.Monic` and
`aeval x p = 0`; it is the only polynomial input to the argument.
-/

namespace Work.DSNORM

/-- If `p : R[X]` is monic and `p` vanishes at `x` (under `aeval`), then the top power `x ^ n`
(with `n = p.natDegree`) is the negative of the `R`-linear combination of the lower powers
prescribed by the lower coefficients of `p`. -/
lemma pow_natDegree_eq_neg_sum_of_aeval_eq_zero {R K : Type*} [CommRing R] [CommRing K]
    [Algebra R K] {x : K} {p : Polynomial R} (hp : p.Monic) (h : Polynomial.aeval x p = 0) :
    x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * x ^ i := by
  have h0 : Polynomial.eval₂ (algebraMap R K) x p = 0 := by
    rw [← Polynomial.aeval_def]; exact h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem exists_pow_mul_eq_of_isIntegral {A : Type*} [CommRing A] [IsDomain A] {a b : A}
    (hb : b ≠ 0)
    (hint : IsIntegral A (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b)) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, ∃ u : A, b ^ (N - 1) * a ^ n = b ^ n * u := by
  obtain ⟨p, hp, hp0⟩ := hint
  set x : FractionRing A := algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b
    with hx
  have hφb : algebraMap A (FractionRing A) b ≠ 0 := by
    intro h
    exact hb (IsFractionRing.injective A (FractionRing A) (by simpa using h))
  have hbx : algebraMap A (FractionRing A) b * x = algebraMap A (FractionRing A) a := by
    rw [hx]; exact mul_div_cancel₀ _ hφb
  have hNpos : 0 < p.natDegree := by
    by_contra h
    have h0 : p.natDegree = 0 := Nat.eq_zero_of_not_pos h
    have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    have hc : p.coeff 0 = 1 := by rw [← h0]; exact hp.coeff_natDegree
    rw [hpC, hc, Polynomial.eval₂_C, map_one] at hp0
    exact one_ne_zero hp0
  refine ⟨p.natDegree, hNpos, ?_⟩
  set N : ℕ := p.natDegree with hNdef
  have hxN : x ^ N
      = -∑ i ∈ Finset.range N, algebraMap A (FractionRing A) (p.coeff i) * x ^ i := by
    rw [hNdef]
    exact pow_natDegree_eq_neg_sum_of_aeval_eq_zero hp (by rw [Polynomial.aeval_def]; exact hp0)
  have key : ∀ k : ℕ, ∃ u : A,
      algebraMap A (FractionRing A) u = algebraMap A (FractionRing A) b ^ (N - 1) * x ^ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases lt_or_ge k N with hn | hn
      · -- low powers: `b ^ (N - 1) * x ^ k = b ^ (N - 1 - k) * a ^ k`
        refine ⟨b ^ (N - 1 - k) * a ^ k, ?_⟩
        have hpow : N - 1 - k + k = N - 1 := by omega
        have hφa : (algebraMap A (FractionRing A) a) ^ k
            = (algebraMap A (FractionRing A) b) ^ k * x ^ k := by
          rw [← hbx, mul_pow]
        simp only [map_mul, map_pow]
        rw [hφa, ← mul_assoc, ← pow_add, hpow]
      · -- reduce `x ^ k = x ^ (k - N) * x ^ N` and use the recurrence for `x ^ N`
        have hw : ∀ i : ℕ, i < N → ∃ u : A,
            algebraMap A (FractionRing A) u
              = algebraMap A (FractionRing A) b ^ (N - 1) * x ^ (k - N + i) := by
          intro i hi
          exact ih (k - N + i) (by omega)
        let g : ℕ → A := fun i => if h : i < N then (hw i h).choose else 0
        have hgmem : ∀ i ∈ Finset.range N,
            algebraMap A (FractionRing A) (g i)
              = algebraMap A (FractionRing A) b ^ (N - 1) * x ^ (k - N + i) := by
          intro i hi
          have h : i < N := Finset.mem_range.mp hi
          dsimp only [g]
          rw [dite_eq_left h]
          exact (hw i h).choose_spec
        have h1 : x ^ k
            = -∑ i ∈ Finset.range N,
                algebraMap A (FractionRing A) (p.coeff i) * x ^ (k - N + i) := by
          have hxk : x ^ (k - N) * x ^ N = x ^ k := by
            rw [← pow_add, Nat.sub_add_cancel hn]
          rw [← hxk, hxN, mul_neg, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [pow_add]; ring
        have hsum : algebraMap A (FractionRing A) b ^ (N - 1) * x ^ k
            = -∑ i ∈ Finset.range N, algebraMap A (FractionRing A) (p.coeff i)
                * (algebraMap A (FractionRing A) b ^ (N - 1) * x ^ (k - N + i)) := by
          rw [h1, mul_neg, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
        refine ⟨-∑ i ∈ Finset.range N, p.coeff i * g i, ?_⟩
        rw [hsum, map_neg, map_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_mul, hgmem i hi]
  intro n
  obtain ⟨u, hu⟩ := key n
  refine ⟨u, ?_⟩
  apply IsFractionRing.injective A (FractionRing A)
  have hφa : (algebraMap A (FractionRing A) a) ^ n
      = (algebraMap A (FractionRing A) b) ^ n * x ^ n := by
    rw [← hbx, mul_pow]
  simp only [map_mul, map_pow]
  rw [hu, hφa]
  ring

end Work.DSNORM
