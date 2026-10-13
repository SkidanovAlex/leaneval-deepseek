import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.N3_ker_aeval
import Submission.Work.DSM2p.N5e_descent
import Submission.Work.DSM2p.N5_helpers

/-!
# Helpers for the descent step of node `N5`

* `pow_sub_pow_mem_of_sub_mem`, `mem_span_singleton_pow`, `sup_span_eq_of_sub_mem` — elementary
  ideal arithmetic;
* `varpi_pow_root`, `varpi_zero_isSMulRegular` — `ϖ_j ^ (p ^ j) = ϖ_0` and `ϖ_0` is a
  nonzerodivisor in a perfectoid ring;
* `poly_mem_of_ker` — the `N3` step: a divisibility statement in `D[1/π]` whose kernel is
  described by `N3` yields a polynomial ideal membership over `D`.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-! ## Ring-theoretic helpers for the descent step -/

/-- If `a - b ∈ J` then `a ^ n - b ^ n ∈ J`. -/
lemma pow_sub_pow_mem_of_sub_mem {R : Type*} [CommRing R] {J : Ideal R} {a b : R}
    (h : a - b ∈ J) (n : ℕ) : a ^ n - b ^ n ∈ J := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow a b n
  rw [hc]; exact Ideal.mul_mem_right _ _ h

/-- `x ^ n ∈ (x)` for `n ≥ 1`. -/
lemma mem_span_singleton_pow {R : Type*} [CommRing R] (x : R) {n : ℕ} (hn : 1 ≤ n) :
    x ^ n ∈ Ideal.span {x} :=
  Ideal.mem_span_singleton.mpr ⟨x ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel hn]⟩

/-- Replacing a generator by a congruent one does not change the ideal `A ⊔ (w)`. -/
lemma sup_span_eq_of_sub_mem {R : Type*} [CommRing R] (A : Ideal R) {w w' : R}
    (h : w - w' ∈ A) : A ⊔ Ideal.span {w} = A ⊔ Ideal.span {w'} := by
  have h1 : w ∈ A ⊔ Ideal.span {w'} := by
    have h2 : w = (w - w') + w' := by ring
    rw [h2]
    exact Ideal.add_mem _ (Ideal.mem_sup_left h)
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton w')))
  have h3 : w' ∈ A ⊔ Ideal.span {w} := by
    have h4 : w' = w - (w - w') := by ring
    rw [h4]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton w)))
      (Ideal.mem_sup_left h)
  refine le_antisymm ?_ ?_
  · exact sup_le le_sup_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h1))
  · exact sup_le le_sup_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h3))

/-- `ϖ_j ^ (p ^ j) = ϖ_0` for any perfectoid ring. -/
lemma varpi_pow_root {R : Type*} [CommRing R] (p : ℕ) (Q : DSMap.PerfectoidData p R) (j : ℕ) :
    (Q.ϖ j) ^ (p ^ j) = Q.ϖ 0 := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.pow_succ', pow_mul, Q.root j, ih]

/-- `ϖ_0` is a nonzerodivisor of a perfectoid ring (`ϖ_0 ^ p = p · unit`). -/
lemma varpi_zero_isSMulRegular {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    (Q : DSMap.PerfectoidData p R) : IsSMulRegular R (Q.ϖ 0) := by
  obtain ⟨v, hv⟩ := Q.unit
  have h1 : IsSMulRegular R ((Q.ϖ 0) ^ p) := by
    rw [hv]
    exact Q.torsionFree.mul (IsUnit.isSMulRegular R (Units.isUnit v))
  exact IsSMulRegular.of_pow_isSMulRegular (Fact.out : p.Prime).pos h1

/-- **The `N3` step.**  Let `π ∈ D`, `L = D[1/π]`, `x ∈ L`, `g ∈ D[X]` with
`ker (aeval x) = (g)`, let `v ∈ D[x]` and `delta ∈ D` with
`(delta / π^e) ^ N = π · v`.  Then `C (delta ^ N) - C (π ^ (e * N + 1)) * h ∈ (g)` for some `h`.

Indeed, multiplying the relation by `π ^ (e * N)` gives
`delta ^ N = π ^ (e * N + 1) · v = π ^ (e * N + 1) · h(x)`, so the polynomial
`C (delta ^ N) - C (π ^ (e * N + 1)) * h` is killed by `aeval x` and hence lies in `(g)`. -/
theorem poly_mem_of_ker {D : Type*} [CommRing D] (π : D) {L : Type*} [CommRing L] [Algebra D L]
    [IsLocalization.Away π L] (e N : ℕ) (delta : D) (x : L) (g : Polynomial D)
    (hker : RingHom.ker (Polynomial.aeval x).toRingHom = Ideal.span {g})
    {v : L} (hv : v ∈ Algebra.adjoin D {x})
    (heq : (algebraMap D L delta * IsLocalization.Away.invSelf π ^ e) ^ N = algebraMap D L π * v) :
    ∃ hD : Polynomial D, Polynomial.C (delta ^ N) - Polynomial.C (π ^ (e * N + 1)) * hD ∈
      Ideal.span {g} := by
  -- `v = hD(x)`
  have hv' : v ∈ (Polynomial.aeval (R := D) x).range := by
    rw [Algebra.adjoin_singleton_eq_range_aeval D x] at hv
    exact hv
  rw [AlgHom.mem_range] at hv'
  obtain ⟨hD, hhD⟩ := hv'
  refine ⟨hD, ?_⟩
  -- the difference is killed by `aeval x`
  have hzero : Polynomial.aeval (R := D) x
      (Polynomial.C (delta ^ N) - Polynomial.C (π ^ (e * N + 1)) * hD) = 0 := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_C, hhD]
    -- `algebraMap (delta ^ N) = algebraMap (π ^ (e*N+1)) * v`
    have h1 : (algebraMap D L delta * IsLocalization.Away.invSelf π ^ e) ^ N
        = algebraMap D L (delta ^ N) * IsLocalization.Away.invSelf π ^ (e * N) := by
      rw [mul_pow, map_pow, ← pow_mul]
    have h2 : algebraMap D L (delta ^ N) * IsLocalization.Away.invSelf π ^ (e * N)
        = algebraMap D L π * v := by
      rw [← h1]; exact heq
    have h3 : (algebraMap D L (delta ^ N) * IsLocalization.Away.invSelf π ^ (e * N))
        * (algebraMap D L π) ^ (e * N) = algebraMap D L (delta ^ N) := by
      rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf π ^ (e * N)), ← mul_pow,
        IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    have h4 : (algebraMap D L π * v) * (algebraMap D L π) ^ (e * N)
        = algebraMap D L (π ^ (e * N + 1)) * v := by
      rw [pow_succ', map_mul, map_pow]; ring
    have := congrArg (fun z : L => z * (algebraMap D L π) ^ (e * N)) h2
    rw [h3, h4] at this
    rw [this, sub_self]
  rw [← hker, RingHom.mem_ker]
  exact hzero


end Work.DSM2p
