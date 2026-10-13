import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.N5d_frobInj_scaled
import Submission.Work.DSM2p.rootClosure_isSMulRegular
import Submission.Work.DSM2p.exists_sub_pow_eq_sub_pow_add_prime_mul

/-!
# Auxiliary lemmas for node `N5` of the M2p design

These are the elementary ingredients of `Work.DSM2p.N5_AAL_Lam`:

* iterating a system of `p`-power roots modulo an ideal
  (`pow_pow_sub_mem_of_root_congr`);
* the `sub`-form of the Frobenius congruence modulo `p`, iterated
  (`sub_pow_pow_sub_mem_span_p`);
* regularity of the pseudo-uniformizers `ϖ_k` in `Λ = A[T^{1/p^∞}]`
  (`Lam1_varpi_regular`), together with `ϖ_j ^ (p ^ j) = ϖ_0` (`Lam1_varpi_pow`);
* iterated Frobenius injectivity along the root tower (`varpi_iterate_mem`, `N5d`);
* the conversion of a polynomial divisibility statement into the target
  divisibility statement `δ ^ N = ϖ_0 · v` (`adjoin_mem_of_span_mem`).

They are placed in their own module so that the node lemmas `N5_AAL_Lam_a`
(range memberships of the lifted `q_j`) and `N5_AAL_Lam_b` (monic approximation of `q_j`)
can be stated and proved on top of them.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-! ## Elementary helpers -/

/-- If `x ^ n` is a nonzerodivisor of a commutative ring then so is `x` (`n > 0`). -/
lemma IsSMulRegular.of_pow_isSMulRegular {R : Type*} [CommRing R] {x : R} {n : ℕ} (hn : 0 < n)
    (h : IsSMulRegular R (x ^ n)) : IsSMulRegular R x := by
  intro a b hab
  have hab' : x * a = x * b := by simpa [smul_eq_mul] using hab
  have key : x ^ n * a = x ^ n * b := by
    have h1 : x ^ n * a = x ^ (n - 1) * (x * a) := by
      rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
    have h2 : x ^ n * b = x ^ (n - 1) * (x * b) := by
      rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
    rw [h1, h2, hab']
  exact h (by simpa [smul_eq_mul] using key)

/-- If `x ^ n` is a unit then so is `x` (`n > 0`). -/
lemma isUnit_of_isUnit_pow {R : Type*} [CommRing R] {x : R} {n : ℕ} (hn : 0 < n)
    (h : IsUnit (x ^ n)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h
  refine IsUnit.of_mul_eq_one (x ^ (n - 1) * ↑u⁻¹) ?_
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn, ← hu, Units.mul_inv]

/-- `(x - y) ^ p ^ j ≡ x ^ (p ^ j) - y ^ (p ^ j)` modulo `p`. -/
lemma sub_pow_pow_sub_mem_span_p {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (j : ℕ)
    (x y : R) :
    (x - y) ^ (p ^ j) - (x ^ (p ^ j) - y ^ (p ^ j)) ∈ Ideal.span {(p : R)} := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ih
    have hc' : (x - y) ^ (p ^ j) = (x ^ (p ^ j) - y ^ (p ^ j)) + (p : R) * c := by
      linear_combination hc
    obtain ⟨z, hz⟩ : ∃ z : R, ((p : R) * c) ^ p = (p : R) * z :=
      ⟨(p : R) ^ (p - 1) * c ^ p, by
        have h1 : (p : R) ^ p = (p : R) ^ (p - 1) * (p : R) := by
          rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
        rw [mul_pow, h1]; ring⟩
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (x ^ (p ^ j) - y ^ (p ^ j)) ((p : R) * c)
    obtain ⟨t, ht⟩ := exists_sub_pow_eq_sub_pow_add_prime_mul hp (x ^ (p ^ j)) (y ^ (p ^ j))
    refine Ideal.mem_span_singleton.mpr
      ⟨t + z + (x ^ (p ^ j) - y ^ (p ^ j)) * ((p : R) * c) * r, ?_⟩
    have hmain : (x - y) ^ (p ^ (j + 1))
        = (x ^ (p ^ j) - y ^ (p ^ j)) ^ p + (p : R) * z
          + (p : R) * ((x ^ (p ^ j) - y ^ (p ^ j)) * ((p : R) * c) * r) := by
      rw [Nat.pow_succ, pow_mul, hc', hr, hz]
      ring
    have hA : (x ^ (p ^ j)) ^ p = x ^ (p ^ (j + 1)) := by rw [← pow_mul, Nat.pow_succ]
    have hB : (y ^ (p ^ j)) ^ p = y ^ (p ^ (j + 1)) := by rw [← pow_mul, Nat.pow_succ]
    rw [hmain, ht, hA, hB]
    ring

/-- Iterating a system of `p`-power roots: if `q (j+1) ^ p ≡ q j` modulo `J` for all `j`, then
`q j ^ (p ^ j) ≡ q 0` modulo `J`. -/
lemma pow_pow_sub_mem_of_root_congr {R : Type*} [CommRing R] (q : ℕ → R) (p : ℕ) (J : Ideal R)
    (h : ∀ j, q (j + 1) ^ p - q j ∈ J) (j : ℕ) : q j ^ (p ^ j) - q 0 ∈ J := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep : (q (j + 1) ^ p) ^ (p ^ j) - q j ^ (p ^ j) ∈ J := by
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (q (j + 1) ^ p) (q j) (p ^ j)
      rw [hc]; exact Ideal.mul_mem_right _ _ (h j)
    have heq : q (j + 1) ^ (p ^ (j + 1)) = (q (j + 1) ^ p) ^ (p ^ j) := by
      rw [Nat.pow_succ', pow_mul]
    rw [heq]
    have hsum : (q (j + 1) ^ p) ^ (p ^ j) - q 0
        = ((q (j + 1) ^ p) ^ (p ^ j) - q j ^ (p ^ j)) + (q j ^ (p ^ j) - q 0) := by ring
    rw [hsum]
    exact Ideal.add_mem _ hstep ih

/-! ## Regularity of the pseudo-uniformizers in `Λ = A[T^{1/p^∞}]` -/

/-- `ϖ_k = algebraMap A Λ (P.ϖ k)` is a nonzerodivisor of `Λ`: its `p ^ k`-th power is `ϖ_0`,
which is a nonzerodivisor because `ϖ_0 ^ p = p · unit` and `p` is a nonzerodivisor. -/
theorem Lam1_varpi_regular (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (k : ℕ) :
    IsSMulRegular (Lam1 A p) (algebraMap A (Lam1 A p) (P.ϖ k)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpreg : IsSMulRegular (Lam1 A p) (p : Lam1 A p) :=
    rootClosure_isSMulRegular A p PUnit.{u + 1} P.torsionFree
  have h0 : IsSMulRegular (Lam1 A p) (algebraMap A (Lam1 A p) (P.ϖ 0)) := by
    obtain ⟨v, hv⟩ := P.unit
    let vu : (Lam1 A p)ˣ := Units.map (algebraMap A (Lam1 A p)) v
    have hpow : (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ p = (p : Lam1 A p) * (vu : Lam1 A p) := by
      show algebraMap A (Lam1 A p) (P.ϖ 0) ^ p
        = (p : Lam1 A p) * algebraMap A (Lam1 A p) (v : A)
      rw [← map_pow, hv, map_mul, map_natCast]
    have h1 : IsSMulRegular (Lam1 A p) ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ p) := by
      rw [hpow]
      exact hpreg.mul (IsUnit.isSMulRegular (Lam1 A p) (Units.isUnit vu))
    exact IsSMulRegular.of_pow_isSMulRegular hp h1
  have hpoweq : (algebraMap A (Lam1 A p) (P.ϖ k)) ^ (p ^ k)
      = algebraMap A (Lam1 A p) (P.ϖ 0) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.pow_succ', pow_mul, ← map_pow, P.root k, ih]
  have h1 : IsSMulRegular (Lam1 A p) ((algebraMap A (Lam1 A p) (P.ϖ k)) ^ (p ^ k)) := by
    rw [hpoweq]; exact h0
  exact IsSMulRegular.of_pow_isSMulRegular (pow_pos hp k) h1

/-- `ϖ_j ^ (p ^ j) = ϖ_0` in `Λ` (`j`-fold iteration of the root system). -/
lemma Lam1_varpi_pow (A : Type u) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A) (j : ℕ) :
    (algebraMap A (Lam1 A p) (P.ϖ j)) ^ (p ^ j) = algebraMap A (Lam1 A p) (P.ϖ 0) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.pow_succ', pow_mul, ← map_pow, P.root j, ih]

/-! ## Iterated Frobenius injectivity (`N5d` along a root tower) -/

/-- If `y ^ (p ^ n) ∈ (ϖ_k)` then `y ∈ (ϖ_{k+n})`: iterate `N5d` `n` times. -/
theorem varpi_iterate_mem (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (y : Lam1 A p) :
    ∀ k n : ℕ, y ^ (p ^ n) ∈ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ k)} →
      y ∈ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ (k + n))} := by
  intro k n
  induction n generalizing k with
  | zero => intro h; simpa using h
  | succ n ih =>
    intro h
    have h1 : (y ^ (p ^ n)) ^ p ∈ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ k)} := by
      have heq : (y ^ (p ^ n)) ^ p = y ^ (p ^ (n + 1)) := by rw [← pow_mul, Nat.pow_succ]
      rw [heq]; exact h
    have h2 := N5d_frobInj_scaled A p P k (y ^ (p ^ n)) h1
    have h3 := ih (k := k + 1) h2
    have hidx : k + 1 + n = k + (n + 1) := by omega
    rwa [hidx] at h3

/-! ## Converting polynomial divisibility into the target divisibility -/

/-- **The elementary conversion.**  Let `π = algebraMap A Λ (P.ϖ 0)`,
`x = frac A p (P.ϖ 0) b m ∈ Λ[1/π]` (so `x = b/π^m`) and let `h ∈ Λ[X]` satisfy

`C a^N - C (π ^ (m*N+1)) * h ∈ (π^m X - b) ⊆ Λ[X]`.

Then `v := h(x)` lies in `Λ[b/π^m]` and `(a/π^m)^N = π · v` in `Λ[1/π]`.

Indeed, evaluating the displayed relation at `X = x` kills the generator `π^m X - b` and gives
`a^N = π^{mN+1} h(x)`; multiplying by `(π^{-1})^{mN}` yields the claim since
`π^{mN} (π^{-1})^{mN} = 1`. -/
theorem adjoin_mem_of_span_mem (A : Type u) [CommRing A] (p : ℕ)
    (P : DSMap.PerfectoidData p A) (a b : Lam1 A p) (m N : ℕ) (h : Polynomial (Lam1 A p))
    (hmem : Polynomial.C (a ^ N)
        - Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1)) * h ∈
      Ideal.span {Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ m) * Polynomial.X
        - Polynomial.C b}) :
    ∃ v ∈ Algebra.adjoin (Lam1 A p) {frac A p (P.ϖ 0) b m},
      frac A p (P.ϖ 0) a m ^ N = algebraMap A (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0) * v := by
  classical
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
  set u : Lam1Loc A p (P.ϖ 0) :=
    IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) (P.ϖ 0)) with hu
  set x : Lam1Loc A p (P.ϖ 0) := frac A p (P.ϖ 0) b m with hx
  set v : Lam1Loc A p (P.ϖ 0) := Polynomial.aeval x h with hv
  have hπu : (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
      (algebraMap A (Lam1 A p) (P.ϖ 0))) * u = 1 := by
    rw [hu]; exact IsLocalization.Away.mul_invSelf (algebraMap A (Lam1 A p) (P.ϖ 0))
  -- the generator `π^m X - b` dies at `X = x`
  have hηw : Polynomial.aeval x
      (Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ m) * Polynomial.X
        - Polynomial.C b) = 0 := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.aeval_C]
    have key : algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
          ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ m) * x
        - algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) b
        = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) b
          * ((algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
              (algebraMap A (Lam1 A p) (P.ϖ 0))) ^ m * u ^ m)
          - algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) b := by
      rw [hx, frac, map_pow, ← hu]; ring
    rw [key, ← mul_pow, hπu, one_pow, mul_one, sub_self]
  -- evaluate the relation at `X = x`
  have hηs : Polynomial.aeval x (Polynomial.C (a ^ N)
      - Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1)) * h) = 0 := by
    rw [← hs, Polynomial.aeval_mul, hηw, mul_zero]
  rw [Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_C] at hηs
  have hkey : algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (a ^ N)
      = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
          ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1)) * v := by
    rw [← sub_eq_zero]; exact hηs
  refine ⟨v, ?_, ?_⟩
  · rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
    exact ⟨h, hv⟩
  · have hfrac : frac A p (P.ϖ 0) a m ^ N
        = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (a ^ N) * u ^ (m * N) := by
      rw [frac, mul_pow, map_pow, ← hu, ← pow_mul]
    rw [hfrac, hkey, map_pow]
    have hpu : (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
        (algebraMap A (Lam1 A p) (P.ϖ 0))) ^ (m * N) * u ^ (m * N) = 1 := by
      rw [← mul_pow, hπu, one_pow]
    rw [IsScalarTower.algebraMap_apply A (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0)]
    calc (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
            (algebraMap A (Lam1 A p) (P.ϖ 0))) ^ (m * N + 1) * v * u ^ (m * N)
        = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (algebraMap A (Lam1 A p) (P.ϖ 0))
          * ((algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
              (algebraMap A (Lam1 A p) (P.ϖ 0))) ^ (m * N) * u ^ (m * N)) * v := by
          rw [pow_succ']; ring
      _ = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (algebraMap A (Lam1 A p) (P.ϖ 0))
            * v := by rw [hpu]; ring


end Work.DSM2p
