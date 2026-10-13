import Mathlib
import Submission.Work.DSM2p.Basic

/-!
# `Work.DSM2p.isReduced` — perfectoid rings are reduced

This module proves that a ring `A` carrying the structure `DSMap.PerfectoidData p A`
(a `p`-torsion-free, `p`-adically complete ring with an element `ϖ` such that `ϖ ^ p = p * unit`,
and with the `p`-power map inducing a bijection `A / ϖ ≅ A / ϖ ^ p`) is reduced.

The argument (Česnavičius–Scholze, *Purity for flat cohomology*, arXiv:1912.10932,
§"Perfectoid rings", and BMS, *Integral p-adic Hodge theory*, Lemma 3.10) is:

* `ϖ := P.ϖ 0` is a nonzerodivisor, being a `p`-th root of the unit multiple `p * v` of `p`;
* if `z ^ 2 = 0` then `z ^ p = 0 ∈ (p)`, so `P.frobInj` gives `z ∈ (ϖ)`.  Iterating
  (using that `ϖ` is a nonzerodivisor) yields `z ∈ (ϖ) ^ n` for all `n`, hence
  `z ∈ (p) ^ n` for all `n` because `ϖ ^ p = p * v`.  The `p`-adic completeness
  (`IsHausdorff`) then forces `z = 0`;
* an arbitrary nilpotent `x` with `x ^ N = 0` is reduced to a square-zero element by
  `(x ^ (N - 1)) ^ 2 = x ^ N * x ^ (N - 2) = 0`.

The cases `p = 0` (`ϖ ^ 0 = p * v` gives `1 = 0`) and `p = 1` (`A` is `⊤`-adically
complete, hence trivial) are degenerate and handled directly.  Note that `P.frobSurj`
is not needed.
-/

namespace Work.DSM2p

theorem isReduced {p : ℕ} {A : Type*} [CommRing A] (P : DSMap.PerfectoidData p A) :
    IsReduced A := by
  by_cases hp0 : p = 0
  · -- `p = 0`: the unit condition reads `1 = 0`, so `A` is the zero ring.
    subst hp0
    obtain ⟨v, hv⟩ := P.unit
    have h1 : (1 : A) = 0 := by simpa using hv
    exact ⟨fun x _ => (subsingleton_of_zero_eq_one h1.symm).allEq x 0⟩
  by_cases hp1 : p = 1
  · -- `p = 1`: `A` is `⊤`-adically complete, hence trivial.
    subst hp1
    have hcomp : IsHausdorff (⊤ : Ideal A) A := by
      rw [← Ideal.span_singleton_one]
      simpa using P.complete.toIsHausdorff
    exact ⟨fun x _ => IsHausdorff.haus hcomp x (fun m => by rw [Ideal.top_pow]; simp)⟩
  · -- `2 ≤ p`: the main argument.
    have hp2 : 2 ≤ p := by omega
    have hp0' : 0 < p := by omega
    obtain ⟨v, hv⟩ := P.unit
    -- `ϖ := P.ϖ 0` is a nonzerodivisor.
    have hϖ : IsSMulRegular A (P.ϖ 0) := by
      have h1 : IsSMulRegular A (↑p * (v : A)) :=
        IsSMulRegular.mul P.torsionFree (Units.isSMulRegular A v)
      rw [← hv] at h1
      exact (IsSMulRegular.pow_iff hp0').mp h1
    -- consequently every power of `ϖ` is a nonzerodivisor, in multiplication form.
    have hnext : ∀ (m : ℕ) {w : A}, P.ϖ 0 ^ m * w = 0 → w = 0 := by
      intro m w hw
      exact (hϖ.pow m) (show (P.ϖ 0 ^ m) • w = (P.ϖ 0 ^ m) • (0 : A) by
        rw [smul_eq_mul, smul_eq_mul, hw, mul_zero])
    -- a square-zero element lies in `(ϖ)`.
    have base : ∀ z : A, z ^ 2 = 0 → z ∈ Ideal.span {P.ϖ 0} := by
      intro z hz
      apply P.frobInj
      have hz0 : z ^ p = 0 := by
        rw [show p = 2 + (p - 2) from by omega, pow_add, hz, zero_mul]
      rw [hz0]
      exact Ideal.zero_mem _
    -- the square-zero lemma.
    have key : ∀ x : A, x ^ 2 = 0 → x = 0 := by
      intro x hx
      -- `x ∈ (ϖ) ^ k` for every `k`.
      have hmem : ∀ k, x ∈ (Ideal.span {P.ϖ 0}) ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Ideal.span_singleton_pow] at ih ⊢
          obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp ih
          have hy2 : y ^ 2 = 0 := by
            have h0 : P.ϖ 0 ^ (k * 2) * y ^ 2 = 0 := by
              have hh : (P.ϖ 0 ^ k * y) ^ 2 = 0 := by rw [← hy]; exact hx
              rwa [mul_pow, ← pow_mul] at hh
            exact hnext (k * 2) h0
          obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (base y hy2)
          rw [Ideal.mem_span_singleton]
          exact ⟨z, by rw [hy, hz]; ring⟩
      -- hence `x ∈ (p) ^ N` for every `N` (using `ϖ ^ p = p * v`).
      have hmem2 : ∀ N, x ∈ (Ideal.span {(p : A)}) ^ N := by
        intro N
        have hid : (Ideal.span {P.ϖ 0}) ^ (p * N) = (Ideal.span {(p : A)}) ^ N := by
          rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
          rw [show P.ϖ 0 ^ (p * N) = (p : A) ^ N * (↑v : A) ^ N from by
            rw [pow_mul, hv, mul_pow]]
          exact Ideal.span_singleton_mul_right_unit (v.isUnit.pow N) _
        rw [← hid]
        exact hmem (p * N)
      -- `p`-adic separation finishes.
      exact IsHausdorff.haus P.complete.toIsHausdorff x (fun N => by
        rw [SModEq.sub_mem]
        rw [show (Ideal.span {(p : A)} ^ N • (⊤ : Submodule A A))
              = ((Ideal.span {(p : A)}) ^ N : Ideal A) from by
          rw [Ideal.smul_eq_mul]; exact Ideal.mul_top _]
        simpa using hmem2 N)
    -- an arbitrary nilpotent is a square-zero element (or `0`).
    refine ⟨fun x hx => ?_⟩
    obtain ⟨N, hN⟩ := hx
    have keyN : ∀ N (x : A), x ^ N = 0 → x = 0 := by
      intro N
      induction N using Nat.strong_induction_on with
      | _ N ih =>
        intro x hx
        rcases N with _ | _ | m
        · have h1 : (1 : A) = 0 := by simpa using hx
          exact (subsingleton_of_zero_eq_one h1.symm).allEq x 0
        · simpa using hx
        · have h2 : (x ^ (m + 1)) ^ 2 = 0 := by
            rw [← pow_mul]
            rw [show (m + 1) * 2 = (m + 1 + 1) + m from by ring, pow_add, hx, zero_mul]
          have h3 : x ^ (m + 1) = 0 := key (x ^ (m + 1)) h2
          exact ih (m + 1) (by omega) x h3
    exact keyN N x hN

end Work.DSM2p
