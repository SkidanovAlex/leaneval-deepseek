import Mathlib
import Submission.Work.DSM5b.aeval_smul_eq_algebraMap_of_totalDegree
import Submission.Work.DSM5b.pow_mem_span_of_monic
import Submission.Work.DSM5b.eq_algebraMap_of_pow_eq_algebraMap

namespace Work.DSM5b

universe a

/-!
# The "Frobenius/integrality engine" of the DSM5b node

`R` is a perfect ring of characteristic the prime `p`, `A` a reduced `R`-algebra.  Suppose

* `h = aeval u C` is a polynomial of degree `≤ d` in the elements `u j`, whose `p`-power roots
  against `T` lie in the image of `R`: `T ^ e • u j = algebraMap (t j)`, and
* `h` satisfies a *monic* relation over `R` of degree `s`, `h ^ s = ∑_{i < s} cᵢ h ^ i`.

Then `T ^ (1/p^k) • h` lies in the image of `R` for every `k`.

The mechanism, and the reason the engine splits into three independent ingredients:

* (`aeval_smul_eq_algebraMap_of_totalDegree`) **clearing denominators**: `T ^ (e * D) • x ∈ R`
  for every `x` of `u`-degree `≤ D`;
* (`pow_mem_span_of_monic`) **the monic relation**: `h ^ m` always lies in the `R`-span of
  `1, h, …, h ^ (s-1)`, so the `u`-degree of `h ^ (p ^ n)` is bounded *uniformly in* `n`;
* (`eq_algebraMap_of_pow_eq_algebraMap`) the **`p`-th power trick**: in a reduced algebra of
  characteristic `p`, an element whose `p ^ n`-th power lies in the image of the perfect ring `R`
  already lies in it.

Explicitly, with `D := d * s` and `n := k + e * D`,
`(ϖ_k h) ^ (p ^ n) = T ^ (p ^ (e*D)) • h ^ (p ^ n)`, and the right hand side is
`∑_{i<s} algebraMap (dᵢ) • (T ^ (e*D) • h ^ i)`, a sum of elements of `R` because every
`h ^ i` has `u`-degree `≤ D`; the `p`-th power trick finishes.  This is the "CRUX" reduction of
`chartCechH0_root_killing`. -/

theorem varpi_smul_eq_algebraMap_of_integral (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R]
    [CharP R p] [PerfectRing R p] {A : Type a} [CommRing A] [Algebra R A] [IsReduced A]
    {m : ℕ} (u : Fin m → A) (t : Fin m → R) (T : R) (e : ℕ)
    (hu : ∀ j, T ^ e • u j = algebraMap R A (t j))
    (h : A) (C : MvPolynomial (Fin m) R) (hC : MvPolynomial.aeval u C = h)
    (d : ℕ) (hdeg : C.totalDegree ≤ d)
    {s : ℕ} (c : Fin s → R) (hmon : h ^ s = ∑ i : Fin s, algebraMap R A (c i) * h ^ (i : ℕ))
    (k : ℕ) :
    ∃ r : R, (frobeniusEquiv R p).symm^[k] T • h = algebraMap R A r := by
  rcases Nat.eq_zero_or_pos s with hs0 | hs
  · -- `s = 0`: the monic relation reads `1 = 0`, so `A` is the zero ring.
    subst hs0
    have h10 : (1 : A) = 0 := by simpa using hmon
    haveI : Subsingleton A := ⟨fun a b => by
      rw [← one_mul a, ← one_mul b, h10, zero_mul, zero_mul]⟩
    exact ⟨0, Subsingleton.elim _ _⟩
  · -- Main case.  Clear the denominators of `h ^ i` for all `i : Fin s` with the single
    -- exponent `e * D`, `D := d * s`.
    set D : ℕ := d * s with hD
    -- `h ^ i` is again a polynomial in `u`, of degree at most `D`.
    have hh_i : ∀ i : Fin s, h ^ (i : ℕ) = MvPolynomial.aeval u (C ^ (i : ℕ)) := by
      intro i
      rw [← hC, ← map_pow]
    have hdeg_i : ∀ i : Fin s, (C ^ (i : ℕ)).totalDegree ≤ D := by
      intro i
      calc (C ^ (i : ℕ)).totalDegree ≤ (i : ℕ) * C.totalDegree := MvPolynomial.totalDegree_pow _ _
        _ ≤ (i : ℕ) * d := Nat.mul_le_mul_left _ hdeg
        _ ≤ s * d := Nat.mul_le_mul_right _ (le_of_lt i.isLt)
        _ = D := by rw [hD]; exact Nat.mul_comm s d
    -- Clearing denominators, uniformly in `i`.
    have hex : ∀ i : Fin s, ∃ r : R, T ^ (e * D) • h ^ (i : ℕ) = algebraMap R A r := by
      intro i
      obtain ⟨r, hr⟩ :=
        aeval_smul_eq_algebraMap_of_totalDegree u t T e hu (C ^ (i : ℕ)) D (hdeg_i i)
      exact ⟨r, by rw [hh_i i]; exact hr⟩
    choose rr hrr using hex
    set n : ℕ := k + e * D with hn
    -- `h ^ (p ^ n)` is an `R`-combination of `h ^ i`, `i < s`, with a *uniform* degree bound.
    obtain ⟨dd, hdd⟩ := pow_mem_span_of_monic hs c hmon (p ^ n)
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hle : e * D ≤ p ^ (e * D) := le_of_lt (Nat.lt_pow_self hp1)
    have hTsplit : T ^ (p ^ (e * D)) = T ^ (e * D) * T ^ (p ^ (e * D) - e * D) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    -- `(ϖ_k) ^ (p ^ k) = T` (the `k`-fold iterated Frobenius-root of `T`).
    have hroot : ∀ j : ℕ, ((frobeniusEquiv R p).symm^[j] T) ^ (p ^ j) = T := by
      intro j
      induction j with
      | zero => rw [Function.iterate_zero, id_eq, pow_zero, pow_one]
      | succ j ih =>
          have hstep : (frobeniusEquiv R p).symm ((frobeniusEquiv R p).symm^[j] T) ^ p =
              (frobeniusEquiv R p).symm^[j] T := frobenius_apply_frobeniusEquiv_symm R p _
          rw [Function.iterate_succ_apply', pow_succ, mul_comm, pow_mul, hstep, ih]
    -- `ϖ_k ^ (p ^ n) = T ^ (p ^ (e * D))`, since `n = k + e * D`.
    have hTkpow : ((frobeniusEquiv R p).symm^[k] T) ^ (p ^ n) = T ^ (p ^ (e * D)) := by
      rw [hn, pow_add, pow_mul, hroot k]
    have hinner : ∀ i : Fin s, algebraMap R A (T ^ (p ^ (e * D))) * h ^ (i : ℕ)
        = algebraMap R A (T ^ (p ^ (e * D) - e * D)) * algebraMap R A (rr i) := by
      intro i
      rw [← Algebra.smul_def, hTsplit, mul_smul, smul_comm, Algebra.smul_def, hrr i, ← map_mul]
    -- The `p ^ n`-th power of `ϖ_k • h` is the image of an explicit element of `R`.
    have hy : ((frobeniusEquiv R p).symm^[k] T • h) ^ (p ^ n)
        = algebraMap R A (∑ i : Fin s, dd i * (T ^ (p ^ (e * D) - e * D) * rr i)) := by
      calc ((frobeniusEquiv R p).symm^[k] T • h) ^ (p ^ n)
          = (algebraMap R A ((frobeniusEquiv R p).symm^[k] T) * h) ^ (p ^ n) := by
              rw [Algebra.smul_def]
        _ = (algebraMap R A ((frobeniusEquiv R p).symm^[k] T)) ^ (p ^ n) * h ^ (p ^ n) := by
              rw [mul_pow]
        _ = algebraMap R A (T ^ (p ^ (e * D))) * h ^ (p ^ n) := by
              rw [← map_pow, hTkpow]
        _ = algebraMap R A (T ^ (p ^ (e * D))) *
              (∑ i : Fin s, algebraMap R A (dd i) * h ^ (i : ℕ)) := by rw [hdd]
        _ = ∑ i : Fin s, algebraMap R A (dd i) *
              (algebraMap R A (T ^ (p ^ (e * D))) * h ^ (i : ℕ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = ∑ i : Fin s, algebraMap R A (dd i) *
              (algebraMap R A (T ^ (p ^ (e * D) - e * D)) * algebraMap R A (rr i)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hinner i]
        _ = algebraMap R A (∑ i : Fin s, dd i * (T ^ (p ^ (e * D) - e * D) * rr i)) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [map_mul, map_mul]
    -- The `p`-th power trick.
    obtain ⟨r', hr'⟩ := eq_algebraMap_of_pow_eq_algebraMap (p := p)
      (x := (frobeniusEquiv R p).symm^[k] T • h)
      n (∑ i : Fin s, dd i * (T ^ (p ^ (e * D) - e * D) * rr i)) hy
    exact ⟨r', hr'⟩

end Work.DSM5b
