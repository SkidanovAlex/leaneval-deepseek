import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.theta_le_log3_mul
import Submission.Commons.Analysis.ExpLog.harmonic_le_one_add_log

/-!
# A Chebyshev-type bound for `∑_{p ≤ N} log p / (p - 1)`

We prove `∑_{p ≤ N} log p / (p−1) ≤ log 3 · (log N + 2)` for `N ≥ 2`.

The input is Hanson's bound `θ(n) ≤ log 3 · n` (`theta_le_log3_mul`, from
`lcm(1,…,n) ≤ 3^n`), combined with Abel summation.  Writing `θ(k) = ∑_{p ≤ k} log p`,
the telescoping identity `1/(p−1) = 1/(N−1) + ∑_{k=p}^{N−1} 1/(k(k−1))` and an
exchange of summation order give the exact identity

`∑_{p ≤ N} log p/(p−1) = θ(N)/(N−1) + ∑_{k=2}^{N−1} θ(k)/(k(k−1))`,

and termwise `θ(k)/(k(k−1)) ≤ log 3 · k/(k(k−1)) = log 3/(k−1)`.  Hence

`∑ ≤ log 3 · ( N/(N−1) + ∑_{k=2}^{N−1} 1/(k−1) ) = log 3 · (1 + H_{N−1}) ≤ log 3·(log N + 2)`.
-/

open scoped BigOperators

namespace Work.RHContract.A.R3

/-- Telescoping: `∑_{k=p}^{N−1} 1/(k(k−1)) = 1/(p−1) − 1/(N−1)`. -/
private lemma telescoping_core {p N : ℕ} (hp : 2 ≤ p) (hpN : p ≤ N) :
    ∑ k ∈ Finset.Icc p (N-1), (1:ℝ)/((k:ℝ)*((k:ℝ)-1))
      = 1/((p:ℝ)-1) - 1/((N:ℝ)-1) := by
  by_cases hle : p ≤ N - 1
  · have h := Finset.sum_Icc_sub (m := p) (n := N-1)
      (f := fun i : ℕ => (1:ℝ)/((i:ℝ)-1)) hle
    have key : ∀ i ∈ Finset.Icc p (N-1),
        ((1:ℝ)/((((i+1:ℕ)):ℝ)-1) - (1:ℝ)/((i:ℝ)-1)) = -((1:ℝ)/((i:ℝ)*((i:ℝ)-1))) := by
      intro i hi
      have hi2 : 2 ≤ i := le_trans hp (Finset.mem_Icc.mp hi).1
      have hcast : (((i+1:ℕ)):ℝ) - 1 = (i:ℝ) := by push_cast; ring
      have hi0 : (i:ℝ) ≠ 0 := by positivity
      have hi1 : (i:ℝ) - 1 ≠ 0 := by
        have h2 : (1:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 1 < i)
        linarith
      rw [hcast]
      field_simp
      ring
    rw [Finset.sum_congr rfl key, Finset.sum_neg_distrib] at h
    have hN1 : 1 ≤ N := by omega
    rw [Nat.sub_add_cancel hN1] at h
    linarith [h]
  · have hpEq : p = N := by omega
    rw [hpEq]
    have hempty : Finset.Icc N (N-1) = ∅ := Finset.Icc_eq_empty_iff.mpr (by omega)
    rw [hempty, Finset.sum_empty, sub_self]

/-- `∑_{p ≤ n} log p ≤ log 3 · n` (Hanson's bound on `θ`). -/
private lemma sum_log_primesLE_le (n : ℕ) :
    (∑ p ∈ Nat.primesLE n, Real.log (p:ℝ)) ≤ Real.log 3 * (n:ℝ) := by
  have h := Commons.NumberTheory.Chebyshev.theta_le_log3_mul n
  rwa [Chebyshev.theta_eq_sum_primesLE (n:ℝ), Nat.floor_natCast] at h

/-- Abel summation: `∑_{p ≤ N} log p/(p−1) = θ(N)/(N−1) + ∑_{k=2}^{N−1} θ(k)/(k(k−1))`. -/
private lemma abel_identity (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log (p:ℝ)/((p:ℝ)-1)
      = (∑ p ∈ Nat.primesLE N, Real.log (p:ℝ))/((N:ℝ)-1)
        + ∑ k ∈ Finset.Icc 2 (N-1), (∑ p ∈ Nat.primesLE k, Real.log (p:ℝ))/((k:ℝ)*((k:ℝ)-1)) := by
  have hdec : ∀ p ∈ Nat.primesLE N,
      (1:ℝ)/((p:ℝ)-1) = 1/((N:ℝ)-1) + ∑ k ∈ Finset.Icc p (N-1), (1:ℝ)/((k:ℝ)*((k:ℝ)-1)) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
    have hpN : p ≤ N := (Nat.mem_primesLE.mp hp).1
    have htel := telescoping_core hp2 hpN
    linarith [htel]
  have hS : (∑ p ∈ Nat.primesLE N, Real.log (p:ℝ)/((p:ℝ)-1))
      = ∑ p ∈ Nat.primesLE N, Real.log (p:ℝ) * (1/((N:ℝ)-1) + ∑ k ∈ Finset.Icc p (N-1), (1:ℝ)/((k:ℝ)*((k:ℝ)-1))) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [div_eq_mul_one_div, hdec p hp]
  have hdist : (∑ p ∈ Nat.primesLE N, Real.log (p:ℝ) * (1/((N:ℝ)-1) + ∑ k ∈ Finset.Icc p (N-1), (1:ℝ)/((k:ℝ)*((k:ℝ)-1))))
      = (∑ p ∈ Nat.primesLE N, Real.log (p:ℝ) * (1/((N:ℝ)-1)))
        + ∑ p ∈ Nat.primesLE N, Real.log (p:ℝ) * (∑ k ∈ Finset.Icc p (N-1), (1:ℝ)/((k:ℝ)*((k:ℝ)-1))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp; ring
  have hfirst : (∑ p ∈ Nat.primesLE N, Real.log (p:ℝ) * (1/((N:ℝ)-1)))
      = (∑ p ∈ Nat.primesLE N, Real.log (p:ℝ))/((N:ℝ)-1) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun p hp => mul_one_div _ _)
  have hsecond : (∑ p ∈ Nat.primesLE N, Real.log (p:ℝ) * (∑ k ∈ Finset.Icc p (N-1), (1:ℝ)/((k:ℝ)*((k:ℝ)-1))))
      = ∑ k ∈ Finset.Icc 2 (N-1), (∑ p ∈ Nat.primesLE k, Real.log (p:ℝ))/((k:ℝ)*((k:ℝ)-1)) := by
    have e1 : ∀ p ∈ Nat.primesLE N, Real.log (p:ℝ) * (∑ k ∈ Finset.Icc p (N-1), (1:ℝ)/((k:ℝ)*((k:ℝ)-1)))
        = ∑ k ∈ Finset.Icc p (N-1), Real.log (p:ℝ)/((k:ℝ)*((k:ℝ)-1)) := by
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_one_div]
    rw [Finset.sum_congr rfl e1]
    have e2 : ∀ p ∈ Nat.primesLE N, (∑ k ∈ Finset.Icc p (N-1), Real.log (p:ℝ)/((k:ℝ)*((k:ℝ)-1)))
        = ∑ k ∈ Finset.Icc 2 (N-1), (if p ≤ k then Real.log (p:ℝ)/((k:ℝ)*((k:ℝ)-1)) else 0) := by
      intro p hp
      have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
      have hpN : p ≤ N := (Nat.mem_primesLE.mp hp).1
      have hfil : (Finset.Icc 2 (N-1)).filter (fun k => p ≤ k) = Finset.Icc p (N-1) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [← Finset.sum_filter, hfil]
    rw [Finset.sum_congr rfl e2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := by have := (Finset.mem_Icc.mp hk).2; omega
    have hfil2 : (Nat.primesLE N).filter (fun p => p ≤ k) = Nat.primesLE k := by
      ext p
      rw [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨hpN, hpp⟩, hpk⟩; exact ⟨hpk, hpp⟩
      · rintro ⟨hpk, hpp⟩; exact ⟨⟨le_trans hpk hkN, hpp⟩, hpk⟩
    rw [← Finset.sum_filter, hfil2]
    rw [Finset.sum_div]
  rw [hS, hdist, hfirst, hsecond]

/-- Reindexing `∑_{k=2}^{N−1} 1/(k−1) = ∑_{j=1}^{N−2} 1/j`. -/
private lemma reindex_sum (N : ℕ) (hN : 2 ≤ N) :
    (∑ k ∈ Finset.Icc 2 (N-1), (1:ℝ)/((k:ℝ)-1)) = ∑ j ∈ Finset.Icc 1 (N-2), (1:ℝ)/(j:ℝ) := by
  refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · intro k1 hk1 k2 hk2 heq
    rw [Finset.mem_Icc] at hk1 hk2
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    refine ⟨j+1, ?_, by omega⟩
    rw [Finset.mem_Icc]; omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Nat.cast_pred (R := ℝ) (n := k) (by omega : 0 < k)]

theorem prime_log_div_sub_one_sum_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) / ((p : ℝ) - 1)
      ≤ Real.log 3 * (Real.log (N : ℝ) + 2) := by
  rw [abel_identity N]
  set R := ∑ k ∈ Finset.Icc 2 (N-1), (1:ℝ)/((k:ℝ)-1) with hRdef
  have hNpos : (0:ℝ) < (N:ℝ) - 1 := by
    have : (1:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 1 < N)
    linarith
  have hfirst : (∑ p ∈ Nat.primesLE N, Real.log (p:ℝ))/((N:ℝ)-1)
      ≤ Real.log 3 * ((N:ℝ)/((N:ℝ)-1)) := by
    calc (∑ p ∈ Nat.primesLE N, Real.log (p:ℝ))/((N:ℝ)-1)
        ≤ (Real.log 3 * (N:ℝ))/((N:ℝ)-1) :=
          div_le_div_of_nonneg_right (sum_log_primesLE_le N) hNpos.le
      _ = Real.log 3 * ((N:ℝ)/((N:ℝ)-1)) := by rw [mul_div_assoc]
  have hterm : ∀ k ∈ Finset.Icc 2 (N-1),
      (∑ p ∈ Nat.primesLE k, Real.log (p:ℝ))/((k:ℝ)*((k:ℝ)-1))
        ≤ Real.log 3 * (1/((k:ℝ)-1)) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hc : (0:ℝ) < (k:ℝ)*((k:ℝ)-1) := by
      have h1 : (0:ℝ) < (k:ℝ) := by
        have : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
        exact this
      have h2 : (0:ℝ) < (k:ℝ) - 1 := by
        have : (1:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 1 < k)
        linarith
      exact mul_pos h1 h2
    have hk0 : (k:ℝ) ≠ 0 := by positivity
    have hkc : (k:ℝ) - 1 ≠ 0 := by
      have : (1:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 1 < k)
      linarith
    calc (∑ p ∈ Nat.primesLE k, Real.log (p:ℝ))/((k:ℝ)*((k:ℝ)-1))
        ≤ (Real.log 3 * (k:ℝ))/((k:ℝ)*((k:ℝ)-1)) :=
          div_le_div_of_nonneg_right (sum_log_primesLE_le k) hc.le
      _ = Real.log 3 * (1/((k:ℝ)-1)) := by field_simp
  have hsecond : (∑ k ∈ Finset.Icc 2 (N-1),
        (∑ p ∈ Nat.primesLE k, Real.log (p:ℝ))/((k:ℝ)*((k:ℝ)-1))) ≤ Real.log 3 * R := by
    calc (∑ k ∈ Finset.Icc 2 (N-1),
          (∑ p ∈ Nat.primesLE k, Real.log (p:ℝ))/((k:ℝ)*((k:ℝ)-1)))
        ≤ ∑ k ∈ Finset.Icc 2 (N-1), Real.log 3 * (1/((k:ℝ)-1)) := Finset.sum_le_sum hterm
      _ = Real.log 3 * R := by rw [hRdef, Finset.mul_sum]
  have htail : (N:ℝ)/((N:ℝ)-1) + R ≤ Real.log (N:ℝ) + 2 := by
    have hRidx := reindex_sum N hN
    have hN1 : 1 ≤ N - 1 := by omega
    have hharm : (∑ j ∈ Finset.Icc 1 (N-1), (1:ℝ)/(j:ℝ))
        ≤ 1 + Real.log (((N-1:ℕ)):ℝ) :=
      Commons.Analysis.ExpLog.harmonic_le_one_add_log (N-1) hN1
    have hsum : (∑ j ∈ Finset.Icc 1 (N-1), (1:ℝ)/(j:ℝ))
        = (∑ j ∈ Finset.Icc 1 (N-2), (1:ℝ)/(j:ℝ)) + 1/(((N-1:ℕ)):ℝ) := by
      have h := Finset.sum_Icc_succ_top (a := 1) (b := N-2)
        (f := fun j : ℕ => (1:ℝ)/(j:ℝ)) (by omega : 1 ≤ N-2+1)
      have hb : N - 2 + 1 = N - 1 := by omega
      simpa [hb] using h
    have hfrac : (N:ℝ)/((N:ℝ)-1) = 1 + 1/((N:ℝ)-1) := by
      have hNc : (N:ℝ) - 1 ≠ 0 := ne_of_gt hNpos
      field_simp
      ring
    have hNcast : (((N-1:ℕ)):ℝ) = (N:ℝ) - 1 := Nat.cast_pred (R := ℝ) (n := N) (by omega : 0 < N)
    have hlog : Real.log (((N-1:ℕ)):ℝ) ≤ Real.log (N:ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast (by omega : 0 < N - 1)
      · exact_mod_cast (by omega : N - 1 ≤ N)
    calc (N:ℝ)/((N:ℝ)-1) + R
        = 1 + ((∑ j ∈ Finset.Icc 1 (N-2), (1:ℝ)/(j:ℝ)) + 1/(((N-1:ℕ)):ℝ)) := by
          rw [hRdef, hRidx, hfrac, hNcast]; ring
      _ = 1 + ∑ j ∈ Finset.Icc 1 (N-1), (1:ℝ)/(j:ℝ) := by rw [hsum]
      _ ≤ 1 + (1 + Real.log (((N-1:ℕ)):ℝ)) := by linarith [hharm]
      _ ≤ Real.log (N:ℝ) + 2 := by linarith [hlog]
  calc (∑ p ∈ Nat.primesLE N, Real.log (p:ℝ))/((N:ℝ)-1)
        + ∑ k ∈ Finset.Icc 2 (N-1), (∑ p ∈ Nat.primesLE k, Real.log (p:ℝ))/((k:ℝ)*((k:ℝ)-1))
      ≤ Real.log 3 * ((N:ℝ)/((N:ℝ)-1)) + Real.log 3 * R := add_le_add hfirst hsecond
    _ = Real.log 3 * ((N:ℝ)/((N:ℝ)-1) + R) := by ring
    _ ≤ Real.log 3 * (Real.log (N:ℝ) + 2) :=
        mul_le_mul_of_nonneg_left htail (Real.log_nonneg (by norm_num))

end Work.RHContract.A.R3
