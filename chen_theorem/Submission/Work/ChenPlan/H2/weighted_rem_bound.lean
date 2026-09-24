import Mathlib
import Submission.Chen.SwitchDefs
import Submission.Work.ChenPlan.H1.weighted_triv_bound
import Submission.Work.NumberTheory.Chen.BTermCount.sumThreePowInvTotientBound
import Submission.Work.NumberTheory.Chen.APSwitchUpper.level_of_distribution_theta_shift

/-!
# The `3^{ω(d)}`-weighted Bombieri–Vinogradov remainder at level `√x/(log x)^B`

`Σ_{d ≤ √x/(log x)^B, d odd} 3^{ω(d)} |θ_d(x) − x/φ(d)| ≤ x/(log x)^A` for every `A`,
with `B = B(A)`.  The unweighted version is the θ-shifted Bombieri–Vinogradov theorem
(`level_of_distribution_theta_shift`); the weight `3^{ω(d)}` is absorbed by Cauchy–Schwarz,

`(Σ_d 3^{ω(d)}|r_d|)² ≤ (Σ_d 9^{ω(d)}|r_d|)(Σ_d |r_d|)`,

the first factor being bounded elementarily by `≪ x (log x)^{10}` (`r_d = θ_d(x) − x/φ(d)`,
`θ_d(x) ≤ (2x/d) log x`, and `Σ_{n ≤ X} 9^{ω n}/φ n ≪ (log X)^9` by the convolution method:
`z^{ω n} = Σ_{d ∣ n, d squarefree} (z-1)^{ω d}`).
-/

open Finset Filter
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.H2

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight

/-! ## Cauchy–Schwarz for the `3^{ω(d)}`-weight -/

/-- `(Σ 3^{ω(d)}|r_d|)² ≤ (Σ 9^{ω(d)}|r_d|)(Σ |r_d|)`. -/
lemma pow3_sum_sq_le (s : Finset ℕ) (a : ℕ → ℝ) :
    (∑ d ∈ s, (3 : ℝ) ^ d.primeFactors.card * |a d|) ^ 2
      ≤ (∑ d ∈ s, (9 : ℝ) ^ d.primeFactors.card * |a d|) * (∑ d ∈ s, |a d|) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun d => (3 : ℝ) ^ d.primeFactors.card * Real.sqrt |a d|) (fun d => Real.sqrt |a d|)
  have h3 : ∀ d : ℕ, ((3 : ℝ) ^ d.primeFactors.card * Real.sqrt |a d|)
      * Real.sqrt |a d| = (3 : ℝ) ^ d.primeFactors.card * |a d| := by
    intro d
    rw [mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
  have h9 : ∀ d : ℕ, ((3 : ℝ) ^ d.primeFactors.card * Real.sqrt |a d|) ^ 2
      = (9 : ℝ) ^ d.primeFactors.card * |a d| := by
    intro d
    have hs : Real.sqrt |a d| ^ 2 = |a d| := Real.sq_sqrt (abs_nonneg _)
    rw [mul_pow, hs]
    congr 1
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have h1 : ∀ d : ℕ, (Real.sqrt |a d|) ^ 2 = |a d| := fun d => Real.sq_sqrt (abs_nonneg _)
  rw [Finset.sum_congr rfl (fun d _ => h3 d), Finset.sum_congr rfl (fun d _ => h9 d),
    Finset.sum_congr rfl (fun d _ => h1 d)] at h
  exact h

/-! ## The convolution bound `Σ_{n ≤ X} z^{ω n}/φ n ≤ (Σ 1/φ)^z` -/

/-- `A z X ≤ (A 1 X)^z` for `z` a natural number `≥ 1`. -/
lemma A_nat_le_pow (m : ℕ) (hm : 1 ≤ m) (X : ℕ) :
    Work.NumberTheory.Chen.BTermCount.A (m : ℝ) X
      ≤ (Work.NumberTheory.Chen.BTermCount.A 1 X) ^ m := by
  induction m with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have ih' := ih hk1
      have hz1 : (1 : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ k + 1 + 1)
      have hAle := Work.NumberTheory.Chen.BTermCount.A_le ((k + 1 + 1 : ℕ) : ℝ) hz1 X
      have hcast : ((k + 1 + 1 : ℕ) : ℝ) - 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      have hshSq : ∑ n ∈ Finset.Icc 1 X,
          Work.NumberTheory.Chen.BTermCount.hSq (((k + 1 + 1 : ℕ) : ℝ) - 1) n
          ≤ Work.NumberTheory.Chen.BTermCount.A ((k + 1 : ℕ) : ℝ) X := by
        rw [hcast]
        exact Work.NumberTheory.Chen.BTermCount.sum_hSq_le _ (by positivity) X
      have hgH : ∑ n ∈ Finset.Icc 1 X, Work.NumberTheory.Chen.BTermCount.gH n
          = Work.NumberTheory.Chen.BTermCount.A 1 X :=
        (Work.NumberTheory.Chen.BTermCount.A_one_eq X).symm
      have hA1nn : 0 ≤ Work.NumberTheory.Chen.BTermCount.A 1 X := by
        rw [Work.NumberTheory.Chen.BTermCount.A_one]
        exact Finset.sum_nonneg (fun n _ => div_nonneg zero_le_one (by positivity))
      calc Work.NumberTheory.Chen.BTermCount.A ((k + 1 + 1 : ℕ) : ℝ) X
          ≤ (∑ n ∈ Finset.Icc 1 X,
                Work.NumberTheory.Chen.BTermCount.hSq (((k + 1 + 1 : ℕ) : ℝ) - 1) n)
              * (∑ n ∈ Finset.Icc 1 X, Work.NumberTheory.Chen.BTermCount.gH n) := hAle
        _ ≤ Work.NumberTheory.Chen.BTermCount.A ((k + 1 : ℕ) : ℝ) X
              * Work.NumberTheory.Chen.BTermCount.A 1 X := by
            rw [hgH]
            exact mul_le_mul_of_nonneg_right hshSq hA1nn
        _ ≤ (Work.NumberTheory.Chen.BTermCount.A 1 X) ^ (k + 1)
              * Work.NumberTheory.Chen.BTermCount.A 1 X :=
            mul_le_mul_of_nonneg_right ih' hA1nn
        _ = (Work.NumberTheory.Chen.BTermCount.A 1 X) ^ (k + 1 + 1) :=
            (pow_succ _ _).symm

/-- `Σ_{n ≤ X} 9^{ω n}/φ n ≤ C (log X)^9` for `X ≥ 2`. -/
lemma A_nine_bound : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
    Work.NumberTheory.Chen.BTermCount.A 9 X ≤ C * (Real.log (X : ℝ)) ^ 9 := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.NumberTheory.Chen.BTermCount.sumInvTotientLogBound
  refine ⟨C1 ^ 9, by positivity, ?_⟩
  intro X hX
  have hA1nn : 0 ≤ Work.NumberTheory.Chen.BTermCount.A 1 X := by
    rw [Work.NumberTheory.Chen.BTermCount.A_one]
    exact Finset.sum_nonneg (fun n _ => div_nonneg zero_le_one (by positivity))
  have hA1 : Work.NumberTheory.Chen.BTermCount.A 1 X ≤ C1 * Real.log (X : ℝ) := by
    rw [Work.NumberTheory.Chen.BTermCount.A_one]
    exact hC1 X hX
  calc Work.NumberTheory.Chen.BTermCount.A 9 X
      ≤ (Work.NumberTheory.Chen.BTermCount.A 1 X) ^ 9 := A_nat_le_pow 9 (by norm_num) X
    _ ≤ (C1 * Real.log (X : ℝ)) ^ 9 := pow_le_pow_left₀ hA1nn hA1 9
    _ = C1 ^ 9 * (Real.log (X : ℝ)) ^ 9 := by ring

/-! ## The elementary `9^{ω(d)}` bound on the shifted-`θ` remainder -/

/-- **The trivial bound.**  For `N ≤ √x`,
`Σ_{d ≤ N, d odd} 9^{ω(d)}|θ_d(x) − x/φ(d)| ≤ C x (log x)^{10}`. -/
lemma triv_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop, ∀ N : ℕ,
    (N : ℝ) ≤ Real.sqrt (x : ℝ) →
    ((Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1)).sum
      (fun d => (9 : ℝ) ^ d.primeFactors.card * |rD x d|)
    ≤ C * (x : ℝ) * (Real.log (x : ℝ)) ^ 10 := by
  obtain ⟨C9, hC9pos, hC9⟩ := A_nine_bound
  set C9' : ℝ := max C9 1 with hC9'def
  have hC9'pos : 0 < C9' := lt_of_lt_of_le zero_lt_one (le_max_right C9 1)
  have hC9'1 : 1 ≤ C9' := le_max_right C9 1
  have hC9' : ∀ X : ℕ, 2 ≤ X →
      Work.NumberTheory.Chen.BTermCount.A 9 X ≤ C9' * (Real.log (X : ℝ)) ^ 9 := by
    intro X hX
    refine le_trans (hC9 X hX) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left C9 1) (by positivity)
  refine ⟨3 * (C9' + 1), by linarith, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 16] with x hx16
  intro N hN
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx2 : 2 ≤ x := by omega
  set L : ℝ := Real.log (x : ℝ) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    have h2 : (1 : ℝ) ≤ Real.log (16 : ℝ) := by rw [h16]; nlinarith [Real.log_two_gt_d9]
    exact le_trans h2 (Real.log_le_log (by norm_num) (by exact_mod_cast hx16))
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLnn : (0 : ℝ) ≤ L := le_of_lt hLpos
  -- `A 9 N ≤ C9 L^9`
  have hA9 : Work.NumberTheory.Chen.BTermCount.A 9 N ≤ C9' * L ^ 9 := by
    by_cases hN1 : N ≤ 1
    · have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 1 := by
        intro d hd
        rw [Finset.mem_Icc] at hd ⊢
        omega
      have hAle : Work.NumberTheory.Chen.BTermCount.A 9 N ≤ 1 := by
        calc Work.NumberTheory.Chen.BTermCount.A 9 N
            ≤ Work.NumberTheory.Chen.BTermCount.A 9 1 := by
              rw [Work.NumberTheory.Chen.BTermCount.A]
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
          _ = 1 := by
              rw [Work.NumberTheory.Chen.BTermCount.A]
              simp
      calc Work.NumberTheory.Chen.BTermCount.A 9 N ≤ 1 := hAle
        _ ≤ C9' * L ^ 9 := by
            have h1 : (1 : ℝ) ≤ L ^ 9 := one_le_pow₀ hL1
            nlinarith [hC9'1]
    · have hN2' : 2 ≤ N := by omega
      have hlogN : Real.log (N : ℝ) ≤ L := by
        rw [hLdef]
        refine Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) ?_
        have hNsq : (N : ℝ) ^ 2 ≤ (x : ℝ) := by
          have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (N : ℝ)) hN 2
          rwa [Real.sq_sqrt (le_of_lt hxpos)] at h
        have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
        nlinarith [hNsq, hN1']
      calc Work.NumberTheory.Chen.BTermCount.A 9 N
          ≤ C9' * (Real.log (N : ℝ)) ^ 9 := hC9' N hN2'
        _ ≤ C9' * L ^ 9 := by
            refine mul_le_mul_of_nonneg_left ?_ hC9'pos.le
            exact pow_le_pow_left₀ (Real.log_natCast_nonneg N) hlogN 9
  -- termwise bound
  have hpt : ∀ d ∈ (Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1),
      (9 : ℝ) ^ d.primeFactors.card * |rD x d| ≤
        (9 : ℝ) ^ d.primeFactors.card * ((2 * (x : ℝ) / (d : ℝ)) * L)
        + (9 : ℝ) ^ d.primeFactors.card * ((x : ℝ) / (Nat.totient d : ℝ)) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, _⟩, _⟩ := hd
    have hθ := Work.ChenPlan.H1.thetaD_le x d hx2 hd1
    have hθnn := Work.ChenPlan.H1.thetaD_nonneg x d
    have hxnn : (0 : ℝ) ≤ (x : ℝ) / (Nat.totient d : ℝ) := by positivity
    have h1 : |rD x d| ≤ thetaD x d + (x : ℝ) / (Nat.totient d : ℝ) := by
      rw [rD, abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    have h2 : thetaD x d ≤ (2 * (x : ℝ) / (d : ℝ)) * L := by
      rw [← hLdef] at hθ
      exact hθ
    calc (9 : ℝ) ^ d.primeFactors.card * |rD x d|
        ≤ (9 : ℝ) ^ d.primeFactors.card
            * (thetaD x d + (x : ℝ) / (Nat.totient d : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (9 : ℝ) ^ d.primeFactors.card
            * ((2 * (x : ℝ) / (d : ℝ)) * L + (x : ℝ) / (Nat.totient d : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  -- the two weighted divisor sums
  have hS2 : ((Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1)).sum
      (fun d => (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ)) ≤ C9' * L ^ 9 := by
    have h2 : ((Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1)).sum
        (fun d => (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ))
        ≤ Work.NumberTheory.Chen.BTermCount.A 9 N := by
      rw [Work.NumberTheory.Chen.BTermCount.A]
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => (Finset.mem_filter.mp hd).1)
        (fun d _ _ => by positivity)
    exact le_trans h2 hA9
  have hS1 : ((Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1)).sum
      (fun d => (9 : ℝ) ^ d.primeFactors.card / (d : ℝ)) ≤ C9' * L ^ 9 := by
    have h1 : ((Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1)).sum
        (fun d => (9 : ℝ) ^ d.primeFactors.card / (d : ℝ))
        ≤ ((Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1)).sum
          (fun d => (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ)) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      have hphi : (Nat.totient d : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
      have hphipos : 0 < (Nat.totient d : ℝ) := by
        exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < d))
      have hinv : (1 : ℝ) / (d : ℝ) ≤ 1 / (Nat.totient d : ℝ) :=
        one_div_le_one_div_of_le hphipos hphi
      calc (9 : ℝ) ^ d.primeFactors.card / (d : ℝ)
          = (9 : ℝ) ^ d.primeFactors.card * ((1 : ℝ) / (d : ℝ)) := by ring
        _ ≤ (9 : ℝ) ^ d.primeFactors.card * (1 / (Nat.totient d : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ) := by ring
    exact le_trans h1 hS2
  -- assemble
  have hsplit : ((Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1)).sum
        (fun d => (9 : ℝ) ^ d.primeFactors.card * |rD x d|)
      ≤ 2 * (x : ℝ) * L * (C9' * L ^ 9) + (x : ℝ) * (C9' * L ^ 9) := by
    calc ((Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1)).sum
          (fun d => (9 : ℝ) ^ d.primeFactors.card * |rD x d|)
        ≤ ((Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1)).sum
            (fun d => (9 : ℝ) ^ d.primeFactors.card * ((2 * (x : ℝ) / (d : ℝ)) * L)
              + (9 : ℝ) ^ d.primeFactors.card * ((x : ℝ) / (Nat.totient d : ℝ))) :=
          Finset.sum_le_sum hpt
      _ = 2 * (x : ℝ) * L * ((Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1)).sum
              (fun d => (9 : ℝ) ^ d.primeFactors.card / (d : ℝ))
            + (x : ℝ) * ((Finset.Icc 1 N).filter (fun d : ℕ => d % 2 = 1)).sum
              (fun d => (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1
          · exact Finset.sum_congr rfl (fun d _ => by ring)
          · exact Finset.sum_congr rfl (fun d _ => by ring)
      _ ≤ 2 * (x : ℝ) * L * (C9' * L ^ 9) + (x : ℝ) * (C9' * L ^ 9) := by
          have h2xL : (0 : ℝ) ≤ 2 * (x : ℝ) * L := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left hS1 h2xL)
            (mul_le_mul_of_nonneg_left hS2 hxpos.le)
  refine le_trans hsplit ?_
  have h3 : C9' * (x : ℝ) * L ^ 9 * (2 * L + 1) = 2 * (x : ℝ) * L * (C9' * L ^ 9)
      + (x : ℝ) * (C9' * L ^ 9) := by ring
  rw [← h3]
  calc C9' * (x : ℝ) * L ^ 9 * (2 * L + 1)
      ≤ C9' * (x : ℝ) * L ^ 9 * (3 * L) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = 3 * C9' * (x : ℝ) * L ^ 10 := by ring
    _ ≤ 3 * (C9' + 1) * (x : ℝ) * L ^ 10 := by
        nlinarith [mul_nonneg hxpos.le (pow_nonneg hLnn 10), hC9'1]

/-- The log-power bookkeeping of the final step: if `C ≤ L^12` and `L ≥ 1` then
`(C x L^{10})·(x/L^{2A+22}) ≤ (x/L^A)²`. -/
lemma arith_key {C L A x : ℝ} (hL : 1 ≤ L) (hC : C ≤ L^12) (hx : 0 ≤ x) :
    (C * x * L^10) * (x / L^(2*A+22)) ≤ (x/L^A)^(2:ℝ) := by
  have hLpos : 0 < L := by linarith
  have hLu : 0 < L^A := Real.rpow_pos_of_pos hLpos A
  have key : C * L^10 ≤ L^22 := by
    calc C * L^10 ≤ L^12 * L^10 := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = L ^ 22 := by
          rw [← Real.rpow_natCast L 12, ← Real.rpow_natCast L 10, ← Real.rpow_add hLpos]
          norm_num
  have h2 : L ^ (2*A+22) = L^(2*A) * L^22 := by
    rw [Real.rpow_add hLpos (2*A) 22]
    simp
  have h3 : (x/L^A)^(2:ℝ) = x^2/L^(2*A) := by
    rw [Real.div_rpow hx hLu.le 2, ← Real.rpow_mul hLpos.le A 2]
    rw [Real.rpow_two]
    congr 1
    ring_nf
  rw [h2, h3, le_div_iff₀ (by positivity : (0:ℝ) < L^(2*A))]
  field_simp
  nlinarith [key, sq_nonneg x]


/-! ## The main theorem -/

theorem weighted_rem_bound :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      ((Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
          (fun d : ℕ => d % 2 = 1)).sum
        (fun d => (3 : ℝ) ^ d.primeFactors.card *
          |((Finset.range (x + 1)).filter (fun p => p.Prime ∧ d ∣ p + 2)).sum
              (fun p => Real.log (p : ℝ))
            - (x : ℝ) / (Nat.totient d : ℝ)|)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  obtain ⟨C, hCpos, hC⟩ := triv_bound
  obtain ⟨B, hBpos, hbv⟩ :=
    Work.NumberTheory.Chen.APSwitchUpper.level_of_distribution_theta_shift (2 * A + 22)
      (by linarith)
  refine ⟨B, hBpos, ?_⟩
  have hbig : ∀ᶠ x : ℕ in Filter.atTop, C ≤ (Real.log (x : ℝ)) ^ (12 : ℝ) := by
    have h1 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun y : ℝ => y ^ (12 : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by norm_num)
    exact (h2.comp h1).eventually_ge_atTop C
  filter_upwards [hC, hbv, hbig, Filter.eventually_ge_atTop 16] with x hCx hbvx hbigx hx16
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  set L : ℝ := Real.log (x : ℝ) with hLdef
  set K : ℕ := ⌊Real.sqrt (x : ℝ) / L ^ B⌋₊ with hKdef
  set S : Finset ℕ := (Finset.Icc 1 K).filter (fun d : ℕ => d % 2 = 1) with hSdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    have h2 : (1 : ℝ) ≤ Real.log (16 : ℝ) := by rw [h16]; nlinarith [Real.log_two_gt_d9]
    exact le_trans h2 (Real.log_le_log (by norm_num) (by exact_mod_cast hx16))
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hKle : (K : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [hKdef]
    have hb1 : (1 : ℝ) ≤ L ^ B := Real.one_le_rpow hL1 hBpos.le
    have hy : Real.sqrt (x : ℝ) / L ^ B ≤ Real.sqrt (x : ℝ) := by
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hLpos B)]
      nlinarith [Real.sqrt_nonneg (x : ℝ), hb1]
    exact le_trans (Nat.floor_le (by positivity)) hy
  -- the elementary factor
  have hT9 : ∑ d ∈ S, (9 : ℝ) ^ d.primeFactors.card * |rD x d| ≤ C * (x : ℝ) * L ^ 10 := by
    rw [hSdef]
    exact hCx K hKle
  -- the unweighted Bombieri–Vinogradov factor
  have hBv : ∑ d ∈ S, |rD x d| ≤ (x : ℝ) / L ^ (2 * A + 22) := by
    rw [hSdef]
    exact hbvx
  have hWnn : 0 ≤ ∑ d ∈ S, (3 : ℝ) ^ d.primeFactors.card * |rD x d| :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (by positivity) (abs_nonneg _))
  have hBvnn : 0 ≤ ∑ d ∈ S, |rD x d| := Finset.sum_nonneg (fun d _ => abs_nonneg _)
  have hW2 : (∑ d ∈ S, (3 : ℝ) ^ d.primeFactors.card * |rD x d|) ^ 2
      ≤ (C * (x : ℝ) * L ^ 10) * ((x : ℝ) / L ^ (2 * A + 22)) :=
    le_trans (pow3_sum_sq_le S (fun d => rD x d))
      (mul_le_mul hT9 hBv hBvnn (by positivity))
  have harith : (C * (x : ℝ) * L ^ 10) * ((x : ℝ) / L ^ (2 * A + 22)) ≤ ((x : ℝ) / L ^ A) ^ 2 := by
    have hC12 : C ≤ L ^ 12 := by simpa using hbigx
    simpa using arith_key hL1 hC12 hxpos.le

  have hfin : ∑ d ∈ S, (3 : ℝ) ^ d.primeFactors.card * |rD x d| ≤ (x : ℝ) / L ^ A := by
    calc ∑ d ∈ S, (3 : ℝ) ^ d.primeFactors.card * |rD x d|
        = Real.sqrt ((∑ d ∈ S, (3 : ℝ) ^ d.primeFactors.card * |rD x d|) ^ 2) :=
          (Real.sqrt_sq hWnn).symm
      _ ≤ Real.sqrt (((x : ℝ) / L ^ A) ^ 2) := Real.sqrt_le_sqrt (le_trans hW2 harith)
      _ = (x : ℝ) / L ^ A := Real.sqrt_sq (by positivity)
  have hconv : ∑ d ∈ S, (fun d : ℕ => (3 : ℝ) ^ d.primeFactors.card *
          |((Finset.range (x + 1)).filter (fun p => p.Prime ∧ d ∣ p + 2)).sum
              (fun p => Real.log (p : ℝ))
            - (x : ℝ) / (Nat.totient d : ℝ)|) d
      = ∑ d ∈ S, (3 : ℝ) ^ d.primeFactors.card * |rD x d| :=
    Finset.sum_congr rfl (fun d _ => rfl)
  rw [hconv]
  exact hfin


end

end Work.ChenPlan.H2
