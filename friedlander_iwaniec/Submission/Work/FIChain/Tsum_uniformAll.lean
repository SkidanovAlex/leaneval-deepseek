import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.LocalS4
import Submission.Work.FIChain.LocalS5c

/-!
# `Submission.Work.FIChain.Tsum_uniformAll`

The same `4` estimate as `Work.FIChain.T_eval4` / `Tsum_uniformC`, but with the constant `K`
*hoisted out of every parameter*: a single pair `(K, H)` works simultaneously for all sequences
`a`, remainders `r`, sieve weights `lam`, and all sizes `N, M, D, D, A, Rem, B`.

The two density inputs `Commons.NumberTheory.Sieve.sum_mu_g_div_gcd_le` and
`sum_mu_g_div_gcd_log_eq` depend only on the density `g`, and their outputs `C24`, `C24'`, `H`
are the only constants entering the proof of `T_eval4`, so the same argument goes through
verbatim with those constants fixed once and for all.
-/

namespace Work.FIChain

open Finset Filter
open Submission.ASP
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The uniform-in-everything `4` estimate: one pair `(K, H)` for all `a, r, lam, N, M, D, D,
`A, Rem, B`. -/
theorem Tsum_uniformAll {g : ℕ → ℝ}
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ K H : ℝ, 0 < K ∧ 0 < H ∧
      Filter.Tendsto (fun n : ℕ => ∑ d ∈ Finset.Icc 1 n,
          (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d) Filter.atTop (nhds (-H)) ∧
      ∀ (a : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (lam : ℕ → ℝ) (N M D Δ : ℕ) (A Rem B : ℝ),
        (hx : 2 ≤ N) → (hy : 2 ≤ M) → (hyx : M ≤ N) →
        (hlog4 : Real.log (N : ℝ) ≤ 4 * Real.log (M : ℝ)) →
        (ha : ∀ n : ℕ, 0 ≤ a n) → (hA : A = Submission.ASP.Acount a (N : ℝ)) →
        (hAd : Submission.ASP.Approx a g r (N : ℝ)) →
        (hRem : ∀ m : ℕ, m ≤ N → Submission.ASP.RemainderSum r D m ≤ Rem) → (hRem0 : 0 ≤ Rem) →
        (hRem3 : Rem ≤ A * (Real.log (N : ℝ)) ^ (-(3 : ℤ))) →
        (hΔy : Δ * M ≤ D) → (hΔ2 : Δ ^ 2 ≤ M) → (hΔ1 : 1 ≤ Δ) →
        (hlam1 : lam 1 = 1) → (hΔsupp : ∀ ν : ℕ, Δ < ν → lam ν = 0) →
        (hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0) → (hlam_le : ∀ ν : ℕ, |lam ν| ≤ 1) →
        (hB : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
            |lam ν| * g ν * (ν.divisors.card : ℝ)
              * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) ≤ B) →
        |Submission.ASP.Tsum a lam (N : ℝ) (M : ℝ) - H * A|
          ≤ K * A * (B * (Real.log (M : ℝ)) ^ (-(5 : ℤ)) + (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
  classical
  obtain ⟨C24, hC24pos, h24⟩ :=
    Commons.NumberTheory.Sieve.sum_mu_g_div_gcd_le hgmul hg1 hp hbound h9
  obtain ⟨C24', H, hC24'pos, hHpos, hHtend, h24log⟩ :=
    Commons.NumberTheory.Sieve.sum_mu_g_div_gcd_log_eq hgmul hg1 hp hbound h9
  refine ⟨4 * C24 + C24' + 3, H, by positivity, hHpos, hHtend, ?_⟩
  intro a r lam N M D Δ A Rem B hx hy hyx hlog4 ha hA hAd hRem hRem0 hRem3 hΔy hΔ2 hΔ1 hlam1 hΔsupp hlam_sq hlam_le hB
  have hgp : ∀ p : ℕ, p.Prime → 0 ≤ g p := fun p hp' => (hp p hp').1
  have hN1 : 1 ≤ N := by omega
  have hM1 : 1 ≤ M := by omega
  have hlogN1 : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogM1 : (0 : ℝ) < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hfl : ⌊(M : ℝ)⌋₊ ≤ N := by rw [Nat.floor_natCast]; exact hyx
  have hfil : (Finset.Icc 1 N).filter (fun b => ((b : ℕ) : ℝ) ≤ (M : ℝ)) = Finset.Icc 1 M := by
    rw [filter_Icc_eq_Icc_floor (by positivity) hfl, Nat.floor_natCast]
  have hAeq : A = Acount a (N : ℝ) := by rw [hA, Acount, Nat.floor_natCast]
  have hA0 : 0 ≤ A := by
    rw [hAeq, Acount, Nat.floor_natCast]
    exact Finset.sum_nonneg (fun n _ => ha n)
  have hB0 : 0 ≤ B := by
    refine le_trans (Finset.sum_nonneg ?_) hB
    intro ν hν
    rw [Finset.mem_filter] at hν
    have hgnn : 0 ≤ g ν := g_nonneg_of_squarefree hgmul hg1 hgp hν.2
    refine mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hgnn) (by positivity)) ?_
    exact Finset.prod_nonneg (fun p hp' => by
      have : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp'))
      positivity)
  have hpow : ∀ k : ℤ, 0 ≤ (Real.log (M : ℝ)) ^ k := fun k => zpow_nonneg hlogM1.le k
  -- (1) `T₁`
  have hT1rw : T1 a lam (N : ℝ) (M : ℝ)
      = ∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * VbLog a lam b (N : ℝ) := by
    rw [T1, Nat.floor_natCast, hfil]
  have hT1eq := T1_eq (a := a) (g := g) (r := r) (lam := lam) (x := (N : ℝ)) (y := (M : ℝ))
    (Δ := Δ) hgmul hAd hΔsupp
  rw [Nat.floor_natCast, hfil] at hT1eq
  have hcoeff : |∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * lamCoeff g lam Δ b|
      ≤ C24 * B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) := by
    refine le_trans (sum_mu_lamCoeff_le hgmul (fun ν y hν hy hνy => h24 ν hν y hy hνy) hg1 hgp hΔsupp hlam_sq hy hΔ2) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hC24pos.le)
      (zpow_nonneg hlogM1.le _)
  have hLMS : (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * Real.log (M : ℝ)
      = (Real.log (M : ℝ)) ^ (-(5 : ℤ)) := by
    have h := zpow_add₀ (ne_of_gt hlogM1) (-(6 : ℤ)) 1
    rw [zpow_one, show (-(6 : ℤ)) + 1 = -(5 : ℤ) from by norm_num] at h
    exact h.symm
  have hT1b : |T1 a lam (N : ℝ) (M : ℝ)|
      ≤ 4 * C24 * B * A * (Real.log (M : ℝ)) ^ (-(5 : ℤ))
        + 2 * A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
    have hmain : C24 * B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (A * Real.log (N : ℝ))
        ≤ 4 * C24 * B * A * (Real.log (M : ℝ)) ^ (-(5 : ℤ)) := by
      calc C24 * B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (A * Real.log (N : ℝ))
          ≤ C24 * B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (A * (4 * Real.log (M : ℝ))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog4 hA0) ?_
            exact mul_nonneg (mul_nonneg hC24pos.le hB0) (hpow _)
        _ = 4 * C24 * B * A * (Real.log (M : ℝ)) ^ (-(5 : ℤ)) := by
            rw [← hLMS]; ring
    have hrem : 2 * Real.log (N : ℝ) * Rem ≤ 2 * A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
      have h1 : 2 * Real.log (N : ℝ) * Rem
          ≤ 2 * Real.log (N : ℝ) * (A * (Real.log (N : ℝ)) ^ (-(3 : ℤ))) :=
        mul_le_mul_of_nonneg_left hRem3 (by linarith)
      refine le_trans h1 (le_of_eq ?_)
      have hLN3 : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℤ))
          = (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
        have h := zpow_add₀ (ne_of_gt hlogN1) 1 (-(3 : ℤ))
        rw [zpow_one, show (1 : ℤ) + (-(3 : ℤ)) = -(2 : ℤ) from by norm_num] at h
        exact h.symm
      rw [← hLN3]; ring
    rw [hT1eq]
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add ?_ ?_) (add_le_add hmain hrem)
    · have habelA : |abelForm (fun m => Acount a (m : ℝ)) N| ≤ A * Real.log (N : ℝ) := by
        rw [hAeq]
        exact abs_abelForm_Acount_le ha hN1
      rw [abs_mul]
      exact le_trans (mul_le_mul hcoeff habelA (abs_nonneg _)
        (mul_nonneg (mul_nonneg hC24pos.le hB0) (hpow _))) (le_of_eq rfl)
    · exact abelForm_r_bound (r := r) (Δ := Δ) (Y := M) (D := D) (N := N) (Rem := Rem)
        hlam_le hlam_sq hN1 (hRem) hΔy
  -- (2) `T₂`
  have hT2rw : T2 a lam (N : ℝ) (M : ℝ)
      = ∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
          * Vb a lam b (N : ℝ) := by
    rw [T2, Nat.floor_natCast, hfil]
  have hT2eq : T2 a lam (N : ℝ) (M : ℝ) + H * A
      = A * ((∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
            * lamCoeff g lam Δ b) + H)
        + ∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
            * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N := by
    rw [hT2rw]
    have hpt : ∀ b ∈ Finset.Icc 1 M,
        (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ) * Vb a lam b (N : ℝ)
          = (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
              * (lamCoeff g lam Δ b * Acount a (N : ℝ)
                  + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N) := by
      intro b hb
      rw [Finset.mem_Icc] at hb
      by_cases hbsq : Squarefree b
      · rw [Vb_nat_eq_coeff hgmul hAd hΔsupp (by omega) hbsq]
      · have hmu : (ArithmeticFunction.moebius b : ℝ) = 0 := by
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hbsq]; norm_num
        rw [hmu]; ring
    rw [Finset.sum_congr rfl hpt]
    rw [show (∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
          * (lamCoeff g lam Δ b * Acount a (N : ℝ)
              + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N))
        = (∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
              * lamCoeff g lam Δ b * Acount a (N : ℝ))
          + ∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
              * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N from by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b _
        ring]
    rw [← Finset.sum_mul, hAeq]
    ring
  have hlogMN : Real.log (M : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 1 ≤ M)) (by exact_mod_cast hyx)
  have hLN3 : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℤ))
      = (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
    have h := zpow_add₀ (ne_of_gt hlogN1) 1 (-(3 : ℤ))
    rw [zpow_one, show (1 : ℤ) + (-(3 : ℤ)) = -(2 : ℤ) from by norm_num] at h
    exact h.symm
  have hrtail : Real.log (M : ℝ) * Rem ≤ A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hRem3 hlogM1.le) ?_
    calc Real.log (M : ℝ) * (A * (Real.log (N : ℝ)) ^ (-(3 : ℤ)))
        = A * (Real.log (M : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℤ))) := by ring
      _ ≤ A * (Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℤ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlogMN (zpow_nonneg hlogN1.le _)) hA0
      _ = A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by rw [hLN3]
  have hcoefflog : |(∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
          * lamCoeff g lam Δ b) + H| ≤ C24' * B * (Real.log (M : ℝ)) ^ (-(5 : ℤ)) := by
    refine le_trans (sum_mu_log_lamCoeff_eq hgmul (fun ν y hν hy hνy => h24log ν hν y hy hνy) hg1 hgp hΔsupp hlam_sq hlam1 hΔ1
      hy hΔ2) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hC24'pos.le)
      (zpow_nonneg hlogM1.le _)
  have hr2 : |∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
          * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N|
      ≤ Real.log (M : ℝ) * Rem := by
    have h1 : ∀ b ∈ Finset.Icc 1 M,
        |(ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
            * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N|
          ≤ |(ArithmeticFunction.moebius b : ℝ)| * ∑ ν ∈ Finset.Icc 1 Δ,
              |lam ν| * (Real.log (M : ℝ) * |r (Nat.lcm ν b) N|) := by
      intro b hb
      rw [Finset.mem_Icc] at hb
      have hlogb0 : 0 ≤ Real.log (b : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b))
      have hlogbM : Real.log (b : ℝ) ≤ Real.log (M : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 1 ≤ b)) (by exact_mod_cast hb.2)
      have hle : |∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N|
          ≤ ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |r (Nat.lcm ν b) N| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum
        intro ν _
        rw [abs_mul]
      calc |(ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
            * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N|
          = |(ArithmeticFunction.moebius b : ℝ)|
              * (Real.log (b : ℝ) * |∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hlogb0]; ring
        _ ≤ |(ArithmeticFunction.moebius b : ℝ)|
              * (Real.log (M : ℝ) * ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |r (Nat.lcm ν b) N|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hlogbM hle (abs_nonneg _) hlogM1.le) (abs_nonneg _)
        _ = |(ArithmeticFunction.moebius b : ℝ)| * ∑ ν ∈ Finset.Icc 1 Δ,
              |lam ν| * (Real.log (M : ℝ) * |r (Nat.lcm ν b) N|) := by
            rw [Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro ν _
            ring
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum h1) ?_
    have h2 : (∑ b ∈ Finset.Icc 1 M, |(ArithmeticFunction.moebius b : ℝ)|
          * ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * (Real.log (M : ℝ) * |r (Nat.lcm ν b) N|))
        ≤ ∑ b ∈ (Finset.Icc 1 M).filter Squarefree,
            ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
              (Real.log (M : ℝ) * |r (Nat.lcm ν b) N|) :=
      sum_mu_lam_abs_le_sqfree (s := Finset.Icc 1 M) (t := Finset.Icc 1 Δ)
        (F := fun b ν => Real.log (M : ℝ) * |r (Nat.lcm ν b) N|)
        (fun b ν => mul_nonneg hlogM1.le (abs_nonneg _)) hlam_sq hlam_le
    refine le_trans h2 ?_
    have h3 : (∑ b ∈ (Finset.Icc 1 M).filter Squarefree,
            ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
              (Real.log (M : ℝ) * |r (Nat.lcm ν b) N|))
        = Real.log (M : ℝ) * ∑ b ∈ (Finset.Icc 1 M).filter Squarefree,
            ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, |r (Nat.lcm ν b) N| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
    rw [h3]
    refine mul_le_mul_of_nonneg_left ?_ hlogM1.le
    rw [Finset.sum_comm]
    exact le_trans (sum_lcm_le_remainderSum (Δ := Δ) (M := M) (D := D) hΔy N) (hRem N le_rfl)
  have hT2b : |T2 a lam (N : ℝ) (M : ℝ) + H * A|
      ≤ A * (C24' * B * (Real.log (M : ℝ)) ^ (-(5 : ℤ))) + A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
    rw [hT2eq]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_nonneg hA0]
    exact add_le_add (mul_le_mul_of_nonneg_left hcoefflog hA0) (le_trans hr2 hrtail)
  -- (3) assembly
  have hTsum : Tsum a lam (N : ℝ) (M : ℝ) - H * A
      = T1 a lam (N : ℝ) (M : ℝ) - (T2 a lam (N : ℝ) (M : ℝ) + H * A) := by
    rw [Tsum_eq, T1, T2]; ring
  rw [hTsum]
  refine le_trans (le_trans (abs_sub _ _) (add_le_add hT1b hT2b)) ?_
  have hX : 0 ≤ B * (Real.log (M : ℝ)) ^ (-(5 : ℤ)) := mul_nonneg hB0 (zpow_nonneg hlogM1.le _)
  have hY : 0 ≤ (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := zpow_nonneg hlogN1.le _
  have hKA : 0 ≤ (4 * C24 + C24' + 3) * A := by positivity
  nlinarith [hA0, hX, hY, hC24pos, hC24'pos.le, mul_nonneg hA0 hX, mul_nonneg hA0 hY,
    mul_nonneg (by positivity : (0:ℝ) ≤ 4 * C24 + C24' + 3) hA0]

end

end Work.FIChain
