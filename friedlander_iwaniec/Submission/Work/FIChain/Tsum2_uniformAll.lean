import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.LocalS5c

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open Submission.ASP

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **§5, main-term estimate with an *explicit* uniform constant.**  `abs_MainS_le` returns the
constant existentially at each scale `M`; here we feed in the single constant `CT` produced by
`abs_Tnu_le` (which is uniform in `ν, M, P`) and redo the summation verbatim, so that the very
same `CT` bounds `|MainS g lam Δ M P|` for *every* `M, P, Δ, B` satisfying the hypotheses. -/
private lemma abs_MainS_le_uniform {g : ℕ → ℝ} {CT : ℝ}
    (hCTpos : 0 < CT)
    (hT : ∀ ν M P : ℕ, Squarefree ν → 1 ≤ ν → ν ^ 4 ≤ M → 256 ≤ M → 2 ≤ P →
      (Real.log (M : ℝ)) ^ 6 ≤ (M : ℝ) ^ ((3 : ℝ) / 16) →
      |Tnu g M P ν| ≤ CT * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
        * (ν.divisors.card : ℝ) * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
        * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)))
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    {lam : ℕ → ℝ} {M P Δ : ℕ} {B : ℝ}
    (hP2 : 2 ≤ P) (hM256 : 256 ≤ M)
    (hlogM : (Real.log (M : ℝ)) ^ 6 ≤ (M : ℝ) ^ ((3 : ℝ) / 16))
    (hΔ4 : Δ ^ 4 ≤ M)
    (hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0)
    (hB : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        |lam ν| * g ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) ≤ B) :
    |MainS g lam Δ M P| ≤ CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * B := by
  have hM2 : 1 < M := by omega
  have hL6 : 0 ≤ (Real.log (M : ℝ)) ^ (-(6 : ℤ)) :=
    le_of_lt (zpow_pos (Real.log_pos (by exact_mod_cast hM2)) _)
  rw [mainS_eq hmul hlam_sq]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hpt : ∀ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
      |lam ν * g ν * Tnu g M P ν|
      ≤ CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
          * ((|lam ν| * g ν * (ν.divisors.card : ℝ)
              * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
            * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2))) := by
    intro ν hν
    rw [Finset.mem_filter] at hν
    obtain ⟨hνIcc, hνsq⟩ := hν
    have hν1 : 1 ≤ ν := (Finset.mem_Icc.mp hνIcc).1
    have hνΔ : ν ≤ Δ := (Finset.mem_Icc.mp hνIcc).2
    have hν4 : ν ^ 4 ≤ M := le_trans (Nat.pow_le_pow_left hνΔ 4) hΔ4
    have hgnn : 0 ≤ g ν := g_nonneg_of_squarefree hmul hg1 hp hνsq
    have hTb := hT ν M P hνsq hν1 hν4 hM256 hP2 hlogM
    have h1 : |lam ν| * g ν * |Tnu g M P ν|
        ≤ |lam ν| * g ν * (CT * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
            * (ν.divisors.card : ℝ) * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
            * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hTb (mul_nonneg (abs_nonneg _) hgnn)
    rw [abs_mul, abs_mul, abs_of_nonneg hgnn]
    refine le_trans h1 (le_of_eq ?_)
    ring
  calc ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, |lam ν * g ν * Tnu g M P ν|
      ≤ ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
            * ((|lam ν| * g ν * (ν.divisors.card : ℝ)
                * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
              * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2))) := Finset.sum_le_sum hpt
    _ = CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
          * (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
              (|lam ν| * g ν * (ν.divisors.card : ℝ)
                * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
              * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2))) := by
        rw [← Finset.mul_sum]
    _ ≤ CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * B :=
        mul_le_mul_of_nonneg_left hB (mul_nonneg hCTpos.le hL6)

theorem Tsum2_uniformAll {g : ℕ → ℝ}
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (a : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (lam : ℕ → ℝ) (N M P D Δ : ℕ) (A Rem B : ℝ),
        (hN : 2 ≤ N) → (hM1 : 1 ≤ M) → (hP1 : 1 ≤ P) → (hP2 : 2 ≤ P) →
        (hMN : M ≤ N) → (hPN : P ≤ N) → (hM256 : 256 ≤ M) →
        (hlogM : (Real.log (M : ℝ)) ^ 6 ≤ (M : ℝ) ^ ((3 : ℝ) / 16)) →
        (ha : ∀ n : ℕ, 0 ≤ a n) → (ha_sq : ∀ n : ℕ, ¬ Squarefree n → a n = 0) →
        (hA : A = Submission.ASP.Acount a (N : ℝ)) →
        (hAd : Submission.ASP.Approx a g r (N : ℝ)) →
        (hRem : ∀ m : ℕ, m ≤ N → Submission.ASP.RemainderSum r D m ≤ Rem) → (hRem0 : 0 ≤ Rem) →
        (hRem3 : Rem ≤ A * (Real.log (N : ℝ)) ^ (-(3 : ℤ))) →
        (hΔMP : Δ * M * P ≤ D) → (hΔ4 : Δ ^ 4 ≤ M) →
        (hΔsupp : ∀ ν : ℕ, Δ < ν → lam ν = 0) →
        (hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0) → (hlam_le : ∀ ν : ℕ, |lam ν| ≤ 1) →
        (hB : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
            |lam ν| * g ν * (ν.divisors.card : ℝ)
              * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
              * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) ≤ B) →
        |Submission.ASP.Tsum2 a lam (N : ℝ) (M : ℝ) (P : ℝ)|
          ≤ K * A * (B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) + (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
  -- The single, *uniform* constant supplied by `abs_Tnu_le` (it does not mention `M` or `P`).
  obtain ⟨CT, hCTpos, hT⟩ := abs_Tnu_le hgmul hg1 hp hbound h9
  have hgpn : ∀ p : ℕ, p.Prime → 0 ≤ g p := fun p hp' => (hp p hp').1
  refine ⟨max CT 2, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro a r lam N M P D Δ A Rem B
    hN hM1 hP1 hP2 hMN hPN hM256 hlogM
    ha ha_sq hA hAd hRem hRem0 hRem3 hΔMP hΔ4 hΔsupp hlam_sq hlam_le hB
  have hA0 : 0 ≤ A := by
    rw [hA, Acount, Nat.floor_natCast]
    exact Finset.sum_nonneg (fun n _ => ha n)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogMpos : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hL6 : 0 ≤ (Real.log (M : ℝ)) ^ (-(6 : ℤ)) := le_of_lt (zpow_pos hlogMpos _)
  have hL2 : 0 ≤ (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := le_of_lt (zpow_pos hlogNpos _)
  have hB0 : 0 ≤ B := by
    refine le_trans (Finset.sum_nonneg ?_) hB
    intro ν hν
    rw [Finset.mem_filter] at hν
    have hgnn : 0 ≤ g ν := g_nonneg_of_squarefree hgmul hg1 hgpn hν.2
    have hprod : 0 ≤ ∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) :=
      Finset.prod_nonneg (fun p _ => by positivity)
    have hlog : 0 ≤ 1 + Real.log ((ν : ℝ) * (P : ℝ) + 2) := by
      have h1 : (1 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hν.1).1
      have h2 : (0 : ℝ) ≤ (P : ℝ) := by positivity
      have h3 : (1 : ℝ) ≤ (ν : ℝ) * (P : ℝ) + 2 := by nlinarith
      have h4 : 0 ≤ Real.log ((ν : ℝ) * (P : ℝ) + 2) := Real.log_nonneg h3
      linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hgnn) (by positivity))
      hprod) hlog
  have hMain : |MainS g lam Δ M P| ≤ CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * B :=
    abs_MainS_le_uniform (g := g) (CT := CT) hCTpos hT hgmul hg1 hgpn
      (lam := lam) (M := M) (P := P) (Δ := Δ) (B := B) hP2 hM256 hlogM hΔ4 hlam_sq hB
  have hRemB := abs_RemS_le hN hM1 hP1 hMN hPN hA0 hRem hRem0 hRem3 hΔMP hlam_le hlam_sq
  have hAabs : |Acount a (N : ℝ)| = A := by rw [← hA]; exact abs_of_nonneg hA0
  rw [Tsum2_decomp hMN hPN hgmul ha_sq hAd hΔsupp]
  calc |Acount a (N : ℝ) * MainS g lam Δ M P + RemS r lam Δ M P N|
      ≤ |Acount a (N : ℝ) * MainS g lam Δ M P| + |RemS r lam Δ M P N| := abs_add_le _ _
    _ = A * |MainS g lam Δ M P| + |RemS r lam Δ M P N| := by rw [abs_mul, hAabs]
    _ ≤ A * (CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * B)
          + 2 * A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hMain hA0) hRemB
    _ ≤ max CT 2 * A
          * (B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) + (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
        have h3 : CT ≤ max CT 2 := le_max_left _ _
        have h4 : (2 : ℝ) ≤ max CT 2 := le_max_right _ _
        have h5 : 0 ≤ max CT 2 := le_trans hCTpos.le h3
        calc A * (CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * B)
              + 2 * A * (Real.log (N : ℝ)) ^ (-(2 : ℤ))
            = CT * (A * (B * (Real.log (M : ℝ)) ^ (-(6 : ℤ))))
              + 2 * (A * (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
              ring
          _ ≤ max CT 2 * (A * (B * (Real.log (M : ℝ)) ^ (-(6 : ℤ))))
                + max CT 2 * (A * (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right h3 (mul_nonneg hA0 (mul_nonneg hB0 hL6))
              · exact mul_le_mul_of_nonneg_right h4 (mul_nonneg hA0 hL2)
          _ = max CT 2 * A
                * (B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) + (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
              ring

end

end Work.FIChain
