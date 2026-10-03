/-
# `Submission.Work.FIChain.RhoTailWeightLe` — the pointwise Rankin weight inequality of the
`ρ`-window tail

The companion's §10 writes the inner variable of the `ρ`-window as `n = n₀n₁` with `n₁ | Π(Pz)` and
`(n₀, Π) = 1`.  The part with `n₁ > Δπ` is estimated by Rankin's trick; the *weight* that has to be
absorbed by the Rankin saving `D^{-ε}`, `ε = log 2 / log Pz`, is `τ(c)²·τ(n₁)·τ(n)·ã(cn₁n)` against
`τ(cn₁n)³·ã(cn₁n)`.  This file proves the corresponding pointwise inequality

    τ(c)² · τ(n₁) · τ(n) · ã(c·n₁·n) ≤ D^{-ε} · τ(c·n₁·n)³ · ã(c·n₁·n)     (ε = log 2 / log Pz)

for `n₁ | Π(Pz)` and `D < n₁`, `D ≥ 1` — the form consumed by the `n₁ > Δπ` tail
(`Submission.Work.FIChain.bprime_window_tail_le` and the `ρ`-window tail).

**Proof.**  Write `m = c·n₁·n`.
* If `ã(m) = 0` both sides vanish.
* Otherwise `μ(m)² ≠ 0`, so `m` is **squarefree** (`Submission.ASP.atil_zero_of_not_squarefree`);
  hence `c`, `n₁`, `n` are pairwise coprime and `Nat.Coprime.card_divisors_mul` gives
  `τ(m) = τ(c)·τ(n₁)·τ(n)`.  So it is enough to show `τ(c)²τ(n₁)τ(n) ≤ D^{-ε}·(τ(c)τ(n₁)τ(n))³`,
  i.e. `D^ε ≤ τ(c)·τ(n₁)²·τ(n)²`, for which `D^ε ≤ τ(n₁)` suffices.
* `D^ε ≤ τ(n₁)`: since `n₁ | Π(Pz) = ∏_{p ≤ Pz} p`, every prime factor of `n₁` is `≤ Pz`
  (`Nat.Prime.dvd_primorial_iff`) and `n₁` is squarefree, so `n₁ = ∏_{p | n₁} p ≤ Pz^{ω(n₁)}`
  (`Work.FIChain.le_pow_card_primeFactors_of_dvd_primorial`).  With `D < n₁` this gives
  `D < Pz^{ω(n₁)}`, hence `log D < ω(n₁)·log Pz`, hence
  `ε·log D < ω(n₁)·log 2`, i.e. `D^ε < 2^{ω(n₁)}`
  (`Work.FIChain.rpow_log_div_log_le_two_pow`).  Finally `2^{ω(n)} ≤ τ(n)`
  (`Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors`).
* The remaining rearrangement of the three real weights is
  `Work.FIChain.rpow_weight_triple_le`: for `P, Q, R ≥ 1` and `D^ε ≤ Q`,
  `P²QR ≤ D^{-ε}(PQR)³` (from `D^{-ε} ≥ Q^{-1}`, `Q^{-1}(PQR)³ = P³Q²R³ ≥ P²QR`).
-/
import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
import Submission.Work.FIChain.le_pow_card_primeFactors_of_dvd_primorial
import Submission.Work.FIChain.rpow_log_div_log_le_two_pow
import Submission.Work.FIChain.rpow_weight_triple_le

namespace Work.FIChain

theorem RhoTailWeightLe (Pz D c n₁ n : ℕ) (hPz : 2 ≤ Pz) (hD : 1 ≤ D)
    (hdvd : n₁ ∣ Work.FIChain.ProdP Pz) (hDn : D < n₁) (hc : 1 ≤ c) (hn : 1 ≤ n) :
    ((c.divisors.card : ℝ)) ^ 2 * ((n₁.divisors.card : ℝ)) * ((n.divisors.card : ℝ))
        * Work.FIChain.atilc (c * n₁ * n)
      ≤ ((D : ℝ)) ^ (-(Real.log 2 / Real.log (Pz : ℝ)))
          * (((c * n₁ * n).divisors.card : ℝ)) ^ 3 * Work.FIChain.atilc (c * n₁ * n) := by
  -- `ã` vanishes unless the argument is squarefree
  by_cases h0 : Work.FIChain.atilc (c * n₁ * n) = 0
  · simp [h0]
  · have hsq : Squarefree (c * n₁ * n) := by
      by_contra hns
      exact h0 (Submission.ASP.atil_zero_of_not_squarefree hns)
    -- squarefreeness of the product splits it into pairwise coprime factors
    have hsq_cn : Squarefree (c * n₁) := (Nat.squarefree_mul_iff.mp hsq).2.1
    have hcop_outer : Nat.Coprime (c * n₁) n := (Nat.squarefree_mul_iff.mp hsq).1
    have hcop_cn₁ : Nat.Coprime c n₁ := (Nat.squarefree_mul_iff.mp hsq_cn).1
    -- `τ` is multiplicative over the coprime factors
    have hcard : (c * n₁ * n).divisors.card
        = c.divisors.card * n₁.divisors.card * n.divisors.card := by
      rw [Nat.Coprime.card_divisors_mul hcop_outer, Nat.Coprime.card_divisors_mul hcop_cn₁]
    have hcardR : (((c * n₁ * n).divisors.card : ℕ) : ℝ)
        = (c.divisors.card : ℝ) * (n₁.divisors.card : ℝ) * (n.divisors.card : ℝ) := by
      rw [hcard]; push_cast; ring
    -- the three divisor counts are `≥ 1`
    have hP1 : (1 : ℝ) ≤ (c.divisors.card : ℝ) := by
      have : (0 : ℕ) < c.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
      exact_mod_cast this
    have hQ1 : (1 : ℝ) ≤ (n₁.divisors.card : ℝ) := by
      have : (0 : ℕ) < n₁.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
      exact_mod_cast this
    have hR1 : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
      have : (0 : ℕ) < n.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
      exact_mod_cast this
    -- the Rankin saving `D^ε ≤ τ(n₁)`, `ε = log 2 / log Pz`
    have hDε : (D : ℝ) ^ (Real.log 2 / Real.log (Pz : ℝ)) ≤ (n₁.divisors.card : ℝ) := by
      have hle : n₁ ≤ Pz ^ n₁.primeFactors.card :=
        le_pow_card_primeFactors_of_dvd_primorial hPz (by simpa [Work.FIChain.ProdP] using hdvd)
      have hDlt : D < Pz ^ n₁.primeFactors.card := lt_of_lt_of_le hDn hle
      have hpow : (D : ℝ) ^ (Real.log 2 / Real.log (Pz : ℝ)) ≤ (2 : ℝ) ^ n₁.primeFactors.card :=
        rpow_log_div_log_le_two_pow hPz hD hDlt
      have hτ : (2 : ℝ) ^ n₁.primeFactors.card ≤ (n₁.divisors.card : ℝ) := by
        have hn₁ : 0 < n₁ := by omega
        exact_mod_cast
          Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors hn₁
      linarith
    -- the pure real rearrangement, then multiply by `ã(m) ≥ 0`
    have hw := rpow_weight_triple_le (P := (c.divisors.card : ℝ)) (Q := (n₁.divisors.card : ℝ))
      (R := (n.divisors.card : ℝ)) (D := (D : ℝ)) (ε := Real.log 2 / Real.log (Pz : ℝ))
      (by exact_mod_cast hD) hP1 hQ1 hR1 hDε
    have hatil : 0 ≤ Work.FIChain.atilc (c * n₁ * n) := Work.FITop.atilFIa_nonneg _
    have hfin := mul_le_mul_of_nonneg_right hw hatil
    rw [hcardR]
    exact hfin

end Work.FIChain
