/-
  Companion paper, §9: the two global constants of the `ã`-sequence.

    * `Htil` = the (1.14)-constant of the density `g̃` of `ã`, i.e.
      `Htil = ∏_p (1 − g̃(p))/(1 − 1/p) = lim ∑_{d} μ(d)g̃(d)log d`;
    * the identity (9.13) `Htil · G = H` where `G = ∏_p (1 − g(p²))` is the companion's (9.8)
      and `H = ∏_p (1 − g(p))/(1 − 1/p)` is the (1.14)-constant of `g`, which for the
      Friedlander–Iwaniec density is `4/π`.

  `H = 4/π` is the paper's (4.8): `g(p)p = 1 + χ₄(p)(1 − 1/p)`, hence
  `(1 − g(p))/(1 − 1/p) = 1 − χ₄(p)/p` and the product is `1/L(1,χ₄) = 4/π`.  The commons
  already contains the product form (`tendsto_prod_one_sub_X2Y4_density`), so here we only
  identify the limit.
-/
import Mathlib
import Submission.ASP.S27
import Submission.ASP.S9k
import Submission.Commons.NumberTheory.Sieve.sum_mu_mul_density_mul_log_tendsto
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tendsto_prod_one_sub_X2Y4_density
import Submission.Commons.NumberTheory.EulerProduct.tendsto_prod_ratio_mul_eq
import Submission.Commons.Analysis.Asymptotics.prime_sum_loglog_real_form
import Submission.Commons.NumberTheory.EulerProduct.tendsto_prod_primesBelow_one_sub_sq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Submission.ASP

open Finset Filter

noncomputable section

/-! ### `H = 4/π` for the Friedlander–Iwaniec density -/

/-- (1.9) for `FIg` with the error in the `zpow` form used by the commons' density lemmas. -/
lemma FI_gdens_prime_sum_ten :
    ∃ c C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, FIg p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ)) := by
  obtain ⟨c, hc⟩ := FI_gdens_prime_sum
  obtain ⟨C, hC, hsum⟩ := hc 10 (by norm_num)
  refine ⟨c, C, hC, fun y hy => ?_⟩
  refine le_trans (hsum y hy) ?_
  have hpos : 0 < Real.log y := Real.log_pos (by linarith)
  have h : (Real.log y) ^ (-(10 : ℤ)) = ((Real.log y) ^ (10 : ℕ))⁻¹ := by
    rw [zpow_neg]; norm_num
  have h2 : (Real.log y) ^ (10 : ℝ) = (Real.log y) ^ (10 : ℕ) := Real.rpow_natCast _ 10
  rw [h, h2, div_eq_mul_inv]

/-- The value of `FIg` at a prime, in the `ZMod` form used by the commons' Euler products. -/
lemma FIg_prime_eq (p : ℕ) :
    FIg p = (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / (p : ℝ) ^ 2 := by
  rw [FIg, Submission.gdens, Submission.N]
  norm_num

/-- **(1.14) for the Friedlander–Iwaniec density**, product form: `H = 4/π`. -/
theorem FI_H_prod_tendsto :
    Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - FIg p) / (1 - 1 / (p : ℝ)))
      Filter.atTop (nhds (4 / Real.pi)) := by
  have hprod : Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
      (1 - (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / (p : ℝ) ^ 2)
        / (1 - 1 / (p : ℝ))) Filter.atTop (nhds (4 / Real.pi)) :=
    Commons.NumberTheory.FriedlanderIwaniec.tendsto_prod_one_sub_X2Y4_density
  have hcongr : (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - FIg p) / (1 - 1 / (p : ℝ)))
      = (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
          (1 - (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / (p : ℝ) ^ 2)
            / (1 - 1 / (p : ℝ))) := by
    funext N
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [FIg_prime_eq p]
  rw [hcongr]
  exact hprod

/-- **(1.14) for the Friedlander–Iwaniec density**: `∑_{d ≤ N} μ(d)g(d)log d → −4/π`. -/
theorem FI_H_eq_four_pi :
    Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) * FIg d * Real.log d) Filter.atTop
      (nhds (-(4 / Real.pi))) := by
  obtain ⟨H, _hHpos, hsum, hprod⟩ :=
    Commons.NumberTheory.Sieve.sum_mu_mul_density_mul_log_tendsto (fun m n hmn => FI_gdens_mul hmn)
      FI_gdens_one (fun p hp => FI_gdens_prime_nonneg hp)
      (by obtain ⟨C, hC, h⟩ := FI_gdens_bound; exact ⟨C, h⟩)
      (by obtain ⟨c, C, -, h⟩ := FI_gdens_prime_sum_ten; exact ⟨c, C, h⟩)
  have hH : H = 4 / Real.pi := tendsto_nhds_unique hprod FI_H_prod_tendsto
  rw [hH] at hsum
  exact hsum

/-! ### The constant `G = ∏_p (1 − g(p²))` as a limit -/

/-- `G = Gprod FIg` is the limit of the finite products `∏_{p < N} (1 − FIg(p²))`. -/
theorem Gprod_FIg_tendsto :
    Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - FIg (p ^ 2)))
      Filter.atTop (nhds (Gprod FIg)) := by
  refine Commons.NumberTheory.EulerProduct.tendsto_prod_primesBelow_one_sub_sq
    (C := 4) (by norm_num) (fun p hp => ?_)
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := pow_pos (by exact_mod_cast hp.pos) 2
  rw [abs_of_nonneg (FIg_nonneg _), le_div_iff₀ hp2]
  exact (FI_gdens_prime_sq_le p hp).2


/-! ### (1.9) for the density `g̃`, in the real form -/

/-- **(1.9) for `g̃`**, in the `ℝ`-indexed form required by the companion's estimates. -/
theorem FIgtil_sum_19_real :
    ∃ c C : ℝ, 0 < C ∧ ∀ z : ℝ, 2 ≤ z →
      |(∑ p ∈ (Finset.Icc 2 ⌊z⌋₊).filter Nat.Prime, FIgtil p)
          - Real.log (Real.log z) - c|
        ≤ C * (Real.log z) ^ (-(10 : ℤ)) := by
  obtain ⟨c, C, h⟩ := FIgtil_sum_19_nat
  have hCnn : 0 ≤ C := by
    by_contra hlt
    simp only [not_le] at hlt
    have h2 := h 2 (by norm_num)
    have hpos : (0 : ℝ) < (Real.log (2 : ℝ)) ^ (-(10 : ℝ)) + 1 / (2 : ℝ) := by
      have h2 : (0:ℝ) < Real.log (2:ℝ) := Real.log_pos (by norm_num)
      have := Real.rpow_pos_of_pos h2 (-(10 : ℝ))
      positivity
    have : C * ((Real.log (2 : ℝ)) ^ (-(10 : ℝ)) + 1 / (2 : ℝ)) < 0 :=
      mul_neg_of_neg_of_pos hlt hpos
    have := abs_nonneg ((∑ p ∈ (Finset.Icc 1 2).filter Nat.Prime, FIgtil p)
      - Real.log (Real.log (2 : ℝ)) - c)
    linarith
  exact Commons.Analysis.Asymptotics.prime_sum_loglog_real_form hCnn h

/-! ### The constant `Htil` of the density `g̃` -/

/-- **(1.14) for the density `g̃` of `ã`**: there is `Htil > 0` with
`∑_{d ≤ N} μ(d)g̃(d)log d → −Htil` and `∏_{p < N}(1 − g̃(p))/(1 − 1/p) → Htil`. -/
theorem FIgtil_H_exists :
    ∃ Htil : ℝ, 0 < Htil ∧
      Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * FIgtil d * Real.log d) Filter.atTop
          (nhds (-Htil)) ∧
      Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
          (1 - FIgtil p) / (1 - 1 / (p : ℝ))) Filter.atTop (nhds Htil) :=
  Commons.NumberTheory.Sieve.sum_mu_mul_density_mul_log_tendsto (fun m n hmn => FIgtil_mul hmn) FIgtil_one
    (fun p hp => ⟨FIgtil_nonneg p, FIgtil_lt_one hp⟩)
    (by obtain ⟨C, hC, h⟩ := FIgtil_bound; exact ⟨C, h⟩)
    (by obtain ⟨c, C, -, h⟩ := FIgtil_sum_19_real; exact ⟨c, C, h⟩)

/-- **Companion §9, (9.13)**: `Htil · G = H = 4/π`, where `G = ∏_p (1 − g(p²))`. -/
theorem FIgtil_H_mul_Gprod {Htil : ℝ}
    (hHtil : Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
        (1 - FIgtil p) / (1 - 1 / (p : ℝ))) Filter.atTop (nhds Htil)) :
    Htil * Gprod FIg = 4 / Real.pi :=
  Commons.NumberTheory.EulerProduct.tendsto_prod_ratio_mul_eq hHtil Gprod_FIg_tendsto
    FI_H_prod_tendsto (fun p hp => by
      rw [FIgtil_prime hp, gtilVal]
      have h1 : (1 : ℝ) - FIg (p ^ 2) ≠ 0 := by
        have := FIg_prime_sq_le_half hp; linarith
      have h2 : (1 : ℝ) - 1 / (p : ℝ) ≠ 0 := by
        have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
        have hlt : 1 / (p : ℝ) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
        linarith
      field_simp
      ring)

end

end Submission.ASP
