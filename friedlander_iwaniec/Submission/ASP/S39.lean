/-
  Companion paper, §9 / §2: the `(2.1)`–`(2.2)`-type estimates for the squarefree-supported
  sequence `ã = atil FIa` with the density `g̃ = FIgtil`.

  * `sum_tau_pow_AtilAd_le` — **(2.1) for `ã`**:
    `∑_{d ≤ D} τ(d)^{20/3}Ã_d(m) ≪ A(x)(log x)^B` (for `D ≤ m`);
  * `sum_sqfree_tau_pow_FIgtil_le` — **(2.2) for `g̃`**: `∑♭_{d ≤ y} τ(d)^{20/3}g̃(d) ≪ (log y)^K`.

  Together with the pointwise identity `r̃_d = Ã_d − g̃(d)Ã` of `S9g` they give the
  `τ^{20/3}`-weighted `(2.3)` for `ã`, hence (by Hölder against the `τ⁰`-weighted `(R)` of `S38`)
  the companion's `(R′)` for `ã`.
-/
import Mathlib
import Submission.ASP.S38
import Submission.ASP.S26
import Submission.ASP.S25
import Submission.ASP.S34
import Submission.ASP.S24
import Submission.ASP.S9g
import Submission.ASP.S30
import Submission.ASP.S2b
import Submission.Commons.NumberTheory.Sieve.sum_squarefree_tau_pow_mul_gdens_le

set_option maxHeartbeats 1600000

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- `a^{40}` as an `rpow` equals `a^{40}` as a natural power. -/
lemma rpow_forty_eq_pow (a : ℝ) : a ^ (40 : ℝ) = a ^ (40 : ℕ) := by
  rw [show (40 : ℝ) = ((40 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `0 ≤ Ã_d(m)`. -/
lemma AtilAd_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (d m : ℕ) : 0 ≤ AtilAd a d m := by
  rw [AtilAd, Ad, Nat.floor_natCast]
  exact Finset.sum_nonneg (fun n _ => atil_nonneg ha n)

/-- **(2.1) for `ã`**: `∑_{d ≤ D} τ(d)^{20/3}·Ã_d(m) ≪ A(x)(log x)^B` (for `D ≤ m`). -/
theorem sum_tau_pow_AtilAd_le :
    ∃ C B X₀ : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ m : ℕ, 2 ≤ m → m ≤ x → ∀ D : ℕ, D ≤ m →
      (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d m)
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log x) ^ B := by
  obtain ⟨Cc, Bc, Xc, hCc, hcube⟩ := cube_range_Ad_le
  refine ⟨Cc, Bc, max Xc 2, hCc, fun x hx m hm2 hmx D hD => ?_⟩
  have hxC : Xc ≤ (x : ℝ) := le_trans (le_max_left _ _) hx
  -- Step 1a: `Ã_d ≤ A_d`
  have hstep1a : (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d m)
      ≤ ∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * Ad FIa d (m : ℝ) :=
    Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left
      (Ad_atil_le FIa FIa_nonneg d (m : ℝ)) (by positivity))
  -- Step 1b: extend the `d`-range to `Icc 1 m`
  have hstep1b : (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * Ad FIa d (m : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 m,
          ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * Ad FIa d (m : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun d hd => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
        le_trans (Finset.mem_Icc.mp hd).2 hD⟩)
      (fun i _ _ => mul_nonneg (by positivity) (Finset.sum_nonneg (fun n _ => FIa_nonneg n)))
  -- Step 2: the divisor swap
  have hstep2 : (∑ d ∈ Finset.Icc 1 m,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * Ad FIa d (m : ℝ))
      ≤ ∑ n ∈ Finset.Icc 1 m, ((n.divisors.card : ℝ)) ^ (8 : ℕ) * FIa n := by
    have h1 : ∀ d : ℕ, ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * Ad FIa d (m : ℝ)
        = ∑ n ∈ (Finset.Icc 1 m).filter (fun n => d ∣ n),
            ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * FIa n := by
      intro d
      rw [Ad, Nat.floor_natCast, Finset.mul_sum]
    simp only [h1]
    rw [sum_dvd_swap]
    refine Finset.sum_le_sum (fun n hn => ?_)
    have h2 : (∑ d ∈ n.divisors, ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * FIa n)
        = (∑ d ∈ n.divisors, ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3)) * FIa n :=
      (Finset.sum_mul _ _ _).symm
    rw [h2]
    exact mul_le_mul_of_nonneg_right (sum_divisors_tau_pow_le n) (FIa_nonneg n)
  -- Step 3: the cube reduction
  have hstep3 : (∑ n ∈ Finset.Icc 1 m, ((n.divisors.card : ℝ)) ^ (8 : ℕ) * FIa n)
      ≤ ∑ d ∈ (Finset.Icc 1 m).filter (fun d => d ^ 3 ≤ m),
          (2 * (d.divisors.card : ℝ)) ^ (40 : ℝ) * (Submission.Ad d m : ℝ) := by
    simp only [rpow_forty_eq_pow]
    refine le_trans (le_of_eq ?_) (sum_FIa_tau_pow_eight_le m)
    exact Finset.sum_congr rfl (fun n _ => by ring)
  -- Step 4: the aggregate bound
  have hstep4 : (∑ d ∈ (Finset.Icc 1 m).filter (fun d => d ^ 3 ≤ m),
        (2 * (d.divisors.card : ℝ)) ^ (40 : ℝ) * (Submission.Ad d m : ℝ))
      ≤ Cc * (Submission.Aseq x : ℝ) * (Real.log x) ^ Bc := hcube x hxC m hm2 hmx
  exact le_trans (le_trans (le_trans hstep1a hstep1b) hstep2) (le_trans hstep3 hstep4)

/-- **(2.2) for `g̃`**: `∑♭_{d ≤ y} τ(d)^{20/3}·g̃(d) ≪ (log y)^K`. -/
theorem sum_sqfree_tau_pow_FIgtil_le :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ y : ℕ, 2 ≤ y →
      (∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * FIgtil d)
        ≤ C * (Real.log y) ^ K := by
  obtain ⟨C, hC, K, hK, h⟩ := Commons.NumberTheory.Sieve.sum_squarefree_tau_pow_mul_gdens_le
    (g := FIgtil) (fun p _ => FIgtil_nonneg p) (fun m n hmn => FIgtil_mul hmn) FIgtil_bound
  exact ⟨C, K, hC, hK, h⟩


/-- **(2.3) for `ã`**: the `τ^{20/3}`-weighted remainder bound. -/
theorem Atil_tau_pow_remainder_le :
    ∃ C B X₀ : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ m : ℕ, 2 ≤ m → m ≤ x → ∀ D : ℕ, D ≤ m →
      (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * |rtildeFull FIr FIg FIgtil FIa d m|)
        ≤ C * ((Submission.Aseq x : ℝ) + Acount (atil FIa) (x : ℝ)) * (Real.log x) ^ B := by
  obtain ⟨C1, B1, X1, hC1, h1⟩ := sum_tau_pow_AtilAd_le
  obtain ⟨C2, K2, hC2, hK2, h2⟩ := sum_sqfree_tau_pow_FIgtil_le
  refine ⟨C1 + C2, max B1 K2, max (max X1 2) 3, by positivity, fun x hx m hm2 hmx D hD => ?_⟩
  have hx1 : X1 ≤ (x : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : (3 : ℝ) ≤ (x : ℝ) := by
    have h : ((3 : ℕ) : ℝ) ≤ (x : ℝ) := le_trans (le_max_right _ _) hx
    simpa using h
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have h3 : (3 : ℝ) ≤ (x : ℝ) := hx3
    have he : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlognn : (0 : ℝ) ≤ Real.log x := le_trans zero_le_one hlog1
  have hAx : (0 : ℝ) ≤ Acount (atil FIa) (x : ℝ) :=
    Finset.sum_nonneg (fun n _ => atil_nonneg FIa_nonneg n)
  have hAmono : Acount (atil FIa) (m : ℝ) ≤ Acount (atil FIa) (x : ℝ) := by
    rw [Acount, Acount]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => atil_nonneg FIa_nonneg i)
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      le_trans (Finset.mem_Icc.mp hn).2 (Nat.floor_mono (by exact_mod_cast hmx))⟩
  have hpt : ∀ d : ℕ, rtildeFull FIr FIg FIgtil FIa d m
      = AtilAd FIa d m - FIgtil d * Acount (atil FIa) (m : ℝ) := by
    intro d
    have h := approx_atil FIa FIg FIr FIgtil (m : ℝ) (FI_approx (m : ℝ)) d m
    rw [AtilAd]
    linarith [h]
  have hbound : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * |rtildeFull FIr FIg FIgtil FIa d m|)
      ≤ (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d m)
        + Acount (atil FIa) (m : ℝ) * (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * FIgtil d) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun d _ => ?_)
    rw [hpt d]
    have h1' : (0 : ℝ) ≤ ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) := by positivity
    have h2' : FIgtil d * Acount (atil FIa) (m : ℝ) ≤ FIgtil d * Acount (atil FIa) (x : ℝ) :=
      mul_le_mul_of_nonneg_left hAmono (FIgtil_nonneg d)
    have hAm : (0 : ℝ) ≤ Acount (atil FIa) (m : ℝ) :=
      Finset.sum_nonneg (fun n _ => atil_nonneg FIa_nonneg n)
    calc ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3)
          * |AtilAd FIa d m - FIgtil d * Acount (atil FIa) (m : ℝ)|
        ≤ ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3)
            * (AtilAd FIa d m + FIgtil d * Acount (atil FIa) (m : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ h1'
          rw [abs_sub_le_iff]
          constructor
          · linarith [AtilAd_nonneg FIa FIa_nonneg d m,
              mul_nonneg (FIgtil_nonneg d) hAm]
          · linarith [AtilAd_nonneg FIa FIa_nonneg d m,
              mul_nonneg (FIgtil_nonneg d) hAm]
      _ ≤ ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d m
            + ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * (FIgtil d * Acount (atil FIa) (m : ℝ)) :=
          le_of_eq (by ring)
      _ = ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d m
            + Acount (atil FIa) (m : ℝ) * (((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * FIgtil d) := by
          ring
  refine le_trans hbound ?_
  have hDm : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d m)
      ≤ ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => mul_nonneg (by positivity) (AtilAd_nonneg FIa FIa_nonneg i m))
  have hD22 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * FIgtil d)
      ≤ C2 * (Real.log x) ^ K2 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun i _ _ => mul_nonneg (by positivity) (FIgtil_nonneg i))) (h2 x (by omega))
    intro d hd
    rw [Finset.mem_filter] at hd ⊢
    exact ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd.1).1,
      le_trans (Finset.mem_Icc.mp hd.1).2 (le_trans hD hmx)⟩, hd.2⟩
  have h1' := h1 x hx1 m hm2 hmx D hD
  have hlogB1 : (Real.log x) ^ B1 ≤ (Real.log x) ^ (max B1 K2) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (le_max_left _ _)
  have hlogK2 : (Real.log x) ^ K2 ≤ (Real.log x) ^ (max B1 K2) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (le_max_right _ _)
  have hpos : (0 : ℝ) ≤ (Real.log x) ^ (max B1 K2) := Real.rpow_nonneg hlognn _
  have hfin : C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B1
        + Acount (atil FIa) (x : ℝ) * (C2 * (Real.log x) ^ K2)
      ≤ (C1 + C2) * ((Submission.Aseq x : ℝ) + Acount (atil FIa) (x : ℝ))
          * (Real.log x) ^ (max B1 K2) := by
    have hA : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := by
      have h0 : (0 : ℝ) ≤ Acount FIa (x : ℝ) := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
      rw [FI_Acount_eq] at h0
      linarith
    have h1a : C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B1
        ≤ C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (max B1 K2) :=
      mul_le_mul_of_nonneg_left hlogB1 (mul_nonneg (le_of_lt hC1) hA)
    have h2a : Acount (atil FIa) (x : ℝ) * (C2 * (Real.log x) ^ K2)
        ≤ Acount (atil FIa) (x : ℝ) * (C2 * (Real.log x) ^ (max B1 K2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogK2 (le_of_lt hC2)) hAx
    have hcomb : C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (max B1 K2)
          + Acount (atil FIa) (x : ℝ) * (C2 * (Real.log x) ^ (max B1 K2))
        = (C1 * (Submission.Aseq x : ℝ) + C2 * Acount (atil FIa) (x : ℝ))
            * (Real.log x) ^ (max B1 K2) := by ring
    refine le_trans (add_le_add h1a h2a) ?_
    rw [hcomb]
    refine mul_le_mul_of_nonneg_right ?_ hpos
    nlinarith [hA, hAx, hC1, hC2]
  calc (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d m)
        + Acount (atil FIa) (m : ℝ) * (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * FIgtil d)
      ≤ C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B1
        + Acount (atil FIa) (x : ℝ) * (C2 * (Real.log x) ^ K2) := by
        refine add_le_add (le_trans hDm h1') ?_
        exact mul_le_mul hAmono hD22
          (Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (FIgtil_nonneg i))) hAx
    _ ≤ (C1 + C2) * ((Submission.Aseq x : ℝ) + Acount (atil FIa) (x : ℝ))
          * (Real.log x) ^ (max B1 K2) := hfin

end

end Submission.ASP
