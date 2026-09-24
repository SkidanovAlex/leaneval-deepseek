import Mathlib
import Submission.Work.GM.HB.hb_defs

namespace Work.GM.HB

open Finset

/-- In the regime `Δ < 100 N`, the honest van der Corput dual range is contained in `[1,31]`:
for an annulus pair `Δ ≤ |θ| ≤ 2Δ` one has `⌊|θ|/(2πN)⌋ ≤ 31`, and all the terms of the dual
sum have modulus `≤ 1`. -/
lemma hbm_dual_small {N : ℕ} (hN : 1 ≤ N) {Δ θ : ℝ} (hΔ1 : 1 ≤ Δ)
    (hΔN : Δ < 100 * (N : ℝ)) (hθ : Δ ≤ |θ|) (hθ2 : |θ| ≤ 2 * Δ) :
    ‖hbm (Nat.ceil (|θ| / (4 * Real.pi * (N : ℝ))))
         (Nat.floor (|θ| / (2 * Real.pi * (N : ℝ)))) θ‖ ≤ 31 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hθabs : 0 < |θ| := by linarith
  have ha1 : 1 ≤ Nat.ceil (|θ| / (4 * Real.pi * (N : ℝ))) :=
    Nat.ceil_pos.mpr (div_pos hθabs (by positivity))
  have hx0 : (0 : ℝ) ≤ |θ| / (2 * Real.pi * (N : ℝ)) := by positivity
  have hx : |θ| / (2 * Real.pi * (N : ℝ)) < 32 := by
    have h1' : |θ| / (2 * Real.pi * (N : ℝ)) ≤ (2 * Δ) / (2 * Real.pi * (N : ℝ)) :=
      div_le_div_of_nonneg_right hθ2 (by positivity)
    have h2' : (2 * Δ) / (2 * Real.pi * (N : ℝ)) = Δ / (Real.pi * (N : ℝ)) := by field_simp
    have h3 : Δ / (Real.pi * (N : ℝ)) < (100 * (N : ℝ)) / (Real.pi * (N : ℝ)) := by
      apply div_lt_div_of_pos_right hΔN; positivity
    have h4 : (100 * (N : ℝ)) / (Real.pi * (N : ℝ)) = 100 / Real.pi := by field_simp
    rw [h2'] at h1'; rw [h4] at h3
    have h5 : (100 : ℝ) / Real.pi < 32 := by
      rw [div_lt_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_d20]
    linarith
  have hb : Nat.floor (|θ| / (2 * Real.pi * (N : ℝ))) ≤ 31 := by
    have h : Nat.floor (|θ| / (2 * Real.pi * (N : ℝ))) < 32 := (Nat.floor_lt hx0).mpr hx
    omega
  have hcard : (Finset.Icc (Nat.ceil (|θ| / (4 * Real.pi * (N : ℝ))))
      (Nat.floor (|θ| / (2 * Real.pi * (N : ℝ))))).card ≤ 31 := by
    rw [Nat.card_Icc]; omega
  calc ‖hbm (Nat.ceil (|θ| / (4 * Real.pi * (N : ℝ))))
         (Nat.floor (|θ| / (2 * Real.pi * (N : ℝ)))) θ‖
      ≤ ∑ n ∈ Finset.Icc (Nat.ceil (|θ| / (4 * Real.pi * (N : ℝ))))
            (Nat.floor (|θ| / (2 * Real.pi * (N : ℝ)))), (Real.sqrt (n : ℝ))⁻¹ :=
        hbm_abs_le_sum _ _ ha1 θ
    _ ≤ ∑ n ∈ Finset.Icc (Nat.ceil (|θ| / (4 * Real.pi * (N : ℝ))))
            (Nat.floor (|θ| / (2 * Real.pi * (N : ℝ)))), (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        simp only [Finset.mem_Icc] at hn
        have hn1 : 1 ≤ n := le_trans ha1 hn.1
        have hsq : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
          rw [show (1 : ℝ) = Real.sqrt 1 by simp]
          exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
        exact inv_le_one_of_one_le₀ hsq
    _ = ((Finset.Icc (Nat.ceil (|θ| / (4 * Real.pi * (N : ℝ))))
            (Nat.floor (|θ| / (2 * Real.pi * (N : ℝ))))).card : ℝ) := by simp
    _ ≤ 31 := by exact_mod_cast hcard

/-- **Kerr's `lem:main1`, regime `Δ < 100N`** (the easy regime: the honest dual range is contained in `[1,31]`, so the pointwise van der Corput transform `Commons.NumberTheory.DirichletPolynomial.pointwise_reflection_vdc` plus `‖hbm a b θ‖ ≤ 31` closes the bound, with `Δ^ε ≥ 1`). -/
theorem kerr_main1_small : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → (N : ℝ) ≤ Δ → Δ < 100 * (N : ℝ) →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      Work.GM.HB.annSum N Δ R t ≤ K * Δ ^ ε * Work.GM.HB.pcount (2 * Δ) R t := by
  intro ε hε
  obtain ⟨Cv, hCv, hvdc⟩ := Commons.NumberTheory.DirichletPolynomial.pointwise_reflection_vdc
  obtain ⟨Cl, hCl, hlog⟩ := log_pow_four_le_rpow hε
  refine ⟨Cv * Cl * 962, by positivity, ?_⟩
  intro N hN Δ hΔ1 hNΔ hΔN R t ht
  have hΔnn : (0 : ℝ) ≤ Δ := by linarith
  have hlogb : (1 + Real.log (2 + 2 * Δ)) ^ 4 ≤ Cl * Δ ^ ε := hlog Δ hΔ1
  have hdual : ∀ θ : ℝ, Δ ≤ |θ| → |θ| ≤ 2 * Δ →
      ‖hbm (Nat.ceil (|θ| / (4 * Real.pi * (N : ℝ))))
           (Nat.floor (|θ| / (2 * Real.pi * (N : ℝ)))) θ‖ ≤ 31 :=
    fun θ h1 h2 => hbm_dual_small hN hΔ1 hΔN h1 h2
  have hpair : ∀ i j : Fin R,
      (if Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ then ‖hbm N (2 * N) (t i - t j)‖ ^ 2 else 0)
        ≤ ((Cv * Cl * 962) * Δ ^ ε) * (if |t i - t j| ≤ 2 * Δ then (1 : ℝ) else 0) := by
    intro i j
    by_cases hc : Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ
    · rw [if_pos hc, if_pos hc.2]
      have hA := hbm_per_pair hCv hvdc hN hΔ1 hNΔ hc.1 hc.2
      have hB := hdual (t i - t j) hc.1 hc.2
      have hB2 : ‖hbm (Nat.ceil (|t i - t j| / (4 * Real.pi * (N : ℝ))))
           (Nat.floor (|t i - t j| / (2 * Real.pi * (N : ℝ)))) (t i - t j)‖ ^ 2 ≤ 961 := by
        have h := pow_le_pow_left₀ (norm_nonneg _) hB 2
        norm_num at h ⊢
        exact h
      have step1 : Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 *
            (1 + ‖hbm (Nat.ceil (|t i - t j| / (4 * Real.pi * (N : ℝ))))
              (Nat.floor (|t i - t j| / (2 * Real.pi * (N : ℝ)))) (t i - t j)‖ ^ 2)
          ≤ Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 * 962 := by
        have h1n : (0 : ℝ) ≤ (1 + Real.log (2 + 2 * Δ)) ^ 4 := by positivity
        nlinarith [hCv, h1n, hB2]
      have step2 : Cv * (1 + Real.log (2 + 2 * Δ)) ^ 4 * 962 ≤ Cv * (Cl * Δ ^ ε) * 962 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogb hCv.le) (by norm_num)
      have step3 : Cv * (Cl * Δ ^ ε) * 962 = (Cv * Cl * 962) * Δ ^ ε := by ring
      have hfin := le_trans hA (le_trans step1 (le_trans step2 (le_of_eq step3)))
      simpa using hfin
    · rw [if_neg hc]
      have hcoef : 0 ≤ (Cv * Cl * 962) * Δ ^ ε :=
        mul_nonneg (by positivity) (Real.rpow_nonneg hΔnn ε)
      have hif : 0 ≤ (if |t i - t j| ≤ 2 * Δ then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      exact mul_nonneg hcoef hif
  calc annSum N Δ R t
      = ∑ i : Fin R, ∑ j : Fin R,
          (if Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ then ‖hbm N (2 * N) (t i - t j)‖ ^ 2 else 0) := rfl
    _ ≤ ∑ i : Fin R, ∑ j : Fin R,
          ((Cv * Cl * 962) * Δ ^ ε) * (if |t i - t j| ≤ 2 * Δ then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = ((Cv * Cl * 962) * Δ ^ ε) *
          (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ 2 * Δ then (1 : ℝ) else 0)) :=
        hbm_sum2_mul_sum _ _
    _ = (Cv * Cl * 962) * Δ ^ ε * pcount (2 * Δ) R t := rfl

end Work.GM.HB
