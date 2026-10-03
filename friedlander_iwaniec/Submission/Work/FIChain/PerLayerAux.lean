/-
# `Work.FIChain.PerLayerAux` — auxiliary inputs of the FI per-layer bound

Two inputs of `Work.FIChain.TnB_FIgtil_perLayer` proved here directly:

* `nuFI_LinNormKup_aux` — the windowed `Ω₂` norm of the §6 sieve density `ν_Δ` at level `Δ`,
  from `sharpNorm_two_FIgtil`;
* `phiSeries_bound_aux` — the summability of the per-layer majorant `phiTerm K k`, via the
  Stirling lower bound `Stirling.le_factorial_stirling` and a comparison with the geometric
  series `∑ (k+1)(r²)^k` with `r = (10/9)·e·log(10/9) < 1`.

Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.FIChain.PerLayerDefs
import Submission.Work.FIChain.sharpNorm_two_FIgtil
import Submission.Work.FIChain.prod_inv_le_of_window_bounds

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

noncomputable section

/-- Backup proof of the windowed norm, from `sharpNorm_two_FIgtil` directly. -/
theorem nuFI_LinNormKup_aux (Δ : ℕ) (hΔ : 3 ≤ Δ) :
    LinNormKup (nuFI Δ) KFI 2 (Δ : ℝ) := by
  obtain ⟨hKpos, hK⟩ := Classical.choose_spec sharpNorm_two_FIgtil
  have hKle : Classical.choose sharpNorm_two_FIgtil ≤ KFI := le_max_left _ _
  intro w z hw hwz hzΔ
  rcases eq_or_lt_of_le hwz with hEq | hlt
  · rw [← hEq]
    have hempty : (Nat.primesBelow ⌈w⌉₊).filter (fun p : ℕ => w ≤ (p : ℝ)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp
      simp only [not_le]
      exact Nat.lt_ceil.mp (Nat.mem_primesBelow.mp hp).1
    rw [hempty, Finset.prod_empty]
    have h1 : Real.log w / Real.log w = 1 :=
      div_self (ne_of_gt (Real.log_pos (by linarith)))
    rw [h1, Real.one_rpow, mul_one]
    exact KFI_one_le
  · have hceilΔ : ⌈z⌉₊ ≤ Δ := Nat.ceil_le.mpr hzΔ
    have hset : (Nat.primesBelow ⌈z⌉₊).filter (fun p : ℕ => w ≤ (p : ℝ))
        = (Nat.primesBelow Δ).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z) := by
      ext p
      rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primesBelow]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨lt_of_lt_of_le h1 (by exact_mod_cast hceilΔ), h2⟩, h3, ?_⟩
        by_contra hcon
        have hzp : ⌈z⌉₊ ≤ p := Nat.ceil_le.mpr (not_lt.mp hcon)
        omega
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨by exact_mod_cast (lt_of_lt_of_le h4 (Nat.le_ceil z)), h2⟩, h3⟩
    rw [hset]
    refine le_trans (hK Δ hΔ w z hw hlt hzΔ) ?_
    exact mul_le_mul_of_nonneg_right hKle
      (Real.rpow_nonneg (div_nonneg (Real.log_nonneg (by linarith))
        (Real.log_nonneg (by linarith))) _)

/-- Backup proof of the summability of the per-layer majorant. -/
theorem phiSeries_bound_aux (K : ℝ) (hK : 1 ≤ K) :
    ∃ Φ : ℝ, 0 < Φ ∧ ∀ N : ℕ,
      (∑ k ∈ Finset.range N, phiTerm K k) ≤ Φ := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  set a : ℝ := (10 : ℝ) / 9 with ha
  have ha1 : (1 : ℝ) < a := by rw [ha]; norm_num
  have ha0 : (0 : ℝ) < a := by linarith
  set l : ℝ := Real.log a with hl
  have hl0 : 0 < l := by rw [hl]; exact Real.log_pos ha1
  set L : ℝ := 2 * l with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  set P : ℝ := Real.log K + 2 * Real.log 2 with hP
  have hP0 : 0 ≤ P := by
    rw [hP]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  set r : ℝ := a * Real.exp 1 * l with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, ha]
    have hlog1 : Real.log ((10 : ℝ) / 9) ≤ 1 / 9 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (10 : ℝ) / 9 by norm_num)
      linarith
    have hlog0 : 0 < Real.log ((10 : ℝ) / 9) := Real.log_pos (by norm_num)
    nlinarith [hlog1, hlog0, Real.exp_one_lt_three, Real.exp_pos 1]
  set c : ℝ := 2 * P / L with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hr2' : ‖r ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hr2
  have hden : 0 < 1 - r ^ 2 := by linarith
  have hsumm1 : Summable (fun k : ℕ => (r ^ 2) ^ k) := summable_geometric_of_norm_lt_one hr2'
  have hsumm2 : Summable (fun k : ℕ => (k : ℝ) * (r ^ 2) ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr2').summable
  have hsumm3 : Summable (fun k : ℕ => ((k : ℝ) + 1) * (r ^ 2) ^ k) :=
    (hsumm2.add hsumm1).congr (fun k => by ring)
  have hsumm4 : Summable (fun k : ℕ => (4 * K * Real.exp (1 + c) * (P + L))
      * (((k : ℝ) + 1) * (r ^ 2) ^ k)) := hsumm3.mul_left _
  have key_tsum : (∑' k : ℕ, ((k : ℝ) + 1) * (r ^ 2) ^ k) = (1 - r ^ 2)⁻¹ ^ 2 := by
    have hsum := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr2').add
      (hasSum_geometric_of_norm_lt_one hr2')
    have hcongr : (fun k : ℕ => (k : ℝ) * (r ^ 2) ^ k + (r ^ 2) ^ k)
        = (fun k : ℕ => ((k : ℝ) + 1) * (r ^ 2) ^ k) := by
      funext k; ring
    rw [hcongr] at hsum
    rw [hsum.tsum_eq]
    field_simp
    try ring
  refine ⟨4 * K * Real.exp (1 + c) * (P + L) * (1 - r ^ 2)⁻¹ ^ 2, ?_, ?_⟩
  · have h1 : 0 < 1 - r ^ 2 := hden
    positivity
  · intro N
    have hterm : ∀ k : ℕ,
        phiTerm K k ≤ (4 * K * Real.exp (1 + c) * (P + L)) * (((k : ℝ) + 1) * (r ^ 2) ^ k) := by
      intro k
      have h2k1 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
      have hk1 : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hAk : P + L * (k : ℝ) ≤ (P + L) * ((k : ℝ) + 1) := by
        nlinarith [hP0, hL0, Nat.cast_nonneg (α := ℝ) k]
      have hlog2ak : Real.log (2 * a ^ k) = Real.log 2 + (k : ℝ) * l := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hl]
      have hI : phiTerm K k
          = K * 4 * a ^ (2 * k) * (P + L * (k : ℝ)) ^ (2 * k + 1)
              / (((2 * k + 1).factorial : ℕ) : ℝ) := by
        rw [phiTerm, hlog2ak]
        have h1 : Real.log K + 2 * (Real.log 2 + (k : ℝ) * l) = P + L * (k : ℝ) := by
          rw [hP, hL]; ring
        rw [h1]
        have h2 : (2 * a ^ k) ^ 2 = 4 * a ^ (2 * k) := by
          rw [mul_pow, ← pow_mul]; ring
        rw [h2]
        ring
      rw [hI]
      have hstir : ((2 * (k : ℝ) + 1) / Real.exp 1) ^ (2 * k + 1)
          ≤ (((2 * k + 1).factorial : ℕ) : ℝ) := by
        have h := Stirling.le_factorial_stirling (2 * k + 1)
        have hs : (2 * (k : ℝ) + 1) = ((2 * k + 1 : ℕ) : ℝ) := by push_cast; ring
        have h0 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * ((2 * k + 1 : ℕ) : ℝ)) := by
          rw [Real.one_le_sqrt]
          have hk1' : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 1 ≤ 2 * k + 1)
          nlinarith [Real.pi_gt_three, hk1']
        have h1 : (0 : ℝ) ≤ (((2 * k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (2 * k + 1) := by
          positivity
        calc ((2 * (k : ℝ) + 1) / Real.exp 1) ^ (2 * k + 1)
            = 1 * ((((2 * k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (2 * k + 1)) := by
              rw [one_mul, hs]
          _ ≤ Real.sqrt (2 * Real.pi * ((2 * k + 1 : ℕ) : ℝ))
                * ((((2 * k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (2 * k + 1)) :=
              mul_le_mul_of_nonneg_right h0 h1
          _ ≤ (((2 * k + 1).factorial : ℕ) : ℝ) := h
      have hid : ((P + L * (k : ℝ)) ^ (2 * k + 1))
            / (((2 * (k : ℝ) + 1)) / Real.exp 1) ^ (2 * k + 1)
          = (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k + 1) := by
        rw [div_pow, div_pow, mul_pow]
        field_simp
        try ring
      have hstep1 : K * 4 * a ^ (2 * k) * (P + L * (k : ℝ)) ^ (2 * k + 1)
            / (((2 * k + 1).factorial : ℕ) : ℝ)
          ≤ K * 4 * a ^ (2 * k)
              * (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k + 1) := by
        have h0 : (P + L * (k : ℝ)) ^ (2 * k + 1) / (((2 * k + 1).factorial : ℕ) : ℝ)
            ≤ (P + L * (k : ℝ)) ^ (2 * k + 1)
              / (((2 * (k : ℝ) + 1) / Real.exp 1) ^ (2 * k + 1)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hstir
        calc K * 4 * a ^ (2 * k) * (P + L * (k : ℝ)) ^ (2 * k + 1)
              / (((2 * k + 1).factorial : ℕ) : ℝ)
            = K * 4 * a ^ (2 * k)
                * ((P + L * (k : ℝ)) ^ (2 * k + 1) / (((2 * k + 1).factorial : ℕ) : ℝ)) := by
              ring
          _ ≤ K * 4 * a ^ (2 * k)
                * ((P + L * (k : ℝ)) ^ (2 * k + 1)
                    / (((2 * (k : ℝ) + 1) / Real.exp 1) ^ (2 * k + 1))) :=
              mul_le_mul_of_nonneg_left h0 (by positivity)
          _ = K * 4 * a ^ (2 * k)
                * (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k + 1) := by
              rw [hid]
      have hsplit : K * 4 * a ^ (2 * k)
            * (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k + 1)
          = K * 4 * (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1))
              * (a * Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k) := by
        rw [pow_succ]
        rw [show K * 4 * a ^ (2 * k)
              * ((Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k)
                * (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)))
            = K * 4
              * (a ^ (2 * k)
                * (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k))
              * (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) by ring]
        rw [← mul_pow]
        rw [show a * (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1))
            = a * Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1) by ring]
        ring
      have hstep2 : K * 4 * a ^ (2 * k)
            * (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k + 1)
          ≤ K * 4 * Real.exp 1 * (P + L * (k : ℝ))
              * (a * Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k) := by
        have h3 : Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)
            ≤ Real.exp 1 * (P + L * (k : ℝ)) := by
          rw [div_le_iff₀ h2k1]
          nlinarith [show (0 : ℝ) ≤ Real.exp 1 * (P + L * (k : ℝ)) by positivity]
        calc K * 4 * a ^ (2 * k)
              * (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k + 1)
            = K * 4 * (Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1))
                * (a * Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k) := hsplit
          _ ≤ K * 4 * (Real.exp 1 * (P + L * (k : ℝ)))
                * (a * Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
          _ = K * 4 * Real.exp 1 * (P + L * (k : ℝ))
                * (a * Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k) := by ring
      have hZle : a * Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)
          ≤ r * (1 + c / (2 * (k : ℝ) + 1)) := by
        have hr_eq : r * (1 + c / (2 * (k : ℝ) + 1))
            = a * Real.exp 1 * (l + P / (2 * (k : ℝ) + 1)) := by
          rw [hr, hc, hL]
          field_simp
          try ring
        rw [hr_eq, div_le_iff₀ h2k1]
        have h2 : L * (k : ℝ) ≤ l * (2 * (k : ℝ) + 1) := by
          rw [hL]; nlinarith [hl0, Nat.cast_nonneg (α := ℝ) k]
        have h3 : (l + P / (2 * (k : ℝ) + 1)) * (2 * (k : ℝ) + 1)
            = l * (2 * (k : ℝ) + 1) + P := by
          field_simp
          try ring
        rw [show a * Real.exp 1 * (l + P / (2 * (k : ℝ) + 1)) * (2 * (k : ℝ) + 1)
            = a * Real.exp 1 * ((l + P / (2 * (k : ℝ) + 1)) * (2 * (k : ℝ) + 1)) by ring, h3]
        nlinarith [h2]
      have hZ0 : 0 ≤ a * Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1) := by positivity
      have hPc : 0 ≤ 1 + c / (2 * (k : ℝ) + 1) := by positivity
      have hexp : (1 + c / (2 * (k : ℝ) + 1)) ^ (2 * k) ≤ Real.exp c := by
        have h1 : 1 + c / (2 * (k : ℝ) + 1) ≤ Real.exp (c / (2 * (k : ℝ) + 1)) := by
          have h := Real.add_one_le_exp (c / (2 * (k : ℝ) + 1)); linarith
        calc (1 + c / (2 * (k : ℝ) + 1)) ^ (2 * k)
            ≤ (Real.exp (c / (2 * (k : ℝ) + 1))) ^ (2 * k) :=
              pow_le_pow_left₀ hPc h1 _
          _ = Real.exp ((c / (2 * (k : ℝ) + 1)) * (2 * (k : ℝ))) := by
              rw [← Real.exp_nat_mul]
              congr 1
              push_cast
              ring
          _ ≤ Real.exp c := by
              rw [Real.exp_le_exp]
              rw [div_mul_eq_mul_div, div_le_iff₀ h2k1]
              exact mul_le_mul_of_nonneg_left (by linarith [Nat.cast_nonneg (α := ℝ) k]) hc0
      have hZ2 : (a * Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k)
          ≤ r ^ (2 * k) * Real.exp c := by
        calc (a * Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k)
            ≤ (r * (1 + c / (2 * (k : ℝ) + 1))) ^ (2 * k) :=
              pow_le_pow_left₀ hZ0 hZle _
          _ = r ^ (2 * k) * (1 + c / (2 * (k : ℝ) + 1)) ^ (2 * k) := by rw [mul_pow]
          _ ≤ r ^ (2 * k) * Real.exp c :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
      calc K * 4 * a ^ (2 * k) * (P + L * (k : ℝ)) ^ (2 * k + 1)
            / (((2 * k + 1).factorial : ℕ) : ℝ)
          ≤ K * 4 * Real.exp 1 * (P + L * (k : ℝ))
              * (a * Real.exp 1 * (P + L * (k : ℝ)) / (2 * (k : ℝ) + 1)) ^ (2 * k) :=
            le_trans hstep1 hstep2
        _ ≤ K * 4 * Real.exp 1 * (P + L * (k : ℝ)) * (r ^ (2 * k) * Real.exp c) :=
            mul_le_mul_of_nonneg_left hZ2 (by positivity)
        _ = 4 * K * Real.exp (1 + c) * (P + L * (k : ℝ)) * (r ^ 2) ^ k := by
            rw [Real.exp_add, ← pow_mul]
            ring
        _ ≤ (4 * K * Real.exp (1 + c) * (P + L)) * (((k : ℝ) + 1) * (r ^ 2) ^ k) := by
            have h2 : (0 : ℝ) ≤ 4 * K * Real.exp (1 + c) * (r ^ 2) ^ k := by positivity
            nlinarith [hAk, h2]
    calc ∑ k ∈ Finset.range N, phiTerm K k
        ≤ ∑ k ∈ Finset.range N,
            (4 * K * Real.exp (1 + c) * (P + L)) * (((k : ℝ) + 1) * (r ^ 2) ^ k) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ ≤ ∑' k : ℕ,
            (4 * K * Real.exp (1 + c) * (P + L)) * (((k : ℝ) + 1) * (r ^ 2) ^ k) :=
          Summable.sum_le_tsum _ (fun k _ => by positivity) hsumm4
      _ = 4 * K * Real.exp (1 + c) * (P + L) * (1 - r ^ 2)⁻¹ ^ 2 := by
          rw [tsum_mul_left, key_tsum]

end

end Work.FIChain
