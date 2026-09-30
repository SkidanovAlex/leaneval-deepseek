import Mathlib
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.pairSetD_inv_le
import Submission.Work.BMF.mr_direct.dupExtra_defs
import Submission.Work.BMF.mr_direct.dupExtra_expand
import Submission.Work.BMF.mr_direct.dupExtra_integral_le
import Submission.Work.BMF.mr_direct.dupExtraR_defs
import Submission.Work.BMF.mr_direct.dupExtraR_expand
import Submission.Work.BMF.mr_direct.dupExtraR_nnD_bounds
import Submission.Work.BMF.mr_direct.dupExtraR_fiber_card
import Submission.Work.BMF.mr_direct.winIdxR_inv_sq_le
import Submission.Work.BMF.mr_direct.winIdxR_filter_dvd_inv_sq_le
import Submission.Work.BMF.mr_direct.primeImgDR_inv_sum_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Mean-square bound for `dupExtraR`

This is the range-generalised analogue of `Work.BMF.mr_direct.dupExtra_integral_le`: the
same proof with `X ↦ A` (the left endpoint of the range, which plays the role of the scale),
`2 * X ↦ B` (the right endpoint), `winIdx ↦ winIdxR` and `pSetD ↦ pSetDR`.

The critical inputs are

* the Montgomery–Vaughan mean value theorem `MVConst`, applied through
  `integral_norm_sum_le` to the set of triples `x ∈ pSetDR` with frequency `nnD x = p·m`
  and coefficient `gamD x = c p · b m · (ω(m;P,Q)+1)^{-1}` (`dupExtraR_expand`);
* the fibre bounds `dupExtraR_nnD_bounds` (the frequencies lie in `[A e^{-1/K}, B e^{1/K}]`)
  and `dupExtraR_fiber_card` (a fibre of `nnD` has at most `2 + 2·#{p' : p' ∣ m}` elements);
* the reciprocal-window sums `winIdxR_inv_sq_le`, `winIdxR_filter_dvd_inv_sq_le`;
* the reciprocal-prime sum bound `pairSetD_inv_le`.

The arithmetic constant `65` of `pairSetD_inv_le`, together with `1/K + 1/P ≤ 3/2`,
`exp (1/K) ≤ 3`, `|gamD| ≤ 1` and the fibre factor `2 + 2·card`, yields the numerical
constants `200000` and `100` of the statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators
open Work.BMF.mrDirect

theorem dupExtraR_integral_le (C₀ : ℝ) (hC₀ : Work.BMF.mrDirect.MVConst C₀)
    (b c : ℕ → ℂ) (K P Q A B S : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB4 : B ≤ 4 * A)
    (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (hS : 0 ≤ S) :
    (∫ t in (-S)..S, ‖Work.BMF.mrDirect.dupExtraR b c K P Q A B t‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * (B * Real.exp (1 / K))) *
          (200000 / A * (1 / K + 1 / P) + 100 / (P * A)) := by
  classical
  have hA0 : 0 < A := by linarith
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hApos : 0 < A * Real.exp (-(1 / K)) := mul_pos hA0 (Real.exp_pos _)
  have hB0 : 0 < B := lt_of_lt_of_le hA0 hAB
  have hBpos : 0 < B * Real.exp (1 / K) := mul_pos hB0 (Real.exp_pos _)
  have hAleB : A * Real.exp (-(1 / K)) ≤ B * Real.exp (1 / K) := by
    have h1 : Real.exp (-(1 / K)) ≤ Real.exp (1 / K) := by
      apply Real.exp_le_exp.mpr
      have h2 : (0 : ℝ) ≤ 1 / K := by positivity
      linarith
    calc A * Real.exp (-(1 / K)) ≤ B * Real.exp (-(1 / K)) :=
          mul_le_mul_of_nonneg_right hAB (Real.exp_pos _).le
      _ ≤ B * Real.exp (1 / K) := mul_le_mul_of_nonneg_left h1 hB0.le
  have hC0nn : 0 ≤ C₀ := hC₀.nonneg
  -- bound on the coefficients gamma
  have hγ : ∀ x ∈ pSetDR K P Q A B, ‖gamD b c P Q x‖ ≤ 1 := by
    intro x hx
    have h1 : ‖c x.1.2‖ ≤ 1 := hc _
    have h2 : ‖b x.2‖ ≤ 1 := hb _
    have h3 : ‖(((((omegaCount P Q x.2 : ℕ) + 1 : ℕ)) : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_natCast]
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _)
    simp only [gamD]
    calc ‖c x.1.2 * b x.2 * ((((omegaCount P Q x.2 : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖
        = ‖c x.1.2‖ * ‖b x.2‖ * ‖((((omegaCount P Q x.2 : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  -- membership of the frequencies in the interval
  have hmem : ∀ x ∈ pSetDR K P Q A B,
      nnD x ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)) := by
    intro x hx
    obtain ⟨hlo, hhi⟩ := dupExtraR_nnD_bounds K P Q A B hA hAB x hx
    rw [Work.BMF.mrDirect.mem_natIcc hBpos.le]
    exact ⟨hlo, hhi⟩
  -- the energy, written with fibers
  set W : ℝ := ∑ y ∈ pairSetD K P Q, (1 : ℝ) / (y.2 : ℝ) with hWdef
  set S1 : ℝ := ∑ p ∈ primeImgDR K P Q A B, (1 : ℝ) / (p : ℝ) with hS1def
  have hWnn : 0 ≤ W := by rw [hWdef]; positivity
  have hS1nn : 0 ≤ S1 := by rw [hS1def]; positivity
  -- T1
  have hT1 : (∑ x ∈ pSetDR K P Q A B, (1 : ℝ) / (nnD x : ℝ) ^ 2)
      ≤ 2 * Real.exp (1 / K) * W / A := by
    rw [pSetDR_eq_sigma, Finset.sum_sigma]
    have hinner : ∀ y ∈ pairSetD K P Q,
        (∑ m ∈ winIdxR K A B y.1, (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
          ≤ (2 * Real.exp (1 / K) / A) * (1 / (y.2 : ℝ)) := by
      intro y hy
      have hwin : y.2 ∈ winPrimes K y.1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).2).1
      have hy2pos : 0 < (y.2 : ℝ) := by
        have h := (mem_winPrimes.mp hwin).1
        exact_mod_cast h.pos
      calc (∑ m ∈ winIdxR K A B y.1, (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
          = (1 / (y.2 : ℝ) ^ 2) * (∑ m ∈ winIdxR K A B y.1, (1 : ℝ) / (m : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _
            simp only [nnD]
            rw [one_div_natCast_mul_sq]
        _ ≤ (1 / (y.2 : ℝ) ^ 2) * (2 * Real.exp (((y.1 : ℝ) + 1) / K) / A) :=
            mul_le_mul_of_nonneg_left (winIdxR_inv_sq_le K A B y.1 hA0) (by positivity)
        _ ≤ (1 / (y.2 : ℝ) ^ 2) * (2 * (Real.exp (1 / K) * (y.2 : ℝ)) / A) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply div_le_div_of_nonneg_right _ hA0.le
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            have he : Real.exp ((y.1 : ℝ) / K) ≤ (y.2 : ℝ) := (mem_winPrimes.mp hwin).2.1
            have hsplit : ((y.1 : ℝ) + 1) / K = 1 / K + (y.1 : ℝ) / K := by ring
            rw [hsplit, Real.exp_add]
            exact mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
        _ = (2 * Real.exp (1 / K) / A) * (1 / (y.2 : ℝ)) := by
            have hne : (y.2 : ℝ) ≠ 0 := ne_of_gt hy2pos
            field_simp
    calc (∑ y ∈ pairSetD K P Q, ∑ m ∈ winIdxR K A B y.1,
            (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
        ≤ ∑ y ∈ pairSetD K P Q, (2 * Real.exp (1 / K) / A) * (1 / (y.2 : ℝ)) :=
          Finset.sum_le_sum hinner
      _ = (2 * Real.exp (1 / K) / A) * W := by
          rw [hWdef, Finset.mul_sum]
      _ = 2 * Real.exp (1 / K) * W / A := by ring
  -- T2
  have hT2 : (∑ x ∈ pSetDR K P Q A B,
        (((primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
          (1 / (nnD x : ℝ) ^ 2))
      ≤ 2 * Real.exp (1 / K) * W * S1 / A := by
    have hin : ∀ p' ∈ primeImgDR K P Q A B,
        (∑ x ∈ pSetDR K P Q A B, (if p' ∣ x.2 then (1 : ℝ) else 0) * (1 / (nnD x : ℝ) ^ 2))
          ≤ (2 * Real.exp (1 / K) / A) * W * (1 / (p' : ℝ)) := by
      intro p' hp'
      have hp'prime : p'.Prime := by
        rw [primeImgDR, Finset.mem_image] at hp'
        obtain ⟨x, hx, hxp⟩ := hp'
        rw [pSetDR_eq_sigma] at hx
        have hx1 : x.1 ∈ pairSetD K P Q := (Finset.mem_sigma.mp hx).1
        have hwin : x.1.2 ∈ winPrimes K x.1.1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx1).2).1
        rw [← hxp]
        exact (mem_winPrimes.mp hwin).1
      have hp1 : 1 ≤ p' := hp'prime.one_le
      have hp'pos : 0 < (p' : ℝ) := by exact_mod_cast hp'prime.pos
      have hfil : (pSetDR K P Q A B).filter (fun x => p' ∣ x.2)
          = (pairSetD K P Q).sigma (fun y => (winIdxR K A B y.1).filter (fun m => p' ∣ m)) := by
        rw [pSetDR_eq_sigma]
        ext x
        simp only [Finset.mem_filter, Finset.mem_sigma]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨h1, h2⟩, h3⟩
      rw [show (∑ x ∈ pSetDR K P Q A B, (if p' ∣ x.2 then (1 : ℝ) else 0) * (1 / (nnD x : ℝ) ^ 2))
            = ∑ x ∈ (pSetDR K P Q A B).filter (fun x => p' ∣ x.2), (1 / (nnD x : ℝ) ^ 2) by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : p' ∣ x.2 <;> simp [h]]
      rw [hfil, Finset.sum_sigma]
      have hinner : ∀ y ∈ pairSetD K P Q,
          (∑ m ∈ (winIdxR K A B y.1).filter (fun m => p' ∣ m),
              (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
            ≤ (2 * Real.exp (1 / K) / A) * (1 / (p' : ℝ)) * (1 / (y.2 : ℝ)) := by
        intro y hy
        have hwin : y.2 ∈ winPrimes K y.1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).2).1
        have hy2pos : 0 < (y.2 : ℝ) := by
          have h := (mem_winPrimes.mp hwin).1
          exact_mod_cast h.pos
        have hsum : (∑ m ∈ (winIdxR K A B y.1).filter (fun m => p' ∣ m), (1 : ℝ) / (m : ℝ) ^ 2)
            ≤ 2 * Real.exp (((y.1 : ℝ) + 1) / K) / ((p' : ℝ) * A) :=
          winIdxR_filter_dvd_inv_sq_le K A B y.1 p' hA0 hp1
        have hexp : Real.exp (((y.1 : ℝ) + 1) / K) ≤ Real.exp (1 / K) * (y.2 : ℝ) := by
          have hle : Real.exp ((y.1 : ℝ) / K) ≤ (y.2 : ℝ) := (mem_winPrimes.mp hwin).2.1
          have hsplit : ((y.1 : ℝ) + 1) / K = 1 / K + (y.1 : ℝ) / K := by ring
          rw [hsplit, Real.exp_add]
          exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
        calc (∑ m ∈ (winIdxR K A B y.1).filter (fun m => p' ∣ m),
                (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
            = (1 / (y.2 : ℝ) ^ 2) * (∑ m ∈ (winIdxR K A B y.1).filter (fun m => p' ∣ m),
                (1 : ℝ) / (m : ℝ) ^ 2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro m _
              simp only [nnD]
              rw [one_div_natCast_mul_sq]
          _ ≤ (1 / (y.2 : ℝ) ^ 2) * (2 * Real.exp (((y.1 : ℝ) + 1) / K) / ((p' : ℝ) * A)) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ ≤ (1 / (y.2 : ℝ) ^ 2) * (2 * (Real.exp (1 / K) * (y.2 : ℝ)) / ((p' : ℝ) * A)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hexp (by norm_num)
          _ = (2 * Real.exp (1 / K) / A) * (1 / (p' : ℝ)) * (1 / (y.2 : ℝ)) := by
              have hy2ne : (y.2 : ℝ) ≠ 0 := ne_of_gt hy2pos
              have hp'ne : (p' : ℝ) ≠ 0 := ne_of_gt hp'pos
              field_simp
      calc (∑ y ∈ pairSetD K P Q, ∑ m ∈ (winIdxR K A B y.1).filter (fun m => p' ∣ m),
              (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
          ≤ ∑ y ∈ pairSetD K P Q, (2 * Real.exp (1 / K) / A) * (1 / (p' : ℝ)) * (1 / (y.2 : ℝ)) :=
            Finset.sum_le_sum hinner
        _ = ((2 * Real.exp (1 / K) / A) * (1 / (p' : ℝ))) * W := by
            rw [hWdef, ← Finset.mul_sum]
        _ = (2 * Real.exp (1 / K) / A) * W * (1 / (p' : ℝ)) := by ring
    calc (∑ x ∈ pSetDR K P Q A B,
            (((primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
              (1 / (nnD x : ℝ) ^ 2))
        = ∑ x ∈ pSetDR K P Q A B, ∑ p' ∈ primeImgDR K P Q A B,
            (if p' ≠ x.1.2 ∧ p' ∣ x.2 then (1 : ℝ) else 0) * (1 / (nnD x : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro x _
          have hc : (((primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ)
              = ∑ p' ∈ (primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2), (1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [hc, Finset.sum_filter, Finset.sum_mul]
      _ = ∑ p' ∈ primeImgDR K P Q A B, ∑ x ∈ pSetDR K P Q A B,
            (if p' ≠ x.1.2 ∧ p' ∣ x.2 then (1 : ℝ) else 0) * (1 / (nnD x : ℝ) ^ 2) :=
          Finset.sum_comm
      _ ≤ ∑ p' ∈ primeImgDR K P Q A B, ∑ x ∈ pSetDR K P Q A B,
            (if p' ∣ x.2 then (1 : ℝ) else 0) * (1 / (nnD x : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro p' _
          apply Finset.sum_le_sum
          intro x _
          by_cases h : p' ∣ x.2
          · by_cases h2 : p' ≠ x.1.2 ∧ p' ∣ x.2
            · rw [if_pos h2, if_pos h]
            · rw [if_neg h2, if_pos h]
              simp
          · rw [if_neg (fun hh => h hh.2), if_neg h]
      _ ≤ ∑ p' ∈ primeImgDR K P Q A B, (2 * Real.exp (1 / K) / A) * W * (1 / (p' : ℝ)) :=
          Finset.sum_le_sum hin
      _ = ((2 * Real.exp (1 / K) / A) * W) * S1 := by
          rw [hS1def, ← Finset.mul_sum]
      _ = 2 * Real.exp (1 / K) * W * S1 / A := by ring
  have hW65 : W ≤ 65 * (1 / K + 1 / P) := by
    rw [hWdef]; exact pairSetD_inv_le K P Q hK hP hPQ
  have hS1W : S1 ≤ W := by
    rw [hS1def, hWdef]
    exact primeImgDR_inv_sum_le K P Q A B
  have hDle : 1 / K + 1 / P ≤ 3 / 2 := by
    have h1 : 1 / K ≤ 1 := by rw [div_le_one hKpos]; linarith
    have h2 : 1 / P ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hP
    linarith
  have he3 : Real.exp (1 / K) ≤ 3 := by
    have h1 : (1 : ℝ) / K ≤ 1 := by rw [div_le_one hKpos]; linarith
    calc Real.exp (1 / K) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
      _ ≤ 3 := le_of_lt Real.exp_one_lt_three
  -- energy bound, fiberwise
  have henergy : (∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
        (((pSetDR K P Q A B).filter (fun x => nnD x = n)).card : ℝ) *
          (∑ x ∈ (pSetDR K P Q A B).filter (fun x => nnD x = n), ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2)
      ≤ 200000 / A * (1 / K + 1 / P) + 100 / (P * A) := by
    have hfiber : (∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
          (((pSetDR K P Q A B).filter (fun x => nnD x = n)).card : ℝ) *
            (∑ x ∈ (pSetDR K P Q A B).filter (fun x => nnD x = n), ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2)
        = ∑ x ∈ pSetDR K P Q A B,
            (((pSetDR K P Q A B).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
              (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2) := by
      have h1 : ∀ n : ℕ, (∑ x ∈ (pSetDR K P Q A B).filter (fun x => nnD x = n),
              ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2
          = ∑ x ∈ (pSetDR K P Q A B).filter (fun x => nnD x = n),
              ‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2 := by
        intro n
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])
      calc (∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
              (((pSetDR K P Q A B).filter (fun x => nnD x = n)).card : ℝ) *
                (∑ x ∈ (pSetDR K P Q A B).filter (fun x => nnD x = n), ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2)
          = ∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
              (((pSetDR K P Q A B).filter (fun x => nnD x = n)).card : ℝ) *
                ((∑ x ∈ (pSetDR K P Q A B).filter (fun x => nnD x = n), ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2) :=
            Finset.sum_congr rfl (fun n _ => by ring)
        _ = ∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
              (((pSetDR K P Q A B).filter (fun x => nnD x = n)).card : ℝ) *
                (∑ x ∈ (pSetDR K P Q A B).filter (fun x => nnD x = n),
                  ‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2) :=
            Finset.sum_congr rfl (fun n _ => by rw [h1 n])
        _ = ∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
              ∑ x ∈ (pSetDR K P Q A B).filter (fun x => nnD x = n),
                (((pSetDR K P Q A B).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
                  (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2) := by
            apply Finset.sum_congr rfl
            intro n _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            rw [(Finset.mem_filter.mp hx).2]
        _ = ∑ x ∈ pSetDR K P Q A B,
              (((pSetDR K P Q A B).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
                (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2) :=
            Finset.sum_fiberwise_of_maps_to hmem _
    have hstep2 : (∑ x ∈ pSetDR K P Q A B,
            (((pSetDR K P Q A B).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
              (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2))
        ≤ 2 * (∑ x ∈ pSetDR K P Q A B, (1 : ℝ) / (nnD x : ℝ) ^ 2)
          + 2 * (∑ x ∈ pSetDR K P Q A B,
              (((primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                (1 / (nnD x : ℝ) ^ 2)) := by
      have h2 : ∀ x ∈ pSetDR K P Q A B,
          (((pSetDR K P Q A B).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
              (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2)
            ≤ (2 + 2 * ((primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                (1 / (nnD x : ℝ) ^ 2) := by
        intro x hx
        have hcard := dupExtraR_fiber_card K P Q A B hK x hx
        have hcardR : (((pSetDR K P Q A B).filter (fun x' => nnD x' = nnD x)).card : ℝ)
            ≤ (2 + 2 * ((primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) := by
          exact_mod_cast hcard
        calc (((pSetDR K P Q A B).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
                (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2)
            ≤ (2 + 2 * ((primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right hcardR (by positivity)
          _ ≤ (2 + 2 * ((primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                (1 / (nnD x : ℝ) ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have hxpos : 0 < (nnD x : ℝ) :=
                lt_of_lt_of_le hApos ((Work.BMF.mrDirect.mem_natIcc hBpos.le).mp (hmem x hx)).1
              rw [div_le_div_iff_of_pos_right (pow_pos hxpos 2)]
              exact pow_le_one₀ (norm_nonneg _) (hγ x hx)
      calc (∑ x ∈ pSetDR K P Q A B,
              (((pSetDR K P Q A B).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
                (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2))
          ≤ ∑ x ∈ pSetDR K P Q A B,
              (2 + 2 * ((primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                (1 / (nnD x : ℝ) ^ 2) :=
            Finset.sum_le_sum h2
        _ = 2 * (∑ x ∈ pSetDR K P Q A B, (1 : ℝ) / (nnD x : ℝ) ^ 2)
              + 2 * (∑ x ∈ pSetDR K P Q A B,
                  (((primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                    (1 / (nnD x : ℝ) ^ 2)) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x _
            push_cast
            ring
    rw [hfiber]
    have hmid : (∑ x ∈ pSetDR K P Q A B,
            (((pSetDR K P Q A B).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
              (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2))
        ≤ 4 * Real.exp (1 / K) * W * (1 + S1) / A := by
      calc _ ≤ 2 * (∑ x ∈ pSetDR K P Q A B, (1 : ℝ) / (nnD x : ℝ) ^ 2)
              + 2 * (∑ x ∈ pSetDR K P Q A B,
                  (((primeImgDR K P Q A B).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                    (1 / (nnD x : ℝ) ^ 2)) := hstep2
        _ ≤ 2 * (2 * Real.exp (1 / K) * W / A) + 2 * (2 * Real.exp (1 / K) * W * S1 / A) := by
            linarith [hT1, hT2]
        _ = 4 * Real.exp (1 / K) * W * (1 + S1) / A := by ring
    have hfinal : 4 * Real.exp (1 / K) * W * (1 + S1) / A
        ≤ 200000 / A * (1 / K + 1 / P) + 100 / (P * A) := by
      have hS1' : S1 ≤ 65 * (1 / K + 1 / P) := le_trans hS1W hW65
      have hkey : W * (1 + S1) ≤ 65 * (1 / K + 1 / P) * (1 + 65 * (1 / K + 1 / P)) := by
        calc W * (1 + S1) ≤ (65 * (1 / K + 1 / P)) * (1 + S1) :=
              mul_le_mul_of_nonneg_right hW65 (by linarith [hS1nn])
          _ ≤ (65 * (1 / K + 1 / P)) * (1 + 65 * (1 / K + 1 / P)) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hee : 4 * Real.exp (1 / K) ≤ 12 := by linarith [he3]
      have hprod : 4 * Real.exp (1 / K) * W * (1 + S1)
          ≤ 12 * (65 * (1 / K + 1 / P) * (1 + 65 * (1 / K + 1 / P))) := by
        calc 4 * Real.exp (1 / K) * W * (1 + S1)
            = (4 * Real.exp (1 / K)) * (W * (1 + S1)) := by ring
          _ ≤ 12 * (65 * (1 / K + 1 / P) * (1 + 65 * (1 / K + 1 / P))) :=
              mul_le_mul hee hkey (by positivity) (by norm_num)
      have harith : 12 * (65 * (1 / K + 1 / P) * (1 + 65 * (1 / K + 1 / P)))
          ≤ 76830 * (1 / K + 1 / P) := by
        nlinarith [hDle, hKpos, hPpos]
      have hdiv1 : 4 * Real.exp (1 / K) * W * (1 + S1) / A
          ≤ 76830 * (1 / K + 1 / P) / A := by
        apply div_le_div_of_nonneg_right _ hA0.le
        linarith [hprod, harith]
      have h3 : 76830 * (1 / K + 1 / P) / A
          ≤ 200000 / A * (1 / K + 1 / P) + 100 / (P * A) := by
        have hDnn : 0 ≤ 1 / K + 1 / P := by positivity
        have h4 : (76830 : ℝ) * (1 / K + 1 / P) / A
            ≤ (200000 : ℝ) * (1 / K + 1 / P) / A := by
          apply div_le_div_of_nonneg_right _ hA0.le
          exact mul_le_mul_of_nonneg_right (by norm_num) hDnn
        have h5 : (200000 : ℝ) * (1 / K + 1 / P) / A = 200000 / A * (1 / K + 1 / P) := by ring
        have h6 : 0 ≤ 100 / (P * A) := by positivity
        linarith [h4, h5.le, h5.ge, h6]
      linarith [hdiv1, h3]
    linarith [hmid, hfinal]
  -- main application of the mean value bound
  have hmain := integral_norm_sum_le C₀ hC₀ (pSetDR K P Q A B) (gamD b c P Q) nnD
      (Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)))
      (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)) S hApos hAleB hS hmem
      (fun x hx => (dupExtraR_nnD_bounds K P Q A B hA hAB x hx).1)
      (fun x hx => (dupExtraR_nnD_bounds K P Q A B hA hAB x hx).2)
  calc (∫ t in (-S)..S, ‖dupExtraR b c K P Q A B t‖ ^ 2)
      = ∫ t in (-S)..S, ‖∑ x ∈ pSetDR K P Q A B,
            gamD b c P Q x * (nnD x : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t _
          simp only []
          rw [dupExtraR_expand]
    _ ≤ (2 * S + 3 * C₀ * (B * Real.exp (1 / K))) *
          (∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
            (((pSetDR K P Q A B).filter (fun x => nnD x = n)).card : ℝ) *
              (∑ x ∈ (pSetDR K P Q A B).filter (fun x => nnD x = n), ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2) := hmain
    _ ≤ (2 * S + 3 * C₀ * (B * Real.exp (1 / K))) *
          (200000 / A * (1 / K + 1 / P) + 100 / (P * A)) := by
          apply mul_le_mul_of_nonneg_left henergy
          nlinarith [hS, hC0nn, hBpos]

end Work.BMF.mr_direct
