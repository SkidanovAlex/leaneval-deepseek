import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.omegaCount_mul_prime
import Submission.Work.BMF.mr_direct.sum_inv_primes_near
import Submission.Work.BMF.mr_direct.integral_norm_sum_le
import Submission.Work.BMF.mr_direct.dupExtra_defs
import Submission.Work.BMF.mr_direct.dupExtra_expand
import Submission.Work.BMF.mr_direct.dupExtra_nnD_bounds
import Submission.Work.BMF.mr_direct.dupExtra_fiber_card
import Submission.Work.BMF.mr_direct.winIdx_sum_bounds
import Submission.Work.BMF.mr_direct.sum_inv_sq_filter_dvd_le
import Submission.Work.BMF.mr_direct.pairSetD_inv_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators
open Work.BMF.mrDirect

/-- `∑_{n ∈ s.image g} f n ≤ ∑_{i ∈ s} f (g i)` for nonnegative `f`. -/
lemma sum_image_le_of_nonneg {ι : Type} (s : Finset ι) (g : ι → ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) : ∑ n ∈ s.image g, f n ≤ ∑ i ∈ s, f (g i) := by
  classical
  have h1 : (∑ n ∈ s.image g, ((s.filter (fun i => g i = n)).card : ℝ) * f n)
      = ∑ i ∈ s, f (g i) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image g) (g := g)
      (f := fun i => f (g i)) (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)]
    apply Finset.sum_congr rfl
    intro n hn
    have hc : ((s.filter (fun i => g i = n)).card : ℝ)
        = ∑ i ∈ s.filter (fun i => g i = n), (1 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [one_mul, (Finset.mem_filter.mp hi).2]
  have h2 : ∑ n ∈ s.image g, f n
      ≤ ∑ n ∈ s.image g, ((s.filter (fun i => g i = n)).card : ℝ) * f n := by
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp hn
    have hc : (1 : ℝ) ≤ ((s.filter (fun i => g i = n)).card : ℝ) := by
      have hpos : 0 < (s.filter (fun i => g i = n)).card :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
      exact_mod_cast hpos
    nlinarith [hf n]
  rw [h1] at h2
  exact h2

/-- `1 / (a*b)^2 = (1/a^2) * (1/b^2)` for naturals. -/
lemma one_div_natCast_mul_sq (a b : ℕ) :
    (1 : ℝ) / ((a * b : ℕ) : ℝ) ^ 2 = (1 / (a : ℝ) ^ 2) * (1 / (b : ℝ) ^ 2) := by
  push_cast
  rw [mul_pow, one_div, mul_inv]
  ring


theorem dupExtra_integral_le (C₀ : ℝ)
    (hC₀ : ∀ (δ : ℝ), 0 < δ → ∀ (N : ℕ) (μ : Fin N → ℝ) (b : Fin N → ℂ),
      (∀ i j, i ≠ j → δ ≤ |μ i - μ j|) → ∀ (A B : ℝ), A ≤ B →
        (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
          ≤ (B - A + C₀ / δ) * ∑ n, ‖b n‖ ^ 2)
    (b c : ℕ → ℂ) (K P Q X S : ℝ) (hX : 1 ≤ X) (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (hS : 0 ≤ S) :
    (∫ t in (-S)..S, ‖Work.BMF.mrDirect.dupExtra b c K P Q X t‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * (2 * X * Real.exp (1 / K))) *
          (200000 / X * (1 / K + 1 / P) + 100 / (P * X)) := by
  classical
  have hXpos : 0 < X := by linarith
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hApos : 0 < X * Real.exp (-(1 / K)) := by positivity
  have hBpos : 0 < 2 * X * Real.exp (1 / K) := by positivity
  have hAleB : X * Real.exp (-(1 / K)) ≤ 2 * X * Real.exp (1 / K) := by
    have h1 : Real.exp (-(1 / K)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0:ℝ) ≤ 1 / K := by positivity
      linarith
    have h2 : (1:ℝ) ≤ 2 * Real.exp (1 / K) := by
      have := Real.one_le_exp (show (0:ℝ) ≤ 1 / K by positivity)
      linarith
    nlinarith [hXpos.le]
  have hC0nn : 0 ≤ C₀ := mv_C0_nonneg C₀ hC₀
  -- bound on the coefficients gamma
  have hγ : ∀ x ∈ pSetD K P Q X, ‖gamD b c P Q x‖ ≤ 1 := by
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
      _ ≤ 1 * 1 * 1 := by
          gcongr
      _ = 1 := by ring
  -- membership of the frequencies in the interval
  have hmem : ∀ x ∈ pSetD K P Q X, nnD x ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)) := by
    intro x hx
    obtain ⟨hlo, hhi⟩ := dupExtra_nnD_bounds K P Q X hX hK hP hPQ x hx
    rw [Work.BMF.mrDirect.mem_natIcc hBpos.le]
    exact ⟨hlo, hhi⟩
  -- the energy, written with fibers
  set W : ℝ := ∑ y ∈ pairSetD K P Q, (1 : ℝ) / (y.2 : ℝ) with hWdef
  set S1 : ℝ := ∑ p ∈ primeImgD K P Q X, (1 : ℝ) / (p : ℝ) with hS1def
  have hWnn : 0 ≤ W := by rw [hWdef]; positivity
  have hS1nn : 0 ≤ S1 := by rw [hS1def]; positivity
  -- T1
  have hT1 : (∑ x ∈ pSetD K P Q X, (1 : ℝ) / (nnD x : ℝ) ^ 2)
      ≤ 2 * Real.exp (1 / K) * W / X := by
    rw [pSetD_eq_sigma, Finset.sum_sigma]
    have hinner : ∀ y ∈ pairSetD K P Q,
        (∑ m ∈ winIdx K X y.1, (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
          ≤ (2 * Real.exp (1 / K) / X) * (1 / (y.2 : ℝ)) := by
      intro y hy
      have hwin : y.2 ∈ winPrimes K y.1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).2).1
      have hy2pos : 0 < (y.2 : ℝ) := by
        have h := (mem_winPrimes.mp hwin).1
        exact_mod_cast h.pos
      calc (∑ m ∈ winIdx K X y.1, (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
          = (1 / (y.2 : ℝ) ^ 2) * (∑ m ∈ winIdx K X y.1, (1 : ℝ) / (m : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _
            simp only [nnD]
            rw [one_div_natCast_mul_sq]
        _ ≤ (1 / (y.2 : ℝ) ^ 2) * (2 * Real.exp (((y.1 : ℝ) + 1) / K) / X) :=
            mul_le_mul_of_nonneg_left (winIdx_sum_bounds.2.1 X K y.1 hX) (by positivity)
        _ ≤ (1 / (y.2 : ℝ) ^ 2) * (2 * (Real.exp (1 / K) * (y.2 : ℝ)) / X) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply div_le_div_of_nonneg_right _ hXpos.le
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            have he : Real.exp ((y.1 : ℝ) / K) ≤ (y.2 : ℝ) := (mem_winPrimes.mp hwin).2.1
            have hsplit : ((y.1 : ℝ) + 1) / K = 1 / K + (y.1 : ℝ) / K := by ring
            rw [hsplit, Real.exp_add]
            exact mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
        _ = (2 * Real.exp (1 / K) / X) * (1 / (y.2 : ℝ)) := by
            have hne : (y.2 : ℝ) ≠ 0 := ne_of_gt hy2pos
            field_simp
    calc (∑ y ∈ pairSetD K P Q, ∑ m ∈ winIdx K X y.1,
            (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
        ≤ ∑ y ∈ pairSetD K P Q, (2 * Real.exp (1 / K) / X) * (1 / (y.2 : ℝ)) :=
          Finset.sum_le_sum hinner
      _ = (2 * Real.exp (1 / K) / X) * W := by
          rw [hWdef, Finset.mul_sum]
      _ = 2 * Real.exp (1 / K) * W / X := by ring
  -- T2
  have hT2 : (∑ x ∈ pSetD K P Q X,
        (((primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
          (1 / (nnD x : ℝ) ^ 2))
      ≤ 2 * Real.exp (1 / K) * W * S1 / X := by
    have hin : ∀ p' ∈ primeImgD K P Q X,
        (∑ x ∈ pSetD K P Q X, (if p' ∣ x.2 then (1 : ℝ) else 0) * (1 / (nnD x : ℝ) ^ 2))
          ≤ (2 * Real.exp (1 / K) / X) * W * (1 / (p' : ℝ)) := by
      intro p' hp'
      have hp'prime : p'.Prime := by
        rw [primeImgD, Finset.mem_image] at hp'
        obtain ⟨x, hx, hxp⟩ := hp'
        rw [pSetD_eq_sigma] at hx
        have hx1 : x.1 ∈ pairSetD K P Q := (Finset.mem_sigma.mp hx).1
        have hwin : x.1.2 ∈ winPrimes K x.1.1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx1).2).1
        rw [← hxp]
        exact (mem_winPrimes.mp hwin).1
      have hp1 : 1 ≤ p' := hp'prime.one_le
      have hp'pos : 0 < (p' : ℝ) := by exact_mod_cast hp'prime.pos
      have hfil : (pSetD K P Q X).filter (fun x => p' ∣ x.2)
          = (pairSetD K P Q).sigma (fun y => (winIdx K X y.1).filter (fun m => p' ∣ m)) := by
        rw [pSetD_eq_sigma]
        ext x
        simp only [Finset.mem_filter, Finset.mem_sigma]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨h1, h2⟩, h3⟩
      rw [show (∑ x ∈ pSetD K P Q X, (if p' ∣ x.2 then (1 : ℝ) else 0) * (1 / (nnD x : ℝ) ^ 2))
            = ∑ x ∈ (pSetD K P Q X).filter (fun x => p' ∣ x.2), (1 / (nnD x : ℝ) ^ 2) by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : p' ∣ x.2 <;> simp [h]]
      rw [hfil, Finset.sum_sigma]
      have hinner : ∀ y ∈ pairSetD K P Q,
          (∑ m ∈ (winIdx K X y.1).filter (fun m => p' ∣ m),
              (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
            ≤ (2 * Real.exp (1 / K) / X) * (1 / (p' : ℝ)) * (1 / (y.2 : ℝ)) := by
        intro y hy
        have hwin : y.2 ∈ winPrimes K y.1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).2).1
        have hy2pos : 0 < (y.2 : ℝ) := by
          have h := (mem_winPrimes.mp hwin).1
          exact_mod_cast h.pos
        have hApos' : 0 < X * Real.exp (-(((y.1 : ℝ)) + 1) / K) := by positivity
        have hsum : (∑ m ∈ (winIdx K X y.1).filter (fun m => p' ∣ m), (1 : ℝ) / (m : ℝ) ^ 2)
            ≤ 2 / ((p' : ℝ) * (X * Real.exp (-(((y.1 : ℝ)) + 1) / K))) := by
          have := sum_inv_sq_filter_dvd_le (X * Real.exp (-(((y.1 : ℝ)) + 1) / K))
            (2 * X * Real.exp (-((y.1 : ℝ)) / K)) p' hApos' hp1
          simpa only [winIdx] using this
        have hexpA : Real.exp (-(((y.1 : ℝ)) + 1) / K)
            = (Real.exp (((y.1 : ℝ) + 1) / K))⁻¹ := by
          rw [show -(((y.1 : ℝ)) + 1) / K = -(((y.1 : ℝ) + 1) / K) by ring, Real.exp_neg]
        have hexp : Real.exp (((y.1 : ℝ) + 1) / K) ≤ Real.exp (1 / K) * (y.2 : ℝ) := by
          have hle : Real.exp ((y.1 : ℝ) / K) ≤ (y.2 : ℝ) := (mem_winPrimes.mp hwin).2.1
          have hsplit : ((y.1 : ℝ) + 1) / K = 1 / K + (y.1 : ℝ) / K := by ring
          rw [hsplit, Real.exp_add]
          exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
        calc (∑ m ∈ (winIdx K X y.1).filter (fun m => p' ∣ m),
                (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
            = (1 / (y.2 : ℝ) ^ 2) * (∑ m ∈ (winIdx K X y.1).filter (fun m => p' ∣ m),
                (1 : ℝ) / (m : ℝ) ^ 2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro m _
              simp only [nnD]
              rw [one_div_natCast_mul_sq]
          _ ≤ (1 / (y.2 : ℝ) ^ 2) * (2 / ((p' : ℝ) * (X * Real.exp (-(((y.1 : ℝ)) + 1) / K)))) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = (1 / (y.2 : ℝ) ^ 2) * (2 * Real.exp (((y.1 : ℝ) + 1) / K) / ((p' : ℝ) * X)) := by
              congr 1
              rw [hexpA]
              have h1 : (p' : ℝ) ≠ 0 := ne_of_gt hp'pos
              have h2 : X ≠ 0 := ne_of_gt hXpos
              have h3 : Real.exp (((y.1 : ℝ) + 1) / K) ≠ 0 := Real.exp_ne_zero _
              field_simp
          _ ≤ (1 / (y.2 : ℝ) ^ 2) * (2 * (Real.exp (1 / K) * (y.2 : ℝ)) / ((p' : ℝ) * X)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hexp (by norm_num)
          _ = (2 * Real.exp (1 / K) / X) * (1 / (p' : ℝ)) * (1 / (y.2 : ℝ)) := by
              have hy2ne : (y.2 : ℝ) ≠ 0 := ne_of_gt hy2pos
              have hp'ne : (p' : ℝ) ≠ 0 := ne_of_gt hp'pos
              field_simp
      calc (∑ y ∈ pairSetD K P Q, ∑ m ∈ (winIdx K X y.1).filter (fun m => p' ∣ m),
              (1 : ℝ) / (nnD (⟨y, m⟩ : Σ _ : Σ _ : ℕ, ℕ, ℕ) : ℝ) ^ 2)
          ≤ ∑ y ∈ pairSetD K P Q, (2 * Real.exp (1 / K) / X) * (1 / (p' : ℝ)) * (1 / (y.2 : ℝ)) :=
            Finset.sum_le_sum hinner
        _ = ((2 * Real.exp (1 / K) / X) * (1 / (p' : ℝ))) * W := by
            rw [hWdef, ← Finset.mul_sum]
        _ = (2 * Real.exp (1 / K) / X) * W * (1 / (p' : ℝ)) := by ring
    calc (∑ x ∈ pSetD K P Q X,
            (((primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
              (1 / (nnD x : ℝ) ^ 2))
        = ∑ x ∈ pSetD K P Q X, ∑ p' ∈ primeImgD K P Q X,
            (if p' ≠ x.1.2 ∧ p' ∣ x.2 then (1 : ℝ) else 0) * (1 / (nnD x : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro x _
          have hc : (((primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ)
              = ∑ p' ∈ (primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2), (1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [hc, Finset.sum_filter, Finset.sum_mul]
      _ = ∑ p' ∈ primeImgD K P Q X, ∑ x ∈ pSetD K P Q X,
            (if p' ≠ x.1.2 ∧ p' ∣ x.2 then (1 : ℝ) else 0) * (1 / (nnD x : ℝ) ^ 2) :=
          Finset.sum_comm
      _ ≤ ∑ p' ∈ primeImgD K P Q X, ∑ x ∈ pSetD K P Q X,
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
      _ ≤ ∑ p' ∈ primeImgD K P Q X, (2 * Real.exp (1 / K) / X) * W * (1 / (p' : ℝ)) :=
          Finset.sum_le_sum hin
      _ = ((2 * Real.exp (1 / K) / X) * W) * S1 := by
          rw [hS1def, ← Finset.mul_sum]
      _ = 2 * Real.exp (1 / K) * W * S1 / X := by ring
  have hW65 : W ≤ 65 * (1 / K + 1 / P) := by
    rw [hWdef]; exact pairSetD_inv_le K P Q hK hP hPQ
  have hS1W : S1 ≤ W := by
    have hsub : primeImgD K P Q X ⊆ (pairSetD K P Q).image (fun y => y.2) := by
      intro p hp
      rw [primeImgD, Finset.mem_image] at hp
      obtain ⟨x, hx, hxp⟩ := hp
      have hx1 : x.1 ∈ pairSetD K P Q := by
        rw [pSetD_eq_sigma] at hx
        exact (Finset.mem_sigma.mp hx).1
      rw [← hxp]
      exact Finset.mem_image.mpr ⟨x.1, hx1, rfl⟩
    rw [hS1def, hWdef]
    calc ∑ p ∈ primeImgD K P Q X, (1 : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ ((pairSetD K P Q).image (fun y => y.2) : Finset ℕ), (1 : ℝ) / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => (1 : ℝ) / (p : ℝ)) hsub
            (fun i _ _ => div_nonneg zero_le_one (Nat.cast_nonneg i))
      _ ≤ ∑ y ∈ pairSetD K P Q, (1 : ℝ) / (y.2 : ℝ) :=
          sum_image_le_of_nonneg (pairSetD K P Q) (fun y => y.2) (fun n => (1 : ℝ) / (n : ℝ))
            (fun n => by positivity)
  have hDle : 1 / K + 1 / P ≤ 3 / 2 := by
    have h1 : 1 / K ≤ 1 := by rw [div_le_one hKpos]; linarith
    have h2 : 1 / P ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hP
    linarith
  have he3 : Real.exp (1 / K) ≤ 3 := by
    have h1 : (1:ℝ) / K ≤ 1 := by rw [div_le_one hKpos]; linarith
    calc Real.exp (1 / K) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
      _ ≤ 3 := le_of_lt Real.exp_one_lt_three
  -- energy bound, fiberwise
  have henergy : (∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
        (((pSetD K P Q X).filter (fun x => nnD x = n)).card : ℝ) *
          (∑ x ∈ (pSetD K P Q X).filter (fun x => nnD x = n), ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2)
      ≤ 200000 / X * (1 / K + 1 / P) + 100 / (P * X) := by
    have hfiber : (∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
          (((pSetD K P Q X).filter (fun x => nnD x = n)).card : ℝ) *
            (∑ x ∈ (pSetD K P Q X).filter (fun x => nnD x = n), ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2)
        = ∑ x ∈ pSetD K P Q X,
            (((pSetD K P Q X).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
              (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2) := by
      have h1 : ∀ n : ℕ, (∑ x ∈ (pSetD K P Q X).filter (fun x => nnD x = n),
              ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2
          = ∑ x ∈ (pSetD K P Q X).filter (fun x => nnD x = n),
              ‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2 := by
        intro n
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])
      calc (∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
              (((pSetD K P Q X).filter (fun x => nnD x = n)).card : ℝ) *
                (∑ x ∈ (pSetD K P Q X).filter (fun x => nnD x = n), ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2)
          = ∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
              (((pSetD K P Q X).filter (fun x => nnD x = n)).card : ℝ) *
                ((∑ x ∈ (pSetD K P Q X).filter (fun x => nnD x = n), ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2) :=
            Finset.sum_congr rfl (fun n _ => by ring)
        _ = ∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
              (((pSetD K P Q X).filter (fun x => nnD x = n)).card : ℝ) *
                (∑ x ∈ (pSetD K P Q X).filter (fun x => nnD x = n),
                  ‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2) :=
            Finset.sum_congr rfl (fun n _ => by rw [h1 n])
        _ = ∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
              ∑ x ∈ (pSetD K P Q X).filter (fun x => nnD x = n),
                (((pSetD K P Q X).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
                  (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2) := by
            apply Finset.sum_congr rfl
            intro n _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            rw [(Finset.mem_filter.mp hx).2]
        _ = ∑ x ∈ pSetD K P Q X,
              (((pSetD K P Q X).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
                (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2) :=
            Finset.sum_fiberwise_of_maps_to hmem _
    have hstep2 : (∑ x ∈ pSetD K P Q X,
            (((pSetD K P Q X).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
              (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2))
        ≤ 2 * (∑ x ∈ pSetD K P Q X, (1 : ℝ) / (nnD x : ℝ) ^ 2)
          + 2 * (∑ x ∈ pSetD K P Q X,
              (((primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                (1 / (nnD x : ℝ) ^ 2)) := by
      have h2 : ∀ x ∈ pSetD K P Q X,
          (((pSetD K P Q X).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
              (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2)
            ≤ (2 + 2 * ((primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                (1 / (nnD x : ℝ) ^ 2) := by
        intro x hx
        have hcard := dupExtra_fiber_card K P Q X hX hK hP hPQ x hx
        have hcardR : (((pSetD K P Q X).filter (fun x' => nnD x' = nnD x)).card : ℝ)
            ≤ (2 + 2 * ((primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) := by
          exact_mod_cast hcard
        calc (((pSetD K P Q X).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
                (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2)
            ≤ (2 + 2 * ((primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right hcardR (by positivity)
          _ ≤ (2 + 2 * ((primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                (1 / (nnD x : ℝ) ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have hxpos : 0 < (nnD x : ℝ) :=
                lt_of_lt_of_le hApos ((Work.BMF.mrDirect.mem_natIcc hBpos.le).mp (hmem x hx)).1
              rw [div_le_div_iff_of_pos_right (pow_pos hxpos 2)]
              exact pow_le_one₀ (norm_nonneg _) (hγ x hx)
      calc (∑ x ∈ pSetD K P Q X,
              (((pSetD K P Q X).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
                (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2))
          ≤ ∑ x ∈ pSetD K P Q X,
              (2 + 2 * ((primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                (1 / (nnD x : ℝ) ^ 2) :=
            Finset.sum_le_sum h2
        _ = 2 * (∑ x ∈ pSetD K P Q X, (1 : ℝ) / (nnD x : ℝ) ^ 2)
              + 2 * (∑ x ∈ pSetD K P Q X,
                  (((primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                    (1 / (nnD x : ℝ) ^ 2)) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x _
            push_cast
            ring
    rw [hfiber]
    have hmid : (∑ x ∈ pSetD K P Q X,
            (((pSetD K P Q X).filter (fun x' => nnD x' = nnD x)).card : ℝ) *
              (‖gamD b c P Q x‖ ^ 2 / (nnD x : ℝ) ^ 2))
        ≤ 4 * Real.exp (1 / K) * W * (1 + S1) / X := by
      calc _ ≤ 2 * (∑ x ∈ pSetD K P Q X, (1 : ℝ) / (nnD x : ℝ) ^ 2)
              + 2 * (∑ x ∈ pSetD K P Q X,
                  (((primeImgD K P Q X).filter (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card : ℝ) *
                    (1 / (nnD x : ℝ) ^ 2)) := hstep2
        _ ≤ 2 * (2 * Real.exp (1 / K) * W / X) + 2 * (2 * Real.exp (1 / K) * W * S1 / X) := by
            linarith [hT1, hT2]
        _ = 4 * Real.exp (1 / K) * W * (1 + S1) / X := by ring
    have hfinal : 4 * Real.exp (1 / K) * W * (1 + S1) / X
        ≤ 200000 / X * (1 / K + 1 / P) + 100 / (P * X) := by
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
      have harith : 12 * (65 * (1 / K + 1 / P) * (1 + 65 * (1 / K + 1 / P))) ≤ 76830 * (1 / K + 1 / P) := by
        nlinarith [hDle, hKpos, hPpos]
      have hdiv1 : 4 * Real.exp (1 / K) * W * (1 + S1) / X ≤ 76830 * (1 / K + 1 / P) / X := by
        apply div_le_div_of_nonneg_right _ hXpos.le
        linarith [hprod, harith]
      have h3 : 76830 * (1 / K + 1 / P) / X
          ≤ 200000 / X * (1 / K + 1 / P) + 100 / (P * X) := by
        have h4 : (76830 : ℝ) * (1 / K + 1 / P) / X ≤ (200000 : ℝ) * (1 / K + 1 / P) / X := by
          apply div_le_div_of_nonneg_right (by linarith) hXpos.le
        have h5 : (200000 : ℝ) * (1 / K + 1 / P) / X = 200000 / X * (1 / K + 1 / P) := by ring
        have h6 : 0 ≤ 100 / (P * X) := by positivity
        linarith [h4, h5.le, h5.ge, h6]
      linarith [hdiv1, h3]
    linarith [hmid, hfinal]
  -- main application of the mean value bound
  have hmain := integral_norm_sum_le C₀ hC₀ (pSetD K P Q X) (gamD b c P Q) nnD
      (Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)))
      (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)) S hApos hAleB hS hmem
      (fun x hx => (dupExtra_nnD_bounds K P Q X hX hK hP hPQ x hx).1)
      (fun x hx => (dupExtra_nnD_bounds K P Q X hX hK hP hPQ x hx).2)
  calc (∫ t in (-S)..S, ‖dupExtra b c K P Q X t‖ ^ 2)
      = ∫ t in (-S)..S, ‖∑ x ∈ pSetD K P Q X,
            gamD b c P Q x * (nnD x : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t _
          simp only []
          rw [dupExtra_expand]
    _ ≤ (2 * S + 3 * C₀ * (2 * X * Real.exp (1 / K))) *
          (∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
            (((pSetD K P Q X).filter (fun x => nnD x = n)).card : ℝ) *
              (∑ x ∈ (pSetD K P Q X).filter (fun x => nnD x = n), ‖gamD b c P Q x‖ ^ 2) / (n : ℝ) ^ 2) := hmain
    _ ≤ (2 * S + 3 * C₀ * (2 * X * Real.exp (1 / K))) *
          (200000 / X * (1 / K + 1 / P) + 100 / (P * X)) := by
          apply mul_le_mul_of_nonneg_left henergy
          nlinarith [hS, hC0nn, hBpos]

end Work.BMF.mr_direct
