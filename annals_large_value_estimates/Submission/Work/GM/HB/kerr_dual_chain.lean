import Mathlib
import Submission.Work.GM.HB.hb_defs


namespace Work.GM.HB

open Finset
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

/-! ## Section 1: index bounds -/

lemma kdc_index_facts {N : ℕ} (hN : 1 ≤ N) {Δ : ℝ} (h100 : 100 * (N : ℝ) ≤ Δ) :
    1 ≤ A0 N Δ ∧ 2 * A0 N Δ ≤ M1 N Δ ∧ 4 * A0 N Δ ≤ M1 N Δ ∧
      2 * M1 N Δ ≤ B2 N Δ ∧ M1 N Δ ≤ B2 N Δ := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hΔpos : (0:ℝ) < Δ := by nlinarith
  obtain ⟨h1, -, -, h4, h5, h6, h7⟩ :=
    hbm_range_facts hN h100 (θ := Δ)
      (by rw [abs_of_nonneg hΔpos.le]) (by rw [abs_of_nonneg hΔpos.le]; linarith)
  exact ⟨h1, h4, h5, h6, h7⟩

lemma kdc_M1_pos {N : ℕ} (hN : 1 ≤ N) {Δ : ℝ} (hΔ : 1 ≤ Δ) : 1 ≤ M1 N Δ := by
  rw [M1]
  exact Nat.ceil_pos.mpr (by
    have : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
    positivity)

lemma kdc_A0_cast_le_delta {N : ℕ} (hN : 1 ≤ N) {Δ : ℝ} (h100 : 100 * (N : ℝ) ≤ Δ) :
    ((A0 N Δ : ℕ) : ℝ) ≤ Δ := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hΔ1 : (1:ℝ) ≤ Δ := by nlinarith
  have hlt : ((A0 N Δ : ℕ) : ℝ) < Δ / (4 * Real.pi * (N:ℝ)) + 1 := by
    rw [A0]; exact Nat.ceil_lt_add_one (by positivity)
  have hx4 : (4:ℝ) ≤ 4 * Real.pi * (N:ℝ) := by nlinarith [Real.pi_gt_three, hN1]
  have h2 : Δ / (4 * Real.pi * (N:ℝ)) ≤ Δ / 4 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hx4
  linarith

lemma kdc_four_A0_add_two_le {N : ℕ} (hN : 1 ≤ N) {Δ : ℝ} (h100 : 100 * (N : ℝ) ≤ Δ) :
    ((4 * A0 N Δ : ℕ) : ℝ) + 2 ≤ 6 * Δ := by
  have hΔ1 : (1:ℝ) ≤ Δ := by
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    nlinarith
  have h := kdc_A0_cast_le_delta hN h100
  push_cast
  linarith

lemma kdc_B2_add_two_le {N : ℕ} (hN : 1 ≤ N) {Δ : ℝ} (h100 : 100 * (N : ℝ) ≤ Δ) :
    ((B2 N Δ : ℕ) : ℝ) + 2 ≤ 6 * Δ := by
  have hΔ1 : (1:ℝ) ≤ Δ := by
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    nlinarith
  have h := B2_le_four_delta N hN hΔ1
  linarith

/-! ## Section 2: step D, splitting the `[A,4A]` block -/

lemma kdc_hbm_upper_bound (A : ℕ) (hA : 1 ≤ A) (θ : ℝ) :
    ‖hbm A (4*A) θ‖ ≤ ‖hbm A (2*A) θ‖ + ‖hbm (2*A) (4*A) θ‖ + 1 := by
  have h1 : hbm A (4*A) θ = hbm A (2*A) θ + hbm (2*A+1) (4*A) θ :=
    hbm_split (a := A) (b := 2*A) (c := 4*A) (by omega) (by omega) θ
  have h2 : hbm (2*A+1) (4*A) θ = hbm (2*A) (4*A) θ - hbm (2*A) (2*A) θ := by
    have h := hbm_split (a := 2*A) (b := 2*A) (c := 4*A) (by omega) (by omega) θ
    rw [h]; abel
  calc ‖hbm A (4*A) θ‖ = ‖hbm A (2*A) θ + hbm (2*A+1) (4*A) θ‖ := by rw [← h1]
    _ ≤ ‖hbm A (2*A) θ‖ + ‖hbm (2*A+1) (4*A) θ‖ := norm_add_le _ _
    _ = ‖hbm A (2*A) θ‖ + ‖hbm (2*A) (4*A) θ - hbm (2*A) (2*A) θ‖ := by rw [h2]
    _ ≤ ‖hbm A (2*A) θ‖ + (‖hbm (2*A) (4*A) θ‖ + ‖hbm (2*A) (2*A) θ‖) := by
        have := norm_sub_le (hbm (2*A) (4*A) θ) (hbm (2*A) (2*A) θ); linarith
    _ ≤ ‖hbm A (2*A) θ‖ + (‖hbm (2*A) (4*A) θ‖ + 1) := by
        have := hbm_single_norm_le (2*A) (by omega) θ; linarith
    _ = ‖hbm A (2*A) θ‖ + ‖hbm (2*A) (4*A) θ‖ + 1 := by ring

lemma kdc_hbm_sq_bound (A : ℕ) (hA : 1 ≤ A) (θ : ℝ) :
    ‖hbm A (4*A) θ‖ ^ 2 ≤ 3 * ‖hbm A (2*A) θ‖ ^ 2 + 3 * ‖hbm (2*A) (4*A) θ‖ ^ 2 + 3 := by
  set u := ‖hbm A (2*A) θ‖ with hu
  set v := ‖hbm (2*A) (4*A) θ‖ with hv
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have h := kdc_hbm_upper_bound A hA θ
  rw [← hu, ← hv] at h
  have hsq : ‖hbm A (4*A) θ‖ ^ 2 ≤ (u + v + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (u - v), sq_nonneg (u - 1), sq_nonneg (v - 1), hsq, hu0, hv0]

lemma kdc_winS_block_split (A : ℕ) (hA : 1 ≤ A) (W : ℝ) (R : ℕ) (t : Fin R → ℝ) :
    winS A (4*A) W R t ≤ 3 * winS A (2*A) W R t + 3 * winS (2*A) (4*A) W R t
      + 3 * pcount W R t := by
  unfold winS pcount
  have hterm : ∀ i j : Fin R,
      (if |t i - t j| ≤ W then ‖hbm A (4*A) (t i - t j)‖ ^ 2 else 0)
      ≤ 3 * (if |t i - t j| ≤ W then ‖hbm A (2*A) (t i - t j)‖ ^ 2 else 0)
        + 3 * (if |t i - t j| ≤ W then ‖hbm (2*A) (4*A) (t i - t j)‖ ^ 2 else 0)
        + 3 * (if |t i - t j| ≤ W then (1:ℝ) else 0) := by
    intro i j
    by_cases hc : |t i - t j| ≤ W
    · rw [if_pos hc, if_pos hc, if_pos hc, if_pos hc]
      linarith [kdc_hbm_sq_bound A hA (t i - t j)]
    · rw [if_neg hc, if_neg hc, if_neg hc, if_neg hc]; norm_num
  calc (∑ i, ∑ j, (if |t i - t j| ≤ W then ‖hbm A (4*A) (t i - t j)‖ ^ 2 else 0))
      ≤ ∑ i, ∑ j, (3 * (if |t i - t j| ≤ W then ‖hbm A (2*A) (t i - t j)‖ ^ 2 else 0)
          + 3 * (if |t i - t j| ≤ W then ‖hbm (2*A) (4*A) (t i - t j)‖ ^ 2 else 0)
          + 3 * (if |t i - t j| ≤ W then (1:ℝ) else 0)) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact hterm i j
    _ = 3 * (∑ i, ∑ j, (if |t i - t j| ≤ W then ‖hbm A (2*A) (t i - t j)‖ ^ 2 else 0))
        + 3 * (∑ i, ∑ j, (if |t i - t j| ≤ W then ‖hbm (2*A) (4*A) (t i - t j)‖ ^ 2 else 0))
        + 3 * (∑ i, ∑ j, (if |t i - t j| ≤ W then (1:ℝ) else 0)) :=
        hbm_sum2_add _ _ _ 3 3 3

/-! ## Section 3: step E, increasing the length -/

lemma kdc_winS_increase_length {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ (N M : ℕ), 1 ≤ N → 2 * N ≤ M → ∀ (W : ℝ), 1 ≤ W → ∀ (R : ℕ) (t : Fin R → ℝ),
      (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      winS N (2*N) W R t ≤ C * (M:ℝ) ^ ε * winS M (2*M) W R t := by
  obtain ⟨C, hC, h⟩ := Commons.NumberTheory.DirichletPolynomial.dirichlet_poly_increase_length ε hε
  refine ⟨C, hC, ?_⟩
  intro N M hN h2N W hW R t hsep
  have hkey := h N M hN h2N W hW 1 (by norm_num) (fun _ => (1:ℂ)) (fun n => by simp) R t hsep
  have hL : (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ W then
        ‖∑ n ∈ Finset.Icc N (2 * N), (1:ℂ) * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))
          / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2 else 0)) = winS N (2*N) W R t := by
    unfold winS hbm
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : |t i - t j| ≤ W <;> simp [hc]
  have hR : (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ W then
        ‖∑ n ∈ Finset.Icc M (2 * M), (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))
          / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2 else 0)) = winS M (2*M) W R t := by
    unfold winS hbm
    rfl
  rw [hL, hR] at hkey
  simpa using hkey

/-! ## Section 4: step F, localizing the `[M₁, 2M₁]` block into `[M₁, B₂]` -/

lemma kdc_winS_loc_reflect : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → 100 * (N : ℝ) ≤ Δ →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      winS (M1 N Δ) (2 * M1 N Δ) (2 * Δ) R t ≤
        C * (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2 * winS (M1 N Δ) (B2 N Δ) (2 * Δ) R t := by
  obtain ⟨C, hC, h⟩ := Commons.NumberTheory.DirichletPolynomial.smooth_range_localization_variable
  refine ⟨C, hC, ?_⟩
  intro N hN Δ hΔ h100 R t hsep
  obtain ⟨-, -, -, h2M, hAB⟩ := kdc_index_facts hN h100
  have hA := kdc_M1_pos hN hΔ
  have hW : 1 ≤ 2 * Δ := by linarith
  have hkey := h (M1 N Δ) (B2 N Δ) hA hAB R t hsep (2*Δ) hW
    (fun _ _ => M1 N Δ) (fun _ _ => 2 * M1 N Δ)
    (fun i j => ⟨le_refl _, by omega, h2M⟩)
  simpa [winS, hbm] using hkey

/-! ## Section 5: clamp bounds and step C (localization 1) -/

lemma kdc_clamp_ceil_le {N : ℕ} (hN : 1 ≤ N) {Δ θ : ℝ} (hθ : |θ| ≤ 2 * Δ) :
    Nat.ceil (|θ| / (4 * Real.pi * (N:ℝ))) ≤ 4 * A0 N Δ := by
  rw [Nat.ceil_le]
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hden : (0:ℝ) < 4 * Real.pi * (N:ℝ) := by positivity
  have h1 : |θ| / (4 * Real.pi * (N:ℝ)) ≤ 2 * Δ / (4 * Real.pi * (N:ℝ)) :=
    div_le_div_of_nonneg_right hθ hden.le
  have h2 : 2 * Δ / (4 * Real.pi * (N:ℝ)) = 2 * (Δ / (4 * Real.pi * (N:ℝ))) := by ring
  have h3 : Δ / (4 * Real.pi * (N:ℝ)) ≤ ((A0 N Δ : ℕ) : ℝ) := Nat.le_ceil _
  have h4 : 2 * ((A0 N Δ : ℕ) : ℝ) ≤ ((4 * A0 N Δ : ℕ) : ℝ) := by push_cast; linarith
  linarith

lemma kdc_clamp_floor_le {N : ℕ} (hN : 1 ≤ N) {Δ θ : ℝ} (hθ : |θ| ≤ 2 * Δ) :
    Nat.floor (|θ| / (2 * Real.pi * (N:ℝ))) ≤ 4 * A0 N Δ := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hden : (0:ℝ) < 2 * Real.pi * (N:ℝ) := by positivity
  have h1 : ((Nat.floor (|θ| / (2 * Real.pi * (N:ℝ))) : ℕ) : ℝ) ≤
      |θ| / (2 * Real.pi * (N:ℝ)) := Nat.floor_le (by positivity)
  have h2 : |θ| / (2 * Real.pi * (N:ℝ)) ≤ 4 * (Δ / (4 * Real.pi * (N:ℝ))) := by
    have hlt : |θ| / (2 * Real.pi * (N:ℝ)) ≤ 2 * Δ / (2 * Real.pi * (N:ℝ)) :=
      div_le_div_of_nonneg_right hθ hden.le
    have he : 2 * Δ / (2 * Real.pi * (N:ℝ)) = 4 * (Δ / (4 * Real.pi * (N:ℝ))) := by ring
    rw [← he]; exact hlt
  have h3 : Δ / (4 * Real.pi * (N:ℝ)) ≤ ((A0 N Δ : ℕ) : ℝ) := Nat.le_ceil _
  have h4 : 4 * ((A0 N Δ : ℕ) : ℝ) = ((4 * A0 N Δ : ℕ) : ℝ) := by push_cast; ring
  have h5 : ((Nat.floor (|θ| / (2 * Real.pi * (N:ℝ))) : ℕ) : ℝ) ≤ ((4 * A0 N Δ : ℕ) : ℝ) := by
    rw [← h4]; linarith
  exact_mod_cast h5

lemma kdc_annDual_le_loc : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → 100 * (N : ℝ) ≤ Δ →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      annDual N Δ R t ≤ C * (Real.log (((4 * A0 N Δ : ℕ) : ℝ) + 2)) ^ 2 *
        winS (A0 N Δ) (4 * A0 N Δ) (2 * Δ) R t := by
  obtain ⟨C, hC, h⟩ := Commons.NumberTheory.DirichletPolynomial.smooth_range_localization_variable
  refine ⟨C, hC, ?_⟩
  intro N hN Δ hΔ h100 R t hsep
  have hA0 : 1 ≤ A0 N Δ := (kdc_index_facts hN h100).1
  have h4A0 : A0 N Δ ≤ 4 * A0 N Δ := by omega
  have hW : 1 ≤ 2 * Δ := by linarith
  set a : Fin R → Fin R → ℕ := fun i j =>
    if |t i - t j| ≤ 2 * Δ then max (A0 N Δ) (Nat.ceil (|t i - t j| / (4 * Real.pi * (N:ℝ))))
    else A0 N Δ with ha
  set b : Fin R → Fin R → ℕ := fun i j =>
    if |t i - t j| ≤ 2 * Δ then max (a i j) (Nat.floor (|t i - t j| / (2 * Real.pi * (N:ℝ))))
    else A0 N Δ with hb
  have hab : ∀ i j : Fin R, A0 N Δ ≤ a i j ∧ a i j ≤ b i j ∧ b i j ≤ 4 * A0 N Δ := by
    intro i j
    by_cases hc : |t i - t j| ≤ 2 * Δ
    · have hcl := kdc_clamp_ceil_le hN hc
      have hfl := kdc_clamp_floor_le hN hc
      have hae : a i j = max (A0 N Δ) (Nat.ceil (|t i - t j| / (4 * Real.pi * (N:ℝ)))) := by
        rw [ha]; simp only [if_pos hc]
      have hbe : b i j = max (max (A0 N Δ) (Nat.ceil (|t i - t j| / (4 * Real.pi * (N:ℝ)))))
          (Nat.floor (|t i - t j| / (2 * Real.pi * (N:ℝ)))) := by
        rw [hb]; simp only [if_pos hc, hae]
      rw [hae, hbe]
      exact ⟨le_max_left _ _, le_max_left _ _, max_le (max_le (by omega) hcl) hfl⟩
    · have hae : a i j = A0 N Δ := by rw [ha]; simp only [if_neg hc]
      have hbe : b i j = A0 N Δ := by rw [hb]; simp only [if_neg hc, hae]
      rw [hae, hbe]
      exact ⟨le_rfl, le_rfl, by omega⟩
  have hloc := h (A0 N Δ) (4 * A0 N Δ) hA0 h4A0 R t hsep (2 * Δ) hW a b hab
  refine le_trans ?_ hloc
  unfold annDual
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  by_cases hc : Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ
  · rw [if_pos hc, if_pos hc.2]
    have h2 : A0 N Δ ≤ Nat.ceil (|t i - t j| / (4 * Real.pi * (N:ℝ))) :=
      (hbm_range_facts hN h100 hc.1 hc.2).2.1
    have hae : a i j = Nat.ceil (|t i - t j| / (4 * Real.pi * (N:ℝ))) := by
      rw [ha]; simp only [if_pos hc.2, max_eq_right h2]
    have hbe : b i j = max (Nat.ceil (|t i - t j| / (4 * Real.pi * (N:ℝ))))
        (Nat.floor (|t i - t j| / (2 * Real.pi * (N:ℝ)))) := by
      rw [hb]; simp only [if_pos hc.2, hae]
    rw [hae, hbe]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbm_sub_le _ _ _) 2
  · rw [if_neg hc]
    by_cases h2 : |t i - t j| ≤ 2 * Δ
    · rw [if_pos h2]; positivity
    · rw [if_neg h2]

/-! ## Section 6: steps D + E + F combined -/

lemma kdc_log_B2_ge_one {N : ℕ} (hN : 1 ≤ N) {Δ : ℝ} (h100 : 100 * (N : ℝ) ≤ Δ) :
    1 ≤ (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2 := by
  have hΔpos : (0:ℝ) < Δ := by
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    nlinarith
  have hB2 : 2 ≤ B2 N Δ := by
    rw [B2]
    have : 1 ≤ Nat.ceil (Δ / (N:ℝ)) := Nat.ceil_pos.mpr (by positivity)
    omega
  have hle : (4:ℝ) ≤ ((B2 N Δ : ℕ) : ℝ) + 2 := by
    have : (2:ℝ) ≤ ((B2 N Δ : ℕ) : ℝ) := by exact_mod_cast hB2
    linarith
  have hlog4 : (1:ℝ) ≤ Real.log (((B2 N Δ : ℕ) : ℝ) + 2) := by
    have h1 : Real.log 4 ≤ Real.log (((B2 N Δ : ℕ) : ℝ) + 2) :=
      Real.log_le_log (by norm_num) hle
    have h2 : (1:ℝ) ≤ Real.log 4 := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      have := Real.log_two_gt_d9
      linarith
    linarith
  nlinarith [hlog4]

lemma kdc_winS_reflect (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → 100 * (N : ℝ) ≤ Δ →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      winS (A0 N Δ) (4 * A0 N Δ) (2 * Δ) R t ≤
        C * (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2 * ((M1 N Δ : ℕ) : ℝ) ^ ε *
          (winS (M1 N Δ) (B2 N Δ) (2 * Δ) R t + pcount (2 * Δ) R t) := by
  obtain ⟨C1, hC1, hlocF⟩ := kdc_winS_loc_reflect
  obtain ⟨C2, hC2, hinc⟩ := kdc_winS_increase_length hε
  refine ⟨6 * C2 * C1 + 3, by positivity, ?_⟩
  intro N hN Δ hΔ h100 R t hsep
  obtain ⟨hA0, h2A0, h4A0, h2M, hAB⟩ := kdc_index_facts hN h100
  have hM1 : 1 ≤ M1 N Δ := kdc_M1_pos hN hΔ
  have hW : 1 ≤ 2 * Δ := by linarith
  have hsplit := kdc_winS_block_split (A0 N Δ) hA0 (2 * Δ) R t
  have hi1 := hinc (A0 N Δ) (M1 N Δ) hA0 h2A0 (2 * Δ) hW R t hsep
  have hi2 := hinc (2 * A0 N Δ) (M1 N Δ) (by omega) (by omega) (2 * Δ) hW R t hsep
  have h4A : 2 * (2 * A0 N Δ) = 4 * A0 N Δ := by ring
  rw [h4A] at hi2
  have hlf := hlocF N hN Δ hΔ h100 R t hsep
  set lg : ℝ := (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2 with hlg
  set me : ℝ := ((M1 N Δ : ℕ) : ℝ) ^ ε with hme
  set X : ℝ := winS (M1 N Δ) (B2 N Δ) (2 * Δ) R t + pcount (2 * Δ) R t with hX
  have hWBnn : 0 ≤ winS (M1 N Δ) (B2 N Δ) (2 * Δ) R t := winS_nonneg _ _ _ _ _
  have hpcnn : 0 ≤ pcount (2 * Δ) R t := pcount_nonneg (2 * Δ) R t
  have hXnn : 0 ≤ X := by rw [hX]; linarith
  have hmenn : 0 ≤ me := by rw [hme]; positivity
  have hlgnn : 0 ≤ lg := by rw [hlg]; positivity
  have hlg1 : 1 ≤ lg := kdc_log_B2_ge_one hN h100
  have hme1 : 1 ≤ me := by
    rw [hme]
    exact Real.one_le_rpow (by exact_mod_cast hM1) hε.le
  have hi1' : winS (A0 N Δ) (2 * A0 N Δ) (2 * Δ) R t
      ≤ C2 * me * winS (M1 N Δ) (2 * M1 N Δ) (2 * Δ) R t := by
    simpa only [hme] using hi1
  have hi2' : winS (2 * A0 N Δ) (4 * A0 N Δ) (2 * Δ) R t
      ≤ C2 * me * winS (M1 N Δ) (2 * M1 N Δ) (2 * Δ) R t := by
    simpa only [hme] using hi2
  have hlf' : winS (M1 N Δ) (2 * M1 N Δ) (2 * Δ) R t
      ≤ C1 * lg * winS (M1 N Δ) (B2 N Δ) (2 * Δ) R t := by
    simpa only [hlg] using hlf
  have h4 : winS (M1 N Δ) (2 * M1 N Δ) (2 * Δ) R t ≤ C1 * lg * X := by
    refine le_trans hlf' ?_
    have hXe : winS (M1 N Δ) (B2 N Δ) (2 * Δ) R t ≤ X := by rw [hX]; linarith
    exact mul_le_mul_of_nonneg_left hXe (by positivity)
  have h5 : winS (A0 N Δ) (4 * A0 N Δ) (2 * Δ) R t
      ≤ 3 * (C2 * me * (C1 * lg * X)) + 3 * (C2 * me * (C1 * lg * X)) + 3 * pcount (2 * Δ) R t := by
    have ha : 3 * winS (A0 N Δ) (2 * A0 N Δ) (2 * Δ) R t ≤ 3 * (C2 * me * (C1 * lg * X)) := by
      have h1 : C2 * me * winS (M1 N Δ) (2 * M1 N Δ) (2 * Δ) R t ≤ C2 * me * (C1 * lg * X) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      exact mul_le_mul_of_nonneg_left (le_trans hi1' h1) (by norm_num)
    have hb : 3 * winS (2 * A0 N Δ) (4 * A0 N Δ) (2 * Δ) R t ≤ 3 * (C2 * me * (C1 * lg * X)) := by
      have h1 : C2 * me * winS (M1 N Δ) (2 * M1 N Δ) (2 * Δ) R t ≤ C2 * me * (C1 * lg * X) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      exact mul_le_mul_of_nonneg_left (le_trans hi2' h1) (by norm_num)
    linarith [hsplit, ha, hb]
  have h6 : 3 * (C2 * me * (C1 * lg * X)) + 3 * (C2 * me * (C1 * lg * X)) + 3 * pcount (2 * Δ) R t
      ≤ (6 * C2 * C1 + 3) * lg * me * X := by
    have hpX : pcount (2 * Δ) R t ≤ X := by rw [hX]; linarith
    have h6b : 3 * (C2 * me * (C1 * lg * X)) + 3 * (C2 * me * (C1 * lg * X))
        = 6 * C2 * C1 * lg * me * X := by ring
    have h6a : 3 * pcount (2 * Δ) R t ≤ 3 * (lg * me * X) := by
      have h1 : 1 ≤ lg * me := by nlinarith [hlg1, hme1]
      have h2 : X ≤ lg * me * X := by nlinarith [h1, hXnn]
      linarith [hpX, h2]
    have h6c : (6 * C2 * C1 + 3) * lg * me * X
        = 6 * C2 * C1 * lg * me * X + 3 * (lg * me * X) := by ring
    linarith [h6b, h6a, h6c]
  have hgoal : winS (A0 N Δ) (4 * A0 N Δ) (2 * Δ) R t ≤ (6 * C2 * C1 + 3) * lg * me * X :=
    le_trans h5 h6
  rw [hX, hlg, hme] at hgoal
  exact hgoal

/-! ## Section 7: absorbing the logs and `M₁^η` -/

lemma kdc_absorb (ε η : ℝ) (_hε : 0 < ε) (hη : 0 < η) (hηε : 3 * η ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → 100 * (N : ℝ) ≤ Δ →
      (Real.log (((4 * A0 N Δ : ℕ) : ℝ) + 2)) ^ 2 *
        (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2 *
          ((M1 N Δ : ℕ) : ℝ) ^ η ≤ C * Δ ^ ε := by
  obtain ⟨C2, hC2, hlog⟩ := log_sq_le_rpow hη
  refine ⟨C2 * (6:ℝ) ^ η * C2 * (6:ℝ) ^ η * (2:ℝ) ^ η, by positivity, ?_⟩
  intro N hN Δ hΔ h100
  have hΔpos : (0:ℝ) < Δ := by linarith
  have hΔ1 : (1:ℝ) ≤ Δ := hΔ
  have hA := kdc_four_A0_add_two_le hN h100
  have hB := kdc_B2_add_two_le hN h100
  have hM := M1_le_two_delta N hN hΔ
  have hA3 : 3 ≤ ((4 * A0 N Δ : ℕ) : ℝ) + 2 := by
    have h1 := (kdc_index_facts hN h100).1
    have : (1:ℝ) ≤ ((A0 N Δ : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast
    linarith
  have hB3 : 3 ≤ ((B2 N Δ : ℕ) : ℝ) + 2 := by
    have h1 : 2 ≤ B2 N Δ := by
      rw [B2]
      have : 1 ≤ Nat.ceil (Δ / (N:ℝ)) := Nat.ceil_pos.mpr (by positivity)
      omega
    have : (2:ℝ) ≤ ((B2 N Δ : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hAe : (Real.log (((4 * A0 N Δ : ℕ) : ℝ) + 2)) ^ 2
      ≤ C2 * (6:ℝ) ^ η * Δ ^ η := by
    have h1 := hlog (((4 * A0 N Δ : ℕ) : ℝ) + 2) hA3
    have h2 : (((4 * A0 N Δ : ℕ) : ℝ) + 2) ^ η ≤ (6 * Δ) ^ η :=
      Real.rpow_le_rpow (by linarith) hA hη.le
    have h3 : (6 * Δ) ^ η = (6:ℝ) ^ η * Δ ^ η := Real.mul_rpow (by norm_num) hΔpos.le
    calc (Real.log (((4 * A0 N Δ : ℕ) : ℝ) + 2)) ^ 2
        ≤ C2 * (((4 * A0 N Δ : ℕ) : ℝ) + 2) ^ η := h1
      _ ≤ C2 * (6 * Δ) ^ η := mul_le_mul_of_nonneg_left h2 hC2.le
      _ = C2 * (6:ℝ) ^ η * Δ ^ η := by rw [h3]; ring
  have hBe : (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2 ≤ C2 * (6:ℝ) ^ η * Δ ^ η := by
    have h1 := hlog (((B2 N Δ : ℕ) : ℝ) + 2) hB3
    have h2 : (((B2 N Δ : ℕ) : ℝ) + 2) ^ η ≤ (6 * Δ) ^ η :=
      Real.rpow_le_rpow (by linarith) hB hη.le
    have h3 : (6 * Δ) ^ η = (6:ℝ) ^ η * Δ ^ η := Real.mul_rpow (by norm_num) hΔpos.le
    calc (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2
        ≤ C2 * (((B2 N Δ : ℕ) : ℝ) + 2) ^ η := h1
      _ ≤ C2 * (6 * Δ) ^ η := mul_le_mul_of_nonneg_left h2 hC2.le
      _ = C2 * (6:ℝ) ^ η * Δ ^ η := by rw [h3]; ring
  have hMe : ((M1 N Δ : ℕ) : ℝ) ^ η ≤ (2:ℝ) ^ η * Δ ^ η := by
    have h1 : ((M1 N Δ : ℕ) : ℝ) ^ η ≤ (2 * Δ) ^ η :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hM hη.le
    rwa [Real.mul_rpow (by norm_num) hΔpos.le] at h1
  have hpow : Δ ^ (3 * η) ≤ Δ ^ ε := Real.rpow_le_rpow_of_exponent_le hΔ1 hηε
  have hfin : (Real.log (((4 * A0 N Δ : ℕ) : ℝ) + 2)) ^ 2 *
      (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2 * ((M1 N Δ : ℕ) : ℝ) ^ η
      ≤ (C2 * (6:ℝ) ^ η * Δ ^ η) * (C2 * (6:ℝ) ^ η * Δ ^ η) * ((2:ℝ) ^ η * Δ ^ η) := by
    have hnn2 : 0 ≤ (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2 := by positivity
    have hnn3 : 0 ≤ ((M1 N Δ : ℕ) : ℝ) ^ η := by positivity
    have hx : (Real.log (((4 * A0 N Δ : ℕ) : ℝ) + 2)) ^ 2 *
        (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2
        ≤ (C2 * (6:ℝ) ^ η * Δ ^ η) * (C2 * (6:ℝ) ^ η * Δ ^ η) :=
      mul_le_mul hAe hBe hnn2 (by positivity)
    exact mul_le_mul hx hMe hnn3 (by positivity)
  have hconst : (C2 * (6:ℝ) ^ η * Δ ^ η) * (C2 * (6:ℝ) ^ η * Δ ^ η) * ((2:ℝ) ^ η * Δ ^ η)
      = (C2 * (6:ℝ) ^ η * C2 * (6:ℝ) ^ η * (2:ℝ) ^ η) * Δ ^ (3 * η) := by
    rw [show (3:ℝ) * η = η + η + η by ring, Real.rpow_add hΔpos, Real.rpow_add hΔpos]
    ring
  calc (Real.log (((4 * A0 N Δ : ℕ) : ℝ) + 2)) ^ 2 *
        (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2 * ((M1 N Δ : ℕ) : ℝ) ^ η
      ≤ (C2 * (6:ℝ) ^ η * Δ ^ η) * (C2 * (6:ℝ) ^ η * Δ ^ η) * ((2:ℝ) ^ η * Δ ^ η) := hfin
    _ = (C2 * (6:ℝ) ^ η * C2 * (6:ℝ) ^ η * (2:ℝ) ^ η) * Δ ^ (3 * η) := hconst
    _ ≤ (C2 * (6:ℝ) ^ η * C2 * (6:ℝ) ^ η * (2:ℝ) ^ η) * Δ ^ ε :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

/-! ## Section 8: the assembly -/

/-- **Kerr's `lem:main1`, main regime `Δ ≥ 100N`, dual form.** The honest dual (reflected) annulus sum at scale `N` is dominated by the windowed difference sum over the reflected block `[M₁, B₂] = [⌈Δ/(2N)⌉, 2⌈Δ/N⌉]` plus the number of pairs. Proven by the recipe (steps B–G) in the `PROOF RECIPE` block of `Submission/Work/GM/HB/hb_defs.lean`. -/
theorem kerr_dual_chain : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → 100 * (N : ℝ) ≤ Δ →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      Work.GM.HB.annDual N Δ R t ≤ K * Δ ^ ε *
        (Work.GM.HB.winS (Work.GM.HB.M1 N Δ) (Work.GM.HB.B2 N Δ) (2 * Δ) R t
          + Work.GM.HB.pcount (2 * Δ) R t) := by
  intro ε hε
  obtain ⟨C1, hC1, hloc⟩ := kdc_annDual_le_loc
  obtain ⟨C4, hC4, href⟩ := kdc_winS_reflect (ε / 4) (by linarith)
  obtain ⟨Ca, hCa, habs⟩ := kdc_absorb ε (ε / 4) hε (by linarith) (by linarith)
  refine ⟨C1 * C4 * Ca + 1, by positivity, ?_⟩
  intro N hN Δ hΔ h100 R t hsep
  have h1 := hloc N hN Δ hΔ h100 R t hsep
  have h2 := href N hN Δ hΔ h100 R t hsep
  have h3 := habs N hN Δ hΔ h100
  set L4 : ℝ := (Real.log (((4 * A0 N Δ : ℕ) : ℝ) + 2)) ^ 2 with hL4
  set LB : ℝ := (Real.log (((B2 N Δ : ℕ) : ℝ) + 2)) ^ 2 with hLB
  set me : ℝ := ((M1 N Δ : ℕ) : ℝ) ^ (ε / 4) with hme
  set X : ℝ := winS (M1 N Δ) (B2 N Δ) (2 * Δ) R t + pcount (2 * Δ) R t with hX
  have hXnn : 0 ≤ X := by
    rw [hX]
    have h4 := winS_nonneg (M1 N Δ) (B2 N Δ) (2 * Δ) R t
    have h5 := pcount_nonneg (2 * Δ) R t
    linarith
  have h1' : annDual N Δ R t ≤ C1 * L4 * winS (A0 N Δ) (4 * A0 N Δ) (2 * Δ) R t := by
    simpa only [hL4] using h1
  have h2' : winS (A0 N Δ) (4 * A0 N Δ) (2 * Δ) R t ≤ (C4 * LB * me) * X := by
    simpa only [hLB, hme, hX] using h2
  have h3' : L4 * LB * me ≤ Ca * Δ ^ ε := by
    simpa only [hL4, hLB, hme] using h3
  have hDnn : 0 ≤ Δ ^ ε := Real.rpow_nonneg (by linarith) ε
  have hstep : annDual N Δ R t ≤ C1 * C4 * Ca * Δ ^ ε * X := by
    have hA : annDual N Δ R t ≤ C1 * L4 * ((C4 * LB * me) * X) :=
      le_trans h1' (mul_le_mul_of_nonneg_left h2' (by positivity))
    have hB : C1 * L4 * ((C4 * LB * me) * X) = C1 * C4 * (L4 * LB * me) * X := by ring
    have hC : C1 * C4 * (L4 * LB * me) * X ≤ C1 * C4 * (Ca * Δ ^ ε) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3' (by positivity)) hXnn
    have hD : C1 * C4 * (Ca * Δ ^ ε) * X = C1 * C4 * Ca * Δ ^ ε * X := by ring
    linarith [hA, hB.le, hD.le, hC]
  have hfin : C1 * C4 * Ca * Δ ^ ε * X ≤ (C1 * C4 * Ca + 1) * Δ ^ ε * X := by
    have hnn : 0 ≤ Δ ^ ε * X := mul_nonneg hDnn hXnn
    nlinarith [hnn]
  have hfinal : annDual N Δ R t ≤ (C1 * C4 * Ca + 1) * Δ ^ ε *
      (winS (M1 N Δ) (B2 N Δ) (2 * Δ) R t + pcount (2 * Δ) R t) := by
    rw [← hX]
    exact le_trans hstep hfin
  exact hfinal

end
end Work.GM.HB
