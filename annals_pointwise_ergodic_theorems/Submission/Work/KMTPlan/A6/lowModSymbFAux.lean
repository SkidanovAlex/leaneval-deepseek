/-
# Elementary facts for the modified KMT bumps `varphiNtj` and the randomised-symbol bound

This module collects the pieces shared by the target
`Submission/Work/KMTPlan/A6/lowModRandL2Fh.lean` (the `ℓ²`-bound for the randomised `f`-side
packets of Case B of the small-scale model estimate of area A6) and by the two delegated
total-variation bounds `varphiNtj_varBound_kpos` / `varphiNtj_varBound_k0j1`:

* the two modulus bounds for the scaled frequency variable `2^{-k}Nx` on the support of `φ_{N,k}`
  (`abs_z_le_two`, `one_eight_le_abs_z`);
* the resulting pointwise bound `‖φ_{N,k,j}(t,·)‖ ≤ 8` for the twists `j ∈ {-1,0,1}` of the paper
  (`norm_varphiNtj_le_eight`);
* the (elementary) support facts `varphiNt_ne_zero_of_varphiNtj_ne_zero`,
  `varphiN_ne_zero_of_varphiNtj_ne_zero` and measurability `measurable_varphiNtj'`;
* the anchored clamped family `lowModSymbF` of Case B: its support (`support_lowModSymbF`) and
  measurability (`measurable_lowModSymbF`);
* `randSymb_bounded_of_varBound_mod`, the family-generic form of
  `Work.KMTPlan.A6.randSymb_bounded_of_varBound` (same proof, with the pointwise bound `Cb` of the
  family as a parameter instead of the hard-wired `‖varphiNt‖ ≤ 1`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowModelVarCaseBAux
import Submission.Work.KMTPlan.A6.randSymb_sup_le_of_lipschitz
import Submission.Work.KMTPlan.A6.tmRandSymb_l2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTContract
open Work.KMTAreas.A7
open Work.Analysis.EndVar

noncomputable section

/-! ## The modulus of the scaled frequency variable -/

/-- `‖z‖ = |z|` for a real number viewed as a complex number. -/
theorem aux_norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

/-- The scaled variable `2^{-k}Nx` written as a product of the `N`-independent factor
`N · 2^{-Log N}` and the scaled variable `2^{Log N - k}x`. -/
theorem abs_z_eq (N k : ℕ) (x : ℝ) :
    (2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x
      = ((N : ℝ) * (2 : ℝ) ^ (-(logN N : ℝ)))
          * ((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * x) := by
  have hBC : (2 : ℝ) ^ (-(k : ℝ))
      = (2 : ℝ) ^ (-(logN N : ℝ)) * (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hBC]; ring

/-- The same, in modulus. -/
theorem abs_z_eq_abs (N k : ℕ) (x : ℝ) :
    |(2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x|
      = ((N : ℝ) * (2 : ℝ) ^ (-(logN N : ℝ)))
          * |(2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * x| := by
  rw [abs_z_eq, abs_mul, abs_of_nonneg (by positivity)]

/-- On the support of `φ_{N,k}` the scaled variable `2^{-k}Nx` has modulus at most `2`. -/
theorem abs_z_le_two {N k : ℕ} (hN : 1 ≤ N) {x : ℝ} (h : varphiN N k x ≠ 0) :
    |(2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x| ≤ 2 := by
  have hle : |(2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * x| ≤ 1 := varphiN_ne_zero_le N k x h
  rw [abs_z_eq_abs]
  have hA : (0 : ℝ) ≤ (N : ℝ) * (2 : ℝ) ^ (-(logN N : ℝ)) := by positivity
  have hstep : (N : ℝ) * (2 : ℝ) ^ (-(logN N : ℝ))
        * |(2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * x|
      ≤ (N : ℝ) * (2 : ℝ) ^ (-(logN N : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hle hA
    simpa only [mul_one] using h1
  have h2 : (N : ℝ) * (2 : ℝ) ^ (-(logN N : ℝ)) < 2 := by
    have hNlt : (N : ℝ) < 2 * (2 : ℝ) ^ ((logN N : ℝ)) := nat_lt_two_mul_two_pow_logN N
    have hp : (0 : ℝ) < (2 : ℝ) ^ (-(logN N : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h3 := mul_lt_mul_of_pos_right hNlt hp
    have h1 : (2 : ℝ) ^ ((logN N : ℝ)) * (2 : ℝ) ^ (-(logN N : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp
    calc (N : ℝ) * (2 : ℝ) ^ (-(logN N : ℝ))
        < (2 * (2 : ℝ) ^ ((logN N : ℝ))) * (2 : ℝ) ^ (-(logN N : ℝ)) := h3
      _ = 2 * ((2 : ℝ) ^ ((logN N : ℝ)) * (2 : ℝ) ^ (-(logN N : ℝ))) := by ring
      _ = 2 := by rw [h1, mul_one]
  linarith

/-- On the support of `φ_{N,k}` with `1 ≤ k` the scaled variable `2^{-k}Nx` has modulus at least
`1/8`. -/
theorem one_eight_le_abs_z {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) {x : ℝ}
    (h : varphiN N k x ≠ 0) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x| := by
  have hann' : (1 : ℝ) / 4 < (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * |x| :=
    (varphiN_supp_annulus hk h).1
  have hann : (1 : ℝ) / 4 < |(2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * x| := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)]
    exact hann'
  rw [abs_z_eq_abs]
  have hNle : (2 : ℝ) ^ ((logN N : ℝ)) ≤ 2 * (N : ℝ) := two_pow_logN_le_two_mul_N hN
  have hA : (0 : ℝ) ≤ (N : ℝ) * (2 : ℝ) ^ (-(logN N : ℝ)) := by positivity
  have h1 : (1 : ℝ) / 2 ≤ (N : ℝ) * (2 : ℝ) ^ (-(logN N : ℝ)) := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ (-(logN N : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (2 : ℝ) ^ ((logN N : ℝ)) * (2 : ℝ) ^ (-(logN N : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp
    have h3 := mul_le_mul_of_nonneg_right hNle hp.le
    rw [h2] at h3
    linarith [h3]
  have hstep : (1 : ℝ) / 2 * (1 / 4)
      ≤ (N : ℝ) * (2 : ℝ) ^ (-(logN N : ℝ))
        * |(2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * x| :=
    mul_le_mul h1 (le_of_lt hann) (by norm_num) hA
  linarith

/-! ## The pointwise bound of the modified bump -/

/-- **The modified bump is bounded by `8`.**  For the twists used by the paper
(`j ∈ {-1,0,1}`, with `(k,j) ≠ (0,-1)`) the factor `(2^{-k}Nξ)^j` has modulus at most `2` on the
support of `φ_{N,k}` (`abs_z_le_two` for `j ≥ 0`, `one_eight_le_abs_z` for `j = -1`, where
`1 ≤ k` is forced), and the modulated bump itself is bounded by `1`. -/
theorem norm_varphiNtj_le_eight (N k : ℕ) (j : ℤ) (hj : j ∈ ({-1, 0, 1} : Finset ℤ))
    (hk : k ≠ 0 ∨ 0 ≤ j) (hN : 1 ≤ N) (t x : ℝ) :
    ‖varphiNtj N k j t x‖ ≤ 8 := by
  have hj' : j = -1 ∨ j = 0 ∨ j = 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hj
  rcases hj' with rfl | rfl | rfl
  · have hk1 : 1 ≤ k := by rcases hk with h | h <;> omega
    by_cases hz : varphiNt N k t x = 0
    · rw [varphiNtj, hz, mul_zero, norm_zero]; norm_num
    · have hphi : varphiN N k x ≠ 0 := fun hc => hz (by rw [varphiNt, hc, zero_mul])
      have hzge := one_eight_le_abs_z hN hk1 hphi
      have hpos : (0 : ℝ) < |(2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x| :=
        lt_of_lt_of_le (by norm_num) hzge
      have h3 : (|(2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x|)⁻¹ ≤ 8 := by
        have h4 := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < (1 : ℝ) / 8)).mpr hzge
        have h5 : ((1 : ℝ) / 8)⁻¹ = 8 := by norm_num
        rwa [h5] at h4
      rw [varphiNtj, zpow_neg_one, norm_mul, norm_inv, aux_norm_ofReal]
      calc (|(2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x|)⁻¹ * ‖varphiNt N k t x‖
          ≤ 8 * 1 := mul_le_mul h3 (varphiNt_norm_le_one N k t x) (norm_nonneg _) (by norm_num)
        _ ≤ 8 := by norm_num
  · rw [varphiNtj_zero]
    exact le_trans (varphiNt_norm_le_one N k t x) (by norm_num)
  · by_cases hz : varphiNt N k t x = 0
    · rw [varphiNtj, hz, mul_zero, norm_zero]; norm_num
    · have hphi : varphiN N k x ≠ 0 := fun hc => hz (by rw [varphiNt, hc, zero_mul])
      have hzle := abs_z_le_two hN hphi
      rw [varphiNtj, zpow_one, norm_mul, aux_norm_ofReal]
      calc |(2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x| * ‖varphiNt N k t x‖
          ≤ 2 * 1 := mul_le_mul hzle (varphiNt_norm_le_one N k t x) (norm_nonneg _) (by norm_num)
        _ ≤ 8 := by norm_num

/-! ## Support and measurability of the modified bump -/

theorem varphiNt_ne_zero_of_varphiNtj_ne_zero (N k : ℕ) (j : ℤ) (t x : ℝ)
    (h : varphiNtj N k j t x ≠ 0) : varphiNt N k t x ≠ 0 := by
  intro h0
  exact h (by rw [varphiNtj, h0, mul_zero])

theorem varphiN_ne_zero_of_varphiNtj_ne_zero (N k : ℕ) (j : ℤ) (t x : ℝ)
    (h : varphiNtj N k j t x ≠ 0) : varphiN N k x ≠ 0 := by
  intro h0
  exact varphiNt_ne_zero_of_varphiNtj_ne_zero N k j t x h (by rw [varphiNt, h0, zero_mul])

/-- The modified bump `varphiNtj N k j t` is measurable in its frequency variable. -/
theorem measurable_varphiNtj' (N k : ℕ) (j : ℤ) (t : ℝ) : Measurable (varphiNtj N k j t) := by
  have hφ : Measurable (varphiN N k) := (contDiff_varphiN N k).continuous.measurable
  have hee : Measurable (fun ξ : ℝ => ee ((N : ℝ) * t * ξ)) :=
    (contDiff_ee_const_mul 1 ((N : ℝ) * t)).continuous.measurable
  have hpow : Measurable (fun ξ : ℝ =>
      ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ) ^ j) := by fun_prop
  exact hpow.mul (hφ.mul hee)

/-! ## Support and measurability of the anchored clamped family -/

/-- A nonzero value of the anchored clamped `f`-side family of Case B forces `n ≠ 0`, the clamping
predicate `lowSmallSet`, and a nonzero value of the modified bump. -/
theorem support_lowModSymbF {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ n : ℕ} {j : ℤ}
    {t x : ℝ}
    (h : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t n x ≠ 0) :
    n ≠ 0 ∧ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n ∧
      varphiNtj (Nat.floor (a n)) k₁ j t x ≠ 0 := by
  simp only [lowModSymbF] at h
  by_cases h0 : n = 0
  · rw [if_pos h0] at h; exact absurd rfl h
  · rw [if_neg h0] at h
    by_cases hc : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · rw [if_pos hc] at h; exact ⟨h0, hc, h⟩
    · rw [if_neg hc] at h; exact absurd rfl h

/-- Every member of the anchored clamped `f`-side family of Case B is measurable. -/
theorem measurable_lowModSymbF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (j : ℤ) (t : ℝ) (m : ℕ) :
    Measurable (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t m) := by
  change Measurable (fun ξ : ℝ => if m = 0 then 0
    else if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m
      then varphiNtj (Nat.floor (a m)) k₁ j t ξ else 0)
  by_cases h0 : m = 0
  · simp only [if_pos h0]; exact measurable_const
  · simp only [if_neg h0]
    by_cases hc : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m
    · simp only [if_pos hc]
      exact measurable_varphiNtj' _ _ _ _
    · simp only [if_neg hc]; exact measurable_const

/-! ## The family-generic randomised-symbol bound -/

/-- **The randomised symbol of the clamped lacunary family `Φ` is bounded by the total variation of
`Φ` plus twice the pointwise bound `Cb` of `Φ`** (the two jumps of the order-convex index set
`lowSmallSet`).  This is `Work.KMTPlan.A6.randSymb_bounded_of_varBound` with the hard-wired bump
`varphiNt` and its bound `1` replaced by an arbitrary family `Φ` with bound `Cb`. -/
theorem randSymb_bounded_of_varBound_mod (Λ : NNReal) (hΛ : 1 < Λ) (C₀ : ℕ) (Cb Cv : ℝ)
    (hCb0 : 0 ≤ Cb) (Φ : ℕ → ℝ → ℂ) (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ)
    (ε : ℕ → ℂ) (x : ℝ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (hε : ∀ n, ‖ε n‖ ≤ 1)
    (hvar : ∑ n ∈ Finset.range K, ‖Φ (n + 1) x - Φ n x‖ ≤ Cv)
    (hΦb : ∀ n, ‖Φ n x‖ ≤ Cb) :
    ‖Work.KMTAreas.A7.randSymb
      (fun n ξ => if n = 0 then 0
        else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then Φ n ξ else 0) ε K x‖
      ≤ Cv + 2 * Cb := by
  classical
  set T : Set ℕ := {n : ℕ | n ≠ 0 ∧ Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n}
    with hT
  set d : ℕ → ℂ := fun n => Φ n x with hd
  set c : ℕ → ℂ := fun n => if n ∈ T then d n else 0 with hc
  have hsym : (Work.KMTAreas.A7.randSymb
      (fun n ξ => if n = 0 then 0
        else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then Φ n ξ else 0) ε K) x
      = ∑ n ∈ Finset.range K, ε n * (c (n + 1) - c n) := by
    simp only [Work.KMTAreas.A7.randSymb]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    simp only [hc, hd, hT, Set.mem_setOf_eq]
    by_cases h : n = 0 <;> simp [h]
  have hconv : ∀ {n j m : ℕ}, n ≤ j → j ≤ m → n ∈ T → m ∈ T → j ∈ T := by
    intro n j m hnj hjm hn hm
    simp only [hT, Set.mem_setOf_eq] at hn hm ⊢
    exact ⟨by omega, Work.KMTPlan.A6.lowSmallSet_conv Λ hΛ ha hnj hjm hn.2 hm.2⟩
  have hterm : ∀ n : ℕ,
      ‖c (n + 1) - c n‖ ≤ ‖d (n + 1) - d n‖ +
        (if (n ∈ T ↔ n + 1 ∈ T) then 0 else Cb : ℝ) := by
    intro n
    have hdn : ‖d n‖ ≤ Cb := hΦb n
    have hdn1 : ‖d (n + 1)‖ ≤ Cb := hΦb (n + 1)
    by_cases h1 : n ∈ T
    · by_cases h2 : n + 1 ∈ T
      · have hc1 : c n = d n := by simp [hc, h1]
        have hc2 : c (n + 1) = d (n + 1) := by simp [hc, h2]
        have hij : (n ∈ T ↔ n + 1 ∈ T) := ⟨fun _ => h2, fun _ => h1⟩
        rw [hc1, hc2, if_pos hij]
        simp
      · have hc1 : c n = d n := by simp [hc, h1]
        have hc2 : c (n + 1) = 0 := by simp [hc, h2]
        have hij : ¬ (n ∈ T ↔ n + 1 ∈ T) := fun hh => h2 (hh.mp h1)
        rw [hc1, hc2, if_neg hij]
        simp only [zero_sub, norm_neg]
        linarith [norm_nonneg (d (n + 1) - d n), hdn]
    · by_cases h2 : n + 1 ∈ T
      · have hc1 : c n = 0 := by simp [hc, h1]
        have hc2 : c (n + 1) = d (n + 1) := by simp [hc, h2]
        have hij : ¬ (n ∈ T ↔ n + 1 ∈ T) := fun hh => h1 (hh.mpr h2)
        rw [hc1, hc2, if_neg hij]
        simp only [sub_zero]
        linarith [norm_nonneg (d (n + 1) - d n), hdn1]
      · have hc1 : c n = 0 := by simp [hc, h1]
        have hc2 : c (n + 1) = 0 := by simp [hc, h2]
        have hij : (n ∈ T ↔ n + 1 ∈ T) := ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩
        rw [hc1, hc2, if_pos hij]
        simp only [sub_zero, norm_zero, add_zero]
        exact norm_nonneg _
  have hjump : ∑ n ∈ Finset.range K, (if (n ∈ T ↔ n + 1 ∈ T) then (0 : ℝ) else Cb)
      = Cb * (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ) := by
    have h1 : ∀ n : ℕ, (if (n ∈ T ↔ n + 1 ∈ T) then (0 : ℝ) else Cb)
        = Cb * ((if ¬ (n ∈ T ↔ n + 1 ∈ T) then (1 : ℕ) else 0 : ℕ) : ℝ) := by
      intro n
      by_cases h : (n ∈ T ↔ n + 1 ∈ T) <;> simp [h]
    rw [Finset.sum_congr rfl (fun n _ => h1 n), ← Finset.mul_sum, ← Nat.cast_sum,
      Finset.sum_boole]
    simp
  have hcard : (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ) ≤ 2 := by
    have := card_jump_le_two hconv K
    exact_mod_cast this
  have h1 : ∑ n ∈ Finset.range K, ‖c (n + 1) - c n‖
      ≤ (∑ n ∈ Finset.range K, ‖d (n + 1) - d n‖)
        + Cb * (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ) := by
    calc ∑ n ∈ Finset.range K, ‖c (n + 1) - c n‖
        ≤ ∑ n ∈ Finset.range K, (‖d (n + 1) - d n‖
            + (if (n ∈ T ↔ n + 1 ∈ T) then (0 : ℝ) else Cb)) :=
          Finset.sum_le_sum (fun n _ => hterm n)
      _ = (∑ n ∈ Finset.range K, ‖d (n + 1) - d n‖)
            + ∑ n ∈ Finset.range K, (if (n ∈ T ↔ n + 1 ∈ T) then (0 : ℝ) else Cb) :=
          Finset.sum_add_distrib
      _ = (∑ n ∈ Finset.range K, ‖d (n + 1) - d n‖)
            + Cb * (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ) := by
          rw [hjump]
  have h3 : Cb * (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ)
      ≤ 2 * Cb := by nlinarith [hcard, hCb0]
  calc ‖(Work.KMTAreas.A7.randSymb
      (fun n ξ => if n = 0 then 0
        else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then Φ n ξ else 0) ε K) x‖
      = ‖∑ n ∈ Finset.range K, ε n * (c (n + 1) - c n)‖ := by rw [hsym]
    _ ≤ ∑ n ∈ Finset.range K, ‖ε n * (c (n + 1) - c n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range K, ‖c (n + 1) - c n‖ := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hε n)
    _ ≤ Cv + 2 * Cb := by linarith [h1, hvar, h3]

end

end Work.KMTPlan.A6
