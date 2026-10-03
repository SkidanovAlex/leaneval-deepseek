/-
# `Submission.Work.FIArea7CF.numeric_core_proof_B`

The proof of `Work.FIArea7.NumericCoreB` (the pure real-variable core of the amended area-7
assembly).  The argument is the one described in the docstring of `NumericCoreB`:

* `Work.FIArea7.numeric_core_proof` (the proved `NumericCore`) applied with `C_H` replaced by
  `2*C_H` bounds `T₁(old) + 2T₂(old) + T₃ + T₄`;
* the region-I angular-mode slack `2K+1 → 2K+L₀+2` is handled by the elementary monotonicity
  `T₁(new) ≤ T₁(old)` and the splitting `L₀+1 ≤ (2K+1) + (2Lm+2)`;
* the three extra summands (`S5`, the `E`-mass term; `S6`, its cross term with `β_L`; `Sx`, the
  `L₀`-slack of region II) are bounded in this same file by `ncExtrasS5_aux`, `ncExtrasS6_aux`
  and `ncExtrasSx_aux`, each of which is an elementary (but threshold-heavy) polylog-absorption
  estimate.

The auxiliary lemmas (`exists_log_rpow_le_rpow`, `cap_mul_log_decay`, `...`) implement the
standard "a power of a logarithm is eventually dominated by a power of `N`" calculus, including
the log-cap `X ≤ (log N)^{3·10⁹}` versus the Rankin decay `(log N)^{-4·10⁹}`.
-/
import Mathlib
import Submission.Work.FIArea7CF.Area7BDefs
import Submission.Work.FIArea7CF.numeric_core_proof
import Submission.Work.FIArea7.NCBasic
import Submission.Work.FIArea7.nc_logK_bound

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.FIArea7CF

open scoped BigOperators



open scoped BigOperators

/-! ## Thresholds for polylogarithmic absorption -/

/-- For fixed `A ≥ 0` and `ε > 0`, `(log N)^A ≤ N^ε` for all large `N`. -/
lemma exists_log_rpow_le_rpow (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → (Real.log N) ^ A ≤ N ^ ε := by
  obtain ⟨m, hm⟩ := exists_nat_ge A
  obtain ⟨X₁, hX₁, hX₁'⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := (1 : ℝ)) zero_le_one
      (n := m) hε
  refine ⟨max X₁ 3, le_max_right _ _, ?_⟩
  intro N hN
  have hNX : X₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hlog1 : 1 ≤ Real.log N := Work.FIArea7.one_le_log_of_three_le hN3
  have h1 : (Real.log N) ^ A ≤ (Real.log N) ^ (m : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 hm
  have h2 : (Real.log N) ^ (m : ℝ) = (Real.log N) ^ m := Real.rpow_natCast _ m
  have h3 : (1 : ℝ) * (Real.log N) ^ m ≤ N ^ ε := hX₁' N hNX
  calc (Real.log N) ^ A ≤ (Real.log N) ^ (m : ℝ) := h1
    _ = (Real.log N) ^ m := h2
    _ ≤ N ^ ε := by simpa using h3

/-- If `log N ≥ 1` and `X ≤ (log N)^B`, then `X (log N)^{-A} (log N)^m ≤ 1` whenever
`m ≤ A - B`.  In particular (with `A = 4·10^9`, `B = 3·10^9`, `m = 2`) the log-cap
`X ≤ (log N)^{3·10^9}` beats the Rankin decay `(log N)^{-4·10^9}`. -/
lemma cap_mul_log_decay {N X A B : ℝ} (m : ℕ) (hlog1 : 1 ≤ Real.log N)
    (hX : X ≤ (Real.log N) ^ B) (hm : (m : ℝ) ≤ A - B) :
    X * (Real.log N) ^ (-A) * (Real.log N) ^ m ≤ 1 := by
  have hL : 0 < Real.log N := lt_of_lt_of_le one_pos hlog1
  have hLnn : 0 ≤ Real.log N := hL.le
  have h1 : X * (Real.log N) ^ (-A) ≤ (Real.log N) ^ B * (Real.log N) ^ (-A) :=
    mul_le_mul_of_nonneg_right hX (Real.rpow_nonneg hLnn _)
  have h2 : (Real.log N) ^ B * (Real.log N) ^ (-A) = (Real.log N) ^ (B - A) := by
    rw [← Real.rpow_add hL]; ring_nf
  have h3 : X * (Real.log N) ^ (-A) ≤ (Real.log N) ^ (B - A) := by
    rw [h2] at h1; exact h1
  have h4 : (Real.log N) ^ (B - A) * (Real.log N) ^ m
      = (Real.log N) ^ (B - A + (m : ℝ)) := by
    rw [← Real.rpow_natCast (Real.log N) m, ← Real.rpow_add hL]
  have h5 : X * (Real.log N) ^ (-A) * (Real.log N) ^ m
      ≤ (Real.log N) ^ (B - A + (m : ℝ)) := by
    rw [← h4]
    exact mul_le_mul_of_nonneg_right h3 (pow_nonneg hLnn m)
  have hexp : B - A + (m : ℝ) ≤ 0 := by linarith
  calc X * (Real.log N) ^ (-A) * (Real.log N) ^ m
      ≤ (Real.log N) ^ (B - A + (m : ℝ)) := h5
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hlog1 hexp

/-- Some `N₀ ≥ 3` with `2 ≤ log N` beyond it. -/
lemma exists_two_le_log : ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → 2 ≤ Real.log N := by
  have h : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 2)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp h
  exact ⟨max a 3, le_max_right _ _, fun N hN => ha N (le_trans (le_max_left _ _) hN)⟩

/-! ## Power bounds from `X^8 ≤ N^{δ₁}` -/

lemma sq_le_rpow_of_pow_eight_le {N X δ₁ : ℝ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    (hX8 : X ^ 8 ≤ N ^ δ₁) : X ^ 2 ≤ N ^ (δ₁ / 4) := by
  have hNpos : 0 < N := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hXle : X ≤ N ^ (δ₁ / 8) := Work.FIArea7.le_rpow_div_eight_of_pow_eight_le hX0 hNpos hX8
  have h1 : X ^ 2 ≤ (N ^ (δ₁ / 8)) ^ 2 := pow_le_pow_left₀ hX0 hXle 2
  have h2 : (N ^ (δ₁ / 8)) ^ 2 = N ^ (δ₁ / 4) := by
    rw [← Real.rpow_natCast (N ^ (δ₁ / 8)) 2, ← Real.rpow_mul hNpos.le]
    ring_nf
  rwa [h2] at h1

lemma cube_le_rpow_of_pow_eight_le {N X δ₁ : ℝ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    (hX8 : X ^ 8 ≤ N ^ δ₁) : X ^ 3 ≤ N ^ (3 * δ₁ / 8) := by
  have hNpos : 0 < N := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hXle : X ≤ N ^ (δ₁ / 8) := Work.FIArea7.le_rpow_div_eight_of_pow_eight_le hX0 hNpos hX8
  have h1 : X ^ 3 ≤ (N ^ (δ₁ / 8)) ^ 3 := pow_le_pow_left₀ hX0 hXle 3
  have h2 : (N ^ (δ₁ / 8)) ^ 3 = N ^ (3 * δ₁ / 8) := by
    rw [← Real.rpow_natCast (N ^ (δ₁ / 8)) 3, ← Real.rpow_mul hNpos.le]
    ring_nf
  rwa [h2] at h1

/-! ## Logarithmic comparisons -/

lemma log_X_add_two_le {N X : ℝ} (hX : 1 ≤ X) (hXN : X ≤ N) (hN : 2 ≤ N) :
    Real.log (X + 2) ≤ 2 * Real.log N := by
  have hpos : 0 < X + 2 := by linarith
  have h2N : X + 2 ≤ 2 * N := by linarith
  have h1 : Real.log (X + 2) ≤ Real.log (2 * N) := Real.log_le_log hpos h2N
  have h2 : Real.log (2 * N) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) (by linarith)
  have h3 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  linarith

lemma log_UB_add_two_le {N UB : ℝ} (hUB : 0 < UB) (hUB' : UB ≤ 4 * N + 2) (hN : 6 ≤ N) :
    Real.log (UB + 2) ≤ 2 * Real.log N := by
  have hpos : 0 < UB + 2 := by linarith
  have hle : UB + 2 ≤ N ^ 2 := by nlinarith
  have h1 : Real.log (UB + 2) ≤ Real.log (N ^ 2) := Real.log_le_log hpos hle
  have h2 : Real.log (N ^ 2) = 2 * Real.log N := by
    rw [Real.log_pow]; norm_num
  linarith

lemma log_Lm_add_two_le {N Lm BL : ℝ} (hN3 : 3 ≤ N) (hlog2 : 2 ≤ Real.log N)
    (hLm1 : 1 ≤ Lm) (hLm : Lm ≤ (Real.log N) ^ BL)
    (hBL : 0 ≤ BL) : Real.log (Lm + 2) ≤ (BL + 2) * Real.log N := by
  have hlogpos : 0 < Real.log N := by linarith
  have hL : 1 ≤ (Real.log N) ^ BL := Real.one_le_rpow (by linarith) hBL
  have hLm2 : Lm + 2 ≤ 3 * (Real.log N) ^ BL := by linarith
  have hpos : 0 < Lm + 2 := by linarith
  have hlog : Real.log (Lm + 2) ≤ Real.log (3 * (Real.log N) ^ BL) :=
    Real.log_le_log hpos hLm2
  have hsplit : Real.log (3 * (Real.log N) ^ BL) = Real.log 3 + BL * Real.log (Real.log N) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hlogpos]
  have hloglog : Real.log (Real.log N) ≤ Real.log N := by
    have := Real.log_le_sub_one_of_pos hlogpos
    linarith
  have hlog3 : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) (by linarith)
  rw [hsplit] at hlog
  have hstep : BL * Real.log (Real.log N) ≤ BL * Real.log N :=
    mul_le_mul_of_nonneg_left hloglog hBL
  calc Real.log (Lm + 2) ≤ Real.log 3 + BL * Real.log (Real.log N) := hlog
    _ ≤ Real.log N + BL * Real.log N := by linarith
    _ ≤ (BL + 2) * Real.log N := by nlinarith

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
lemma sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have h2 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, h1, h2]

theorem ncExtrasSx_aux : ∀ (Clat BL δ₁ : ℝ),
    0 < Clat → 0 ≤ BL → 0 < δ₁ → δ₁ < 3 / 32 →
    ∃ c N₀ : ℝ, 0 < c ∧
      ∀ {N X Lm : ℝ} {K : ℕ} {θ : ℝ},
        N₀ ≤ N → 3 ≤ N → 1 ≤ X → 0 < θ → θ ≤ 1 → X ^ 8 ≤ N ^ δ₁ →
        1 ≤ (K : ℝ) → X ^ 3 * (Real.log (N + 2)) ^ 20 ≤ (K : ℝ) →
        (K : ℝ) ≤ 2 * X ^ 3 * (Real.log (N + 2)) ^ 20 →
        1 ≤ Lm → Lm ≤ (Real.log N) ^ BL →
          (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
              * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁))
          ≤ c * X⁻¹ * N ^ 2 * Real.log N := by
  intro Clat BL δ₁ hCl hBL hδ0 hδ32
  obtain ⟨NT, hNT3, hNT⟩ :=
    exists_log_rpow_le_rpow (BL + 4) (ε := 3 * δ₁ / 8) (by linarith)
  refine ⟨(1 + Clat) * 240000000, max NT 5, by positivity, ?_⟩
  intro N X Lm K θ hN0 hN3 hX1 hθ0 hθ1 hX8 hK1 hKg hKu hLm1 hLmBL
  have hNNT : NT ≤ N := le_trans (le_max_left NT 5) hN0
  have hN5 : 5 ≤ N := le_trans (le_max_right NT 5) hN0
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hN2 : 2 ≤ N := by linarith
  have hXpos : 0 < X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hlog1 : 1 ≤ Real.log N := Work.FIArea7.one_le_log_of_three_le hN3
  have hlogpos : 0 < Real.log N := by linarith
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hL2 : Real.log (N + 2) ≤ 2 * Real.log N := Work.FIArea7.log_add_two_le_two_mul_log hN2
  have hL2nn : 0 ≤ Real.log (N + 2) := Real.log_nonneg (by linarith)
  have hK2 : (Real.log ((K : ℝ) + 2)) ^ 2 ≤ 2500 * (Real.log N) ^ 2 :=
    Work.FIArea7.nc_logK_bound hN5 hX1 hX8 hδ0 hδ32 hK1 hKu
  have htheta : θ * N + Real.sqrt N + 1 ≤ 3 * N := by
    have hs : Real.sqrt N ≤ N := by
      rw [Real.sqrt_le_iff]; exact ⟨by linarith, by nlinarith⟩
    have hθN : θ * N ≤ N := by nlinarith
    linarith
  have hL3 : (Real.log (N + 2)) ^ 3 ≤ 8 * (Real.log N) ^ 3 := by
    calc (Real.log (N + 2)) ^ 3 ≤ (2 * Real.log N) ^ 3 := pow_le_pow_left₀ hL2nn hL2 3
      _ = 8 * (Real.log N) ^ 3 := by ring
  have hLmBL1 : 1 ≤ (Real.log N) ^ BL := Real.one_le_rpow hlog1 hBL
  have hLm4 : 2 * Lm + 2 ≤ 4 * (Real.log N) ^ BL := by linarith
  have hX2 : X ^ 2 ≤ N ^ (δ₁ / 4) := sq_le_rpow_of_pow_eight_le hN1 hX1 hX8
  have hlogNpow : (Real.log N) ^ (BL + 4) ≤ N ^ (3 * δ₁ / 8) := hNT N hNNT
  have hBLnn : 0 ≤ (Real.log N) ^ BL := Real.rpow_nonneg hlog0 _
  -- key: X * N^(-δ₁) * (log N)^(BL+4) ≤ X⁻¹
  have hkey : X * N ^ (-δ₁) * (Real.log N) ^ (BL + 4) ≤ X⁻¹ := by
    have hNdec : 0 ≤ N ^ (-δ₁) := Real.rpow_nonneg hNpos.le _
    have h1 : X ^ 2 * N ^ (-δ₁) ≤ N ^ (δ₁ / 4) * N ^ (-δ₁) :=
      mul_le_mul_of_nonneg_right hX2 hNdec
    have h2 : N ^ (δ₁ / 4) * N ^ (-δ₁) = N ^ (-(3 * δ₁ / 4)) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    have h3 : X ^ 2 * N ^ (-δ₁) ≤ N ^ (-(3 * δ₁ / 4)) := by rw [← h2]; exact h1
    have h4 : X ^ 2 * N ^ (-δ₁) * (Real.log N) ^ (BL + 4) ≤ 1 := by
      have h5 : X ^ 2 * N ^ (-δ₁) * (Real.log N) ^ (BL + 4)
          ≤ N ^ (-(3 * δ₁ / 4)) * N ^ (3 * δ₁ / 8) :=
        mul_le_mul h3 hlogNpow (Real.rpow_nonneg hlog0 _) (Real.rpow_nonneg hNpos.le _)
      have h6 : N ^ (-(3 * δ₁ / 4)) * N ^ (3 * δ₁ / 8) = N ^ (-(3 * δ₁ / 8)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      have h7 : N ^ (-(3 * δ₁ / 8)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      linarith [h5, h6.le, h6.ge, h7]
    have hXne : X ≠ 0 := ne_of_gt hXpos
    calc X * N ^ (-δ₁) * (Real.log N) ^ (BL + 4)
        = X⁻¹ * (X ^ 2 * N ^ (-δ₁) * (Real.log N) ^ (BL + 4)) := by
          field_simp
      _ ≤ X⁻¹ * 1 := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = X⁻¹ := by ring
  -- the factor-wise bound
  have hstep1 : (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
              * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁))
      ≤ (1 + Clat) * (1000 * (3 * N) * (8 * (Real.log N) ^ 3))
              * (2500 * (Real.log N) ^ 2) * (X * (4 * (Real.log N) ^ BL) * N ^ (1 - δ₁)) := by
    gcongr
  have hNrpow : N ^ (1 - δ₁) = N * N ^ (-δ₁) := by
    rw [Real.rpow_sub hNpos, Real.rpow_one, Real.rpow_neg hNpos.le]
    field_simp
  have hlogpow : (Real.log N) ^ 3 * (Real.log N) ^ 2 * (Real.log N) ^ BL
      = Real.log N * (Real.log N) ^ (BL + 4) := by
    have hLHS : (Real.log N) ^ 3 * (Real.log N) ^ 2 * (Real.log N) ^ BL
        = (Real.log N) ^ (5 + BL) := by
      rw [show (Real.log N) ^ 3 * (Real.log N) ^ 2 = (Real.log N) ^ 5 by ring,
        ← Real.rpow_natCast (Real.log N) 5, ← Real.rpow_add hlogpos]
      push_cast
      ring
    have hRHS : Real.log N * (Real.log N) ^ (BL + 4) = (Real.log N) ^ (5 + BL) := by
      nth_rewrite 1 [← Real.rpow_one (Real.log N)]
      rw [← Real.rpow_add hlogpos]
      ring_nf
    rw [hLHS, hRHS]
  have hfac : (1 + Clat) * (1000 * (3 * N) * (8 * (Real.log N) ^ 3))
              * (2500 * (Real.log N) ^ 2) * (X * (4 * (Real.log N) ^ BL) * N ^ (1 - δ₁))
      = (1 + Clat) * 240000000 * (N ^ 2 * Real.log N)
          * (X * N ^ (-δ₁) * (Real.log N) ^ (BL + 4)) := by
    calc (1 + Clat) * (1000 * (3 * N) * (8 * (Real.log N) ^ 3))
            * (2500 * (Real.log N) ^ 2) * (X * (4 * (Real.log N) ^ BL) * N ^ (1 - δ₁))
        = (1 + Clat) * 240000000 * (N * N ^ (1 - δ₁)) * X
            * ((Real.log N) ^ 3 * (Real.log N) ^ 2 * (Real.log N) ^ BL) := by ring
      _ = (1 + Clat) * 240000000 * (N * (N * N ^ (-δ₁))) * X
            * (Real.log N * (Real.log N) ^ (BL + 4)) := by rw [hNrpow, hlogpow]
      _ = (1 + Clat) * 240000000 * (N ^ 2 * Real.log N)
            * (X * N ^ (-δ₁) * (Real.log N) ^ (BL + 4)) := by ring
  have hstep2 : (1 + Clat) * (1000 * (3 * N) * (8 * (Real.log N) ^ 3))
              * (2500 * (Real.log N) ^ 2) * (X * (4 * (Real.log N) ^ BL) * N ^ (1 - δ₁))
      ≤ (1 + Clat) * 240000000 * (N ^ 2 * Real.log N) * X⁻¹ := by
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  calc (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
              * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁))
      ≤ (1 + Clat) * (1000 * (3 * N) * (8 * (Real.log N) ^ 3))
              * (2500 * (Real.log N) ^ 2) * (X * (4 * (Real.log N) ^ BL) * N ^ (1 - δ₁)) := hstep1
    _ ≤ (1 + Clat) * 240000000 * (N ^ 2 * Real.log N) * X⁻¹ := hstep2
    _ = ((1 + Clat) * 240000000) * X⁻¹ * N ^ 2 * Real.log N := by ring


lemma le_mul_inv_of_mul_le {a b X : ℝ} (hX : 0 < X) (h : a * X ≤ b) : a ≤ b * X⁻¹ := by
  calc a = a * X * X⁻¹ := by field_simp
    _ ≤ b * X⁻¹ := mul_le_mul_of_nonneg_right h (by positivity)

/-- `X^3 * N^{δ₁-1} ≤ 1` in the FI range. -/
lemma cube_mul_rpow_sub_le_one {N X δ₁ : ℝ} (hN1 : 1 ≤ N) (hδ0 : 0 < δ₁)
    (hδ32 : δ₁ < 3 / 32) (hX1 : 1 ≤ X) (hX8 : X ^ 8 ≤ N ^ δ₁) :
    X ^ 3 * N ^ (δ₁ - 1) ≤ 1 := by
  have hNpos : 0 < N := by linarith
  have hN8 : X ^ 3 ≤ N ^ (3 * δ₁ / 8) := cube_le_rpow_of_pow_eight_le hN1 hX1 hX8
  have hdec : N ^ (δ₁ - 1) ≤ N ^ (-(5 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hmul : X ^ 3 * N ^ (δ₁ - 1) ≤ N ^ (3 * δ₁ / 8) * N ^ (-(5 : ℝ) / 8) :=
    mul_le_mul hN8 hdec (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)
  have heq : N ^ (3 * δ₁ / 8) * N ^ (-(5 : ℝ) / 8) = N ^ (3 * δ₁ / 8 - 5 / 8) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hle1 : N ^ (3 * δ₁ / 8 - 5 / 8) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  rw [heq] at hmul
  linarith [hmul, hle1]

theorem ncExtrasS5_aux : ∀ (CR BL δ₁ B : ℝ),
    0 < CR → 0 ≤ BL → 0 < δ₁ → δ₁ < 3 / 32 → B ≤ 4 * 10 ^ 9 - 2 →
    ∃ c N₀ : ℝ, 0 < c ∧
      ∀ {N X Lm Ev : ℝ} {K : ℕ},
        N₀ ≤ N → 3 ≤ N → 1 ≤ X → X ^ 8 ≤ N ^ δ₁ →
        X ≤ (Real.log N) ^ B →
        1 ≤ (K : ℝ) → X ^ 3 * (Real.log (N + 2)) ^ 20 ≤ (K : ℝ) →
        (K : ℝ) ≤ 2 * X ^ 3 * (Real.log (N + 2)) ^ 20 →
        1 ≤ Lm → Lm ≤ (Real.log N) ^ BL → 0 ≤ Ev →
        Ev ≤ 2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ))
             + 2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5) →
          (Real.log ((K : ℝ) + 2)) ^ 2 * Ev * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁)
          ≤ c * X⁻¹ * N ^ 2 * Real.log N := by
  intro CR BL δ₁ B hCR hBL hδ0 hδ32 hB
  obtain ⟨NT1, hNT13, hNT1⟩ := exists_two_le_log
  refine ⟨15000 + 15000 * CR * (BL + 2) ^ 2, max NT1 5, by positivity, ?_⟩
  intro N X Lm Ev K hN0 hN3 hX1 hX8 hXcap hK1 hKg hKu hLm1 hLmBL hEvnn hEv
  have hNT1le : NT1 ≤ N := le_trans (le_max_left NT1 5) hN0
  have hN5 : 5 ≤ N := le_trans (le_max_right NT1 5) hN0
  have hN3' : 3 ≤ N := by linarith
  have hlog2 : 2 ≤ Real.log N := hNT1 N hNT1le
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hN2 : 2 ≤ N := by linarith
  have hXpos : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log N := by linarith
  have hlogpos : 0 < Real.log N := by linarith
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hK2 : (Real.log ((K : ℝ) + 2)) ^ 2 ≤ 2500 * (Real.log N) ^ 2 :=
    Work.FIArea7.nc_logK_bound hN5 hX1 hX8 hδ0 hδ32 hK1 hKu
  have hLm2 : Real.log (Lm + 2) ≤ (BL + 2) * Real.log N :=
    log_Lm_add_two_le hN3' hlog2 hLm1 hLmBL hBL
  have hLm2nn : 0 ≤ Real.log (Lm + 2) := Real.log_nonneg (by linarith)
  have hLm2sq : (Real.log (Lm + 2)) ^ 2 ≤ ((BL + 2) * Real.log N) ^ 2 :=
    pow_le_pow_left₀ hLm2nn hLm2 2
  have hXleN : X ≤ N := by
    have h := Work.FIArea7.le_rpow_div_eight_of_pow_eight_le (by linarith : (0:ℝ) ≤ X) hNpos hX8
    calc X ≤ N ^ (δ₁ / 8) := h
      _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one N
  have hlogX : Real.log (X + 2) ≤ 2 * Real.log N := log_X_add_two_le hX1 hXleN hN2
  have hlogXnn : 0 ≤ Real.log (X + 2) := Real.log_nonneg (by linarith)
  have hL2nn : 0 ≤ Real.log (N + 2) := Real.log_nonneg (by linarith)
  have hB2 : ((2 : ℕ) : ℝ) ≤ 4 * 10 ^ 9 - B := by
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2]
    linarith
  have hcap := cap_mul_log_decay (N := N) (X := X) 2 (A := 4 * 10 ^ 9) (B := B)
    hlog1 hXcap hB2
  have hlogdec : Real.log N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)) ≤ 1 := by
    nth_rewrite 1 [← Real.rpow_one (Real.log N)]
    rw [← Real.rpow_add hlogpos]
    exact Real.rpow_le_one_of_one_le_of_nonpos hlog1 (by norm_num)
  -- X^3 * N^δ₁ ≤ N
  have hX3N : X ^ 3 * N ^ δ₁ ≤ N := by
    have h := cube_le_rpow_of_pow_eight_le hN1 hX1 hX8
    calc X ^ 3 * N ^ δ₁ ≤ N ^ (3 * δ₁ / 8) * N ^ δ₁ :=
          mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (3 * δ₁ / 8 + δ₁) := by rw [← Real.rpow_add hNpos]
      _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one N
  -- ===== piece A (the Rankin summand) =====
  have hS1 : (Real.log ((K : ℝ) + 2)) ^ 2 * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
        * (N * Real.log (X + 2)) * X ≤ 10000 * (N ^ 2 * Real.log N) := by
    calc (Real.log ((K : ℝ) + 2)) ^ 2 * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
            * (N * Real.log (X + 2)) * X
        ≤ (2500 * (Real.log N) ^ 2) * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
            * (N * (2 * Real.log N)) * X := by gcongr
      _ = 10000 * (N ^ 2 * Real.log N)
            * (X * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)) * (Real.log N) ^ 2) := by ring
      _ ≤ 10000 * (N ^ 2 * Real.log N) * 1 :=
          mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = 10000 * (N ^ 2 * Real.log N) := by ring
  have hS2 : (Real.log ((K : ℝ) + 2)) ^ 2 * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
        * (X ^ 2 * N ^ δ₁) * X ≤ 5000 * (N ^ 2 * Real.log N) := by
    calc (Real.log ((K : ℝ) + 2)) ^ 2 * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
            * (X ^ 2 * N ^ δ₁) * X
        ≤ (2500 * (Real.log N) ^ 2) * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
            * (X ^ 2 * N ^ δ₁) * X := by gcongr
      _ = 5000 * Real.log N * N
            * (X ^ 3 * N ^ δ₁ * Real.log N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ))) := by ring
      _ ≤ 5000 * Real.log N * N * (N * 1) := by
          have hsum : X ^ 3 * N ^ δ₁ * Real.log N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ))
              = (X ^ 3 * N ^ δ₁) * (Real.log N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ))) := by ring
          rw [hsum]
          have hp : (X ^ 3 * N ^ δ₁) * (Real.log N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
              ≤ N * 1 := mul_le_mul hX3N hlogdec (by positivity) (by linarith)
          exact mul_le_mul_of_nonneg_left hp (by positivity)
      _ = 5000 * (N ^ 2 * Real.log N) := by ring
  have hApiece : (Real.log ((K : ℝ) + 2)) ^ 2 * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
        * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X ≤ 15000 * (N ^ 2 * Real.log N) := by
    have hsplit : (Real.log ((K : ℝ) + 2)) ^ 2 * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
          * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X
        = (Real.log ((K : ℝ) + 2)) ^ 2 * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
            * (N * Real.log (X + 2)) * X
          + (Real.log ((K : ℝ) + 2)) ^ 2 * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
            * (X ^ 2 * N ^ δ₁) * X := by ring
    rw [hsplit]
    linarith [hS1, hS2]
  -- ===== piece B (the truncation summand) =====
  have hden : (Real.log N) ^ 5 ≤ (Real.log (N + 2)) ^ 5 :=
    pow_le_pow_left₀ hlog0 (Real.log_le_log (by linarith) (by linarith)) 5
  have hBX : 2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5) * X
      ≤ 2 * CR * (BL + 2) ^ 2 * N / (Real.log N) ^ 3 := by
    have h1 : 2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5) * X
        = 2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X * (Real.log (N + 2)) ^ 5) := by
      field_simp
    rw [h1]
    have hnum : 2 * CR * N * (Real.log (Lm + 2)) ^ 2
        ≤ 2 * CR * N * ((BL + 2) * Real.log N) ^ 2 :=
      mul_le_mul_of_nonneg_left hLm2sq (by positivity)
    have hden2 : (Real.log N) ^ 5 ≤ X * (Real.log (N + 2)) ^ 5 := by
      have h3 : (0:ℝ) ≤ (Real.log (N + 2)) ^ 5 := pow_nonneg hL2nn 5
      nlinarith [hden, hX1, h3]
    calc 2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X * (Real.log (N + 2)) ^ 5)
        ≤ 2 * CR * N * ((BL + 2) * Real.log N) ^ 2 / (X * (Real.log (N + 2)) ^ 5) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 2 * CR * N * ((BL + 2) * Real.log N) ^ 2 / (Real.log N) ^ 5 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden2
      _ = 2 * CR * (BL + 2) ^ 2 * N / (Real.log N) ^ 3 := by
          field_simp
  have hB1 : (Real.log ((K : ℝ) + 2)) ^ 2
        * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
        * (N * Real.log (X + 2)) * X ≤ 10000 * CR * (BL + 2) ^ 2 * (N ^ 2 * Real.log N) := by
    have hsplit : (Real.log ((K : ℝ) + 2)) ^ 2
          * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
          * (N * Real.log (X + 2)) * X
        = (Real.log ((K : ℝ) + 2)) ^ 2
          * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5) * X)
          * (N * Real.log (X + 2)) := by ring
    rw [hsplit]
    have h1 : (Real.log ((K : ℝ) + 2)) ^ 2
        * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5) * X)
        ≤ (2500 * (Real.log N) ^ 2) * (2 * CR * (BL + 2) ^ 2 * N / (Real.log N) ^ 3) :=
      mul_le_mul hK2 hBX (by positivity) (by positivity)
    have h2 : N * Real.log (X + 2) ≤ N * (2 * Real.log N) :=
      mul_le_mul_of_nonneg_left hlogX (by linarith)
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    have hQ : 2500 * (Real.log N) ^ 2 * (2 * CR * (BL + 2) ^ 2 * N / (Real.log N) ^ 3)
        * (N * (2 * Real.log N)) = 10000 * CR * (BL + 2) ^ 2 * N ^ 2 := by
      field_simp
      ring
    rw [hQ] at h3
    calc (Real.log ((K : ℝ) + 2)) ^ 2
            * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5) * X)
            * (N * Real.log (X + 2))
        ≤ 10000 * CR * (BL + 2) ^ 2 * N ^ 2 := h3
      _ ≤ 10000 * CR * (BL + 2) ^ 2 * (N ^ 2 * Real.log N) := by
          have hc : (0:ℝ) ≤ CR * (BL + 2) ^ 2 * N ^ 2 := by positivity
          have hle : CR * (BL + 2) ^ 2 * N ^ 2 ≤ CR * (BL + 2) ^ 2 * N ^ 2 * Real.log N := by
            nlinarith [hlog1, hc]
          have h10000 : (0:ℝ) ≤ 10000 := by norm_num
          have := mul_le_mul_of_nonneg_left hle h10000
          linarith [this]
  have hB2core : 2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5)
        * (X ^ 2 * N ^ δ₁) * X ≤ 2 * CR * (BL + 2) ^ 2 * N ^ 2 / Real.log N := by
    have hcancel : 2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5)
        * (X ^ 2 * N ^ δ₁) * X
        = 2 * CR * N * (Real.log (Lm + 2)) ^ 2 * N ^ δ₁ * X / (Real.log (N + 2)) ^ 5 := by
      field_simp
    rw [hcancel]
    have hXle : X ≤ N ^ (δ₁ / 8) :=
      Work.FIArea7.le_rpow_div_eight_of_pow_eight_le (by linarith : (0:ℝ) ≤ X) hNpos hX8
    have hnum2 : 2 * CR * N * (Real.log (Lm + 2)) ^ 2 * N ^ δ₁ * X
        ≤ 2 * CR * N * ((BL + 2) * Real.log N) ^ 2 * N ^ δ₁ * N ^ (δ₁ / 8) := by
      calc 2 * CR * N * (Real.log (Lm + 2)) ^ 2 * N ^ δ₁ * X
          ≤ 2 * CR * N * ((BL + 2) * Real.log N) ^ 2 * N ^ δ₁ * X := by
            have h1 : 2 * CR * N * (Real.log (Lm + 2)) ^ 2
                ≤ 2 * CR * N * ((BL + 2) * Real.log N) ^ 2 :=
              mul_le_mul_of_nonneg_left hLm2sq (by positivity)
            exact mul_le_mul (mul_le_mul h1 le_rfl (by positivity) (by positivity)) le_rfl
              (by linarith) (by positivity)
        _ ≤ 2 * CR * N * ((BL + 2) * Real.log N) ^ 2 * N ^ δ₁ * N ^ (δ₁ / 8) :=
            mul_le_mul le_rfl hXle (by positivity) (by positivity)
    have hNp : N * N ^ δ₁ * N ^ (δ₁ / 8) ≤ N ^ 2 := by
      have h1 : N ^ (1 + δ₁ + δ₁ / 8) = N * N ^ δ₁ * N ^ (δ₁ / 8) := by
        rw [Real.rpow_add hNpos (1 + δ₁) (δ₁ / 8), Real.rpow_add hNpos 1 δ₁, Real.rpow_one]
      rw [← h1]
      calc N ^ (1 + δ₁ + δ₁ / 8) ≤ N ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = N ^ 2 := Real.rpow_two N
    calc 2 * CR * N * (Real.log (Lm + 2)) ^ 2 * N ^ δ₁ * X / (Real.log (N + 2)) ^ 5
        ≤ 2 * CR * N * ((BL + 2) * Real.log N) ^ 2 * N ^ δ₁ * N ^ (δ₁ / 8)
            / (Real.log (N + 2)) ^ 5 :=
          div_le_div_of_nonneg_right hnum2 (by positivity)
      _ ≤ 2 * CR * N * ((BL + 2) * Real.log N) ^ 2 * N ^ δ₁ * N ^ (δ₁ / 8)
            / (Real.log N) ^ 5 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 2 * CR * (BL + 2) ^ 2 * (N * N ^ δ₁ * N ^ (δ₁ / 8)) / (Real.log N) ^ 3 := by
          field_simp
      _ ≤ 2 * CR * (BL + 2) ^ 2 * N ^ 2 / (Real.log N) ^ 3 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hNp (by positivity)
      _ ≤ 2 * CR * (BL + 2) ^ 2 * N ^ 2 / Real.log N := by
          apply div_le_div_of_nonneg_left (by positivity) hlogpos
          have h1 : Real.log N ≤ (Real.log N) ^ 3 := by
            nlinarith [hlog1, mul_nonneg hlog0 hlog0]
          exact h1
  have hB2 : (Real.log ((K : ℝ) + 2)) ^ 2
        * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
        * (X ^ 2 * N ^ δ₁) * X ≤ 5000 * CR * (BL + 2) ^ 2 * (N ^ 2 * Real.log N) := by
    have hsplit : (Real.log ((K : ℝ) + 2)) ^ 2
          * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
          * (X ^ 2 * N ^ δ₁) * X
        = (Real.log ((K : ℝ) + 2)) ^ 2
          * ((2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
              * (X ^ 2 * N ^ δ₁) * X) := by ring
    rw [hsplit]
    have h1 : (Real.log ((K : ℝ) + 2)) ^ 2
          * ((2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
              * (X ^ 2 * N ^ δ₁) * X)
        ≤ (2500 * (Real.log N) ^ 2)
          * ((2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
              * (X ^ 2 * N ^ δ₁) * X) :=
      mul_le_mul_of_nonneg_right hK2 (by positivity)
    have h1' : (2500 * (Real.log N) ^ 2)
          * ((2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
              * (X ^ 2 * N ^ δ₁) * X)
        ≤ (2500 * (Real.log N) ^ 2) * (2 * CR * (BL + 2) ^ 2 * N ^ 2 / Real.log N) :=
      mul_le_mul_of_nonneg_left hB2core (by positivity)
    have hQ : 2500 * (Real.log N) ^ 2 * (2 * CR * (BL + 2) ^ 2 * N ^ 2 / Real.log N)
        = 5000 * CR * (BL + 2) ^ 2 * (N ^ 2 * Real.log N) := by
      field_simp
      ring
    linarith [h1, h1', hQ.le, hQ.ge]
  have hBpiece : (Real.log ((K : ℝ) + 2)) ^ 2
        * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
        * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X
        ≤ 15000 * CR * (BL + 2) ^ 2 * (N ^ 2 * Real.log N) := by
    have hsplit : (Real.log ((K : ℝ) + 2)) ^ 2
          * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
          * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X
        = (Real.log ((K : ℝ) + 2)) ^ 2
            * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
            * (N * Real.log (X + 2)) * X
          + (Real.log ((K : ℝ) + 2)) ^ 2
            * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
            * (X ^ 2 * N ^ δ₁) * X := by ring
    rw [hsplit]
    linarith [hB1, hB2]
  -- ===== assembling =====
  have hmain : (Real.log ((K : ℝ) + 2)) ^ 2 * Ev * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X
      ≤ (15000 + 15000 * CR * (BL + 2) ^ 2) * (N ^ 2 * Real.log N) := by
    have h1 : (Real.log ((K : ℝ) + 2)) ^ 2 * Ev * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X
        ≤ (Real.log ((K : ℝ) + 2)) ^ 2
            * ((2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
              + (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5)))
            * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hEv (by positivity)
    have hexp : (Real.log ((K : ℝ) + 2)) ^ 2
            * ((2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
              + (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5)))
            * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X
        = (Real.log ((K : ℝ) + 2)) ^ 2
            * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
            * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X
          + (Real.log ((K : ℝ) + 2)) ^ 2
            * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
            * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X := by ring
    rw [hexp] at h1
    have hfin : (Real.log ((K : ℝ) + 2)) ^ 2
            * (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
            * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X
          + (Real.log ((K : ℝ) + 2)) ^ 2
            * (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
            * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) * X
        ≤ 15000 * (N ^ 2 * Real.log N) + 15000 * CR * (BL + 2) ^ 2 * (N ^ 2 * Real.log N) :=
      add_le_add hApiece hBpiece
    have htot : (15000 + 15000 * CR * (BL + 2) ^ 2) * (N ^ 2 * Real.log N)
        = 15000 * (N ^ 2 * Real.log N) + 15000 * CR * (BL + 2) ^ 2 * (N ^ 2 * Real.log N) := by ring
    linarith [h1, hfin, htot.le, htot.ge]
  have hgoal : (Real.log ((K : ℝ) + 2)) ^ 2 * Ev * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁)
      ≤ (15000 + 15000 * CR * (BL + 2) ^ 2) * (N ^ 2 * Real.log N) * X⁻¹ :=
    le_mul_inv_of_mul_le hXpos hmain
  calc (Real.log ((K : ℝ) + 2)) ^ 2 * Ev * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁)
      ≤ (15000 + 15000 * CR * (BL + 2) ^ 2) * (N ^ 2 * Real.log N) * X⁻¹ := hgoal
    _ = (15000 + 15000 * CR * (BL + 2) ^ 2) * X⁻¹ * N ^ 2 * Real.log N := by ring


/-- `N^{1-δ} * N = N^{2-δ}`. -/
lemma rpow_one_sub_mul {N δ : ℝ} (hN : 0 < N) : N ^ (1 - δ) * N = N ^ (2 - δ) := by
  have h1 : N ^ (1 - δ) * N = N ^ (1 - δ) * N ^ (1 : ℝ) := by rw [Real.rpow_one]
  rw [h1, ← Real.rpow_add hN, show (1 : ℝ) - δ + 1 = 2 - δ by ring]

lemma sqrt_A_eq {N : ℝ} (hN0 : 0 ≤ N) (hlog0 : 0 ≤ Real.log N) :
    Real.sqrt (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
      = Real.sqrt 2 * Real.sqrt N * (Real.log N) ^ (-(2 * 10 ^ 9 : ℝ)) := by
  have h1 : 2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ))
      = (2 * N) * ((Real.log N) ^ (-(4 * 10 ^ 9 : ℝ))) := by ring
  rw [h1, Real.sqrt_mul (by linarith : (0:ℝ) ≤ 2 * N),
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlog0]
  norm_num

lemma sqrt_B_eq {N X Lm CR : ℝ} (hX0 : 0 ≤ X) (hCR : 0 < CR) (hN0 : 0 ≤ N)
    (hLmnn : 0 ≤ Real.log (Lm + 2)) (hL2nn : 0 ≤ Real.log (N + 2)) :
    Real.sqrt (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
      = Real.sqrt (2 * CR) * Real.sqrt N * Real.log (Lm + 2)
          / (X * (Real.log (N + 2)) ^ ((5 : ℝ) / 2)) := by
  rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 * CR * N * (Real.log (Lm + 2)) ^ 2)]
  have hden : Real.sqrt (X ^ 2 * (Real.log (N + 2)) ^ 5)
      = X * (Real.log (N + 2)) ^ ((5 : ℝ) / 2) := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ X ^ 2), Real.sqrt_sq hX0, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast (Real.log (N + 2)) 5, ← Real.rpow_mul hL2nn]
    norm_num
  have hnum : Real.sqrt (2 * CR * N * (Real.log (Lm + 2)) ^ 2)
      = Real.sqrt (2 * CR) * Real.sqrt N * Real.log (Lm + 2) := by
    rw [show 2 * CR * N * (Real.log (Lm + 2)) ^ 2
          = (2 * CR) * (N * (Real.log (Lm + 2)) ^ 2) by ring,
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * CR),
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ N), Real.sqrt_sq hLmnn]
    ring
  rw [hden, hnum]

theorem ncExtrasS6_aux : ∀ (c₁ CR BL δ₁ : ℝ),
    0 < c₁ → 0 < CR → 0 ≤ BL → 0 < δ₁ → δ₁ < 3 / 32 →
    ∃ c N₀ : ℝ, 0 < c ∧
      ∀ {N X Lm UB Ev : ℝ} {K : ℕ} {θ : ℝ},
        N₀ ≤ N → 3 ≤ N → 1 ≤ X → 0 < θ → θ ≤ 1 → X ^ 8 ≤ N ^ δ₁ →
        1 ≤ (K : ℝ) → X ^ 3 * (Real.log (N + 2)) ^ 20 ≤ (K : ℝ) →
        (K : ℝ) ≤ 2 * X ^ 3 * (Real.log (N + 2)) ^ 20 →
        1 ≤ Lm → Lm ≤ (Real.log N) ^ BL → 0 < UB → UB ≤ 4 * θ * N + 2 → 0 ≤ Ev →
        Ev ≤ 2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ))
             + 2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5) →
          (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
              * Real.sqrt Ev * (5 * Real.sqrt N + N ^ (δ₁ / 2))
          ≤ c * X⁻¹ * N ^ 2 * Real.log N := by
  intro c₁ CR BL δ₁ hc1 hCR hBL hδ0 hδ32
  obtain ⟨NT1, hNT13, hNT1⟩ := exists_two_le_log
  obtain ⟨NT2, hNT23, hNT2⟩ := exists_log_rpow_le_rpow 1 (ε := 7 * δ₁ / 24) (by linarith)
  refine ⟨45000 * Real.sqrt 2 * c₁ + 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2),
    max (max NT1 NT2) 6, by positivity, ?_⟩
  intro N X Lm UB Ev K θ hN0 hN3 hX1 hθ0 hθ1 hX8 hK1 hKg hKu hLm1 hLmBL hUB0 hUB hEvnn hEv
  have hNT1le : NT1 ≤ N :=
    le_trans (le_trans (le_max_left NT1 NT2) (le_max_left (max NT1 NT2) 6)) hN0
  have hNT2le : NT2 ≤ N :=
    le_trans (le_trans (le_max_right NT1 NT2) (le_max_left (max NT1 NT2) 6)) hN0
  have hN6 : 6 ≤ N := le_trans (le_max_right (max NT1 NT2) 6) hN0
  have hlog2 : 2 ≤ Real.log N := hNT1 N hNT1le
  have hlogpow : Real.log N ≤ N ^ (7 * δ₁ / 24) := by simpa using hNT2 N hNT2le
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hN2 : 2 ≤ N := by linarith
  have hN3' : 3 ≤ N := by linarith
  have hXpos : 0 < X := by linarith
  have hLone : 1 ≤ Real.log N := Work.FIArea7.one_le_log_of_three_le hN3'
  have hL2one : 1 ≤ Real.log (N + 2) := Work.FIArea7.one_le_log_of_three_le (by linarith)
  have hL2nn : 0 ≤ Real.log (N + 2) := by linarith
  have hlogUBnn : 0 ≤ Real.log (UB + 2) := Real.log_nonneg (by linarith)
  have hK2 : (Real.log ((K : ℝ) + 2)) ^ 2 ≤ 2500 * (Real.log N) ^ 2 :=
    Work.FIArea7.nc_logK_bound (by linarith) hX1 hX8 hδ0 hδ32 hK1 hKu
  have hLm2 : Real.log (Lm + 2) ≤ (BL + 2) * Real.log N :=
    log_Lm_add_two_le hN3' hlog2 hLm1 hLmBL hBL
  have hLm2nn : 0 ≤ Real.log (Lm + 2) := Real.log_nonneg (by linarith)
  have hUB' : UB ≤ 4 * N + 2 := by nlinarith [hUB, hθ1]
  have hlogUB : Real.log (UB + 2) ≤ 2 * Real.log N := log_UB_add_two_le hUB0 hUB' hN6
  have h1UB : 1 + Real.log (UB + 2) ≤ 3 * Real.log N := by linarith
  have hsqA := sqrt_A_eq hNpos.le (by linarith)
  have hsqB := sqrt_B_eq (CR := CR) hXpos.le hCR hNpos.le hLm2nn hL2nn
  have hAnn : 0 ≤ 2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)) := by positivity
  have hBnn : 0 ≤ 2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5) := by
    positivity
  have hsqrtEv : Real.sqrt Ev ≤ Real.sqrt (2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ)))
      + Real.sqrt (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5)) :=
    le_trans (Real.sqrt_le_sqrt hEv) (sqrt_add_le' hAnn hBnn)
  -- replace `Real.log N` by a local variable `L`
  set L : ℝ := Real.log N with hL
  rw [← hL] at *
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := by linarith
  -- elementary power/log bounds
  have hXle : X ≤ N ^ (δ₁ / 8) :=
    Work.FIArea7.le_rpow_div_eight_of_pow_eight_le hXpos.le hNpos hX8
  have hlog3 : L ^ 3 * L ^ (-(2 * 10 ^ 9 : ℝ)) ≤ L := by
    have h3 : L ^ 3 * L ^ (-(2 * 10 ^ 9 : ℝ))
        = L ^ ((3 : ℝ) + (-(2 * 10 ^ 9 : ℝ))) := by
      rw [← Real.rpow_natCast L 3, ← Real.rpow_add hLpos]
      push_cast
      ring
    rw [h3]
    calc L ^ ((3 : ℝ) + (-(2 * 10 ^ 9 : ℝ))) ≤ L ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
      _ = L := Real.rpow_one L
  have hlog2sq : L ^ 2 ≤ N ^ (7 * δ₁ / 12) := by
    have h1 : L ^ 2 ≤ (N ^ (7 * δ₁ / 24)) ^ 2 := pow_le_pow_left₀ hLnn hlogpow 2
    have h2 : (N ^ (7 * δ₁ / 24)) ^ 2 = N ^ (7 * δ₁ / 12) := by
      rw [← Real.rpow_natCast (N ^ (7 * δ₁ / 24)) 2, ← Real.rpow_mul hNpos.le]
      ring_nf
    rwa [h2] at h1
  have hfacA : X ^ 2 * N ^ (-δ₁) * L ≤ 1 := by
    have h1 : X ^ 2 * N ^ (-δ₁) ≤ N ^ (-(3 * δ₁ / 4)) := by
      have h5 : X ^ 2 ≤ N ^ (δ₁ / 4) := sq_le_rpow_of_pow_eight_le hN1 hX1 hX8
      calc X ^ 2 * N ^ (-δ₁) ≤ N ^ (δ₁ / 4) * N ^ (-δ₁) :=
            mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hNpos.le _)
        _ = N ^ (δ₁ / 4 - δ₁) := by rw [← Real.rpow_add hNpos]; ring_nf
        _ = N ^ (-(3 * δ₁ / 4)) := by congr 1; ring
    calc X ^ 2 * N ^ (-δ₁) * L ≤ N ^ (-(3 * δ₁ / 4)) * N ^ (7 * δ₁ / 24) :=
          mul_le_mul h1 hlogpow hLnn (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (-(11 * δ₁ / 24)) := by rw [← Real.rpow_add hNpos]; congr 1; ring
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hlog3b : L ^ 3 ≤ N ^ (7 * δ₁ / 8) := by
    have h0 : L ^ (3 : ℝ) ≤ (N ^ (7 * δ₁ / 24)) ^ (3 : ℝ) :=
      Real.rpow_le_rpow hLnn hlogpow (by norm_num)
    have h2 : (N ^ (7 * δ₁ / 24)) ^ (3 : ℝ) = N ^ (7 * δ₁ / 8) := by
      rw [← Real.rpow_mul hNpos.le]
      congr 1
      ring
    rw [h2] at h0
    simpa using h0
  have hfacB : X * N ^ (-δ₁) * L ^ 3 ≤ 1 := by
    have h1 : X * N ^ (-δ₁) ≤ N ^ (-(7 * δ₁ / 8)) := by
      calc X * N ^ (-δ₁) ≤ N ^ (δ₁ / 8) * N ^ (-δ₁) :=
            mul_le_mul_of_nonneg_right hXle (Real.rpow_nonneg hNpos.le _)
        _ = N ^ (δ₁ / 8 - δ₁) := by rw [← Real.rpow_add hNpos]; ring_nf
        _ = N ^ (-(7 * δ₁ / 8)) := by congr 1; ring
    calc X * N ^ (-δ₁) * L ^ 3 ≤ N ^ (-(7 * δ₁ / 8)) * N ^ (7 * δ₁ / 8) :=
          mul_le_mul h1 hlog3b (pow_nonneg hLnn 3) (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (-(7 * δ₁ / 8) + 7 * δ₁ / 8) := by rw [← Real.rpow_add hNpos]
      _ = N ^ (0 : ℝ) := by congr 1; ring
      _ = 1 := Real.rpow_zero N
  have h2sqrt : (5 * Real.sqrt N + N ^ (δ₁ / 2)) * Real.sqrt N ≤ 6 * N := by
    have h3 : N ^ (δ₁ / 2) ≤ Real.sqrt N := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h4 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
    nlinarith [h3, h4, Real.sqrt_nonneg N, hN1]
  have hN6mul : N ^ (1 - δ₁) * (6 * N) = 6 * N ^ (2 - δ₁) := by
    have h := rpow_one_sub_mul (δ := δ₁) hNpos
    calc N ^ (1 - δ₁) * (6 * N) = 6 * (N ^ (1 - δ₁) * N) := by ring
      _ = 6 * N ^ (2 - δ₁) := by rw [h]
  -- ===== piece A (Rankin square root) =====
  have hPieceA : (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
        * (5 * Real.sqrt N + N ^ (δ₁ / 2)) * Real.sqrt (2 * N * L ^ (-(4 * 10 ^ 9 : ℝ))) * X
      ≤ 45000 * Real.sqrt 2 * c₁ * (N ^ 2 * L) := by
    rw [hsqA]
    have hre : (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
          * (5 * Real.sqrt N + N ^ (δ₁ / 2)) * (Real.sqrt 2 * Real.sqrt N * L ^ (-(2 * 10 ^ 9 : ℝ))) * X
        = Real.sqrt 2 * c₁ * ((Real.log ((K : ℝ) + 2)) ^ 2 * (1 + Real.log (UB + 2)) * N ^ (1 - δ₁)
            * ((5 * Real.sqrt N + N ^ (δ₁ / 2)) * Real.sqrt N) * L ^ (-(2 * 10 ^ 9 : ℝ)) * X ^ 2) := by
      ring
    rw [hre]
    calc Real.sqrt 2 * c₁ * ((Real.log ((K : ℝ) + 2)) ^ 2 * (1 + Real.log (UB + 2)) * N ^ (1 - δ₁)
            * ((5 * Real.sqrt N + N ^ (δ₁ / 2)) * Real.sqrt N) * L ^ (-(2 * 10 ^ 9 : ℝ)) * X ^ 2)
        ≤ Real.sqrt 2 * c₁ * ((2500 * L ^ 2) * (3 * L) * N ^ (1 - δ₁)
            * (6 * N) * L ^ (-(2 * 10 ^ 9 : ℝ)) * X ^ 2) := by gcongr
      _ = 45000 * Real.sqrt 2 * c₁ * (N ^ (2 - δ₁) * (L ^ 3 * L ^ (-(2 * 10 ^ 9 : ℝ))) * X ^ 2) := by
          have hstep : 2500 * L ^ 2 * (3 * L) * N ^ (1 - δ₁) * (6 * N) * L ^ (-(2 * 10 ^ 9 : ℝ)) * X ^ 2
              = 7500 * (N ^ (1 - δ₁) * (6 * N)) * L ^ 3 * L ^ (-(2 * 10 ^ 9 : ℝ)) * X ^ 2 := by ring
          rw [hstep, hN6mul]
          ring
      _ = 45000 * Real.sqrt 2 * c₁
            * (N ^ 2 * (X ^ 2 * N ^ (-δ₁) * (L ^ 3 * L ^ (-(2 * 10 ^ 9 : ℝ))))) := by
          have hsplit : N ^ (2 - δ₁) * (L ^ 3 * L ^ (-(2 * 10 ^ 9 : ℝ))) * X ^ 2
              = N ^ 2 * (X ^ 2 * N ^ (-δ₁) * (L ^ 3 * L ^ (-(2 * 10 ^ 9 : ℝ)))) := by
            rw [show (2 : ℝ) - δ₁ = 2 + (-δ₁) by ring, Real.rpow_add hNpos, Real.rpow_two]
            ring
          rw [hsplit]
      _ ≤ 45000 * Real.sqrt 2 * c₁ * (N ^ 2 * (X ^ 2 * N ^ (-δ₁) * L)) := by
          have hc : (0:ℝ) ≤ 45000 * Real.sqrt 2 * c₁ := by positivity
          have hNL : (0:ℝ) ≤ N ^ 2 := by positivity
          have h1 : X ^ 2 * N ^ (-δ₁) * (L ^ 3 * L ^ (-(2 * 10 ^ 9 : ℝ)))
              ≤ X ^ 2 * N ^ (-δ₁) * L :=
            mul_le_mul_of_nonneg_left hlog3 (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hNL) hc
      _ ≤ 45000 * Real.sqrt 2 * c₁ * (N ^ 2 * 1) := by
          have hc : (0:ℝ) ≤ 45000 * Real.sqrt 2 * c₁ := by positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfacA (by positivity)) hc
      _ ≤ 45000 * Real.sqrt 2 * c₁ * (N ^ 2 * L) := by
          have h1 : N ^ 2 * 1 ≤ N ^ 2 * L := mul_le_mul_of_nonneg_left hLone (by positivity)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
  -- ===== piece B (truncation square root) =====
  have hBfrac : Real.sqrt (2 * CR) * Real.sqrt N * Real.log (Lm + 2)
        / (X * (Real.log (N + 2)) ^ ((5 : ℝ) / 2))
      ≤ Real.sqrt (2 * CR) * Real.sqrt N * Real.log (Lm + 2) / X := by
    apply div_le_div_of_nonneg_left (by positivity) hXpos
    have h1 : 1 ≤ (Real.log (N + 2)) ^ ((5 : ℝ) / 2) := Real.one_le_rpow hL2one (by norm_num)
    nlinarith [h1, hXpos]
  have hPieceB : (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
        * (5 * Real.sqrt N + N ^ (δ₁ / 2))
        * Real.sqrt (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5)) * X
      ≤ 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * (N ^ 2 * L) := by
    rw [hsqB]
    have hstep1 : (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
          * (5 * Real.sqrt N + N ^ (δ₁ / 2))
          * (Real.sqrt (2 * CR) * Real.sqrt N * Real.log (Lm + 2)
              / (X * (Real.log (N + 2)) ^ ((5 : ℝ) / 2))) * X
        ≤ (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
          * (5 * Real.sqrt N + N ^ (δ₁ / 2))
          * (Real.sqrt (2 * CR) * Real.sqrt N * Real.log (Lm + 2) / X) * X := by
      apply mul_le_mul_of_nonneg_right _ hXpos.le
      apply mul_le_mul_of_nonneg_left hBfrac (by positivity)
    have hcancel : (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
          * (5 * Real.sqrt N + N ^ (δ₁ / 2))
          * (Real.sqrt (2 * CR) * Real.sqrt N * Real.log (Lm + 2) / X) * X
        = Real.sqrt (2 * CR) * Real.log (Lm + 2)
          * ((Real.log ((K : ℝ) + 2)) ^ 2 * (1 + Real.log (UB + 2)) * c₁ * N ^ (1 - δ₁)
            * ((5 * Real.sqrt N + N ^ (δ₁ / 2)) * Real.sqrt N) * X) := by
      field_simp
    rw [hcancel] at hstep1
    have hstep2 : Real.sqrt (2 * CR) * Real.log (Lm + 2)
          * ((Real.log ((K : ℝ) + 2)) ^ 2 * (1 + Real.log (UB + 2)) * c₁ * N ^ (1 - δ₁)
            * ((5 * Real.sqrt N + N ^ (δ₁ / 2)) * Real.sqrt N) * X)
        ≤ Real.sqrt (2 * CR) * ((BL + 2) * L)
          * ((2500 * L ^ 2) * (3 * L) * c₁ * N ^ (1 - δ₁) * (6 * N) * X) := by gcongr
    have hstep3 : Real.sqrt (2 * CR) * ((BL + 2) * L)
          * ((2500 * L ^ 2) * (3 * L) * c₁ * N ^ (1 - δ₁) * (6 * N) * X)
        = 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * (X * N ^ (2 - δ₁) * L ^ 4) := by
      have hstep3' : Real.sqrt (2 * CR) * ((BL + 2) * L)
            * ((2500 * L ^ 2) * (3 * L) * c₁ * N ^ (1 - δ₁) * (6 * N) * X)
          = 7500 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * (N ^ (1 - δ₁) * (6 * N)) * L ^ 4 * X := by
        ring_nf
      rw [hstep3', hN6mul]
      ring_nf
    have hstep4 : 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * (X * N ^ (2 - δ₁) * L ^ 4)
        ≤ 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * (N ^ 2 * L) := by
      have hsplit4 : X * N ^ (2 - δ₁) * L ^ 4 = (N ^ 2 * L) * (X * N ^ (-δ₁) * L ^ 3) := by
        rw [show (2 : ℝ) - δ₁ = 2 + (-δ₁) by ring, Real.rpow_add hNpos, Real.rpow_two]
        ring
      rw [hsplit4]
      have hc : (0:ℝ) ≤ 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * (N ^ 2 * L) := by positivity
      calc 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * ((N ^ 2 * L) * (X * N ^ (-δ₁) * L ^ 3))
          = (45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * (N ^ 2 * L)) * (X * N ^ (-δ₁) * L ^ 3) := by
            ring
        _ ≤ (45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * (N ^ 2 * L)) * 1 :=
            mul_le_mul_of_nonneg_left hfacB (by positivity)
        _ = 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * (N ^ 2 * L) := by ring
    linarith [hstep1, hstep2, hstep3.le, hstep3.ge, hstep4]
  -- ===== assembly =====
  have hPnn : 0 ≤ (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2))
      * (c₁ * N ^ (1 - δ₁)) * (5 * Real.sqrt N + N ^ (δ₁ / 2)) := by positivity
  have hreass : (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
        * Real.sqrt Ev * (5 * Real.sqrt N + N ^ (δ₁ / 2))
      = ((Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
          * (5 * Real.sqrt N + N ^ (δ₁ / 2))) * Real.sqrt Ev := by ring
  have hstep : (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
        * Real.sqrt Ev * (5 * Real.sqrt N + N ^ (δ₁ / 2))
      ≤ ((Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
          * (5 * Real.sqrt N + N ^ (δ₁ / 2)))
        * (Real.sqrt (2 * N * L ^ (-(4 * 10 ^ 9 : ℝ)))
          + Real.sqrt (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))) := by
    rw [hreass]
    exact mul_le_mul_of_nonneg_left hsqrtEv hPnn
  have hLa : ((Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
          * (5 * Real.sqrt N + N ^ (δ₁ / 2))) * Real.sqrt (2 * N * L ^ (-(4 * 10 ^ 9 : ℝ)))
      ≤ 45000 * Real.sqrt 2 * c₁ * (N ^ 2 * L) * X⁻¹ :=
    le_mul_inv_of_mul_le hXpos hPieceA
  have hLb : ((Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
          * (5 * Real.sqrt N + N ^ (δ₁ / 2)))
        * Real.sqrt (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5))
      ≤ 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * (N ^ 2 * L) * X⁻¹ :=
    le_mul_inv_of_mul_le hXpos hPieceB
  have hexpand : ((Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
          * (5 * Real.sqrt N + N ^ (δ₁ / 2)))
        * (Real.sqrt (2 * N * L ^ (-(4 * 10 ^ 9 : ℝ)))
          + Real.sqrt (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5)))
      = ((Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
          * (5 * Real.sqrt N + N ^ (δ₁ / 2))) * Real.sqrt (2 * N * L ^ (-(4 * 10 ^ 9 : ℝ)))
        + ((Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
          * (5 * Real.sqrt N + N ^ (δ₁ / 2)))
          * Real.sqrt (2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5)) := by
    ring
  calc (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2)) * (c₁ * N ^ (1 - δ₁))
        * Real.sqrt Ev * (5 * Real.sqrt N + N ^ (δ₁ / 2))
      ≤ _ := hstep
    _ = _ := hexpand
    _ ≤ 45000 * Real.sqrt 2 * c₁ * (N ^ 2 * L) * X⁻¹
        + 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2) * (N ^ 2 * L) * X⁻¹ := by
          linarith [hLa, hLb]
    _ = (45000 * Real.sqrt 2 * c₁ + 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2)) * X⁻¹
          * N ^ 2 * L := by ring
    _ = (45000 * Real.sqrt 2 * c₁ + 45000 * Real.sqrt (2 * CR) * c₁ * (BL + 2)) * X⁻¹
          * N ^ 2 * Real.log N := by rw [hL]


/-! ## The assembly -/

theorem numeric_core_proof_B : Work.FIArea7.NumericCoreB := by
  intro C_L C_H C_E C_G c₁ Clat CP CX CR BL hCL hCH hCE hCG hc₁ hCl hCP hCX hCR hBL δ₁ hδ0 hδ32
  obtain ⟨c0, N00, hc0pos, hnum⟩ :=
    Work.FIArea7.numeric_core_proof C_L (2 * C_H) C_E C_G c₁ Clat δ₁
      hCL (by linarith) hCE hCG hc₁ hCl hδ0 hδ32
  have hnuU : Work.FITop4.nuU ≤ 4 * 10 ^ 9 - 2 := by
    norm_num [Work.FITop4.nuU, Work.FITop4.sigmaChoice, Work.FITop4.Aprime, Work.FITop4.Asave]
  obtain ⟨csx, Nsx, hcsxpos, hsx⟩ := ncExtrasSx_aux Clat BL δ₁ hCl hBL hδ0 hδ32
  obtain ⟨c5, N5, hc5pos, h5⟩ := ncExtrasS5_aux CR BL δ₁ Work.FITop4.nuU hCR hBL hδ0 hδ32 hnuU
  obtain ⟨c6, N6, hc6pos, h6⟩ := ncExtrasS6_aux c₁ CR BL δ₁ hc₁ hCR hBL hδ0 hδ32
  refine ⟨c0 + (C_H + CP + CX) * (csx + c5 + c6), max (max N00 Nsx) (max N5 N6),
    by positivity, ?_⟩
  intro N X Lm K L₀ θ Pz UB E2v Ev hN0 hN3 hX1 hθ0 hθ1 hX8 hXcap hPz0 hK1 hKg hKu hL0 hLm1 hLmBL
    hUB0 hUB hE2nn hE2 hEvnn hEv
  rw [show (2 : ℝ) + N = N + 2 by ring]
  have hN00 : N00 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN0
  have hNsx : Nsx ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN0
  have hN5 : N5 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN0
  have hN6 : N6 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN0
  have hNpos : 0 < N := by linarith
  have hlogNnn : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlog2Nnn : 0 ≤ Real.log (N + 2) := Real.log_nonneg (by linarith)
  have hlogX2nn : 0 ≤ Real.log (X + 2) := Real.log_nonneg (by linarith)
  have hlogUBnn : 0 ≤ Real.log (UB + 2) := Real.log_nonneg (by linarith)
  -- the four inputs
  have hcore := hnum hN00 hN3 hX1 hθ0 hθ1 hX8 hPz0 hK1 hKg hKu hUB0 hUB hE2nn hE2
  rw [show (2 : ℝ) + N = N + 2 by ring] at hcore
  have hSxle := hsx hNsx hN3 hX1 hθ0 hθ1 hX8 hK1 hKg hKu hLm1 hLmBL
  have hS5le := h5 hN5 hN3 hX1 hX8 hXcap hK1 hKg hKu hLm1 hLmBL hEvnn hEv
  have hS6le := h6 hN6 hN3 hX1 hθ0 hθ1 hX8 hK1 hKg hKu hLm1 hLmBL hUB0 hUB hEvnn hEv
  -- ===== abbreviations =====
  set T1n : ℝ := C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
      * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1)
          + (N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1) ^ ((3 : ℝ) / 2)) with hT1n
  set T2n : ℝ := C_H * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
      * (Real.log ((K : ℝ) + 2)) ^ 2
      * (X * (2 * (K : ℝ) + (L₀ : ℝ) + 2) * N ^ (1 - δ₁) + X * Real.log (UB + 2)) with hT2n
  set T3g : ℝ := C_E * (X + 1) * (N + 1) * (Real.log (N + 2)) ^ 4 * E2v / (K : ℝ) with hT3g
  set T4g : ℝ := C_G * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log (N + 2) with hT4g
  set S5g : ℝ := CP * (Real.log ((K : ℝ) + 2)) ^ 2 * Ev * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁)
    with hS5g
  set S6g : ℝ := CX * (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2))
      * (c₁ * N ^ (1 - δ₁)) * Real.sqrt Ev * (5 * Real.sqrt N + N ^ (δ₁ / 2)) with hS6g
  -- ===== step 1: the region-I term decreases when `2K+1` is replaced by `2K+L₀+2` =====
  have hT1 : T1n ≤
      C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
        * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
            + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2)) := by
    rw [hT1n]
    have hden : (0 : ℝ) < 2 * (K : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (K : ℝ) := hK1
      linarith
    have hle : 2 * (K : ℝ) + 1 ≤ 2 * (K : ℝ) + (L₀ : ℝ) + 2 := by linarith
    have hNδ : 0 ≤ N ^ δ₁ := Real.rpow_nonneg hNpos.le _
    have hu : N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ N ^ δ₁ / (2 * (K : ℝ) + 1) :=
      div_le_div_of_nonneg_left hNδ hden hle
    have h1 : N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1 ≤ N ^ δ₁ / (2 * (K : ℝ) + 1) + 1 := by
      linarith
    have h2 : (0 : ℝ) ≤ N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1 := by positivity
    have hsq : Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1)
        ≤ Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) := Real.sqrt_le_sqrt h1
    have hrp : (N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1) ^ ((3 : ℝ) / 2)
        ≤ (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow h2 h1 (by norm_num)
    have hpre : (0 : ℝ) ≤ C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2 := by
      positivity
    have hX0 : 0 ≤ X := by linarith
    exact mul_le_mul_of_nonneg_left
      (by linarith [mul_le_mul_of_nonneg_left hsq hX0, hrp]) hpre
  -- ===== step 2: the region-II term, with the mode slack =====
  have hT2split : C_H * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2
        * (X * (2 * (K : ℝ) + (L₀ : ℝ) + 2) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
      = C_H * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2
        * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
      + C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * ((L₀ : ℝ) + 1) * N ^ (1 - δ₁))) := by
    ring
  have hT2extra : C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * ((L₀ : ℝ) + 1) * N ^ (1 - δ₁)))
      ≤ C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁)))
      + C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁))) := by
    have hL01 : (L₀ : ℝ) + 1 ≤ (2 * (K : ℝ) + 1) + (2 * Lm + 2) := by linarith
    have hnn : 0 ≤ C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2) * X * N ^ (1 - δ₁) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hL01 hnn]
  have hT2 : T2n ≤
      (2 * C_H) * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2
        * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
      + C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁))) := by
    rw [hT2n]
    have hstep1 : C_H * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * (2 * (K : ℝ) + (L₀ : ℝ) + 2) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
        ≤ C_H * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
        + C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁)))
        + C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁))) := by
      linarith [hT2split.le, hT2split.ge, hT2extra]
    have hmid : C_H * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
        + C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁)))
        = (2 * C_H) * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
        - C_H * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2 * X * Real.log (UB + 2) := by ring
    have hlogUBterm : 0 ≤ C_H * (1 + Clat)
        * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2 * X * Real.log (UB + 2) := by positivity
    linarith [hstep1, hmid, hlogUBterm]
  -- ===== the numeric core =====
  have hcore' : C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
        * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
            + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2))
      + (2 * C_H) * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2
        * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
      + C_E * (X + 1) * (N + 1) * (Real.log (N + 2)) ^ 4 * E2v / (K : ℝ)
      + C_G * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log (N + 2)
      ≤ c0 * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log N := hcore
  -- ===== the extras =====
  have hS5g_eq : S5g = CP * ((Real.log ((K : ℝ) + 2)) ^ 2 * Ev
      * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁)) := by rw [hS5g]; ring
  have hS6g_eq : S6g = CX * ((Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2))
      * (c₁ * N ^ (1 - δ₁)) * Real.sqrt Ev * (5 * Real.sqrt N + N ^ (δ₁ / 2))) := by
    rw [hS6g]; ring
  have hS5_nn : 0 ≤ (Real.log ((K : ℝ) + 2)) ^ 2 * Ev
      * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁) := by positivity
  have hS6_nn : 0 ≤ (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2))
      * (c₁ * N ^ (1 - δ₁)) * Real.sqrt Ev * (5 * Real.sqrt N + N ^ (δ₁ / 2)) := by positivity
  have hSx_nn : 0 ≤ (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
      * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁)) := by positivity
  have hsum : C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
        * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁))) + S5g + S6g
      ≤ (C_H + CP + CX) * (csx + c5 + c6) * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) := by
    rw [hS5g_eq, hS6g_eq]
    have h1 : C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁)))
        ≤ C_H * (csx * X⁻¹ * N ^ 2 * Real.log N) :=
      mul_le_mul_of_nonneg_left hSxle hCH.le
    have h2 : CP * ((Real.log ((K : ℝ) + 2)) ^ 2 * Ev * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁))
        ≤ CP * (c5 * X⁻¹ * N ^ 2 * Real.log N) :=
      mul_le_mul_of_nonneg_left hS5le hCP.le
    have h3 : CX * ((Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2))
          * (c₁ * N ^ (1 - δ₁)) * Real.sqrt Ev * (5 * Real.sqrt N + N ^ (δ₁ / 2)))
        ≤ CX * (c6 * X⁻¹ * N ^ 2 * Real.log N) :=
      mul_le_mul_of_nonneg_left hS6le hCX.le
    have hXinv_nn : 0 ≤ X⁻¹ * N ^ 2 * Real.log N := by positivity
    have hcore0 : X⁻¹ * N ^ 2 * Real.log N ≤ (Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N) := by
      have hle : X⁻¹ ≤ Pz⁻¹ + X⁻¹ := by
        have := inv_pos.mpr hPz0
        linarith
      have h2 := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ N ^ 2 * Real.log N)
      calc X⁻¹ * N ^ 2 * Real.log N = X⁻¹ * (N ^ 2 * Real.log N) := by ring
        _ ≤ (Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N) := h2
    have hmid : C_H * (csx * (X⁻¹ * N ^ 2 * Real.log N))
        + CP * (c5 * (X⁻¹ * N ^ 2 * Real.log N))
        + CX * (c6 * (X⁻¹ * N ^ 2 * Real.log N))
        = (C_H * csx + CP * c5 + CX * c6) * (X⁻¹ * N ^ 2 * Real.log N) := by ring
    have hle2 : C_H * csx + CP * c5 + CX * c6 ≤ (C_H + CP + CX) * (csx + c5 + c6) := by
      nlinarith [hcsxpos, hc5pos, hc6pos, hCH.le, hCP.le, hCX.le]
    calc C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
            * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁)))
          + CP * ((Real.log ((K : ℝ) + 2)) ^ 2 * Ev * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁))
          + CX * ((Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2))
              * (c₁ * N ^ (1 - δ₁)) * Real.sqrt Ev * (5 * Real.sqrt N + N ^ (δ₁ / 2)))
        ≤ C_H * (csx * (X⁻¹ * N ^ 2 * Real.log N)) + CP * (c5 * (X⁻¹ * N ^ 2 * Real.log N))
          + CX * (c6 * (X⁻¹ * N ^ 2 * Real.log N)) := by linarith
      _ = (C_H * csx + CP * c5 + CX * c6) * (X⁻¹ * N ^ 2 * Real.log N) := hmid
      _ ≤ ((C_H + CP + CX) * (csx + c5 + c6)) * (X⁻¹ * N ^ 2 * Real.log N) :=
          mul_le_mul_of_nonneg_right hle2 hXinv_nn
      _ ≤ ((C_H + CP + CX) * (csx + c5 + c6)) * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) :=
          mul_le_mul_of_nonneg_left hcore0 (by positivity)
      _ = (C_H + CP + CX) * (csx + c5 + c6) * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) := by ring
  -- ===== final assembly =====
  have hstep1 : T1n + T2n + T3g + T4g + S5g + S6g
      ≤ C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
              + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2))
        + ((2 * C_H) * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
            * (Real.log ((K : ℝ) + 2)) ^ 2
            * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
          + C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
            * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁))))
        + T3g + T4g + S5g + S6g := by
    linarith [hT1, hT2]
  have hstep2 : C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
              + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2))
        + ((2 * C_H) * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
            * (Real.log ((K : ℝ) + 2)) ^ 2
            * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
          + C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
            * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁))))
        + T3g + T4g + S5g + S6g
      ≤ c0 * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log N
        + (C_H + CP + CX) * (csx + c5 + c6) * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) := by
    rw [← hT3g, ← hT4g] at hcore'
    linarith [hcore', hsum]
  calc T1n + T2n + T3g + T4g + S5g + S6g
      ≤ C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
              + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2))
        + ((2 * C_H) * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
            * (Real.log ((K : ℝ) + 2)) ^ 2
            * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
          + C_H * ((1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3)
            * (Real.log ((K : ℝ) + 2)) ^ 2 * (X * (2 * Lm + 2) * N ^ (1 - δ₁))))
        + T3g + T4g + S5g + S6g := hstep1
    _ ≤ c0 * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log N
        + (C_H + CP + CX) * (csx + c5 + c6) * ((Pz⁻¹ + X⁻¹) * (N ^ 2 * Real.log N)) := hstep2
    _ = (c0 + (C_H + CP + CX) * (csx + c5 + c6)) * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log N := by ring
end Work.FIArea7CF
