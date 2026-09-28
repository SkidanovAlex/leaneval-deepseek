import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiDefs
import Submission.Work.HP.Sig2.le_mul_log_of_div_log_le
import Submission.Work.HP.Sig2.log_pow_le_rpow
import Submission.Work.HP.MDEstimates.hiparts.HiAssembly

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.HP.MDEstimates.hiparts

/-! ## Comparisons of the universal constant `1900` with the conversion constants -/

lemma hc_cmp_T1 (x : ℝ) (h : x ≤ 1900) : x ≤ 2000 - Real.log 128 := by
  have h1 := hc_log_128_le
  linarith

lemma hc_cmp_T1Q (x : ℝ) (h : x ≤ 1900) : x ≤ 2000 - 59 * Real.log 2 := by
  have h1 := hc_log_two_le_07
  linarith

lemma hc_cmp_T2P (k : ℕ) (x : ℝ) (hk : 4 ≤ k) (h : x ≥ -1900) :
    x ≥ -2000 + Real.log 128 + ((67:ℝ) - (k:ℝ)) * Real.log 2 := by
  have h1 := hc_log_128_le
  have h2 := hc_log_two_le_07
  have h2pos : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hk4 : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hmul : ((67:ℝ) - (k:ℝ)) * Real.log 2 ≤ 63 * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith) h2pos
  linarith

lemma hc_cmp_T2Q (k : ℕ) (x : ℝ) (hk : 4 ≤ k) (h : x ≥ -1900) :
    x ≥ -2000 + ((126:ℝ) - (k:ℝ)) * Real.log 2 := by
  have h2 := hc_log_two_le_07
  have h2pos : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hk4 : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hmul : ((126:ℝ) - (k:ℝ)) * Real.log 2 ≤ 122 * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith) h2pos
  linarith

lemma hc_cmp_BP_T2 (x : ℝ) (h : x ≥ -1900) : x ≥ -2000 + Real.log 128 + 61 * Real.log 2 := by
  have h1 := hc_log_128_le
  have h2 := hc_log_two_le_07
  linarith

lemma hc_cmp_BQ_T2 (x : ℝ) (h : x ≥ -1900) : x ≥ -2000 + 120 * Real.log 2 := by
  have h1 := hc_log_two_le_07
  linarith

/-- **Per-cell arithmetic for the `𝔡₃ > A^{1/20}` part of the case-`I` sum at `(d,n) = (4,4)`.**
Here `N_{4,4} - 2 = 68` is the rank of `Γ_{x,y}`, `hiCell A B d l R0 = A^{68-R0} B^{2R0-8} d^{-R0} + (2A/l)^{67-R0}`
is the `R0`-th term of the Lemma-R0 bound, `hiLZ B Δ M = B^{9/2}Δ²(B^{3/2}+Δ^{3/2})(log 2Δ)²min{Δ,M^{53}}`
is the convenient `ℓ^{(1)}` bound (`MDEstimates.ell44_convenient` at `Z = B`), and
`hiMin A B d l = min_{4 ≤ R0 ≤ 67} hiCell A B d l R0`.

The assertion is that one dyadic cell (with `𝔡₃`-cutoff `Δ` and `λ₁`-cutoff `M`), whose pair count
is at most `hiLZ B (2Δ) (2M)` (the convenient `ℓ^{(1)}` bound evaluated at the doubled cutoffs),
contributes at most `K A^{68-1/32} B² B^{-1/1000}`.

Hints.  Set `a = log A`, `b = log B`, `d = log Δ`, `m = log M`; the claim is
`log (hiLZ B (2Δ) (2M)) + log (hiMin A B Δ M) ≤ (68 - 1/32) a + 2b - b/1000` up to `log K`.
Since `hiMin ≤ hiCell (R0)` for every `R0 ∈ {4,…,67}` (`hiMin_le_cell`), it suffices to exhibit,
for each `Δ, M` in the range, a single `R0` (allowed to depend on `Δ` and `M`) with
`hiLZ B (2Δ) (2M) * hiCell A B Δ M R0 ≤ K A^{68-1/32} B² B^{-1/1000}`.

* `hiLZ B (2Δ) (2M) ≈ B^{9/2}(2Δ)²(B^{3/2}+(2Δ)^{3/2})(log 4Δ)² min{2Δ,(2M)^{53}}`; the first term
  of `hiCell` is increasing in `R0`, the second decreasing, and they cross near
  `R0 ≈ (8b - a)/(2b - d)` (clamped to `{4,…,67}`), so a case split on ranges of `Δ` with
  `R0 = 4, 5, 6, 7` and `R0 = 67` (the latter needed only when `Δ ≥ B²/A`, i.e. when
  `B²/(AΔ) ≤ 1`) suffices. Beware the two branches of `min{2Δ,(2M)^{53}}`.
* Use `B ≤ C A (log A + 1)` (`Work.HP.Sig2.le_mul_log_of_div_log_le`) to convert powers of `B`
  into powers of `A`, and `(log A + 1)^m ≤ A^ε` (`Work.HP.Sig2.log_pow_le_rpow`) together with
  `B₀ ≤ B` to absorb logarithmic factors into the margin `B^{-1/1000}`.
* The margin is genuinely thin (at `A ≈ B` the worst cells are near `Δ ≈ B^{0.52}`,
  `M ≈ B^{0.01}` with `R0 = 4`), so the proof must track the exponents; but a positive power
  margin of roughly `B^{-0.015}` is available, and `B₀` may be taken astronomically large. -/
theorem hi_cell_arith :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B Δ M : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      A ^ ((1 : ℝ) / 20) ≤ Δ → Δ ≤ 48 * B ^ 2 / A → 1 ≤ M → M ≤ A →
      hiLZ B (2 * Δ) (2 * M) * hiMin A B Δ M
        ≤ K * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ)) := by
  obtain ⟨B₁, hB₁, hlogsq⟩ := log_sq_le
  refine ⟨hiK, max (max B₁ ((9:ℝ)^2000)) (Real.exp 1000000), hiK_pos, ?_⟩
  intro A B Δ M hB hAB hAB2 hΔ1 hΔ2 hM1 hM2
  have hBexp : Real.exp 1000000 ≤ B := le_trans (le_max_right _ _) hB
  have hB9 : (9:ℝ)^2000 ≤ B := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hB)
  have hBB₁ : B₁ ≤ B := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hB)
  have hBpos : 0 < B := lt_of_lt_of_le (Real.exp_pos 1000000) hBexp
  have hB1 : (1:ℝ) ≤ B :=
    le_trans (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)) hBexp
  have hlogB : (1000000:ℝ) ≤ Real.log B := by
    have h := Real.log_le_log (Real.exp_pos 1000000) hBexp
    rwa [Real.log_exp] at h
  have hlogBpos : 0 < Real.log B := by linarith
  have hdivpos : 0 < B / Real.log B := div_pos hBpos hlogBpos
  have hApos : 0 < A := lt_of_lt_of_le hdivpos hAB
  have hA1 : (1:ℝ) ≤ A := by
    have h2 : 1 ≤ B / Real.log B := by
      rw [le_div_iff₀ hlogBpos]
      nlinarith [Real.log_le_self hBpos.le, hB1]
    linarith
  have hlogA : Real.log (B / Real.log B) ≤ Real.log A := Real.log_le_log hdivpos hAB
  have hlogdiv : Real.log (B / Real.log B) = Real.log B - Real.log (Real.log B) := by
    rw [Real.log_div (ne_of_gt hBpos) (ne_of_gt hlogBpos)]
  have ha : Real.log B - Real.log (Real.log B) ≤ Real.log A := by
    rw [← hlogdiv]; exact hlogA
  have hll : Real.log (Real.log B) ≤ Real.log B / 400 + 400 := hc_log_le_div_add _ hlogBpos
  have hΔ1' : (1:ℝ) ≤ Δ := le_trans (Real.one_le_rpow hA1 (by norm_num)) hΔ1
  have hΔpos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ1'
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hd : Real.log A / 20 ≤ Real.log Δ := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hApos _) hΔ1
    rw [Real.log_rpow hApos] at h
    linarith
  have h5b : Real.log Δ ≤ Real.log 48 + 2 * Real.log B - Real.log A := by
    have h := Real.log_le_log hΔpos hΔ2
    rw [Real.log_div (by positivity) (ne_of_gt hApos),
        Real.log_mul (by norm_num) (ne_of_gt (pow_pos hBpos 2)), Real.log_pow] at h
    push_cast at h
    linarith
  have hm : (0:ℝ) ≤ Real.log M := Real.log_nonneg hM1
  have hm2 : Real.log M ≤ Real.log A := Real.log_le_log hMpos hM2
  have hlog4 : (Real.log (4 * Δ)) ^ 2 ≤ B ^ ((1:ℝ)/1000) := hlogsq A B Δ hBB₁ hA1 hΔ1' hΔ2
  by_cases hcaseA : Δ ≤ B
  · by_cases hbrP : 2 * Δ ≤ (2 * M) ^ 53
    · -- case A, branch P
      have hLb : hiLZ B (2 * Δ) (2 * M) ≤ 64 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 3 :=
        le_trans (hiLZ_le_A_P B Δ M hBpos hΔpos hcaseA hbrP)
          (hc_absorb_AP B Δ hBpos hΔpos hlog4)
      have hbr : Real.log Δ ≤ 53 * Real.log M + 52 * Real.log 2 := hc_branchP_log hΔpos hMpos hbrP
      obtain ⟨k, hk, h1, h2⟩ := hc_core_AP (Real.log A) (Real.log B) (Real.log Δ) (Real.log M)
        hlogB ha hll hd hm h5b hbr
      have hk4 : 4 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk67 : k ≤ 67 := (Finset.mem_Icc.mp hk).2
      refine hc_assemble A B Δ M (64 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 3) hApos hBpos hΔpos hMpos
        hLb k hk ?_ ?_
      · exact conv_AP_T1 A B Δ hApos hBpos hΔpos k hk4 hk67
          (hc_cmp_T1 _ (c1AP_unpack h1))
      · exact conv_AP_T2 A B Δ M hApos hBpos hΔpos hMpos k hk4 hk67
          (hc_cmp_T2P k _ hk4 (c2AP_unpack h2))
    · -- case A, branch Q
      have hbrQ : (2 * M) ^ 53 ≤ 2 * Δ := le_of_lt (not_le.mp hbrP)
      have hLb : hiLZ B (2 * Δ) (2 * M) ≤ 32 * 2 ^ 53 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 2 * M ^ 53 :=
        le_trans (hiLZ_le_A_Q B Δ M hBpos hΔpos hMpos.le hcaseA hbrQ)
          (hc_absorb_AQ B Δ M hBpos hΔpos hMpos.le hlog4)
      have hbr : 53 * Real.log M + 52 * Real.log 2 ≤ Real.log Δ := hc_branchQ_log hΔpos hMpos hbrQ
      obtain ⟨k, hk, h1, h2⟩ := hc_core_AQ (Real.log A) (Real.log B) (Real.log Δ) (Real.log M)
        hlogB ha hll hd hm h5b hbr
      have hk4 : 4 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk67 : k ≤ 67 := (Finset.mem_Icc.mp hk).2
      refine hc_assemble A B Δ M (32 * 2 ^ 53 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 2 * M ^ 53) hApos hBpos
        hΔpos hMpos hLb k hk ?_ ?_
      · exact conv_AQ_T1 A B Δ M hApos hBpos hΔpos hMpos k hk4 hk67
          (hc_cmp_T1Q _ (c1AQ_unpack h1))
      · exact conv_AQ_T2 A B Δ M hApos hBpos hΔpos hMpos k hk4 hk67
          (hc_cmp_T2Q k _ hk4 (c2AQ_unpack h2))
  · -- case B
    have hcaseB : B ≤ Δ := le_of_lt (not_le.mp hcaseA)
    by_cases hbrP : 2 * Δ ≤ (2 * M) ^ 53
    · -- case B, branch P
      have hLb : hiLZ B (2 * Δ) (2 * M)
          ≤ 64 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((9:ℝ)/2) :=
        le_trans (hiLZ_le_B_P B Δ M hBpos hΔpos hcaseB hbrP)
          (hc_absorb_BP B Δ hBpos hΔpos hlog4)
      have hbr : Real.log Δ ≤ 53 * Real.log M + 52 * Real.log 2 := hc_branchP_log hΔpos hMpos hbrP
      have hcBlog : Real.log B ≤ Real.log Δ := Real.log_le_log hBpos hcaseB
      obtain ⟨hc1, hc2⟩ := hc_core_BP (Real.log A) (Real.log B) (Real.log Δ) (Real.log M)
        hlogB ha hll hm hcBlog h5b hbr
      refine hc_assemble A B Δ M (64 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((9:ℝ)/2)) hApos hBpos
        hΔpos hMpos hLb 6 (by norm_num [Finset.mem_Icc]) ?_ ?_
      · have h := conv_BP_T1 A B Δ hApos hBpos hΔpos (hc_cmp_T1 _ (c1BP_unpack hc1))
        simpa only [show ((68:ℝ) - ((6:ℕ):ℝ)) = (62:ℝ) by norm_num,
          show ((2:ℝ) * ((6:ℕ):ℝ) - 8) = (4:ℝ) by norm_num,
          show (-((6:ℕ):ℝ)) = (-6:ℝ) by norm_num] using h
      · have h := conv_BP_T2 A B Δ M hApos hBpos hΔpos hMpos
            (hc_cmp_BP_T2 _ (c2BP_unpack hc2))
        simpa only [show ((67:ℝ) - ((6:ℕ):ℝ)) = (61:ℝ) by norm_num] using h
    · -- case B, branch Q
      have hbrQ : (2 * M) ^ 53 ≤ 2 * Δ := le_of_lt (not_le.mp hbrP)
      have hLb : hiLZ B (2 * Δ) (2 * M)
          ≤ 32 * 2 ^ 53 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((7:ℝ)/2) * M ^ 53 :=
        le_trans (hiLZ_le_B_Q B Δ M hBpos hΔpos hMpos.le hcaseB hbrQ)
          (hc_absorb_BQ B Δ M hBpos hΔpos hMpos.le hlog4)
      have hbr : 53 * Real.log M + 52 * Real.log 2 ≤ Real.log Δ := hc_branchQ_log hΔpos hMpos hbrQ
      have hcBlog : Real.log B ≤ Real.log Δ := Real.log_le_log hBpos hcaseB
      obtain ⟨hc1, hc2⟩ := hc_core_BQ (Real.log A) (Real.log B) (Real.log Δ) (Real.log M)
        hlogB ha hll hm hcBlog h5b hbr
      refine hc_assemble A B Δ M (32 * 2 ^ 53 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((7:ℝ)/2) * M ^ 53)
        hApos hBpos hΔpos hMpos hLb 6 (by norm_num [Finset.mem_Icc]) ?_ ?_
      · have h := conv_BQ_T1 A B Δ M hApos hBpos hΔpos hMpos
            (hc_cmp_T1Q _ (c1BQ_unpack hc1))
        simpa only [show ((68:ℝ) - ((6:ℕ):ℝ)) = (62:ℝ) by norm_num,
          show ((2:ℝ) * ((6:ℕ):ℝ) - 8) = (4:ℝ) by norm_num,
          show (-((6:ℕ):ℝ)) = (-6:ℝ) by norm_num] using h
      · have h := conv_BQ_T2 A B Δ M hApos hBpos hΔpos hMpos
            (hc_cmp_BQ_T2 _ (c2BQ_unpack hc2))
        simpa only [show ((67:ℝ) - ((6:ℕ):ℝ)) = (61:ℝ) by norm_num] using h

end Work.HP.MDEstimates.hiparts
