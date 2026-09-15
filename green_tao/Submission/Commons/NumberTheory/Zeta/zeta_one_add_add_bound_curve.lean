import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_strip_smallIm_bound
import Submission.Commons.NumberTheory.Zeta.riemannZeta_residue_uniform_bound

open Complex Filter Set
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- `ζ` is bounded on the compact rectangle `-1 ≤ Re s ≤ 3/4`, `|Im s| ≤ 1`. -/
private theorem zeta_compact_left_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 3 / 4 → |s.im| ≤ 1 →
      ‖riemannZeta s‖ ≤ M := by
  set K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ''
      (Set.Icc (-1 : ℝ) (3 / 4) ×ˢ Set.Icc (-1 : ℝ) 1) with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    have hφ : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) := by fun_prop
    exact (isCompact_Icc.prod isCompact_Icc).image hφ
  have hdiff : DifferentiableOn ℂ riemannZeta K := by
    intro s hs
    rw [hKdef] at hs
    rcases hs with ⟨p, hp, rfl⟩
    obtain ⟨hp1, hp2⟩ := hp
    simp only [Set.mem_Icc] at hp1 hp2
    have hne : (p.1 : ℂ) + Complex.I * (p.2 : ℂ) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [hp1.2]
    exact (differentiableAt_riemannZeta hne).differentiableWithinAt
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hdiff.continuousOn
  refine ⟨max M 0 + 1, by positivity, ?_⟩
  intro s h1 h2 h3
  have hsK : s ∈ K := by
    rw [hKdef]
    refine ⟨(s.re, s.im), ?_, ?_⟩
    · simp only [Set.mem_prod, Set.mem_Icc]
      refine ⟨⟨h1, h2⟩, ?_, ?_⟩
      · linarith [neg_abs_le s.im]
      · linarith [le_abs_self s.im]
    · have hval : (s.re : ℂ) + Complex.I * (s.im : ℂ) = s := by
        rw [mul_comm]; exact Complex.re_add_im s
      exact hval
  calc ‖riemannZeta s‖ ≤ M := hM s hsK
    _ ≤ max M 0 + 1 := by linarith [le_max_left M (0 : ℝ)]

theorem zeta_one_add_add_bound_curve {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) :
    ∃ C : ℝ, 0 < C ∧ ∀ z z' : ℂ,
      -1 ≤ z.re → z.re ≤ -(β / Real.log (|z.im| + 2)) →
      -1 ≤ z'.re → z'.re ≤ -(β / Real.log (|z'.im| + 2)) →
      ‖riemannZeta (1 + z + z')‖ ≤ C * (|z.im| + |z'.im| + 3) ^ 4 := by
  obtain ⟨C1, hC1pos, hC1⟩ := zeta_strip_polyGrowth
  obtain ⟨C2, hC2pos, hC2⟩ := zeta_strip_smallIm_bound
  obtain ⟨M, hMpos, hM⟩ := zeta_compact_left_bound
  refine ⟨C1 + M + (5 * C2 + 10 * C2 / β), by positivity, ?_⟩
  intro z z' hz1 hz2 hz1' hz2'
  set base : ℝ := |z.im| + |z'.im| + 3 with hbasedef
  have hbase_ge_one : (1 : ℝ) ≤ base := by
    rw [hbasedef]; have := abs_nonneg z.im; have := abs_nonneg z'.im; linarith
  have hbase_nonneg : (0 : ℝ) ≤ base := by linarith
  set A : ℝ := Real.log (|z.im| + 2) with hAdef
  set B : ℝ := Real.log (|z'.im| + 2) with hBdef
  have hApos : 0 < A := by
    rw [hAdef]; exact Real.log_pos (by linarith [abs_nonneg z.im])
  have hBpos : 0 < B := by
    rw [hBdef]; exact Real.log_pos (by linarith [abs_nonneg z'.im])
  have hzre_neg : z.re < 0 := by
    have hpos : 0 < β / A := div_pos hβ hApos
    linarith
  have hzre'_neg : z'.re < 0 := by
    have hpos : 0 < β / B := div_pos hβ hBpos
    linarith
  set s : ℂ := 1 + z + z' with hsdef
  have hre : s.re = 1 + z.re + z'.re := by simp [hsdef]
  have him : s.im = z.im + z'.im := by simp [hsdef]
  have hslo : -1 ≤ s.re := by rw [hre]; linarith
  have hslt1 : s.re < 1 := by rw [hre]; linarith
  have hbound_t : |s.im| ≤ |z.im| + |z'.im| := by rw [him]; exact abs_add_le _ _
  have hbound_t_base : |s.im| + 3 ≤ base := by rw [hbasedef]; linarith [hbound_t]
  by_cases ht : 1 ≤ |s.im|
  · -- far from the real axis: polynomial strip bound
    have hb := hC1 s.re s.im hslo (by linarith : s.re ≤ 3) ht
    have hsw : ((s.re : ℂ) + Complex.I * (s.im : ℂ)) = s := by
      rw [mul_comm]; exact Complex.re_add_im s
    rw [hsw] at hb
    calc ‖riemannZeta s‖ ≤ C1 * (|s.im| + 3) ^ 4 := hb
      _ ≤ C1 * base ^ 4 := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hC1pos)
          exact pow_le_pow_left₀ (by linarith [abs_nonneg s.im]) hbound_t_base 4
      _ ≤ (C1 + M + (5 * C2 + 10 * C2 / β)) * base ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hbase_nonneg 4)
          have hp : (0 : ℝ) < 5 * C2 + 10 * C2 / β := by positivity
          linarith
  · have ht1 : |s.im| ≤ 1 := le_of_lt (not_le.mp ht)
    have ht2 : |s.im| ≤ 2 := by linarith
    by_cases hsig : s.re ≤ 3 / 4
    · -- compact piece
      have hb := hM s hslo hsig ht1
      calc ‖riemannZeta s‖ ≤ M := hb
        _ ≤ M * base ^ 4 := by
            have h1 : (1 : ℝ) ≤ base ^ 4 := one_le_pow₀ hbase_ge_one
            nlinarith [le_of_lt hMpos, h1]
        _ ≤ (C1 + M + (5 * C2 + 10 * C2 / β)) * base ^ 4 := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg hbase_nonneg 4)
            have hp : (0 : ℝ) < C1 + (5 * C2 + 10 * C2 / β) := by positivity
            linarith
    · -- near the line Re s = 1: use the explicit pole-term bound
      have hsig' : 3 / 4 ≤ s.re := by linarith
      have hsw : ((s.re : ℂ) + Complex.I * (s.im : ℂ)) = s := by
        rw [mul_comm]; exact Complex.re_add_im s
      have hsne : (s.re : ℂ) + Complex.I * (s.im : ℂ) ≠ 1 := by
        rw [hsw]
        intro h
        have hh := congrArg Complex.re h
        rw [hre] at hh
        simp at hh
        linarith
      have hb := hC2 (1 / 4) s.re s.im (by norm_num) (by norm_num)
        (by linarith) (by linarith) ht2 hsne
      rw [hsw] at hb
      -- lower bound on ‖s - 1‖
      have hs_ne1 : s ≠ 1 := by
        intro h
        have hh := congrArg Complex.re h
        rw [hre] at hh
        simp at hh
        linarith
      have hsm1_re : (s - 1).re = z.re + z'.re := by
        rw [hsdef]; simp
        ring
      have hgap : β / A + β / B ≤ -(s - 1).re := by
        rw [hsm1_re]
        have h1 : β / A ≤ -z.re := by linarith
        have h2 : β / B ≤ -z'.re := by linarith
        linarith
      have hgap_pos : 0 < β / A + β / B := by positivity
      have hnorm_ge : β / A + β / B ≤ ‖s - 1‖ := by
        have h1 : |(s - 1).re| ≤ ‖s - 1‖ := abs_re_le_norm (s - 1)
        have h2 : |(s - 1).re| = -(s - 1).re := by
          rw [abs_of_neg (by linarith [hgap, hgap_pos])]
        linarith
      have hinv : ‖s - 1‖⁻¹ ≤ (A + B) / β := by
        have hDpos : 0 < β / A + β / B := hgap_pos
        have h1 : ‖s - 1‖⁻¹ ≤ (β / A + β / B)⁻¹ :=
          (inv_le_inv₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne1)) hDpos).mpr hnorm_ge
        have hDA : β / A ≤ β / A + β / B := by
          have : 0 < β / B := div_pos hβ hBpos
          linarith
        have h2 : (β / A + β / B)⁻¹ ≤ (β / A)⁻¹ :=
          (inv_le_inv₀ hDpos (div_pos hβ hApos)).mpr hDA
        have h3 : (β / A)⁻¹ = A / β := by rw [inv_div]
        have h4 : A / β ≤ (A + B) / β := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hβ)
          linarith
        linarith
      have hAB : A + B ≤ 2 * base := by
        have hA : A ≤ |z.im| + 2 := by
          rw [hAdef]
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < |z.im| + 2 by linarith [abs_nonneg z.im])
          linarith
        have hB : B ≤ |z'.im| + 2 := by
          rw [hBdef]
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < |z'.im| + 2 by linarith [abs_nonneg z'.im])
          linarith
        rw [hbasedef]; linarith [abs_nonneg z.im, abs_nonneg z'.im]
      have hinv2 : ‖s - 1‖⁻¹ ≤ 2 * base / β := by
        calc ‖s - 1‖⁻¹ ≤ (A + B) / β := hinv
          _ ≤ 2 * base / β := by
              apply div_le_div_of_nonneg_right hAB (le_of_lt hβ)
      have hb' : ‖riemannZeta s‖ ≤ 5 * C2 * (1 + 2 * base / β) := by
        have hCone : C2 * (1 + 1 / (1 / 4 : ℝ)) = 5 * C2 := by ring_nf
        rw [hCone] at hb
        have h7 : 1 / ‖s - 1‖ = ‖s - 1‖⁻¹ := one_div _
        have h8 : (1 : ℝ) + 1 / ‖s - 1‖ ≤ 1 + 2 * base / β := by
          rw [h7]; linarith [hinv2]
        calc ‖riemannZeta s‖ ≤ 5 * C2 * (1 + 1 / ‖s - 1‖) := hb
          _ ≤ 5 * C2 * (1 + 2 * base / β) := by
              apply mul_le_mul_of_nonneg_left h8 (by positivity)
      have hfinal : 5 * C2 * (1 + 2 * base / β) ≤
          (C1 + M + (5 * C2 + 10 * C2 / β)) * base ^ 4 := by
        have hP : (1 : ℝ) ≤ base ^ 4 := one_le_pow₀ hbase_ge_one
        have hP4 : base ≤ base ^ 4 := by
          have := pow_le_pow_right₀ hbase_ge_one (show (1:ℕ) ≤ 4 by norm_num)
          simpa using this
        have hexp : 5 * C2 * (1 + 2 * base / β) = 5 * C2 + (10 * C2 / β) * base := by
          field_simp [ne_of_gt hβ]; ring
        rw [hexp]
        have h1 : 5 * C2 ≤ 5 * C2 * base ^ 4 := by nlinarith [le_of_lt hC2pos, hP]
        have h2 : (10 * C2 / β) * base ≤ (10 * C2 / β) * base ^ 4 :=
          mul_le_mul_of_nonneg_left hP4 (by positivity)
        have h3 : 5 * C2 + (10 * C2 / β) * base ≤ (5 * C2 + 10 * C2 / β) * base ^ 4 := by
          have := add_le_add h1 h2
          calc 5 * C2 + (10 * C2 / β) * base
              ≤ 5 * C2 * base ^ 4 + (10 * C2 / β) * base ^ 4 := this
            _ = (5 * C2 + 10 * C2 / β) * base ^ 4 := by ring
        have h4 : 5 * C2 + 10 * C2 / β ≤ C1 + M + (5 * C2 + 10 * C2 / β) := by
          have : 0 < C1 + M := by positivity
          linarith
        calc 5 * C2 + (10 * C2 / β) * base
            ≤ (5 * C2 + 10 * C2 / β) * base ^ 4 := h3
          _ ≤ (C1 + M + (5 * C2 + 10 * C2 / β)) * base ^ 4 := by
              apply mul_le_mul_of_nonneg_right h4 (pow_nonneg hbase_nonneg 4)
      calc ‖riemannZeta s‖ ≤ 5 * C2 * (1 + 2 * base / β) := hb'
        _ ≤ (C1 + M + (5 * C2 + 10 * C2 / β)) * base ^ 4 := hfinal

end Commons.NumberTheory.Zeta
