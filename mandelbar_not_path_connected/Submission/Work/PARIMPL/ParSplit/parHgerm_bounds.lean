import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.phase_of_split
import Submission.Work.PARIMPL.ParSplit.parChart_algebra
import Submission.Work.PARIMPL.ParSplit.parRho_ne_zero
import Submission.Work.PARIMPL.ParSplit.parGerm_conj
import Submission.Work.PARIMPL.ParSplit.Hp_double_root_count
import Submission.Work.PARIMPL.ParSplit.g_mem_of_split
import Submission.Work.PARIMPL.ParSplit.deriv_star_comp_sq
import Submission.Work.PARIMPL.ParSplit.parChartSq
import Submission.Work.PARIMPL.ParSplit.BuildSplit
import Submission.Work.PARIMPL.ParSplit.parHgerm_tail_bounds
import Submission.Work.PARIMPL.ParSplit.parU0_sq_off_collision
import Submission.Work.PARIMPL.ParSplit.parU0_sq_of_E_eq_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.PARIMPL.ParSplit.parHgerm_bounds`

The uniform bounds of the germ `parHgerm` of the parameter normal form: the `bounds` field of
`Work.PARIMPL.ParNormal`, proved here from three local ingredients

* `parHgerm_tail_bounds` — the uniform `O(ζ²)` expansion of `parHgerm` in `ζ` (and a bound on
  the linear coefficient `parH1`);
* `parU0_sq_off_collision` — off the collision locus `{E = 0}` the germ at `0` satisfies
  `parU0^2 = σ · (W/‖W‖)^2` with `W = 2 (m - F m)/E`, so that the phase inequality of
  `phase_of_split` gives `Re (parU0^2) ≥ 574/1024`;
* `parU0_sq_of_E_eq_zero` — *on* the collision locus `parU0^2 = 1` exactly (there the phase
  inequality degenerates, since `W = 0`; the identity is proved from the parabolic structure).

The principal square root has nonnegative real part, so `parU0` is `1`-close on the whole ball,
and the remaining clauses of `ParBounds` follow from the tail bound and `‖parHgerm S c 0‖ = 1`.

(`pgb_assembly` below isolates that last step, so that this file only imports sorry-free
modules; the in-flight `parU0_phase`/`parChart_continuity` targets are *not* needed here.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit


variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- The principal square root has nonnegative real part. -/
theorem pgb_sqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  rw [Complex.sqrt_eq_real_add_ite, Complex.add_re]
  have h0 : (((if 0 ≤ z.im then (1 : ℂ) else -1)
      * ((Real.sqrt ((‖z‖ - z.re) / 2) : ℝ) : ℂ) * Complex.I)).re = 0 := by
    by_cases h : 0 ≤ z.im <;> simp [h, Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h0, add_zero]
  exact Real.sqrt_nonneg _

/-- Swap-side phase test. -/
theorem pgb_unit_sq_neg (W : ℂ) (hW : W ≠ 0) (h : 7 * ‖W‖ ≤ 8 * |W.im|) :
    ∃ t : ℂ, ‖t‖ = 1 ∧ t ^ 2 = -(W / ((‖W‖ : ℝ) : ℂ)) ^ 2 ∧ 7 / 8 ≤ t.re := by
  have hnorm : ‖W / (Complex.I * ((‖W‖ : ℝ) : ℂ))‖ = 1 := Work.PARIMPL.norm_div_I_norm W hW
  have hsq : (W / (Complex.I * ((‖W‖ : ℝ) : ℂ))) ^ 2 = -(W / ((‖W‖ : ℝ) : ℂ)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, Complex.I_sq]
    field_simp
  rcases Work.PARIMPL.exists_unit_close_of_im W hW h with h1 | h1
  · exact ⟨W / (Complex.I * ((‖W‖ : ℝ) : ℂ)), hnorm, hsq,
      Work.PARIMPL.seven_eighths_le_re hnorm h1⟩
  · refine ⟨-(W / (Complex.I * ((‖W‖ : ℝ) : ℂ))), ?_, ?_, ?_⟩
    · rw [norm_neg]; exact hnorm
    · rw [neg_pow, hsq]; norm_num
    · rw [Complex.neg_re]
      exact Work.PARIMPL.seven_eighths_le_re (by rw [norm_neg]; exact hnorm) h1

/-- Fix-side phase test. -/
theorem pgb_unit_sq_pos (W : ℂ) (hW : W ≠ 0) (h : 7 * ‖W‖ ≤ 8 * |W.re|) :
    ∃ t : ℂ, ‖t‖ = 1 ∧ t ^ 2 = (W / ((‖W‖ : ℝ) : ℂ)) ^ 2 ∧ 7 / 8 ≤ t.re := by
  have hnorm : ‖W / ((‖W‖ : ℝ) : ℂ)‖ = 1 := Work.PARIMPL.norm_div_norm W hW
  rcases Work.PARIMPL.exists_unit_close_of_re W hW h with h1 | h1
  · exact ⟨W / ((‖W‖ : ℝ) : ℂ), hnorm, rfl, Work.PARIMPL.seven_eighths_le_re hnorm h1⟩
  · refine ⟨-(W / ((‖W‖ : ℝ) : ℂ)), ?_, ?_, ?_⟩
    · rw [norm_neg]; exact hnorm
    · rw [neg_pow]; norm_num
    · rw [Complex.neg_re]
      exact Work.PARIMPL.seven_eighths_le_re (by rw [norm_neg]; exact hnorm) h1

/-- Finishing step: a unit `t` with `Re t ≥ 7/8` and `u ^ 2 = t ^ 2`, where `u` has nonnegative
real part, satisfies `‖u‖ = 1` and `‖u - 1‖ ≤ 1/2`. -/
theorem pgb_finish {u t : ℂ} (hre : 0 ≤ u.re) (ht1 : ‖t‖ = 1) (ht3 : 7 / 8 ≤ t.re)
    (hsq : u ^ 2 = t ^ 2) : ‖u‖ = 1 ∧ ‖u - 1‖ ≤ 1 / 2 := by
  have hnorm : ‖u‖ = 1 := by
    have h2 : ‖u‖ ^ 2 = 1 := by rw [← norm_pow, hsq, norm_pow, ht1]; norm_num
    nlinarith [norm_nonneg u]
  refine ⟨hnorm, ?_⟩
  have hfac : (u - t) * (u + t) = 0 := by
    have h : (u - t) * (u + t) = u ^ 2 - t ^ 2 := by ring
    rw [h, hsq, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · have hut : u = t := by linear_combination h
    rw [hut]; exact Work.PARIMPL.norm_sub_one_le_of_re ht1 ht3
  · have hut : u = -t := by linear_combination h
    exfalso
    rw [hut, Complex.neg_re] at hre
    linarith

/-- **Assembly** of `parHgerm_bounds` from the three ingredients. -/
theorem pgb_assembly (S : SplitData d)
    (hTail : ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∃ r > 0, ∃ A : ℝ, 0 ≤ A ∧ ∃ B : ℝ, 0 ≤ B ∧
      (∀ c ∈ Metric.ball c₀ ρ', ‖parH1 S c‖ ≤ B) ∧
      (∀ c ∈ Metric.ball c₀ ρ', ∀ ζ : ℂ, ‖ζ‖ < r →
        ‖parHgerm S c ζ - parHgerm S c 0 - parH1 S c * ζ‖ ≤ A * ‖ζ‖ ^ 2))
    (hOff : ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ', S.E c ≠ 0 →
      parU0 S c ^ 2 =
        (parSigma S c : ℂ) * ((2 * (S.m c - Work.EL.F c (S.m c)) / S.E c) ^ 2 /
          ((‖2 * (S.m c - Work.EL.F c (S.m c)) / S.E c‖ : ℝ) : ℂ) ^ 2))
    (hCol : ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ', S.E c = 0 → parU0 S c ^ 2 = 1) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∃ r > 0, ∃ A : ℝ, 0 ≤ A ∧
      ∀ c ∈ Metric.ball c₀ ρ', Work.PARIMPL.ParBounds (fun ζ => parHgerm S c ζ)
        (parHgerm S c 0) (parH1 S c) A r := by
  obtain ⟨ρT, hρT0, hρTρ, rT, hrT0, A, hA0, B, hB0, hH1, htail⟩ := hTail
  obtain ⟨ρO, hρO0, hρOρ, hOffc⟩ := hOff
  obtain ⟨ρC, hρC0, hρCρ, hColc⟩ := hCol
  obtain ⟨ρρ, hρρ0, hρρρ, hrhoc⟩ := parRho_ne_zero S
  obtain ⟨ρP, hρP0, hρPρ, hphase⟩ := phase_of_split S
  obtain ⟨ρG, hρG0, hρGρ, hmemg⟩ := g_mem_of_split S
  obtain ⟨ρR, hρR0, hρRρ, hsmall⟩ :=
    exists_small_ball_of_continuous S.hρ S.hR S.cont_m (S.cont_E.div_const 2) S.m₀
      (by rw [S.E₀]; norm_num)
  -- shrink the tail radius so that `A * r ^ 2 + B * r ≤ 1 / 2`
  set r : ℝ := min rT (1 / (2 * (A + B + 1))) with hrdef
  have hrpos : 0 < r := lt_min hrT0 (by positivity)
  have hrT : r ≤ rT := min_le_left _ _
  have hr1 : A * r ^ 2 + B * r ≤ 1 / 2 := by
    have hAB : 0 ≤ A + B := by linarith
    have hrle : r ≤ 1 / (2 * (A + B + 1)) := min_le_right _ _
    have hconv : (A + B) * r ≤ 1 / 2 := by
      have h1 : (A + B) * r ≤ (A + B) * (1 / (2 * (A + B + 1))) :=
        mul_le_mul_of_nonneg_left hrle hAB
      have h2 : (A + B) * (1 / (2 * (A + B + 1))) ≤ 1 / 2 := by
        rw [mul_one_div]
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      linarith
    have hr1' : r ≤ 1 := by
      have h3 : 1 / (2 * (A + B + 1)) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      linarith
    have hsq : A * r ^ 2 ≤ A * r := by
      have h4 : r ^ 2 ≤ r := by nlinarith [hrpos, hr1']
      exact mul_le_mul_of_nonneg_left h4 hA0
    linarith [hsq, hconv, mul_nonneg hB0 (le_of_lt hrpos)]
  -- the parameter radius
  set ρ' : ℝ := min (min (min ρT ρO) (min ρC ρρ)) (min (min ρP ρG) ρR) with hρ'def
  have hρ'0 : 0 < ρ' := by
    rw [hρ'def]
    exact lt_min (lt_min (lt_min hρT0 hρO0) (lt_min hρC0 hρρ0))
      (lt_min (lt_min hρP0 hρG0) hρR0)
  have hL1 : ρ' ≤ min (min ρT ρO) (min ρC ρρ) := by rw [hρ'def]; exact min_le_left _ _
  have hL2 : ρ' ≤ min (min ρP ρG) ρR := by rw [hρ'def]; exact min_le_right _ _
  have hA1 : min (min ρT ρO) (min ρC ρρ) ≤ min ρT ρO := min_le_left _ _
  have hA2 : min (min ρT ρO) (min ρC ρρ) ≤ min ρC ρρ := min_le_right _ _
  have hB1 : min (min ρP ρG) ρR ≤ min ρP ρG := min_le_left _ _
  have hleT : ρ' ≤ ρT := le_trans (le_trans hL1 hA1) (min_le_left _ _)
  have hleO : ρ' ≤ ρO := le_trans (le_trans hL1 hA1) (min_le_right _ _)
  have hleC : ρ' ≤ ρC := le_trans (le_trans hL1 hA2) (min_le_left _ _)
  have hleρ : ρ' ≤ ρρ := le_trans (le_trans hL1 hA2) (min_le_right _ _)
  have hleP : ρ' ≤ ρP := le_trans (le_trans hL2 hB1) (min_le_left _ _)
  have hleG : ρ' ≤ ρG := le_trans (le_trans hL2 hB1) (min_le_right _ _)
  have hleR : ρ' ≤ ρR := le_trans hL2 (min_le_right _ _)
  have hρ'ρ : ρ' ≤ S.ρ := le_trans hleT hρTρ
  refine ⟨ρ', hρ'0, hρ'ρ, r, hrpos, A, hA0, ?_⟩
  intro c hc
  have hcT : c ∈ Metric.ball c₀ ρT := Metric.ball_subset_ball hleT hc
  have hcO : c ∈ Metric.ball c₀ ρO := Metric.ball_subset_ball hleO hc
  have hcC : c ∈ Metric.ball c₀ ρC := Metric.ball_subset_ball hleC hc
  have hcρ : c ∈ Metric.ball c₀ S.ρ := Metric.ball_subset_ball hρ'ρ hc
  have hcLL : c ∈ Metric.ball c₀ ρρ := Metric.ball_subset_ball hleρ hc
  have hcP : c ∈ Metric.ball c₀ ρP := Metric.ball_subset_ball hleP hc
  have hcG : c ∈ Metric.ball c₀ ρG := Metric.ball_subset_ball hleG hc
  have hcR : c ∈ Metric.ball c₀ ρR := Metric.ball_subset_ball hleR hc
  have hτeq : parHgerm S c 0 = parU0 S c := parHgerm_zero S c (hrhoc c hcLL)
  have hre : 0 ≤ (parU0 S c).re := pgb_sqrt_re_nonneg _
  have hmain : ‖parU0 S c‖ = 1 ∧ ‖parU0 S c - 1‖ ≤ 1 / 2 := by
    by_cases hE : S.E c = 0
    · have hsq : parU0 S c ^ 2 = 1 := hColc c hcC hE
      have hnorm : ‖parU0 S c‖ = 1 := by
        have h2 : ‖parU0 S c‖ ^ 2 = 1 := by rw [← norm_pow, hsq]; norm_num
        nlinarith [norm_nonneg (parU0 S c)]
      refine ⟨hnorm, ?_⟩
      have hfac : (parU0 S c - 1) * (parU0 S c + 1) = 0 := by
        have h : (parU0 S c - 1) * (parU0 S c + 1) = parU0 S c ^ 2 - 1 := by ring
        rw [h, hsq, sub_self]
      rcases mul_eq_zero.mp hfac with h | h
      · have hut : parU0 S c = 1 := by linear_combination h
        rw [hut]; norm_num
      · have hut : parU0 S c = -1 := by linear_combination h
        exfalso
        rw [hut, Complex.neg_re] at hre
        norm_num at hre
    · have hWne : 2 * (S.m c - Work.EL.F c (S.m c)) / S.E c ≠ 0 := by
        intro h0
        rcases (div_eq_zero_iff).mp h0 with h1 | h1
        · have h2 : S.m c - Work.EL.F c (S.m c) = 0 :=
            (mul_eq_zero.mp h1).resolve_left (by norm_num)
          have hfix : Work.EL.F c (S.m c) = S.m c := by linear_combination -h2
          have hsm : dist (S.m c) d.z₁ + ‖S.E c‖ / 2 < S.R := by
            have h := hsmall c hcR
            rw [norm_div, Complex.norm_ofNat] at h
            linarith
          exact hE (SplitData.E_eq_zero_of_fixed_mid S hcρ hsm hfix)
        · exact hE h1
      have hsqW := hOffc c hcO hE
      refine parSigma_eq_neg_one_or_one S c |>.elim ?_ ?_
      · intro hσ
        have hswap : gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2 := by
          by_contra hcon
          rw [parSigma, if_neg hcon] at hσ
          norm_num at hσ
        have hineq : 7 * ‖2 * (S.m c - Work.EL.F c (S.m c)) / S.E c‖ ≤
            8 * |(2 * (S.m c - Work.EL.F c (S.m c)) / S.E c).im| :=
          (hphase c hcP hE).1 hswap
        obtain ⟨t, ht1, ht2, ht3⟩ := pgb_unit_sq_neg _ hWne hineq
        have hsq : parU0 S c ^ 2 = t ^ 2 := by
          have h1 : (parSigma S c : ℂ) = -1 := by rw [hσ]; norm_num
          rw [hsqW, h1, neg_one_mul, ← div_pow]
          exact ht2.symm
        exact pgb_finish hre ht1 ht3 hsq
      · intro hσ
        have hnswap : ¬ (gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2) := by
          intro hcon
          rw [parSigma, if_pos hcon] at hσ
          norm_num at hσ
        have hfix : gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2 := by
          rcases S.swap_or_fix_of_split hcρ (hmemg c hcG) with h | h
          · exact h
          · exact absurd h hnswap
        have hineq : 7 * ‖2 * (S.m c - Work.EL.F c (S.m c)) / S.E c‖ ≤
            8 * |(2 * (S.m c - Work.EL.F c (S.m c)) / S.E c).re| :=
          (hphase c hcP hE).2 hfix
        obtain ⟨t, ht1, ht2, ht3⟩ := pgb_unit_sq_pos _ hWne hineq
        have hsq : parU0 S c ^ 2 = t ^ 2 := by
          have h1 : (parSigma S c : ℂ) = 1 := by rw [hσ]; norm_num
          rw [hsqW, h1, one_mul, ← div_pow]
          exact ht2.symm
        exact pgb_finish hre ht1 ht3 hsq
  obtain ⟨hnormU, hcloseU⟩ := hmain
  have hζbound : ∀ ζ : ℂ, ‖ζ‖ < r → ‖parHgerm S c ζ - parHgerm S c 0‖ ≤ 1 / 2 := by
    intro ζ hζ
    have hζT : ‖ζ‖ < rT := lt_of_lt_of_le hζ hrT
    have h1 : ‖parHgerm S c ζ - parHgerm S c 0 - parH1 S c * ζ‖ ≤ A * ‖ζ‖ ^ 2 :=
      htail c hcT ζ hζT
    have h2 : ‖parH1 S c * ζ‖ ≤ B * ‖ζ‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hH1 c hcT) (norm_nonneg ζ)
    have h4 : ‖parHgerm S c ζ - parHgerm S c 0‖ ≤ A * ‖ζ‖ ^ 2 + B * ‖ζ‖ := by
      calc ‖parHgerm S c ζ - parHgerm S c 0‖
          = ‖(parHgerm S c ζ - parHgerm S c 0 - parH1 S c * ζ) + parH1 S c * ζ‖ := by
              congr 1
              ring
        _ ≤ ‖parHgerm S c ζ - parHgerm S c 0 - parH1 S c * ζ‖ + ‖parH1 S c * ζ‖ :=
            norm_add_le _ _
        _ ≤ A * ‖ζ‖ ^ 2 + B * ‖ζ‖ := add_le_add h1 h2
    have h5 : A * ‖ζ‖ ^ 2 + B * ‖ζ‖ ≤ A * r ^ 2 + B * r := by
      have h6 : ‖ζ‖ ≤ r := le_of_lt hζ
      have h7 : ‖ζ‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg ζ) h6 2
      nlinarith [hA0, hB0]
    linarith
  refine ⟨hrpos, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hτeq]; exact hnormU
  · intro ζ hζ
    exact htail c hcT ζ (lt_of_lt_of_le hζ hrT)
  · intro ζ hζ
    have h0 : ‖parHgerm S c 0‖ = 1 := by rw [hτeq]; exact hnormU
    have hle : ‖parHgerm S c ζ‖ ≤ ‖parHgerm S c 0‖ + ‖parHgerm S c ζ - parHgerm S c 0‖ := by
      have heq : parHgerm S c ζ = parHgerm S c 0 + (parHgerm S c ζ - parHgerm S c 0) := by ring
      calc ‖parHgerm S c ζ‖ = ‖parHgerm S c 0 + (parHgerm S c ζ - parHgerm S c 0)‖ :=
            congrArg norm heq
        _ ≤ ‖parHgerm S c 0‖ + ‖parHgerm S c ζ - parHgerm S c 0‖ := norm_add_le _ _
    linarith [hζbound ζ hζ]
  · intro ζ hζ
    have h0 : ‖parHgerm S c 0‖ = 1 := by rw [hτeq]; exact hnormU
    have hsym : ‖parHgerm S c 0 - parHgerm S c ζ‖ ≤ 1 / 2 := by
      rw [norm_sub_rev]; exact hζbound ζ hζ
    have hle : ‖parHgerm S c 0‖
        ≤ ‖parHgerm S c ζ‖ + ‖parHgerm S c 0 - parHgerm S c ζ‖ := by
      have heq : parHgerm S c 0 = parHgerm S c ζ + (parHgerm S c 0 - parHgerm S c ζ) := by ring
      calc ‖parHgerm S c 0‖ = ‖parHgerm S c ζ + (parHgerm S c 0 - parHgerm S c ζ)‖ :=
            congrArg norm heq
        _ ≤ ‖parHgerm S c ζ‖ + ‖parHgerm S c 0 - parHgerm S c ζ‖ := norm_add_le _ _
    linarith
  · rw [hτeq]; exact hcloseU
/-- The uniform bounds of the germ `parHgerm` of the parameter normal form (`ParBounds`). -/
theorem parHgerm_bounds {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : Work.PARIMPL.ParSplit.SplitData d) : ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∃ r > 0, ∃ A : ℝ, 0 ≤ A ∧ ∀ c ∈ Metric.ball c₀ ρ', Work.PARIMPL.ParBounds (fun ζ => Work.PARIMPL.ParSplit.parHgerm S c ζ) (Work.PARIMPL.ParSplit.parHgerm S c 0) (Work.PARIMPL.ParSplit.parH1 S c) A r := by
  exact pgb_assembly S (parHgerm_tail_bounds S) (parU0_sq_off_collision S) (parU0_sq_of_E_eq_zero S)

end Work.PARIMPL.ParSplit
