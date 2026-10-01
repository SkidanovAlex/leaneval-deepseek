import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.HB10_3Engine
import Submission.Work.ZeroFreeTables.OffAxis.L52SupplyGen
import Submission.Work.ZeroFreeTables.OffAxis.tf72Fc_ten_eight
import Submission.Work.ZeroFreeTables.OffAxis.tf72f_moment_step
import Submission.Work.ZeroFreeTables.tf72f_laplace_counterexample_bounds
import Submission.Work.ZeroFreeTables.tf72f_gap_mono
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.LinnikAreas.boxMaxZero

open DirichletCharacter Complex
open scoped Classical BigOperators Interval
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

/-! ## Numerical input: the margin in the failure of (10.7)

`RectHB10_3_refute_quant` is the quantitative form of `tf72f_refute_TestFn_uncond`: the sharp
values
`tf72f_laplace_counterexample_bounds` at the endpoint `λ₁ = 792/1000` together with the
maximality of the gap `λ ↦ F(−λ) − 2F(6/7−λ)` there (`tf72f_gap_mono`) give the strictly positive
margin `83/9000 = 8/5 − 2·(8/9) + 187/1000`, where `761/500 − 2·(1709/2000) = −187/1000`. -/

/-- **The `F`-method combination (10.7) fails with an explicit margin.**  For every test function
`T` with `x₀ = 7/3`, `f = tf72f (6/7)`, `F 0 = 8/9`, `F(-6/7) = 8/5` and every
`0 ≤ λ₁ ≤ 792/1000`,

`T.F(-6/7) - T.F(-λ₁) ≥ 2 (T.F 0 - T.F(6/7-λ₁)) + 83/9000`. -/
theorem RectHB10_3_refute_quant (T : Work.ZeroFreeTables.TestFn) (hT : T.x₀ = 7/3)
    (hf : T.f = Work.ZeroFreeTables.tf72f (6/7)) (hF0 : T.F 0 = 8/9)
    (hF6 : T.F (-(6/7)) = 8/5) :
    ∀ l₁ : ℝ, 0 ≤ l₁ → l₁ ≤ 792/1000 →
      T.F (-(6/7)) - T.F (-l₁) ≥ 2 * (T.F 0 - T.F (6/7 - l₁)) + 83/9000 := by
  intro l₁ h0 h1
  obtain ⟨hb1, hb2⟩ := Work.ZeroFreeTables.tf72f_laplace_counterexample_bounds
  have hb1' : (∫ t in (0:ℝ)..(7/3),
      Real.exp ((792/1000:ℝ) * t) * Work.ZeroFreeTables.tf72f (6/7) t) ≤ 761/500 := by
    have h := hb1
    rwa [show (2:ℝ)/(6/7) = 7/3 by norm_num] at h
  have hb2' : (1709/2000 : ℝ) ≤ ∫ t in (0:ℝ)..(7/3),
      Real.exp (-(57/875:ℝ) * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
    have h := hb2
    rwa [show (2:ℝ)/(6/7) = 7/3 by norm_num] at h
  have eB : T.F (-l₁) = ∫ t in (0:ℝ)..(7/3),
      Real.exp (l₁ * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
    rw [Work.ZeroFreeTables.F_eq_tf72f_int T hT hf]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [show -((-l₁) * t) = l₁ * t from by ring]
  have eC : T.F (6/7 - l₁) = ∫ t in (0:ℝ)..(7/3),
      Real.exp (-((6/7 - l₁) * t)) * Work.ZeroFreeTables.tf72f (6/7) t :=
    Work.ZeroFreeTables.F_eq_tf72f_int T hT hf (6/7 - l₁)
  have hgap := Work.ZeroFreeTables.tf72f_gap_mono l₁ h0 h1
  have hker : T.F (-l₁) - 2 * T.F (6/7 - l₁) ≤ (761/500 : ℝ) - 2 * (1709/2000 : ℝ) := by
    rw [eB, eC]
    linarith
  have hsub : (761/500 : ℝ) - 2 * (1709/2000 : ℝ) = -(187/1000) := by norm_num
  rw [hsub] at hker
  rw [hF6, hF0]
  linarith

/-! ## The §10 endgame at `λ = 6/7`

From Heath-Brown's (10.6) for the test function of Lemma 7.2 at `λ = 6/7`, the ordering
`0 ≤ λ₁ ≤ λ₃ ≤ 6/7` and the identity `f(0)(7/6) = 3F(0) − F(−6/7)` (Lemma 7.5), one gets (10.7)
with the `ε'`-slack `s = 8ε' f(0)`.  The moment step `hmom` then splits: either `λ₁ ≤ 792/1000`,
and the refutation `href` contradicts (10.7), or `λ₁ ≥ 6/7 − ε/2`, which already gives
`λ₃ ≥ 6/7 − ε/2 > 6/7 − ε`. -/

/-- **HB §10 endgame.**  From (10.6) at `λ = 6/7` one reads off (10.7) with slack `s`, and the
moment step plus the refutation force `λ₃ ≥ 6/7 - ε`. -/
theorem RectHB10_3_endgame (T : Work.ZeroFreeTables.TestFn) (ε' ε s l₁ l₂ l₃ : ℝ)
    (hε : 0 < ε) (hT : T.x₀ = 7/3) (hf : T.f = Work.ZeroFreeTables.tf72f (6/7))
    (hF0 : T.F 0 = 8/9) (hF6 : T.F (-(6/7)) = 8/5)
    (hL75 : T.f 0 * (7/6) = 3 * T.F 0 - T.F (-(6/7)))
    (hs0 : 0 ≤ s) (hse : s ≤ ε/10000) (hs83 : s < 83/9000)
    (hs8 : 8 * ε' * T.f 0 ≤ s)
    (hmom : ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      T.F (-(6/7)) - T.F (-l) ≤ 2 * (T.F 0 - T.F (6/7 - l)) + s →
        l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l)
    (href : ∀ l : ℝ, 0 ≤ l → l ≤ 792/1000 →
      T.F (-(6/7)) - T.F (-l) ≥ 2 * (T.F 0 - T.F (6/7 - l)) + 83/9000)
    (h106 : T.F (-l₁) - T.F 0 - T.F (l₂ - l₁) - T.F (l₃ - l₁) + T.f 0 * (7/6 + 8 * ε') ≥ 0)
    (h01 : 0 ≤ l₁) (h13 : l₁ ≤ l₃) (h23 : l₂ ≤ l₃) (h36 : l₃ ≤ 6/7) :
    6/7 - ε ≤ l₃ := by
  by_contra hcon
  rw [not_le] at hcon
  have hanti := Work.ZeroFreeTables.TestFn_F_antitone T
  have h2 : T.F (6/7 - l₁) ≤ T.F (l₂ - l₁) := hanti (by linarith)
  have h3 : T.F (6/7 - l₁) ≤ T.F (l₃ - l₁) := hanti (by linarith)
  have h107 : T.F (-(6/7)) - T.F (-l₁) ≤ 2 * (T.F 0 - T.F (6/7 - l₁)) + s := by
    have hk : T.f 0 * (7/6 + 8 * ε') = (3 * T.F 0 - T.F (-(6/7))) + 8 * ε' * T.f 0 := by
      rw [← hL75]; ring
    rw [hk] at h106
    linarith [h2, h3, h106, hs8]
  by_cases hcase : l₁ < 6/7
  · rcases hmom l₁ h01 hcase h107 with hle | hbig
    · have hh := href l₁ h01 hle
      linarith
    · linarith
  · push Not at hcase
    linarith

/-! ## The target -/

/-- **HB Lemma 10.3 at rectangle height `L`, in the off-axis case.**  For every `ε > 0` and every
rectangle height `L ≥ 1` there is `q₀` such that for `q ≥ q₀`: if `ρ₁` is a non-principal zero with
`|Im ρ₁| ≤ L` of `χ₁`, realising the minimum of `λ = (1-Re)·log q` over *all* non-principal zeros of
height `≤ 10L` (`IsRectMin L χ₁ ρ₁`), if `1 < |Im ρ₁|` (so `ρ₁` is not real — HB's case 3, the `P₃`
case, cannot occur), and if `(χ₂,ρ₂)`, `(χ₃,ρ₃)` are two further conjugate pairs (all six
inequalities of distinctness), both zero pairs lying in the working region `|Im| ≤ 1`
(`IsZ`), `ρ₂` realising the minimum of `λ` among the zeros of all characters outside
`{χ₁,χ₁⁻¹}` and `ρ₃` realising the minimum among those outside `{χ₁,χ₁⁻¹,χ₂,χ₂⁻¹}`, then
`λ₃ = λ(ρ₃) ≥ 6/7 - ε`.  (`λ₁ ≤ λ₂` is free from `IsRectMin` since `|Im ρ₂| ≤ 1 ≤ 10L`.)
This is Heath-Brown (1992), §10 (Lemma 10.1 and Lemma 10.2), run at rectangle height `L`; the two
non-real-`ρ₁` configurations are the `F`-method ones, so the `P₃` case-3 engine is not needed. -/
theorem RectHB10_3 : ∀ ε : ℝ, 0 < ε → ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      Work.LinnikContract.IsZ χ₂ ρ₂ → Work.LinnikContract.IsZ χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.LinnikContract.IsZ χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) →
      (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.LinnikContract.IsZ χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
        χ ≠ χ₂ → χ ≠ χ₂⁻¹ → Work.LinnikContract.lamOf q ρ₃ ≤ Work.LinnikContract.lamOf q u) →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
      Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 - ε →
      6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃ := by
  intro ε hε L hL
  -- HB Lemma 7.2's test function at the limiting slope `λ = 6/7`
  set T : Work.ZeroFreeTables.TestFn := Work.ZeroFreeTables.tf72T (6/7) (by norm_num) with hTdef
  have h67 : (0:ℝ) < 6/7 := by norm_num
  have hT0 : T.x₀ = 7/3 := by
    rw [hTdef]; show (2:ℝ)/(6/7) = 7/3; norm_num
  have hTf : T.f = Work.ZeroFreeTables.tf72f (6/7) := by rw [hTdef]; rfl
  have hTFc : T.Fc = Work.ZeroFreeTables.tf72Fc (6/7) := by rw [hTdef]; rfl
  have hTf0 : T.f 0 = 32/35 := by
    rw [hTf]
    show Work.ZeroFreeTables.tf72f (6/7) 0 = 32/35
    rw [Work.ZeroFreeTables.tf72f_at_zero (6/7) h67]; norm_num
  have hTF0 : T.F 0 = 8/9 := by
    show (Work.ZeroFreeTables.tf72Fc (6/7) ((0:ℝ):ℂ)).re = 8/9
    rw [show ((0:ℝ):ℂ) = 0 from by norm_num]
    exact Work.ZeroFreeTables.tf72Fc_zero_re (6/7) h67
  have hTF6 : T.F (-(6/7)) = 8/5 := by
    show (Work.ZeroFreeTables.tf72Fc (6/7) (((-(6/7) : ℝ)):ℂ)).re = 8/5
    exact Work.ZeroFreeTables.tf72Fc_neglam_re (6/7) h67
  have hL75 : T.f 0 * (7/6) = 3 * T.F 0 - T.F (-(6/7)) := by
    rw [hTf0, hTF0, hTF6]; norm_num
  -- the slack `ε'` and `s = 8 ε' f(0)`
  set ε' : ℝ := min (ε/100000) (1/2000) with hε'def
  have hε' : 0 < ε' := by
    rw [hε'def]; exact lt_min (by linarith) (by norm_num)
  have hε'le : ε' ≤ ε/100000 := by rw [hε'def]; exact min_le_left _ _
  have hε'le2 : ε' ≤ 1/2000 := by rw [hε'def]; exact min_le_right _ _
  have hs0 : (0:ℝ) ≤ 8 * ε' * T.f 0 := by rw [hTf0]; nlinarith [hε']
  have hse : 8 * ε' * T.f 0 ≤ ε/10000 := by
    rw [hTf0]
    nlinarith [hε'le]
  have hs83 : 8 * ε' * T.f 0 < 83/9000 := by
    rw [hTf0]
    nlinarith [hε'le2]
  -- the numerical hypotheses (10.8)/(10.9) of the engine
  have hnum : ∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → |μ| ≤ 4 →
      (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
        - 2 * (T.Fc ((μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6 := by
    intro a μ ha0 ha6 hμ
    have h := tf72Fc_ten_eight.1 a μ ha0 ha6 hμ
    rw [hTFc, hTf0]
    linarith
  have hnum2 : ∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → 4 ≤ |μ| →
      (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6 := by
    intro a μ ha0 ha6 hμ
    have h := tf72Fc_ten_eight.2 a μ ha0 ha6 hμ
    rw [hTFc, hTf0]
    linarith
  -- the moment step, in the `F`-vocabulary
  have hmom : ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      T.F (-(6/7)) - T.F (-l) ≤ 2 * (T.F 0 - T.F (6/7 - l)) + 8 * ε' * T.f 0 →
        l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l := by
    intro l hl0 hl67 hl
    have hA : T.F (-(6/7)) = ∫ t in (0:ℝ)..(7/3),
        Real.exp ((6/7:ℝ) * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [Work.ZeroFreeTables.F_eq_tf72f_int T hT0 hTf]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      rw [show -((-(6/7:ℝ)) * t) = (6/7:ℝ) * t from by ring]
    have hB : T.F (-l) = ∫ t in (0:ℝ)..(7/3),
        Real.exp (l * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [Work.ZeroFreeTables.F_eq_tf72f_int T hT0 hTf]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      rw [show -((-l) * t) = l * t from by ring]
    have hZ : T.F 0 = ∫ t in (0:ℝ)..(7/3), Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [Work.ZeroFreeTables.F_eq_tf72f_int T hT0 hTf]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      rw [show -((0:ℝ) * t) = 0 from by ring, Real.exp_zero, one_mul]
    have hD : T.F (6/7 - l) = ∫ t in (0:ℝ)..(7/3),
        Real.exp (-((6/7 - l) * t)) * Work.ZeroFreeTables.tf72f (6/7) t :=
      Work.ZeroFreeTables.F_eq_tf72f_int T hT0 hTf (6/7 - l)
    rw [hA, hB, hZ, hD] at hl
    exact Work.ZeroFreeTables.OffAxis.tf72f_moment_step ε (8 * ε' * T.f 0) hε hs0 hse l
      hl0 hl67 hl
  -- the `q`-thresholds
  obtain ⟨δ, hδ0, hδ1, qS, hS⟩ := L52SupplyGen ε' hε'
  obtain ⟨qE, hE⟩ := HB10_3Engine T ε' δ hε' hδ0 hδ1
  refine ⟨max qE (max qS (Nat.ceil (Real.exp L) + 1)), ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR h1m hZ2 hZ3 h21 h2i h31 h3i h32 h3ii
    _h2min _h3min hlam23 hlam3
  have hqE : qE ≤ q := le_trans (le_max_left _ _) hq
  have hqS : qS ≤ q := le_trans (le_max_of_le_right (le_max_left _ _)) hq
  have hqL : Nat.ceil (Real.exp L) + 1 ≤ q :=
    le_trans (le_max_of_le_right (le_max_right _ _)) hq
  have hLlog : L ≤ Real.log (q : ℝ) := by
    have h1 : Real.exp L ≤ (q : ℝ) := by
      have h2 : (Nat.ceil (Real.exp L) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ _) hqL)
      exact le_trans (Nat.le_ceil _) h2
    have h := Real.log_le_log (Real.exp_pos L) h1
    rwa [Real.log_exp] at h
  have h106 := hE q hqE L χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ (hS q hqS) hL hLlog hR h1m hZ2 hZ3
    h21 h2i h31 h3i h32 h3ii hlam23 (by linarith) hnum hnum2
  -- the ordering `0 ≤ λ₁ ≤ λ₃ ≤ 6/7`
  have h01 : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := by
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
    have hre : ρ₁.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hR.1.2.1
    rw [Work.LinnikContract.lamOf]
    exact mul_nonneg (by linarith) hlog
  have h13 : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₃ :=
    hR.2 χ₃ ρ₃ (Work.ZeroFreeTables.isZAt_mono (by linarith) hZ3)
  have h36 : Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 := by linarith
  exact RectHB10_3_endgame T ε' ε (8 * ε' * T.f 0) (Work.LinnikContract.lamOf q ρ₁)
    (Work.LinnikContract.lamOf q ρ₂) (Work.LinnikContract.lamOf q ρ₃)
    hε hT0 hTf hTF0 hTF6 hL75 hs0 hse hs83 (le_of_eq rfl) hmom
    (RectHB10_3_refute_quant T hT0 hTf hTF0 hTF6) h106 h01 h13 hlam23 h36

end Work.ZeroFreeTables.OffAxis
