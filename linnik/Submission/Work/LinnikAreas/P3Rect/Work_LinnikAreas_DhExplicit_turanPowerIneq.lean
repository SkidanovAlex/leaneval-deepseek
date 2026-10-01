import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_Inputs
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_Defs
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_XiAux
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_Reduction
import Submission.Work.LinnikAreas.DhK.turanWeighted
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_turanPowerStepConst

namespace Work.LinnikAreas.DhExplicit

open scoped Classical BigOperators
open Work.LinnikContract

set_option maxHeartbeats 0

/-!
# `Work.LinnikAreas.DhExplicit.turanPowerIneq`

The Turán power inequality of the Deuring–Heilbronn argument (Kadiri–Ng–Wong, arXiv:1902.08640,
§2), in the explicit form used to feed the arithmetic core of `arithTuranCore`.

Given the two analytic inputs `MassBound` (KNW Lemma 2.6) and `ExplFormula` (KNW (2.5)–(2.6)) and
`ConductorLarge` (Siegel), there are absolute `κ > 0`, `q₀` such that for every `q ≥ q₀` and every
pair of zeros `ρ₀` (real, `λ(ρ₀) ≤ 1/100`) and `ρ` (`|Im ρ| ≤ 1`, `λ(ρ) ≤ (1/3) log q`) of a real
character `χ₀` of level `q`, some power `1 ≤ j ≤ κ log q` satisfies

`(1/36) / (4 + λ(ρ)/log q)^{2j} ≤ 4 j (1 - Re ρ₀) / 4^{2j+1}`.

Ingredients: `weylBound_of_massBound` (the Weyl sum is `≪ log q`), `diffBound_of_expl` (the
differentiated explicit formula at `c = 5`, in "exceptional zero removed" form), and the delegated
Turán step `turanPowerStepConst`.  `ConductorLarge` is used only to make the conductor of `χ₀`
large enough that `ExplFormula` (whose threshold bounds the *level* of the character) may be
applied to the primitive character inducing `χ₀`, and that `MassBound` applies at that level.
-/

/-! ## From `MassBound` to the Weyl-sum bound -/

/-- `MassBound` gives the Weyl-sum bound. -/
theorem weylBound_of_massBound (hmass : MassBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ N : ℕ, q₀ ≤ N → ∀ [NeZero N]
      (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive → χ ^ 2 = 1 →
      ∀ {c γ' : ℝ}, 2 ≤ c → c ≤ 10 → |γ'| ≤ 1 →
      Summable (fun v : ℂ => (DhK.kMult χ v : ℝ) *
        (1 / ((c - v.re) ^ 2 + v.im ^ 2) + 1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2))) ∧
      (∑' v : ℂ, (DhK.kMult χ v : ℝ) *
        (1 / ((c - v.re) ^ 2 + v.im ^ 2) + 1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2)))
        ≤ C * Real.log (N : ℝ) := by
  obtain ⟨C₀, hC₀, hM⟩ := hmass
  refine ⟨30 * C₀, by positivity, 3, ?_⟩
  intro N hN _ χ hχ hprim _ c γ' hc hc10 hγ'
  have hN2 : 2 ≤ N := by omega
  have hlogN1 : 1 ≤ Real.log (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 3 ≤ N)
    have h1 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    exact le_trans h1 (Real.log_le_log (by norm_num) h3)
  have hw1re : (3 / 2 : ℝ) ≤ ((c : ℂ)).re := by simp; linarith
  have hw2re : (3 / 2 : ℝ) ≤ ((c : ℂ) + Complex.I * (γ' : ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    linarith
  obtain ⟨hs1, hb1⟩ := hM N hN2 χ hχ hprim (c : ℂ) hw1re
  obtain ⟨hs2, hb2⟩ := hM N hN2 χ hχ hprim ((c : ℂ) + Complex.I * (γ' : ℂ)) hw2re
  have hden1 : ∀ v : ℂ, ‖(c : ℂ) - v‖ ^ 2 = (c - v.re) ^ 2 + v.im ^ 2 := by
    intro v
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hden2 : ∀ v : ℂ, ‖(c : ℂ) + Complex.I * (γ' : ℂ) - v‖ ^ 2
      = (c - v.re) ^ 2 + (v.im - γ') ^ 2 := by
    intro v
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero]
    ring
  have hs1' : Summable (fun v : ℂ => (DhK.kMult χ v : ℝ) * (1 / ((c - v.re) ^ 2 + v.im ^ 2))) := by
    refine hs1.congr (fun v => ?_)
    rw [div_eq_mul_inv, one_div, hden1 v]
  have hs2' : Summable (fun v : ℂ => (DhK.kMult χ v : ℝ) *
      (1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2))) := by
    refine hs2.congr (fun v => ?_)
    rw [div_eq_mul_inv, one_div, hden2 v]
  have hscomb : Summable (fun v : ℂ => (DhK.kMult χ v : ℝ) *
      (1 / ((c - v.re) ^ 2 + v.im ^ 2) + 1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2))) := by
    refine (hs1'.add hs2').congr (fun v => ?_)
    ring
  refine ⟨hscomb, ?_⟩
  have hsplit : (∑' v : ℂ, (DhK.kMult χ v : ℝ) *
      (1 / ((c - v.re) ^ 2 + v.im ^ 2) + 1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2)))
      = (∑' v : ℂ, (DhK.kMult χ v : ℝ) * (1 / ((c - v.re) ^ 2 + v.im ^ 2)))
        + (∑' v : ℂ, (DhK.kMult χ v : ℝ) * (1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2))) := by
    rw [← Summable.tsum_add hs1' hs2']
    exact tsum_congr (fun v => by ring)
  rw [hsplit]
  have hb1' : (∑' v : ℂ, (DhK.kMult χ v : ℝ) * (1 / ((c - v.re) ^ 2 + v.im ^ 2)))
      ≤ C₀ * (Real.log (N : ℝ) + 14) := by
    have h := hb1
    have heq : (∑' v : ℂ, (DhK.kMult χ v : ℝ) / ‖(c : ℂ) - v‖ ^ 2)
        = (∑' v : ℂ, (DhK.kMult χ v : ℝ) * (1 / ((c - v.re) ^ 2 + v.im ^ 2))) :=
      tsum_congr (fun v => by rw [div_eq_mul_inv, one_div, hden1 v])
    rw [heq] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₀))
    have hcn : ‖(c : ℂ)‖ = c := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [hcn]
    have h1 : Real.log (2 + c) ≤ 2 + c - 1 := Real.log_le_sub_one_of_pos (by linarith)
    linarith
  have hb2' : (∑' v : ℂ, (DhK.kMult χ v : ℝ) * (1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2)))
      ≤ C₀ * (Real.log (N : ℝ) + 14) := by
    have h := hb2
    have heq : (∑' v : ℂ, (DhK.kMult χ v : ℝ) / ‖(c : ℂ) + Complex.I * (γ' : ℂ) - v‖ ^ 2)
        = (∑' v : ℂ, (DhK.kMult χ v : ℝ) * (1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2))) :=
      tsum_congr (fun v => by rw [div_eq_mul_inv, one_div, hden2 v])
    rw [heq] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₀))
    have hnorm : ‖(c : ℂ) + Complex.I * (γ' : ℂ)‖ ≤ 11 := by
      have h1 := norm_add_le (c : ℂ) (Complex.I * (γ' : ℂ))
      have h2 : ‖(c : ℂ)‖ = c := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have h3 : ‖Complex.I * (γ' : ℂ)‖ = |γ'| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      linarith [h1, h2, h3, hγ', hc10]
    have h1 : Real.log (2 + ‖(c : ℂ) + Complex.I * (γ' : ℂ)‖)
        ≤ 2 + ‖(c : ℂ) + Complex.I * (γ' : ℂ)‖ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    linarith
  calc (∑' v : ℂ, (DhK.kMult χ v : ℝ) * (1 / ((c - v.re) ^ 2 + v.im ^ 2)))
        + (∑' v : ℂ, (DhK.kMult χ v : ℝ) * (1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2)))
      ≤ C₀ * (Real.log (N : ℝ) + 14) + C₀ * (Real.log (N : ℝ) + 14) := add_le_add hb1' hb2'
    _ = C₀ * (2 * Real.log (N : ℝ) + 28) := by ring
    _ ≤ 30 * C₀ * Real.log (N : ℝ) := by nlinarith [hC₀, hlogN1]

/-- `ExplFormula` in "pinned" (exceptional zero removed) form at `c ≥ 5`. -/
theorem diffBound_of_expl (hef : ExplFormula) :
    ∃ q₀ : ℕ, ∀ N : ℕ, q₀ ≤ N → ∀ [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → χ ^ 2 = 1 → ∀ {β₁ : ℝ}, β₁ < 1 →
      DirichletCharacter.completedLFunction χ (β₁ : ℂ) = 0 → ∀ (j : ℕ), 1 ≤ j →
      ∀ {c γ' : ℝ}, 5 ≤ c →
      Summable (fun v : ℂ => (DhK.kMult χ v : ℝ) *
        ((1 / ((c : ℂ) - v) ^ (2 * j)).re
          + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re)) ∧
      4 * (j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1) ≥
        ∑' v : ℂ, (if v = (β₁ : ℂ) then 0 else (DhK.kMult χ v : ℝ)) *
          ((1 / ((c : ℂ) - v) ^ (2 * j)).re
            + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re) := by
  obtain ⟨q₀, hE⟩ := hef
  refine ⟨q₀, ?_⟩
  intro N hN _ χ hχ hprim hχ2 β₁ hβ₁ hz j hj c γ' hc
  obtain ⟨hsumm, hbnd⟩ := hE N hN χ hχ hprim hχ2 j hj c γ' hc hβ₁ hz
  refine ⟨hsumm, ?_⟩
  set f : ℂ → ℝ := fun v => (1 / ((c : ℂ) - v) ^ (2 * j)).re
      + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re with hf
  have hpt : ∀ v : ℂ, (if v = (β₁ : ℂ) then 0 else (DhK.kMult χ v : ℝ)) * f v
      = (if v = (β₁ : ℂ) then 0 else (DhK.kMult χ v : ℝ) * f v) := by
    intro v
    by_cases hv : v = (β₁ : ℂ) <;> simp [hv]
  have hkey : (∑' v : ℂ, (if v = (β₁ : ℂ) then 0 else (DhK.kMult χ v : ℝ)) * f v)
      = (∑' v : ℂ, (DhK.kMult χ v : ℝ) * f v) - (DhK.kMult χ (β₁ : ℂ) : ℝ) * f (β₁ : ℂ) := by
    rw [tsum_congr hpt]
    have h := Summable.tsum_eq_add_tsum_ite hsumm ((β₁ : ℂ))
    linarith [h]
  rw [hkey]
  exact hbnd

/-! ## The main theorem -/

theorem turanPowerIneq : Work.LinnikAreas.DhExplicit.MassBound → Work.LinnikAreas.DhExplicit.ExplFormula → Work.LinnikAreas.DhExplicit.ConductorLarge →
    ∃ κ : ℝ, 0 < κ ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₀ : DirichletCharacter ℂ q) (ρ₀ ρ : ℂ),
      Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
      Work.LinnikContract.zeroMult χ₀ ρ ≠ 0 → ρ ≠ ρ₀ → |ρ.im| ≤ 1 →
      Work.LinnikContract.lamOf q ρ ≤ (1 / 3) * Real.log q →
      ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ κ * Real.log q ∧
        (1 / 36) / ((4 : ℝ) + Work.LinnikContract.lamOf q ρ / Real.log q) ^ (2 * j)
          ≤ 4 * (j : ℝ) * (1 - ρ₀.re) / (4 : ℝ) ^ (2 * j + 1) := by
  intro hmass hef hcond
  obtain ⟨CW, hCWpos, qWeyl, hWeylBound⟩ := weylBound_of_massBound hmass
  obtain ⟨qDiff, hDiffBound⟩ := diffBound_of_expl hef
  obtain ⟨qCond, hCond⟩ := hcond (max qWeyl (max qDiff 3))
  refine ⟨10000 * CW, by positivity, max (max qWeyl 3) (max qDiff qCond), ?_⟩
  intro q hq hqne χ₀ ρ₀ ρ hmin hχ2 hρ₀im h100 hzm hρne himρ hρle
  have hqWeyl : qWeyl ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq3 : 3 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hqDiff : qDiff ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hqCond : qCond ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hχ₀ne : χ₀ ≠ 1 := hmin.1.1
  have hzρ₀m : Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 := hmin.1.2.1
  haveI : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  -- the conductor is large
  have hf_ge : max qWeyl (max qDiff 3) ≤ χ₀.conductor :=
    hCond q hqCond χ₀ ρ₀ hχ₀ne hχ2 hρ₀im hzρ₀m h100
  have hf3 : 3 ≤ χ₀.conductor := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hf_ge
  have hf_diff : qDiff ≤ χ₀.conductor := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hf_ge
  have hf_weyl : qWeyl ≤ χ₀.conductor := le_trans (le_max_left _ _) hf_ge
  -- basic numerical bounds
  have hlogq1 : 1 ≤ Real.log (q : ℝ) := by
    have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have h1 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    exact le_trans h1 (Real.log_le_log (by norm_num) h3)
  have hlogq : 0 < Real.log (q : ℝ) := lt_of_lt_of_le zero_lt_one hlogq1
  -- the primitive character inducing `χ₀`
  have hχ'ne : χ₀.primitiveCharacter ≠ 1 := DhK.primitiveCharacter_ne_one hχ₀ne
  have hχ'prim : χ₀.primitiveCharacter.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ₀
  have hχ'2 : χ₀.primitiveCharacter ^ 2 = 1 := by
    refine (DirichletCharacter.changeLevel_eq_one_iff χ₀.conductor_dvd_level).mp ?_
    rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, hχ2]
  -- the two zeros lie in the critical strip
  have hρ₀strip : 0 < ρ₀.re ∧ ρ₀.re < 1 := DhK.zeroMult_strip χ₀ hχ₀ne hzρ₀m
  have hρstrip : 0 < ρ.re ∧ ρ.re < 1 := DhK.zeroMult_strip χ₀ hχ₀ne hzm
  have hzρ₀' : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₀.primitiveCharacter) ρ₀ ≠ 0 := by
    simpa only [Work.LinnikContract.zeroMult] using hzρ₀m
  have hzρ' : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₀.primitiveCharacter) ρ ≠ 0 := by
    simpa only [Work.LinnikContract.zeroMult] using hzm
  -- the numerical hypotheses of the Turán step
  have hρ₀le' : 1 - ρ₀.re ≤ 1 / 100 := by
    have h := h100
    rw [Work.LinnikContract.lamOf] at h
    have h2 : (1 - ρ₀.re) ≤ (1 - ρ₀.re) * Real.log q :=
      le_mul_of_one_le_right (by linarith [hρ₀strip.2]) hlogq1
    linarith
  have hρle' : 1 - ρ.re ≤ 1 / 3 := by
    have h := hρle
    rw [Work.LinnikContract.lamOf] at h
    by_contra hc
    push_neg at hc
    nlinarith [h, hlogq, hc]
  -- the Weyl bound at level `χ₀.conductor`
  have hweyl' : ∀ {c γ' : ℝ}, 2 ≤ c → c ≤ 10 → |γ'| ≤ 1 →
      Summable (fun v : ℂ => (DhK.kMult χ₀.primitiveCharacter v : ℝ) *
        (1 / ((c - v.re) ^ 2 + v.im ^ 2) + 1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2))) ∧
      (∑' v : ℂ, (DhK.kMult χ₀.primitiveCharacter v : ℝ) *
        (1 / ((c - v.re) ^ 2 + v.im ^ 2) + 1 / ((c - v.re) ^ 2 + (v.im - γ') ^ 2)))
        ≤ CW * Real.log ((χ₀.conductor : ℕ) : ℝ) := by
    intro c γ' hc hc10 hγ'
    exact hWeylBound (χ₀.conductor) hf_weyl χ₀.primitiveCharacter hχ'ne hχ'prim hχ'2 hc hc10 hγ'
  -- the explicit formula at level `χ₀.conductor`
  have hβ₁zero : DirichletCharacter.completedLFunction χ₀.primitiveCharacter (((ρ₀.re : ℝ) : ℂ)) = 0 := by
    have h0 : DirichletCharacter.completedLFunction χ₀.primitiveCharacter ρ₀ = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hzρ₀'
    have he : (((ρ₀.re : ℝ) : ℂ)) = ρ₀ := by
      apply Complex.ext <;> simp [hρ₀im]
    rw [he]; exact h0
  have hdiff' : ∀ (j : ℕ), 1 ≤ j → ∀ {c γ' : ℝ}, 5 ≤ c →
      Summable (fun v : ℂ => (DhK.kMult χ₀.primitiveCharacter v : ℝ) *
        ((1 / ((c : ℂ) - v) ^ (2 * j)).re
          + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re)) ∧
      4 * (j : ℝ) * (1 - ρ₀.re) / (c - 1) ^ (2 * j + 1) ≥
        ∑' v : ℂ, (if v = ρ₀ then 0 else (DhK.kMult χ₀.primitiveCharacter v : ℝ)) *
          ((1 / ((c : ℂ) - v) ^ (2 * j)).re
            + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re) := by
    intro j hj c γ' hc
    obtain ⟨hs, hb⟩ := hDiffBound (χ₀.conductor) hf_diff χ₀.primitiveCharacter hχ'ne hχ'prim
      hχ'2 (β₁ := ρ₀.re) hρ₀strip.2 hβ₁zero j hj hc
    refine ⟨hs, ?_⟩
    have he : (((ρ₀.re : ℝ) : ℂ)) = ρ₀ := by
      apply Complex.ext <;> simp [hρ₀im]
    simpa only [he] using hb
  -- the Turán step
  obtain ⟨j, hj1, hjK, hjineq⟩ :=
    turanPowerStepConst χ₀.primitiveCharacter ρ₀ ρ hf3 hχ'ne hχ'prim hχ'2 hρ₀im hzρ₀' hzρ'
      himρ hρne hρ₀le' hρle' hCWpos hweyl' hdiff'
  refine ⟨j, hj1, ?_, ?_⟩
  · have hlogf : Real.log (((χ₀.conductor : ℕ)) : ℝ) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < χ₀.conductor))
        (by exact_mod_cast Nat.le_of_dvd (by omega : 0 < q) χ₀.conductor_dvd_level)
    calc (j : ℝ) ≤ 10000 * CW * Real.log (((χ₀.conductor : ℕ)) : ℝ) := hjK
      _ ≤ 10000 * CW * Real.log (q : ℝ) := mul_le_mul_of_nonneg_left hlogf (by positivity)
  · have hlam : Work.LinnikContract.lamOf q ρ / Real.log q = 1 - ρ.re := by
      rw [Work.LinnikContract.lamOf, mul_div_assoc, div_self (ne_of_gt hlogq), mul_one]
    have hden : (4 : ℝ) + Work.LinnikContract.lamOf q ρ / Real.log q = 5 - ρ.re := by
      rw [hlam]; ring
    rw [hden]; exact hjineq

end Work.LinnikAreas.DhExplicit
