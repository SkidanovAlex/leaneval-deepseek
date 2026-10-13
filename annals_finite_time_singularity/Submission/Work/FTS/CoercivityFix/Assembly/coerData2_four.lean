/-
# `Assembly/coerData2_four` — the three iterations of the corrected step

Design `NOTES_assembly.md` §4.1: from the level-`1` data `coerData2_one`, iterate the
corrected step three times, choosing the step coefficient `c₂` at each level by
`Step.exists_small_step_coeffs`, to obtain the level-`4` data

  `CoerData2 α 4 (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') cc₄ CC₄`      for every `α ∈ (0, 1/4]`,

i.e. the level-`4` coercivity `cc₄·|f|²_{ℋ⁴} ≤ IP4 … α (𝓛̂ f) f` of the clean operator
`𝓛̂ = 𝓛 − Transport` together with the level-`4` Cauchy–Schwarz bound.  The mathematical
content is the paper's arithmetic (`step2_data`); this file *sequences* the three
applications and produces the coefficients.

## Why a local copy of the step

`Assembly.step2_data` is stated with the *full* `StepReg2 α n` port package, whose
`normSub` field is **unsatisfiable** for `α < -1/10` (`not_stepReg2_of_lt`, whose proof
passes through the `sorry` of `Assembly.exists_not_normSub_lt`); hence `step2_data`'s proof
term depends on `sorryAx`.  The corrected induction only ever runs in the paper's range
`(0, α₂] ⊆ (0, 1/4]`, where `StepReg2` *is* available (`StepReg2_all`), so the step is
stated here with the honest hypothesis `-(1/10) ≤ α` (a verbatim transcription of
`step2_data`'s body: `cs_clause_succ` for the Cauchy–Schwarz clause and `coer_clause_succ`
for the coercivity) and iterated.

## The constants (for the assembler)

With `κₙ = √Cₙ` from the `α`-uniform defect bound (`E2hat_HkSq_le_uniform`; `κₙ` is one
number valid for all `α ≥ -1/10`), and `c_{1,n} = 1` at each level,

    cc₂ = 2·min 1 (min 1 c₂)/(2·1),      CC₂ = 3·max 1 (max 1 c₂)·CC₁
    cc₃ = cc₂·min 1 (min 1 c₂')/(2·1),   CC₃ = 3·max 1 (max 1 c₂')·CC₂
    cc₄ = cc₃·min 1 (min 1 c₂'')/(2·1),  CC₄ = 3·max 1 (max 1 c₂'')·CC₃

with `c₂, c₂', c₂''` the small coefficients supplied by `exists_small_step_coeffs`.  Since
`StepSmall` forces `c₂ ≤ cc²/(4(CC·κ)²)`, the coercivity constant `cc₄` is *very* small
(cubically small at each level: with `CC₁ ~ 10²²` and `κₙ ~ 1` it is below `10⁻⁵⁷⁰`).  It is
positive, which is all `UnifIP.coer` needs, but its size is what makes the transfer
`𝓛_Γ^T = 𝓛̂ + Corr` delicate: the `L₁₂`-slots of `Corr` can only be bounded by
Cauchy–Schwarz with the `ℋ¹` constant `CC₁`, so they cannot be split off as a separate term
dominated by `cc₄`; they have to be absorbed *inside* the induction.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.Instantiate
import Submission.Work.FTS.CoercivityFix.Assembly.StepReg2_all
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2_levels
import Submission.Work.FTS.CoercivityFix.Assembly.step2_data
import Submission.Work.FTS.CoercivityFix.Assembly.E2hat_HkSq_le_uniform
import Submission.Work.FTS.CoercivityFix.Step

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ)

set_option autoImplicit false

/-! ## The `α`-uniform defect constant in the `HkNorm` form -/

/-- **The `Ê₂`-slot bound in the `HkNorm` form, with a constant valid for the whole range
`α ≥ -1/10`.**  This is `Assembly.Instantiate.hE2_all` with the uniformity of the constant
made explicit: the number `κ` below is `√Cₙ` of `E2hat_HkSq_le_uniform`, hence independent
of `α`, which is what lets the three step coefficients be chosen *before* `α` is fixed. -/
theorem hE2_unif (n : ℕ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ α : ℝ, -(1 / 10 : ℝ) ≤ α → ∀ f : Fn, RegQ α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
  obtain ⟨Cn, hCn, hb⟩ := E2hat_HkSq_le_uniform n
  refine ⟨Real.sqrt Cn, Real.sqrt_nonneg _, fun α hα f hf => ?_⟩
  have h1 : Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
      = Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)) := rfl
  rw [h1, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  refine le_trans (Real.sqrt_le_sqrt (hb α hα f hf)) ?_
  rw [Real.sqrt_mul hCn.le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg Cn)
  set A := Work.Spaces.HkSq α n f with hA
  set B := Work.Spaces.HkSq α n (Work.Spaces.Dth f) with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact Work.Spaces.HkSq_nonneg α n f
  have hB0 : 0 ≤ B := by rw [hB]; exact Work.Spaces.HkSq_nonneg α n _
  have hsq : A + B ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
    rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    nlinarith [Real.sqrt_nonneg A, Real.sqrt_nonneg B,
      mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))] at h

/-! ## The step, in the paper's range `α ≥ -1/10` -/

/-- **The corrected step with the honest hypothesis `-(1/10) ≤ α`.**  This is the body of
`Assembly.step2_data` with the absurd branch `α < -1/10` deleted, so that the proof does not
pass through the `sorry` of `exists_not_normSub_lt`. -/
theorem step2_data_ge (α : ℝ) (n : ℕ) (hα : -(1 / 10 : ℝ) ≤ α)
    {IP : Fn → Fn → ℝ} {cc CC κ c₁ c₂ D : ℝ}
    (hdata : CoerData2 α n IP cc CC)
    (hκ : 0 ≤ κ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D)
    (hsmall : Work.FTS.CoercivityFix.StepSmall cc CC κ c₁ c₂)
    (hr : StepReg2 α n) (hc : Comm2 α n IP)
    (hE2 : ∀ f : Fn, RegQ α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hnormD : ∀ f : Fn, RegQ α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ D * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f))) :
    CoerData2 α (n + 1) (Work.Coercivity.HkIPStep c₁ c₂ IP)
      (cc * min 1 (min c₁ c₂) / (2 * D)) (3 * max 1 (max c₁ c₂) * CC) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the coercivity constant is positive
    have hmin : 0 < min 1 (min c₁ c₂) := lt_min one_pos (lt_min hc₁ hc₂)
    exact div_pos (mul_pos hdata.hcc hmin) (by positivity)
  · -- the Cauchy–Schwarz constant is positive
    exact mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le one_pos (le_max_left _ _)))
      hdata.hCC
  · -- Cauchy–Schwarz: the three slots, each bounded through the level-`(n+1)` norm of `f`
    exact cs_clause_succ α hα n hdata.cs (le_of_lt hdata.hCC)
      (fun f hf => RegQ_dth_ge α hα hf) hc₁ hc₂
  · -- coercivity of `𝓛̂`: the paper's arithmetic, with the `RegQ`-ports of `hr`
    exact coer_clause_succ α n hdata hκ hc₁ hc₂ hD hsmall hr hc hE2 hnormD

/-! ## The three iterations -/

/-- **The level-`4` data of the corrected induction**, with the coefficients produced by the
paper's small-step choice.  This is `NOTES_assembly.md` §4.1. -/
theorem coerData2_four :
    ∃ (c₁ c₂ c₁' c₂' c₁'' c₂'' cc CC : ℝ),
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₁' ∧ 0 < c₂' ∧ 0 < c₁'' ∧ 0 < c₂'' ∧ 0 < cc ∧ 0 < CC ∧
      ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 4) →
        CoerData2 α 4 (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) cc CC := by
  -- the level-1 data (`cc₁ = 2`) and the three `α`-uniform defect constants
  obtain ⟨CC₁, hCC₁, hdata₁⟩ := coerData2_one
  obtain ⟨κ₁, hκ₁, hE2₁⟩ := hE2_unif 1
  obtain ⟨κ₂, hκ₂, hE2₂⟩ := hE2_unif 2
  obtain ⟨κ₃, hκ₃, hE2₃⟩ := hE2_unif 3
  -- the coefficients are fixed at the sample point `α = 1/8` (in the paper's range)
  have hα₈ : (1 / 8 : ℝ) ∈ Set.Ioc 0 (1 / 4) := ⟨by norm_num, by norm_num⟩
  have hα₈pos : (0 : ℝ) < 1 / 8 := by norm_num
  have hα₈' : -(1 / 10 : ℝ) ≤ 1 / 8 := by norm_num
  have d₁₈ : CoerData2 (1 / 8) 1 (Work.Coercivity.H1IP (1 / 8)) 2 CC₁ :=
    hdata₁ (1 / 8) hα₈
  -- level 1 → 2
  obtain ⟨c₂, hc₂, hsmall₂⟩ := Work.FTS.CoercivityFix.exists_small_step_coeffs
    (cc := 2) (CC := CC₁) (κ := κ₁) (c₁ := 1) (by norm_num) hCC₁ (by norm_num) hκ₁
  have d₂₈ : CoerData2 (1 / 8) 2
      (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP (1 / 8)))
      (2 * min 1 (min 1 c₂) / (2 * 1)) (3 * max 1 (max 1 c₂) * CC₁) :=
    step2_data_ge (1 / 8) 1 hα₈' d₁₈ hκ₁ (by norm_num) hc₂ (by norm_num) hsmall₂
      (StepReg2_all (1 / 8) hα₈pos 1) (Comm2_L1 (1 / 8) hα₈pos) (hE2₁ (1 / 8) hα₈')
      (hnormD_all (1 / 8) hα₈pos (n := 1) (by norm_num))
  -- level 2 → 3
  obtain ⟨c₂', hc₂', hsmall₂'⟩ := Work.FTS.CoercivityFix.exists_small_step_coeffs
    (cc := 2 * min 1 (min 1 c₂) / (2 * 1)) (CC := 3 * max 1 (max 1 c₂) * CC₁)
    (κ := κ₂) (c₁ := 1) d₂₈.hcc d₂₈.hCC (by norm_num) hκ₂
  have d₃₈ : CoerData2 (1 / 8) 3
      (Work.Coercivity.HkIPStep 1 c₂'
        (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP (1 / 8))))
      ((2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
      (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁)) :=
    step2_data_ge (1 / 8) 2 hα₈' d₂₈ hκ₂ (by norm_num) hc₂' (by norm_num) hsmall₂'
      (StepReg2_all (1 / 8) hα₈pos 2)
      (Comm2_succ (1 / 8) hα₈pos 1 (Comm2_L1 (1 / 8) hα₈pos))
      (hE2₂ (1 / 8) hα₈') (hnormD_all (1 / 8) hα₈pos (n := 2) (by norm_num))
  -- level 3 → 4
  obtain ⟨c₂'', hc₂'', hsmall₂''⟩ := Work.FTS.CoercivityFix.exists_small_step_coeffs
    (cc := (2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
    (CC := 3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁))
    (κ := κ₃) (c₁ := 1) d₃₈.hcc d₃₈.hCC (by norm_num) hκ₃
  have d₄₈ : CoerData2 (1 / 8) 4
      (Work.Coercivity.HkIPStep 1 c₂''
        (Work.Coercivity.HkIPStep 1 c₂'
          (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP (1 / 8)))))
      (((2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
        * min 1 (min 1 c₂'') / (2 * 1))
      (3 * max 1 (max 1 c₂'') * (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁))) :=
    step2_data_ge (1 / 8) 3 hα₈' d₃₈ hκ₃ (by norm_num) hc₂'' (by norm_num) hsmall₂''
      (StepReg2_all (1 / 8) hα₈pos 3)
      (Comm2_succ (1 / 8) hα₈pos 2 (Comm2_succ (1 / 8) hα₈pos 1 (Comm2_L1 (1 / 8) hα₈pos)))
      (hE2₃ (1 / 8) hα₈') (hnormD_all (1 / 8) hα₈pos (n := 3) (by norm_num))
  refine ⟨1, c₂, 1, c₂', 1, c₂'',
    ((2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
      * min 1 (min 1 c₂'') / (2 * 1),
    3 * max 1 (max 1 c₂'') * (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁)),
    by norm_num, hc₂, by norm_num, hc₂', by norm_num, hc₂'', d₄₈.hcc, d₄₈.hCC, ?_⟩
  intro α hαI
  have hα : 0 < α := hαI.1
  have hα' : -(1 / 10 : ℝ) ≤ α := by linarith
  -- the same three steps, now at the given `α` (the coefficients are the fixed ones)
  have e₁ : CoerData2 α 1 (Work.Coercivity.H1IP α) 2 CC₁ := hdata₁ α hαI
  have e₂ : CoerData2 α 2 (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP α))
      (2 * min 1 (min 1 c₂) / (2 * 1)) (3 * max 1 (max 1 c₂) * CC₁) :=
    step2_data_ge α 1 hα' e₁ hκ₁ (by norm_num) hc₂ (by norm_num) hsmall₂
      (StepReg2_all α hα 1) (Comm2_L1 α hα) (hE2₁ α hα')
      (hnormD_all α hα (n := 1) (by norm_num))
  have e₃ : CoerData2 α 3
      (Work.Coercivity.HkIPStep 1 c₂'
        (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP α)))
      ((2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
      (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁)) :=
    step2_data_ge α 2 hα' e₂ hκ₂ (by norm_num) hc₂' (by norm_num) hsmall₂'
      (StepReg2_all α hα 2) (Comm2_succ α hα 1 (Comm2_L1 α hα))
      (hE2₂ α hα') (hnormD_all α hα (n := 2) (by norm_num))
  have e₄ : CoerData2 α 4
      (Work.Coercivity.HkIPStep 1 c₂''
        (Work.Coercivity.HkIPStep 1 c₂'
          (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP α))))
      (((2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
        * min 1 (min 1 c₂'') / (2 * 1))
      (3 * max 1 (max 1 c₂'') * (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁))) :=
    step2_data_ge α 3 hα' e₃ hκ₃ (by norm_num) hc₂'' (by norm_num) hsmall₂''
      (StepReg2_all α hα 3)
      (Comm2_succ α hα 2 (Comm2_succ α hα 1 (Comm2_L1 α hα)))
      (hE2₃ α hα') (hnormD_all α hα (n := 3) (by norm_num))
  simpa only [IP4] using e₄

end Work.FTS.CoercivityFix.Assembly
