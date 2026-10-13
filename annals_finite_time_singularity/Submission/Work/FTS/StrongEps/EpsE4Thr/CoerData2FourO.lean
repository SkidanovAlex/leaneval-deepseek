/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/CoerData2FourO.lean` — the level-four clean data of the
coercivity induction, on the open class

`CoercivityFix/Assembly/coerData2_four.lean` runs the clean (`𝓛̂`) induction three times, from the
level-`1` data `coerData2_one` to the level-`4` data `CoerData2 α 4 (IP4 …)`, using the step
`step2_data_ge` with the instances `StepReg2_all`, `Comm2_L1`/`Comm2_succ`, the `Ê₂`-bounds
`hE2_unif` and the norm comparisons `hnormD_all`.

This file is the open-class re-run: the same proof with `CoerData2` replaced by `CoerData2O` and
each input by its proved open port (`coerData2_one_H1IP_O`, `step2_data_ge_O`, `StepReg2_all_O`,
`Comm2_L1_O`, `Comm2_succ_O`, `hnormD_all_O`, `hE2_unif_O` from `E2hat_HkSq_le_uniform_O`).
It supplies the `hCD₁` input side of the final `transfer_level4` assembly.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.EpsE4Thr.StepDataO
import Submission.Work.FTS.StrongEps.EpsE4Thr.Coer1LhatO
import Submission.Work.FTS.StrongEps.EpsE4Thr.step2_data_ge_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.StepReg2_all_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.Comm2_L1_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.Comm2_succ_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2hat_HkSq_le_uniform_O
import Submission.Work.FTS.CoercivityFix.Assembly.coerData2_four

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4
local notation "IP2" => Work.FTS.CoercivityFix.Assembly.IP2
local notation "IP3" => Work.FTS.CoercivityFix.Assembly.IP3

/-- **The `Ê₂`-defect norm bound on the open class** (the open analogue of
`Assembly.hE2_unif`), from `E2hat_HkSq_le_uniform_O` via `Real.sqrt`. -/
theorem hE2_unif_O (n : ℕ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ α : ℝ, 0 < α → ∀ f : Fn, RegQo α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
  obtain ⟨Cn, hCn, hb⟩ := E2hat_HkSq_le_uniform_O n
  refine ⟨Real.sqrt Cn, Real.sqrt_nonneg _, fun α hα f hf => ?_⟩
  have hA0 : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
  have hB0 : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
    Work.Spaces.HkSq_nonneg α n _
  have hsq : Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
      ≤ (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) ^ 2 := by
    rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    nlinarith [Real.sqrt_nonneg (Work.Spaces.HkSq α n f),
      Real.sqrt_nonneg (Work.Spaces.HkSq α n (Work.Spaces.Dth f)),
      mul_nonneg (Real.sqrt_nonneg (Work.Spaces.HkSq α n f))
        (Real.sqrt_nonneg (Work.Spaces.HkSq α n (Work.Spaces.Dth f)))]
  have hsplit : Real.sqrt (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
      ≤ Real.sqrt (Work.Spaces.HkSq α n f)
        + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at h
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  calc Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f))
      ≤ Real.sqrt (Cn * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        Real.sqrt_le_sqrt (hb α hα f hf)
    _ = Real.sqrt Cn
          * Real.sqrt (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :=
        Real.sqrt_mul hCn.le _
    _ ≤ Real.sqrt Cn * (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        mul_le_mul_of_nonneg_left hsplit (Real.sqrt_nonneg Cn)

theorem coerData2_four_O :
    ∃ (c₁ c₂ c₁' c₂' c₁'' c₂'' cc CC : ℝ),
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₁' ∧ 0 < c₂' ∧ 0 < c₁'' ∧ 0 < c₂'' ∧ 0 < cc ∧ 0 < CC ∧
      ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 4) →
        CoerData2O α 4 (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) cc CC := by
  -- the level-1 data (`cc₁ = 2`) and the three `α`-uniform defect constants
  obtain ⟨CC₁, hCC₁, hdata₁⟩ := coerData2_one_H1IP_O
  obtain ⟨κ₁, hκ₁, hE2₁⟩ := hE2_unif_O 1
  obtain ⟨κ₂, hκ₂, hE2₂⟩ := hE2_unif_O 2
  obtain ⟨κ₃, hκ₃, hE2₃⟩ := hE2_unif_O 3
  -- the coefficients are fixed at the sample point `α = 1/8` (in the paper's range)
  have hα₈ : (1 / 8 : ℝ) ∈ Set.Ioc 0 (1 / 4) := ⟨by norm_num, by norm_num⟩
  have hα₈pos : (0 : ℝ) < 1 / 8 := by norm_num
  have d₁₈ : CoerData2O (1 / 8) 1 (Work.Coercivity.H1IP (1 / 8)) 2 CC₁ :=
    hdata₁ (1 / 8) hα₈
  -- level 1 → 2
  obtain ⟨c₂, hc₂, hsmall₂⟩ := Work.FTS.CoercivityFix.exists_small_step_coeffs
    (cc := 2) (CC := CC₁) (κ := κ₁) (c₁ := 1) (by norm_num) hCC₁ (by norm_num) hκ₁
  have d₂₈ : CoerData2O (1 / 8) 2
      (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP (1 / 8)))
      (2 * min 1 (min 1 c₂) / (2 * 1)) (3 * max 1 (max 1 c₂) * CC₁) :=
    step2_data_ge_O (1 / 8) 1 hα₈pos d₁₈ hκ₁ (by norm_num) hc₂ (by norm_num) hsmall₂
      (StepReg2_all_O (1 / 8) hα₈pos 1) (Comm2_L1_O (1 / 8) hα₈pos) (hE2₁ (1 / 8) hα₈pos)
      (hnormD_all_O (1 / 8) hα₈pos (n := 1) (by norm_num))
  -- level 2 → 3
  obtain ⟨c₂', hc₂', hsmall₂'⟩ := Work.FTS.CoercivityFix.exists_small_step_coeffs
    (cc := 2 * min 1 (min 1 c₂) / (2 * 1)) (CC := 3 * max 1 (max 1 c₂) * CC₁)
    (κ := κ₂) (c₁ := 1) d₂₈.hcc d₂₈.hCC (by norm_num) hκ₂
  have d₃₈ : CoerData2O (1 / 8) 3
      (Work.Coercivity.HkIPStep 1 c₂'
        (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP (1 / 8))))
      ((2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
      (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁)) :=
    step2_data_ge_O (1 / 8) 2 hα₈pos d₂₈ hκ₂ (by norm_num) hc₂' (by norm_num) hsmall₂'
      (StepReg2_all_O (1 / 8) hα₈pos 2)
      (Comm2_succ_O (1 / 8) hα₈pos 1 (Comm2_L1_O (1 / 8) hα₈pos))
      (hE2₂ (1 / 8) hα₈pos) (hnormD_all_O (1 / 8) hα₈pos (n := 2) (by norm_num))
  -- level 3 → 4
  obtain ⟨c₂'', hc₂'', hsmall₂''⟩ := Work.FTS.CoercivityFix.exists_small_step_coeffs
    (cc := (2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
    (CC := 3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁))
    (κ := κ₃) (c₁ := 1) d₃₈.hcc d₃₈.hCC (by norm_num) hκ₃
  have d₄₈ : CoerData2O (1 / 8) 4
      (Work.Coercivity.HkIPStep 1 c₂''
        (Work.Coercivity.HkIPStep 1 c₂'
          (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP (1 / 8)))))
      (((2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
        * min 1 (min 1 c₂'') / (2 * 1))
      (3 * max 1 (max 1 c₂'') * (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁))) :=
    step2_data_ge_O (1 / 8) 3 hα₈pos d₃₈ hκ₃ (by norm_num) hc₂'' (by norm_num) hsmall₂''
      (StepReg2_all_O (1 / 8) hα₈pos 3)
      (Comm2_succ_O (1 / 8) hα₈pos 2 (Comm2_succ_O (1 / 8) hα₈pos 1 (Comm2_L1_O (1 / 8) hα₈pos)))
      (hE2₃ (1 / 8) hα₈pos) (hnormD_all_O (1 / 8) hα₈pos (n := 3) (by norm_num))
  refine ⟨1, c₂, 1, c₂', 1, c₂'',
    ((2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
      * min 1 (min 1 c₂'') / (2 * 1),
    3 * max 1 (max 1 c₂'') * (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁)),
    by norm_num, hc₂, by norm_num, hc₂', by norm_num, hc₂'', d₄₈.hcc, d₄₈.hCC, ?_⟩
  intro α hαI
  have hα : 0 < α := hαI.1
    -- the same three steps, now at the given `α` (the coefficients are the fixed ones)
  have e₁ : CoerData2O α 1 (Work.Coercivity.H1IP α) 2 CC₁ := hdata₁ α hαI
  have e₂ : CoerData2O α 2 (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP α))
      (2 * min 1 (min 1 c₂) / (2 * 1)) (3 * max 1 (max 1 c₂) * CC₁) :=
    step2_data_ge_O α 1 hα e₁ hκ₁ (by norm_num) hc₂ (by norm_num) hsmall₂
      (StepReg2_all_O α hα 1) (Comm2_L1_O α hα) (hE2₁ α hα)
      (hnormD_all_O α hα (n := 1) (by norm_num))
  have e₃ : CoerData2O α 3
      (Work.Coercivity.HkIPStep 1 c₂'
        (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP α)))
      ((2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
      (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁)) :=
    step2_data_ge_O α 2 hα e₂ hκ₂ (by norm_num) hc₂' (by norm_num) hsmall₂'
      (StepReg2_all_O α hα 2) (Comm2_succ_O α hα 1 (Comm2_L1_O α hα))
      (hE2₂ α hα) (hnormD_all_O α hα (n := 2) (by norm_num))
  have e₄ : CoerData2O α 4
      (Work.Coercivity.HkIPStep 1 c₂''
        (Work.Coercivity.HkIPStep 1 c₂'
          (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP α))))
      (((2 * min 1 (min 1 c₂) / (2 * 1)) * min 1 (min 1 c₂') / (2 * 1))
        * min 1 (min 1 c₂'') / (2 * 1))
      (3 * max 1 (max 1 c₂'') * (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁))) :=
    step2_data_ge_O α 3 hα e₃ hκ₃ (by norm_num) hc₂'' (by norm_num) hsmall₂''
      (StepReg2_all_O α hα 3)
      (Comm2_succ_O α hα 2 (Comm2_succ_O α hα 1 (Comm2_L1_O α hα)))
      (hE2₃ α hα) (hnormD_all_O α hα (n := 3) (by norm_num))
  simpa only [Work.FTS.CoercivityFix.Assembly.IP4] using e₄

end Work.FTS.StrongEps.EpsE4Thr
