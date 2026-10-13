/-
# `Assembly/Instantiate.lean` — the base level, the norm comparison and the `Ê₂` constant

This file discharges, from the already-proved material of the chapter, the three inputs the
corrected step needs at *every* level:

* the level-`1` data `CoerData2 α 1 (H1IP α) 2 CC`: coercivity is `Coer1.coer1_Lhat`,
  Cauchy–Schwarz is `Assembly.H1IP_cs_Q` (with an `α`-independent constant);
* the one-sided norm comparison `HkSq α (n+1) f ≤ HkSq α n f + HkSq α n (D_θf) +
  HkSq α n (D_z f)` in the interior class (`Assembly.HkSq_succ_le_Q`);
* the `Ê₂`-slot constant in the `HkNorm` form that the step consumes
  (`Assembly.E2hat_HkSq_le_uniform`, uniform in `α ≥ -1/10`).

It also records the level-`1` algebraic inputs `Comm2 α 1 (H1IP α)`; the higher levels are
obtained by `Assembly.Comm2_succ`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.H1IP_cs_Q
import Submission.Work.FTS.CoercivityFix.Assembly.H1IP_core_Q
import Submission.Work.FTS.CoercivityFix.Assembly.HkSq_succ_le_Q
import Submission.Work.FTS.CoercivityFix.Assembly.E2hat_HkSq_le_uniform
import Submission.Work.FTS.CoercivityFix.StepAssembly.H1IP_congr_qd
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat
import Submission.Work.FTS.CoercivityFix.Coer1.coer1_Lhat

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

/-- **The level-`1` algebraic inputs**: congruence (membership-free), additivity on
`RegQ α 1`, and the two commutator identities of `Lhat`. -/
theorem Comm2_L1 (α : ℝ) (hα : 0 < α) : Comm2 α 1 (Work.Coercivity.H1IP α) where
  congr := fun _f _f' _g h => Work.FTS.CoercivityFix.StepAssembly.H1IP_congr_qd α h
  add := fun f₁ f₂ g h₁ h₂ hg =>
    (H1IP_core_Q α hα).1 f₁ f₂ g h₁ h₂ hg
  dthC := fun f hf z θ hzθ =>
    Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat hf hzθ.1 hzθ.2.1 hzθ.2.2
  dzC := fun f hf z θ hzθ =>
    Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat hf hzθ.1 hzθ.2.1 hzθ.2.2

/-- **The level-`1` data of the corrected induction**, with coercivity constant `2` (the
constant of `Coer1.coer1_Lhat`) and a Cauchy–Schwarz constant independent of `α`. -/
theorem coerData2_one :
    ∃ CC : ℝ, 0 < CC ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 4) →
      CoerData2 α 1 (Work.Coercivity.H1IP α) 2 CC := by
  obtain ⟨C, hC, hcs⟩ := H1IP_cs_Q
  refine ⟨C, hC, fun α hα => ?_⟩
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 / 4 := hα.2
  exact
    { hcc := by norm_num
      hCC := hC
      cs := fun f g hf hg => hcs α hα0 f g hf hg
      coer := fun f hf =>
        Work.FTS.CoercivityFix.Coer1.coer1_Lhat α hα0 hα1 hf }

/-- **The one-sided norm comparison at every level `n ≥ 1`**, in the interior class and
with constant `1`. -/
theorem hnormD_all (α : ℝ) (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    ∀ f : Fn, RegQ α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ 1 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f)) := by
  intro f hf
  obtain ⟨hsm, hmem, _⟩ := hf
  rw [one_mul]
  exact HkSq_succ_le_Q α hα n hn hsm hmem

/-- **The `Ê₂`-slot constant in the `HkNorm` form**, uniform in `α ≥ -1/10` and depending on
the level only. -/
theorem hE2_all {α : ℝ} (hα : -(1 / 10 : ℝ) ≤ α) (n : ℕ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ f : Fn, RegQ α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
  obtain ⟨Cn, hCn, hb⟩ := E2hat_HkSq_le_uniform n
  refine ⟨Real.sqrt Cn, Real.sqrt_nonneg _, fun f hf => ?_⟩
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

end Work.FTS.CoercivityFix.Assembly
