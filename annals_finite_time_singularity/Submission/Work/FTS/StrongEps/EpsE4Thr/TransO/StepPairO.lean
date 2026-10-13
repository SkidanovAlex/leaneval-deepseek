/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/TransO/StepPairO.lean` — the joint clean/transfer step, on the **open** class

`CoercivityFix/Transfer/L4Step.stepPair` composes the clean induction step
(`Assembly.step2_data_ge`) and the transfer induction step (`Transfer.stepT`) into a single step
that climbs both the clean data `CoerData2` and the transfer data `CoerDataT` at the same `IP`.

This module is the open-class twin: `Assembly.step2_data_ge → TransO.step2_data_ge_O`,
`Transfer.stepT → TransO.stepT_O`, and the class `CoerAdm → CoerAdmO` throughout (with
`CoerData2 → CoerData2O`, `CoerDataTO` and `StepReg2O`).  The pairing `IP`, the constants and the
smallness conditions are unchanged.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.StepTO
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.DefsO
import Submission.Work.FTS.StrongEps.EpsE4Thr.step2_data_ge_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.StepDataO
import Submission.Work.FTS.StrongEps.EpsE4Thr.StepReg2_all_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.Comm2_L1_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.Comm2_succ_O

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongEps.EpsE4Thr (CoerAdmO CoerData2O CoerDataTO RegQo StepReg2O Comm2O
  hnormD_all_O)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **The joint induction, one step, on the open class.**  From the level-`n` clean data and the
level-`n` transfer data of the same `IP` with the *same* Cauchy–Schwarz constant `CC`, one obtains
the level-`(n+1)` versions, provided the smallness conditions of `step2_data_ge_O` and of
`stepT_O` hold. -/
theorem stepPair_O (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : n ≤ 3) (hn1 : 1 ≤ n)
    {IP : Fn → Fn → ℝ} {cc CC ccT : ℝ}
    (hcl : CoerData2O α n IP cc CC)
    (ht : CoerDataTO α n IP ccT CC)
    (hc : Comm2O α n IP)
    (hcw : Work.FTS.CoercivityFix.Transfer.CommSm α n IP)
    (hcs1 : ∀ f : Fn, CoerAdmO α f →
      |IP (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f)|
        ≤ CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dth f))
    (hcs2 : ∀ f : Fn, CoerAdmO α f →
      |IP (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f)|
        ≤ CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dz f))
    (hreg : StepReg2O α n)
    {κE κ₁ κ₂ J : ℝ} (hκE : 0 ≤ κE) (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (hJ : 0 < J)
    (hÊ : ∀ f : Fn, RegQo α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κE * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hid1 : ∀ f : Fn, CoerAdmO α f → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
          + Work.FTS.CoercivityFix.Transfer.E1 α f z θ)
    (hid2 : ∀ f : Fn, CoerAdmO α f → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
          + Work.FTS.CoercivityFix.Transfer.E2 α f z θ)
    (hbk1 : ∀ f : Fn, CoerAdmO α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
        (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f))
    (hbk2 : ∀ f : Fn, CoerAdmO α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
        (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f))
    (hnA : ∀ f : Fn, CoerAdmO α f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
        ≤ α * κ₁ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hnB : ∀ f : Fn, CoerAdmO α f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
        ≤ κ₂ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hsmall : Work.FTS.CoercivityFix.StepSmall cc CC κE 1 J)
    (hs3 : J * (16 * (CC * κ₂) ^ 2) ≤ ccT * cc)
    (hs4 : J * (16 * (CC * κ₂) ^ 2) ≤ 1 * cc ^ 2)
    (hs1 : 1 * (16 * (CC * α * κ₁) ^ 2) ≤ ccT * cc)
    (hs2 : CC * α * κ₁ ≤ cc / 8) :
    0 < cc * min 1 (min 1 J) / (2 * 1) ∧
      0 < min (3 * ccT / 4) (min (5 * 1 * cc / 8) (3 * J * cc / 4)) / 1 ∧
      CoerData2O α (n + 1)
        (Work.Coercivity.HkIPStep 1 J IP) (cc * min 1 (min 1 J) / (2 * 1))
        (3 * max 1 (max 1 J) * CC) ∧
      CoerDataTO α (n + 1) (Work.Coercivity.HkIPStep 1 J IP)
        (min (3 * ccT / 4) (min (5 * 1 * cc / 8) (3 * J * cc / 4)) / 1)
        (3 * max 1 (max 1 J) * CC) := by
  have hD : (0 : ℝ) < 1 := one_pos
  have hnormD : ∀ f : Fn, RegQo α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ 1 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f)) :=
    hnormD_all_O α hα hn1
  have hnormDT : ∀ f : Fn, CoerAdmO α f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ 1 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f)) :=
    fun f hf => hnormD f (regQo_mono (k := n + 1) (l := 5) (by omega) hf.1)
  have hclean := Work.FTS.StrongEps.EpsE4Thr.step2_data_ge_O α n hα hcl hκE one_pos hJ hD
    hsmall hreg hc hÊ hnormD
  have htrans := stepT_O α n hα hn (ht := ht) (hcl := hcl) (hc := hcw) (hreg := hreg)
    (hid1 := hid1) (hid2 := hid2) (hbk1 := hbk1) (hbk2 := hbk2)
    (hcs1 := hcs1) (hcs2 := hcs2)
    (hn1 := hnA) (hn2 := hnB)
    (hκ₁ := hκ₁) (hκ₂ := hκ₂) (hc₁ := one_pos) (hc₂ := hJ) (hD := hD)
    (hs1 := hs1) (hs2 := hs2) (hs3 := hs3) (hs4 := hs4) (hnormD := hnormDT)
  refine ⟨hclean.hcc, htrans.hcc, ?_, ?_⟩
  · simpa only [one_mul] using hclean
  · simpa only [one_mul] using htrans

end Work.FTS.StrongEps.EpsE4Thr.TransO
