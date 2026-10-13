/-
# `Transfer/L4Step.lean` — the joint clean/transfer induction step

`Transfer/stepT` runs one step of the paper's induction for `𝓛_Γ^T`; `Assembly.step2_data_ge`
runs one step for the clean operator `𝓛̂`.  This module composes them into a single step
(`stepPair`) and packages the per-level inputs of the transfer (`LevelPkg`).

The main theorem `Transfer.transfer_level4` (the level-`4` assembly) lives in
`Transfer/L4Main.lean`; `Transfer/level4.lean` is the aggregator.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.Instantiate
import Submission.Work.FTS.CoercivityFix.Assembly.StepReg2_all
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2_levels
import Submission.Work.FTS.CoercivityFix.Assembly.step2_data
import Submission.Work.FTS.CoercivityFix.Assembly.Main
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.CoerDataT
import Submission.Work.FTS.CoercivityFix.Transfer.stepT
import Submission.Work.FTS.CoercivityFix.Transfer.Dth_LGammaT_eq
import Submission.Work.FTS.CoercivityFix.Transfer.Dz_LGammaT_eq
import Submission.Work.FTS.CoercivityFix.Coer1T.hardyHyp_of_coerAdm
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2_succ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ CoerAdm)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The joint induction, one step.**  From the level-`n` clean data and the level-`n`
transfer data of the same `IP` with the *same* Cauchy–Schwarz constant `CC`, one obtains the
level-`(n+1)` versions, provided the smallness conditions of `step2_data_ge` and of `stepT`
hold. -/
theorem stepPair (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : n ≤ 3) (hn1 : 1 ≤ n)
    {IP : Fn → Fn → ℝ} {cc CC ccT : ℝ}
    (hcl : Work.FTS.CoercivityFix.Assembly.CoerData2 α n IP cc CC)
    (ht : CoerDataT α n IP ccT CC)
    (hc : Work.FTS.CoercivityFix.Assembly.Comm2 α n IP)
    (hcw : Work.FTS.CoercivityFix.Transfer.CommSm α n IP)
    (hcs1 : ∀ f : Fn, CoerAdm α f →
      |IP (E1 α f) (Work.Spaces.Dth f)|
        ≤ CC * Work.Spaces.HkNorm α n (E1 α f) * Work.Spaces.HkNorm α n (Work.Spaces.Dth f))
    (hcs2 : ∀ f : Fn, CoerAdm α f →
      |IP (E2 α f) (Work.Spaces.Dz f)|
        ≤ CC * Work.Spaces.HkNorm α n (E2 α f) * Work.Spaces.HkNorm α n (Work.Spaces.Dz f))
    (hreg : Work.FTS.CoercivityFix.Assembly.StepReg2 α n)
    {κE κ₁ κ₂ J : ℝ} (hκE : 0 ≤ κE) (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (hJ : 0 < J)
    (hÊ : ∀ f : Fn, RegQ α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κE * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hid1 : ∀ f : Fn, CoerAdm α f → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ + E1 α f z θ)
    (hid2 : ∀ f : Fn, CoerAdm α f → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ + E2 α f z θ)
    (hbk1 : ∀ f : Fn, CoerAdm α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (E1 α f) (Work.Spaces.Dth f))
    (hbk2 : ∀ f : Fn, CoerAdm α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (E2 α f) (Work.Spaces.Dz f))
    (hnA : ∀ f : Fn, CoerAdm α f → Work.Spaces.HkNorm α n (E1 α f)
      ≤ α * κ₁ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hnB : ∀ f : Fn, CoerAdm α f → Work.Spaces.HkNorm α n (E2 α f)
      ≤ κ₂ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hsmall : Work.FTS.CoercivityFix.StepSmall cc CC κE 1 J)
    (hs3 : J * (16 * (CC * κ₂) ^ 2) ≤ ccT * cc)
    (hs4 : J * (16 * (CC * κ₂) ^ 2) ≤ 1 * cc ^ 2)
    (hs1 : 1 * (16 * (CC * α * κ₁) ^ 2) ≤ ccT * cc)
    (hs2 : CC * α * κ₁ ≤ cc / 8) :
    0 < cc * min 1 (min 1 J) / (2 * 1) ∧
      0 < min (3 * ccT / 4) (min (5 * 1 * cc / 8) (3 * J * cc / 4)) / 1 ∧
      Work.FTS.CoercivityFix.Assembly.CoerData2 α (n + 1)
        (Work.Coercivity.HkIPStep 1 J IP) (cc * min 1 (min 1 J) / (2 * 1))
        (3 * max 1 (max 1 J) * CC) ∧
      CoerDataT α (n + 1) (Work.Coercivity.HkIPStep 1 J IP)
        (min (3 * ccT / 4) (min (5 * 1 * cc / 8) (3 * J * cc / 4)) / 1)
        (3 * max 1 (max 1 J) * CC) := by
  have hCC'pos : 0 < 3 * max 1 (max 1 J) * CC := by
    have h1 : (1 : ℝ) ≤ max 1 (max 1 J) := le_max_left _ _
    nlinarith [hcl.hCC]
  have hD : (0 : ℝ) < 1 := one_pos
  have hnormD : ∀ f : Fn, RegQ α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ 1 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f)) :=
    Work.FTS.CoercivityFix.Assembly.hnormD_all α hα hn1
  have hnormDT : ∀ f : Fn, CoerAdm α f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ 1 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f)) :=
    fun f hf => hnormD f (Work.FTS.GalerkinFix.RegQ.regQ_mono hf.reg (by omega))
  have hclean := Work.FTS.CoercivityFix.Assembly.step2_data_ge α n (by linarith) hcl hκE
    one_pos hJ hD hsmall hreg hc hÊ hnormD
  have htrans := stepT α n hα hn (ht := ht) (hcl := hcl) (hc := hcw) (hreg := hreg)
    (hid1 := hid1) (hid2 := hid2) (hbk1 := hbk1) (hbk2 := hbk2)
    (hcs1 := hcs1) (hcs2 := hcs2)
    (hn1 := hnA) (hn2 := hnB)
    (hκ₁ := hκ₁) (hκ₂ := hκ₂) (hc₁ := one_pos) (hc₂ := hJ) (hD := hD)
    (hs1 := hs1) (hs2 := hs2) (hs3 := hs3) (hs4 := hs4) (hnormD := hnormDT)
  refine ⟨hclean.hcc, htrans.hcc, ?_, ?_⟩
  · simpa only [one_mul] using hclean
  · simpa only [one_mul] using htrans


/-- **Everything the level-`n` slot of the transfer needs about the two defects**: the weakened
algebraic package `Comm2w` of the level-`n` inner product, and — for every `f ∈ CoerAdm` — the
two bundled `AddOK` inputs of `Comm2w.add` together with the two Cauchy–Schwarz bounds on the
error pairings.  These are the inputs `stepPair` consumes in place of the (refuted)
`RegQ α n (E1 α f)` / `RegQ α n (E2 α f)`. -/
def LevelPkg (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (CC : ℝ) : Prop :=
  Work.FTS.CoercivityFix.Transfer.CommSm α n IP ∧
    (∀ f : Fn, CoerAdm α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (E1 α f) (Work.Spaces.Dth f) ∧
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (E2 α f) (Work.Spaces.Dz f) ∧
      |IP (E1 α f) (Work.Spaces.Dth f)|
          ≤ CC * Work.Spaces.HkNorm α n (E1 α f) * Work.Spaces.HkNorm α n (Work.Spaces.Dth f) ∧
      |IP (E2 α f) (Work.Spaces.Dz f)|
          ≤ CC * Work.Spaces.HkNorm α n (E2 α f) * Work.Spaces.HkNorm α n (Work.Spaces.Dz f))
