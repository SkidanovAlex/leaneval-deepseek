/-
# EL nest: the self-similarity of the three arm chains (`armChain_nest`)

The three certified `b₂`-nest chains `Cert.armChainA/B/C` (`Submission/Work/ELNest/ArmChain.lean`)
pull the level-`n` arm pairs of the nest at the branch point `b₂` back to the level-`(n+1)` pairs:
each chain consists of six `armStepOf` steps, and each step feeds to `pb1Top` either the near arc
`(p.2, p.2 + arcLen p.2 p.1)` or the far arc `(p.1, p.1 + arcLen p.1 p.2)` of the current pair `p`
and takes the `T`-preimage arc with index `k ∈ {0,1}`.

This file proves the *angle* half of that statement, `armChain_nest`: with `y = 64⁻ⁿ`, the six
steps of each chain act on the affine families

* `S0(y) = (22/63 + (289/21483)y, 25/63 - (41/21483)y)`       (the level-`n` arm-`A` pair),
* `T0(y) = (25/63 + (1156/21483)y, 37/63 - (164/21483)y)`     (the level-`n` arm-`B` pair),
* `V0(y) = (37/63 + (4624/21483)y, 22/63 - (656/21483)y)`     (the level-`n` arm-`C` pair),

by replacing `y` with `y/64`; for `C` the two angles come out interchanged (the final state `S2`
is the arm-`C` state at `y/64` with its components swapped), exactly as the statement of
`armChain_nest` records.

Every quantity involved is affine in `y` and every fractional part that occurs is either a no-op
or a shift by an integer; the ten step lemmas below are the ten distinct `(near/far, k)` steps the
three chains use, each of them abstract over the chain through hypotheses on `near j` and `k j`.
The six arm angles are put in closed form in the first section, and the three chain lemmas
assemble the steps.
-/
import Mathlib
import Submission.Work.ELNest.ArmChain
import Submission.Work.ELNest.T10_armA1
import Submission.Work.ELNest.T10_armB1
import Submission.Work.ELNest.T10_armC1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

/-! ## The six arm angles in closed form

`contract t fix N = Int.fract (fix + centred (t - fix)/N)` is affine in `N = 64ⁿ` on the arm
angles: `centred (t - fix) = t - fix` for the five angles with `t - fix ∈ (-1/2, 1/2)`, while
`centred (1349/1023 - 22/63) = -656/21483` for the second arm-`C` angle, whose difference
`1349/1023 - 22/63 = 62481/64449` lies just below `1`. -/

lemma armA1_closed (n : ℕ) : armA1 n = (22:ℝ)/63 + ((289:ℝ)/21483) * ((64:ℝ)^n)⁻¹ := by
  rw [armA1, alpha1, ArmC1.contract_eq_of_centred (t := (371:ℝ)/1023) (fix := (22:ℝ)/63) (N := 64^n) (by norm_num) (by norm_num)]
  push_cast
  have h : ((371:ℝ)/1023 - 22/63) = ((289:ℝ)/21483) := by norm_num
  rw [h, Int.fract_eq_iff]
  refine ⟨?_, ?_, 0, by push_cast; ring⟩
  · have hZ0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have hd : (0:ℝ) ≤ (289:ℝ)/21483 := by norm_num
    have := mul_nonneg hd hZ0
    linarith
  · have hinv : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hd : (0:ℝ) ≤ (289:ℝ)/21483 := by norm_num
    have h2 : ((289:ℝ)/21483) * ((64:ℝ)^n)⁻¹ ≤ (289:ℝ)/21483 := mul_le_of_le_one_right hd hinv
    have hnum : (22:ℝ)/63 + 289/21483 < 1 := by norm_num
    linarith

lemma armA2_closed (n : ℕ) : armA2 n = (25:ℝ)/63 - ((41:ℝ)/21483) * ((64:ℝ)^n)⁻¹ := by
  rw [armA2, alpha2, ArmC1.contract_eq_of_centred (t := (404:ℝ)/1023) (fix := (25:ℝ)/63) (N := 64^n) (by norm_num) (by norm_num)]
  push_cast
  have h : ((404:ℝ)/1023 - 25/63) = -((41:ℝ)/21483) := by norm_num
  rw [h, Int.fract_eq_iff]
  refine ⟨?_, ?_, 0, by push_cast; ring⟩
  · have hinv : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hd : (0:ℝ) ≤ (41:ℝ)/21483 := by norm_num
    have h2 : ((41:ℝ)/21483) * ((64:ℝ)^n)⁻¹ ≤ (41:ℝ)/21483 := mul_le_of_le_one_right hd hinv
    have hnum : (0:ℝ) ≤ 25/63 - 41/21483 := by norm_num
    linarith
  · have hZ0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have hd : (0:ℝ) ≤ (41:ℝ)/21483 := by norm_num
    have hthis := mul_nonneg hd hZ0
    have hnum : (25:ℝ)/63 < 1 := by norm_num
    linarith

lemma armB1_closed (n : ℕ) : armB1 n = (25:ℝ)/63 + ((1156:ℝ)/21483) * ((64:ℝ)^n)⁻¹ := by
  rw [armB1, ArmC1.contract_eq_of_centred (t := (461:ℝ)/1023) (fix := (25:ℝ)/63) (N := 64^n) (by norm_num) (by norm_num)]
  push_cast
  have h : ((461:ℝ)/1023 - 25/63) = ((1156:ℝ)/21483) := by norm_num
  rw [h, Int.fract_eq_iff]
  refine ⟨?_, ?_, 0, by push_cast; ring⟩
  · have hZ0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have hd : (0:ℝ) ≤ (1156:ℝ)/21483 := by norm_num
    have := mul_nonneg hd hZ0
    linarith
  · have hinv : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hd : (0:ℝ) ≤ (1156:ℝ)/21483 := by norm_num
    have h2 : ((1156:ℝ)/21483) * ((64:ℝ)^n)⁻¹ ≤ (1156:ℝ)/21483 := mul_le_of_le_one_right hd hinv
    have hnum : (25:ℝ)/63 + 1156/21483 < 1 := by norm_num
    linarith

lemma armB2_closed (n : ℕ) : armB2 n = (37:ℝ)/63 - ((164:ℝ)/21483) * ((64:ℝ)^n)⁻¹ := by
  rw [armB2, ArmC1.contract_eq_of_centred (t := (593:ℝ)/1023) (fix := (37:ℝ)/63) (N := 64^n) (by norm_num) (by norm_num)]
  push_cast
  have h : ((593:ℝ)/1023 - 37/63) = -((164:ℝ)/21483) := by norm_num
  rw [h, Int.fract_eq_iff]
  refine ⟨?_, ?_, 0, by push_cast; ring⟩
  · have hinv : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hd : (0:ℝ) ≤ (164:ℝ)/21483 := by norm_num
    have h2 : ((164:ℝ)/21483) * ((64:ℝ)^n)⁻¹ ≤ (164:ℝ)/21483 := mul_le_of_le_one_right hd hinv
    have hnum : (0:ℝ) ≤ 37/63 - 164/21483 := by norm_num
    linarith
  · have hZ0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have hd : (0:ℝ) ≤ (164:ℝ)/21483 := by norm_num
    have hthis := mul_nonneg hd hZ0
    have hnum : (37:ℝ)/63 < 1 := by norm_num
    linarith

lemma armC1_closed (n : ℕ) : armC1 n = (37:ℝ)/63 + ((4624:ℝ)/21483) * ((64:ℝ)^n)⁻¹ := by
  rw [armC1, ArmC1.contract_eq_of_centred (t := (821:ℝ)/1023) (fix := (37:ℝ)/63) (N := 64^n) (by norm_num) (by norm_num)]
  push_cast
  have h : ((821:ℝ)/1023 - 37/63) = ((4624:ℝ)/21483) := by norm_num
  rw [h, Int.fract_eq_iff]
  refine ⟨?_, ?_, 0, by push_cast; ring⟩
  · have hZ0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have hd : (0:ℝ) ≤ (4624:ℝ)/21483 := by norm_num
    have := mul_nonneg hd hZ0
    linarith
  · have hinv : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hd : (0:ℝ) ≤ (4624:ℝ)/21483 := by norm_num
    have h2 : ((4624:ℝ)/21483) * ((64:ℝ)^n)⁻¹ ≤ (4624:ℝ)/21483 := mul_le_of_le_one_right hd hinv
    have hnum : (37:ℝ)/63 + 4624/21483 < 1 := by norm_num
    linarith

lemma armC2_closed (n : ℕ) : armC2 n = (22:ℝ)/63 - ((656:ℝ)/21483) * ((64:ℝ)^n)⁻¹ := by
  have hc : centred ((1349:ℝ)/1023 - 22/63) = -((656:ℝ)/21483) := by
    have h : Int.fract ((1349:ℝ)/1023 - 22/63 + 1/2) = (20171:ℝ)/42966 := by
      rw [Int.fract_eq_iff]
      exact ⟨by norm_num, by norm_num, 1, by norm_num⟩
    simp only [centred, h]
    norm_num
  rw [armC2, contract, hc]
  push_cast
  rw [Int.fract_eq_iff]
  refine ⟨?_, ?_, 0, by push_cast; ring⟩
  · have hinv : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hd : (0:ℝ) ≤ (656:ℝ)/21483 := by norm_num
    have h2 : ((656:ℝ)/21483) * ((64:ℝ)^n)⁻¹ ≤ (656:ℝ)/21483 := mul_le_of_le_one_right hd hinv
    have hnum : (0:ℝ) ≤ 22/63 - 656/21483 := by norm_num
    linarith
  · have hZ0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have hd : (0:ℝ) ≤ (656:ℝ)/21483 := by norm_num
    have hthis := mul_nonneg hd hZ0
    have hnum : (22:ℝ)/63 < 1 := by norm_num
    linarith

/-! ## The ten steps of the three chains

Every step is an elementary computation: `arcLen` is a difference, the two `Int.fract` of a step
are `x ↦ Int.fract (-x/2 + k/2)` with `k ∈ {0,1}`, and for `0 < y ≤ 1` each fractional part is a
no-op or a shift by `-1`. -/

/-- One `armStepOf` step of the certified arm chains: the state ``S0`, the level-`n` arm-`A` pair`
`(((22:ℝ)/63) + ((289:ℝ)/21483)*(y), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y))`
is sent by the near arc (`k = 1`) to the state ``S1``
`(((52:ℝ)/63) - ((289:ℝ)/42966)*(y), ((19:ℝ)/63) + ((41:ℝ)/42966)*(y))`.  Here `y` stands for `64⁻ⁿ ∈ (0,1]`. -/
lemma armStep_A0_S1 (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (hn : near j = true)
    (hk : (k j : ℝ) = 1) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armStepOf near k j (((22:ℝ)/63) + ((289:ℝ)/21483)*(y), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y))
      = (((52:ℝ)/63) - ((289:ℝ)/42966)*(y), ((19:ℝ)/63) + ((41:ℝ)/42966)*(y)) := by
  have harc : Work.EL.arcLen (((25:ℝ)/63) - ((41:ℝ)/21483)*(y)) (((22:ℝ)/63) + ((289:ℝ)/21483)*(y)) = ((20:ℝ)/21) + ((10:ℝ)/651)*(y) := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  rw [Work.ELNest.armStepOf, Work.ELNest.armArcOf, if_pos hn, hk, harc, Prod.mk.injEq]
  constructor
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- One `armStepOf` step of the certified arm chains: the state ``S1``
`(((52:ℝ)/63) - ((289:ℝ)/42966)*(y), ((19:ℝ)/63) + ((41:ℝ)/42966)*(y))`
is sent by the far arc (`k = 0`) to the state ``S2``
`(((22:ℝ)/63) - ((41:ℝ)/85932)*(y), ((37:ℝ)/63) + ((289:ℝ)/85932)*(y))`.  Here `y` stands for `64⁻ⁿ ∈ (0,1]`. -/
lemma armStep_S1_S2 (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (hn : ¬ (near j = true))
    (hk : (k j : ℝ) = 0) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armStepOf near k j (((52:ℝ)/63) - ((289:ℝ)/42966)*(y), ((19:ℝ)/63) + ((41:ℝ)/42966)*(y))
      = (((22:ℝ)/63) - ((41:ℝ)/85932)*(y), ((37:ℝ)/63) + ((289:ℝ)/85932)*(y)) := by
  have harc : Work.EL.arcLen (((52:ℝ)/63) - ((289:ℝ)/42966)*(y)) (((19:ℝ)/63) + ((41:ℝ)/42966)*(y)) = ((10:ℝ)/21) + ((5:ℝ)/651)*(y) := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  rw [Work.ELNest.armStepOf, Work.ELNest.armArcOf, if_neg hn, hk, harc, Prod.mk.injEq]
  constructor
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩

/-- One `armStepOf` step of the certified arm chains: the state ``S2``
`(((22:ℝ)/63) - ((41:ℝ)/85932)*(y), ((37:ℝ)/63) + ((289:ℝ)/85932)*(y))`
is sent by the near arc (`k = 1`) to the state ``S3``
`(((52:ℝ)/63) + ((41:ℝ)/171864)*(y), ((13:ℝ)/63) - ((289:ℝ)/171864)*(y))`.  Here `y` stands for `64⁻ⁿ ∈ (0,1]`. -/
lemma armStep_S2_S3 (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (hn : near j = true)
    (hk : (k j : ℝ) = 1) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armStepOf near k j (((22:ℝ)/63) - ((41:ℝ)/85932)*(y), ((37:ℝ)/63) + ((289:ℝ)/85932)*(y))
      = (((52:ℝ)/63) + ((41:ℝ)/171864)*(y), ((13:ℝ)/63) - ((289:ℝ)/171864)*(y)) := by
  have harc : Work.EL.arcLen (((37:ℝ)/63) + ((289:ℝ)/85932)*(y)) (((22:ℝ)/63) - ((41:ℝ)/85932)*(y)) = ((16:ℝ)/21) - ((5:ℝ)/1302)*(y) := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  rw [Work.ELNest.armStepOf, Work.ELNest.armArcOf, if_pos hn, hk, harc, Prod.mk.injEq]
  constructor
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- One `armStepOf` step of the certified arm chains: the state ``S3``
`(((52:ℝ)/63) + ((41:ℝ)/171864)*(y), ((13:ℝ)/63) - ((289:ℝ)/171864)*(y))`
is sent by the far arc (`k = 0`) to the state ``S4``
`(((25:ℝ)/63) + ((289:ℝ)/343728)*(y), ((37:ℝ)/63) - ((41:ℝ)/343728)*(y))`.  Here `y` stands for `64⁻ⁿ ∈ (0,1]`. -/
lemma armStep_S3_S4 (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (hn : ¬ (near j = true))
    (hk : (k j : ℝ) = 0) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armStepOf near k j (((52:ℝ)/63) + ((41:ℝ)/171864)*(y), ((13:ℝ)/63) - ((289:ℝ)/171864)*(y))
      = (((25:ℝ)/63) + ((289:ℝ)/343728)*(y), ((37:ℝ)/63) - ((41:ℝ)/343728)*(y)) := by
  have harc : Work.EL.arcLen (((52:ℝ)/63) + ((41:ℝ)/171864)*(y)) (((13:ℝ)/63) - ((289:ℝ)/171864)*(y)) = ((8:ℝ)/21) - ((5:ℝ)/2604)*(y) := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  rw [Work.ELNest.armStepOf, Work.ELNest.armArcOf, if_neg hn, hk, harc, Prod.mk.injEq]
  constructor
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩

/-- One `armStepOf` step of the certified arm chains: the state ``S4``
`(((25:ℝ)/63) + ((289:ℝ)/343728)*(y), ((37:ℝ)/63) - ((41:ℝ)/343728)*(y))`
is sent by the far arc (`k = 1`) to the state ``S5``
`(((13:ℝ)/63) + ((41:ℝ)/687456)*(y), ((19:ℝ)/63) - ((289:ℝ)/687456)*(y))`.  Here `y` stands for `64⁻ⁿ ∈ (0,1]`. -/
lemma armStep_S4_S5 (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (hn : ¬ (near j = true))
    (hk : (k j : ℝ) = 1) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armStepOf near k j (((25:ℝ)/63) + ((289:ℝ)/343728)*(y), ((37:ℝ)/63) - ((41:ℝ)/343728)*(y))
      = (((13:ℝ)/63) + ((41:ℝ)/687456)*(y), ((19:ℝ)/63) - ((289:ℝ)/687456)*(y)) := by
  have harc : Work.EL.arcLen (((25:ℝ)/63) + ((289:ℝ)/343728)*(y)) (((37:ℝ)/63) - ((41:ℝ)/343728)*(y)) = ((4:ℝ)/21) - ((5:ℝ)/5208)*(y) := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  rw [Work.ELNest.armStepOf, Work.ELNest.armArcOf, if_neg hn, hk, harc, Prod.mk.injEq]
  constructor
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- One `armStepOf` step of the certified arm chains: the state ``S5``
`(((13:ℝ)/63) + ((41:ℝ)/687456)*(y), ((19:ℝ)/63) - ((289:ℝ)/687456)*(y))`
is sent by the far arc (`k = 1`) to the state ``S6`, the level-`(n+1)` arm-`A` pair`
`(((22:ℝ)/63) + ((289:ℝ)/21483)*(y/64), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y/64))`.  Here `y` stands for `64⁻ⁿ ∈ (0,1]`. -/
lemma armStep_S5_A0half (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (hn : ¬ (near j = true))
    (hk : (k j : ℝ) = 1) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armStepOf near k j (((13:ℝ)/63) + ((41:ℝ)/687456)*(y), ((19:ℝ)/63) - ((289:ℝ)/687456)*(y))
      = (((22:ℝ)/63) + ((289:ℝ)/21483)*(y/64), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y/64)) := by
  have harc : Work.EL.arcLen (((13:ℝ)/63) + ((41:ℝ)/687456)*(y)) (((19:ℝ)/63) - ((289:ℝ)/687456)*(y)) = ((2:ℝ)/21) - ((5:ℝ)/10416)*(y) := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  rw [Work.ELNest.armStepOf, Work.ELNest.armArcOf, if_neg hn, hk, harc, Prod.mk.injEq]
  constructor
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- One `armStepOf` step of the certified arm chains: the state ``T0`, the level-`n` arm-`B` pair`
`(((25:ℝ)/63) + ((1156:ℝ)/21483)*(y), ((37:ℝ)/63) - ((164:ℝ)/21483)*(y))`
is sent by the far arc (`k = 1`) to the state ``U1``
`(((13:ℝ)/63) + ((82:ℝ)/21483)*(y), ((19:ℝ)/63) - ((578:ℝ)/21483)*(y))`.  Here `y` stands for `64⁻ⁿ ∈ (0,1]`. -/
lemma armStep_B0_U1 (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (hn : ¬ (near j = true))
    (hk : (k j : ℝ) = 1) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armStepOf near k j (((25:ℝ)/63) + ((1156:ℝ)/21483)*(y), ((37:ℝ)/63) - ((164:ℝ)/21483)*(y))
      = (((13:ℝ)/63) + ((82:ℝ)/21483)*(y), ((19:ℝ)/63) - ((578:ℝ)/21483)*(y)) := by
  have harc : Work.EL.arcLen (((25:ℝ)/63) + ((1156:ℝ)/21483)*(y)) (((37:ℝ)/63) - ((164:ℝ)/21483)*(y)) = ((4:ℝ)/21) - ((40:ℝ)/651)*(y) := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  rw [Work.ELNest.armStepOf, Work.ELNest.armArcOf, if_neg hn, hk, harc, Prod.mk.injEq]
  constructor
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- One `armStepOf` step of the certified arm chains: the state ``U1``
`(((13:ℝ)/63) + ((82:ℝ)/21483)*(y), ((19:ℝ)/63) - ((578:ℝ)/21483)*(y))`
is sent by the far arc (`k = 1`) to the state ``S0`, the level-`n` arm-`A` pair`
`(((22:ℝ)/63) + ((289:ℝ)/21483)*(y), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y))`.  Here `y` stands for `64⁻ⁿ ∈ (0,1]`. -/
lemma armStep_U1_A0 (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (hn : ¬ (near j = true))
    (hk : (k j : ℝ) = 1) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armStepOf near k j (((13:ℝ)/63) + ((82:ℝ)/21483)*(y), ((19:ℝ)/63) - ((578:ℝ)/21483)*(y))
      = (((22:ℝ)/63) + ((289:ℝ)/21483)*(y), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y)) := by
  have harc : Work.EL.arcLen (((13:ℝ)/63) + ((82:ℝ)/21483)*(y)) (((19:ℝ)/63) - ((578:ℝ)/21483)*(y)) = ((2:ℝ)/21) - ((20:ℝ)/651)*(y) := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  rw [Work.ELNest.armStepOf, Work.ELNest.armArcOf, if_neg hn, hk, harc, Prod.mk.injEq]
  constructor
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- One `armStepOf` step of the certified arm chains: the state ``V0`, the level-`n` arm-`C` pair`
`(((37:ℝ)/63) + ((4624:ℝ)/21483)*(y), ((22:ℝ)/63) - ((656:ℝ)/21483)*(y))`
is sent by the far arc (`k = 1`) to the state ``V1``
`(((52:ℝ)/63) + ((328:ℝ)/21483)*(y), ((13:ℝ)/63) - ((2312:ℝ)/21483)*(y))`.  Here `y` stands for `64⁻ⁿ ∈ (0,1]`. -/
lemma armStep_C0_V1 (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (hn : ¬ (near j = true))
    (hk : (k j : ℝ) = 1) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armStepOf near k j (((37:ℝ)/63) + ((4624:ℝ)/21483)*(y), ((22:ℝ)/63) - ((656:ℝ)/21483)*(y))
      = (((52:ℝ)/63) + ((328:ℝ)/21483)*(y), ((13:ℝ)/63) - ((2312:ℝ)/21483)*(y)) := by
  have harc : Work.EL.arcLen (((37:ℝ)/63) + ((4624:ℝ)/21483)*(y)) (((22:ℝ)/63) - ((656:ℝ)/21483)*(y)) = ((16:ℝ)/21) - ((160:ℝ)/651)*(y) := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  rw [Work.ELNest.armStepOf, Work.ELNest.armArcOf, if_neg hn, hk, harc, Prod.mk.injEq]
  constructor
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- One `armStepOf` step of the certified arm chains: the state ``V1``
`(((52:ℝ)/63) + ((328:ℝ)/21483)*(y), ((13:ℝ)/63) - ((2312:ℝ)/21483)*(y))`
is sent by the far arc (`k = 0`) to the state ``T0`, the level-`n` arm-`B` pair`
`(((25:ℝ)/63) + ((1156:ℝ)/21483)*(y), ((37:ℝ)/63) - ((164:ℝ)/21483)*(y))`.  Here `y` stands for `64⁻ⁿ ∈ (0,1]`. -/
lemma armStep_V1_B0 (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (hn : ¬ (near j = true))
    (hk : (k j : ℝ) = 0) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armStepOf near k j (((52:ℝ)/63) + ((328:ℝ)/21483)*(y), ((13:ℝ)/63) - ((2312:ℝ)/21483)*(y))
      = (((25:ℝ)/63) + ((1156:ℝ)/21483)*(y), ((37:ℝ)/63) - ((164:ℝ)/21483)*(y)) := by
  have harc : Work.EL.arcLen (((52:ℝ)/63) + ((328:ℝ)/21483)*(y)) (((13:ℝ)/63) - ((2312:ℝ)/21483)*(y)) = ((8:ℝ)/21) - ((80:ℝ)/651)*(y) := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  rw [Work.ELNest.armStepOf, Work.ELNest.armArcOf, if_neg hn, hk, harc, Prod.mk.injEq]
  constructor
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩

/-! ## Conversion helpers

`S4` is the arm-`B` state at level `n+1`, and `S2` is the arm-`C` state at level `n+1` with its
two angles interchanged. -/

/-- The successor relation `64^{-(n+1)} = 64⁻ⁿ/64`. -/
lemma inv_pow_succ_64 (n : ℕ) : ((64:ℝ)^(n+1))⁻¹ = ((64:ℝ)^n)⁻¹ / 64 := by
  rw [pow_succ, mul_inv, div_eq_mul_inv]

/-- The state `S4` is the arm-`B` state at level `n+1`: the two descriptions differ by the
rational identities `289/343728 = (1156/21483)/64` and `41/343728 = (164/21483)/64`. -/
lemma S4_eq_B0_div (y : ℝ) : (((25:ℝ)/63) + ((289:ℝ)/343728)*(y), ((37:ℝ)/63) - ((41:ℝ)/343728)*(y)) = (((25:ℝ)/63) + ((1156:ℝ)/21483)*(y/64), ((37:ℝ)/63) - ((164:ℝ)/21483)*(y/64)) := by
  rw [Prod.mk.injEq]
  constructor <;> ring

/-- The state `S2` is the arm-`C` state at level `n+1`, with the two angles interchanged:
`S2 = (22/63 - (41/85932)y, 37/63 + (289/85932)y)` and the swapped arm-`C` state at `y/64` is
`(22/63 - (656/21483)(y/64), 37/63 + (4624/21483)(y/64))`. -/
lemma S2_eq_C0_div_swap (y : ℝ) : (((22:ℝ)/63) - ((41:ℝ)/85932)*(y), ((37:ℝ)/63) + ((289:ℝ)/85932)*(y)) = (((22:ℝ)/63) - ((656:ℝ)/21483)*(y/64), ((37:ℝ)/63) + ((4624:ℝ)/21483)*(y/64)) := by
  rw [Prod.mk.injEq]
  constructor <;> ring

/-! ## The three chains

Each chain is the six-fold iterate of `armStepOf` along the symbols of `nearX`/`kX`, applied to
the level-`n` pair of that arm; the six steps multiply `y = 64⁻ⁿ` by `1/64`. -/

/-- **The six-step A chain, affine in `y = 64⁻ⁿ`.**  The six steps of the certified
A chain send the level-`n` pair `(((22:ℝ)/63) + ((289:ℝ)/21483)*(y), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y))` to `(((22:ℝ)/63) + ((289:ℝ)/21483)*(y/64), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y/64))`. -/
lemma armChainA_affine (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA
        (((22:ℝ)/63) + ((289:ℝ)/21483)*(y), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y)) 6
      = (((22:ℝ)/63) + ((289:ℝ)/21483)*(y/64), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y/64)) := by
  change Work.ELNest.armStepOf Work.ELNest.nearA Work.ELNest.kA 0
      (Work.ELNest.armStepOf Work.ELNest.nearA Work.ELNest.kA 1
      (Work.ELNest.armStepOf Work.ELNest.nearA Work.ELNest.kA 2
      (Work.ELNest.armStepOf Work.ELNest.nearA Work.ELNest.kA 3
      (Work.ELNest.armStepOf Work.ELNest.nearA Work.ELNest.kA 4
      (Work.ELNest.armStepOf Work.ELNest.nearA Work.ELNest.kA 5
      ((((22:ℝ)/63) + ((289:ℝ)/21483)*(y), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y))))))))
      = (((22:ℝ)/63) + ((289:ℝ)/21483)*(y/64), ((25:ℝ)/63) - ((41:ℝ)/21483)*(y/64))
  rw [      armStep_A0_S1 Work.ELNest.nearA Work.ELNest.kA 5 (by decide) (by norm_num [Work.ELNest.kA]) y hy hy1,
      armStep_S1_S2 Work.ELNest.nearA Work.ELNest.kA 4 (by decide) (by norm_num [Work.ELNest.kA]) y hy hy1,
      armStep_S2_S3 Work.ELNest.nearA Work.ELNest.kA 3 (by decide) (by norm_num [Work.ELNest.kA]) y hy hy1,
      armStep_S3_S4 Work.ELNest.nearA Work.ELNest.kA 2 (by decide) (by norm_num [Work.ELNest.kA]) y hy hy1,
      armStep_S4_S5 Work.ELNest.nearA Work.ELNest.kA 1 (by decide) (by norm_num [Work.ELNest.kA]) y hy hy1,
      armStep_S5_A0half Work.ELNest.nearA Work.ELNest.kA 0 (by decide) (by norm_num [Work.ELNest.kA]) y hy hy1]

/-- **The six-step B chain, affine in `y = 64⁻ⁿ`.**  The six steps of the certified
B chain send the level-`n` pair `(((25:ℝ)/63) + ((1156:ℝ)/21483)*(y), ((37:ℝ)/63) - ((164:ℝ)/21483)*(y))` to `(((25:ℝ)/63) + ((1156:ℝ)/21483)*(y/64), ((37:ℝ)/63) - ((164:ℝ)/21483)*(y/64))`. -/
lemma armChainB_affine (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB
        (((25:ℝ)/63) + ((1156:ℝ)/21483)*(y), ((37:ℝ)/63) - ((164:ℝ)/21483)*(y)) 6
      = (((25:ℝ)/63) + ((1156:ℝ)/21483)*(y/64), ((37:ℝ)/63) - ((164:ℝ)/21483)*(y/64)) := by
  change Work.ELNest.armStepOf Work.ELNest.nearB Work.ELNest.kB 0
      (Work.ELNest.armStepOf Work.ELNest.nearB Work.ELNest.kB 1
      (Work.ELNest.armStepOf Work.ELNest.nearB Work.ELNest.kB 2
      (Work.ELNest.armStepOf Work.ELNest.nearB Work.ELNest.kB 3
      (Work.ELNest.armStepOf Work.ELNest.nearB Work.ELNest.kB 4
      (Work.ELNest.armStepOf Work.ELNest.nearB Work.ELNest.kB 5
      ((((25:ℝ)/63) + ((1156:ℝ)/21483)*(y), ((37:ℝ)/63) - ((164:ℝ)/21483)*(y))))))))
      = (((25:ℝ)/63) + ((1156:ℝ)/21483)*(y/64), ((37:ℝ)/63) - ((164:ℝ)/21483)*(y/64))
  rw [      armStep_B0_U1 Work.ELNest.nearB Work.ELNest.kB 5 (by decide) (by norm_num [Work.ELNest.kB]) y hy hy1,
      armStep_U1_A0 Work.ELNest.nearB Work.ELNest.kB 4 (by decide) (by norm_num [Work.ELNest.kB]) y hy hy1,
      armStep_A0_S1 Work.ELNest.nearB Work.ELNest.kB 3 (by decide) (by norm_num [Work.ELNest.kB]) y hy hy1,
      armStep_S1_S2 Work.ELNest.nearB Work.ELNest.kB 2 (by decide) (by norm_num [Work.ELNest.kB]) y hy hy1,
      armStep_S2_S3 Work.ELNest.nearB Work.ELNest.kB 1 (by decide) (by norm_num [Work.ELNest.kB]) y hy hy1,
      armStep_S3_S4 Work.ELNest.nearB Work.ELNest.kB 0 (by decide) (by norm_num [Work.ELNest.kB]) y hy hy1,
      S4_eq_B0_div y]

/-- **The six-step C chain, affine in `y = 64⁻ⁿ`.**  The six steps of the certified
C chain send the level-`n` pair `(((37:ℝ)/63) + ((4624:ℝ)/21483)*(y), ((22:ℝ)/63) - ((656:ℝ)/21483)*(y))` to `(((22:ℝ)/63) - ((656:ℝ)/21483)*(y/64), ((37:ℝ)/63) + ((4624:ℝ)/21483)*(y/64))`. -/
lemma armChainC_affine (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC
        (((37:ℝ)/63) + ((4624:ℝ)/21483)*(y), ((22:ℝ)/63) - ((656:ℝ)/21483)*(y)) 6
      = (((22:ℝ)/63) - ((656:ℝ)/21483)*(y/64), ((37:ℝ)/63) + ((4624:ℝ)/21483)*(y/64)) := by
  change Work.ELNest.armStepOf Work.ELNest.nearC Work.ELNest.kC 0
      (Work.ELNest.armStepOf Work.ELNest.nearC Work.ELNest.kC 1
      (Work.ELNest.armStepOf Work.ELNest.nearC Work.ELNest.kC 2
      (Work.ELNest.armStepOf Work.ELNest.nearC Work.ELNest.kC 3
      (Work.ELNest.armStepOf Work.ELNest.nearC Work.ELNest.kC 4
      (Work.ELNest.armStepOf Work.ELNest.nearC Work.ELNest.kC 5
      ((((37:ℝ)/63) + ((4624:ℝ)/21483)*(y), ((22:ℝ)/63) - ((656:ℝ)/21483)*(y))))))))
      = (((22:ℝ)/63) - ((656:ℝ)/21483)*(y/64), ((37:ℝ)/63) + ((4624:ℝ)/21483)*(y/64))
  rw [      armStep_C0_V1 Work.ELNest.nearC Work.ELNest.kC 5 (by decide) (by norm_num [Work.ELNest.kC]) y hy hy1,
      armStep_V1_B0 Work.ELNest.nearC Work.ELNest.kC 4 (by decide) (by norm_num [Work.ELNest.kC]) y hy hy1,
      armStep_B0_U1 Work.ELNest.nearC Work.ELNest.kC 3 (by decide) (by norm_num [Work.ELNest.kC]) y hy hy1,
      armStep_U1_A0 Work.ELNest.nearC Work.ELNest.kC 2 (by decide) (by norm_num [Work.ELNest.kC]) y hy hy1,
      armStep_A0_S1 Work.ELNest.nearC Work.ELNest.kC 1 (by decide) (by norm_num [Work.ELNest.kC]) y hy hy1,
      armStep_S1_S2 Work.ELNest.nearC Work.ELNest.kC 0 (by decide) (by norm_num [Work.ELNest.kC]) y hy hy1,
      S2_eq_C0_div_swap y]
/-! ## The statement -/

theorem armChain_nest (n : ℕ) :
    Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA
        (Work.ELNest.armA1 n, Work.ELNest.armA2 n) 6
      = (Work.ELNest.armA1 (n + 1), Work.ELNest.armA2 (n + 1)) ∧
    Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB
        (Work.ELNest.armB1 n, Work.ELNest.armB2 n) 6
      = (Work.ELNest.armB1 (n + 1), Work.ELNest.armB2 (n + 1)) ∧
    Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC
        (Work.ELNest.armC1 n, Work.ELNest.armC2 n) 6
      = (Work.ELNest.armC2 (n + 1), Work.ELNest.armC1 (n + 1)) := by
  have hy : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [show (Work.ELNest.armA1 n, Work.ELNest.armA2 n) = (((22:ℝ)/63) + ((289:ℝ)/21483)*(((64:ℝ)^n)⁻¹), ((25:ℝ)/63) - ((41:ℝ)/21483)*(((64:ℝ)^n)⁻¹)) from by
          rw [armA1_closed n, armA2_closed n],
        armChainA_affine ((64:ℝ)^n)⁻¹ hy hy1,
        show (Work.ELNest.armA1 (n + 1), Work.ELNest.armA2 (n + 1)) = (((22:ℝ)/63) + ((289:ℝ)/21483)*(((64:ℝ)^n)⁻¹/64), ((25:ℝ)/63) - ((41:ℝ)/21483)*(((64:ℝ)^n)⁻¹/64)) from by
          rw [armA1_closed (n + 1), armA2_closed (n + 1), inv_pow_succ_64 n]]
  · rw [show (Work.ELNest.armB1 n, Work.ELNest.armB2 n) = (((25:ℝ)/63) + ((1156:ℝ)/21483)*(((64:ℝ)^n)⁻¹), ((37:ℝ)/63) - ((164:ℝ)/21483)*(((64:ℝ)^n)⁻¹)) from by
          rw [armB1_closed n, armB2_closed n],
        armChainB_affine ((64:ℝ)^n)⁻¹ hy hy1,
        show (Work.ELNest.armB1 (n + 1), Work.ELNest.armB2 (n + 1)) = (((25:ℝ)/63) + ((1156:ℝ)/21483)*(((64:ℝ)^n)⁻¹/64), ((37:ℝ)/63) - ((164:ℝ)/21483)*(((64:ℝ)^n)⁻¹/64)) from by
          rw [armB1_closed (n + 1), armB2_closed (n + 1), inv_pow_succ_64 n]]
  · rw [show (Work.ELNest.armC1 n, Work.ELNest.armC2 n) = (((37:ℝ)/63) + ((4624:ℝ)/21483)*(((64:ℝ)^n)⁻¹), ((22:ℝ)/63) - ((656:ℝ)/21483)*(((64:ℝ)^n)⁻¹)) from by
          rw [armC1_closed n, armC2_closed n],
        armChainC_affine ((64:ℝ)^n)⁻¹ hy hy1,
        show (Work.ELNest.armC2 (n + 1), Work.ELNest.armC1 (n + 1)) = (((22:ℝ)/63) - ((656:ℝ)/21483)*(((64:ℝ)^n)⁻¹/64), ((37:ℝ)/63) + ((4624:ℝ)/21483)*(((64:ℝ)^n)⁻¹/64)) from by
          rw [armC2_closed (n + 1), armC1_closed (n + 1), inv_pow_succ_64 n]]

end Work.ELNest

