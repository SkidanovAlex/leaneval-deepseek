/-
# EL nest: the self-similarity of the angle formulas (`nestPair_nest`)

The pair of rays of the `z₁`-nest at level `n` has angles
`(βₙ, βₙ') = (bAng n, bAng' n)`, and the nest is self-similar: the ten steps of the
nest chain (`Work.ELNest.nestPair`, one `pb1Top` application per step) send the level-`n`
pair to the level-`(n+1)` pair.  With

    bAng n  = α₁ − (α₁ − β₀)/1024ⁿ,      bAng' n = α₂ + (β₀' − α₂)/1024ⁿ,

both angles are affine in `y = 1024⁻ⁿ`, and every one of the ten steps is an elementary
computation: `arcLen` is a difference, the two `Int.fract` of the step are `x ↦ fract(-x/2+k/2)`
with `k ∈ {0,1}`, and for `0 < y ≤ 1` every fractional part involved is a no-op (`z = 0`) or
a shift by `-1` (`z = -1`).  The result is again affine in `y`, with the same coefficients
scaled by `1/1024`.

All the constants of the computation are held in this file; the ten steps appear as the ten
lemmas `nestStep_9, …, nestStep_0` (in the order in which `nestPair` applies them), assembled
in `nestPair_affine` and specialised to `y = 1024⁻ⁿ` in the main theorem.
-/
import Mathlib
import Submission.Work.ELNest.Chain
import Submission.Work.ELNest.bAng_nest_arc
import Submission.Work.ELNest.T_iterate_bAng

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

/-! ## The ten steps of the nest chain, with the level-`n` angles affine in `y = 1024⁻ⁿ` -/

/-- Step `9` of the nest chain: the pair `(((371:ℝ)/1023) - ((15:ℝ)/349184)*y, ((404:ℝ)/1023) + ((139:ℝ)/349184)*y)`
maps to the pair `(((326:ℝ)/1023) + ((15:ℝ)/698368)*y, ((821:ℝ)/1023) - ((139:ℝ)/698368)*y)` of the next level of the chain.
(The branch used is `the near arc (p.2, p.2 + arcLen p.2 p.1)`
and `k = 0`.) -/
lemma nestStep_9 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.nestStep 9 (((371:ℝ)/1023) - ((15:ℝ)/349184)*y, ((404:ℝ)/1023) + ((139:ℝ)/349184)*y)
      = (((326:ℝ)/1023) + ((15:ℝ)/698368)*y, ((821:ℝ)/1023) - ((139:ℝ)/698368)*y) := by
  have harc : arcLen (((404:ℝ)/1023) + ((139:ℝ)/349184)*y) (((371:ℝ)/1023) - ((15:ℝ)/349184)*y) = ((30:ℝ)/31) - ((7:ℝ)/15872)*y := by
    rw [arcLen, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  unfold Work.ELNest.nestStep Work.ELNest.nestArc Work.ELNest.nestK
  norm_num
  rw [harc]
  constructor
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩

/-- Step `8` of the nest chain: the pair `(((326:ℝ)/1023) + ((15:ℝ)/698368)*y, ((821:ℝ)/1023) - ((139:ℝ)/698368)*y)`
maps to the pair `(((860:ℝ)/1023) - ((15:ℝ)/1396736)*y, ((101:ℝ)/1023) + ((139:ℝ)/1396736)*y)` of the next level of the chain.
(The branch used is `the near arc (p.2, p.2 + arcLen p.2 p.1)`
and `k = 1`.) -/
lemma nestStep_8 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.nestStep 8 (((326:ℝ)/1023) + ((15:ℝ)/698368)*y, ((821:ℝ)/1023) - ((139:ℝ)/698368)*y)
      = (((860:ℝ)/1023) - ((15:ℝ)/1396736)*y, ((101:ℝ)/1023) + ((139:ℝ)/1396736)*y) := by
  have harc : arcLen (((821:ℝ)/1023) - ((139:ℝ)/698368)*y) (((326:ℝ)/1023) + ((15:ℝ)/698368)*y) = ((16:ℝ)/31) + ((7:ℝ)/31744)*y := by
    rw [arcLen, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  unfold Work.ELNest.nestStep Work.ELNest.nestArc Work.ELNest.nestK
  norm_num
  rw [harc]
  constructor
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- Step `7` of the nest chain: the pair `(((860:ℝ)/1023) - ((15:ℝ)/1396736)*y, ((101:ℝ)/1023) + ((139:ℝ)/1396736)*y)`
maps to the pair `(((461:ℝ)/1023) - ((139:ℝ)/2793472)*y, ((593:ℝ)/1023) + ((15:ℝ)/2793472)*y)` of the next level of the chain.
(The branch used is `the far arc (p.1, p.1 + arcLen p.1 p.2)`
and `k = 0`.) -/
lemma nestStep_7 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.nestStep 7 (((860:ℝ)/1023) - ((15:ℝ)/1396736)*y, ((101:ℝ)/1023) + ((139:ℝ)/1396736)*y)
      = (((461:ℝ)/1023) - ((139:ℝ)/2793472)*y, ((593:ℝ)/1023) + ((15:ℝ)/2793472)*y) := by
  have harc : arcLen (((860:ℝ)/1023) - ((15:ℝ)/1396736)*y) (((101:ℝ)/1023) + ((139:ℝ)/1396736)*y) = ((8:ℝ)/31) + ((7:ℝ)/63488)*y := by
    rw [arcLen, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  unfold Work.ELNest.nestStep Work.ELNest.nestArc Work.ELNest.nestK
  norm_num
  rw [harc]
  constructor
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩

/-- Step `6` of the nest chain: the pair `(((461:ℝ)/1023) - ((139:ℝ)/2793472)*y, ((593:ℝ)/1023) + ((15:ℝ)/2793472)*y)`
maps to the pair `(((215:ℝ)/1023) - ((15:ℝ)/5586944)*y, ((281:ℝ)/1023) + ((139:ℝ)/5586944)*y)` of the next level of the chain.
(The branch used is `the far arc (p.1, p.1 + arcLen p.1 p.2)`
and `k = 1`.) -/
lemma nestStep_6 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.nestStep 6 (((461:ℝ)/1023) - ((139:ℝ)/2793472)*y, ((593:ℝ)/1023) + ((15:ℝ)/2793472)*y)
      = (((215:ℝ)/1023) - ((15:ℝ)/5586944)*y, ((281:ℝ)/1023) + ((139:ℝ)/5586944)*y) := by
  have harc : arcLen (((461:ℝ)/1023) - ((139:ℝ)/2793472)*y) (((593:ℝ)/1023) + ((15:ℝ)/2793472)*y) = ((4:ℝ)/31) + ((7:ℝ)/126976)*y := by
    rw [arcLen, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  unfold Work.ELNest.nestStep Work.ELNest.nestArc Work.ELNest.nestK
  norm_num
  rw [harc]
  constructor
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- Step `5` of the nest chain: the pair `(((215:ℝ)/1023) - ((15:ℝ)/5586944)*y, ((281:ℝ)/1023) + ((139:ℝ)/5586944)*y)`
maps to the pair `(((371:ℝ)/1023) - ((139:ℝ)/11173888)*y, ((404:ℝ)/1023) + ((15:ℝ)/11173888)*y)` of the next level of the chain.
(The branch used is `the far arc (p.1, p.1 + arcLen p.1 p.2)`
and `k = 1`.) -/
lemma nestStep_5 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.nestStep 5 (((215:ℝ)/1023) - ((15:ℝ)/5586944)*y, ((281:ℝ)/1023) + ((139:ℝ)/5586944)*y)
      = (((371:ℝ)/1023) - ((139:ℝ)/11173888)*y, ((404:ℝ)/1023) + ((15:ℝ)/11173888)*y) := by
  have harc : arcLen (((215:ℝ)/1023) - ((15:ℝ)/5586944)*y) (((281:ℝ)/1023) + ((139:ℝ)/5586944)*y) = ((2:ℝ)/31) + ((7:ℝ)/253952)*y := by
    rw [arcLen, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  unfold Work.ELNest.nestStep Work.ELNest.nestArc Work.ELNest.nestK
  norm_num
  rw [harc]
  constructor
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- Step `4` of the nest chain: the pair `(((371:ℝ)/1023) - ((139:ℝ)/11173888)*y, ((404:ℝ)/1023) + ((15:ℝ)/11173888)*y)`
maps to the pair `(((326:ℝ)/1023) + ((139:ℝ)/22347776)*y, ((821:ℝ)/1023) - ((15:ℝ)/22347776)*y)` of the next level of the chain.
(The branch used is `the near arc (p.2, p.2 + arcLen p.2 p.1)`
and `k = 0`.) -/
lemma nestStep_4 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.nestStep 4 (((371:ℝ)/1023) - ((139:ℝ)/11173888)*y, ((404:ℝ)/1023) + ((15:ℝ)/11173888)*y)
      = (((326:ℝ)/1023) + ((139:ℝ)/22347776)*y, ((821:ℝ)/1023) - ((15:ℝ)/22347776)*y) := by
  have harc : arcLen (((404:ℝ)/1023) + ((15:ℝ)/11173888)*y) (((371:ℝ)/1023) - ((139:ℝ)/11173888)*y) = ((30:ℝ)/31) - ((7:ℝ)/507904)*y := by
    rw [arcLen, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  unfold Work.ELNest.nestStep Work.ELNest.nestArc Work.ELNest.nestK
  norm_num
  rw [harc]
  constructor
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩

/-- Step `3` of the nest chain: the pair `(((326:ℝ)/1023) + ((139:ℝ)/22347776)*y, ((821:ℝ)/1023) - ((15:ℝ)/22347776)*y)`
maps to the pair `(((860:ℝ)/1023) - ((139:ℝ)/44695552)*y, ((101:ℝ)/1023) + ((15:ℝ)/44695552)*y)` of the next level of the chain.
(The branch used is `the near arc (p.2, p.2 + arcLen p.2 p.1)`
and `k = 1`.) -/
lemma nestStep_3 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.nestStep 3 (((326:ℝ)/1023) + ((139:ℝ)/22347776)*y, ((821:ℝ)/1023) - ((15:ℝ)/22347776)*y)
      = (((860:ℝ)/1023) - ((139:ℝ)/44695552)*y, ((101:ℝ)/1023) + ((15:ℝ)/44695552)*y) := by
  have harc : arcLen (((821:ℝ)/1023) - ((15:ℝ)/22347776)*y) (((326:ℝ)/1023) + ((139:ℝ)/22347776)*y) = ((16:ℝ)/31) + ((7:ℝ)/1015808)*y := by
    rw [arcLen, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  unfold Work.ELNest.nestStep Work.ELNest.nestArc Work.ELNest.nestK
  norm_num
  rw [harc]
  constructor
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- Step `2` of the nest chain: the pair `(((860:ℝ)/1023) - ((139:ℝ)/44695552)*y, ((101:ℝ)/1023) + ((15:ℝ)/44695552)*y)`
maps to the pair `(((461:ℝ)/1023) - ((15:ℝ)/89391104)*y, ((593:ℝ)/1023) + ((139:ℝ)/89391104)*y)` of the next level of the chain.
(The branch used is `the far arc (p.1, p.1 + arcLen p.1 p.2)`
and `k = 0`.) -/
lemma nestStep_2 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.nestStep 2 (((860:ℝ)/1023) - ((139:ℝ)/44695552)*y, ((101:ℝ)/1023) + ((15:ℝ)/44695552)*y)
      = (((461:ℝ)/1023) - ((15:ℝ)/89391104)*y, ((593:ℝ)/1023) + ((139:ℝ)/89391104)*y) := by
  have harc : arcLen (((860:ℝ)/1023) - ((139:ℝ)/44695552)*y) (((101:ℝ)/1023) + ((15:ℝ)/44695552)*y) = ((8:ℝ)/31) + ((7:ℝ)/2031616)*y := by
    rw [arcLen, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  unfold Work.ELNest.nestStep Work.ELNest.nestArc Work.ELNest.nestK
  norm_num
  rw [harc]
  constructor
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩

/-- Step `1` of the nest chain: the pair `(((461:ℝ)/1023) - ((15:ℝ)/89391104)*y, ((593:ℝ)/1023) + ((139:ℝ)/89391104)*y)`
maps to the pair `(((215:ℝ)/1023) - ((139:ℝ)/178782208)*y, ((281:ℝ)/1023) + ((15:ℝ)/178782208)*y)` of the next level of the chain.
(The branch used is `the far arc (p.1, p.1 + arcLen p.1 p.2)`
and `k = 1`.) -/
lemma nestStep_1 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.nestStep 1 (((461:ℝ)/1023) - ((15:ℝ)/89391104)*y, ((593:ℝ)/1023) + ((139:ℝ)/89391104)*y)
      = (((215:ℝ)/1023) - ((139:ℝ)/178782208)*y, ((281:ℝ)/1023) + ((15:ℝ)/178782208)*y) := by
  have harc : arcLen (((461:ℝ)/1023) - ((15:ℝ)/89391104)*y) (((593:ℝ)/1023) + ((139:ℝ)/89391104)*y) = ((4:ℝ)/31) + ((7:ℝ)/4063232)*y := by
    rw [arcLen, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  unfold Work.ELNest.nestStep Work.ELNest.nestArc Work.ELNest.nestK
  norm_num
  rw [harc]
  constructor
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-- Step `0` of the nest chain: the pair `(((215:ℝ)/1023) - ((139:ℝ)/178782208)*y, ((281:ℝ)/1023) + ((15:ℝ)/178782208)*y)`
maps to the pair `(((371:ℝ)/1023) - ((15:ℝ)/357564416)*y, ((404:ℝ)/1023) + ((139:ℝ)/357564416)*y)` of the next level of the chain.
(The branch used is `the far arc (p.1, p.1 + arcLen p.1 p.2)`
and `k = 1`.) -/
lemma nestStep_0 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.nestStep 0 (((215:ℝ)/1023) - ((139:ℝ)/178782208)*y, ((281:ℝ)/1023) + ((15:ℝ)/178782208)*y)
      = (((371:ℝ)/1023) - ((15:ℝ)/357564416)*y, ((404:ℝ)/1023) + ((139:ℝ)/357564416)*y) := by
  have harc : arcLen (((215:ℝ)/1023) - ((139:ℝ)/178782208)*y) (((281:ℝ)/1023) + ((15:ℝ)/178782208)*y) = ((2:ℝ)/31) + ((7:ℝ)/8126464)*y := by
    rw [arcLen, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  unfold Work.ELNest.nestStep Work.ELNest.nestArc Work.ELNest.nestK
  norm_num
  rw [harc]
  constructor
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
  · rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩

/-! ## The ten steps assembled -/

/-- The ten steps of the nest chain, applied to the level-`n` pair with `y = 1024⁻ⁿ`
(`0 < y ≤ 1`), give the level-`(n+1)` pair: the self-similarity of the angle formulas
`((371/1023 − (15/349184)y), (404/1023 + (139/349184)y)) ↦`
`((371/1023 − (15/357564416)y), (404/1023 + (139/357564416)y))`
(note `357564416 = 349184 · 1024`). -/
lemma nestPair_affine (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Work.ELNest.nestPair (((371:ℝ)/1023) - ((15:ℝ)/349184)*y, ((404:ℝ)/1023) + ((139:ℝ)/349184)*y) 10
      = (((371:ℝ)/1023) - ((15:ℝ)/357564416)*y, ((404:ℝ)/1023) + ((139:ℝ)/357564416)*y) := by
  change Work.ELNest.nestStep 0 (Work.ELNest.nestStep 1 (Work.ELNest.nestStep 2 (Work.ELNest.nestStep 3 (Work.ELNest.nestStep 4 (Work.ELNest.nestStep 5 (Work.ELNest.nestStep 6 (Work.ELNest.nestStep 7 (Work.ELNest.nestStep 8 (Work.ELNest.nestStep 9 (((371:ℝ)/1023) - ((15:ℝ)/349184)*y, ((404:ℝ)/1023) + ((139:ℝ)/349184)*y))))))))))
      = (((371:ℝ)/1023) - ((15:ℝ)/357564416)*y, ((404:ℝ)/1023) + ((139:ℝ)/357564416)*y)
  simp only [nestStep_9 y hy hy1, nestStep_8 y hy hy1, nestStep_7 y hy hy1,
    nestStep_6 y hy hy1, nestStep_5 y hy hy1, nestStep_4 y hy hy1,
    nestStep_3 y hy hy1, nestStep_2 y hy hy1, nestStep_1 y hy hy1, nestStep_0 y hy hy1]

/-! ## The self-similarity of the nest -/

theorem nestPair_nest (n : ℕ) :
    Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 10
      = (Work.ELNest.bAng (n + 1), Work.ELNest.bAng' (n + 1)) := by
  have hpos : (0 : ℝ) < ((1024 : ℝ) ^ n)⁻¹ := by positivity
  have hle : ((1024 : ℝ) ^ n)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by norm_num)
  have key := nestPair_affine ((1024 : ℝ) ^ n)⁻¹ hpos hle
  rw [show Work.ELNest.bAng n = ((371:ℝ)/1023) - ((15:ℝ)/349184) * ((1024 : ℝ) ^ n)⁻¹ from by
        rw [Work.ELNest.bAng, Work.ELNest.alpha1, Work.ELNest.beta0, div_eq_mul_inv]; ring,
      show Work.ELNest.bAng' n = ((404:ℝ)/1023) + ((139:ℝ)/349184) * ((1024 : ℝ) ^ n)⁻¹ from by
        rw [Work.ELNest.bAng', Work.ELNest.alpha2, Work.ELNest.beta0', div_eq_mul_inv]; ring,
      show Work.ELNest.bAng (n + 1) = ((371:ℝ)/1023) - ((15:ℝ)/357564416) * ((1024 : ℝ) ^ n)⁻¹ from by
        rw [Work.ELNest.bAng, Work.ELNest.alpha1, Work.ELNest.beta0, pow_succ, div_mul_eq_div_div]; ring,
      show Work.ELNest.bAng' (n + 1) = ((404:ℝ)/1023) + ((139:ℝ)/357564416) * ((1024 : ℝ) ^ n)⁻¹ from by
        rw [Work.ELNest.bAng', Work.ELNest.alpha2, Work.ELNest.beta0', pow_succ, div_mul_eq_div_div]; ring]
  exact key

end Work.ELNest
