/-
# `armB_W0`: the root arc `(α₁, α₂)` sits inside the reversed arm-`B` arc

At level `n` the arm-`B` pair of the `b₂`-nest is, in closed form,
`(25/63 + (1156/21483)·64⁻ⁿ, 37/63 - (164/21483)·64⁻ⁿ)` (`Work.ELNest.armChain_nest`).
Feeding this pair through `t ≤ 5` steps of the certified `armChainB` pattern (`nearB`, `kB`) and
taking the arc `armArcOf nearB (5-t)` used by the next `pb1Top` call produces, for each `t`, an
explicit arc whose *reversed* orientation contains the whole root arc `(α₁, α₂)`.

The proof unfolds the chains into the three normal forms of `Work.ELNest.armChainB_norm`
(`armB_step_far_one`, `armB_step_far_zero`, `armB_step_near_one`), reads off the closed forms of
the two arc endpoints and of `arcLen` of the reversed arc, and reduces the inclusion to finitely
many linear inequalities in `64⁻ⁿ ∈ (0,1]` and in `f = Int.fract (θ - α₁) ∈ (0, 33/1023)`, each of
which is discharged by `linarith`/`ring`.
-/
import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELNest.ArmChain
import Submission.Work.ELNest.armChainB_norm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Work.ELNest

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## helpers -/

lemma armArcOf_farB {j : ℕ} {p : ℝ × ℝ} (h : nearB j = false) :
    armArcOf nearB j p = (p.1, p.1 + Work.EL.arcLen p.1 p.2) := by
  unfold armArcOf; rw [h]; simp

lemma armArcOf_nearB {j : ℕ} {p : ℝ × ℝ} (h : nearB j = true) :
    armArcOf nearB j p = (p.2, p.2 + Work.EL.arcLen p.2 p.1) := by
  unfold armArcOf; rw [h]; simp

lemma fract_eq_of_lt_sub (u : ℝ) (K : ℤ) (h0 : (K : ℝ) < u) (h1 : u < (K : ℝ) + 1) :
    Int.fract u = u - K := by
  have h0' : (0 : ℝ) < u - (K : ℝ) := by linarith
  have h1' : u - (K : ℝ) < 1 := by linarith
  rw [← Int.fract_sub_intCast u K]
  exact Int.fract_eq_self.mpr ⟨le_of_lt h0', h1'⟩

lemma fract_eq_add_one (u : ℝ) (h0 : (-1:ℝ) < u) (h1 : u < 0) : Int.fract u = u + 1 := by
  have h0' : (((-1:ℤ)) : ℝ) < u := by push_cast; linarith
  have h1' : u < (((-1:ℤ)) : ℝ) + 1 := by push_cast; linarith
  have h := fract_eq_of_lt_sub u (-1) h0' h1'
  rw [h]; push_cast; ring

lemma fract_eq_self_of (u : ℝ) (h0 : 0 < u) (h1 : u < 1) : Int.fract u = u :=
  Int.fract_eq_self.mpr ⟨le_of_lt h0, h1⟩

lemma fract_sub_eq_fract (θ c : ℝ) :
    Int.fract (θ - c) =
      Int.fract (Int.fract (θ - Work.EL.alpha1) + (Work.EL.alpha1 - c)) := by
  have h : θ - c = (Int.fract (θ - Work.EL.alpha1) + (Work.EL.alpha1 - c))
      + (⌊θ - Work.EL.alpha1⌋ : ℝ) := by
    have hf := Int.fract_add_floor (θ - Work.EL.alpha1)
    linarith
  rw [h, Int.fract_add_intCast]

/-! ## the six pairs -/

lemma pair1 (n : ℕ) :
    armPairOf nearB kB (armB1 n, armB2 n) 1 =
      ((13/63 + (82:ℝ)/21483 * ((64:ℝ)^n)⁻¹,
        19/63 - (578:ℝ)/21483 * ((64:ℝ)^n)⁻¹) : ℝ × ℝ) := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [show armPairOf nearB kB (armB1 n, armB2 n) 1
        = armStepOf nearB kB 5 (armPairOf nearB kB (armB1 n, armB2 n) 0) from rfl,
      show armPairOf nearB kB (armB1 n, armB2 n) 0 = (armB1 n, armB2 n) from rfl,
      armB1_closed n, armB2_closed n]
  rw [armB_step_far_one 5 (by decide) (armB_kB_cast_one (j := 5) (by decide))
      (25/63 + (1156:ℝ)/21483 * ((64:ℝ)^n)⁻¹) (37/63 - (164:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  refine Prod.ext ?_ ?_ <;> ring

lemma pair2 (n : ℕ) :
    armPairOf nearB kB (armB1 n, armB2 n) 2 =
      ((22/63 + (289:ℝ)/21483 * ((64:ℝ)^n)⁻¹,
        25/63 - (41:ℝ)/21483 * ((64:ℝ)^n)⁻¹) : ℝ × ℝ) := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [show armPairOf nearB kB (armB1 n, armB2 n) 2
        = armStepOf nearB kB 4 (armPairOf nearB kB (armB1 n, armB2 n) 1) from rfl, pair1 n]
  rw [armB_step_far_one 4 (by decide) (armB_kB_cast_one (j := 4) (by decide))
      (13/63 + (82:ℝ)/21483 * ((64:ℝ)^n)⁻¹) (19/63 - (578:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  refine Prod.ext ?_ ?_ <;> ring

lemma pair3 (n : ℕ) :
    armPairOf nearB kB (armB1 n, armB2 n) 3 =
      ((52/63 - (289:ℝ)/42966 * ((64:ℝ)^n)⁻¹,
        19/63 + (41:ℝ)/42966 * ((64:ℝ)^n)⁻¹) : ℝ × ℝ) := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [show armPairOf nearB kB (armB1 n, armB2 n) 3
        = armStepOf nearB kB 3 (armPairOf nearB kB (armB1 n, armB2 n) 2) from rfl, pair2 n]
  rw [armB_step_near_one 3 (by decide) (armB_kB_cast_one (j := 3) (by decide))
      (22/63 + (289:ℝ)/21483 * ((64:ℝ)^n)⁻¹) (25/63 - (41:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  refine Prod.ext ?_ ?_ <;> ring

lemma pair4 (n : ℕ) :
    armPairOf nearB kB (armB1 n, armB2 n) 4 =
      ((22/63 - (41:ℝ)/85932 * ((64:ℝ)^n)⁻¹,
        37/63 + (289:ℝ)/85932 * ((64:ℝ)^n)⁻¹) : ℝ × ℝ) := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [show armPairOf nearB kB (armB1 n, armB2 n) 4
        = armStepOf nearB kB 2 (armPairOf nearB kB (armB1 n, armB2 n) 3) from rfl, pair3 n]
  rw [armB_step_far_zero 2 (by decide) (armB_kB_cast_zero (j := 2) (by decide))
      (52/63 - (289:ℝ)/42966 * ((64:ℝ)^n)⁻¹) (19/63 + (41:ℝ)/42966 * ((64:ℝ)^n)⁻¹)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  refine Prod.ext ?_ ?_ <;> ring

lemma pair5 (n : ℕ) :
    armPairOf nearB kB (armB1 n, armB2 n) 5 =
      ((52/63 + (41:ℝ)/171864 * ((64:ℝ)^n)⁻¹,
        13/63 - (289:ℝ)/171864 * ((64:ℝ)^n)⁻¹) : ℝ × ℝ) := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [show armPairOf nearB kB (armB1 n, armB2 n) 5
        = armStepOf nearB kB 1 (armPairOf nearB kB (armB1 n, armB2 n) 4) from rfl, pair4 n]
  rw [armB_step_near_one 1 (by decide) (armB_kB_cast_one (j := 1) (by decide))
      (22/63 - (41:ℝ)/85932 * ((64:ℝ)^n)⁻¹) (37/63 + (289:ℝ)/85932 * ((64:ℝ)^n)⁻¹)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  refine Prod.ext ?_ ?_ <;> ring



/-! ## the six arcs `armArcOf ... (pair t)` -/

lemma X0 (n : ℕ) :
    armArcOf nearB 5 (armPairOf nearB kB (armB1 n, armB2 n) 0) =
      ((25/63 + (1156:ℝ)/21483 * ((64:ℝ)^n)⁻¹,
        37/63 - (164:ℝ)/21483 * ((64:ℝ)^n)⁻¹) : ℝ × ℝ) := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [show armPairOf nearB kB (armB1 n, armB2 n) 0 = (armB1 n, armB2 n) from rfl,
      armB1_closed n, armB2_closed n]
  rw [armArcOf_farB (by decide : nearB 5 = false)]
  have harc : Work.EL.arcLen (25/63 + (1156:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
      (37/63 - (164:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
      = 4/21 - (1320:ℝ)/21483 * ((64:ℝ)^n)⁻¹ := by
    rw [Work.EL.arcLen,
      show 37/63 - (164:ℝ)/21483 * ((64:ℝ)^n)⁻¹ - (25/63 + (1156:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
        = 4/21 - (1320:ℝ)/21483 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨0, by push_cast; ring⟩⟩
  rw [harc]
  refine Prod.ext rfl ?_
  ring

lemma X1 (n : ℕ) :
    armArcOf nearB 4 (armPairOf nearB kB (armB1 n, armB2 n) 1) =
      ((13/63 + (82:ℝ)/21483 * ((64:ℝ)^n)⁻¹,
        19/63 - (578:ℝ)/21483 * ((64:ℝ)^n)⁻¹) : ℝ × ℝ) := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [pair1 n]
  rw [armArcOf_farB (by decide : nearB 4 = false)]
  have harc : Work.EL.arcLen (13/63 + (82:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
      (19/63 - (578:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
      = 2/21 - (660:ℝ)/21483 * ((64:ℝ)^n)⁻¹ := by
    rw [Work.EL.arcLen,
      show 19/63 - (578:ℝ)/21483 * ((64:ℝ)^n)⁻¹ - (13/63 + (82:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
        = 2/21 - (660:ℝ)/21483 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨0, by push_cast; ring⟩⟩
  rw [harc]
  refine Prod.ext rfl ?_
  ring

lemma X2 (n : ℕ) :
    armArcOf nearB 3 (armPairOf nearB kB (armB1 n, armB2 n) 2) =
      ((25/63 - (41:ℝ)/21483 * ((64:ℝ)^n)⁻¹,
        85/63 + (289:ℝ)/21483 * ((64:ℝ)^n)⁻¹) : ℝ × ℝ) := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [pair2 n]
  rw [armArcOf_nearB (by decide : nearB 3 = true)]
  have harc : Work.EL.arcLen (25/63 - (41:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
      (22/63 + (289:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
      = 20/21 + (330:ℝ)/21483 * ((64:ℝ)^n)⁻¹ := by
    rw [Work.EL.arcLen,
      show 22/63 + (289:ℝ)/21483 * ((64:ℝ)^n)⁻¹ - (25/63 - (41:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
        = -1/21 + (330:ℝ)/21483 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  rw [harc]
  refine Prod.ext rfl ?_
  ring

lemma X3 (n : ℕ) :
    armArcOf nearB 2 (armPairOf nearB kB (armB1 n, armB2 n) 3) =
      ((52/63 - (289:ℝ)/42966 * ((64:ℝ)^n)⁻¹,
        82/63 + (41:ℝ)/42966 * ((64:ℝ)^n)⁻¹) : ℝ × ℝ) := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [pair3 n]
  rw [armArcOf_farB (by decide : nearB 2 = false)]
  have harc : Work.EL.arcLen (52/63 - (289:ℝ)/42966 * ((64:ℝ)^n)⁻¹)
      (19/63 + (41:ℝ)/42966 * ((64:ℝ)^n)⁻¹)
      = 10/21 + (330:ℝ)/42966 * ((64:ℝ)^n)⁻¹ := by
    rw [Work.EL.arcLen,
      show 19/63 + (41:ℝ)/42966 * ((64:ℝ)^n)⁻¹ - (52/63 - (289:ℝ)/42966 * ((64:ℝ)^n)⁻¹)
        = -11/21 + (330:ℝ)/42966 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  rw [harc]
  refine Prod.ext rfl ?_
  ring

lemma X4 (n : ℕ) :
    armArcOf nearB 1 (armPairOf nearB kB (armB1 n, armB2 n) 4) =
      ((37/63 + (289:ℝ)/85932 * ((64:ℝ)^n)⁻¹,
        85/63 - (41:ℝ)/85932 * ((64:ℝ)^n)⁻¹) : ℝ × ℝ) := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [pair4 n]
  rw [armArcOf_nearB (by decide : nearB 1 = true)]
  have harc : Work.EL.arcLen (37/63 + (289:ℝ)/85932 * ((64:ℝ)^n)⁻¹)
      (22/63 - (41:ℝ)/85932 * ((64:ℝ)^n)⁻¹)
      = 16/21 - (330:ℝ)/85932 * ((64:ℝ)^n)⁻¹ := by
    rw [Work.EL.arcLen,
      show 22/63 - (41:ℝ)/85932 * ((64:ℝ)^n)⁻¹ - (37/63 + (289:ℝ)/85932 * ((64:ℝ)^n)⁻¹)
        = -5/21 - (330:ℝ)/85932 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  rw [harc]
  refine Prod.ext rfl ?_
  ring

lemma X5 (n : ℕ) :
    armArcOf nearB 0 (armPairOf nearB kB (armB1 n, armB2 n) 5) =
      ((52/63 + (41:ℝ)/171864 * ((64:ℝ)^n)⁻¹,
        76/63 - (289:ℝ)/171864 * ((64:ℝ)^n)⁻¹) : ℝ × ℝ) := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [pair5 n]
  rw [armArcOf_farB (by decide : nearB 0 = false)]
  have harc : Work.EL.arcLen (52/63 + (41:ℝ)/171864 * ((64:ℝ)^n)⁻¹)
      (13/63 - (289:ℝ)/171864 * ((64:ℝ)^n)⁻¹)
      = 8/21 - (330:ℝ)/171864 * ((64:ℝ)^n)⁻¹ := by
    rw [Work.EL.arcLen,
      show 13/63 - (289:ℝ)/171864 * ((64:ℝ)^n)⁻¹ - (52/63 + (41:ℝ)/171864 * ((64:ℝ)^n)⁻¹)
        = -13/21 - (330:ℝ)/171864 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  rw [harc]
  refine Prod.ext rfl ?_
  ring



/-! ## the per-step inequalities -/

lemma key0 (X : ℝ) (hX0 : 0 < X) (hX1 : X ≤ 1) :
    ∀ f : ℝ, 0 < f → f < 33/1023 →
    0 < Int.fract (f + (-4826/21483 + (164:ℝ)/21483 * X)) ∧
      Int.fract (f + (-4826/21483 + (164:ℝ)/21483 * X)) < 17/21 + (1320:ℝ)/21483 * X := by
  intro f hf0 hf1
  have hlow : (-1:ℝ) < f + (-4826/21483 + (164:ℝ)/21483 * X) := by linarith
  have hhigh : f + (-4826/21483 + (164:ℝ)/21483 * X) < 0 := by linarith
  rw [fract_eq_add_one (f + (-4826/21483 + (164:ℝ)/21483 * X)) hlow hhigh]
  constructor <;> linarith

lemma key1 (X : ℝ) (hX0 : 0 < X) (hX1 : X ≤ 1) :
    ∀ f : ℝ, 0 < f → f < 33/1023 →
    0 < Int.fract (f + (1312/21483 + (578:ℝ)/21483 * X)) ∧
      Int.fract (f + (1312/21483 + (578:ℝ)/21483 * X)) < 19/21 + (660:ℝ)/21483 * X := by
  intro f hf0 hf1
  have hlow : (0:ℝ) < f + (1312/21483 + (578:ℝ)/21483 * X) := by linarith
  have hhigh : f + (1312/21483 + (578:ℝ)/21483 * X) < 1 := by linarith
  rw [fract_eq_self_of (f + (1312/21483 + (578:ℝ)/21483 * X)) hlow hhigh]
  constructor <;> linarith

lemma key2 (X : ℝ) (hX0 : 0 < X) (hX1 : X ≤ 1) :
    ∀ f : ℝ, 0 < f → f < 33/1023 →
    0 < Int.fract (f + (-21194/21483 - (289:ℝ)/21483 * X)) ∧
      Int.fract (f + (-21194/21483 - (289:ℝ)/21483 * X)) < 1/21 - (330:ℝ)/21483 * X := by
  intro f hf0 hf1
  have hlow : (-1:ℝ) < f + (-21194/21483 - (289:ℝ)/21483 * X) := by linarith
  have hhigh : f + (-21194/21483 - (289:ℝ)/21483 * X) < 0 := by linarith
  rw [fract_eq_add_one (f + (-21194/21483 - (289:ℝ)/21483 * X)) hlow hhigh]
  constructor <;> linarith

lemma key3 (X : ℝ) (hX0 : 0 < X) (hX1 : X ≤ 1) :
    ∀ f : ℝ, 0 < f → f < 33/1023 →
    0 < Int.fract (f + (-20171/21483 - (41:ℝ)/42966 * X)) ∧
      Int.fract (f + (-20171/21483 - (41:ℝ)/42966 * X)) < 11/21 - (330:ℝ)/42966 * X := by
  intro f hf0 hf1
  have hlow : (-1:ℝ) < f + (-20171/21483 - (41:ℝ)/42966 * X) := by linarith
  have hhigh : f + (-20171/21483 - (41:ℝ)/42966 * X) < 0 := by linarith
  rw [fract_eq_add_one (f + (-20171/21483 - (41:ℝ)/42966 * X)) hlow hhigh]
  constructor <;> linarith

lemma key4 (X : ℝ) (hX0 : 0 < X) (hX1 : X ≤ 1) :
    ∀ f : ℝ, 0 < f → f < 33/1023 →
    0 < Int.fract (f + (-21194/21483 + (41:ℝ)/85932 * X)) ∧
      Int.fract (f + (-21194/21483 + (41:ℝ)/85932 * X)) < 5/21 + (330:ℝ)/85932 * X := by
  intro f hf0 hf1
  have hlow : (-1:ℝ) < f + (-21194/21483 + (41:ℝ)/85932 * X) := by linarith
  have hhigh : f + (-21194/21483 + (41:ℝ)/85932 * X) < 0 := by linarith
  rw [fract_eq_add_one (f + (-21194/21483 + (41:ℝ)/85932 * X)) hlow hhigh]
  constructor <;> linarith

lemma key5 (X : ℝ) (hX0 : 0 < X) (hX1 : X ≤ 1) :
    ∀ f : ℝ, 0 < f → f < 33/1023 →
    0 < Int.fract (f + (-18125/21483 + (289:ℝ)/171864 * X)) ∧
      Int.fract (f + (-18125/21483 + (289:ℝ)/171864 * X)) < 13/21 + (330:ℝ)/171864 * X := by
  intro f hf0 hf1
  have hlow : (-1:ℝ) < f + (-18125/21483 + (289:ℝ)/171864 * X) := by linarith
  have hhigh : f + (-18125/21483 + (289:ℝ)/171864 * X) < 0 := by linarith
  rw [fract_eq_add_one (f + (-18125/21483 + (289:ℝ)/171864 * X)) hlow hhigh]
  constructor <;> linarith



/-! ## assembly -/

lemma inArc_of_key {θ X1 X2 ℓ d : ℝ} (hθ : Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2)
    (hlen : Work.EL.arcLen X2 X1 = ℓ) (hd : d = Work.EL.alpha1 - X2)
    (hkey : ∀ f : ℝ, 0 < f → f < (33:ℝ)/1023 →
      0 < Int.fract (f + d) ∧ Int.fract (f + d) < ℓ) :
    Work.EL.InArc θ X2 X1 := by
  have harc : Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 = (33:ℝ)/1023 := by
    rw [Work.EL.arcLen,
      show Work.EL.alpha2 - Work.EL.alpha1 = 33/1023 from by
        rw [Work.EL.alpha1, Work.EL.alpha2]; norm_num]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have hf0 : 0 < Int.fract (θ - Work.EL.alpha1) := hθ.1
  have hf1 : Int.fract (θ - Work.EL.alpha1) < (33:ℝ)/1023 := by
    have h := hθ.2; rwa [harc] at h
  obtain ⟨h1, h2⟩ := hkey _ hf0 hf1
  refine ⟨?_, ?_⟩
  · rw [fract_sub_eq_fract θ X2, ← hd]; exact h1
  · rw [fract_sub_eq_fract θ X2, ← hd, hlen]; exact h2

lemma armB_t0 (n : ℕ) (θ : ℝ) (hθ : Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2) :
    Work.EL.InArc θ
      (armArcOf nearB 5 (armPairOf nearB kB (armB1 n, armB2 n) 0)).2
      (armArcOf nearB 5 (armPairOf nearB kB (armB1 n, armB2 n) 0)).1 := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [X0 n]
  show Work.EL.InArc θ (37/63 - (164:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (25/63 + (1156:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
  refine inArc_of_key (X1 := 25/63 + (1156:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (X2 := 37/63 - (164:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (ℓ := 17/21 + (1320:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (d := -4826/21483 + (164:ℝ)/21483 * ((64:ℝ)^n)⁻¹) hθ ?_ ?_ ?_
  · rw [Work.EL.arcLen,
      show 25/63 + (1156:ℝ)/21483 * ((64:ℝ)^n)⁻¹ - (37/63 - (164:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
        = -4/21 + (1320:ℝ)/21483 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  · rw [Work.EL.alpha1]; ring
  · exact key0 _ hx0 hx1

lemma armB_t1 (n : ℕ) (θ : ℝ) (hθ : Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2) :
    Work.EL.InArc θ
      (armArcOf nearB 4 (armPairOf nearB kB (armB1 n, armB2 n) 1)).2
      (armArcOf nearB 4 (armPairOf nearB kB (armB1 n, armB2 n) 1)).1 := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [X1 n]
  show Work.EL.InArc θ (19/63 - (578:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (13/63 + (82:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
  refine inArc_of_key (X1 := 13/63 + (82:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (X2 := 19/63 - (578:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (ℓ := 19/21 + (660:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (d := 1312/21483 + (578:ℝ)/21483 * ((64:ℝ)^n)⁻¹) hθ ?_ ?_ ?_
  · rw [Work.EL.arcLen,
      show 13/63 + (82:ℝ)/21483 * ((64:ℝ)^n)⁻¹ - (19/63 - (578:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
        = -2/21 + (660:ℝ)/21483 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  · rw [Work.EL.alpha1]; ring
  · exact key1 _ hx0 hx1

lemma armB_t2 (n : ℕ) (θ : ℝ) (hθ : Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2) :
    Work.EL.InArc θ
      (armArcOf nearB 3 (armPairOf nearB kB (armB1 n, armB2 n) 2)).2
      (armArcOf nearB 3 (armPairOf nearB kB (armB1 n, armB2 n) 2)).1 := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [X2 n]
  show Work.EL.InArc θ (85/63 + (289:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (25/63 - (41:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
  refine inArc_of_key (X1 := 25/63 - (41:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (X2 := 85/63 + (289:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (ℓ := 1/21 - (330:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
    (d := -21194/21483 - (289:ℝ)/21483 * ((64:ℝ)^n)⁻¹) hθ ?_ ?_ ?_
  · rw [Work.EL.arcLen,
      show 25/63 - (41:ℝ)/21483 * ((64:ℝ)^n)⁻¹ - (85/63 + (289:ℝ)/21483 * ((64:ℝ)^n)⁻¹)
        = -20/21 - (330:ℝ)/21483 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  · rw [Work.EL.alpha1]; ring
  · exact key2 _ hx0 hx1

lemma armB_t3 (n : ℕ) (θ : ℝ) (hθ : Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2) :
    Work.EL.InArc θ
      (armArcOf nearB 2 (armPairOf nearB kB (armB1 n, armB2 n) 3)).2
      (armArcOf nearB 2 (armPairOf nearB kB (armB1 n, armB2 n) 3)).1 := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [X3 n]
  show Work.EL.InArc θ (82/63 + (41:ℝ)/42966 * ((64:ℝ)^n)⁻¹)
    (52/63 - (289:ℝ)/42966 * ((64:ℝ)^n)⁻¹)
  refine inArc_of_key (X1 := 52/63 - (289:ℝ)/42966 * ((64:ℝ)^n)⁻¹)
    (X2 := 82/63 + (41:ℝ)/42966 * ((64:ℝ)^n)⁻¹)
    (ℓ := 11/21 - (330:ℝ)/42966 * ((64:ℝ)^n)⁻¹)
    (d := -20171/21483 - (41:ℝ)/42966 * ((64:ℝ)^n)⁻¹) hθ ?_ ?_ ?_
  · rw [Work.EL.arcLen,
      show 52/63 - (289:ℝ)/42966 * ((64:ℝ)^n)⁻¹ - (82/63 + (41:ℝ)/42966 * ((64:ℝ)^n)⁻¹)
        = -10/21 - (330:ℝ)/42966 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  · rw [Work.EL.alpha1]; ring
  · exact key3 _ hx0 hx1

lemma armB_t4 (n : ℕ) (θ : ℝ) (hθ : Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2) :
    Work.EL.InArc θ
      (armArcOf nearB 1 (armPairOf nearB kB (armB1 n, armB2 n) 4)).2
      (armArcOf nearB 1 (armPairOf nearB kB (armB1 n, armB2 n) 4)).1 := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [X4 n]
  show Work.EL.InArc θ (85/63 - (41:ℝ)/85932 * ((64:ℝ)^n)⁻¹)
    (37/63 + (289:ℝ)/85932 * ((64:ℝ)^n)⁻¹)
  refine inArc_of_key (X1 := 37/63 + (289:ℝ)/85932 * ((64:ℝ)^n)⁻¹)
    (X2 := 85/63 - (41:ℝ)/85932 * ((64:ℝ)^n)⁻¹)
    (ℓ := 5/21 + (330:ℝ)/85932 * ((64:ℝ)^n)⁻¹)
    (d := -21194/21483 + (41:ℝ)/85932 * ((64:ℝ)^n)⁻¹) hθ ?_ ?_ ?_
  · rw [Work.EL.arcLen,
      show 37/63 + (289:ℝ)/85932 * ((64:ℝ)^n)⁻¹ - (85/63 - (41:ℝ)/85932 * ((64:ℝ)^n)⁻¹)
        = -16/21 + (330:ℝ)/85932 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  · rw [Work.EL.alpha1]; ring
  · exact key4 _ hx0 hx1

lemma armB_t5 (n : ℕ) (θ : ℝ) (hθ : Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2) :
    Work.EL.InArc θ
      (armArcOf nearB 0 (armPairOf nearB kB (armB1 n, armB2 n) 5)).2
      (armArcOf nearB 0 (armPairOf nearB kB (armB1 n, armB2 n) 5)).1 := by
  have hx0 : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hx1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [X5 n]
  show Work.EL.InArc θ (76/63 - (289:ℝ)/171864 * ((64:ℝ)^n)⁻¹)
    (52/63 + (41:ℝ)/171864 * ((64:ℝ)^n)⁻¹)
  refine inArc_of_key (X1 := 52/63 + (41:ℝ)/171864 * ((64:ℝ)^n)⁻¹)
    (X2 := 76/63 - (289:ℝ)/171864 * ((64:ℝ)^n)⁻¹)
    (ℓ := 13/21 + (330:ℝ)/171864 * ((64:ℝ)^n)⁻¹)
    (d := -18125/21483 + (289:ℝ)/171864 * ((64:ℝ)^n)⁻¹) hθ ?_ ?_ ?_
  · rw [Work.EL.arcLen,
      show 52/63 + (41:ℝ)/171864 * ((64:ℝ)^n)⁻¹ - (76/63 - (289:ℝ)/171864 * ((64:ℝ)^n)⁻¹)
        = -8/21 + (330:ℝ)/171864 * ((64:ℝ)^n)⁻¹ from by ring]
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  · rw [Work.EL.alpha1]; ring
  · exact key5 _ hx0 hx1

theorem armB_W0 {c : ℂ} (n t : ℕ) (ht : t < 6) : ∀ θ : ℝ, Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ (Work.ELNest.armArcOf Work.ELNest.nearB (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (Work.ELNest.armB1 n, Work.ELNest.armB2 n) t)).2 (Work.ELNest.armArcOf Work.ELNest.nearB (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (Work.ELNest.armB1 n, Work.ELNest.armB2 n) t)).1 := by
  interval_cases t
  · exact armB_t0 n
  · exact armB_t1 n
  · exact armB_t2 n
  · exact armB_t3 n
  · exact armB_t4 n
  · exact armB_t5 n

end Work.ELAssembly
