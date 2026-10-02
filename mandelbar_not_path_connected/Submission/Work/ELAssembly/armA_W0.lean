/-
# `armA_W0`: the root arc lies in the arc fed to `pb1Top` at every step of the arm-`A` chain

`Submission/Work/ELAssembly/armA_W0.lean`.

The `c`-side condition `hcvA` of the arm-`A` chain (a hypothesis of `Work.ELNest.armPair_coLands`
and of `Work.ELAssembly.coLand_Z`) asks, at every step `t < 6` of the chain, for
`c ∈ arcSide hN Q I.2 I.1` where `I = armArcOf nearA (5-t) p_t` is the arc fed to `pb1Top` at that
step and `p_t = armPairOf nearA kA (armA1 n, armA2 n) t` the current pair.  `cv_mem_arcSide_of_W0`
reduces this to the purely angle-theoretic statement, proved here: the root arc `(α₁, α₂)` is
contained in the arc `(I.2, I.1)`, i.e.

  `∀ θ, InArc θ α₁ α₂ → InArc θ I.2 I.1`.

The proof is a finite exact rational computation.  On the box
`a ∈ [22/63, α₁]`, `b ∈ [α₂, 25/63]` — which contains the level-`n` arm-`A` pair
`(armA1 n, armA2 n)` for every `n`, since `armA1 n = 22/63 + (α₁ - 22/63)/64ⁿ` and
`armA2 n = 25/63 + (α₂ - 25/63)/64ⁿ` — the pair `p_t` and the arc `I_t = armArcOf nearA (5-t) p_t`
are explicit affine functions of `(a, b)`, given by the normal forms of
`Submission/Work/ELNest/armChainA_norm.lean`; the two `Int.fract`s of `InArc θ I_t.2 I_t.1` then
resolve by sign, and the statement becomes two linear inequalities.  The table of the arcs is

| `t` | arc `I_t = (I_t.1, I_t.2)` | `InArc θ I_t.2 I_t.1` |
|-----|----------------------------|------------------------|
| 0 | `(b, a+1)` | `0 < θ-a`, `θ-a < b-a` |
| 1 | `(1-a/2, (3-b)/2)` | `2θ+b>1`, `2θ+a<2` |
| 2 | `(1/2+a/4, 5/4+b/4)` | `4θ-b>1`, `4θ<a+2` |
| 3 | `(7/8-b/8, 5/4-a/8)` | `8θ+a>2`, `8θ<7-b` |
| 4 | `(3/8+a/16, 9/16+b/16)` | `16θ>b-7`, `16θ<a+6` |
| 5 | `(7/32-b/32, 5/16-a/32)` | `32θ+a>10`, `32θ<39-b` |
-/
import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELNest.ArmChain
import Submission.Work.ELNest.armChainA_norm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.ELAssembly

open Work.ELNest

/-! ## The numeric data of the root arc -/

theorem W0_alpha1_lt_alpha2 : Work.EL.alpha1 < Work.EL.alpha2 := by
  norm_num [Work.EL.alpha1, Work.EL.alpha2]

theorem W0_alpha1_lt_one : Work.EL.alpha1 < 1 := by
  norm_num [Work.EL.alpha1]

theorem W0_alpha2_lt_one : Work.EL.alpha2 < 1 := by
  norm_num [Work.EL.alpha2]

/-- `arcLen α₁ α₂ = 1/31`: the length of the root arc. -/
theorem W0_arcLen_alpha1_alpha2 : Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 = 1 / 31 := by
  have h : Work.EL.alpha2 - Work.EL.alpha1 = 1 / 31 := by
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  rw [Work.EL.arcLen, h, Int.fract_eq_self]
  norm_num

/-! ## The two branches of `armArcOf` for the near/far pattern `nearA` -/

theorem W0_arc_near (j : ℕ) (hj : nearA j = true) (x y : ℝ) :
    armArcOf nearA j (x, y) = (y, y + Int.fract (x - y)) := by
  simp [armArcOf, Work.EL.arcLen, hj]

theorem W0_arc_far (j : ℕ) (hj : nearA j = false) (x y : ℝ) :
    armArcOf nearA j (x, y) = (x, x + Int.fract (y - x)) := by
  simp [armArcOf, Work.EL.arcLen, hj]

/-! ## The box of the level-`n` arm-`A` pair -/

/-- `armA1 n = 22/63 + (α₁ - 22/63)/64ⁿ`, hence `22/63 ≤ armA1 n ≤ α₁`. -/
theorem W0_armA1_mem (n : ℕ) : (22 / 63 : ℝ) ≤ armA1 n ∧ armA1 n ≤ Work.EL.alpha1 := by
  have hα : centred (alpha1 - 22 / 63) = alpha1 - 22 / 63 := by
    rw [centred, Int.fract_eq_self.mpr ⟨by norm_num [alpha1], by norm_num [alpha1]⟩]
    ring
  have hpow : (((64 : ℕ) ^ n : ℕ) : ℝ) = (64 : ℝ) ^ n := Nat.cast_pow 64 n
  have hden : (0 : ℝ) < (((64 : ℕ) ^ n : ℕ) : ℝ) := by
    rw [hpow]; positivity
  have hone : (1 : ℝ) ≤ (((64 : ℕ) ^ n : ℕ) : ℝ) := by
    rw [hpow]; exact one_le_pow₀ (by norm_num)
  have h0 : (0 : ℝ) < alpha1 - 22 / 63 := by norm_num [alpha1]
  have h3 : (22 / 63 : ℝ) ≤ 22 / 63 + (alpha1 - 22 / 63) / (((64 : ℕ) ^ n : ℕ) : ℝ) := by
    have := div_nonneg (le_of_lt h0) (le_of_lt hden)
    linarith
  have hdiv : (alpha1 - 22 / 63) / (((64 : ℕ) ^ n : ℕ) : ℝ) ≤ alpha1 - 22 / 63 :=
    div_le_self (le_of_lt h0) hone
  have h4 : 22 / 63 + (alpha1 - 22 / 63) / (((64 : ℕ) ^ n : ℕ) : ℝ) ≤ Work.EL.alpha1 := by
    have heq : alpha1 = Work.EL.alpha1 := rfl
    linarith
  have hfr : Int.fract (22 / 63 + (alpha1 - 22 / 63) / (((64 : ℕ) ^ n : ℕ) : ℝ))
      = 22 / 63 + (alpha1 - 22 / 63) / (((64 : ℕ) ^ n : ℕ) : ℝ) :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith [h4, W0_alpha1_lt_one]⟩
  unfold armA1 contract
  rw [hα, hfr]
  exact ⟨h3, h4⟩

/-- `armA2 n = 25/63 + (α₂ - 25/63)/64ⁿ`, hence `α₂ ≤ armA2 n ≤ 25/63`. -/
theorem W0_armA2_mem (n : ℕ) : Work.EL.alpha2 ≤ armA2 n ∧ armA2 n ≤ 25 / 63 := by
  have hα : centred (alpha2 - 25 / 63) = alpha2 - 25 / 63 := by
    rw [centred, Int.fract_eq_self.mpr ⟨by norm_num [alpha2], by norm_num [alpha2]⟩]
    ring
  have hpow : (((64 : ℕ) ^ n : ℕ) : ℝ) = (64 : ℝ) ^ n := Nat.cast_pow 64 n
  have hden : (0 : ℝ) < (((64 : ℕ) ^ n : ℕ) : ℝ) := by
    rw [hpow]; positivity
  have hone : (1 : ℝ) ≤ (((64 : ℕ) ^ n : ℕ) : ℝ) := by
    rw [hpow]; exact one_le_pow₀ (by norm_num)
  have h0 : alpha2 - 25 / 63 < 0 := by norm_num [alpha2]
  have hdiv : alpha2 - 25 / 63 ≤ (alpha2 - 25 / 63) / (((64 : ℕ) ^ n : ℕ) : ℝ) := by
    rw [le_div_iff₀ hden]
    have hm := mul_le_mul_of_nonpos_right hone (le_of_lt h0)
    simpa [mul_comm] using hm
  have h1 : Work.EL.alpha2 ≤ 25 / 63 + (alpha2 - 25 / 63) / (((64 : ℕ) ^ n : ℕ) : ℝ) := by
    have heq : alpha2 = Work.EL.alpha2 := rfl
    linarith
  have h2 : 25 / 63 + (alpha2 - 25 / 63) / (((64 : ℕ) ^ n : ℕ) : ℝ) ≤ 25 / 63 := by
    have := div_nonpos_of_nonpos_of_nonneg (le_of_lt h0) (le_of_lt hden)
    linarith
  have hα2nn : (0 : ℝ) ≤ Work.EL.alpha2 := by norm_num [Work.EL.alpha2]
  have hfr : Int.fract (25 / 63 + (alpha2 - 25 / 63) / (((64 : ℕ) ^ n : ℕ) : ℝ))
      = 25 / 63 + (alpha2 - 25 / 63) / (((64 : ℕ) ^ n : ℕ) : ℝ) :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  unfold armA2 contract
  rw [hα, hfr]
  exact ⟨h1, h2⟩

/-! ## The pairs `p_t = armPairOf nearA kA (a,b) t` on the box -/

theorem W0_pair_one (a b : ℝ) (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63) :
    armPairOf nearA kA (a, b) 1 = (1 - a / 2, (1 - b) / 2) := by
  have hAB : Work.EL.alpha1 < Work.EL.alpha2 := W0_alpha1_lt_alpha2
  have hA1 : Work.EL.alpha1 < 1 := W0_alpha1_lt_one
  have h2' : a ≤ (371 : ℝ) / 1023 := by simpa [Work.EL.alpha1] using h2
  have h3' : (404 : ℝ) / 1023 ≤ b := by simpa [Work.EL.alpha2] using h3
  exact armA_step_near_one 5 (by decide) (armA_kA_cast_one (j := 5) (by decide)) a b
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

theorem W0_pair_two (a b : ℝ) (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63) :
    armPairOf nearA kA (a, b) 2 = ((1 + b) / 4, 1 / 2 + a / 4) := by
  show armStepOf nearA kA 4 (armPairOf nearA kA (a, b) 1) = ((1 + b) / 4, 1 / 2 + a / 4)
  have hAB : Work.EL.alpha1 < Work.EL.alpha2 := W0_alpha1_lt_alpha2
  have hA1 : Work.EL.alpha1 < 1 := W0_alpha1_lt_one
  have h2' : a ≤ (371 : ℝ) / 1023 := by simpa [Work.EL.alpha1] using h2
  have h3' : (404 : ℝ) / 1023 ≤ b := by simpa [Work.EL.alpha2] using h3
  have hp := W0_pair_one a b h1 h2 h3 h4
  have hstep : armStepOf nearA kA 4 (1 - a / 2, (1 - b) / 2)
      = ((1 + b) / 4, 1 / 2 + a / 4) := by
    have h := armA_step_far_zero 4 (by decide) (armA_kA_cast_zero (j := 4) (by decide))
      (1 - a / 2) ((1 - b) / 2) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [h]
    refine Prod.ext ?_ ?_ <;> ring
  rw [hp]
  exact hstep

theorem W0_pair_three (a b : ℝ) (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63) :
    armPairOf nearA kA (a, b) 3 = (7 / 8 - b / 8, 1 / 4 - a / 8) := by
  show armStepOf nearA kA 3 (armPairOf nearA kA (a, b) 2) = (7 / 8 - b / 8, 1 / 4 - a / 8)
  have hAB : Work.EL.alpha1 < Work.EL.alpha2 := W0_alpha1_lt_alpha2
  have hA1 : Work.EL.alpha1 < 1 := W0_alpha1_lt_one
  have h2' : a ≤ (371 : ℝ) / 1023 := by simpa [Work.EL.alpha1] using h2
  have h3' : (404 : ℝ) / 1023 ≤ b := by simpa [Work.EL.alpha2] using h3
  have hp := W0_pair_two a b h1 h2 h3 h4
  have hstep : armStepOf nearA kA 3 ((1 + b) / 4, 1 / 2 + a / 4)
      = (7 / 8 - b / 8, 1 / 4 - a / 8) := by
    have h := armA_step_near_one 3 (by decide) (armA_kA_cast_one (j := 3) (by decide))
      ((1 + b) / 4) (1 / 2 + a / 4) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [h]
    refine Prod.ext ?_ ?_ <;> ring
  rw [hp]
  exact hstep

theorem W0_pair_four (a b : ℝ) (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63) :
    armPairOf nearA kA (a, b) 4 = (3 / 8 + a / 16, 9 / 16 + b / 16) := by
  show armStepOf nearA kA 2 (armPairOf nearA kA (a, b) 3) = (3 / 8 + a / 16, 9 / 16 + b / 16)
  have hAB : Work.EL.alpha1 < Work.EL.alpha2 := W0_alpha1_lt_alpha2
  have hA1 : Work.EL.alpha1 < 1 := W0_alpha1_lt_one
  have h2' : a ≤ (371 : ℝ) / 1023 := by simpa [Work.EL.alpha1] using h2
  have h3' : (404 : ℝ) / 1023 ≤ b := by simpa [Work.EL.alpha2] using h3
  have hp := W0_pair_three a b h1 h2 h3 h4
  have hstep : armStepOf nearA kA 2 (7 / 8 - b / 8, 1 / 4 - a / 8)
      = (3 / 8 + a / 16, 9 / 16 + b / 16) := by
    have h := armA_step_far_zero 2 (by decide) (armA_kA_cast_zero (j := 2) (by decide))
      (7 / 8 - b / 8) (1 / 4 - a / 8) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [h]
    refine Prod.ext ?_ ?_ <;> ring
  rw [hp]
  exact hstep

theorem W0_pair_five (a b : ℝ) (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63) :
    armPairOf nearA kA (a, b) 5 = (7 / 32 - b / 32, 5 / 16 - a / 32) := by
  show armStepOf nearA kA 1 (armPairOf nearA kA (a, b) 4) = (7 / 32 - b / 32, 5 / 16 - a / 32)
  have hAB : Work.EL.alpha1 < Work.EL.alpha2 := W0_alpha1_lt_alpha2
  have hA1 : Work.EL.alpha1 < 1 := W0_alpha1_lt_one
  have h2' : a ≤ (371 : ℝ) / 1023 := by simpa [Work.EL.alpha1] using h2
  have h3' : (404 : ℝ) / 1023 ≤ b := by simpa [Work.EL.alpha2] using h3
  have hp := W0_pair_four a b h1 h2 h3 h4
  have hstep : armStepOf nearA kA 1 (3 / 8 + a / 16, 9 / 16 + b / 16)
      = (7 / 32 - b / 32, 5 / 16 - a / 32) := by
    have h := armA_step_far_one 1 (by decide) (armA_kA_cast_one (j := 1) (by decide))
      (3 / 8 + a / 16) (9 / 16 + b / 16) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [h]
    refine Prod.ext ?_ ?_ <;> ring
  rw [hp]
  exact hstep

/-! ## The six containments `InArc θ I_t.2 I_t.1` -/

theorem W0_case_zero (a b θ : ℝ) (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63)
    (hθ1 : Work.EL.alpha1 < θ) (hθ2 : θ < Work.EL.alpha2) :
    Work.EL.InArc θ (armArcOf nearA 5 (armPairOf nearA kA (a, b) 0)).2
      (armArcOf nearA 5 (armPairOf nearA kA (a, b) 0)).1 := by
  have h2' : a ≤ (371 : ℝ) / 1023 := by simpa [Work.EL.alpha1] using h2
  have h3' : (404 : ℝ) / 1023 ≤ b := by simpa [Work.EL.alpha2] using h3
  have hθ1' : (371 : ℝ) / 1023 < θ := by simpa [Work.EL.alpha1] using hθ1
  have hθ2' : θ < (404 : ℝ) / 1023 := by simpa [Work.EL.alpha2] using hθ2
  have harc : armArcOf nearA 5 (armPairOf nearA kA (a, b) 0) = (b, a + 1) := by
    show armArcOf nearA 5 (a, b) = (b, a + 1)
    rw [W0_arc_near 5 (by decide) a b]
    have hf : Int.fract (a - b) = a - b + 1 :=
      armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
    rw [hf]
    exact Prod.ext rfl (by ring)
  rw [harc]
  have hfa : Int.fract (θ - (a + 1)) = θ - a :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
  have hfb : Int.fract (b - (a + 1)) = b - a :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
  simp only [Work.EL.InArc, Work.EL.arcLen, hfa, hfb]
  constructor <;> linarith

theorem W0_case_one (a b θ : ℝ) (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63)
    (hθ1 : Work.EL.alpha1 < θ) (hθ2 : θ < Work.EL.alpha2) :
    Work.EL.InArc θ (armArcOf nearA 4 (armPairOf nearA kA (a, b) 1)).2
      (armArcOf nearA 4 (armPairOf nearA kA (a, b) 1)).1 := by
  have hAB : Work.EL.alpha1 < Work.EL.alpha2 := W0_alpha1_lt_alpha2
  have hA1 : Work.EL.alpha1 < 1 := W0_alpha1_lt_one
  have h2' : a ≤ (371 : ℝ) / 1023 := by simpa [Work.EL.alpha1] using h2
  have h3' : (404 : ℝ) / 1023 ≤ b := by simpa [Work.EL.alpha2] using h3
  have hθ1' : (371 : ℝ) / 1023 < θ := by simpa [Work.EL.alpha1] using hθ1
  have hθ2' : θ < (404 : ℝ) / 1023 := by simpa [Work.EL.alpha2] using hθ2
  have harc : armArcOf nearA 4 (armPairOf nearA kA (a, b) 1) = (1 - a / 2, (3 - b) / 2) := by
    rw [W0_pair_one a b h1 h2 h3 h4, W0_arc_far 4 (by decide) (1 - a / 2) ((1 - b) / 2)]
    have hf : Int.fract ((1 - b) / 2 - (1 - a / 2)) = (1 - b) / 2 - (1 - a / 2) + 1 :=
      armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
    rw [hf]
    exact Prod.ext rfl (by ring)
  rw [harc]
  have hfa : Int.fract (θ - (3 - b) / 2) = θ + (b - 1) / 2 :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
  have hfb : Int.fract ((1 - a / 2) - (3 - b) / 2) = (b - a + 1) / 2 :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
  simp only [Work.EL.InArc, Work.EL.arcLen, hfa, hfb]
  constructor <;> linarith

theorem W0_case_two (a b θ : ℝ) (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63)
    (hθ1 : Work.EL.alpha1 < θ) (hθ2 : θ < Work.EL.alpha2) :
    Work.EL.InArc θ (armArcOf nearA 3 (armPairOf nearA kA (a, b) 2)).2
      (armArcOf nearA 3 (armPairOf nearA kA (a, b) 2)).1 := by
  have hAB : Work.EL.alpha1 < Work.EL.alpha2 := W0_alpha1_lt_alpha2
  have hA1 : Work.EL.alpha1 < 1 := W0_alpha1_lt_one
  have h2' : a ≤ (371 : ℝ) / 1023 := by simpa [Work.EL.alpha1] using h2
  have h3' : (404 : ℝ) / 1023 ≤ b := by simpa [Work.EL.alpha2] using h3
  have hθ1' : (371 : ℝ) / 1023 < θ := by simpa [Work.EL.alpha1] using hθ1
  have hθ2' : θ < (404 : ℝ) / 1023 := by simpa [Work.EL.alpha2] using hθ2
  have harc : armArcOf nearA 3 (armPairOf nearA kA (a, b) 2)
      = (1 / 2 + a / 4, 5 / 4 + b / 4) := by
    rw [W0_pair_two a b h1 h2 h3 h4, W0_arc_near 3 (by decide) ((1 + b) / 4) (1 / 2 + a / 4)]
    have hf : Int.fract ((1 + b) / 4 - (1 / 2 + a / 4))
        = (1 + b) / 4 - (1 / 2 + a / 4) + 1 :=
      armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
    rw [hf]
    exact Prod.ext rfl (by ring)
  rw [harc]
  have hfa : Int.fract (θ - (5 / 4 + b / 4)) = θ - 1 / 4 - b / 4 :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
  have hfb : Int.fract ((1 / 2 + a / 4) - (5 / 4 + b / 4)) = (a - b + 1) / 4 :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
  simp only [Work.EL.InArc, Work.EL.arcLen, hfa, hfb]
  constructor <;> linarith

theorem W0_case_three (a b θ : ℝ) (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63)
    (hθ1 : Work.EL.alpha1 < θ) (hθ2 : θ < Work.EL.alpha2) :
    Work.EL.InArc θ (armArcOf nearA 2 (armPairOf nearA kA (a, b) 3)).2
      (armArcOf nearA 2 (armPairOf nearA kA (a, b) 3)).1 := by
  have hAB : Work.EL.alpha1 < Work.EL.alpha2 := W0_alpha1_lt_alpha2
  have hA1 : Work.EL.alpha1 < 1 := W0_alpha1_lt_one
  have h2' : a ≤ (371 : ℝ) / 1023 := by simpa [Work.EL.alpha1] using h2
  have h3' : (404 : ℝ) / 1023 ≤ b := by simpa [Work.EL.alpha2] using h3
  have hθ1' : (371 : ℝ) / 1023 < θ := by simpa [Work.EL.alpha1] using hθ1
  have hθ2' : θ < (404 : ℝ) / 1023 := by simpa [Work.EL.alpha2] using hθ2
  have harc : armArcOf nearA 2 (armPairOf nearA kA (a, b) 3)
      = (7 / 8 - b / 8, 5 / 4 - a / 8) := by
    rw [W0_pair_three a b h1 h2 h3 h4, W0_arc_far 2 (by decide) (7 / 8 - b / 8) (1 / 4 - a / 8)]
    have hf : Int.fract ((1 / 4 - a / 8) - (7 / 8 - b / 8))
        = (1 / 4 - a / 8) - (7 / 8 - b / 8) + 1 :=
      armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
    rw [hf]
    exact Prod.ext rfl (by ring)
  rw [harc]
  have hfa : Int.fract (θ - (5 / 4 - a / 8)) = θ - 1 / 4 + a / 8 :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
  have hfb : Int.fract ((7 / 8 - b / 8) - (5 / 4 - a / 8)) = (a - b + 5) / 8 :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
  simp only [Work.EL.InArc, Work.EL.arcLen, hfa, hfb]
  constructor <;> linarith

theorem W0_case_four (a b θ : ℝ) (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63)
    (hθ1 : Work.EL.alpha1 < θ) (hθ2 : θ < Work.EL.alpha2) :
    Work.EL.InArc θ (armArcOf nearA 1 (armPairOf nearA kA (a, b) 4)).2
      (armArcOf nearA 1 (armPairOf nearA kA (a, b) 4)).1 := by
  have hAB : Work.EL.alpha1 < Work.EL.alpha2 := W0_alpha1_lt_alpha2
  have hA1 : Work.EL.alpha1 < 1 := W0_alpha1_lt_one
  have h2' : a ≤ (371 : ℝ) / 1023 := by simpa [Work.EL.alpha1] using h2
  have h3' : (404 : ℝ) / 1023 ≤ b := by simpa [Work.EL.alpha2] using h3
  have hθ1' : (371 : ℝ) / 1023 < θ := by simpa [Work.EL.alpha1] using hθ1
  have hθ2' : θ < (404 : ℝ) / 1023 := by simpa [Work.EL.alpha2] using hθ2
  have harc : armArcOf nearA 1 (armPairOf nearA kA (a, b) 4)
      = (3 / 8 + a / 16, 9 / 16 + b / 16) := by
    rw [W0_pair_four a b h1 h2 h3 h4,
      W0_arc_far 1 (by decide) (3 / 8 + a / 16) (9 / 16 + b / 16)]
    have hf : Int.fract ((9 / 16 + b / 16) - (3 / 8 + a / 16))
        = (9 / 16 + b / 16) - (3 / 8 + a / 16) :=
      armA_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 (by push_cast; ring)
    rw [hf]
    exact Prod.ext rfl (by ring)
  rw [harc]
  have hfa : Int.fract (θ - (9 / 16 + b / 16)) = θ + 7 / 16 - b / 16 :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
  have hfb : Int.fract ((3 / 8 + a / 16) - (9 / 16 + b / 16)) = (a - b + 13) / 16 :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
  simp only [Work.EL.InArc, Work.EL.arcLen, hfa, hfb]
  constructor <;> linarith

theorem W0_case_five (a b θ : ℝ) (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63)
    (hθ1 : Work.EL.alpha1 < θ) (hθ2 : θ < Work.EL.alpha2) :
    Work.EL.InArc θ (armArcOf nearA 0 (armPairOf nearA kA (a, b) 5)).2
      (armArcOf nearA 0 (armPairOf nearA kA (a, b) 5)).1 := by
  have hAB : Work.EL.alpha1 < Work.EL.alpha2 := W0_alpha1_lt_alpha2
  have hA1 : Work.EL.alpha1 < 1 := W0_alpha1_lt_one
  have h2' : a ≤ (371 : ℝ) / 1023 := by simpa [Work.EL.alpha1] using h2
  have h3' : (404 : ℝ) / 1023 ≤ b := by simpa [Work.EL.alpha2] using h3
  have hθ1' : (371 : ℝ) / 1023 < θ := by simpa [Work.EL.alpha1] using hθ1
  have hθ2' : θ < (404 : ℝ) / 1023 := by simpa [Work.EL.alpha2] using hθ2
  have harc : armArcOf nearA 0 (armPairOf nearA kA (a, b) 5)
      = (7 / 32 - b / 32, 5 / 16 - a / 32) := by
    rw [W0_pair_five a b h1 h2 h3 h4,
      W0_arc_far 0 (by decide) (7 / 32 - b / 32) (5 / 16 - a / 32)]
    have hf : Int.fract ((5 / 16 - a / 32) - (7 / 32 - b / 32))
        = (5 / 16 - a / 32) - (7 / 32 - b / 32) :=
      armA_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 (by push_cast; ring)
    rw [hf]
    exact Prod.ext rfl (by ring)
  rw [harc]
  have hfa : Int.fract (θ - (5 / 16 - a / 32)) = θ - 5 / 16 + a / 32 :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 (by push_cast; ring)
  have hfb : Int.fract ((7 / 32 - b / 32) - (5 / 16 - a / 32)) = (a - b + 29) / 32 :=
    armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) (by push_cast; ring)
  simp only [Work.EL.InArc, Work.EL.arcLen, hfa, hfb]
  constructor <;> linarith

/-! ## The generic case split -/

theorem armA_W0_gen (t : ℕ) (ht : t < 6) (a b θ : ℝ)
    (h1 : (22 / 63 : ℝ) ≤ a) (h2 : a ≤ Work.EL.alpha1)
    (h3 : Work.EL.alpha2 ≤ b) (h4 : b ≤ 25 / 63)
    (hθ1 : Work.EL.alpha1 < θ) (hθ2 : θ < Work.EL.alpha2) :
    Work.EL.InArc θ (armArcOf nearA (5 - t) (armPairOf nearA kA (a, b) t)).2
      (armArcOf nearA (5 - t) (armPairOf nearA kA (a, b) t)).1 := by
  interval_cases t <;>
    first
      | exact W0_case_zero a b θ h1 h2 h3 h4 hθ1 hθ2
      | exact W0_case_one a b θ h1 h2 h3 h4 hθ1 hθ2
      | exact W0_case_two a b θ h1 h2 h3 h4 hθ1 hθ2
      | exact W0_case_three a b θ h1 h2 h3 h4 hθ1 hθ2
      | exact W0_case_four a b θ h1 h2 h3 h4 hθ1 hθ2
      | exact W0_case_five a b θ h1 h2 h3 h4 hθ1 hθ2

/-! ## The target -/

theorem armA_W0 {c : ℂ} (n t : ℕ) (ht : t < 6) : ∀ θ : ℝ, Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ (Work.ELNest.armArcOf Work.ELNest.nearA (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (Work.ELNest.armA1 n, Work.ELNest.armA2 n) t)).2 (Work.ELNest.armArcOf Work.ELNest.nearA (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (Work.ELNest.armA1 n, Work.ELNest.armA2 n) t)).1 := by
  intro θ hθ
  obtain ⟨ha1, ha2⟩ := W0_armA1_mem n
  obtain ⟨hb1, hb2⟩ := W0_armA2_mem n
  have hu0 : 0 < Int.fract (θ - Work.EL.alpha1) := hθ.1
  have hu1 : Int.fract (θ - Work.EL.alpha1) < 1 / 31 := by
    have h := hθ.2
    rwa [W0_arcLen_alpha1_alpha2] at h
  obtain ⟨z, hz⟩ := (Int.fract_eq_iff.mp
    (rfl : Int.fract (θ - Work.EL.alpha1) = Int.fract (θ - Work.EL.alpha1))).2.2
  have hshift : ∀ X : ℝ,
      Int.fract (θ - X) = Int.fract (Work.EL.alpha1 + Int.fract (θ - Work.EL.alpha1) - X) := by
    intro X
    refine Int.fract_eq_fract.mpr ⟨z, ?_⟩
    linarith
  have hsub : Work.EL.alpha2 - Work.EL.alpha1 = 1 / 31 := by
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hkey := armA_W0_gen t ht (armA1 n) (armA2 n)
    (Work.EL.alpha1 + Int.fract (θ - Work.EL.alpha1)) ha1 ha2 hb1 hb2
    (by linarith) (by linarith)
  have hA : Int.fract (θ - (armArcOf nearA (5 - t)
        (armPairOf nearA kA (armA1 n, armA2 n) t)).2)
      = Int.fract (Work.EL.alpha1 + Int.fract (θ - Work.EL.alpha1) - (armArcOf nearA (5 - t)
        (armPairOf nearA kA (armA1 n, armA2 n) t)).2) :=
    hshift _
  exact ⟨by rw [hA]; exact hkey.1, by rw [hA]; exact hkey.2⟩

end Work.ELAssembly
