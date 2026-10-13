/-
# `FTS/PhiStar/StarPkgo2Aux/F0EPU.lean` — the flat bound for `EPU α Y = ∂_θ𝒰(Φ̃_*)`

`Work.FTS.PhiStar.F0 n K f` (see `CoreAux/Defs.lean`) is the flat class: all the mixed
weighted derivatives `(z+1)^k ∂_z^k D_θ^i f` with `k + i ≤ n` are bounded by `K` on the open
quadrant `Q0 = (0,∞) × (0,π/2)`.  `Fb n K f` is the pair `F0 n K f`, `F0 n K (∂_θ f)`.

The field `EPU α Y` of `CoreAux/FieldsDefs.lean` is

`EPU α Y = - ( 2 cos 2θ · (z/(z+1)) · W₁ + sin 2θ · (z/(z+1)) · (3∂_θY + α(∂_θY/(z+1) + z∂_z∂_θY)) )`

with `W₁ = 3Y + α(Y/(z+1) + z∂_zY)`.  Every factor is a flat-class function: the angular and
radial coefficients `cos 2θ, sin 2θ, z/(z+1), 1/(z+1)` are given at level `6` with constant
`A ≥ 1`, and `Y`, `∂_θY` are given at level `6` with constant `A·K` (that is the hypothesis
`Fb 6 (A*K) Y`).  Since `∂_z` costs one order (`F0_zpz`) and products cost the factor `2^n`
(`F0_mul`), the level drops from `6` to `5`, and the constant accumulates a factor
`A^4 · K · (α+1)`.

This is the `K`-form of the bound (`CoreAux/F0_EPU_bound.lean` proves the weaker `K+1`-form):
the conclusion is *linear* in `K`, which is what the consumers need, because in the intended
application `K = Cs·α` is small when `α` is small.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_mul
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_basic
import Submission.Work.FTS.PhiStar.CoreAux.Fb_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.PhiStar.StarPkgo2Aux

open Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Small closures of the smoothness class `SmoothOpen` -/

/-- `SmoothOpen` is closed under pointwise sums. -/
private theorem SmoothOpen_add {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) :=
  ContDiffOn.add hf hg

/-- `SmoothOpen` is closed under pointwise products. -/
private theorem SmoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) :=
  ContDiffOn.mul hf hg

/-- Constant functions are `SmoothOpen`. -/
private theorem SmoothOpen_const (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => c) :=
  contDiffOn_const

/-- `cos(2θ)` is `C^∞` on the open quadrant. -/
private theorem SmoothOpen_cos_two :
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.cos (2 * θ)) := by
  have h1 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (2 : ℝ) * p.2) :=
    contDiff_const.mul contDiff_snd
  have h2 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.cos (2 * p.2)) :=
    Real.contDiff_cos.comp h1
  exact h2.contDiffOn

/-- `sin(2θ)` is `C^∞` on the open quadrant. -/
private theorem SmoothOpen_sin_two :
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) := by
  have h1 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (2 : ℝ) * p.2) :=
    contDiff_const.mul contDiff_snd
  have h2 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.contDiff_sin.comp h1
  exact h2.contDiffOn

/-- `z ↦ (z+1)⁻¹` is `C^∞` on the open quadrant. -/
private theorem SmoothOpen_inv_one_add :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (z + 1)⁻¹) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 + 1)
      Work.FTS.EllipticEst.Q0 :=
    (contDiff_fst.add contDiff_const).contDiffOn
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (p.1 + 1)⁻¹)
      Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.inv h1 ?_
    intro p hp
    have hz : (0 : ℝ) < p.1 := hp.1
    have hz1 : (0 : ℝ) < p.1 + 1 := by linarith
    exact ne_of_gt hz1
  exact h2

/-- `z ↦ z/(z+1)` is `C^∞` on the open quadrant. -/
private theorem SmoothOpen_z_div :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (z + 1)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      Work.FTS.EllipticEst.Q0 :=
    contDiff_fst.contDiffOn
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 + 1)
      Work.FTS.EllipticEst.Q0 :=
    (contDiff_fst.add contDiff_const).contDiffOn
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 / (p.1 + 1))
      Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.div h1 h2 ?_
    intro p hp
    have hz : (0 : ℝ) < p.1 := hp.1
    have hz1 : (0 : ℝ) < p.1 + 1 := by linarith
    exact ne_of_gt hz1
  exact h3

/-! ## The flat calculus at the level needed here -/

/-- Products at level `5`: the constant of `F0_mul` is `2^5 = 32` there. -/
private theorem F0_mul5 {K K' : ℝ} {f g : ℝ → ℝ → ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hf : Work.FTS.PhiStar.F0 5 K f) (hg : Work.FTS.PhiStar.F0 5 K' g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ)
      ∧ Work.FTS.PhiStar.F0 5 (32 * K * K') (fun z θ => f z θ * g z θ) := by
  have h := F0_mul hK hK' hsf hsg hf hg
  have hpow : ((2 : ℝ) ^ 5 * K * K') = 32 * K * K' := by norm_num
  rw [hpow] at h
  exact ⟨SmoothOpen_mul hsf hsg, h⟩

/-- Sums at level `5`, carrying smoothness along. -/
private theorem F0_add5 {K K' : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hf : Work.FTS.PhiStar.F0 5 K f) (hg : Work.FTS.PhiStar.F0 5 K' g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ)
      ∧ Work.FTS.PhiStar.F0 5 (K + K') (fun z θ => f z θ + g z θ) :=
  ⟨SmoothOpen_add hsf hsg, F0_add hsf hsg hf hg⟩

/-- `z ∂_z` drops one order and multiplies the constant by `6` at level `5`. -/
private theorem F0_zpz5 {K : ℝ} {f : ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.FTS.PhiStar.F0 6 K f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz f z θ)
      ∧ Work.FTS.PhiStar.F0 5 (6 * K) (fun z θ => z * Work.Spaces.pz f z θ) := by
  have h := F0_zpz (n := 5) hK hsf hf
  have h6 : ((5 : ℕ) : ℝ) + 1 = 6 := by norm_num
  refine ⟨hsf.Dz, h.mono (le_refl 5) ?_⟩
  show (((5 : ℕ) : ℝ) + 1) * K ≤ 6 * K
  rw [h6]

/-- Multiplication by a constant, with the constant `32 * |c|` at level `5`. -/
private theorem F0_const_mul5 {c K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.FTS.PhiStar.F0 5 K f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ)
      ∧ Work.FTS.PhiStar.F0 5 (32 * |c| * K) (fun z θ => c * f z θ) :=
  F0_mul5 (abs_nonneg c) hK (SmoothOpen_const c) hsf (F0.const 5 c) hf

/-- Multiplication by a nonnegative constant, with the constant `32 * c`. -/
private theorem F0_const_mul5_of_nonneg {c K : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    {f : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hf : Work.FTS.PhiStar.F0 5 K f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ)
      ∧ Work.FTS.PhiStar.F0 5 (32 * c * K) (fun z θ => c * f z θ) := by
  obtain ⟨hs, h⟩ := F0_const_mul5 (c := c) hK hsf hf
  rw [abs_of_nonneg hc] at h
  exact ⟨hs, h⟩

/-- Negation at level `5`, with the constant `32 * K`. -/
private theorem F0_neg5 {K : ℝ} {f : ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.FTS.PhiStar.F0 5 K f) :
    Work.FTS.PhiStar.F0 5 (32 * K) (fun z θ => - f z θ) := by
  obtain ⟨hs, h⟩ := F0_const_mul5 (c := (-1 : ℝ)) hK hsf hf
  have hone : (32 : ℝ) * |(-1 : ℝ)| * K = 32 * K := by
    have habs : |(-1 : ℝ)| = 1 := by rw [abs_neg, abs_one]
    rw [habs]; ring
  rw [hone] at h
  refine F0_congr (fun z θ _ _ _ => ?_) h
  ring

/-! ## The main bound -/

theorem F0EPU : ∃ C : ℝ, 0 < C ∧ ∀ (α K A : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 1 ≤ A →
    Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) →
    Work.FTS.PhiStar.Fb 6 (A * K) Y →
    Work.FTS.PhiStar.F0 5 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EPU α Y) := by
  refine ⟨10000000000, by norm_num, ?_⟩
  intro α K A Y hα hK hA hsY hsq hccs hcos hsin hz1 hinv hY
  -- elementary nonnegativity
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hL0 : (0 : ℝ) ≤ A * K := mul_nonneg hA0 hK
  have hAA0 : (0 : ℝ) ≤ A * A := mul_nonneg hA0 hA0
  have hX0 : (0 : ℝ) ≤ A ^ 2 * K := mul_nonneg (pow_nonneg hA0 2) hK
  -- smoothness of the two `Y`-blocks
  have hsPY : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Y) := hsY.pth
  -- the two coefficient functions rewritten in the `z + 1` shape
  have hz1c : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => z / (z + 1)) := by
    refine F0_congr ?_ hz1
    intro z θ hz hθ hθ'
    show z / (z + 1) = z / (1 + z)
    rw [add_comm z 1]
  have hinvc : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (z + 1)⁻¹) := by
    refine F0_congr ?_ hinv
    intro z θ hz hθ hθ'
    show (z + 1)⁻¹ = (1 + z)⁻¹
    rw [add_comm z 1]
  -- level-5 forms
  have hY5 : Work.FTS.PhiStar.F0 5 (A * K) Y := hY.f0.mono (by norm_num) le_rfl
  have hPY5 : Work.FTS.PhiStar.F0 5 (A * K) (Work.Spaces.pth Y) :=
    hY.fd.mono (by norm_num) le_rfl
  have hcos5 : Work.FTS.PhiStar.F0 5 A (fun _ θ : ℝ => Real.cos (2 * θ)) :=
    hcos.mono (by norm_num) le_rfl
  have hsin5 : Work.FTS.PhiStar.F0 5 A (fun _ θ : ℝ => Real.sin (2 * θ)) :=
    hsin.mono (by norm_num) le_rfl
  have hz1c5 : Work.FTS.PhiStar.F0 5 A (fun z _ : ℝ => z / (z + 1)) :=
    hz1c.mono (by norm_num) le_rfl
  have hinvc5 : Work.FTS.PhiStar.F0 5 A (fun z _ : ℝ => (z + 1)⁻¹) :=
    hinvc.mono (by norm_num) le_rfl
  -- the four `Y`-blocks appearing in `W₁` and in the angular bracket
  obtain ⟨hsV1, hV1⟩ := F0_mul5 hL0 hA0 hsY SmoothOpen_inv_one_add hY5 hinvc5
  obtain ⟨hsV2, hV2⟩ := F0_mul5 hL0 hA0 hsPY SmoothOpen_inv_one_add hPY5 hinvc5
  obtain ⟨hsV3, hV3⟩ := F0_zpz5 hL0 hsY hY.f0
  obtain ⟨hsV4, hV4⟩ := F0_zpz5 hL0 hsPY hY.fd
  obtain ⟨hsV5, hV5⟩ := F0_add5 hsV1 hsV3 hV1 hV3
  obtain ⟨hsV6, hV6⟩ := F0_add5 hsV2 hsV4 hV2 hV4
  have hV5c0 : (0 : ℝ) ≤ 32 * (A * K) * A + 6 * (A * K) := by
    have h1 : (0 : ℝ) ≤ 32 * (A * K) * A := mul_nonneg (mul_nonneg (by norm_num) hL0) hA0
    have h2 : (0 : ℝ) ≤ 6 * (A * K) := mul_nonneg (by norm_num) hL0
    linarith
  obtain ⟨hsV7, hV7⟩ := F0_const_mul5_of_nonneg (c := α) hα hV5c0 hsV5 hV5
  obtain ⟨hsV7d, hV7d⟩ := F0_const_mul5_of_nonneg (c := α) hα hV5c0 hsV6 hV6
  obtain ⟨hsV8, hV8⟩ := F0_const_mul5_of_nonneg (c := (3 : ℝ)) (by norm_num) hL0 hsY hY5
  obtain ⟨hsV8d, hV8d⟩ := F0_const_mul5_of_nonneg (c := (3 : ℝ)) (by norm_num) hL0 hsPY hPY5
  -- `W₁` and the angular bracket, at level `5`
  obtain ⟨hsW, hW⟩ := F0_add5 hsV8 hsV7 hV8 hV7
  obtain ⟨hsU, hU⟩ := F0_add5 hsV8d hsV7d hV8d hV7d
  -- the bound `Kw ≤ (96 + 1216α) A²K` for the common constant `Kw`
  have hA2le : A ≤ A ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hA hA0
    simpa [pow_two] using h
  have hAK : A * K ≤ A ^ 2 * K := mul_le_mul_of_nonneg_right hA2le hK
  have hinner : 32 * (A * K) * A + 6 * (A * K) ≤ 38 * (A ^ 2 * K) := by
    have h1 : 32 * (A * K) * A = 32 * (A ^ 2 * K) := by ring
    have h2 : 6 * (A * K) ≤ 6 * (A ^ 2 * K) :=
      mul_le_mul_of_nonneg_left hAK (by norm_num)
    rw [h1]
    linarith [h2]
  have hKw : 32 * 3 * (A * K) + 32 * α * (32 * (A * K) * A + 6 * (A * K))
      ≤ (96 + 1216 * α) * (A ^ 2 * K) := by
    have h8 : 32 * 3 * (A * K) ≤ 96 * (A ^ 2 * K) := by
      have h : (32 : ℝ) * 3 * (A * K) = 96 * (A * K) := by ring
      rw [h]
      exact mul_le_mul_of_nonneg_left hAK (by norm_num)
    have h32a : (0 : ℝ) ≤ 32 * α := by linarith
    have h3 : 32 * α * (32 * (A * K) * A + 6 * (A * K))
        ≤ 32 * α * (38 * (A ^ 2 * K)) :=
      mul_le_mul_of_nonneg_left hinner h32a
    have h3' : (32 : ℝ) * α * (38 * (A ^ 2 * K)) = 1216 * α * (A ^ 2 * K) := by ring
    rw [h3'] at h3
    have hsum := add_le_add h8 h3
    have heq : 96 * (A ^ 2 * K) + 1216 * α * (A ^ 2 * K)
        = (96 + 1216 * α) * (A ^ 2 * K) := by ring
    rw [heq] at hsum
    exact hsum
  have hKW : 32 * 3 * (A * K) + 32 * α * (32 * (A * K) * A + 6 * (A * K))
      ≤ 1312 * (α + 1) * (A ^ 2 * K) := by
    have hcoef : (96 + 1216 * α) ≤ 1312 * (α + 1) := by linarith
    have h2 := mul_le_mul_of_nonneg_right hcoef hX0
    calc 32 * 3 * (A * K) + 32 * α * (32 * (A * K) * A + 6 * (A * K))
        ≤ (96 + 1216 * α) * (A ^ 2 * K) := hKw
      _ ≤ 1312 * (α + 1) * (A ^ 2 * K) := h2
  have hW2 : Work.FTS.PhiStar.F0 5 (1312 * (α + 1) * (A ^ 2 * K))
      (fun z θ => 3 * Y z θ + α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ)) :=
    hW.mono (le_refl 5) hKW
  have hU2 : Work.FTS.PhiStar.F0 5 (1312 * (α + 1) * (A ^ 2 * K))
      (fun z θ => 3 * Work.Spaces.pth Y z θ
        + α * (Work.Spaces.pth Y z θ * (z + 1)⁻¹
          + z * Work.Spaces.pz (Work.Spaces.pth Y) z θ)) :=
    hU.mono (le_refl 5) hKW
  -- the coefficient factors
  have hAA32 : (0 : ℝ) ≤ 32 * A * A := mul_nonneg (mul_nonneg (by norm_num) hA0) hA0
  have hE1c0 : (0 : ℝ) ≤ 32 * 2 * (32 * A * A) := mul_nonneg (by norm_num) hAA32
  have hCα0 : (0 : ℝ) ≤ 1312 * (α + 1) * (A ^ 2 * K) := by
    have h1 : (0 : ℝ) ≤ 1312 * (α + 1) :=
      mul_nonneg (by norm_num) (by linarith : (0 : ℝ) ≤ α + 1)
    exact mul_nonneg h1 hX0
  obtain ⟨hsG1, hG1⟩ := F0_mul5 hA0 hA0 SmoothOpen_cos_two SmoothOpen_z_div hcos5 hz1c5
  obtain ⟨hsE1, hE1⟩ := F0_const_mul5_of_nonneg (c := (2 : ℝ)) (by norm_num) hAA32 hsG1 hG1
  obtain ⟨hsG2, hG2⟩ := F0_mul5 hA0 hA0 SmoothOpen_sin_two SmoothOpen_z_div hsin5 hz1c5
  -- the two big products
  obtain ⟨hsP, hP⟩ := F0_mul5 hE1c0 hCα0 hsE1 hsW hE1 hW2
  obtain ⟨hsQ, hQ⟩ := F0_mul5 hAA32 hCα0 hsG2 hsU hG2 hU2
  obtain ⟨hsPQ, hPQ⟩ := F0_add5 hsP hsQ hP hQ
  have hPQ0 : (0 : ℝ) ≤ 32 * (32 * 2 * (32 * A * A)) * (1312 * (α + 1) * (A ^ 2 * K))
      + 32 * (32 * A * A) * (1312 * (α + 1) * (A ^ 2 * K)) := by
    have h1 : (0 : ℝ) ≤ 32 * (32 * 2 * (32 * A * A)) * (1312 * (α + 1) * (A ^ 2 * K)) :=
      mul_nonneg (mul_nonneg (by norm_num) hE1c0) hCα0
    have h2 : (0 : ℝ) ≤ 32 * (32 * A * A) * (1312 * (α + 1) * (A ^ 2 * K)) :=
      mul_nonneg (mul_nonneg (by norm_num) hAA32) hCα0
    linarith
  have hN := F0_neg5 hPQ0 hsPQ hPQ
  -- unfold the definitions and identify the expression with `EPU α Y`
  have hFinal : Work.FTS.PhiStar.F0 5
      (32 * (32 * (32 * 2 * (32 * A * A)) * (1312 * (α + 1) * (A ^ 2 * K))
        + 32 * (32 * A * A) * (1312 * (α + 1) * (A ^ 2 * K))))
      (Work.FTS.PhiStar.EPU α Y) := by
    refine F0_congr ?_ hN
    intro z θ hz hθ hθ'
    simp only [Work.FTS.PhiStar.EPU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk,
      Work.Construction.s2, div_eq_mul_inv]
    ring
  -- the numerical bound on the accumulated constant
  have hbound : 32 * (32 * (32 * 2 * (32 * A * A)) * (1312 * (α + 1) * (A ^ 2 * K))
        + 32 * (32 * A * A) * (1312 * (α + 1) * (A ^ 2 * K)))
      ≤ 10000000000 * A ^ 4 * K * (α + 1) := by
    have hnn : (0 : ℝ) ≤ (α + 1) * A ^ 4 * K :=
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ α + 1) (pow_nonneg hA0 4)) hK
    have hbig : (2794455040 : ℝ) ≤ 10000000000 := by norm_num
    calc 32 * (32 * (32 * 2 * (32 * A * A)) * (1312 * (α + 1) * (A ^ 2 * K))
            + 32 * (32 * A * A) * (1312 * (α + 1) * (A ^ 2 * K)))
        = 2794455040 * ((α + 1) * A ^ 4 * K) := by ring
      _ ≤ 10000000000 * ((α + 1) * A ^ 4 * K) := mul_le_mul_of_nonneg_right hbig hnn
      _ = 10000000000 * A ^ 4 * K * (α + 1) := by ring
  exact hFinal.mono (le_refl 5) hbound

end Work.FTS.PhiStar.StarPkgo2Aux
