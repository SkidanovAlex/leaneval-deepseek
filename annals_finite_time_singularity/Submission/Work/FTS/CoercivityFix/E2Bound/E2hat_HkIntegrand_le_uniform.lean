import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.QuadAux
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkIntegrand_add_le
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.CoercivityFix.E2Bound.zop_phi_bound
import Submission.Work.FTS.CoercivityFix.E2Bound.HkIntegrand_zmul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.E2Bound

open scoped Real Topology

set_option autoImplicit false

/-! # The `ℋⁿ`-bound for the `D_z`-commutator defect `Ê₂`

`Work.FTS.CoercivityFix.E2hat f = (2zf + 3z·D_θf)/(1+z)² = 2·φ·f + 3·φ·D_θf` with
`φ(z) = z/(1+z)²`.  This file proves the *pointwise* slot bound

`HkIntegrand α n (Ê₂ f) z θ ≤ C · (HkIntegrand α n f z θ + HkIntegrand α n (D_θ f) z θ)`

with `C` depending only on `n` (in fact `C = 18·κ_n·(1+K_n)² + 1`, where `κ_n` is the
multiplier constant of `HkIntegrand_zmul_le` and `K_n` the uniform bound on the `D_z`-iterates
of `φ`), on the open quadrant `z > 0`, `0 < θ < π/2`.

The three ingredients, all independent of each other:

* `HkIntegrand_zmul_le`: for a multiplier `a = a(z)` whose `D_z`-iterates up to order `n` are
  bounded by `K` on `(0,∞)`, `HkIntegrand α n (a·f) ≤ C(n)·(1+K)²·HkIntegrand α n f`
  (the Leibniz bookkeeping);
* `zop_phi_bound`: the specific bound for `φ(z) = z/(1+z)²`;
* the subadditivity `HkIntegrand_add_le` / homogeneity `HkIntegrand_const_mul` of the
  integrand, which split `Ê₂ f = 2·(φ·f) + 3·(φ·D_θ f)` and scale the two pieces.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

/-! ## The `z`-only multiplier `φ(z) = z/(1+z)²` -/

/-- `φ(z) = z/(1+z)²` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_zDiv : ContDiffOn ℝ Work.Stability.smoothOrder
    (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi (-1)) := by
  refine ContDiffOn.div (by fun_prop) (by fun_prop) ?_
  intro z hz
  simp only [Set.mem_Ioi] at hz
  exact pow_ne_zero 2 (by linarith)

/-- A function of `z` alone, `C^∞` on `(-1,∞)`, is `SmoothQuad` as a function of `(z,θ)`. -/
theorem smoothQuad_of_zOnly {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi (-1))) :
    Work.FTS.LocData.SmoothQuad (fun z _ : ℝ => a z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun z _ : ℝ => a z))
    (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2))
  have h : Function.uncurry (fun z _ : ℝ => a z) = fun p : ℝ × ℝ => a p.1 := rfl
  rw [h]
  exact ha.comp contDiffOn_fst (fun p hp => hp.1)

/-- `φ(z) = z/(1+z)²` is `SmoothQuad`. -/
theorem smoothQuad_zDiv : Work.FTS.LocData.SmoothQuad (fun z _ : ℝ => z / (1 + z) ^ 2) :=
  smoothQuad_of_zOnly contDiffOn_zDiv

/-! ## The explicit form of the defect -/

/-- **The defect as a `z`-multiplier.**  `Ê₂ f = 2·φ·f + 3·φ·D_θf` with `φ(z) = z/(1+z)²`. -/
theorem E2hat_eq_zmul (f : ℝ → ℝ → ℝ) :
    Work.FTS.CoercivityFix.E2hat f
      = fun z θ => 2 * ((z / (1 + z) ^ 2) * f z θ)
          + 3 * ((z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ) := by
  funext z θ
  rw [Work.FTS.CoercivityFix.E2hat_eq]
  field_simp

/-- **The `ℋⁿ`-slot bound for the `D_z`-commutator defect.**

`HkIntegrand α n (Ê₂ f) ≤ C·(HkIntegrand α n f + HkIntegrand α n (D_θ f))` pointwise on the
open quadrant, with `C = 18·κ_n·(1+K_n)² + 1` (`κ_n` from the multiplier estimate
`HkIntegrand_zmul_uniform`, `K_n` from `zop_phi_bound`).  The proof splits
`Ê₂ f = 2·(φ·f) + 3·(φ·D_θ f)` with the subadditivity of the integrand, contracts each of the
two terms by the multiplier estimate for `φ(z) = z/(1+z)²`, and adds up. -/
theorem E2hat_HkIntegrand_le_uniform (α : ℝ) (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad f → ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ ≤ C * (Work.Spaces.HkIntegrand α n f z θ + Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ) := by
  obtain ⟨Cm, hCmpos, hCm⟩ := HkIntegrand_zmul_le α n
  obtain ⟨K, hK0, hKb⟩ := zop_phi_bound n
  refine ⟨18 * Cm * (1 + K) ^ 2 + 1, ?_, ?_⟩
  · have h : 0 ≤ Cm * (1 + K) ^ 2 := mul_nonneg hCmpos.le (sq_nonneg _)
    linarith
  · intro f hf z hz θ hθ
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    -- `D_θ f` is again `SmoothQuad`
    have hDth : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) := by
      simpa using Work.FTS.LocData.SmoothQuad.DthIter hf 1
    -- the explicit `z`-multiplier form of the defect
    rw [E2hat_eq_zmul f]
    -- the two summands are `SmoothQuad`
    have hA : Work.FTS.LocData.SmoothQuad
        (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) :=
      Work.FTS.LocData.smoothQuad_const_mul 2
        (Work.FTS.LocData.smoothQuad_mul smoothQuad_zDiv hf)
    have hB : Work.FTS.LocData.SmoothQuad
        (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) :=
      Work.FTS.LocData.smoothQuad_const_mul 3
        (Work.FTS.LocData.smoothQuad_mul smoothQuad_zDiv hDth)
    -- subadditivity of the integrand on the sum of the two `SmoothQuad` summands
    have h1 := Work.FTS.LocData.HkIntegrand_add_le α n hA hB hzIz hθI
    have h1' : Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)
            + 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α n
            (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) z θ
          + 2 * Work.Spaces.HkIntegrand α n
            (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ := by
      simpa only [Pi.add_apply] using h1
    -- homogeneity in the amplitude
    have h2 := Work.FTS.LocData.HkIntegrand_const_mul α n 2
      (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
    have h3 := Work.FTS.LocData.HkIntegrand_const_mul α n 3
      (fun z θ : ℝ => (z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ) z θ
    norm_num at h2 h3
    -- the multiplier estimate for `φ`, applied to `f` and to `D_θ f`
    have h4 := hCm (fun z : ℝ => z / (1 + z) ^ 2) K hK0 hKb smoothQuad_zDiv f hf z hz θ hθ
    have h5 := hCm (fun z : ℝ => z / (1 + z) ^ 2) K hK0 hKb smoothQuad_zDiv
      (Work.Spaces.Dth f) hDth z hz θ hθ
    -- bookkeeping
    have hX : 0 ≤ Work.Spaces.HkIntegrand α n f z θ := Work.Spaces.HkIntegrand_nonneg α n f z θ
    have hY : 0 ≤ Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
      Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ
    have hK1 : (0 : ℝ) ≤ (1 + K) ^ 2 := by positivity
    have hC0 : 0 ≤ Cm * (1 + K) ^ 2 := mul_nonneg hCmpos.le hK1
    have hCX : 0 ≤ Cm * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ := mul_nonneg hC0 hX
    have hCY : 0 ≤ Cm * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
      mul_nonneg hC0 hY
    nlinarith [h1', h2, h3, h4, h5, hX, hY, hCX, hCY]

end Work.FTS.CoercivityFix.E2Bound
