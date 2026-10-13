import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.ClassC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology MeasureTheory

namespace Work.FTS.StrongEps.E4R3.Decay3Aux

set_option autoImplicit false

/-- `α ^ (-(1/2)) ≥ 0` for **every** real `α`.  For `α ≥ 0` this is `Real.rpow_nonneg`; for
`α < 0` the Mathlib definition of `rpow` is `exp (log α * y) * cos (y π)`, and the factor
`cos (-(1/2) π) = 0`.  (No positivity of `α` is available in `ellPkg_mono`, unlike in its
sibling `starPkg_mono`.) -/
theorem rpow_neg_half_nonneg (α : ℝ) : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
  by_cases hα : 0 ≤ α
  · exact Real.rpow_nonneg hα _
  · rw [Real.rpow_def_of_neg (lt_of_not_ge hα)]
    have hc : Real.cos (-(1 / 2 : ℝ) * Real.pi) = 0 := by
      rw [show -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
    rw [hc, mul_zero]

/-- Monotonicity of the elliptic package in the constant `Ce`.  Every `Ce`-occurrence in
`EllPkgGo`/`EllPkgK` is a single estimate of the shape `A ≤ Ce * B` with `B ≥ 0`
(`B = Xn α g`, `B = HkNorm α k g`, or `B = α ^ (-(1/2)) * Xn α g`); the non-estimate fields
are `Ce`-free.  Hence `Ce ≤ Ce'` transports the whole package. -/
theorem ellPkg_mono {α Ce Ce' : ℝ} (h : Ce ≤ Ce') {k : ℕ} {g Φg : Work.FTS.Galerkin.Fn}
    (hp : Work.FTS.VocabO.EllPkgGo α Ce g Φg ∧ Work.FTS.ClassC.EllPkgK α k Ce g Φg) :
    Work.FTS.VocabO.EllPkgGo α Ce' g Φg ∧ Work.FTS.ClassC.EllPkgK α k Ce' g Φg := by
  obtain ⟨hGo, hK⟩ := hp
  have hA : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := rpow_neg_half_nonneg α
  have hXn : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hHk : (0 : ℝ) ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  refine ⟨{ hGo with
    R := ⟨hGo.R.1, le_trans hGo.R.2 (mul_le_mul_of_nonneg_right h hXn)⟩,
    U := ⟨hGo.U.1, le_trans hGo.U.2 (mul_le_mul_of_nonneg_right h hXn)⟩,
    V := ⟨hGo.V.1, le_trans hGo.V.2 (mul_le_mul_of_nonneg_right h hXn)⟩,
    Vth := ⟨hGo.Vth.1,
      le_trans hGo.Vth.2
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hA) hXn)⟩ }, ?_⟩
  exact { hK with
    R := ⟨hK.R.1, le_trans hK.R.2 (mul_le_mul_of_nonneg_right h hHk)⟩,
    U := ⟨hK.U.1, le_trans hK.U.2 (mul_le_mul_of_nonneg_right h hHk)⟩,
    V := ⟨hK.V.1, le_trans hK.V.2 (mul_le_mul_of_nonneg_right h hHk)⟩ }

end Work.FTS.StrongEps.E4R3.Decay3Aux
