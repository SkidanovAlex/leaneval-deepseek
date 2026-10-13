/-
# `Work.FTS.EllSol.EllPkgAux.MollKdAux` — the two-dimensional mollifier is smooth with compact support

`Kd δ ε (t,s) = sKer δ t * sKer ε s` is the two-dimensional kernel whose convolution with the
uncurried integrand `Hxy` reproduces `zmoll` (see `MollConvDefs`).  For the convolution
calculus (`HasCompactSupport.contDiff_convolution_right`) it must be `C^∞` and compactly
supported, which is what this module provides.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Unfolded form of the mollifying kernel. -/
theorem sKer_eq (ε : ℝ) : Work.FTS.EllSol.PkgK5.K5c.sKer ε
    = fun t : ℝ => (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
        Real.smoothTransition (1 - (t / ε) ^ 2) := by
  funext t
  simp only [Work.FTS.EllSol.PkgK5.K5c.sKer, Work.FTS.EllSol.PkgK5.K5c.sBump]

/-- The mollifying kernel `sKer ε` is `C^∞` (it is a rescaled smooth bump). -/
theorem sKer_contDiff (ε : ℝ) (n : ℕ) :
    ContDiff ℝ n (Work.FTS.EllSol.PkgK5.K5c.sKer ε) := by
  rw [sKer_eq ε]
  fun_prop

/-- Unfolded form of the two-dimensional mollifier. -/
theorem Kd_eq (δ ε : ℝ) : Kd δ ε = fun p : ℝ × ℝ =>
    (δ * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
        Real.smoothTransition (1 - (p.1 / δ) ^ 2)
      * ((ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
        Real.smoothTransition (1 - (p.2 / ε) ^ 2)) := by
  funext p
  simp only [Kd, Work.FTS.EllSol.PkgK5.K5c.sKer, Work.FTS.EllSol.PkgK5.K5c.sBump]

/-- The two-dimensional mollifier is `C^∞`. -/
theorem Kd_contDiff (δ ε : ℝ) (n : ℕ) : ContDiff ℝ n (Kd δ ε) := by
  rw [Kd_eq δ ε]
  fun_prop

/-- The two-dimensional mollifier is compactly supported (its support lies in
`[-δ,δ] × [-ε,ε]`). -/
theorem Kd_hasCompactSupport (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    HasCompactSupport (Kd δ ε) := by
  refine HasCompactSupport.intro (K := Set.Icc (-δ) δ ×ˢ Set.Icc (-ε) ε)
    (isCompact_Icc.prod isCompact_Icc) ?_
  rintro ⟨t, s⟩ hp
  simp only [Set.mem_prod, Set.mem_Icc, not_and_or, not_le] at hp
  rcases hp with (h | h) | (h | h)
  · have ht : δ ≤ |t| := by
      have h1 : δ ≤ -t := by linarith
      exact le_trans h1 (neg_le_abs t)
    show Work.FTS.EllSol.PkgK5.K5c.sKer δ t * Work.FTS.EllSol.PkgK5.K5c.sKer ε s = 0
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ ht, zero_mul]
  · have ht : δ ≤ |t| := by
      have h1 : δ ≤ t := le_of_lt h
      exact le_trans h1 (le_abs_self t)
    show Work.FTS.EllSol.PkgK5.K5c.sKer δ t * Work.FTS.EllSol.PkgK5.K5c.sKer ε s = 0
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ ht, zero_mul]
  · have hs : ε ≤ |s| := by
      have h1 : ε ≤ -s := by linarith
      exact le_trans h1 (neg_le_abs s)
    show Work.FTS.EllSol.PkgK5.K5c.sKer δ t * Work.FTS.EllSol.PkgK5.K5c.sKer ε s = 0
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε hs, mul_zero]
  · have hs : ε ≤ |s| := by
      have h1 : ε ≤ s := le_of_lt h
      exact le_trans h1 (le_abs_self s)
    show Work.FTS.EllSol.PkgK5.K5c.sKer δ t * Work.FTS.EllSol.PkgK5.K5c.sKer ε s = 0
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε hs, mul_zero]

end Work.FTS.EllSol.EllPkgAux
