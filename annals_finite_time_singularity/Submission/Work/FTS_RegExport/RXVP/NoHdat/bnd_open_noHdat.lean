import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXVP3.bnd_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXVP.NoHdat

open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- `|c2m θ| ≤ 2` (`c2m θ = cos 2θ - sin²θ`). -/
private lemma abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m]
  have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h2 : |Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact Real.sin_sq_le_one θ
  linarith [abs_sub (Real.cos (2 * θ)) (Real.sin θ ^ 2)]

private lemma abs_add_three' (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h2 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith



end Work.FTS_RegExport.RXVP.NoHdat
