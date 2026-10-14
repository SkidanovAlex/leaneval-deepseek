import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.StrongEps.EpsE4Thr.Coer1Open
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalZero_zero
import Submission.Work.FTS_MuLamOK.Rows.Rl0Open
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.H2.T1Q.SliceIntQ
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rowsAuxT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

theorem rowsAuxT (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlinear.Pieces.AuxRows IP α K g Φs Φg := by
  obtain ⟨K1, hK1pos, hK1⟩ := Work.FTS.Nonlinear.Pieces.rak_bound
  obtain ⟨K2, hK2pos, hK2⟩ := Work.FTS_MuLamOK.Rows.Rl0Open
  obtain ⟨K3, hK3pos, hK3⟩ := Work.FTS_MuLamOK.Rows.Rl1Open Ce Cs
  obtain ⟨K4, hK4pos, hK4⟩ := Work.FTS_MuLamOK.Rows.Rl2Open
  refine ⟨K1 + K2 + K3 + K4 + 1, by linarith, ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  -- the fragment of `ClassC` consumed by the four rows
  have hso : Work.FTS.EllipticEst.SmoothOpen g := hctx.hg.reg
  have hmem : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hso 4 (by norm_num) hctx.hg.mem
  have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hctx.hs.toStarPkgo
  have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hB : 0 ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
    have h1 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
    have h2 : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hX
    have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hK1 hα hα1).trans (by linarith)
  · exact (hK2 hα hα1 hso hmem).trans (mul_le_mul_of_nonneg_right (by linarith) hB)
  · exact (hK3 hα hα1 hso hmem hs hell).trans (mul_le_mul_of_nonneg_right (by linarith) hB)
  · exact (hK4 hα hα1 hso hmem).trans (mul_le_mul_of_nonneg_right (by linarith) hX)

end Work.FTS.StrongEps.E4R3.N4C
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.CoerDataTO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The level-one Cauchy–Schwarz bound of `H1IP` on the open class.**  The frozen
`Assembly.H1IP_cs_Q` is stated on `RegQ α 1`; the sharp form
`Transfer.H1IP_cs_of_mem` needs only `HkMem α 1`, which `RegQo` supplies. -/
theorem H1IP_cs_Q_O : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → ∀ f g : Fn,
    RegQo α 1 f → RegQo α 1 g →
      |Work.Coercivity.H1IP α f g|
        ≤ C * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g :=
  ⟨10 ^ 22, by norm_num, fun α hα f g hf hg =>
    Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem α hα f g hf.2.1 hg.2.1⟩


end Work.FTS.StrongEps.EpsE4Thr
end
end
