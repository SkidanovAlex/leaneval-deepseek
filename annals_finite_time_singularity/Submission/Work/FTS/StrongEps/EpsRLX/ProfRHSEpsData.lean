import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.XDataClean
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSTraces
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

theorem ProfRHSEpsData {α C₀ Ce Cs B : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B) :
    ∃ R : ℝ, 0 < R ∧ ∀ {W : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W → Work.FTS.Nonlin.Xn α W ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 W ≤ B →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) ≤ R := by
  classical
  -- ## the profile data of `profRHS`: smooth, honest, of bounded `ℋ⁴`-size
  obtain ⟨CX, hCX, hX⟩ :=
    XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀) (B := B) hα hEll hstar hml hB
  -- ## the trace-to-`ε`-space transfer
  obtain ⟨C, hCpos, hTE⟩ := Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
  -- ## `γ - 1 = α/10 > 0`
  have hgam1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]
    linarith [hα.1]
  have hcoefnn : 0 ≤ C / (Work.Spaces.gam α - 1) ^ 2 :=
    div_nonneg hCpos.le (sq_nonneg _)
  refine ⟨C / (Work.Spaces.gam α - 1) ^ 2 * (CX + 1), ?_, ?_⟩
  · have h1 : 0 < (Work.Spaces.gam α - 1) ^ 2 := pow_pos hgam1 2
    positivity
  · intro W hW hXn hHk
    obtain ⟨hso, hmem4, hsq4⟩ := hX hW hXn hHk
    have hmem1 : Work.Spaces.HkMem α 1 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) :=
      Work.FTS.OpenPkg.HkMem_mono_open hso 1 (by norm_num) hmem4
    obtain ⟨ht1, ht2⟩ :=
      ProfRHSTraces (α := α) (Ce := Ce) (Cs := Cs) hα hW (hEll W hW).1 hstar
    obtain ⟨hem, hesq⟩ := hTE α hα _ hso hmem1 ht1 ht2
    refine ⟨hem, ?_⟩
    have hmono : Work.Spaces.HkSq α 1 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W)
        ≤ Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) :=
      Work.FTS.StrongLWP.HkSq_mono_of_mem (k := 4) (k' := 1) (by norm_num) hmem4
    calc Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W)
        ≤ C / (Work.Spaces.gam α - 1) ^ 2
            * Work.Spaces.HkSq α 1 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) := hesq
      _ ≤ C / (Work.Spaces.gam α - 1) ^ 2
            * Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) :=
          mul_le_mul_of_nonneg_left hmono hcoefnn
      _ ≤ C / (Work.Spaces.gam α - 1) ^ 2 * (CX + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoefnn
          linarith

end Work.FTS.StrongEps.EpsRLX
