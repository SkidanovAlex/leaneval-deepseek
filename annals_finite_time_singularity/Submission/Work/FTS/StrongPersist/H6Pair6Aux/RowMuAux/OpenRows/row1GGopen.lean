import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows

theorem row1GGopen {CA : ℝ} (hCA : 0 < CA) {α Ce : ℝ} (hα : 0 < α)
    {f Ξg : Work.FTS.Galerkin.Fn} (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) (hEll : Work.FTS.VocabO.EllPkgGo α Ce f Ξg)
    (hsup : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg) z θ) ^ 2
        ≤ CA / (Work.Spaces.gam α - 1)
          * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
              (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg)) z θ') :
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1gg α f Ξg) ≤ ENNReal.ofReal
      (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * 6
        * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2) := by
  -- The angular slot data of the datum itself (`B₀ = f`, energy `Phi0 f`), in the open class.
  have hsl : Work.FTS.NonlinRows.Rl1.SlotData α f
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f) (Work.Spaces.HkSq α 4 f) :=
    slotData_open_g hα hso hmem
  refine Work.FTS.NonlinRows.Rl1.rowGG_engine (CA := CA) (α := α) (Ce := Ce) (g := f)
    (A := Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg))
    (B₀ := f) (Φ₀ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f)
    (N := Work.FTS.Nonlin.N1gg α f Ξg) (c := 6)
    hCA hα hEll.R.1.1 hEll.R.1.2 ?_ hsup hsl (fun _ _ => rfl) (by norm_num) ?_
  · calc Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg))
        ≤ Ce * Work.FTS.Nonlin.Xn α f := hEll.R.2
      _ ≤ max Ce 0 * Work.FTS.Nonlin.Xn α f :=
          mul_le_mul_of_nonneg_right (le_max_left Ce 0) (Work.Spaces.HkNorm_nonneg α 4 f)
  · intro r _ θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 :=
      Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.abs_K_le_three_aux θ
    have hA0 : 0 ≤ |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg) r θ| := abs_nonneg _
    have hg0 : 0 ≤ |f r θ| := abs_nonneg _
    have habs : |Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg)
          r θ * f r θ)|
        = 2 * (|Work.Spaces.K θ|
            * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg) r θ| * |f r θ|) := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    simp only [Work.FTS.Nonlin.N1gg]
    rw [habs]
    calc 2 * (|Work.Spaces.K θ|
            * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg) r θ| * |f r θ|)
        ≤ 2 * (3 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg) r θ| * |f r θ|) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hA0) hg0
      _ = 6 * (|Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg) r θ| * |f r θ|) := by
          ring

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows
