import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-
The open-quadrant row 3 of the `gg`-block: `N₃^{gg} = -2α𝒱(Φ̃_g)D_zg`.

This is the `SmoothOpen`/`HkMem α 4`-instance of `Work.FTS.NonlinRows.Rl1.row3_gg`
(`Submission/Work/FTS/NonlinRows/Rl1/ggBounds.lean`), which is stated for the closed-quadrant
class `GalClass`.  The only row-dependent input of the engine `rowGG_engine` is the slot data
of `D_zf`, which at the open level is `slotData_open_dz`
(`Submission/Work/FTS/StrongPersist/H6Pair6Aux/RowMuAux/SlotDataOpen.lean`); everything else
(the coefficient data `hEll.V`, the pointwise factorisation
`|K θ · N r θ| ≤ 6α·|𝒱 r θ|·|D_zf r θ|` and the constant bookkeeping) is copied verbatim
from `row3_gg`.

The slot energy `Phi2 f r = ∫_θ (D_zf r θ)²` is definitionally the one the engine asks for,
and the factor `6` of the general engine is specialised here to `6α` (row factor `2` times the
`α` of `N₃^{gg}`).
-/
theorem row3GGopen {CA : ℝ} (hCA : 0 < CA) {α Ce : ℝ} (hα : 0 < α)
    {f Ξg : Work.FTS.Galerkin.Fn} (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) (hEll : Work.FTS.VocabO.EllPkgGo α Ce f Ξg)
    (hsup : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg) z θ) ^ 2
        ≤ CA / (Work.Spaces.gam α - 1)
          * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
              (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg)) z θ') :
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3gg α f Ξg) ≤ ENNReal.ofReal
      (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * (6 * α)
        * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2) := by
  obtain ⟨hVq, hVle⟩ := hEll.V
  have hsl : Work.FTS.NonlinRows.Rl1.SlotData α (Work.Spaces.Dz f)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi2 f) (Work.Spaces.HkSq α 4 f) :=
    slotData_open_dz hα hso hmem
  refine Work.FTS.NonlinRows.Rl1.rowGG_engine (CA := CA) (α := α) (Ce := Ce) (g := f)
    (A := Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg)) (B₀ := Work.Spaces.Dz f)
    (Φ₀ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi2 f)
    (N := Work.FTS.Nonlin.N3gg α f Ξg) (c := 6 * α)
    hCA hα hVq.1 hVq.2 ?_ hsup hsl (fun r _ => rfl) (by positivity) ?_
  · calc Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg))
        ≤ Ce * Work.FTS.Nonlin.Xn α f := hVle
      _ ≤ max Ce 0 * Work.FTS.Nonlin.Xn α f :=
          mul_le_mul_of_nonneg_right (le_max_left Ce 0) (Work.Spaces.HkNorm_nonneg α 4 f)
  · intro r _ θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 :=
      Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.abs_K_le_three_aux θ
    have hA0 : 0 ≤ |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg) r θ| := abs_nonneg _
    have hg0 : 0 ≤ |Work.Spaces.Dz f r θ| := abs_nonneg _
    have habs : |Work.Spaces.K θ * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg)
          r θ * Work.Spaces.Dz f r θ)|
        = 2 * α * |Work.Spaces.K θ|
            * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg) r θ|
            * |Work.Spaces.Dz f r θ| := by
      simp only [abs_mul, abs_neg, abs_of_nonneg hα.le, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    simp only [Work.FTS.Nonlin.N3gg]
    rw [habs]
    calc 2 * α * |Work.Spaces.K θ|
          * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg) r θ| * |Work.Spaces.Dz f r θ|
        ≤ 2 * α * 3 * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg) r θ|
            * |Work.Spaces.Dz f r θ| := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hA0) hg0
          nlinarith [hK, hα]
      _ = 6 * α * (|Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg) r θ|
            * |Work.Spaces.Dz f r θ|) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows
