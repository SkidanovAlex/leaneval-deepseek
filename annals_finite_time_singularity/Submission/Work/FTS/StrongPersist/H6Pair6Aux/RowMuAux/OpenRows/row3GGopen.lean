import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row1GGopen =====
section

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
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row2GGopen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-- `N₂^{gg} = -2·𝒰(Φ̃_g)∂_θf = -2·(𝒰(Φ̃_g)/sin 2θ)·D_θf` on the open quadrant. -/
private theorem n2gg_eq_open (α : ℝ) (f Ξg : Fn) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.Nonlin.N2gg α f Ξg z θ
      = -2 * ((Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) z θ
          / Work.Construction.s2 θ) * Work.Spaces.Dth f z θ) := by
  have hs : Work.Construction.s2 θ ≠ 0 := by
    rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
    exact ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos]))
  have h1 : Work.Spaces.Dth f z θ = Work.Construction.s2 θ * Work.Spaces.pth f z θ := rfl
  have hU : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) z θ / Work.Construction.s2 θ
      * (Work.Construction.s2 θ * Work.Spaces.pth f z θ)
      = Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) z θ * Work.Spaces.pth f z θ := by
    rw [← mul_assoc, div_mul_cancel₀ _ hs]
  simp only [Work.FTS.Nonlin.N2gg]
  rw [h1, hU]
  ring

theorem row2GGopen {CA : ℝ} (hCA : 0 < CA) {α Ce : ℝ} (hα : 0 < α)
    {f Ξg : Work.FTS.Galerkin.Fn} (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) (hEll : Work.FTS.VocabO.EllPkgGo α Ce f Ξg)
    (hsup : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ((Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) z θ / Work.Construction.s2 θ)) ^ 2
        ≤ CA / (Work.Spaces.gam α - 1)
          * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
              (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) z θ
                / Work.Construction.s2 θ) z θ') :
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2gg α f Ξg) ≤ ENNReal.ofReal
      (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * 6
        * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2) := by
  obtain ⟨hUq, hUle⟩ := hEll.U
  have hsl : Work.FTS.NonlinRows.Rl1.SlotData α (Work.Spaces.Dth f)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 f) (Work.Spaces.HkSq α 4 f) :=
    slotData_open_dth hα hso hmem
  refine Work.FTS.NonlinRows.Rl1.rowGG_engine (CA := CA) (α := α) (Ce := Ce) (g := f)
    (A := fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) z θ
      / Work.Construction.s2 θ)
    (B₀ := Work.Spaces.Dth f)
    (Φ₀ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 f)
    (N := Work.FTS.Nonlin.N2gg α f Ξg) (c := 6)
    hCA hα hUq.1 hUq.2 ?_ hsup hsl (fun r _ => rfl) (by norm_num) ?_
  · calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α f Ξg) z θ / Work.Construction.s2 θ)
        ≤ Ce * Work.FTS.Nonlin.Xn α f := hUle
      _ ≤ max Ce 0 * Work.FTS.Nonlin.Xn α f :=
          mul_le_mul_of_nonneg_right (le_max_left Ce 0) (Work.Spaces.HkNorm_nonneg α 4 f)
  · intro r _ θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 :=
      Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.abs_K_le_three_aux θ
    have hA0 : 0 ≤ |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) r θ
        / Work.Construction.s2 θ| := abs_nonneg _
    have hg0 : 0 ≤ |Work.Spaces.Dth f r θ| := abs_nonneg _
    have habs : |Work.Spaces.K θ * (-2 * ((Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α f Ξg) r θ / Work.Construction.s2 θ)
            * Work.Spaces.Dth f r θ))|
        = 2 * |Work.Spaces.K θ|
          * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) r θ
              / Work.Construction.s2 θ| * |Work.Spaces.Dth f r θ| := by
      simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [n2gg_eq_open α f Ξg hθ, habs]
    calc 2 * |Work.Spaces.K θ|
          * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) r θ
              / Work.Construction.s2 θ| * |Work.Spaces.Dth f r θ|
        ≤ 2 * 3 * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) r θ
              / Work.Construction.s2 θ| * |Work.Spaces.Dth f r θ| := by
          refine mul_le_mul_of_nonneg_right ?_ hg0
          refine mul_le_mul_of_nonneg_right ?_ hA0
          nlinarith [hK]
      _ = 6 * (|Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) r θ
              / Work.Construction.s2 θ| * |Work.Spaces.Dth f r θ|) := by ring

end

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row3GGopen =====
section

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
end
