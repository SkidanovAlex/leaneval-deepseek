/-
# The `D_z ∂_θ`-companion of the derivation identity (`ThetaU`)

The companion of `Work.FTS.EllipticEst.ThetaU.mixed_pth_expand_V` for `D_z ∂_θG`:

  `mixed j i (D_z ∂_θG) = ∑_{a<i} C(i-1,a) · (D_θ^a sin 2θ) · mixed (j+1) (i-1-a) (∂_θ²G)`.

The proof uses the commutation `D_θ^i (D_z f) = D_z (D_θ^i f)`
(`Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen`) to identify
`mixed j i (D_z ∂_θG)` with `mixed (j+1) i (∂_θG)`, and then `mixed_pth_expand_V`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.ThetaU.SlotVDefs
import Submission.Work.FTS.EllipticEst.ThetaU.mixed_pth_expand_V
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

theorem mixed_Dzpth_expand_V {G : ℝ → ℝ → ℝ} (hG : SmV G) (j i : ℕ) (hi : 1 ≤ i) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Spaces.pth G)) z θ
      = ∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) *
          (Work.FTS.EllipticEst.sinIter a θ
            * Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 G) z θ) := by
  have hstep : Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Spaces.pth G)) z θ
      = Work.Spaces.mixed (j + 1) i (Work.Spaces.pth G) z θ := by
    have hcomm : Set.EqOn
        (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter 1 (Work.Spaces.pth G))))
        (Function.uncurry (Work.Spaces.mixed 1 i (Work.Spaces.pth G))) V :=
      OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen isOpen_V
        (fun n => (hG.pth).of_le_nat n) 1 i
    have hc := DzIter_congr_V hcomm j (mem_V hz hθ)
    have h4 := congrFun (congrFun
      (Work.Spaces.DzIter_add_right j 1 (Work.Spaces.DthIter i (Work.Spaces.pth G))) z) θ
    show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz (Work.Spaces.pth G))) z θ
        = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i (Work.Spaces.pth G)) z θ
    rw [h4]
    exact hc
  rw [hstep]
  exact mixed_pth_expand_V hG (j + 1) i hi hz hθ

end Work.FTS.EllipticEst.ThetaU
