import Mathlib
import Submission.Work.Diff.EXT.ufslice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.JetConv

/-- The `m`-th spatial jet of a slice `y' ↦ w (p.1, y')` is the full jet at `p`, restricted along
the inclusion of `E` into `ℝ × E` in every variable.  Immediate from
`Work.Diff.EXT.sjet_apply` by extensionality, using
`ContinuousMultilinearMap.compContinuousLinearMap_apply`. -/
theorem slice_jet_comp_inr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {V : Set (ℝ × E)} (hV : IsOpen V) {w : ℝ × E → Z}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w V) {p : ℝ × E} (hp : p ∈ V) (m : ℕ) :
    iteratedFDeriv ℝ m (fun y' : E => w (p.1, y')) p.2
      = (iteratedFDeriv ℝ m w p).compContinuousLinearMap
          (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ E) := by
  ext v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact Work.Diff.EXT.sjet_apply hV hw hp m v

end Work.Diff.EXT.JetConv
