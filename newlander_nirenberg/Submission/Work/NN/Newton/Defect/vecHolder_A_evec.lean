import Mathlib
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.CR.Flat.Holder.Bilinear

/-!
# The column `z ↦ A z e_j` is `C^{0,α}`-small when `A` is componentwise `C^{1,α}`-small

`Work.NN.Newton.CVBound A α a P` bounds, for every vector `w` with `‖w‖ ≤ 1` and every coordinate
`k`, the `C^{1,α}(P)`-norm of the component `z ↦ (A z w)_k` by `a`.  The `VecHolder`-form of
smallness — which is what the perturbed `∂̄`-equation consumes — asks instead for a *global* bound
on the vector `z ↦ A z w`:

* `‖A z w‖ ≤ a`, and
* `‖A z w - A z' w‖ ≤ a ‖z - z'‖ ^ α`.

Both follow from the componentwise bounds, the first by taking the sup over the finitely many
coordinates and the second by applying the componentwise Hölder estimates coordinate by
coordinate.  This file records the two elementary conversions from the Hölder norm to pointwise
information, and the target `vecHolder_A_evec` for the columns `w = e_j`.
-/

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Newton.Defect

namespace VecHolderAux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A bound `holderNorm 1 α f Ω ≤ ofReal a` (with `a ≥ 0`) gives the pointwise bound
`‖f z‖ ≤ a` on `Ω`: the `C^0` part of the `C^{1,α}`-norm controls the supremum. -/
lemma norm_le_of_holderNorm_one_le {f : X → ℂ} {Ω : Set X} {α a : ℝ} (ha : 0 ≤ a)
    (h : Work.CR.Flat.holderNorm 1 α f Ω ≤ ENNReal.ofReal a) {z : X} (hz : z ∈ Ω) :
    ‖f z‖ ≤ a := by
  have h1 : ENNReal.ofReal ‖f z‖ ≤ ENNReal.ofReal a :=
    calc ENNReal.ofReal ‖f z‖
        ≤ Work.CR.Flat.iterDerivNorm 0 f Ω := by
          rw [← norm_iteratedFDerivWithin_zero (𝕜 := ℝ) (s := Ω) (f := f) (x := z)]
          exact Work.CR.Flat.le_iterDerivNorm 0 f Ω hz
      _ ≤ Work.CR.Flat.holderNorm 1 α f Ω :=
          Work.CR.Flat.iterDerivNorm_le_holderNorm 1 α f Ω (Nat.zero_le 1)
      _ ≤ ENNReal.ofReal a := h
  exact (ENNReal.ofReal_le_ofReal_iff ha).mp h1

/-- A bound `holderNorm 1 α f Ω ≤ ofReal a` (with `a ≥ 0`) gives the pointwise Hölder estimate
`‖f z - f z'‖ ≤ a ‖z - z'‖ ^ α` on `Ω`: the `C^{0,α}` part of the `C^{1,α}`-norm. -/
lemma norm_sub_le_of_holderNorm_one_le {f : X → ℂ} {Ω : Set X} {α a : ℝ} (ha : 0 ≤ a)
    (h : Work.CR.Flat.holderNorm 1 α f Ω ≤ ENNReal.ofReal a) {z z' : X}
    (hz : z ∈ Ω) (hz' : z' ∈ Ω) :
    ‖f z - f z'‖ ≤ a * ‖z - z'‖ ^ α := by
  rcases eq_or_ne z z' with rfl | hne
  · rw [sub_self, norm_zero]
    exact mul_nonneg ha (Real.rpow_nonneg (norm_nonneg _) α)
  · have h1 : ENNReal.ofReal (‖f z - f z'‖ / ‖z - z'‖ ^ α) ≤ ENNReal.ofReal a :=
      calc ENNReal.ofReal (‖f z - f z'‖ / ‖z - z'‖ ^ α)
          ≤ Work.CR.Flat.holderSeminorm 0 α f Ω := by
            rw [← Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub f Ω z z']
            exact Work.CR.Flat.le_holderSeminorm 0 α f Ω hz hz' hne
        _ ≤ Work.CR.Flat.holderNorm 1 α f Ω :=
            Work.CR.Flat.holderSeminorm_le_holderNorm 1 α f Ω (Nat.zero_le 1)
        _ ≤ ENNReal.ofReal a := h
    have h2 : ‖f z - f z'‖ / ‖z - z'‖ ^ α ≤ a := (ENNReal.ofReal_le_ofReal_iff ha).mp h1
    have hpos : 0 < ‖z - z'‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) α
    exact (div_le_iff₀ hpos).mp h2

end VecHolderAux

end Work.NN.Newton.Defect

namespace Work.NN.Newton.Defect

theorem vecHolder_A_evec {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (ha0 : 0 ≤ a)
    (hA : Work.NN.Newton.CVBound A α a (Work.NN.Newton.polydiscR n r)) (j : Fin n) :
    Work.NN.Final.VecHolder (fun z => A z (Work.NN.Newton.evec j)) α a
      (Work.NN.Newton.polydiscR n r) := by
  have hw : ‖Work.NN.Newton.evec j‖ ≤ 1 := by
    rw [Work.NN.Newton.evec, Pi.norm_single]
    norm_num
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [pi_norm_le_iff_of_nonneg ha0]
    intro k
    exact VecHolderAux.norm_le_of_holderNorm_one_le ha0 (hA (Work.NN.Newton.evec j) hw k) hz
  · intro z hz z' hz'
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg ha0 (Real.rpow_nonneg (norm_nonneg _) α))]
    intro k
    exact VecHolderAux.norm_sub_le_of_holderNorm_one_le ha0 (hA (Work.NN.Newton.evec j) hw k) hz hz'

end Work.NN.Newton.Defect
