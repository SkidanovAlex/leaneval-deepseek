import Mathlib
import Submission.Diff.Grad

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A Gram–Schmidt family of frames for a time-dependent metric

This module contains the definitions used by the proof of
`Work.Diff.GE.exists_ON_frame_family`: for a bilinear form `b` on a real vector space `V` we define
the Gram–Schmidt orthonormalisation `gs b κ` of a family `κ`, and for a family of metrics
`G : ℝ → SMet I M` we define the corresponding family of frames `frameFamily G t x s` at `x`,
together with the "pre-normalisation" vectors `frameU G t x s i` and the explicit
Uhlenbeck/Ricci derivative `frameEdot G t x`.

The choice of starting frame is `Submission.Diff.onFrame (G t) x`, the `Classical.epsilon`-chosen
`G t`-orthonormal frame; this is what makes `frameEdot`'s bound refer to `rmNormSq (G t) x`
directly, since `rmC (G t) x` is by definition the curvature array in that frame.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

/-! ## Gram–Schmidt orthonormalisation of a family for a bilinear form -/

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- `gsU b κ E i` is `κ i` with the `b`-projections onto the vectors `E j`, `j < i`, removed.
(The values `E j` for `j ≥ i` are ignored, which is why it can be used as the recursion step.) -/
noncomputable def gsU {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V) (E : Fin n → V) (i : Fin n) : V :=
  κ i - ∑ j : Fin n, if j.val < i.val then b (κ i) (E j) • E j else 0

/-- One Gram–Schmidt step: normalise `gsU b κ E i` with respect to `b`. -/
noncomputable def gsStep {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V) (E : Fin n → V)
    (i : Fin n) : V :=
  (Real.sqrt (b (gsU b κ E i) (gsU b κ E i)))⁻¹ • gsU b κ E i

/-- Gram–Schmidt orthonormalisation of the family `κ` for the bilinear form `b`, defined by
recursion on the index so that `gs b κ i` only uses the values `gs b κ j` with `j < i`. -/
noncomputable def gs {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V) : Fin n → V :=
  WellFounded.fix (InvImage.wf (fun i : Fin n => i.val) wellFounded_lt)
    (fun i ih => gsStep b κ (fun j => if h : j.val < i.val then ih j h else 0) i)

/-- `gsU` only depends on the vectors `E j` with `j < i`. -/
theorem gsU_congr {n : ℕ} {b : V → V → ℝ} {κ : Fin n → V} {E E' : Fin n → V} {i : Fin n}
    (h : ∀ j, j.val < i.val → E j = E' j) : gsU b κ E i = gsU b κ E' i := by
  rw [gsU, gsU]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j.val < i.val
  · rw [if_pos hj, if_pos hj, h j hj]
  · rw [if_neg hj, if_neg hj]

/-- The recursion equation for Gram–Schmidt. -/
theorem gs_eq {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V) (i : Fin n) :
    gs b κ i = gsStep b κ (gs b κ) i := by
  have h : gs b κ i =
      gsStep b κ (fun j => if j.val < i.val then gs b κ j else 0) i :=
    WellFounded.fix_eq (InvImage.wf (fun i : Fin n => i.val) wellFounded_lt) _ i
  rw [h]
  have hcong := gsU_congr (b := b) (κ := κ)
    (E := fun j => if j.val < i.val then gs b κ j else 0) (E' := gs b κ)
    (fun j hj => by rw [if_pos hj])
  simp only [gsStep]
  rw [hcong]

/-- The unfolding of `gs` at an index. -/
theorem gs_apply {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V) (i : Fin n) :
    gs b κ i =
      (Real.sqrt (b (gsU b κ (gs b κ) i) (gsU b κ (gs b κ) i)))⁻¹ • gsU b κ (gs b κ) i :=
  gs_eq b κ i

end Generic

/-! ## The frames attached to a family of metrics -/

section Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The bilinear form of the metric `G s` at `x`. -/
noncomputable def frameB (G : ℝ → SMet I M) (x : M) (s : ℝ) :
    TangentSpace I x → TangentSpace I x → ℝ :=
  fun u v => (G s).inner x u v

/-- The Gram–Schmidt family of frames at `x`, built from the `G t`-orthonormal frame
`onFrame (G t) x` by orthonormalisation with respect to `G s`. -/
noncomputable def frameFamily (G : ℝ → SMet I M) (t : ℝ) (x : M) (s : ℝ) :
    Fin (Module.finrank ℝ E) → TangentSpace I x :=
  gs (frameB G x s) (onFrame (G t) x)

/-- The pre-normalisation vector of the Gram–Schmidt construction. -/
noncomputable def frameU (G : ℝ → SMet I M) (t : ℝ) (x : M) (s : ℝ)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
  gsU (frameB G x s) (onFrame (G t) x) (frameFamily G t x s) i

/-- The derivative of the frame at time `t`, as given by the Ric tensor of `G t` in the frame
`onFrame (G t) x`: in an Uhlenbeck frame with `∂ₛ eᵢ = Ric(eᵢ)^♯` one has
`∂ₛ eᵢ = ∑ⱼ Ric(eᵢ,eⱼ) eⱼ`, and triangularity of Gram–Schmidt leaves only the terms `j ≤ i`,
with the diagonal term doubled by the normalisation. -/
noncomputable def frameEdot (G : ℝ → SMet I M) (t : ℝ) (x : M) :
    Fin (Module.finrank ℝ E) → TangentSpace I x :=
  fun i => (ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x i)) • (onFrame (G t) x i)
    + ∑ j : Fin (Module.finrank ℝ E),
        if j.val < i.val then
          (2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j)) • (onFrame (G t) x j)
        else 0

/-- The recursion equation for the frame family. -/
theorem frameFamily_eq (G : ℝ → SMet I M) (t : ℝ) (x : M) (s : ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    frameFamily G t x s i =
      (Real.sqrt (frameB G x s (frameU G t x s i) (frameU G t x s i)))⁻¹ • frameU G t x s i :=
  gs_apply (frameB G x s) (onFrame (G t) x) i

end Manifold

end Work.Diff.GE
