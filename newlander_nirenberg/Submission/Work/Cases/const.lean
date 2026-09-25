import Mathlib
import Submission.Work.Core.Defs
import Submission.Work.Core.Reduction
import Submission.Work.Complex.standardForm

namespace Work.Cases

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff

/-- **Newlander–Nirenberg for a constant almost complex structure.**
If `J₀ : E n →L[ℝ] E n` satisfies `J₀ ∘ J₀ = -1`, then the conclusion of `newlander_nirenberg`
holds for the constant field `J = fun _ => J₀` on any open `U ∋ x`: there is a smooth chart to
`ℂⁿ` whose differential is complex linear.  Here the structure is already linear, so the chart can
be taken linear: identify `E n` with `ℂⁿ` by a real-linear isomorphism `T` intertwining `J₀` with
multiplication by `i` (this is `Submission.Work.Complex.standardForm`), and use the components of
`T` as the holomorphic functions; then apply `Submission.exists_chart_of_holomorphic`
(`Submission/Work/Core/Reduction.lean`). -/
theorem const {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    (J₀ : E n →L[ℝ] E n) (hJ₀ : ∀ v, J₀ (J₀ v) = -v) {x : E n} (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (F n),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → F n) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : F n → E n) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E n,
        fderiv ℝ (φ : E n → F n) y (J₀ v) = Complex.I • fderiv ℝ (φ : E n → F n) y v := by
  obtain ⟨T, hT⟩ := Work.Complex.standardForm J₀ hJ₀
  let φ : OpenPartialHomeomorph (E n) (F n) :=
    { toFun := T
      invFun := T.symm
      source := U
      target := T '' U
      map_source' := fun y hy => ⟨y, hy, rfl⟩
      map_target' := by rintro z ⟨y, hy, rfl⟩; simpa using hy
      left_inv' := fun y _ => T.symm_apply_apply y
      right_inv' := by rintro z ⟨y, hy, rfl⟩; exact T.apply_symm_apply (T y)
      continuousOn_toFun := T.continuous.continuousOn
      continuousOn_invFun := T.symm.continuous.continuousOn
      open_source := hU
      open_target := T.isOpenMap U hU }
  refine ⟨φ, hx, fun y hy => hy, ?_, ?_, ?_⟩
  · show ContDiffOn ℝ ∞ (T : E n → F n) U
    exact T.contDiff.contDiffOn
  · show ContDiffOn ℝ ∞ (T.symm : F n → E n) (T '' U)
    exact T.symm.contDiff.contDiffOn
  · intro y _ v
    have hfd : fderiv ℝ (T : E n → F n) y = (T : E n →L[ℝ] F n) :=
      ContinuousLinearEquiv.fderiv T
    show fderiv ℝ (T : E n → F n) y (J₀ v) = Complex.I • fderiv ℝ (T : E n → F n) y v
    rw [hfd]
    simpa using hT v

end Work.Cases
