import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# PTGEOMETRIC: the transfer lemma for the ambient perturbation

If `χ : M → ℝ` is `C^∞` and nonnegative with `χ x = 0` at an interior point `x`, and `w : M → F` is
`C^∞` into a normed space, then the derivative of `y ↦ χ y • w y` at `x` vanishes.  This is what
makes the perturbation by `χ • w` *invisible* to the derivative at the zeros of the cut-off `χ`, so
that a transversality property obtained at one stage of the ambient perturbation iteration survives
all the later stages — without any disjointness assumption on the cut-offs.

The proof is the product rule in the chart (`hχχ.smul hww`) together with Fermat's rule at the
interior local minimum of `χ`.  The one technical point is the `TangentSpace`-instance mismatch:
`set_option backward.isDefEq.respectTransparency false` is what allows the chart-level
`HasFDerivWithinAt` statements (whose derivative is typed in the tangent space) to be used directly.

## Main results

* `Work.PTGeometric.mfderiv_smul_eq_zero_of_isLocalMin`
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **The transfer lemma.**  If `χ : M → ℝ` is `C^∞` and nonnegative with `χ x = 0` at an interior
point `x`, and `w : M → F` is `C^∞` into a normed space `F`, then the derivative of `y ↦ χ y • w y`
at `x` vanishes.

(With `0 ≤ χ` and `χ x = 0`, the point `x` is a global minimum of `χ`, so `mfderiv χ x = 0`; the
product rule then gives `mfderiv (χ • w) x = χ x • mfderiv w x + (mfderiv χ x) • w x = 0`.) -/
theorem mfderiv_smul_eq_zero_of_isLocalMin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : M → ℝ} (hχ : ContMDiff I (𝓘(ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {w : M → F} (hw : ContMDiff I (𝓘(ℝ, F)) ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    {x : M} (hχ0 : ∀ y, 0 ≤ χ y) (hχx : χ x = 0) (hx : I.IsInteriorPoint x) :
    mfderiv I (𝓘(ℝ, F)) (fun y => χ y • w y) x = 0 := by
  set z0 : E := (extChartAt I x) x with hz0
  have hcoe : (extChartAt I x).symm z0 = x := by
    rw [hz0]; exact (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have hmem : z0 ∈ interior (Set.range I) := by
    rw [ModelWithCorners.isInteriorPoint_iff] at hx
    exact interior_mono (extChartAt_target_subset_range (I := I) x) hx
  have hnhds : Set.range I ∈ 𝓝 z0 :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hmem) interior_subset
  have hwritten : writtenInExtChartAt I (𝓘(ℝ, F)) x (χ • w) =
      fun v : E => χ ((extChartAt I x).symm v) • w ((extChartAt I x).symm v) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_self_eq]
    rfl
  have hχχ : HasFDerivWithinAt (fun v : E => χ ((extChartAt I x).symm v))
      (mfderiv I (𝓘(ℝ)) χ x) (Set.range I) z0 := by
    have h := ((hχ x).mdifferentiableAt (by simp)).hasMFDerivAt
    unfold HasMFDerivAt at h
    exact h.2
  have hww : HasFDerivWithinAt (fun v : E => w ((extChartAt I x).symm v))
      (mfderiv I (𝓘(ℝ, F)) w x) (Set.range I) z0 := by
    have h := ((hw x).mdifferentiableAt (by simp)).hasMFDerivAt
    unfold HasMFDerivAt at h
    exact h.2
  have h1 : HasFDerivWithinAt
      (fun v : E => χ ((extChartAt I x).symm v) • w ((extChartAt I x).symm v))
      (mfderiv I (𝓘(ℝ, F)) (fun y => χ y • w y) x) (Set.range I) z0 := by
    have h := (((hχ x).smul (hw x)).mdifferentiableAt (by simp)).hasMFDerivAt
    unfold HasMFDerivAt at h
    rw [hwritten] at h
    exact h.2
  have h2 : fderiv ℝ (fun v : E => χ ((extChartAt I x).symm v) • w ((extChartAt I x).symm v)) z0 =
      mfderiv I (𝓘(ℝ, F)) (fun y => χ y • w y) x := (h1.hasFDerivAt hnhds).fderiv
  have hmin : IsLocalMin (fun v : E => χ ((extChartAt I x).symm v)) z0 := by
    have h0 : χ ((extChartAt I x).symm z0) = 0 := by rw [hcoe, hχx]
    have : ∀ z, χ ((extChartAt I x).symm z0) ≤ χ ((extChartAt I x).symm z) := by
      intro z; rw [h0]; exact hχ0 _
    exact Filter.Eventually.of_forall this
  have hzero : fderiv ℝ (fun v : E => χ ((extChartAt I x).symm v) • w ((extChartAt I x).symm v)) z0 = 0 := by
    have h0 : χ ((extChartAt I x).symm z0) = 0 := by rw [hcoe, hχx]
    have hfun : (fun v : E => χ ((extChartAt I x).symm v) • w ((extChartAt I x).symm v))
        = (fun v : E => χ ((extChartAt I x).symm v)) •
          (fun v : E => w ((extChartAt I x).symm v)) := rfl
    have hχd0 : mfderiv I (𝓘(ℝ)) χ x = 0 := by
      rw [← (hχχ.hasFDerivAt hnhds).fderiv, hmin.fderiv_eq_zero]
    have key : fderiv ℝ ((fun v : E => χ ((extChartAt I x).symm v)) •
          (fun v : E => w ((extChartAt I x).symm v))) z0 = 0 := by
      rw [((hχχ.smul hww).hasFDerivAt hnhds).fderiv, hχd0, h0]
      ext v
      simp
    exact hfun.symm ▸ key
  rw [← h2, hzero]

end

end Work.PTGeometric
