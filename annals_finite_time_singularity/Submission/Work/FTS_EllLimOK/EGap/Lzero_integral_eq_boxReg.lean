import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.Phi_deriv
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory

namespace Work.FTS_EllLimOK.EGap

/-- A two-point set in `ℝ` is null. -/
private theorem volume_pair_eq_zero (a b : ℝ) :
    (MeasureTheory.volume ({a, b} : Set ℝ)) = 0 := by
  have hfin : ({a, b} : Set ℝ).Finite := by simp
  exact hfin.measure_zero MeasureTheory.volume

theorem Lzero_integral_eq_boxReg (α : ℝ) (v : ℝ → ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    (hbox : Work.FTS_EllLimOK.BoxReg v)
    (heq : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.bslOp α v z θ = 0) :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero v z θ * v z θ)
      = α ^ 2 * z ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 v z θ * v z θ)
        + α * (5 + α) * z * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz v z θ * v z θ) := by
  -- The equation `bslOp α v z = 0` on the open angle interval gives the pointwise identity
  -- of integrands there.
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Elliptic.Lzero v z θ * v z θ
        = α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 v z θ * v z θ)
          + α * (5 + α) * z * (Work.Spaces.pz v z θ * v z θ) := by
    intro θ hθ
    have h0 : Work.Elliptic.Lzero v z θ
        = (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 v z θ
          + (α * (5 + α) * z) * Work.Spaces.pz v z θ := by
      have h := heq θ hθ
      simp only [Work.Elliptic.bslOp_apply] at h
      linarith
    rw [h0]
    ring
  -- Hence the two integrands agree almost everywhere on `Iθ`: they can differ only at the
  -- two endpoints `θ = 0` and `θ = π/2`, a null set.
  have hae : (fun θ : ℝ => Work.Elliptic.Lzero v z θ * v z θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 v z θ * v z θ)
        + α * (5 + α) * z * (Work.Spaces.pz v z θ * v z θ)) := by
    change ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Elliptic.Lzero v z θ * v z θ
        = α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 v z θ * v z θ)
          + α * (5 + α) * z * (Work.Spaces.pz v z θ * v z θ)
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc,
      MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (volume_pair_eq_zero 0 (π / 2))
    intro x hx
    by_contra hmem
    have hx0 : x ≠ 0 := fun h0 => hmem (by simp [h0])
    have hxpi : x ≠ π / 2 := fun hp => hmem (by simp [hp])
    refine hx (fun hxI => ?_)
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hxI
    exact hpt x ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0),
      lt_of_le_of_ne hxI.2 hxpi⟩
  -- `BoxReg` makes the two `z`-derivative slices continuous, hence integrable, on `Iθ`.
  have hzmem : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  obtain ⟨-, -, hpzcont, hp2cont⟩ :=
    boxReg_facts (show z / 2 < 2 * z by linarith)
      (hbox (z / 2) (2 * z) (by linarith) (by linarith))
  have hcurve : ContinuousOn (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) Work.Spaces.Iθ :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hpzslice : ContinuousOn (fun θ : ℝ => Work.Spaces.pz v z θ) Work.Spaces.Iθ :=
    hpzcont.comp hcurve (fun θ hθ => ⟨hzmem, hθ⟩)
  have hp2slice : ContinuousOn (fun θ : ℝ => Work.Spaces.pzIter 2 v z θ) Work.Spaces.Iθ :=
    hp2cont.comp hcurve (fun θ hθ => ⟨hzmem, hθ⟩)
  have hvslice : ContinuousOn (fun θ : ℝ => v z θ) Work.Spaces.Iθ := (hbox.slice hz).continuousOn
  have hBint : Integrable (fun θ : ℝ => Work.Spaces.pzIter 2 v z θ * v z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hp2slice.mul hvslice).integrableOn_compact isCompact_Icc
  have hCint : Integrable (fun θ : ℝ => Work.Spaces.pz v z θ * v z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hpzslice.mul hvslice).integrableOn_compact isCompact_Icc
  -- Linearity of the integral.
  have hsplit : (∫ θ in Work.Spaces.Iθ,
        (α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 v z θ * v z θ)
          + α * (5 + α) * z * (Work.Spaces.pz v z θ * v z θ)))
      = α ^ 2 * z ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 v z θ * v z θ)
        + α * (5 + α) * z * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz v z θ * v z θ) := by
    rw [MeasureTheory.integral_add (hBint.const_mul (α ^ 2 * z ^ 2))
        (hCint.const_mul (α * (5 + α) * z)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae hae]
  exact hsplit

end Work.FTS_EllLimOK.EGap
