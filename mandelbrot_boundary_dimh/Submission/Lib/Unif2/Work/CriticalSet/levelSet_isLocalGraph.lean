import Mathlib
import Submission.Lib.Unif2.Work.CriticalSet.Defs

namespace Work.CriticalSet

open Filter Set
open scoped Manifold ContDiff Topology

noncomputable section

open Classical

/-- **The implicit function theorem in `ℂ ≃ ℝ²`, in the form needed here.**

Let `φ : ℂ → ℝ` be `C¹` at `z₀` with non-vanishing derivative there.  Then there is a real-linear
isomorphism `e : ℂ ≃L[ℝ] ℝ × ℝ`, a radius `ρ > 0` and a function `g : ℝ → ℝ`, `C¹` at `0` with
`g 0 = 0`, such that on the ball of radius `ρ` around `0` the level set `{φ = φ z₀}`, transported by
`w ↦ e w` to `ℝ × ℝ`, is exactly the graph of `g`.

The isomorphism `e` is chosen so that the second coordinate direction `e.symm (0,1)` is a direction
in which the (real) derivative of `φ` does not vanish: this is what makes the implicit equation
solvable for the second coordinate.  Since `1` and `I` span `ℂ` over `ℝ`, at least one of the two
non-vanishing alternatives (which are the coordinates `(im, re)` and `(re, im)` of `e`) works. -/
theorem exists_local_graph_of_contDiffAt {φ : ℂ → ℝ} {z₀ : ℂ}
    (hφ : ContDiffAt ℝ 1 φ z₀) (hne : fderiv ℝ φ z₀ ≠ 0) :
    ∃ (e : ℂ ≃L[ℝ] ℝ × ℝ) (ρ : ℝ) (g : ℝ → ℝ), 0 < ρ ∧ ContDiffAt ℝ 1 g 0 ∧ g 0 = 0 ∧
      ∀ w : ℂ, e w ∈ Metric.ball 0 ρ → (φ (z₀ + w) = φ z₀ ↔ (e w).2 = g ((e w).1)) := by
  -- A real-linear functional on `ℂ` which kills `1` and `I` is zero.
  have hlin : ∀ (M : ℂ →L[ℝ] ℝ), M 1 = 0 → M Complex.I = 0 → M = 0 := by
    intro M h1 h2
    ext z
    have hz : M z = M ((z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I) := by
      conv_lhs => rw [show z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I from by simp]
    rw [hz, map_add, map_smul, map_smul, h1, h2]
    simp
  -- the two candidate coordinate systems
  let eSwap : ℂ ≃L[ℝ] ℝ × ℝ :=
    Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
  let eId : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM
  -- choose coordinates whose second direction is a direction of non-vanishing derivative
  let e : ℂ ≃L[ℝ] ℝ × ℝ := if fderiv ℝ φ z₀ 1 = 0 then eId else eSwap
  have hee : e.symm ((0 : ℝ), (1 : ℝ)) =
      if fderiv ℝ φ z₀ 1 = 0 then Complex.I else (1 : ℂ) := by
    by_cases h1 : fderiv ℝ φ z₀ 1 = 0
    · simp [e, h1, eId, Complex.equivRealProdCLM_symm_apply]
    · simp [e, h1, eSwap, Complex.equivRealProdCLM_symm_apply]
  have he : (fderiv ℝ φ z₀) (e.symm ((0 : ℝ), (1 : ℝ))) ≠ 0 := by
    rw [hee]
    by_cases h1 : fderiv ℝ φ z₀ 1 = 0
    · simp only [h1, ↓reduceIte]
      intro hI
      exact hne (hlin (fderiv ℝ φ z₀) h1 hI)
    · simpa [h1] using h1
  -- the implicit equation, in the new coordinates
  let f : ℝ × ℝ → ℝ := fun p => φ (z₀ + e.symm p)
  have hf : ContDiffAt ℝ 1 f 0 := by
    have h1 : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => z₀ + e.symm p) 0 :=
      contDiffAt_const.add (e.symm.contDiff.contDiffAt)
    have h2 : ContDiffAt ℝ 1 φ ((fun p : ℝ × ℝ => z₀ + e.symm p) 0) := by simpa using hφ
    simpa [f, Function.comp_def] using ContDiffAt.comp 0 h2 h1
  have hfd : HasFDerivAt f ((fderiv ℝ φ z₀).comp (e.symm : (ℝ × ℝ) →L[ℝ] ℂ)) 0 := by
    have hφd : HasFDerivAt φ (fderiv ℝ φ z₀) z₀ :=
      (hφ.differentiableAt (by norm_num)).hasFDerivAt
    have hTd : HasFDerivAt (fun p : ℝ × ℝ => z₀ + e.symm p)
        (e.symm : (ℝ × ℝ) →L[ℝ] ℂ) 0 :=
      (ContinuousLinearMap.hasFDerivAt (e.symm : (ℝ × ℝ) →L[ℝ] ℂ)).const_add z₀
    have hφd' : HasFDerivAt φ (fderiv ℝ φ z₀) ((fun p : ℝ × ℝ => z₀ + e.symm p) 0) := by
      simpa using hφd
    simpa [f, Function.comp_def] using HasFDerivAt.comp 0 hφd' hTd
  have hfderiv : fderiv ℝ f 0 = (fderiv ℝ φ z₀).comp (e.symm : (ℝ × ℝ) →L[ℝ] ℂ) := hfd.fderiv
  -- the derivative in the second coordinate is invertible
  have hif : ((fderiv ℝ f 0) ∘SL ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hfderiv]
    have hcomp : (fderiv ℝ φ z₀).comp (e.symm : (ℝ × ℝ) →L[ℝ] ℂ) ∘SL
        ContinuousLinearMap.inr ℝ ℝ ℝ
        = ContinuousLinearMap.toSpanSingleton ℝ ((fderiv ℝ φ z₀) (e.symm ((0 : ℝ), (1 : ℝ)))) := by
      ext
      simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [hcomp]
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.toSpanSingleton ℝ
        (((fderiv ℝ φ z₀) (e.symm ((0 : ℝ), (1 : ℝ)))))⁻¹) ?_ ?_
    · ext
      simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, inv_mul_cancel₀ he]
    · ext
      simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_inv_cancel₀ he]
  -- the implicit function and its properties
  let g : ℝ → ℝ := hf.implicitFunction (by norm_num : (1 : WithTop ℕ∞) ≠ 0) hif
  have hgC : ContDiffAt ℝ 1 g 0 := by
    have := ContDiffAt.contDiffAt_implicitFunction hf (by norm_num : (1 : WithTop ℕ∞) ≠ 0) hif
    simpa [g] using this
  have hg0 : g 0 = 0 := by
    have := ContDiffAt.implicitFunction_apply_self hf (by norm_num : (1 : WithTop ℕ∞) ≠ 0) hif
    simpa [g] using this
  have hev : ∀ᶠ v in nhds (0 : ℝ × ℝ), f v = f 0 ↔ g v.1 = v.2 := by
    have := ContDiffAt.eventually_apply_eq_iff_implicitFunction (f := f) (u := (0 : ℝ × ℝ)) hf
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0) hif
    simpa [g] using this
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨e, ρ, g, hρ, hgC, hg0, ?_⟩
  intro w hw
  have h1 := hball (Metric.mem_ball.mp hw)
  have hfw : f (e w) = φ (z₀ + w) := by simp [f]
  have hf0 : f 0 = φ z₀ := by simp [f]
  rw [hfw, hf0] at h1
  exact ⟨fun h => (h1.mp h).symm, fun h => h1.mpr h.symm⟩

/-- **The level set of a harmonic function at a regular point is locally a `C¹` graph.**

`IsLocalLevelGraphAt u x₀` asks for a real-linear isomorphism `e : ℂ ≃L[ℝ] ℝ × ℝ`, a radius `ρ > 0`
and `g : ℝ → ℝ` which is `C¹` at `0` with `g 0 = 0`, such that for every `y` in the source of the
preferred chart at `x₀` with `e ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀)` in the ball of radius `ρ`,
one has `u y = u x₀ ↔ (e (...)).2 = g ((e (...)).1)`.

This is the implicit function statement in `ℝ²`, applied to the chart pullback
`φ := u ∘ (chartAt ℂ x₀).symm` at the point `z₀ := (chartAt ℂ x₀) x₀`, whose gradient does not vanish
(`hreg` is literally `fderiv ℝ φ z₀ ≠ 0`); see `Work.CriticalSet.exists_local_graph_of_contDiffAt`
for the analytic content. -/
theorem levelSet_isLocalGraph {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {u : X → ℝ} {x₀ : X}
    (h : Submission.HarmonicOnXAt u x₀) (hreg : ¬ IsCriticalPointAt u x₀) :
    IsLocalLevelGraphAt u x₀ := by
  have hharm : InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := h
  have hφ : ContDiffAt ℝ 1 (u ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) :=
    hharm.1.of_le (by norm_num)
  have hne : fderiv ℝ (u ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 := hreg
  obtain ⟨e, ρ, g, hρ, hgC, hg0, hmain⟩ := exists_local_graph_of_contDiffAt hφ hne
  refine ⟨e, ρ, g, hρ, hgC, hg0, ?_⟩
  intro y hy hbal
  have h1 := hmain ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀) hbal
  have hsub : (chartAt ℂ x₀) x₀ + ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀) = (chartAt ℂ x₀) y := by
    abel
  rw [hsub] at h1
  have huy : (u ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) y) = u y := by
    simp only [Function.comp_apply]
    rw [(chartAt ℂ x₀).left_inv hy]
  have hux : (u ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = u x₀ := by
    simp only [Function.comp_apply]
    rw [(chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)]
  rw [huy, hux] at h1
  exact h1

end

end Work.CriticalSet
