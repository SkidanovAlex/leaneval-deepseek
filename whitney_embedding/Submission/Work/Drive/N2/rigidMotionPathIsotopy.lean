import Mathlib
import Submission.Work.Drive.Morse

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology in
/-- **Path of rigid motions applied to a picture (the engine of items (3) and (4) of the lead's plan).**

`c : ℝ → ℝ³` is a smooth `2π`-periodic *immersed* picture (`hcper` says it is a circle embedding,
`hcimm` that its derivative never vanishes), `s ↦ R s` is a smooth path of linear maps of `ℝ³` each of
which is isometric (`‖R s y‖ = ‖y‖`, hence injective), and `s ↦ v s` is a smooth path of translations.
Then the family of slices `E s := fun y => R s (c y) + v s` is a smooth isotopy of immersed circle
embeddings:

* `(s, y) ↦ R s (c y) + v s` is jointly `C^∞`, and each time slice is smooth;
* each slice is injective modulo the period (so an embedding of the circle);
* each slice is immersive: its derivative never vanishes.

Together with `Work.Drive.N2.goodDrawingOn_rigidMotion` (an isometry plus a translation preserves all
three clauses of a good drawing) this is the "+ rigid motions" family of the collar construction: the
orientation flip of a round/planar picture (a rotation by `π`) and the relabelling by translations
through the third coordinate (`v s = s • e₃`) are instances of it; the injectivity and immersion clauses
are exactly the `heinj`/`heimm` inputs of `Work.Drive.N2.collarDrawing`. -/
theorem rigidMotionPathIsotopy (c : ℝ → EuclideanSpace ℝ (Fin 3))
    (hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ c)
    (hcper : ∀ x y : ℝ, c x = c y → ∃ k : ℤ, y = x + k * (2 * Real.pi))
    (hcimm : ∀ y : ℝ, fderiv ℝ c y ≠ 0)
    (R : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (v : ℝ → EuclideanSpace ℝ (Fin 3))
    (hRsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R)
    (hvsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hiso : ∀ s : ℝ, ∀ y : EuclideanSpace ℝ (Fin 3), ‖R s y‖ = ‖y‖) :
    (ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun p : ℝ × ℝ => R p.1 (c p.2) + v p.1)) ∧
      (∀ s : ℝ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun y : ℝ => R s (c y) + v s)) ∧
      (∀ s : ℝ, ∀ x y : ℝ, R s (c x) = R s (c y) → ∃ k : ℤ, y = x + k * (2 * Real.pi)) ∧
      (∀ s : ℝ, ∀ y : ℝ, fderiv ℝ (fun t : ℝ => R s (c t) + v s) y ≠ 0) := by
  -- `R s` is norm preserving, hence injective (and vanishes only at `0`).
  have hRzero : ∀ s : ℝ, ∀ z : EuclideanSpace ℝ (Fin 3), R s z = 0 → z = 0 := by
    intro s z hz
    have h : ‖z‖ = 0 := by rw [← hiso s z, hz, norm_zero]
    exact norm_eq_zero.mp h
  -- the derivative of a single slice, `fderiv (fun t => R s (c t) + v s) y = (R s).comp (fderiv c y)`
  have hfderiv : ∀ s y : ℝ,
      fderiv ℝ (fun t : ℝ => R s (c t) + v s) y = (R s).comp (fderiv ℝ c y) := by
    intro s y
    have hcd : DifferentiableAt ℝ c y := (hc.contDiff.differentiable (by simp)).differentiableAt
    have h : HasFDerivAt (fun t : ℝ => R s (c t) + v s) ((R s).comp (fderiv ℝ c y)) y :=
      HasFDerivAt.add_const (v s) (HasFDerivAt.comp y ((R s).hasFDerivAt) hcd.hasFDerivAt)
    exact h.fderiv
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- joint smoothness of the uncurried family
    have h1 : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) ∞
        (fun p : ℝ × ℝ => R p.1) :=
      hRsm.comp_contMDiff (contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)))
    have h2 : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun p : ℝ × ℝ => c p.2) :=
      hc.comp (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)))
    have h3 : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun p : ℝ × ℝ => R p.1 (c p.2)) := h1.clm_apply h2
    have h4 : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun p : ℝ × ℝ => v p.1) :=
      hvsm.comp_contMDiff (contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)))
    exact h3.add h4
  · -- each time slice is smooth
    intro s
    have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin 3) => R s z + v s) := by
      simpa using (ContinuousLinearMap.contDiff (R s)).add contDiff_const
    exact hg.comp_contMDiff hc
  · -- injectivity modulo the period
    intro s x y hxy
    apply hcper x y
    have h0 : R s (c x - c y) = 0 := by rw [map_sub, hxy, sub_self]
    have hnorm : ‖c x - c y‖ = 0 := by rw [← hiso s (c x - c y), h0, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · -- immersivity of each slice
    intro s y hzero
    apply hcimm y
    rw [hfderiv s y] at hzero
    refine ContinuousLinearMap.ext (fun w => ?_)
    have hw : (R s) ((fderiv ℝ c y) w) = 0 := by
      have h := congrArg (fun (L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)) => L w) hzero
      simpa using h
    exact hRzero s ((fderiv ℝ c y) w) hw

end Work.Drive.N2
