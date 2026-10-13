import Mathlib
import Submission.Work.WilE9.Ift.ift_exists
import Submission.Work.WilE9.EaD.eaD_hasFDerivAt
import Submission.Work.WilE9.EaD.eaEval_contDiff

set_option maxHeartbeats 1000000
noncomputable section
open Classical Filter Topology

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-- **Local uniqueness of a nondegenerate solution.**  If the system `h` vanishes at `(x, y)` and the
fibre Jacobian `∂h/∂y` is invertible there, then among the `y'` near `y` the equations
have the unique solution `y`.  This is the uniqueness half of the implicit function theorem,
applied to the fibre map `v ↦ (a ↦ eaEval c (h a) (Fin.append x v))`. -/
theorem eaEval_eventually_eq {p q r : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (h : Fin q → WilkiesDesign.E.EAPoly (p + q) r) (x : Fin p → ℝ) (y : Fin q → ℝ)
    (hy : ∀ a, WilkiesDesign.E.eaEval c (h a) (Fin.append x y) = 0)
    (hdet : (Matrix.of fun (a : Fin q) (l : Fin q) =>
      WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.natAdd p l) (h a))
        (Fin.append x y)).det ≠ 0) :
    ∀ᶠ y' in nhds y, (∀ a, WilkiesDesign.E.eaEval c (h a) (Fin.append x y') = 0) → y' = y := by
  classical
  -- The fibre Jacobian, as a matrix.
  set J : Matrix (Fin q) (Fin q) ℝ := Matrix.of fun (a : Fin q) (l : Fin q) =>
    eaEval c (eaD c (Fin.natAdd p l) (h a)) (Fin.append x y) with hJ
  have hJdet : J.det ≠ 0 := by rw [hJ]; exact hdet
  have hJunit : IsUnit J.det := isUnit_iff_ne_zero.mpr hJdet
  -- The derivative of the fibre map `v ↦ (a ↦ eaEval c (h a) (Fin.append x v))` at `y`.
  set L : (Fin q → ℝ) →L[ℝ] (Fin q → ℝ) :=
    (ContinuousLinearMap.pi fun a : Fin q =>
        Work.WilE9.Ift.ambDeriv c (h a) (Fin.append x y) ∘SL Work.WilE9.Ift.appendCLM p q)
      ∘SL ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ) with hL
  have hLv : ∀ v : Fin q → ℝ, L v = J.mulVec v := by
    intro v
    have h1 := Work.WilE9.Ift.graphEval_snd c h x y v
    rw [hL, hJ]
    exact h1
  -- ... and it is invertible, because `J` is.
  have hLinv : L.IsInvertible := by
    refine ⟨(Matrix.toLinearEquiv' J
      (Matrix.invertibleOfIsUnitDet J hJunit)).toContinuousLinearEquiv, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    rw [hLv v]
    change (Matrix.toLin' J) v = J.mulVec v
    exact Matrix.toLin'_apply J v
  -- The fibre map.
  set φ : (Fin q → ℝ) → (Fin q → ℝ) :=
    Work.WilE9.Ift.graphEval c h ∘ (fun v : Fin q → ℝ => (x, v)) with hφ
  have hφα : ∀ (v : Fin q → ℝ) (a : Fin q), φ v a = eaEval c (h a) (Fin.append x v) :=
    fun v a => rfl
  -- It is smooth, hence strictly differentiable, with the derivative computed above.
  have hcφ : ContDiff ℝ ⊤ φ := by
    rw [hφ]
    exact (Work.WilE9.Ift.graphEval_contDiff c h).comp (contDiff_prodMk_right x)
  have hshift : HasFDerivAt (fun v : Fin q → ℝ => (x, v))
      (ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ)) y := by
    have h1 := (ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ)).hasFDerivAt (x := y)
    have h2 := h1.add_const (x, (0 : Fin q → ℝ))
    have hfun : (fun v : Fin q → ℝ =>
        (ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ)) v + (x, (0 : Fin q → ℝ)))
        = fun v : Fin q → ℝ => (x, v) := by
      funext v
      simp [ContinuousLinearMap.inr_apply]
    rwa [hfun] at h2
  have hfa : HasFDerivAt φ L y := by
    have h0 := (Work.WilE9.Ift.hasFDerivAt_graphEval c h x y).comp y hshift
    rw [hφ]
    exact h0
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := (WithTop.coe_lt_top (0 : ℕ∞)).ne'
  have hsc : HasStrictFDerivAt φ L y := by
    have h1 : HasStrictFDerivAt φ (fderiv ℝ φ y) y := hcφ.contDiffAt.hasStrictFDerivAt hn
    simpa only [hfa.fderiv] using h1
  -- Local injectivity, via the inverse function theorem.
  obtain ⟨e, he⟩ := hLinv
  have hsl : HasStrictFDerivAt φ (e : (Fin q → ℝ) →L[ℝ] (Fin q → ℝ)) y :=
    hsc.congr_fderiv he.symm
  filter_upwards [hsl.eventually_left_inverse] with y' hleft
  intro hzero
  have hzy' : φ y' = 0 := funext fun a => by rw [hφα]; exact hzero a
  have hzy : φ y = 0 := funext fun a => by rw [hφα]; exact hy a
  calc y' = HasStrictFDerivAt.localInverse φ e y hsl (φ y') := hleft.symm
    _ = HasStrictFDerivAt.localInverse φ e y hsl (φ y) := by rw [hzy', hzy]
    _ = y := hsl.localInverse_apply_image

end Work.WilE7
