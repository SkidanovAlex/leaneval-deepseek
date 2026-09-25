/-
# Transfer of the `n = 1` result between `ℂ` and `E 1 = ℝ²`

This file contains the bookkeeping bridging the `ℂ`-picture (the Beltrami equation and the
contraction of `Solve.lean`) with the statement of the challenge for `n = 1`, whose model space is
`E 1 = EuclideanSpace ℝ (Fin 2) = ℝ²` and whose target is `F 1 = EuclideanSpace ℂ (Fin 1) = ℂ`.
-/
import Mathlib
import Submission.Work.Beltrami.Defs
import Submission.Work.Core.Reduction
import Submission.Work.Beltrami.bijective_of_ne_zero

namespace Work.Beltrami

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open scoped ContDiff

noncomputable section

/-- The linear isometry `ℝ² → ℂ`, `(x, y) ↦ x + i y`. -/
def eC : E 1 ≃L[ℝ] ℂ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans
    ((LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv.trans
      Complex.equivRealProdCLM.symm)

/-- The `ℂ`-linear isometry `ℂ¹ → ℂ`. -/
def zF : F 1 ≃L[ℂ] ℂ :=
  (EuclideanSpace.equiv (Fin 1) ℂ).trans
    (LinearEquiv.funUnique (Fin 1) ℂ ℂ).toContinuousLinearEquiv

/-- The pull-back of a field of endomorphisms on `E 1` by the linear equivalence `T`, based at `x`:
`J' z = T ∘ J (x + T⁻¹ z) ∘ T⁻¹`. -/
def pullback (T : E 1 ≃L[ℝ] ℂ) (x : E 1) (J : E 1 → E 1 →L[ℝ] E 1) : ℂ → ℂ →L[ℝ] ℂ :=
  fun z => (T : E 1 →L[ℝ] ℂ).comp ((J (x + T.symm z)).comp (T.symm : ℂ →L[ℝ] E 1))

/-- The defining identity of the pull-back at the base point: `T (J p v) = J' (T (p - x)) (T v)`. -/
theorem pullback_T (T : E 1 ≃L[ℝ] ℂ) (x p : E 1) (J : E 1 → E 1 →L[ℝ] E 1) (v : E 1) :
    pullback T x J (T (p - x)) ((T : E 1 →L[ℝ] ℂ) v) = (T : E 1 →L[ℝ] ℂ) ((J p) v) := by
  simp only [pullback, ContinuousLinearMap.comp_apply]
  simp [ContinuousLinearEquiv.symm_apply_apply]

/-- The chain rule for `y ↦ w (T (y - x))`. -/
theorem fderiv_comp_translate (T : E 1 ≃L[ℝ] ℂ) (x p : E 1) (w : ℂ → ℂ)
    (hw : DifferentiableAt ℝ w (T (p - x))) :
    fderiv ℝ (fun y : E 1 => w (T (y - x))) p =
      (fderiv ℝ w (T (p - x))).comp (T : E 1 →L[ℝ] ℂ) := by
  have h3 : HasFDerivAt (fun y : E 1 => y - x) (1 : E 1 →L[ℝ] E 1) p :=
    (hasFDerivAt_id p).sub_const x
  have h4 : HasFDerivAt (fun y : E 1 => (T : E 1 →L[ℝ] ℂ) y) (T : E 1 →L[ℝ] ℂ) (p - x) :=
    (T : E 1 →L[ℝ] ℂ).hasFDerivAt
  have h5 : HasFDerivAt (fun y : E 1 => T (y - x)) (T : E 1 →L[ℝ] ℂ) p := by
    have h6 := h4.comp p h3
    have h7 : (T : E 1 →L[ℝ] ℂ) ∘SL (1 : E 1 →L[ℝ] E 1) = (T : E 1 →L[ℝ] ℂ) :=
      ContinuousLinearMap.comp_id _
    rw [h7] at h6
    simpa [Function.comp_def] using h6
  exact (hw.hasFDerivAt.comp p h5).fderiv

/-- **Holomorphy transfers across the identification `T`.** -/
theorem isJHolAt_comp {J : E 1 → E 1 →L[ℝ] E 1} (T : E 1 ≃L[ℝ] ℂ) (x p : E 1) {w : ℂ → ℂ}
    (hw : DifferentiableAt ℝ w (T (p - x)))
    (hhol : ∀ v : ℂ, fderiv ℝ w (T (p - x)) (pullback T x J (T (p - x)) v)
        = Complex.I * fderiv ℝ w (T (p - x)) v) :
    ∀ v : E 1, fderiv ℝ (fun y => w (T (y - x))) p (J p v)
      = Complex.I * fderiv ℝ (fun y => w (T (y - x))) p v := by
  intro v
  rw [fderiv_comp_translate T x p w hw]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← pullback_T T x p J v]
  exact hhol ((T : E 1 →L[ℝ] ℂ) v)

/-- **Nonvanishing of the differential transfers across the identification.** -/
theorem fderiv_ne_zero_comp (T : E 1 ≃L[ℝ] ℂ) (x p : E 1) {w : ℂ → ℂ}
    (hw : DifferentiableAt ℝ w (T (p - x))) (h : fderiv ℝ w (T (p - x)) ≠ 0) :
    fderiv ℝ (fun y => w (T (y - x))) p ≠ 0 := by
  rw [fderiv_comp_translate T x p w hw]
  intro hcon
  apply h
  have h3 : ((fderiv ℝ w (T (p - x))).comp (T : E 1 →L[ℝ] ℂ)).comp
      (T.symm : ℂ →L[ℝ] E 1) = 0 := by
    rw [hcon]; ext v; simp
  have h4 : (fderiv ℝ w (T (p - x))).comp ((T : E 1 →L[ℝ] ℂ).comp (T.symm : ℂ →L[ℝ] E 1))
      = fderiv ℝ w (T (p - x)) := by
    have h5 : (T : E 1 →L[ℝ] ℂ).comp (T.symm : ℂ →L[ℝ] E 1) = 1 := by
      ext v; simp
    rw [h5]
    ext v; simp
  have h6 : ((fderiv ℝ w (T (p - x))).comp (T : E 1 →L[ℝ] ℂ)).comp (T.symm : ℂ →L[ℝ] E 1)
      = (fderiv ℝ w (T (p - x))).comp ((T : E 1 →L[ℝ] ℂ).comp (T.symm : ℂ →L[ℝ] E 1)) :=
    ContinuousLinearMap.comp_assoc _ _ _
  rw [h6, h4] at h3
  exact h3

/-- A `J`-holomorphic function on `E 1` with everywhere nonvanishing differential yields the chart
required by the challenge theorem (`n = 1`), through `Submission.exists_chart_of_holomorphic`. -/
theorem exists_chart_one {U V : Set (E 1)} {J : E 1 → E 1 →L[ℝ] E 1} {x : E 1} {u : E 1 → ℂ}
    (hV : IsOpen V) (hVU : V ⊆ U) (hxV : x ∈ V) (hu : ContDiffOn ℝ ∞ u V)
    (hhol : ∀ y ∈ V, ∀ v : E 1, fderiv ℝ u y (J y v) = Complex.I * fderiv ℝ u y v)
    (hJ2 : ∀ y ∈ V, ∀ v : E 1, J y (J y v) = -v)
    (hd : ∀ y ∈ V, fderiv ℝ u y ≠ 0) :
    ∃ φ : OpenPartialHomeomorph (E 1) (F 1),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E 1 → F 1) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : F 1 → E 1) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E 1,
        fderiv ℝ (φ : E 1 → F 1) y (J y v)
          = Complex.I • fderiv ℝ (φ : E 1 → F 1) y v := by
  classical
  have hinv : ∀ y ∈ V, Function.Bijective
      (fderiv ℝ (fun y : E 1 => fun _ : Fin 1 => u y) y) := by
    intro y hy
    have h0 : fderiv ℝ (fun y : E 1 => fun _ : Fin 1 => u y) y
        = ContinuousLinearMap.pi (fun _ : Fin 1 => fderiv ℝ u y) := by
      rw [fderiv_pi]
      intro j
      exact ((hu.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp))
    rw [h0]
    constructor
    · intro a b hab
      have h := congrFun hab 0
      simp only [ContinuousLinearMap.pi_apply] at h
      exact (bijective_of_ne_zero (hJ2 y hy) (hhol y hy) (hd y hy)).1 h
    · intro c
      obtain ⟨v, hv⟩ := (bijective_of_ne_zero (hJ2 y hy) (hhol y hy) (hd y hy)).2 (c 0)
      refine ⟨v, ?_⟩
      funext i
      simp only [ContinuousLinearMap.pi_apply]
      rw [Subsingleton.elim i 0]
      exact hv
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ :=
    Submission.exists_chart_of_holomorphic (n := 1) hV hVU J hxV (fun _ : Fin 1 => u)
      (fun _ => hu) (fun _ y hy v => hhol y hy v) hinv
  exact ⟨φ, h1, h2, h3, h4, h5⟩

end

end Work.Beltrami
