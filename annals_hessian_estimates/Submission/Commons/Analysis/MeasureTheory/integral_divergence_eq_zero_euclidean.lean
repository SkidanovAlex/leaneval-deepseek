import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory Measure
open scoped Topology

namespace Commons.Analysis.MeasureTheory

/-- The `i`-th component of the divergence integral of a compactly supported `C¹` vector field
on `EuclideanSpace ℝ (Fin n)`, i.e. `∫ x, ∂ᵢ Vᵢ(x)`, vanishes.

This is the one-dimensional divergence theorem applied along the `i`-th coordinate direction,
obtained here by integration by parts: for the constant function `f ≡ 1` and the scalar function
`g = Vᵢ` one has `∫ 1 * g' = - ∫ 0 * g = 0`, and `g'` along `eᵢ` is exactly the `i`-th component
of `fderiv ℝ V · eᵢ`. -/
private theorem integral_fderiv_coord_eq_zero {n : ℕ} [Nonempty (Fin n)]
    (V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hV : ContDiff ℝ 1 V) (hc : HasCompactSupport V) (i : Fin n) :
    (∫ x, (fderiv ℝ V x (EuclideanSpace.single i 1)) i) = 0 := by
  -- the `i`-th coordinate projection, as a continuous linear map
  let p : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) i
  -- the "scalar times the `i`-th coordinate" pairing
  let B : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ p
  have hB : ∀ (c : ℝ) (w : EuclideanSpace ℝ (Fin n)), B c w = c * w i := by
    intro c w; simp [B, p]
  have hInt_fderiv : Integrable
      (fun x => ((fderiv ℝ V x) (EuclideanSpace.single i 1)) i) := by
    have h1 : HasCompactSupport (fun x => (fderiv ℝ V x) (EuclideanSpace.single i 1)) :=
      hc.fderiv_apply ℝ (EuclideanSpace.single i 1)
    have h2 : HasCompactSupport
        (fun x => ((fderiv ℝ V x) (EuclideanSpace.single i 1)) i) := by
      have := h1.comp_left (g := fun w : EuclideanSpace ℝ (Fin n) => w i) (by simp)
      simpa [Function.comp_def] using this
    exact (by fun_prop : Continuous
      fun x => ((fderiv ℝ V x) (EuclideanSpace.single i 1)) i).integrable_of_hasCompactSupport h2
  have hInt_V : Integrable (fun x => V x i) := by
    have h2 : HasCompactSupport (fun x => V x i) := by
      have := hc.comp_left (g := fun w : EuclideanSpace ℝ (Fin n) => w i) (by simp)
      simpa [Function.comp_def] using this
    exact (by fun_prop : Continuous fun x => V x i).integrable_of_hasCompactSupport h2
  have hf'g : Integrable (fun x =>
      B ((fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ)) x) (EuclideanSpace.single i 1))
        (V x)) := by
    have : (fun x => B ((fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ)) x)
        (EuclideanSpace.single i 1)) (V x)) = fun _ => (0:ℝ) := by
      funext x; simp
    rw [this]; exact integrable_zero _ _ _
  have hfg' : Integrable (fun x => B (1:ℝ)
      ((fderiv ℝ V x) (EuclideanSpace.single i 1))) := by
    have : (fun x => B (1:ℝ) ((fderiv ℝ V x) (EuclideanSpace.single i 1)))
        = fun x => ((fderiv ℝ V x) (EuclideanSpace.single i 1)) i := by
      funext x; rw [hB, one_mul]
    rw [this]; exact hInt_fderiv
  have hfg : Integrable (fun x => B (1:ℝ) (V x)) := by
    have : (fun x => B (1:ℝ) (V x)) = fun x => V x i := by
      funext x; rw [hB, one_mul]
    rw [this]; exact hInt_V
  have hf : ∀ x ∈ tsupport V,
      DifferentiableAt ℝ (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ)) x :=
    fun x _ => differentiableAt_const 1
  have hg : ∀ x ∈ tsupport (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ)),
      DifferentiableAt ℝ V x :=
    fun x _ => (hV.differentiable one_ne_zero).differentiableAt
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume) (E := EuclideanSpace ℝ (Fin n)) (F := ℝ) (G := EuclideanSpace ℝ (Fin n))
    (W := ℝ) (f := fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ)) (g := V)
    (v := EuclideanSpace.single i 1) (B := B) hf'g hfg' hfg hf hg
  have hlhs : (∫ x, B (1:ℝ) ((fderiv ℝ V x) (EuclideanSpace.single i 1)))
      = ∫ x, ((fderiv ℝ V x) (EuclideanSpace.single i 1)) i := by
    congr 1 with x; rw [hB, one_mul]
  have hrhs : (∫ x, B ((fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ)) x)
      (EuclideanSpace.single i 1)) (V x)) = 0 := by
    have : (fun x => B ((fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ)) x)
        (EuclideanSpace.single i 1)) (V x)) = fun _ => (0:ℝ) := by
      funext x; simp
    rw [this, integral_zero]
  rw [hlhs, hrhs, neg_zero] at h
  exact h

theorem integral_divergence_eq_zero_euclidean
    {n : ℕ} [Nonempty (Fin n)]
    (V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hV : ContDiff ℝ 1 V) (hc : HasCompactSupport V) :
    (∫ x, ∑ i : Fin n, (fderiv ℝ V x (EuclideanSpace.single i 1)) i) = 0 := by
  have hInt : ∀ i : Fin n, Integrable
      (fun x => (fderiv ℝ V x (EuclideanSpace.single i 1)) i) := by
    intro i
    have h1 : HasCompactSupport (fun x => (fderiv ℝ V x) (EuclideanSpace.single i 1)) :=
      hc.fderiv_apply ℝ (EuclideanSpace.single i 1)
    have h2 : HasCompactSupport
        (fun x => ((fderiv ℝ V x) (EuclideanSpace.single i 1)) i) := by
      have := h1.comp_left (g := fun w : EuclideanSpace ℝ (Fin n) => w i) (by simp)
      simpa [Function.comp_def] using this
    exact (by fun_prop : Continuous
      fun x => ((fderiv ℝ V x) (EuclideanSpace.single i 1)) i).integrable_of_hasCompactSupport h2
  have hterm : ∀ i : Fin n, (∫ x, (fderiv ℝ V x (EuclideanSpace.single i 1)) i) = 0 :=
    fun i => integral_fderiv_coord_eq_zero V hV hc i
  trans ∑ i : Fin n, ∫ x, (fderiv ℝ V x (EuclideanSpace.single i 1)) i
  · exact integral_finsetSum Finset.univ (fun i _ => hInt i)
  · simp [hterm]

end Commons.Analysis.MeasureTheory