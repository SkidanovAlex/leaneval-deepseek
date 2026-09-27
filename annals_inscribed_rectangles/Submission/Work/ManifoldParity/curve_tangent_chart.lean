import Mathlib
import Submission.Work.ManifoldParity.Defs

/-!
# A curve lying in `K` is tangent to the local graph charts of `K`

This file supplies the elementary local input for constructing a tangent field on a compact
locally-graph set `K ⊆ ℝⁿ` from a family of closed curves covering `K`:

* `hasFDerivAt_gmap`, `fderiv_gmap`: the derivative of the graph map `u ↦ u • eᵢ + η u`;
* `curve_tangent_chart`: if `γ` is a smooth curve with values in `K`, `γ t` lies in the chart
  neighbourhood `U` of a graph chart `(i, U, η)`, and `γ'(t) ≠ 0`, then `γ'(t)` is a non-zero
  multiple of the chart tangent `eᵢ + η'(tᵢ)(1)`.
-/

namespace Work.ManifoldParity

noncomputable section

open Set Function
open scoped Topology Manifold

abbrev ctSmooth : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {n : ℕ}

theorem hasFDerivAt_gmap (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n)) (u : ℝ)
    (hη : HasFDerivAt η (fderiv ℝ η u) u) :
    HasFDerivAt (gmap i η)
      (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ)) + fderiv ℝ η u) u := by
  have h1 : HasFDerivAt (fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ))
      (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))) u := by
    have h := (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt
      (x := u)
    have hf : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))))
        = fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) := by
      ext v; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rwa [hf] at h
  have h2 : gmap i η = fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u := rfl
  rw [h2]
  exact h1.add hη

theorem fderiv_gmap (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n)) (u : ℝ)
    (hη : HasFDerivAt η (fderiv ℝ η u) u) :
    fderiv ℝ (gmap i η) u (1 : ℝ) = EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η u) (1 : ℝ) := by
  rw [(hasFDerivAt_gmap i η u hη).fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply]

/-- **A curve in `K` is tangent to every local graph chart of `K`.** -/
theorem curve_tangent_chart (K : Set (EuclideanSpace ℝ (Fin n)))
    (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ → EuclideanSpace ℝ (Fin n))
    (hchart : IsGraphChart K i U η)
    (γ : ℝ → EuclideanSpace ℝ (Fin n)) (hγ : ContDiff ℝ ctSmooth γ) (hγK : ∀ t, γ t ∈ K)
    (t : ℝ) (hγU : γ t ∈ U) (hvel : fderiv ℝ γ t 1 ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧
      fderiv ℝ γ t 1 = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (γ t i)) (1 : ℝ)) := by
  obtain ⟨hUo, hηsm, hηi, hgr⟩ := hchart
  have hγc : Continuous γ := hγ.continuous
  have hγd : DifferentiableAt ℝ γ t := (hγ.contDiffAt).differentiableAt (by simp [ctSmooth])
  have hηd : DifferentiableAt ℝ η (γ t i) :=
    (hηsm.contDiffAt).differentiableAt (by simp [ctSmooth])
  have hev : ∀ᶠ s in 𝓝 t, γ s = gmap i η ((γ s) i) := by
    have h1 : ∀ᶠ s in 𝓝 t, γ s ∈ U := hγc.continuousAt (hUo.mem_nhds hγU)
    filter_upwards [h1] with s hs
    exact (hgr (γ s) hs).mp (hγK s)
  set ℓ : ℝ → ℝ := fun s => (γ s) i with hℓ
  have hℓd : DifferentiableAt ℝ ℓ t := by
    have h := (PiLp.proj 2 (fun _ : Fin n => ℝ) i).hasFDerivAt.comp t hγd.hasFDerivAt
    exact h.differentiableAt
  have hchain : HasFDerivAt (fun s => gmap i η (ℓ s))
      ((fderiv ℝ (gmap i η) (ℓ t)).comp (fderiv ℝ ℓ t)) t := by
    have h := (hasFDerivAt_gmap i η (ℓ t) hηd.hasFDerivAt).comp t hℓd.hasFDerivAt
    rw [Function.comp_def] at h
    rw [← (hasFDerivAt_gmap i η (ℓ t) hηd.hasFDerivAt).fderiv] at h
    exact h
  have heq : fderiv ℝ γ t = (fderiv ℝ (gmap i η) (ℓ t)).comp (fderiv ℝ ℓ t) := by
    rw [← hchain.fderiv]
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hev] with s hs
    simp only [hℓ]
    exact hs
  refine ⟨fderiv ℝ ℓ t 1, ?_, ?_⟩
  · intro hc
    have hzero : fderiv ℝ γ t 1 = 0 := by
      rw [heq]; simp [hc]
    exact hvel hzero
  · rw [heq]
    simp only [ContinuousLinearMap.comp_apply]
    have hsmul : fderiv ℝ (gmap i η) (ℓ t) ((fderiv ℝ ℓ t) 1)
        = ((fderiv ℝ ℓ t) 1) • (fderiv ℝ (gmap i η) (ℓ t) (1 : ℝ)) := by
      conv_lhs => rw [show (fderiv ℝ ℓ t) 1 = ((fderiv ℝ ℓ t) 1) • (1 : ℝ) from by simp]
      rw [map_smul]
    rw [hsmul, fderiv_gmap i η (ℓ t) hηd.hasFDerivAt]

end

end Work.ManifoldParity
