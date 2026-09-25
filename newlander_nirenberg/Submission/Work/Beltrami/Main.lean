/-
# The `n = 1` case of the Newlander--Nirenberg theorem

This file assembles the `n = 1` case of the challenge statement from the `ℂ`-picture Beltrami
solution (`Solve.lean` together with `exists_hol_of_beltrami`), using `Transfer.lean` to move
between `ℂ` and `E 1 = ℝ²`, and `Submission.exists_chart_of_holomorphic` to produce the chart.

`LocalHolInput` is the local input that the Beltrami argument provides on `ℂ`: near every point of
a smooth complex structure there is, on a small ball, a `J`-holomorphic function with nowhere
vanishing differential.
-/
import Mathlib
import Submission.Work.Beltrami.Solve
import Submission.Work.Beltrami.Transfer

namespace Work.Beltrami

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open scoped ContDiff Topology

noncomputable section

/-- The local input provided by the Beltrami argument on `ℂ`. -/
def LocalHolInput : Prop :=
  ∀ {J : ℂ → ℂ →L[ℝ] ℂ} {ρ : ℝ} (z₀ : ℂ), 0 < ρ →
    ContDiffOn ℝ ∞ J (Metric.ball z₀ ρ) →
    (∀ z ∈ Metric.ball z₀ ρ, ∀ v : ℂ, J z (J z v) = -v) →
    ∃ (w : ℂ → ℂ) (σ : ℝ), 0 < σ ∧ ContDiffOn ℝ ∞ w (Metric.ball z₀ σ) ∧
      (∀ z ∈ Metric.ball z₀ σ, ∀ v : ℂ,
        fderiv ℝ w z (J z v) = Complex.I * fderiv ℝ w z v) ∧
      (∀ z ∈ Metric.ball z₀ σ, fderiv ℝ w z ≠ 0)

/-- **The `n = 1` Newlander--Nirenberg theorem**, reduced to the local Beltrami input
`LocalHolInput`. -/
theorem newlander_nirenberg_one_of_hol (Hsolve : LocalHolInput)
    {U : Set (E 1)} (hU : IsOpen U) (J : E 1 → E 1 →L[ℝ] E 1) (hJ : IsAlmostComplexOn J U)
    {x : E 1} (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E 1) (F 1),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E 1 → F 1) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : F 1 → E 1) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E 1,
        fderiv ℝ (φ : E 1 → F 1) y (J y v)
          = Complex.I • fderiv ℝ (φ : E 1 → F 1) y v := by
  classical
  obtain ⟨hJsm, hJJ2⟩ := hJ
  obtain ⟨δ₀, hδ₀pos, hδ₀U⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  -- the structure pulled back to `ℂ`
  let J₁ : ℂ → ℂ →L[ℝ] ℂ := pullback eC x J
  have hJ₁apply : ∀ z v : ℂ, J₁ z v = eC (J (x + eC.symm z) (eC.symm v)) := by
    intro z v; simp [J₁, pullback]
  -- a radius on which the pulled-back structure is defined
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    Metric.continuousAt_iff.mp ((continuous_iff_continuousAt.mp eC.symm.continuous) (0 : ℂ)) δ₀ hδ₀pos
  have himg : ∀ z : ℂ, dist z 0 < δ₁ → x + eC.symm z ∈ U := by
    intro z hz
    apply hδ₀U
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have h1 := hδ₁ hz
    rw [dist_eq_norm] at h1
    have h2 : eC.symm (0 : ℂ) = (0 : E 1) := map_zero eC.symm
    rw [h2, sub_zero] at h1
    simpa using h1
  have hJ₁sm : ContDiffOn ℝ ∞ J₁ (Metric.ball 0 δ₁) := by
    rw [contDiffOn_clm_apply]
    intro v
    have h2 : ContDiffOn ℝ ∞ (fun z : ℂ => J (x + eC.symm z)) (Metric.ball 0 δ₁) :=
      hJsm.comp (by fun_prop) (fun z hz => himg z (by simpa [Metric.mem_ball] using hz))
    have h3 : ContDiffOn ℝ ∞ (fun z : ℂ => (J (x + eC.symm z)) (eC.symm v))
        (Metric.ball 0 δ₁) :=
      h2.clm_apply contDiffOn_const
    exact (ContinuousLinearMap.contDiff (n := ∞) ((eC : E 1 →L[ℝ] ℂ))).comp_contDiffOn h3
  have hJ₁2 : ∀ z ∈ Metric.ball 0 δ₁, ∀ v : ℂ, J₁ z (J₁ z v) = -v := by
    intro z hz v
    have hzU : x + eC.symm z ∈ U := himg z (by simpa [Metric.mem_ball] using hz)
    rw [hJ₁apply, hJ₁apply]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    rw [hJJ2 _ hzU (eC.symm v)]
    simp
  -- apply the local input
  obtain ⟨w, σ, hσpos, hwsm, hwhol, hwne⟩ := Hsolve 0 hδ₁pos hJ₁sm hJ₁2
  -- a radius around `x` on which everything holds
  obtain ⟨ε, hεpos, hε⟩ :=
    Metric.continuousAt_iff.mp ((continuous_iff_continuousAt.mp (eC : E 1 →L[ℝ] ℂ).continuous)
      (0 : E 1)) σ hσpos
  set V : Set (E 1) := Metric.ball x (min ε (min δ₁ δ₀)) with hV
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hxV : x ∈ V := by
    simp only [hV, Metric.mem_ball, dist_self]
    exact lt_min hεpos (lt_min hδ₁pos hδ₀pos)
  have hVU : V ⊆ U := by
    intro y hy
    apply hδ₀U
    simp only [hV, Metric.mem_ball, dist_eq_norm] at hy ⊢
    linarith [hy, min_le_right ε (min δ₁ δ₀), min_le_right δ₁ δ₀]
  have hball : ∀ y ∈ V, eC (y - x) ∈ Metric.ball 0 σ := by
    intro y hy
    have h1 : dist (y - x) 0 < ε := by
      simp only [hV, Metric.mem_ball, dist_eq_norm] at hy
      rw [dist_eq_norm, sub_zero]
      exact lt_of_lt_of_le hy (min_le_left ε (min δ₁ δ₀))
    have h2 := hε h1
    rw [dist_eq_norm] at h2
    have h3 : (eC : E 1 →L[ℝ] ℂ) 0 = (0 : ℂ) := map_zero (eC : E 1 →L[ℝ] ℂ)
    rw [h3, sub_zero] at h2
    simpa [Metric.mem_ball, dist_eq_norm] using h2
  have hdiff : ∀ y ∈ V, DifferentiableAt ℝ w (eC (y - x)) := by
    intro y hy
    exact (hwsm.differentiableOn (by simp)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hball y hy))
  have hu_sm : ContDiffOn ℝ ∞ (fun y : E 1 => w (eC (y - x))) V := by
    have h1 : ContDiffOn ℝ ∞ (fun y : E 1 => eC (y - x)) V := by
      have h2 : ContDiff ℝ ∞ (fun y : E 1 => (eC : E 1 →L[ℝ] ℂ) y - eC x) := by fun_prop
      exact h2.contDiffOn
    exact hwsm.comp h1 (fun y hy => hball y hy)
  have hu_hol : ∀ y ∈ V, ∀ v : E 1,
      fderiv ℝ (fun y : E 1 => w (eC (y - x))) y (J y v)
        = Complex.I * fderiv ℝ (fun y : E 1 => w (eC (y - x))) y v := by
    intro y hy v
    exact isJHolAt_comp eC x y (hdiff y hy) (fun u => hwhol _ (hball y hy) u) v
  have hu_ne : ∀ y ∈ V, fderiv ℝ (fun y : E 1 => w (eC (y - x))) y ≠ 0 := by
    intro y hy
    exact fderiv_ne_zero_comp eC x y (hdiff y hy) (hwne _ (hball y hy))
  exact exists_chart_one hVopen hVU hxV hu_sm hu_hol (fun y hy v => hJJ2 y (hVU hy) v) hu_ne

end

end Work.Beltrami
