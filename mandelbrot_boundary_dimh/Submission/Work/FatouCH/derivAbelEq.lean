import Mathlib

namespace Work.FatouCH

open scoped Topology

/-- Differentiation of the Abel relation: if `Φ`, `v` are holomorphic on `ball z₀ R` and `Φ (z + v z) = Φ z + 1` whenever `z` and `z + v z` both lie in `ball z₀ R`, then at such a `z` we have `deriv Φ (z + v z) * (1 + deriv v z) = deriv Φ z`. -/
theorem derivAbelEq (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ)
    (hΦ : DifferentiableOn ℂ Φ (Metric.ball z₀ R)) (hv : DifferentiableOn ℂ v (Metric.ball z₀ R))
    (hAbel : ∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ (z + v z) = Φ z + 1)
    {z : ℂ} (hz : z ∈ Metric.ball z₀ R) (hz' : z + v z ∈ Metric.ball z₀ R) :
    deriv Φ (z + v z) * (1 + deriv v z) = deriv Φ z := by
  -- The set `{w | w ∈ ball z₀ R ∧ w + v w ∈ ball z₀ R}` is a neighbourhood of `z`: openness of the
  -- ball and continuity of `w ↦ w + v w` (which follows from differentiability of `v`).
  have hball : Metric.ball z₀ R ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hz
  have hball' : Metric.ball z₀ R ∈ 𝓝 (z + v z) := Metric.isOpen_ball.mem_nhds hz'
  have hΦz : DifferentiableAt ℂ Φ z := hΦ.differentiableAt hball
  have hΦz' : DifferentiableAt ℂ Φ (z + v z) := hΦ.differentiableAt hball'
  have hvz : DifferentiableAt ℂ v z := hv.differentiableAt hball
  have hu : DifferentiableAt ℂ (fun w : ℂ => w + v w) z := differentiableAt_id.add hvz
  have hpre : (fun w : ℂ => w + v w) ⁻¹' Metric.ball z₀ R ∈ 𝓝 z :=
    hu.continuousAt.preimage_mem_nhds hball'
  -- So near `z` the function `w ↦ Φ (w + v w) - Φ w` is constantly `1`.
  have hconst : (fun w : ℂ => Φ (w + v w) - Φ w) =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
    filter_upwards [hball, hpre] with w hw hw'
    rw [hAbel w hw hw']
    ring
  have key : deriv (fun w : ℂ => Φ (w + v w) - Φ w) z = 0 := by
    rw [hconst.deriv_eq]
    simp
  -- Chain rule: the derivative of `w ↦ Φ (w + v w) - Φ w` at `z` is
  -- `Φ' (z + v z) * (1 + v' z) - Φ' z`.
  have h1 : HasDerivAt Φ (deriv Φ (z + v z)) (z + v z) := hΦz'.hasDerivAt
  have h2 : HasDerivAt (fun w : ℂ => w + v w) (1 + deriv v z) z :=
    (hasDerivAt_id (z : ℂ)).add hvz.hasDerivAt
  have h3 : HasDerivAt (fun w : ℂ => Φ (w + v w))
      (deriv Φ (z + v z) * (1 + deriv v z)) z := h1.comp z h2
  have h4 : HasDerivAt (fun w : ℂ => Φ (w + v w) - Φ w)
      (deriv Φ (z + v z) * (1 + deriv v z) - deriv Φ z) z :=
    h3.sub hΦz.hasDerivAt
  have hd := h4.deriv
  rw [key] at hd
  exact sub_eq_zero.mp hd.symm

end Work.FatouCH
