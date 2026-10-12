import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Algebra.Order.Archimedean.Real.Hom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.LatSym

open scoped Topology

/-- For a smooth `c : ℝ³ → ℂ` vanishing in a neighbourhood of the origin, the function
`u ↦ c u * (⟪u,u⟫³)⁻¹` is smooth: away from the origin the factor `⟪u,u⟫³ = ‖u‖⁶` is
nonzero (so the inverse is smooth there), while on a ball around the origin `c` vanishes
identically, so the product is locally `0`. -/
theorem contDiff_mul_inv_innerSq3 {c : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (h0 : ∃ δ : ℝ, 0 < δ ∧ ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ < δ → c u = 0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 3) =>
        c u * ((((inner ℝ u u : ℝ) ^ 3 : ℝ)) : ℂ)⁻¹) := by
  obtain ⟨δ, hδpos, hδ⟩ := h0
  -- Smoothness of the (un-inverted) factor `u ↦ (⟪u,u⟫³ : ℂ)`.
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 3) => (((inner ℝ u u : ℝ) ^ 3 : ℝ) : ℂ)) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : EuclideanSpace ℝ (Fin 3) => inner ℝ u u) :=
      ContDiff.inner ℝ contDiff_id contDiff_id
    have h2 : ContDiff ℝ (⊤ : ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin 3) => (inner ℝ u u : ℝ) ^ 3) := h1.pow 3
    exact Complex.ofRealCLM.contDiff.comp h2
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u = 0
  · -- At the origin the product vanishes on a whole ball, hence is locally `0`.
    subst hu
    have hmem : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) δ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hδpos
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with v hv
    have hv' : c v = 0 := hδ v (by simpa [Metric.mem_ball, dist_zero_right] using hv)
    simp [hv']
  · -- Away from the origin `⟪u,u⟫³ = ‖u‖⁶ ≠ 0`, so the inverse is smooth.
    have hne : (((inner ℝ u u : ℝ) ^ 3 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      have hpos : 0 < (inner ℝ u u : ℝ) := by
        rw [real_inner_self_eq_norm_sq]
        exact pow_pos (norm_pos_iff.mpr hu) 2
      exact pow_ne_zero 3 (ne_of_gt hpos)
    exact (hc.contDiffAt).mul ((hF.contDiffAt).inv hne)

end Work.BoseBoxFock.LatSym
