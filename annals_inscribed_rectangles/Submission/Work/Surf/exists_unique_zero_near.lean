import Mathlib

namespace Work.Surf

open Metric

/-- Quantitative inverse-function-theorem step: if `F` has an invertible derivative `L` at `p`, `F p = 0`,
and `G` is a `C^1` map whose derivative is uniformly close to that of `F` on a ball around `p`, while
`G p` is close to `F p`, then `G` has exactly one zero in that ball. -/
theorem exists_unique_zero_near {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F G : E → E) (hG : ContDiff ℝ 1 G) {p : E} (hp : F p = 0)
    (L : E ≃L[ℝ] E) (hL : (L : E →L[ℝ] E) = fderiv ℝ F p) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hFclose : ∀ x ∈ Metric.closedBall p ρ,
      ‖fderiv ℝ F x - fderiv ℝ F p‖ ≤ 1 / (4 * (‖(L.symm : E →L[ℝ] E)‖ + 1)))
    (hδ1 : δ ≤ 1 / (4 * (‖(L.symm : E →L[ℝ] E)‖ + 1)))
    (hδ2 : δ ≤ ρ / (2 * (‖(L.symm : E →L[ℝ] E)‖ + 1)))
    (hG0 : ‖G p - F p‖ < δ)
    (hG1 : ∀ x ∈ Metric.closedBall p ρ, ‖fderiv ℝ G x - fderiv ℝ F x‖ < δ) :
    ∃! x : E, x ∈ Metric.closedBall p ρ ∧ G x = 0 := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  set c : ℝ := ‖(L.symm : E →L[ℝ] E)‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
  have hc1 : 0 < c + 1 := by linarith
  have hδ1' : δ ≤ 1 / (4 * (c + 1)) := by simpa [hc] using hδ1
  have hδ2' : δ ≤ ρ / (2 * (c + 1)) := by simpa [hc] using hδ2
  set K : ℝ := c / (2 * (c + 1)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hK_half : K < 1 / 2 := by
    rw [hK, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (c + 1))]
    linarith
  have hK1 : K < 1 := by linarith
  let φ : E → E := fun z => z - (L.symm : E →L[ℝ] E) (G z)
  let g : E → E := fun z => G z - (L : E →L[ℝ] E) z
  -- (1) the derivative of `G` on the ball is close to `L`
  have hGL : ∀ x ∈ Metric.closedBall p ρ,
      ‖fderiv ℝ G x - (L : E →L[ℝ] E)‖ ≤ 1 / (2 * (c + 1)) := by
    intro x hx
    have h1 : ‖fderiv ℝ G x - fderiv ℝ F x‖ < δ := hG1 x hx
    have h2 : ‖fderiv ℝ F x - fderiv ℝ F p‖ ≤ 1 / (4 * (c + 1)) := by
      simpa [hc] using hFclose x hx
    have h3 : fderiv ℝ G x - (L : E →L[ℝ] E)
        = (fderiv ℝ G x - fderiv ℝ F x) + (fderiv ℝ F x - fderiv ℝ F p) := by
      rw [hL]; abel
    rw [h3]
    calc ‖(fderiv ℝ G x - fderiv ℝ F x) + (fderiv ℝ F x - fderiv ℝ F p)‖
        ≤ ‖fderiv ℝ G x - fderiv ℝ F x‖ + ‖fderiv ℝ F x - fderiv ℝ F p‖ := norm_add_le _ _
      _ ≤ δ + 1 / (4 * (c + 1)) := add_le_add h1.le h2
      _ ≤ 1 / (2 * (c + 1)) := by
          have hh : (1 : ℝ) / (2 * (c + 1)) = 1 / (4 * (c + 1)) + 1 / (4 * (c + 1)) := by
            field_simp
            ring
          linarith
  have hCLM : ∀ z : E, fderiv ℝ g z = fderiv ℝ G z - (L : E →L[ℝ] E) := by
    intro z
    change fderiv ℝ (G - ⇑(L : E →L[ℝ] E)) z = fderiv ℝ G z - (L : E →L[ℝ] E)
    rw [fderiv_sub (hGd z) (ContinuousLinearMap.differentiableAt (L : E →L[ℝ] E)),
      ContinuousLinearMap.fderiv]
  -- (2) `g` has Lipschitz constant `1/(2(c+1))` on the ball
  have hseg : ∀ x ∈ Metric.closedBall p ρ, ∀ y ∈ Metric.closedBall p ρ,
      ‖g y - g x‖ ≤ (1 / (2 * (c + 1))) * ‖y - x‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hGd z).sub (ContinuousLinearMap.differentiableAt (L : E →L[ℝ] E)))
      (fun z hz => by rw [hCLM z]; exact hGL z hz)
      (convex_closedBall p ρ) hx hy
  -- (3) hence `φ = id - L⁻¹ ∘ G` is `K`-Lipschitz on the ball, with `K = c/(2(c+1)) < 1`
  have hkey : ∀ x y : E, φ y - φ x = -((L.symm : E →L[ℝ] E) (g y - g x)) := by
    intro x y
    dsimp only [φ, g]
    simp only [map_sub]
    simp [ContinuousLinearEquiv.symm_apply_apply]
    abel_nf
  have hφ_lip : ∀ x ∈ Metric.closedBall p ρ, ∀ y ∈ Metric.closedBall p ρ,
      dist (φ x) (φ y) ≤ K * dist x y := by
    intro x hx y hy
    have h1 : ‖φ y - φ x‖ ≤ c * ‖g y - g x‖ := by
      rw [hkey, norm_neg]
      calc ‖(L.symm : E →L[ℝ] E) (g y - g x)‖ ≤ ‖(L.symm : E →L[ℝ] E)‖ * ‖g y - g x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = c * ‖g y - g x‖ := by rw [hc]
    have h2 : c * ‖g y - g x‖ ≤ c * ((1 / (2 * (c + 1))) * ‖y - x‖) :=
      mul_le_mul_of_nonneg_left (hseg x hx y hy) hc0
    have h3 : c * ((1 / (2 * (c + 1))) * ‖y - x‖) = K * ‖y - x‖ := by
      rw [hK]; ring
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖φ x - φ y‖ = ‖φ y - φ x‖ := norm_sub_rev _ _
      _ ≤ c * ‖g y - g x‖ := h1
      _ ≤ c * ((1 / (2 * (c + 1))) * ‖y - x‖) := h2
      _ = K * ‖y - x‖ := h3
      _ = K * ‖x - y‖ := by rw [norm_sub_rev]
  -- (4) the size of `φ p - p`
  have hKρ : K * ρ < ρ / 2 := by
    have h := mul_lt_mul_of_pos_right hK_half hρ
    linarith
  have hφ_p : dist (φ p) p < ρ / 2 := by
    have h1 : φ p - p = -((L.symm : E →L[ℝ] E) (G p)) := by
      dsimp only [φ]; abel
    have h2 : ‖(L.symm : E →L[ℝ] E) (G p)‖ ≤ c * ‖G p‖ := by
      calc ‖(L.symm : E →L[ℝ] E) (G p)‖ ≤ ‖(L.symm : E →L[ℝ] E)‖ * ‖G p‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = c * ‖G p‖ := by rw [hc]
    have h3 : ‖G p‖ < δ := by simpa [hp] using hG0
    have h4 : c * δ ≤ c * (ρ / (2 * (c + 1))) := mul_le_mul_of_nonneg_left hδ2' hc0
    have h5 : c * (ρ / (2 * (c + 1))) = K * ρ := by rw [hK]; ring
    rw [dist_eq_norm, h1, norm_neg]
    calc ‖(L.symm : E →L[ℝ] E) (G p)‖ ≤ c * ‖G p‖ := h2
      _ ≤ c * δ := mul_le_mul_of_nonneg_left h3.le hc0
      _ ≤ c * (ρ / (2 * (c + 1))) := h4
      _ = K * ρ := h5
      _ < ρ / 2 := hKρ
  -- (5) `φ` maps the ball into itself
  have hmap : Set.MapsTo φ (Metric.closedBall p ρ) (Metric.closedBall p ρ) := by
    intro x hx
    have h1 : dist (φ x) (φ p) ≤ K * dist x p :=
      hφ_lip x hx p (by simp [hρ.le])
    have h2 : K * dist x p ≤ K * ρ := by
      have hxp : dist x p ≤ ρ := mem_closedBall.mp hx
      exact mul_le_mul_of_nonneg_left hxp hK0
    have h3 : dist (φ x) (φ p) < ρ / 2 := lt_of_le_of_lt (le_trans h1 h2) hKρ
    rw [mem_closedBall]
    have h4 : dist (φ x) p ≤ dist (φ x) (φ p) + dist (φ p) p := dist_triangle _ _ _
    linarith
  -- (6) Banach fixed point
  have hcontr : ContractingWith ⟨K, hK0⟩
      (hmap.restrict φ (Metric.closedBall p ρ) (Metric.closedBall p ρ)) := by
    refine ⟨?_, ?_⟩
    · exact_mod_cast hK1
    · refine LipschitzWith.of_dist_le_mul ?_
      intro x y
      have hxy := hφ_lip x.1 x.2 y.1 y.2
      have e1 : ((hmap.restrict φ (Metric.closedBall p ρ) (Metric.closedBall p ρ)) x : E) = φ x.1 := rfl
      have e2 : ((hmap.restrict φ (Metric.closedBall p ρ) (Metric.closedBall p ρ)) y : E) = φ y.1 := rfl
      rw [Subtype.dist_eq, e1, e2, Subtype.dist_eq]
      exact hxy
  have hcompl : IsComplete (Metric.closedBall p ρ) := (Metric.isClosed_closedBall).isComplete
  obtain ⟨y, hy_mem, hy_fix, -, -⟩ :=
    ContractingWith.exists_fixedPoint' hcompl hmap hcontr
      (x := p) (by rw [mem_closedBall, dist_self]; exact hρ.le)
      (by rw [edist_dist]; exact ENNReal.ofReal_ne_top)
  have hy0 : G y = 0 := by
    have h1 : (L.symm : E →L[ℝ] E) (G y) = 0 := by
      have h2 : φ y = y := hy_fix
      dsimp only [φ] at h2
      exact sub_eq_self.mp h2
    have hinj : Function.Injective (L.symm : E →L[ℝ] E) := (L.symm).injective
    exact hinj (by rw [h1, map_zero])
  refine ⟨y, ⟨hy_mem, hy0⟩, ?_⟩
  intro z hz
  obtain ⟨hz_mem, hz0⟩ := hz
  have hzf : φ z = z := by dsimp only [φ]; rw [hz0, map_zero, sub_zero]
  have hyf : φ y = y := hy_fix
  have h := hφ_lip z hz_mem y hy_mem
  have hd : dist z y = dist (φ z) (φ y) := by rw [hzf, hyf]
  have h2 : dist z y ≤ K * dist z y := by
    calc dist z y = dist (φ z) (φ y) := hd
      _ ≤ K * dist z y := h
  have hd0 : dist z y = 0 := by nlinarith [(dist_nonneg : (0 : ℝ) ≤ dist z y), hK1]
  exact dist_eq_zero.mp hd0

end Work.Surf
