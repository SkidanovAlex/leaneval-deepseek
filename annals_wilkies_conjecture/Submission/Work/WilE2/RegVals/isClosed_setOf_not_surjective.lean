import Mathlib

namespace Work.WilE2.RegVals

open ContinuousLinearMap

/-- **The surjective maps are open.**  A surjective continuous linear map
`T : ℝⁿ → ℝᵐ` admits a continuous right inverse `σ` (surjectivity gives a linear right
inverse, continuous because `ℝᵐ` is finite dimensional), and for any `S` with
`‖S - T‖ < (‖σ‖ + 1)⁻¹` one has

`S ∘ σ = T ∘ σ + (S - T) ∘ σ = 1 + (S - T) ∘ σ`,

with `‖(S - T) ∘ σ‖ < 1`, so `1 + (S - T) ∘ σ` is invertible and `S` has a right inverse, hence
is surjective. -/
theorem isOpen_setOf_surjective {n m : ℕ} :
    IsOpen {T : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) | Function.Surjective T} := by
  rw [isOpen_iff_mem_nhds]
  intro T hT
  -- a linear right inverse of `T`, continuous because the target is finite dimensional
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective T.toLinearMap
    (LinearMap.range_eq_top.2 (fun y => hT y))
  have hgc : Continuous g := g.continuous_of_finiteDimensional
  let g' : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) := ⟨g, hgc⟩
  have hTg : T.comp g' = ContinuousLinearMap.id ℝ (Fin m → ℝ) :=
    ContinuousLinearMap.ext fun x => by
      have hx : T (g x) = x := LinearMap.ext_iff.1 hg x
      simpa [g'] using hx
  have hεpos : (0 : ℝ) < (‖g'‖ + 1)⁻¹ := by positivity
  refine Filter.mem_of_superset (Metric.ball_mem_nhds T hεpos) ?_
  intro S hS
  rw [Metric.mem_ball, dist_eq_norm] at hS
  set X : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := (S - T).comp g' with hXdef
  -- the perturbation `X = (S - T) ∘ g'` has norm `< 1`
  have hX : ‖X‖ < 1 := by
    have h1 : ‖S - T‖ * (‖g'‖ + 1) < (‖g'‖ + 1)⁻¹ * (‖g'‖ + 1) :=
      mul_lt_mul_of_pos_right hS (by positivity)
    have h2 : (‖g'‖ + 1)⁻¹ * (‖g'‖ + 1) = 1 := inv_mul_cancel₀ (by positivity)
    have h3 : ‖X‖ ≤ ‖S - T‖ * ‖g'‖ := by
      rw [hXdef]; exact ContinuousLinearMap.opNorm_comp_le _ _
    have h4 : ‖S - T‖ * ‖g'‖ ≤ ‖S - T‖ * (‖g'‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg g']) (norm_nonneg (S - T))
    linarith
  -- hence `1 + X` is a unit, with inverse `w`
  have hunit : IsUnit ((1 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) + X) := by
    have hneg : ‖-X‖ < 1 := by rw [norm_neg]; exact hX
    have h : IsUnit ((1 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) - -X) :=
      IsUnit.one_sub_of_norm_lt_one (x := -X) hneg
    rwa [sub_neg_eq_add] at h
  obtain ⟨u, hu⟩ := hunit
  rw [ContinuousLinearMap.one_def] at hu
  set w : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := (↑u⁻¹ : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) with hw
  have huw : (ContinuousLinearMap.id ℝ (Fin m → ℝ) + X).comp w
      = ContinuousLinearMap.id ℝ (Fin m → ℝ) := by
    have h : (↑u : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))
        * (↑u⁻¹ : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) = 1 := by simp
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.mul_def, hu, ← hw] at h
    exact h
  have hsub : X = S.comp g' - T.comp g' := by
    rw [hXdef]; exact ContinuousLinearMap.sub_comp S T g'
  have hsplit : S.comp g' = X + ContinuousLinearMap.id ℝ (Fin m → ℝ) := by
    rw [hsub, hTg, sub_add_cancel]
  have huw2 : w + X.comp w = ContinuousLinearMap.id ℝ (Fin m → ℝ) := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.id_comp] at huw
    exact huw
  -- `g' ∘ w` is a right inverse of `S`
  have hcomp : S.comp (g'.comp w) = ContinuousLinearMap.id ℝ (Fin m → ℝ) := by
    rw [← ContinuousLinearMap.comp_assoc, hsplit, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.id_comp, add_comm]
    exact huw2
  intro y
  refine ⟨(g'.comp w) y, ?_⟩
  have h := congrArg (fun f : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => f y) hcomp
  simpa [ContinuousLinearMap.comp_apply] using h

/-- **The non-surjective maps are closed**, i.e. surjectivity is an open condition for continuous
linear maps `ℝⁿ → ℝᵐ`. -/
theorem isClosed_setOf_not_surjective {n m : ℕ} :
    IsClosed {T : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) | ¬ Function.Surjective T} := by
  have hopen : IsOpen {T : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) | Function.Surjective T} :=
    isOpen_setOf_surjective
  rw [show {T : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) | ¬ Function.Surjective T}
      = {T : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) | Function.Surjective T}ᶜ from rfl]
  exact isClosed_compl_iff.mpr hopen

end Work.WilE2.RegVals
