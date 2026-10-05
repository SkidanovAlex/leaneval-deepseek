import Mathlib

/-!
# Differentiation under the integral sign for a parametric interval integral,
# from a *local* `C¹` hypothesis

If `G : ℝ × ℝ → F` is `C¹` on an *open* set `U` that contains the closed slab
`{s₀} ×ˢ uIcc a b`, then the function `s ↦ ∫ u in a..b, G (s,u)` is differentiable at every point
of some ball around `s₀`, with derivative `∫ u in a..b, (fderiv ℝ G (s,u)) ∘ inl`.

The proof localises the classical dominated-convergence argument for parametric integrals
(`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`) to a neighbourhood of the
compact slab: openness of `U` and compactness of `uIcc a b` produce a ball `ball s₀ ε` on which
the slab lies in `U`, the derivative `fderiv ℝ G` is continuous there (so it is bounded on the
compact set `closedBall s₀ (ε/2) ×ˢ uIcc a b`), and each slice is differentiable on that ball.

This is the `HasFDerivAt`-form, local analogue of the team's globally-`C¹` results
`Work.RPA3.hasFDerivAt_param_intervalIntegral` and
`Work.RPB.B3.hasFDerivAt_param_intervalIntegral_gen`.
-/

set_option autoImplicit false

namespace Work.RPB.B5

open MeasureTheory Set

open scoped Topology Interval

/-- Localisation of a slab: if `U` is open and contains `{s₀} ×ˢ uIcc a b`, then it contains a whole
`ball s₀ ε` times the interval. -/
private theorem exists_ball_prod_subset {s₀ a b : ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hsub : {s₀} ×ˢ Set.uIcc a b ⊆ U) :
    ∃ ε > 0, ∀ x ∈ Metric.ball s₀ ε, ∀ u ∈ Set.uIcc a b, (x, u) ∈ U := by
  have hev : ∀ᶠ x : ℝ in 𝓝 s₀, ∀ u ∈ Set.uIcc a b, (x, u) ∈ U := by
    refine isCompact_uIcc.eventually_forall_of_forall_eventually (fun u hu => ?_)
    have : (s₀, u) ∈ U := hsub ⟨by simp, hu⟩
    exact hU.mem_nhds this
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hev
  exact ⟨ε, hεpos, fun x hx u hu => hε hx u hu⟩

theorem paramIntegralHasFDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (G : ℝ × ℝ → F) {s₀ a b : ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U) (hsub : {s₀} ×ˢ Set.uIcc a b ⊆ U) :
    ∃ r > 0, ∀ s ∈ Metric.ball s₀ r,
      HasFDerivAt (fun s : ℝ => ∫ u in a..b, G (s, u))
        (∫ u in a..b, (fderiv ℝ G (s, u)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) s := by
  obtain ⟨ε, hεpos, hε⟩ := exists_ball_prod_subset hU hsub
  -- the compact slab on which the derivative will be bounded
  have hK2 : IsCompact (Metric.closedBall s₀ (ε / 2) ×ˢ Set.uIcc a b) :=
    (isCompact_closedBall s₀ (ε / 2)).prod isCompact_uIcc
  have hK2U : Metric.closedBall s₀ (ε / 2) ×ˢ Set.uIcc a b ⊆ U := by
    intro z hz
    have hd : dist z.1 s₀ ≤ ε / 2 := Metric.mem_closedBall.mp hz.1
    exact hε z.1 (by rw [Metric.mem_ball]; linarith) z.2 hz.2
  have hballU : ∀ x ∈ Metric.ball s₀ (ε / 2), ∀ u ∈ Set.uIcc a b, (x, u) ∈ U := by
    intro x hx u hu
    have hd : dist x s₀ < ε / 2 := Metric.mem_ball.mp hx
    exact hε x (by rw [Metric.mem_ball]; linarith) u hu
  -- the `fderiv` of a `C¹` function on an open set is continuous at every point of it
  have hfdcont : ∀ p ∈ U, ContinuousAt (fderiv ℝ G) p := by
    intro p hp
    have hcd : ContDiffAt ℝ 1 G p := hG.contDiffAt (hU.mem_nhds hp)
    exact hcd.continuousAt_fderiv (by norm_num)
  -- the partial derivative in the parameter direction, as a linear map `ℝ →L[ℝ] F`
  let T : ((ℝ × ℝ) →L[ℝ] F) →L[ℝ] (ℝ →L[ℝ] F) :=
    ContinuousLinearMap.precomp F (ContinuousLinearMap.inl ℝ ℝ ℝ)
  have hpre : ∀ A : (ℝ × ℝ) →L[ℝ] F,
      T A = A.comp (ContinuousLinearMap.inl ℝ ℝ ℝ) := fun A =>
    ContinuousLinearMap.precomp_apply F (ContinuousLinearMap.inl ℝ ℝ ℝ) A
  let φ : ℝ × ℝ → (ℝ →L[ℝ] F) :=
    fun z => (fderiv ℝ G z).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)
  have hφT : φ = fun z => T (fderiv ℝ G z) := funext (fun z => (hpre (fderiv ℝ G z)).symm)
  have hφcont : ∀ p ∈ U, ContinuousAt φ p := by
    intro p hp
    have h2 : ContinuousAt (fun z => T (fderiv ℝ G z)) p :=
      (T.continuous.continuousAt.comp (hfdcont p hp))
    rw [hφT]
    exact h2
  -- slices are continuous on the interval
  have hGslice : ∀ x : ℝ, (∀ u ∈ Set.uIcc a b, (x, u) ∈ U) →
      ContinuousOn (fun u : ℝ => G (x, u)) (Set.uIcc a b) := by
    intro x hx
    refine fun u hu => ?_
    have hca : ContinuousAt (fun u : ℝ => G (x, u)) u :=
      ((hG.continuousOn.continuousAt (hU.mem_nhds (hx u hu))).comp
        (continuousAt_const.prodMk continuousAt_id))
    exact hca.continuousWithinAt
  have hφslice : ∀ x : ℝ, (∀ u ∈ Set.uIcc a b, (x, u) ∈ U) →
      ContinuousOn (fun u : ℝ => φ (x, u)) (Set.uIcc a b) := by
    intro x hx
    refine fun u hu => ?_
    have hca : ContinuousAt (fun u : ℝ => φ (x, u)) u :=
      ((hφcont (x, u) (hx u hu)).comp
        (continuousAt_const.prodMk continuousAt_id))
    exact hca.continuousWithinAt
  -- uniform bound on the compact slab
  have hφcontK : ContinuousOn φ (Metric.closedBall s₀ (ε / 2) ×ˢ Set.uIcc a b) :=
    fun p hp => (hφcont p (hK2U hp)).continuousWithinAt
  obtain ⟨C, hC⟩ := hK2.exists_bound_of_continuousOn hφcontK
  refine ⟨ε / 2, by positivity, fun s hs => ?_⟩
  have hsU : ∀ u ∈ Set.uIcc a b, (s, u) ∈ U := hballU s hs
  have key : HasFDerivAt (fun x : ℝ => ∫ u in a..b, G (x, u))
      (∫ u in a..b, φ (s, u)) s := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume) (F := fun x u => G (x, u)) (F' := fun x u => φ (x, u))
      (s := Metric.ball s₀ (ε / 2)) (bound := fun _ => C)
      (Metric.isOpen_ball.mem_nhds hs) ?_ ?_ ?_ ?_ ?_ ?_
    · have hmem : ∀ᶠ x : ℝ in 𝓝 s, x ∈ Metric.ball s₀ (ε / 2) :=
        Metric.isOpen_ball.mem_nhds hs
      refine hmem.mono (fun x hx => ?_)
      exact ((hGslice x (hballU x hx)).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc
    · exact (hGslice s hsU).intervalIntegrable
    · exact ((hφslice s hsU).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
      refine hC (x, t) ⟨?_, Set.uIoc_subset_uIcc ht⟩
      rw [Metric.mem_closedBall]
      exact le_of_lt (Metric.mem_ball.mp hx)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
      have hxU : (x, t) ∈ U := hballU x hx t (Set.uIoc_subset_uIcc ht)
      have hd : DifferentiableAt ℝ G (x, t) :=
        (hG.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)
      simpa only [φ, Function.comp_def] using
        (hd.hasFDerivAt.comp (𝕜 := ℝ) (x := x) (hasFDerivAt_prodMk_left x t))
  simpa only [φ] using key

end Work.RPB.B5
