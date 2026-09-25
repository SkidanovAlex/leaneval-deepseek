import Mathlib
import Submission.Work.CR.Flat.Cauchy.iteratedFDeriv_succ_of_slice_bounds

namespace Work.NN.Core

open Set Filter
open scoped Topology

/-- Auxiliary lemma: under the slice hypotheses, `iteratedFDeriv ℝ k F` is differentiable at every
point of `Ω`, with an explicitly constructed continuous linear derivative.

The candidate derivative `D` is built by currying: for each direction `v` the multilinear map
`u ↦ L u v` is bounded by `K * ‖v‖` because of `hbound`, and the Hölder estimate `hholder` turns
into the little-o remainder through the Taylor bound
`Work.CR.Flat.Cauchy.norm_sub_fderiv_le_of_fderiv_holder`. -/
lemma exists_hasFDerivAt_iteratedFDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {k : ℕ} {F : E → ℂ} {Ω : Set E} (hΩopen : IsOpen Ω)
    (hΩconv : Convex ℝ Ω) {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hdiff : ∀ u : Fin k → E, ∀ z ∈ Ω,
      DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ k F y u) z)
    (hbound : ∀ u : Fin k → E, ∀ z ∈ Ω,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z‖ ≤ K * ∏ i, ‖u i‖)
    (hholder : ∀ u : Fin k → E, ∀ z ∈ Ω, ∀ z' ∈ Ω,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z
        - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z'‖
        ≤ K * (∏ i, ‖u i‖) * ‖z - z'‖ ^ α) :
    ∀ z ∈ Ω, ∃ D : E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ),
      HasFDerivAt (iteratedFDeriv ℝ k F) D z := by
  have hprod_nonneg : ∀ u : Fin k → E, 0 ≤ ∏ i, ‖u i‖ :=
    fun u => Finset.prod_nonneg (fun i _ => norm_nonneg _)
  intro z hz
  obtain ⟨L, hL⟩ := Work.CR.Flat.Cauchy.multilinearMap_fderiv_of_apply_differentiable
    (Φ := iteratedFDeriv ℝ k F) (z := z) (fun u => hdiff u z hz)
  let Lv : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin k => E) ℂ :=
    { toFun := fun v =>
        { toFun := fun u => L u v
          map_update_add' := by
            intro _ u j x y
            simpa only [add_apply] using
              congrArg (fun f : E →L[ℝ] ℂ => f v) (MultilinearMap.map_update_add L u j x y)
          map_update_smul' := by
            intro _ u j c x
            simpa only [smul_apply] using
              congrArg (fun f : E →L[ℝ] ℂ => f v) (MultilinearMap.map_update_smul L u j c x) }
      map_add' := by
        intro v w
        ext u
        exact map_add (L u) v w
      map_smul' := by
        intro c v
        ext u
        exact map_smul (L u) c v }
  have hLv : ∀ v u, Lv v u = L u v := fun v u => rfl
  let D : E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ) :=
    MultilinearMap.mkContinuousLinear Lv K (fun v u => by
      rw [hLv]
      calc ‖L u v‖ ≤ ‖L u‖ * ‖v‖ := ContinuousLinearMap.le_opNorm (L u) v
        _ ≤ (K * ∏ i, ‖u i‖) * ‖v‖ := by
              gcongr
              simpa only [hL u] using hbound u z hz
        _ = K * ‖v‖ * ∏ i, ‖u i‖ := by ring)
  have hD : ∀ v u, D v u = L u v := by
    intro v u
    simp only [D, MultilinearMap.mkContinuousLinear, LinearMap.mkContinuous_apply]
    exact hLv v u
  refine ⟨D, ?_⟩
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hKc : Tendsto (fun y : E => K * ‖y - z‖ ^ α) (𝓝 z) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : E => K) (𝓝 z) (𝓝 K)).mul
        ((tendsto_norm_sub_self z).rpow_const_nhds_zero hα)
  filter_upwards [(tendsto_order.1 hKc).2 c hc, hΩopen.mem_nhds hz] with y hylt hymem
  have hCnn : 0 ≤ K * ‖y - z‖ ^ α * ‖y - z‖ :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg _)
  have hbd : ‖iteratedFDeriv ℝ k F y - iteratedFDeriv ℝ k F z - D (y - z)‖
      ≤ K * ‖y - z‖ ^ α * ‖y - z‖ := by
    rw [ContinuousMultilinearMap.opNorm_le_iff hCnn]
    intro u
    have hpt : (iteratedFDeriv ℝ k F y - iteratedFDeriv ℝ k F z - D (y - z)) u
        = (fun y' => iteratedFDeriv ℝ k F y' u) y - (fun y' => iteratedFDeriv ℝ k F y' u) z
          - fderiv ℝ (fun y' => iteratedFDeriv ℝ k F y' u) z (y - z) := by
      simp only [sub_apply, hD, hL]
    rw [hpt]
    have hA' := Work.CR.Flat.Cauchy.norm_sub_fderiv_le_of_fderiv_holder
      (g := fun y' => iteratedFDeriv ℝ k F y' u)
      hΩconv hα (mul_nonneg hK (hprod_nonneg u))
      (fun y' hy' => hdiff u y' hy')
      (fun y' hy' z' hz' => hholder u y' hy' z' hz') hz hymem
    calc ‖(fun y' => iteratedFDeriv ℝ k F y' u) y - (fun y' => iteratedFDeriv ℝ k F y' u) z
            - fderiv ℝ (fun y' => iteratedFDeriv ℝ k F y' u) z (y - z)‖
        ≤ (K * ∏ i, ‖u i‖) * ‖y - z‖ ^ α * ‖y - z‖ := hA'
      _ = (K * ‖y - z‖ ^ α * ‖y - z‖) * ∏ i, ‖u i‖ := by ring
  calc ‖iteratedFDeriv ℝ k F y - iteratedFDeriv ℝ k F z - D (y - z)‖
      ≤ K * ‖y - z‖ ^ α * ‖y - z‖ := hbd
    _ ≤ c * ‖y - z‖ := mul_le_mul_of_nonneg_right (le_of_lt hylt) (norm_nonneg _)

theorem diff_iter_of_slice_bounds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {k : ℕ} {F : E → ℂ} {Ω : Set E} (hΩopen : IsOpen Ω)
    (hΩconv : Convex ℝ Ω) {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hdiff : ∀ u : Fin k → E, ∀ z ∈ Ω,
      DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ k F y u) z)
    (hbound : ∀ u : Fin k → E, ∀ z ∈ Ω,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z‖ ≤ K * ∏ i, ‖u i‖)
    (hholder : ∀ u : Fin k → E, ∀ z ∈ Ω, ∀ z' ∈ Ω,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z
        - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z'‖
        ≤ K * (∏ i, ‖u i‖) * ‖z - z'‖ ^ α) :
    ∀ z ∈ Ω, DifferentiableAt ℝ (iteratedFDeriv ℝ k F) z := by
  intro z hz
  obtain ⟨D, hD⟩ := exists_hasFDerivAt_iteratedFDeriv (k := k) (F := F) (Ω := Ω)
    hΩopen hΩconv hα hK hdiff hbound hholder z hz
  exact hD.differentiableAt

end Work.NN.Core
