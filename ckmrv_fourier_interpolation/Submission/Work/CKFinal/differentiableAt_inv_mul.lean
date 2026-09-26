import Mathlib

namespace Work.CKFinal

open Filter Topology

/-- If `G` is complex differentiable on a punctured neighbourhood of `0` and the product
`q ↦ q⁻¹ * G q` tends to `0` along the punctured neighbourhood of `0`, then that product is
in fact complex differentiable at `0`.

This is Riemann's removable singularity theorem: `q ↦ q⁻¹ * G q` is holomorphic on a punctured
neighbourhood of `0` and is continuous at `0` (its punctured limit is `0`, which is also its
value at `0`), hence it is analytic at `0`. -/
theorem differentiableAt_inv_mul {G : ℂ → ℂ}
    (hd : ∀ᶠ q : ℂ in nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ, DifferentiableAt ℂ G q)
    (hlim : Filter.Tendsto (fun q : ℂ => q⁻¹ * G q) (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ) (nhds 0)) :
    DifferentiableAt ℂ (fun q : ℂ => q⁻¹ * G q) 0 := by
  let F : ℂ → ℂ := fun q => q⁻¹ * G q
  -- `F` is holomorphic on a punctured neighbourhood of `0`.
  have hdiff : ∀ᶠ z : ℂ in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z := by
    filter_upwards [hd, self_mem_nhdsWithin] with z hz hz0
    exact (differentiableAt_inv hz0).mul hz
  -- `F` is continuous at `0`: its value there is `0` and its punctured limit is `0`.
  have hF0 : F 0 = 0 := by simp [F]
  have hcont : ContinuousAt F 0 := by
    rw [continuousAt_iff_punctured_nhds]
    simpa [hF0] using hlim
  -- Riemann's removable singularity theorem, weak form.
  have hana : AnalyticAt ℂ F 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hcont
  simpa [F] using hana.differentiableAt

end Work.CKFinal
