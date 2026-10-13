import Mathlib
import Submission.Work.WilE7.DimAPI.eventually_surjective_of_det_ne_zero

set_option autoImplicit false
noncomputable section

namespace Work.WilE7.DimAPI

/-- General form of `ker_comp_eq_ker_of_finrank_range_eq` for a composite `π.comp T` with
`T : V →ₗ W` and `π : W →ₗ U`.  If the range of `π.comp T` has the same dimension as the
range of `T`, then the two kernels coincide.  Indeed `T.ker ≤ (π.comp T).ker` always, and
rank–nullity for `T` and for `π.comp T` (over the common finite-dimensional domain `V`)
forces the two kernels to have equal dimension. -/
theorem ker_comp_eq_ker_of_finrank_range_eq_gen {V W U : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]
    (T : V →ₗ[ℝ] W) (π : W →ₗ[ℝ] U)
    (h : Module.finrank ℝ (π.comp T).range = Module.finrank ℝ T.range) :
    (π.comp T).ker = T.ker := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq (LinearMap.ker_le_ker_comp T π) ?_
  have hT := LinearMap.finrank_range_add_finrank_ker T
  have hC := LinearMap.finrank_range_add_finrank_ker (π.comp T)
  omega

/-- **Kernel of the derivative is unchanged by a rank-preserving projection, locally.**

Let `g : ℝ^K → ℝ^P` be analytic at `x`, let the differential `dg_y` have constant rank `M` on a
neighbourhood of `x`, and let `π : ℝ^P → ℝ^M` be a linear map whose composition with `dg_x` is
surjective.  Then, near `x`, `ker (π ∘ dg_y) = ker (dg_y)`.

Indeed `π ∘ dg_x` is surjective, hence has a right inverse `ℓ`; the family
`y ↦ (π ∘ dg_y) ∘ ℓ` of endomorphisms of `ℝ^M` is continuous at `x` (since `g` is analytic, so
`dg` is continuous) and equals the identity there, so its determinant is nonzero on a
neighbourhood of `x`, on which `π ∘ dg_y` is again surjective.  There
`ker (π ∘ dg_y)` has dimension `K - M`, the same as `ker (dg_y)` (which equals `K - M` because
`dg_y` has rank `M` by assumption); since `ker (dg_y) ⊆ ker (π ∘ dg_y)`, the two coincide. -/
theorem eventually_ker_comp_fderiv_eq {K P M : ℕ} (g : (Fin K → ℝ) → (Fin P → ℝ))
    (x : Fin K → ℝ) (hg : AnalyticAt ℝ g x)
    (hrank : ∀ᶠ y in nhds x, Module.finrank ℝ (fderiv ℝ g y).range = M)
    (π : (Fin P → ℝ) →L[ℝ] (Fin M → ℝ))
    (hπ : Function.Surjective fun v : Fin K → ℝ => π ((fderiv ℝ g x) v)) :
    ∀ᶠ y in nhds x, (π.comp (fderiv ℝ g y)).ker = (fderiv ℝ g y).ker := by
  -- `fderiv ℝ g` is continuous at `x`, since `g` is analytic there.
  have hcont : ContinuousAt (fderiv ℝ g) x :=
    (hg.contDiffAt (n := 1)).continuousAt_fderiv (by norm_num)
  -- The projection of the derivative is surjective at `x`, so it has a right inverse `ℓ`.
  have hrange_c : (π.comp (fderiv ℝ g x)).range = ⊤ := LinearMap.range_eq_top.mpr hπ
  obtain ⟨ℓ, hℓ⟩ :=
    ContinuousLinearMap.exists_rightInverse_of_surjective (π.comp (fderiv ℝ g x)) hrange_c
  -- The family `y ↦ (π ∘ dg_y) ∘ ℓ` of endomorphisms of `ℝ^M` is continuous at `x`.
  have hGcont : ContinuousAt (fun y : Fin K → ℝ => (π.comp (fderiv ℝ g y)).comp ℓ) x :=
    (((ContinuousLinearMap.compL ℝ (Fin M → ℝ) (Fin K → ℝ) (Fin M → ℝ)).flip ℓ).comp
      ((ContinuousLinearMap.compL ℝ (Fin K → ℝ) (Fin P → ℝ) (Fin M → ℝ)) π)).continuous.continuousAt.comp
        hcont
  -- At `x` it is the identity, so its determinant is `1 ≠ 0`.
  have hGc : ((π.comp (fderiv ℝ g x)).comp ℓ).det ≠ 0 := by
    rw [hℓ]
    simp [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
  -- Hence near `x` the projection of the derivative is surjective.
  have hsurj_ev : ∀ᶠ y in nhds x,
      Function.Surjective fun v : Fin K → ℝ => π ((fderiv ℝ g y) v) := by
    filter_upwards [eventually_surjective_of_det_ne_zero
      (fun y : Fin K → ℝ => (π.comp (fderiv ℝ g y)).comp ℓ) hGcont hGc] with y hy
    intro w
    obtain ⟨u, hu⟩ := hy w
    exact ⟨ℓ u, by simpa only [ContinuousLinearMap.comp_apply] using hu⟩
  -- Finally, on the neighbourhood where this holds and where the rank of `dg` is `M`, the
  -- kernels agree.
  filter_upwards [hsurj_ev, hrank] with y hySurj hyrank
  have hcoe : ((π.comp (fderiv ℝ g y) : (Fin K → ℝ) →L[ℝ] (Fin M → ℝ)) :
      (Fin K → ℝ) →ₗ[ℝ] (Fin M → ℝ)) =
      (π : (Fin P → ℝ) →ₗ[ℝ] (Fin M → ℝ)).comp
        ((fderiv ℝ g y) : (Fin K → ℝ) →ₗ[ℝ] (Fin P → ℝ)) := by
    ext w; rfl
  have hfin : Module.finrank ℝ ((π : (Fin P → ℝ) →ₗ[ℝ] (Fin M → ℝ)).comp
        ((fderiv ℝ g y) : (Fin K → ℝ) →ₗ[ℝ] (Fin P → ℝ))).range
      = Module.finrank ℝ ((fderiv ℝ g y) : (Fin K → ℝ) →ₗ[ℝ] (Fin P → ℝ)).range := by
    rw [← hcoe]
    rw [show ((π.comp (fderiv ℝ g y)) : (Fin K → ℝ) →ₗ[ℝ] (Fin M → ℝ)).range = ⊤ from
      LinearMap.range_eq_top.mpr hySurj, Submodule.topEquiv.finrank_eq, Module.finrank_fin_fun]
    exact hyrank.symm
  have hker := ker_comp_eq_ker_of_finrank_range_eq_gen
      ((fderiv ℝ g y) : (Fin K → ℝ) →ₗ[ℝ] (Fin P → ℝ))
      (π : (Fin P → ℝ) →ₗ[ℝ] (Fin M → ℝ)) hfin
  rw [← hcoe] at hker
  exact hker

end Work.WilE7.DimAPI
