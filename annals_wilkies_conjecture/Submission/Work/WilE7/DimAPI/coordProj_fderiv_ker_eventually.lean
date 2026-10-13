import Mathlib
import Submission.Work.WilE7.DimAPI.ker_comp_eq_ker_of_finrank_range_eq
import Submission.Work.WilE7.DimAPI.eventually_surjective_of_det_ne_zero

set_option autoImplicit false
noncomputable section

namespace Work.WilE7.DimAPI

/-- The coordinate projection `v ↦ (fun i ↦ v (ı i))`, bundled as a continuous linear map. -/
def coordProjCLM {D r : ℕ} (ı : Fin r ↪ Fin D) : (Fin D → ℝ) →L[ℝ] (Fin r → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (ı i))

@[simp]
lemma coordProjCLM_apply {D r : ℕ} (ı : Fin r ↪ Fin D) (v : Fin D → ℝ) :
    coordProjCLM ı v = fun i => v (ı i) := by
  funext i
  simp [coordProjCLM]

/-- **Coordinate projection of the derivative is injective on the range, locally.**

Let `Ω ⊆ ℝ^D` be open, `γ` analytic on `Ω`, and suppose that at every point `y ∈ Ω` the
differential `fderiv ℝ γ y` has range of the fixed dimension `r`.  If at the point `c` the
coordinate projection onto the `r` coordinates selected by an embedding `ı : Fin r ↪ Fin D`
is surjective on the range of `fderiv ℝ γ c`, then the same projection is *injective* on the
range of `fderiv ℝ γ y` for all `y` near `c`: a vector `v` whose `ı`-coordinates of
`(fderiv ℝ γ y) v` all vanish must satisfy `(fderiv ℝ γ y) v = 0`.

Indeed, `π ∘ fderiv ℝ γ c` is surjective, hence has a right inverse `ℓ`, and the family
`y ↦ (π ∘ fderiv ℝ γ y) ∘ ℓ` of endomorphisms of `ℝ^r` is continuous at `c` and equals the
identity there; so its determinant is nonzero on a neighbourhood of `c`, and on that
neighbourhood `π ∘ fderiv ℝ γ y` is again surjective.  There
`ker ((π ∘ fderiv ℝ γ y))` has the same dimension `D - r` as `ker (fderiv ℝ γ y)` (both equal
`D - r`), and since it contains `ker (fderiv ℝ γ y)` the two kernels coincide. -/
theorem coordProj_fderiv_ker_eventually {D : ℕ} {Ω : Set (Fin D → ℝ)} (hΩ : IsOpen Ω)
    {γ : (Fin D → ℝ) → (Fin D → ℝ)} (hγ : AnalyticOnNhd ℝ γ Ω)
    {c : Fin D → ℝ} (hc : c ∈ Ω)
    {r : ℕ} (hr : ∀ y ∈ Ω, Module.finrank ℝ (fderiv ℝ γ y).range = r)
    (ı : Fin r ↪ Fin D)
    (hı : Function.Surjective fun v : Fin D → ℝ => (fderiv ℝ γ c) v ∘ ı) :
    ∀ᶠ y in nhds c, ∀ v : Fin D → ℝ, (fun i => (fderiv ℝ γ y) v (ı i)) = 0 →
      (fderiv ℝ γ y) v = 0 := by
  -- The projection onto the `ı`-coordinates.
  set π : (Fin D → ℝ) →L[ℝ] (Fin r → ℝ) := coordProjCLM ı with hπ
  -- `fderiv ℝ γ` is continuous at `c`, since `γ` is analytic there.
  have hcont : ContinuousAt (fderiv ℝ γ) c :=
    ((hγ c hc).contDiffAt (n := 1)).continuousAt_fderiv (by norm_num)
  -- The projection of the derivative is surjective at `c`.
  have hı' : Function.Surjective fun v : Fin D → ℝ => π ((fderiv ℝ γ c) v) := by
    intro w
    obtain ⟨v, hv⟩ := hı w
    refine ⟨v, ?_⟩
    funext i
    simpa only [hπ, coordProjCLM_apply, Function.comp_apply] using congrFun hv i
  have hrange_c : (π.comp (fderiv ℝ γ c)).range = ⊤ := LinearMap.range_eq_top.mpr hı'
  -- Choose a right inverse `ℓ` of `π ∘ fderiv ℝ γ c`.
  obtain ⟨ℓ, hℓ⟩ :=
    ContinuousLinearMap.exists_rightInverse_of_surjective (π.comp (fderiv ℝ γ c)) hrange_c
  -- The family `y ↦ (π ∘ fderiv ℝ γ y) ∘ ℓ` of endomorphisms of `ℝ^r` is continuous at `c`.
  have hGcont : ContinuousAt (fun y : Fin D → ℝ => (π.comp (fderiv ℝ γ y)).comp ℓ) c :=
    (((ContinuousLinearMap.compL ℝ (Fin r → ℝ) (Fin D → ℝ) (Fin r → ℝ)).flip ℓ).comp
      ((ContinuousLinearMap.compL ℝ (Fin D → ℝ) (Fin D → ℝ) (Fin r → ℝ)) π)).continuous.continuousAt.comp
        hcont
  -- At `c` it is the identity, so its determinant is `1 ≠ 0`.
  have hGc : ((π.comp (fderiv ℝ γ c)).comp ℓ).det ≠ 0 := by
    rw [hℓ]
    simp [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
  -- Hence near `c` the projection of the derivative is surjective.
  have hsurj_ev : ∀ᶠ y in nhds c, Function.Surjective fun v : Fin D → ℝ => π ((fderiv ℝ γ y) v) := by
    filter_upwards [eventually_surjective_of_det_ne_zero
      (fun y : Fin D → ℝ => (π.comp (fderiv ℝ γ y)).comp ℓ) hGcont hGc] with y hy
    intro w
    obtain ⟨u, hu⟩ := hy w
    exact ⟨ℓ u, by simpa only [ContinuousLinearMap.comp_apply] using hu⟩
  -- Finally, on the neighbourhood where this holds and which lies in `Ω`, the kernels agree.
  filter_upwards [hsurj_ev, hΩ.mem_nhds hc] with y hySurj hyΩ
  intro v hv
  have hvπ : π ((fderiv ℝ γ y) v) = 0 := by
    rw [hπ]
    simpa only [coordProjCLM_apply] using hv
  have hcoe : (((π.comp (fderiv ℝ γ y)) : (Fin D → ℝ) →L[ℝ] (Fin r → ℝ)) :
      (Fin D → ℝ) →ₗ[ℝ] (Fin r → ℝ)) =
      (π : (Fin D → ℝ) →ₗ[ℝ] (Fin r → ℝ)).comp
        ((fderiv ℝ γ y) : (Fin D → ℝ) →ₗ[ℝ] (Fin D → ℝ)) := by
    ext w; rfl
  have hfin : Module.finrank ℝ ((π : (Fin D → ℝ) →ₗ[ℝ] (Fin r → ℝ)).comp
        ((fderiv ℝ γ y) : (Fin D → ℝ) →ₗ[ℝ] (Fin D → ℝ))).range
      = Module.finrank ℝ ((fderiv ℝ γ y) : (Fin D → ℝ) →ₗ[ℝ] (Fin D → ℝ)).range := by
    rw [← hcoe]
    rw [show ((π.comp (fderiv ℝ γ y)) : (Fin D → ℝ) →ₗ[ℝ] (Fin r → ℝ)).range = ⊤ from
      LinearMap.range_eq_top.mpr hySurj, Submodule.topEquiv.finrank_eq, Module.finrank_fin_fun]
    exact (hr y hyΩ).symm
  have hker := ker_comp_eq_ker_of_finrank_range_eq
      ((fderiv ℝ γ y) : (Fin D → ℝ) →ₗ[ℝ] (Fin D → ℝ))
      (π : (Fin D → ℝ) →ₗ[ℝ] (Fin r → ℝ)) hfin
  have hvker : v ∈ ((fderiv ℝ γ y) : (Fin D → ℝ) →ₗ[ℝ] (Fin D → ℝ)).ker := by
    rw [← hker]
    exact LinearMap.mem_ker.mpr hvπ
  exact LinearMap.mem_ker.mp hvker

end Work.WilE7.DimAPI
