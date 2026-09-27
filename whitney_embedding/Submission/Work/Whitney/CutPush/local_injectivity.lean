import Mathlib
import Submission.Work.Whitney.CutPush.collar_injectivity
import Submission.Work.Whitney.CutPush.tangent_range_chart

/-!
# Local injectivity from the inverse function theorem

The compactness lemma `exists_isOpen_injOn_of_compact_injOn` (`CutPush/collar_injectivity.lean`) needs
*local* injectivity at every point of the compact set.  This file supplies it from the inverse function
theorem, first for maps between normed spaces and then (via charts) for maps out of a smooth manifold.

* `exists_nhds_injOn_of_hasStrictFDerivAt` — an invertible strict derivative at a point makes the map
  injective on a neighbourhood of it (immediate from `HasStrictFDerivAt.eventually_left_inverse`:
  every point near `a` is recovered from its image by the local inverse);
* `exists_nhds_injOn_of_mfderiv_injective` — the same for a `C^∞` map `F : M → ℝ^{2n}` with injective
  `mfderiv` at a point, by reading the map in a chart.
-/

namespace Work.Whitney.CutPush

open scoped Manifold Topology ContDiff

/-- **Local injectivity from an invertible strict derivative.** -/
theorem exists_nhds_injOn_of_hasStrictFDerivAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace E]
    {f : E → F} {f' : E ≃L[ℝ] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E →L[ℝ] F) a) :
    ∃ U ∈ 𝓝 a, Set.InjOn f U := by
  refine ⟨{x : E | hf.localInverse f f' a (f x) = x}, hf.eventually_left_inverse, ?_⟩
  intro x hx y hy hxy
  rw [← hx, hxy, hy]

/-- **Local injectivity from an injective strict derivative.**  If `f' = d f (a)` has a continuous
linear *left* inverse `L` (i.e. `L ∘ f' = id`), then `f` is injective on a neighbourhood of `a`: this is
the previous lemma applied to `L ∘ f`, whose derivative is the identity.  This is the form needed for
immersions, where `f'` is only injective (an embedding of the source into the target), not onto. -/
theorem exists_nhds_injOn_of_hasStrictFDerivAt_of_leftInverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace E]
    {f : E → F} {f' : E →L[ℝ] F} {a : E} (hf : HasStrictFDerivAt f f' a)
    (L : F →L[ℝ] E) (hL : L.comp f' = 1) :
    ∃ U ∈ 𝓝 a, Set.InjOn f U := by
  have hLstrict : HasStrictFDerivAt (fun y : F => L y) L (f a) :=
    ContinuousLinearMap.hasStrictFDerivAt L
  have hLf : HasStrictFDerivAt (fun x : E => L (f x)) (1 : E →L[ℝ] E) a := by
    have h := HasStrictFDerivAt.comp (f := f) (f' := f') (x := a)
      (g := fun y : F => L y) (g' := L) hLstrict hf
    rw [hL] at h
    simpa using h
  obtain ⟨U, hU, hUinj⟩ := exists_nhds_injOn_of_hasStrictFDerivAt
    (f := fun x : E => L (f x)) (f' := ContinuousLinearEquiv.refl ℝ E) hLf
  refine ⟨U, hU, fun x hx y hy hxy => hUinj hx hy ?_⟩
  simpa using congrArg L hxy

/-- **Local injectivity of a smooth map with injective `mfderiv`.**  For a `C^∞` map `F : M → ℝ^{2n}`
from an `n`-manifold with injective `mfderiv` at `y`, read in a chart: the chart representation has
injective (hence left-invertible) Fréchet derivative at `c y`, so it is injective on a neighbourhood of
`c y`, and this transports back to `M`. -/
theorem exists_nhds_injOn_of_mfderiv_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {F : M → EuclideanSpace ℝ (Fin (2 * n))}
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    {y : M} (hinj : Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y)) :
    ∃ U ∈ 𝓝 y, Set.InjOn F U := by
  classical
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) y with hc
  have hcy : y ∈ c.source := mem_chart_source _ _
  have hcsm : ContMDiffAt (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) c y :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hcy)
  have hsymm : ContMDiffAt (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c y) :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds (c.map_source hcy))
  set G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) := fun u => F (c.symm u) with hG
  have hGcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (c y) := by
    have h1 : c.symm (c y) = y := c.left_inv hcy
    have h2 : ContMDiffAt (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) F (c.symm (c y)) := by
      rw [h1]; exact hF.contMDiffAt
    have h3 : ContMDiffAt (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (F ∘ c.symm) (c y) :=
      ContMDiffAt.comp (c y) h2 hsymm
    simpa only [Function.comp_def] using h3.contDiffAt
  have hker : ∀ v, fderiv ℝ G (c y) v = 0 → v = 0 := by
    intro v hv
    obtain ⟨w, hw⟩ := surjective_mfderiv_chart c hcy hcsm hsymm v
    have hchain := mfderiv_apply_eq_mfderiv_chartAt F hF c hcy hcsm hsymm w
    rw [← hG] at hchain
    rw [mfderiv_eq_fderiv] at hchain
    have hzero : mfderiv (𝓡 n) (𝓡 (2 * n)) F y w = 0 := by
      rw [hchain, hw]
      exact hv
    have hw0 : w = 0 := hinj (hzero.trans (map_zero (mfderiv (𝓡 n) (𝓡 (2 * n)) F y)).symm)
    rw [← hw, hw0]
    exact map_zero _
  have hGinj : Function.Injective (fderiv ℝ G (c y)) := fun v w hvw =>
    sub_eq_zero.mp (hker (v - w) (by rw [map_sub, hvw, sub_self]))
  obtain ⟨L, hL⟩ : ∃ L : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n),
      L.comp (fderiv ℝ G (c y)) = 1 := by
    have hleft := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
      (𝕜 := ℝ) hGinj
    exact ⟨ContinuousLinearMap.HasLeftInverse.leftInverse hleft,
      ContinuousLinearMap.ext (fun x =>
        ContinuousLinearMap.HasLeftInverse.leftInverse_leftInverse hleft x)⟩
  obtain ⟨V, hV, hVinj⟩ := exists_nhds_injOn_of_hasStrictFDerivAt_of_leftInverse
    (f := G) (f' := fderiv ℝ G (c y)) (a := c y) (hGcd.hasStrictFDerivAt (by simp)) L hL
  refine ⟨c.source ∩ c ⁻¹' V, ?_, ?_⟩
  · refine Filter.inter_mem (c.open_source.mem_nhds hcy) ?_
    show c ⁻¹' V ∈ 𝓝 y
    exact Filter.Tendsto.eventually (c.continuousAt hcy) hV
  · intro x hx z hz hxz
    have hGx : G (c x) = F x := by
      simp only [hG]
      rw [c.left_inv hx.1]
    have hGz : G (c z) = F z := by
      simp only [hG]
      rw [c.left_inv hz.1]
    have : c x = c z := hVinj hx.2 hz.2 (by rw [hGx, hGz, hxz])
    rw [← c.left_inv hx.1, ← c.left_inv hz.1, this]

end Work.Whitney.CutPush
