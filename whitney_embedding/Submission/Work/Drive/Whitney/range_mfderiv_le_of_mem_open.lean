import Mathlib

/-!
# The tangent space of a linear subspace is the subspace

If a smooth map `g : M → ℝ^{2n}` on a smooth `n`-manifold takes its values in a linear subspace `K`
on an open set `U ∋ x`, then the range of its manifold derivative `mfderiv g x` is contained in `K`.

The mathematical content is the chain rule plus the fact that `K` is closed: the difference
quotients of `g` in a direction `v` lie in `K` and converge to `mfderiv g x v`; a derivative of a map
which is (eventually) constant into a closed affine subspace stays in that subspace.
-/

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Filter Topology Set

set_option linter.style.haveILetI false

/-- **Euclidean auxiliary lemma.**  If `f : E → F` has derivative `f'` at `x` and takes its values
in a closed submodule `K ≤ F` on a neighbourhood of `x`, then `f'` maps into `K`.

Indeed, for every `v` the vectors `c • (f (x + c⁻¹ • v) - f x)` converge to `f' v` as `c → ∞`
(`HasFDerivAt.lim_real`) while lying in `K` for large `c`; `K` being closed, the limit lies in `K`. -/
theorem range_le_of_eventually_mem_submodule {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E →L[ℝ] F}
    {x : E} (K : Submodule ℝ F) (hKc : IsClosed (K : Set F))
    (hf : HasFDerivAt f f' x) (hmem : ∀ᶠ y in 𝓝 x, f y ∈ K) : f'.range ≤ K := by
  intro y hy
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hy
  have hxK : f x ∈ K := hmem.self_of_nhds
  have htend := hf.lim_real v
  have hev : ∀ᶠ c : ℝ in atTop, c • (f (x + c⁻¹ • v) - f x) ∈ K := by
    have hc : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
    have hpt : Tendsto (fun c : ℝ => x + c⁻¹ • v) atTop (𝓝 (x + (0 : ℝ) • v)) :=
      tendsto_const_nhds.add (hc.smul_const v)
    have hmem' : ∀ᶠ c : ℝ in atTop, x + c⁻¹ • v ∈ {y | f y ∈ K} :=
      hpt.eventually (by simpa using hmem)
    filter_upwards [hmem'] with c hc'
    exact K.smul_mem c (K.sub_mem hc' hxK)
  exact hKc.mem_of_tendsto htend hev

/-- **The derivative of a map which takes its values in a linear subspace lands in it.**

If `g : M → ℝ^{2n}` is `C^∞` on the smooth `n`-manifold `M` and takes its values in the linear
subspace `K` on an open set `U ∋ x`, then `range (mfderiv g x) ⊆ K`.

This is the "tangent space of a linear subspace is the subspace" fact: needed to see that the
flattening `F ∘ f` of a tube contained in the plane `K` has its tangent plane at the seam *equal*
to `K` (equality then follows from `finrank K = n` and the immersion). -/
theorem range_mfderiv_le_of_mem_open {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (g : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hg : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))))
    (U : Set M) (hUo : IsOpen U) (x : M) (hxU : x ∈ U) (hU : ∀ y ∈ U, g y ∈ K) :
    LinearMap.range ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g x).toLinearMap) ≤ K := by
  classical
  -- `chartAt` of `x` and the chart representation of `g`
  haveI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) 1 M :=
    IsManifold.of_le (m := 1) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  let c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x
  have hxs : x ∈ c.source := mem_chart_source _ _
  have ha : c x ∈ c.target := c.map_source hxs
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) := fun y => g (c.symm y)
  -- `K` is closed, being a finite-dimensional subspace of a Euclidean space
  have hKc : IsClosed (K : Set (EuclideanSpace ℝ (Fin (2 * n)))) :=
    Submodule.closed_of_finiteDimensional K
  -- the chart representation is differentiable and its derivative is the one of `mfderiv g x`
  have hcs : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (c.symm : _ → M) (c x) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) ha
  have hgmd : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g x :=
    (hg x).mdifferentiableAt (by simp)
  have hFmd : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (c x) :=
    MDifferentiableAt.comp_of_eq (c x) hgmd hcs (c.left_inv hxs)
  have hFderiv : HasFDerivAt F (fderiv ℝ F (c x)) (c x) := hFmd.differentiableAt.hasFDerivAt
  -- the chart representation lands in `K` near `c x`
  have hmem : ∀ᶠ y in 𝓝 (c x), F y ∈ K := by
    have hcont : ContinuousAt (c.symm : EuclideanSpace ℝ (Fin n) → M) (c x) :=
      (c.symm).continuousAt (by rw [OpenPartialHomeomorph.symm_source]; exact ha)
    have htend : Tendsto (c.symm : EuclideanSpace ℝ (Fin n) → M) (𝓝 (c x)) (𝓝 x) := by
      have h := hcont.tendsto
      rwa [c.left_inv hxs] at h
    have hU' : ∀ᶠ y in 𝓝 (c x), c.symm y ∈ U := htend.eventually (hUo.mem_nhds hxU)
    filter_upwards [hU'] with y hy
    exact hU _ hy
  -- `mfderiv g x` is the chart derivative composed with the derivative of the chart representation
  have hcmd : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (c : M → _) x :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hxs
  have heq : g =ᶠ[𝓝 x] F ∘ c := by
    filter_upwards [c.open_source.mem_nhds hxs] with y hy
    show g y = g (c.symm (c y))
    rw [c.left_inv hy]
  have hcomp := mfderiv_comp x hFmd hcmd
  have hdecomp : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g x
      = (fderiv ℝ F (c x)).comp (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c x) := by
    have h1 : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g x
        = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (F ∘ c) x :=
      Filter.EventuallyEq.mfderiv_eq heq
    rw [h1, hcomp, mfderiv_eq_fderiv]
    rfl
  -- assemble
  change (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g x).range ≤ K
  refine le_trans ?_ (range_le_of_eventually_mem_submodule K hKc hFderiv hmem)
  rw [hdecomp]
  exact LinearMap.range_comp_le_range _ _

end Work.Drive.Whitney
