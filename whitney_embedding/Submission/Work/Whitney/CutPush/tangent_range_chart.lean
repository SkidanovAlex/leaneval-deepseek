import Mathlib
import Submission.Work.Whitney.CutPush.frame_ode

/-!
# The tangent plane of an immersion, computed in a chart

`Work.Whitney.CutPush.range_mfderiv_eq_range_fderiv_chart`: for a `C^∞` map `F : M → ℝ^{2n}` from a
smoothly charted `n`-manifold and a chart `c` around a point `y`, the range of the manifold derivative
`mfderiv F y` (an `n`-plane in `ℝ^{2n}`, the tangent plane of the sheet `F '' M` at `F y`) equals the
range of the ordinary Fréchet derivative of the chart representation `u ↦ F (c.symm u)` at `c y`.

This is the bridge that lets *local*, chart-based computations of the tangent planes of a finger be
glued into a global smooth frame field: the chart representation is a plain map of Euclidean spaces,
while the tangent plane of the sheet is intrinsically `range (mfderiv F y)`.

The proof is the chain rule along the chart, in the two forms `mfderiv_apply_eq_mfderiv_chartAt`
(pointwise) and `surjective_mfderiv_chart` (the chart's manifold derivative is onto, since a chart is
a local diffeomorphism); both avoid the type ascriptions of `→L`-valued compositions.
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff Topology
open Set Filter

variable {n : ℕ}

/-! ## The chain rule along a chart -/

/-- **The chain rule along a chart, in application form.**  For a point `y` of the source of the chart
`c`, the manifold derivative of `F` at `y` is the manifold derivative of the chart representation
`u ↦ F (c.symm u)` at `c y`, composed with the manifold derivative of the chart. -/
theorem mfderiv_apply_eq_mfderiv_chartAt {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (F : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {y : M} (hy : y ∈ c.source)
    (hcsm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hsymm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c y))
    (w : EuclideanSpace ℝ (Fin n)) :
    mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y w
      = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
          (fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) (c y)
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c y w) := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c y := hcsm.mdifferentiableAt hne
  have hs : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm (c y) := hsymm.mdifferentiableAt hne
  have hFd : MDifferentiableAt (𝓡 n) (𝓡 (2 * n)) F (c.symm (c y)) := by
    rw [c.left_inv hy]; exact (hF y).mdifferentiableAt hne
  have hrep : MDifferentiableAt (𝓡 n) (𝓡 (2 * n))
      (fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) (c y) :=
    MDifferentiableAt.comp (c y) hFd hs
  have heq : F =ᶠ[𝓝 y] (fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) ∘ c := by
    filter_upwards [c.open_source.mem_nhds hy] with z hz
    rw [Function.comp_apply, c.left_inv hz]
  have hcongr : mfderiv (𝓡 n) (𝓡 (2 * n)) F y
      = mfderiv (𝓡 n) (𝓡 (2 * n)) ((fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) ∘ c) y :=
    heq.mfderiv_eq
  have h1 : mfderiv (𝓡 n) (𝓡 (2 * n)) F y w
      = mfderiv (𝓡 n) (𝓡 (2 * n)) ((fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) ∘ c) y w :=
    congrArg (fun (f : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))) => f w) hcongr
  have h2 : mfderiv (𝓡 n) (𝓡 (2 * n))
        ((fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) ∘ c) y w
      = mfderiv (𝓡 n) (𝓡 (2 * n)) (fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) (c y)
          (mfderiv (𝓡 n) (𝓡 n) c y w) :=
    mfderiv_comp_apply_of_eq (x := y) (y := c y) (f := c)
      (g := fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) hrep hc rfl w
  rw [h1, h2]

/-! ## The chart's manifold derivative is onto -/

/-- **Surjectivity of the manifold derivative of a chart.** -/
theorem surjective_mfderiv_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {y : M} (hy : y ∈ c.source)
    (hcsm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hsymm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c y)) :
    Function.Surjective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c y) := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c y := hcsm.mdifferentiableAt hne
  have hs : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm (c y) := hsymm.mdifferentiableAt hne
  -- `c ∘ c.symm = id` near `c y`
  have hcy : c y ∈ c.target := c.map_source hy
  have hc_right : MDifferentiableAt (𝓡 n) (𝓡 n) c (c.symm (c y)) := by
    rw [c.left_inv hy]; exact hc
  have heq : c ∘ c.symm =ᶠ[𝓝 (c y)] id := by
    filter_upwards [c.open_target.mem_nhds hcy] with z hz
    rw [Function.comp_apply, c.right_inv hz]
    rfl
  have hcomp : mfderiv (𝓡 n) (𝓡 n) (c ∘ c.symm) (c y)
      = (mfderiv (𝓡 n) (𝓡 n) c (c.symm (c y))).comp
          (mfderiv (𝓡 n) (𝓡 n) c.symm (c y)) :=
    mfderiv_comp (f := c.symm) (g := c) (x := c y) hc_right hs
  rw [c.left_inv hy] at hcomp
  have hid : mfderiv (𝓡 n) (𝓡 n) (c ∘ c.symm) (c y)
      = mfderiv (𝓡 n) (𝓡 n) (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (c y) :=
    heq.mfderiv_eq
  rw [hid, mfderiv_id] at hcomp
  intro u
  refine ⟨mfderiv (𝓡 n) (𝓡 n) c.symm (c y) u, ?_⟩
  have h := congrArg (fun f => f u) hcomp
  exact h.symm

/-! ## The range of the tangent plane -/

/-- **The range of the manifold derivative is the range of the chart representation's derivative.** -/
theorem range_mfderiv_eq_range_fderiv_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (F : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {y : M} (hy : y ∈ c.source)
    (hcsm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hsymm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c y)) :
    LinearMap.range ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y
        : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).toLinearMap)
      = LinearMap.range ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) (c y)
          : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).toLinearMap) := by
  have hpt : ∀ w : EuclideanSpace ℝ (Fin n),
      mfderiv (𝓡 n) (𝓡 (2 * n)) F y w
        = mfderiv (𝓡 n) (𝓡 (2 * n)) (fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) (c y)
            (mfderiv (𝓡 n) (𝓡 n) c y w) :=
    fun w => mfderiv_apply_eq_mfderiv_chartAt F hF c hy hcsm hsymm w
  have hsurj := surjective_mfderiv_chart c hy hcsm hsymm
  rw [← mfderiv_eq_fderiv]
  refine le_antisymm ?_ ?_
  · rintro v ⟨w, rfl⟩
    exact ⟨mfderiv (𝓡 n) (𝓡 n) c y w, (hpt w).symm⟩
  · rintro v ⟨u, rfl⟩
    obtain ⟨w, hw⟩ := hsurj u
    refine ⟨w, ?_⟩
    change mfderiv (𝓡 n) (𝓡 (2 * n)) F y w
      = mfderiv (𝓡 n) (𝓡 (2 * n)) (fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) (c y) u
    rw [hpt w, hw]


/-! ## The Fréchet derivative of a smooth map along a smooth curve -/

/-- **The family `t ↦ fderiv ℝ F (u t)` is smooth** for a `C^∞` map `F` and a `C^∞` curve `u`.
This is the CLM-valued smoothness that the frame-field construction consumes (it feeds the
hypothesis of `exists_smooth_projection_range_family`, and the smoothness of the chart-local frame
families of M1 in `NOTES_S58_alignment.md`). -/
theorem contDiff_fderiv_comp {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E → G} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    {u : ℝ → E} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => fderiv ℝ F (u t)) := by
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ F) :=
    contDiffOn_univ.mp ((contDiffOn_infty_iff_fderiv_of_isOpen (𝕜 := ℝ) (f := F)
      (s := Set.univ) isOpen_univ).mp hF.contDiffOn).2
  exact hfd.comp hu


/-! ## The chart form of the bridge, for an actual chart of `M` -/

/-- **The tangent plane of the sheet, computed in a chart of the manifold.**  The hypotheses
`smoothness` of the previous bridge are discharged for `chartAt (EuclideanSpace ℝ (Fin n)) x`, which
is the form in which M1 (`NOTES_S58_alignment.md` §2) consumes it. -/
theorem range_mfderiv_eq_range_fderiv_chartAt {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (F : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (x : M) {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    LinearMap.range ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y
        : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).toLinearMap)
      = LinearMap.range ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) =>
            F ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm u))
          ((chartAt (EuclideanSpace ℝ (Fin n)) x) y)
          : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).toLinearMap) := by
  refine range_mfderiv_eq_range_fderiv_chart F hF (chartAt (EuclideanSpace ℝ (Fin n)) x) hy ?_ ?_
  · exact (contMDiffOn_extChartAt (I := 𝓡 n) (x := x) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)
  · have htgt : (extChartAt (𝓡 n) x).target
        = (chartAt (EuclideanSpace ℝ (Fin n)) x).target := by
      rw [extChartAt_target]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
        Set.range_id, Set.inter_univ]
    have hnhds : (extChartAt (𝓡 n) x).target ∈ 𝓝
        ((chartAt (EuclideanSpace ℝ (Fin n)) x) y) := by
      rw [htgt]
      exact (chartAt (EuclideanSpace ℝ (Fin n)) x).open_target.mem_nhds
        ((chartAt (EuclideanSpace ℝ (Fin n)) x).map_source hy)
    exact (contMDiffOn_extChartAt_symm (I := 𝓡 n) (x := x)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffAt hnhds

end Work.Whitney.CutPush
