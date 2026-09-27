import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.morseLemma2
import Submission.Work.Drive.N2.hadamard2
import Submission.Work.Drive.N2.exists_local_diffeomorph
import Submission.Work.Drive.N2.isCritical_iff_chartRep

namespace Work.Drive.N2

private lemma one_add_one_le_infty : (1 : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  rw [WithTop.coe_le_coe]
  exact le_top

open scoped Manifold ContDiff in
/-- **A nondegenerate critical point is isolated, in chart form.**  For a smooth function `f` on a
surface and a nondegenerate critical point `p`, there is `r > 0` such that the closed ball of radius
`r` around the chart image of `p` lies in the target of the extended chart at `p`, and the derivative
of the chart representative `f ∘ (extChartAt (𝓡 2) p).symm` vanishes at no point of that closed ball
other than the centre.  Bricks available: `Work.Drive.N2.morseLemma2`, `Work.Drive.N2.hadamard2`,
`Work.Drive.N2.exists_local_diffeomorph`, `Work.Drive.N2.isCritical_iff_chartRep`. -/
theorem exists_chart_ball_noOtherCritical {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (p : M)
    (hp : Work.Drive.Morse.NondegCrit f p) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (extChartAt (𝓡 2) p p) r ⊆ (extChartAt (𝓡 2) p).target ∧
      ∀ y ∈ Metric.closedBall (extChartAt (𝓡 2) p p) r,
        fderiv ℝ (f ∘ (extChartAt (𝓡 2) p).symm) y = 0 → y = extChartAt (𝓡 2) p p := by
  obtain ⟨hcrit, hinj0⟩ := hp
  let e := extChartAt (𝓡 2) p
  let g : Plane → ℝ := fun y => f (e.symm y)
  let L : Plane →L[ℝ] (Plane →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ g) (e p)
  have hinj : Function.Injective L := hinj0
  have heptgt : e p ∈ e.target := e.map_source (mem_extChartAt_source p)
  -- smoothness of the chart representative at `e p`
  have hsmOn : ContDiffOn ℝ ∞ g e.target := by
    have h1 : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) ∞ (f ∘ e.symm) e.target :=
      (hf.contMDiffOn (s := Set.univ)).comp (contMDiffOn_extChartAt_symm (I := 𝓡 2) p)
        (fun x _ => Set.mem_univ _)
    exact h1.contDiffOn
  have hgp : ContDiffAt ℝ ∞ g (e p) :=
    hsmOn.contDiffAt ((isOpen_extChartAt_target p).mem_nhds heptgt)
  -- `e p` is a critical point of the chart representative
  have hg0 : fderiv ℝ g (e p) = 0 := by
    have h := (isCritical_iff_chartRep f hf p p (mem_extChartAt_source p)).mp hcrit
    change fderiv ℝ (fun y => f ((extChartAt (𝓡 2) p).symm y)) ((extChartAt (𝓡 2) p) p) = 0
    exact h
  -- the Hessian at `e p` is injective, hence (in finite dimension) an isomorphism
  have hfr : Module.finrank ℝ Plane = Module.finrank ℝ (Plane →L[ℝ] ℝ) := by
    rw [← LinearEquiv.finrank_eq
        (LinearMap.toContinuousLinearMap : (Plane →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Plane →L[ℝ] ℝ)),
      Module.finrank_linearMap]
    simp [finrank_euclideanSpace]
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have htop : L.range = ⊤ :=
    LinearMap.range_eq_top.mpr
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj)
  obtain ⟨L', hL'⟩ : ∃ L' : Plane ≃L[ℝ] (Plane →L[ℝ] ℝ),
      (L' : Plane →L[ℝ] (Plane →L[ℝ] ℝ)) = L :=
    ⟨ContinuousLinearEquiv.ofBijective L hker htop,
      ContinuousLinearEquiv.coe_ofBijective L hker htop⟩
  -- `fderiv ℝ g` is a local homeomorphism at `e p`, with value `0` there
  have hF_cd : ContDiffAt ℝ 1 (fderiv ℝ g) (e p) :=
    hgp.fderiv_right (m := 1) one_add_one_le_infty
  have hstrict : HasStrictFDerivAt (fderiv ℝ g) (L' : Plane →L[ℝ] (Plane →L[ℝ] ℝ)) (e p) := by
    rw [hL']
    exact hF_cd.hasStrictFDerivAt (by simp)
  let φ : OpenPartialHomeomorph Plane (Plane →L[ℝ] ℝ) :=
    hstrict.toOpenPartialHomeomorph (fderiv ℝ g)
  have hφcoe : (φ : Plane → (Plane →L[ℝ] ℝ)) = fderiv ℝ g :=
    hstrict.toOpenPartialHomeomorph_coe
  have hepφ : e p ∈ φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  -- a ball inside the source of `φ` and inside the chart target
  have hUopen : IsOpen (φ.source ∩ e.target) :=
    φ.open_source.inter (isOpen_extChartAt_target p)
  have hepU : e p ∈ φ.source ∩ e.target := ⟨hepφ, heptgt⟩
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hepU)
  refine ⟨ε / 2, half_pos hεpos, ?_, ?_⟩
  · exact subset_trans (Metric.closedBall_subset_ball (half_lt_self hεpos))
      (fun y hy => (hεsub hy).2)
  · intro y hy hy0
    have hyball : y ∈ Metric.ball (e p) ε :=
      Metric.closedBall_subset_ball (half_lt_self hεpos) hy
    have hyU := hεsub hyball
    have hφy : φ y = 0 := by rw [hφcoe]; exact hy0
    have hφx : φ (e p) = 0 := by rw [hφcoe]; exact hg0
    exact φ.injOn hyU.1 hepφ (by rw [hφy, hφx])

end Work.Drive.N2
