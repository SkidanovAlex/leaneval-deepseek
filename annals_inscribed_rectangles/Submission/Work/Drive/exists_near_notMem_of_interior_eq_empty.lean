import Mathlib
import Submission.Work.Drive.sideGermDefs

/-!
# The single-point avoidance is dense in the perturbation parameter

`Work.Drive.ChartPert Q 4 Ξ` is a smooth `4`-parameter family of self-maps of the capping space whose
parameter-derivative `mfderiv (𝓡 4) (𝓡 4) (fun t => Ξ t p) t` is **onto** at every parameter `t` and
every point `p` (third clause of the definition).  Consequently, for every base parameter `s₀` and
every point `p₀`, the curve

> `f : ℝ⁴ → CappingSpace`,  `f σ = Ξ (s₀ + σ) p₀`

is a smooth map between `4`-dimensional manifolds whose manifold derivative at `0` is onto, i.e. an
*immersion of maximal rank* — a local diffeomorphism at `0` by the inverse function theorem.

The file proves the geometric consequence used all over the germ/Sard route: a nowhere-dense set is
avoided on a dense set of parameters.  If `K` has empty interior then, for every `ε > 0`, some `σ`
with `‖σ‖ < ε` has `Ξ (s₀ + σ) p₀ ∉ K`.

The proof is the inverse function theorem in the chart `chartAt ℝ⁴ (Ξ s₀ p₀)`:

* `f` is `C^∞` and `mfderiv f 0` is onto (chain rule: the derivative of `σ ↦ s₀ + σ` is the identity
  and the parameter-derivative of `Ξ` is onto);
* the chart-composite `G = chartAt _ (Ξ s₀ p₀) ∘ f : ℝ⁴ → ℝ⁴` is therefore `C^∞` at `0` with
  `fderiv G 0` onto;
* hence `map G (𝓝 0) = 𝓝 (G 0)`, so the image of a small ball around `0` contains an open
  neighbourhood of `G 0`; pulling it back by the (open) inverse of the chart produces an open
  neighbourhood of `Ξ s₀ p₀` contained in `K` as soon as `f` maps that ball into `K` — contradicting
  `interior K = ∅`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Filter Set

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted

/-- **The single-point avoidance is dense in the perturbation parameter.**  If `K ⊆ CappingSpace` has
empty interior then, for any chart perturbation `Ξ` (whose parameter-derivative is surjective at every
point — `ChartPert`'s third clause), point `p₀` and base parameter `s₀`, there are parameters `σ` of
arbitrarily small norm with `Ξ (s₀ + σ) p₀ ∉ K`. -/
theorem exists_near_notMem_of_interior_eq_empty
    {Q : ℂ → Work.Drive.CappingSpace}
    {Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace}
    (hΞ : Work.Drive.ChartPert Q 4 Ξ) (p₀ : Work.Drive.CappingSpace)
    (K : Set Work.Drive.CappingSpace) (hK : interior K = ∅)
    (s₀ : EuclideanSpace ℝ (Fin 4)) (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : EuclideanSpace ℝ (Fin 4), ‖σ‖ < ε ∧ Ξ (s₀ + σ) p₀ ∉ K := by
  classical
  -- ## Step 1: the family `σ ↦ Ξ (s₀ + σ) p₀` is smooth, and its parameter-derivative at `0` is onto
  have hf_cmd : ContMDiffAt (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun σ : EuclideanSpace ℝ (Fin 4) => Ξ (s₀ + σ) p₀) 0 := by
    have hT1 : ContMDiffAt (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun σ : EuclideanSpace ℝ (Fin 4) => s₀ + σ) 0 :=
      ((contDiffAt_const (c := s₀)).add contDiffAt_id).contMDiffAt
    have hT : ContMDiffAt (𝓡 4) ((𝓡 4).prod (𝓡 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun σ : EuclideanSpace ℝ (Fin 4) => (s₀ + σ, p₀)) 0 :=
      hT1.prodMk contMDiffAt_const
    exact hΞ.2.1.contMDiffAt.comp 0 hT
  have hf_md : MDifferentiableAt (𝓡 4) (𝓡 4)
      (fun σ : EuclideanSpace ℝ (Fin 4) => Ξ (s₀ + σ) p₀) 0 :=
    hf_cmd.mdifferentiableAt (by simp)
  have hsurj_f : Function.Surjective (mfderiv (𝓡 4) (𝓡 4)
      (fun σ : EuclideanSpace ℝ (Fin 4) => Ξ (s₀ + σ) p₀) 0) := by
    have hmd₂ : MDifferentiableAt (𝓡 4) (𝓡 4)
        (fun σ : EuclideanSpace ℝ (Fin 4) => s₀ + σ) 0 :=
      (differentiableAt_id.const_add s₀).mdifferentiableAt
    have hmd₁ : MDifferentiableAt (𝓡 4) (𝓡 4)
        (fun t : EuclideanSpace ℝ (Fin 4) => Ξ t p₀) (s₀ + 0) := by
      have hpair : ContMDiffAt (𝓡 4) ((𝓡 4).prod (𝓡 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun σ : EuclideanSpace ℝ (Fin 4) => (σ, p₀)) (s₀ + 0) :=
        contMDiffAt_id.prodMk contMDiffAt_const
      exact ((hΞ.2.1.contMDiffAt (x := (s₀ + 0, p₀))).comp (s₀ + 0) hpair).mdifferentiableAt
        (by simp)
    rw [show (fun σ : EuclideanSpace ℝ (Fin 4) => Ξ (s₀ + σ) p₀)
        = (fun t : EuclideanSpace ℝ (Fin 4) => Ξ t p₀) ∘
          (fun σ : EuclideanSpace ℝ (Fin 4) => s₀ + σ) from rfl]
    rw [mfderiv_comp (x := (0 : EuclideanSpace ℝ (Fin 4))) hmd₁ hmd₂]
    have h2 : Function.Surjective
        (mfderiv (𝓡 4) (𝓡 4) (fun σ : EuclideanSpace ℝ (Fin 4) => s₀ + σ) 0) := by
      rw [mfderiv_eq_fderiv]
      have hd : fderiv ℝ (fun σ : EuclideanSpace ℝ (Fin 4) => s₀ + σ) 0
          = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4)) := by
        have h := ((hasFDerivAt_id (𝕜 := ℝ) (x := (0 : EuclideanSpace ℝ (Fin 4)))).const_add
          s₀).fderiv
        simpa using h
      rw [hd]
      intro v
      exact ⟨v, rfl⟩
    intro w
    obtain ⟨u, hu⟩ := hΞ.2.2 (s₀ + 0) p₀ w
    obtain ⟨v, hv⟩ := h2 u
    exact ⟨v, by rw [ContinuousLinearMap.comp_apply, hv]; exact hu⟩
  -- ## Step 2: the composite with the chart at `Ξ s₀ p₀` is smooth, with onto derivative at `0`
  have hG_cd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun σ : EuclideanSpace ℝ (Fin 4) =>
        extChartAt (𝓡 4) (Ξ (s₀ + 0) p₀) (Ξ (s₀ + σ) p₀)) 0 := by
    have h := ((contMDiffAt_iff_target.mp hf_cmd).2).contDiffAt
    simpa [Function.comp_def, add_zero] using h
  have hmd_e : MDifferentiableAt (𝓡 4) (𝓡 4) (extChartAt (𝓡 4) (Ξ (s₀ + 0) p₀))
      ((fun σ : EuclideanSpace ℝ (Fin 4) => Ξ (s₀ + σ) p₀) 0) :=
    mdifferentiableAt_extChartAt (I := (𝓡 4)) (H := EuclideanSpace ℝ (Fin 4))
      (mem_chart_source _ _)
  have hchain := mfderiv_comp (x := (0 : EuclideanSpace ℝ (Fin 4)))
    (f := fun σ : EuclideanSpace ℝ (Fin 4) => Ξ (s₀ + σ) p₀)
    (g := extChartAt (𝓡 4) (Ξ (s₀ + 0) p₀)) hmd_e hf_md
  have hsurj_e : Function.Surjective
      (mfderiv (𝓡 4) (𝓡 4) (extChartAt (𝓡 4) (Ξ (s₀ + 0) p₀))
        ((fun σ : EuclideanSpace ℝ (Fin 4) => Ξ (s₀ + σ) p₀) 0)) := by
    change Function.Surjective (mfderiv (𝓡 4) (𝓡 4) (extChartAt (𝓡 4) (Ξ (s₀ + 0) p₀))
      (Ξ (s₀ + 0) p₀))
    obtain ⟨A, hA⟩ := isInvertible_mfderiv_extChartAt (I := 𝓡 4)
      (x := Ξ (s₀ + 0) p₀) (mem_extChartAt_source _)
    rw [← hA]
    exact A.surjective
  have hsurj_G : Function.Surjective (fderiv ℝ
      (fun σ : EuclideanSpace ℝ (Fin 4) =>
        extChartAt (𝓡 4) (Ξ (s₀ + 0) p₀) (Ξ (s₀ + σ) p₀)) 0) := by
    have key : Function.Surjective (mfderiv (𝓡 4) (𝓡 4)
        (fun σ : EuclideanSpace ℝ (Fin 4) =>
          extChartAt (𝓡 4) (Ξ (s₀ + 0) p₀) (Ξ (s₀ + σ) p₀)) 0) := by
      change Function.Surjective (mfderiv (𝓡 4) (𝓡 4)
        ((extChartAt (𝓡 4) (Ξ (s₀ + 0) p₀)) ∘
          fun σ : EuclideanSpace ℝ (Fin 4) => Ξ (s₀ + σ) p₀) 0)
      rw [hchain]
      intro w
      obtain ⟨u, hu⟩ := hsurj_e w
      obtain ⟨v, hv⟩ := hsurj_f u
      exact ⟨v, by rw [ContinuousLinearMap.comp_apply, hv, hu]⟩
    rw [← mfderiv_eq_fderiv]
    exact key
  -- ## Step 3: replace `extChartAt` by `chartAt` (the same map, as `𝓡 4` is the identity on `ℝ⁴`)
  have hcoe : ⇑(extChartAt (𝓡 4) (Ξ (s₀ + 0) p₀)) =
      ⇑(chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) := by
    rw [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
  have hHeq : (fun σ : EuclideanSpace ℝ (Fin 4) =>
        (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + σ) p₀))
      = (fun σ : EuclideanSpace ℝ (Fin 4) =>
        extChartAt (𝓡 4) (Ξ (s₀ + 0) p₀) (Ξ (s₀ + σ) p₀)) := by
    funext σ
    simp only [hcoe]
  have hH_cd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun σ : EuclideanSpace ℝ (Fin 4) =>
        (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + σ) p₀)) 0 := by
    rw [hHeq]; exact hG_cd
  have hH_surj : Function.Surjective (fderiv ℝ
      (fun σ : EuclideanSpace ℝ (Fin 4) =>
        (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + σ) p₀)) 0) := by
    rw [hHeq]; exact hsurj_G
  -- ## Step 4: the inverse function theorem: the image of the ball is a neighbourhood of `G 0`
  have hstrict : HasStrictFDerivAt
      (fun σ : EuclideanSpace ℝ (Fin 4) =>
        (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + σ) p₀))
      (fderiv ℝ (fun σ : EuclideanSpace ℝ (Fin 4) =>
        (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + σ) p₀)) 0) 0 :=
    hH_cd.hasStrictFDerivAt (by simp)
  have hmap : Filter.map (fun σ : EuclideanSpace ℝ (Fin 4) =>
        (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + σ) p₀)) (𝓝 0)
      = 𝓝 ((chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + 0) p₀)) :=
    hstrict.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hH_surj)
  -- shrink the ball so that the family stays inside the source of the chart
  have hpre : (fun σ : EuclideanSpace ℝ (Fin 4) => Ξ (s₀ + σ) p₀) ⁻¹'
      (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).source ∈
      𝓝 (0 : EuclideanSpace ℝ (Fin 4)) :=
    hf_cmd.continuousAt.preimage_mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).open_source.mem_nhds
        (mem_chart_source _ _))
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hδ'pos : 0 < min δ (ε / 2) := lt_min hδpos (by linarith)
  have hδ'lt : min δ (ε / 2) < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (min δ (ε / 2)) ∈
      𝓝 (0 : EuclideanSpace ℝ (Fin 4)) := Metric.ball_mem_nhds _ hδ'pos
  have himg : (fun σ : EuclideanSpace ℝ (Fin 4) =>
        (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + σ) p₀)) ''
        Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (min δ (ε / 2)) ∈
      𝓝 ((chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + 0) p₀)) := by
    have h1 : (fun σ : EuclideanSpace ℝ (Fin 4) =>
          (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + σ) p₀)) ''
          Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (min δ (ε / 2)) ∈
        Filter.map (fun σ : EuclideanSpace ℝ (Fin 4) =>
          (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + σ) p₀)) (𝓝 0) :=
      Filter.image_mem_map hball
    rwa [hmap] at h1
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp himg
  -- ## Step 5: contradiction — `f` mapping the ball into `K` would put `Ξ s₀ p₀` in `interior K`
  by_contra hcon
  push Not at hcon
  have hfin : (fun σ : EuclideanSpace ℝ (Fin 4) => Ξ (s₀ + σ) p₀) ''
      Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (min δ (ε / 2)) ⊆ K := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact hcon σ (lt_trans (by rwa [Metric.mem_ball, dist_zero_right] at hσ) hδ'lt)
  have hmem : (Ξ (s₀ + 0) p₀) ∈ interior K := by
    have hWsub : (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).symm ''
        (Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + 0) p₀)) r ∩
          (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).target) ⊆ K := by
      rintro y ⟨z, hz, rfl⟩
      obtain ⟨hzB, _⟩ := hz
      obtain ⟨σ, hσ, rfl⟩ := hrsub hzB
      simp only []
      have hsrc : Ξ (s₀ + σ) p₀ ∈
          (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).source :=
        hδsub (Metric.ball_subset_ball (min_le_left _ _) hσ)
      have hleft : (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).symm
          ((chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + σ) p₀)) =
          Ξ (s₀ + σ) p₀ :=
        PartialEquiv.left_inv _ hsrc
      rw [hleft]
      exact hfin ⟨σ, hσ, rfl⟩
    have hWopen : IsOpen ((chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).symm ''
        (Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + 0) p₀)) r ∩
          (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).target)) :=
      (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).symm.isOpen_image_of_subset_source
        (Metric.isOpen_ball.inter (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).open_target)
        (by rw [OpenPartialHomeomorph.symm_source]; exact inter_subset_right)
    have hWc : Ξ (s₀ + 0) p₀ ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).symm ''
        (Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + 0) p₀)) r ∩
          (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).target) :=
      ⟨(chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)) (Ξ (s₀ + 0) p₀),
        ⟨Metric.mem_ball_self hrpos,
          (chartAt (EuclideanSpace ℝ (Fin 4)) (Ξ (s₀ + 0) p₀)).map_source
            (mem_chart_source _ _)⟩,
        PartialEquiv.left_inv _ (mem_chart_source _ _)⟩
    exact interior_maximal hWsub hWopen hWc
  rw [hK] at hmem
  exact hmem

end Work.Drive
