import Mathlib
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm

/-!
# Two-sided straightening of the germ of an immersed curve

`Work.Noncompact.CompressionTube.exists_straightened_chart_twoSided` is the two-sided form of
`Work.Noncompact.CompressionTube.exists_straightened_chart` (from
`Submission/Work/Noncompact/CompressionTube/immersedArcWithGerm.lean`): for a `C^∞` curve
`α : ℝ → M` in an `n`-manifold whose manifold derivative at `1` is injective, there is a chart
`c'` at `α 1` in the maximal atlas, a direction `w ≠ 0` and `e > 0` with

`c' (α t) = c' (α 1) + (t - 1) • w`   for all `t` with `|t - 1| ≤ e`.

The construction is the same straightening of the chart expression `h = chartAt (α 1) ∘ α`: the
map `F y = h (1 + ξ (y - x₀)) + η (y - x₀)` sends the line `t ↦ x₀ + (t - 1) • v` onto the curve,
and its local inverse (restricted to a ball) is the straightening chart.  The underlying
`exists_straightening` already produces the two-sided equality; only the passage back to the
manifold has to be kept two-sided as well, since that is what the compression-tube construction
needs.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff Topology
open Set Metric Filter

theorem exists_straightened_chart_twoSided {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    {α : ℝ → M} (hα : ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) Work.Noncompact.CompressionTube.smoothOrder α)
    (himm : Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) α 1)) :
    ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e ∧ w ≠ 0 ∧
      c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder M ∧ α 1 ∈ c'.source ∧
      ∀ t : ℝ, |t - 1| ≤ e →
        α t ∈ c'.source ∧ c' (α t) = c' (α 1) + (t - 1) • w := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  set q : M := α 1 with hqdef
  set cq : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) q with hcqdef
  have hcqsrc : q ∈ cq.source := mem_chart_source _ q
  have hcqmax : cq ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas q
  have hcqc : ContMDiffOn (MC n) (MC n) smoothOrder (↑cq) cq.source :=
    contMDiffOn_of_mem_maximalAtlas hcqmax
  have hcqs : ContMDiffOn (MC n) (MC n) smoothOrder (↑cq.symm) cq.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hcqmax
  set h : ℝ → EuclideanSpace ℝ (Fin n) := fun t => cq (α t) with hhdef
  have hh1 : h 1 = cq q := rfl
  have hVopen : IsOpen {t : ℝ | α t ∈ cq.source} :=
    IsOpen.preimage hα.continuous cq.open_source
  have h1V : (1:ℝ) ∈ {t : ℝ | α t ∈ cq.source} := hcqsrc
  have hhcdon : ContDiffOn ℝ smoothOrder h {t : ℝ | α t ∈ cq.source} := by
    have h1 : ContMDiffOn MCreal (MC n) smoothOrder (fun t : ℝ => cq (α t))
        {t : ℝ | α t ∈ cq.source} :=
      hcqc.comp (hα.contMDiffOn.mono (subset_univ _)) (fun t ht => ht)
    exact contMDiffOn_iff_contDiffOn.mp (by simpa only [hhdef] using h1)
  set v : EuclideanSpace ℝ (Fin n) := (fderiv ℝ h 1) 1 with hvdef
  have hcur_inj : Function.Injective (mfderiv MCreal (MC n) (fun t : ℝ => cq (α t)) 1) := by
    have hcq_md : MDifferentiableAt (MC n) (MC n) (↑cq : M → EuclideanSpace ℝ (Fin n)) q :=
      (hcqc.contMDiffAt (cq.open_source.mem_nhds hcqsrc)).mdifferentiableAt hn0
    have hα_md : MDifferentiableAt MCreal (MC n) α 1 := hα.contMDiffAt.mdifferentiableAt hn0
    have hcomp := mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MC n)
      (f := α) (g := (↑cq : M → EuclideanSpace ℝ (Fin n))) 1 hcq_md hα_md
    rw [show (fun t : ℝ => cq (α t)) = (↑cq : M → EuclideanSpace ℝ (Fin n)) ∘ α from rfl, hcomp]
    intro a b hab
    simp only [ContinuousLinearMap.comp_apply] at hab
    exact himm (isLocalDiffeomorphAt_chart_mfderiv_injective hcqmax hcqsrc hab)
  have hvne : v ≠ 0 := by
    have hf_inj : Function.Injective (fderiv ℝ h 1) := by
      have hh := hcur_inj
      rw [mfderiv_eq_fderiv, ← hhdef] at hh
      exact hh
    rw [hvdef]
    intro h0
    have h1 : (1:ℝ) = 0 := hf_inj (by rw [h0, map_zero])
    exact absurd h1 (one_ne_zero : (1:ℝ) ≠ 0)
  obtain ⟨Φ, ρ, hρpos, hΦsm, hΦsm', hΦx₀, hΦsx₀, hΦgerm⟩ :=
    exists_straightening hVopen h1V hhcdon hh1 hvdef.symm hvne
  set c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) := cq ≫ₕ Φ.symm with hc'def
  have hc'src : c'.source = cq.source ∩ ↑cq ⁻¹' Φ.target := by
    rw [hc'def, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  have hc'tgt : c'.target = Φ.source ∩ ↑Φ ⁻¹' cq.target := by
    rw [hc'def, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.symm_target]
  have hc'max : c' ∈ IsManifold.maximalAtlas (MC n) smoothOrder M := by
    rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    constructor
    · rw [hc'src]
      have h1 : ContMDiffOn (MC n) (MC n) smoothOrder (↑Φ.symm) Φ.target :=
        fun z hz => contMDiffWithinAt_iff_contDiffWithinAt.mpr (hΦsm' z hz).contDiffWithinAt
      have h2 := h1.comp (hcqc.mono inter_subset_left) (fun x hx => hx.2)
      simpa only [hc'def, OpenPartialHomeomorph.coe_trans] using h2
    · rw [hc'tgt]
      have h1 : ContMDiffOn (MC n) (MC n) smoothOrder (↑Φ) Φ.source :=
        fun z hz => contMDiffWithinAt_iff_contDiffWithinAt.mpr (hΦsm z hz).contDiffWithinAt
      have h2 := hcqs.comp (h1.mono inter_subset_left) (fun x hx => hx.2)
      simpa only [hc'def, OpenPartialHomeomorph.coe_trans_symm,
        OpenPartialHomeomorph.symm_symm] using h2
  obtain ⟨ε₂, hε₂pos, hε₂sub⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds h1V)
  refine ⟨c', v, min ρ (ε₂ / 2), lt_min hρpos (by positivity), hvne, hc'max, ?_, ?_⟩
  · rw [hc'src]
    refine ⟨hcqsrc, ?_⟩
    rw [Set.mem_preimage]
    exact (hΦgerm 1 (by rw [sub_self, abs_zero]; exact hρpos.le)).1
  · intro t ht
    have htm : |t - 1| ≤ min ρ (ε₂ / 2) := ht
    have htρ : |t - 1| ≤ ρ := le_trans htm (min_le_left _ _)
    have htd : dist t 1 < ε₂ := by
      rw [Real.dist_eq]
      have h := le_trans htm (min_le_right ρ (ε₂ / 2))
      linarith
    have hsrc : α t ∈ cq.source := hε₂sub (Metric.mem_ball.mpr htd)
    obtain ⟨hΦt, hΦs⟩ := hΦgerm t htρ
    refine ⟨?_, ?_⟩
    · rw [hc'src]
      exact ⟨hsrc, hΦt⟩
    · have h1 : c' (α t) = cq q + (t - 1) • v := by
        show Φ.symm (cq (α t)) = cq q + (t - 1) • v
        exact hΦs
      have h2 : c' (α 1) = cq q := by
        show Φ.symm (cq (α 1)) = cq q
        exact hΦsx₀
      rw [h1, h2]

end Work.Noncompact.CompressionTube
