import Mathlib
import Submission.Work.Whitney.CutPush.projection_family_of_charts
import Submission.Work.Whitney.CutPush.bump_on_compact
import Submission.Work.Whitney.CutPush.tangent_range_chart
import Submission.Work.Whitney.CutPush.compact_between

/-!
# The chart-local tangent-plane family of the sheet (M1, §2.1)

`exists_local_chart_family`: on a piece `K ⊆ U` of the parameter line whose image under the curve
`δ` lies in one chart of `M`, there is a **globally smooth** family `Ψ` of linear maps
`ℝ^n →L ℝ^{2n}` with

* `range (Ψ t) = range (mfderiv F (δ t))` for `t ∈ K` (the tangent plane of the sheet), and
* `Ψ t` injective for `t ∈ K`,

so that `exists_local_projection_family` (`CutPush/projection_family_of_charts.lean`) can be applied
to it.  The family is built as `Ψ t = fderiv ℝ G (u t)` with

* `u t := χ t • c (δ t)` (`χ` a bump equal to `1` on a neighbourhood of `K`, so `u = c ∘ δ` there and
  `u` is *globally* smooth),
* `G := ψ • (F ∘ c.symm)` (`ψ` a bump equal to `1` on a neighbourhood of `u '' K`, so `G` is globally
  smooth while `fderiv G (u t) = fderiv (F ∘ c.symm) (c (δ t))` for `t ∈ K`),

where `c = extChartAt (𝓡 n) x`.  The identification of the range with the intrinsic tangent plane is
`range_mfderiv_eq_range_fderiv_chart` (`CutPush/tangent_range_chart.lean`).
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff
open Topology

/-- **The chart-local tangent-plane family.** -/
theorem exists_local_chart_family {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (F : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFinj : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y))
    {δ : ℝ → M}
    (hδ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) δ)
    {x : M} {U K : Set ℝ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hch : ∀ u ∈ U, δ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ∃ (Ψ : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))) (O : Set ℝ),
      IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      (∀ t ∈ O, Function.Injective (Ψ t)) ∧
      (∀ t ∈ O, LinearMap.range (Ψ t : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)))
        = LinearMap.range ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t)
            : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).toLinearMap)) := by
  classical
  obtain ⟨χ, V, hχc, hVo, hKV, hVU, hV1, hχs⟩ :=
    exists_contDiffBump_one_on_open_of_compact hU hK hKU
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x with hc
  have hc_src : c.source = (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    rw [hc]
  -- the smoothness of the chart coordinate of `δ`
  have hcδ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => c (δ t)) U := by
    have h1 : ContMDiffOn (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => c (δ t)) U :=
      (contMDiffOn_extChartAt (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (H := EuclideanSpace ℝ (Fin n)) (x := x) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp
        hδ.contMDiffOn (fun t ht => hch t ht)
    exact h1.contDiffOn
  obtain ⟨L, hLcpt, hKL, hLV⟩ := exists_isCompact_between hVo hK hKV
  set u : ℝ → EuclideanSpace ℝ (Fin n) := fun t => χ t • c (δ t) with hu
  have huc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u :=
    contDiff_bump_mul_contDiffOn hU hcδ hχc hχs
  -- the chart representation of `F`
  have hFc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : EuclideanSpace ℝ (Fin n) => F (c.symm v)) c.target := by
    have htg : (extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x).target
        = c.target := by
      rw [hc, extChartAt_target]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
        Set.range_id, Set.inter_univ]
    have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : EuclideanSpace ℝ (Fin n) => c.symm v) c.target := by
      have h2 := contMDiffOn_extChartAt_symm
        (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (x := x)
        (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      rw [htg] at h2
      exact h2
    exact ((hF.contMDiffOn (s := Set.univ)).comp h1 (fun x _ => Set.mem_univ (c.symm x))).contDiffOn
  have huL : u '' L ⊆ c.target := by
    rintro v ⟨t, ht, rfl⟩
    have ht1 : χ t = 1 := hV1 t (hLV ht)
    have hmem : δ t ∈ c.source := by
      rw [hc_src]
      exact hch t (hVU (hLV ht))
    rw [hu]
    simp only
    rw [ht1, one_smul]
    exact c.map_source hmem
  -- the cut-off on the `E` side, on the image of the *compact* set `L`
  obtain ⟨ψ, W, hψc, hWo, huLW, hWt, hW1, hψs⟩ :=
    exists_contDiffBump_one_on_open_of_compact c.open_target (hLcpt.image huc.continuous) huL
  set G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun v => ψ v • F (c.symm v) with hG
  have hGc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G :=
    contDiff_bump_mul_contDiffOn c.open_target hFc hψc hψs
  set O : Set ℝ := V ∩ u ⁻¹' W with hOdef
  have hOo : IsOpen O := hVo.inter (hWo.preimage huc.continuous)
  have hKO : K ⊆ O := fun t ht => ⟨hKV ht, huLW ⟨t, hKL ht, rfl⟩⟩
  have hOU : O ⊆ U := fun t ht => hVU ht.1
  refine ⟨fun t => fderiv ℝ G (u t), O, hOo, hKO, hOU, contDiff_fderiv_comp hGc huc, ?_⟩
  -- the common ingredients on `K`
  have key : ∀ t ∈ O,
      (u t = c (δ t)) ∧
      (fderiv ℝ G (u t) = fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => F (c.symm v)) (c (δ t))) ∧
      (δ t ∈ c.source) := by
    intro t ht
    have hut : u t = c (δ t) := by
      have ht1 : χ t = 1 := hV1 t ht.1
      rw [hu]
      simp only
      rw [ht1, one_smul]
    have heq : G =ᶠ[𝓝 (u t)] (fun v : EuclideanSpace ℝ (Fin n) => F (c.symm v)) := by
      filter_upwards [hWo.mem_nhds ht.2] with v hv
      show ψ v • F (c.symm v) = F (c.symm v)
      rw [hW1 v hv, one_smul]
    have hfd : fderiv ℝ G (u t)
        = fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => F (c.symm v)) (u t) := heq.fderiv_eq
    have hmem : δ t ∈ c.source := hch t (hVU ht.1)
    exact ⟨hut, by rw [hfd, hut], hmem⟩
  -- the smoothness of the chart and of its inverse at the relevant points
  have hcsm : ∀ t ∈ O, ContMDiffAt ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) c (δ t) := by
    intro t ht
    exact (contMDiffOn_extChartAt (I := ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))))) (H := EuclideanSpace ℝ (Fin n)) (x := x)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds ((key t ht).2.2))
  have hsymm : ∀ t ∈ O, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c (δ t)) := by
    intro t ht
    have htg : (extChartAt ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) x).target = c.target := by
      rw [hc, extChartAt_target]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
        Set.range_id, Set.inter_univ]
    have hnhds : (extChartAt ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) x).target ∈ 𝓝 (c (δ t)) := by
      rw [htg]
      exact c.open_target.mem_nhds (c.map_source (key t ht).2.2)
    exact (contMDiffOn_extChartAt_symm (I := ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))))) (x := x)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffAt hnhds
  have hpt : ∀ t ∈ O, ∀ z : EuclideanSpace ℝ (Fin n),
      mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))) F (δ t) z
        = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))))
            (fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) (c (δ t))
            (mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) c (δ t) z) := by
    intro t ht z
    exact mfderiv_apply_eq_mfderiv_chartAt F hF c (key t ht).2.2 (hcsm t ht) (hsymm t ht) z
  have hsurj : ∀ t ∈ O, Function.Surjective (mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) c (δ t)) := by
    intro t ht
    exact surjective_mfderiv_chart c (key t ht).2.2 (hcsm t ht) (hsymm t ht)
  refine ⟨?_, ?_⟩
  · -- injectivity
    intro t ht
    show Function.Injective (fderiv ℝ G (u t))
    rw [(key t ht).2.1]
    intro v w hvw
    have hdiff : fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => F (c.symm v)) (c (δ t)) (v - w)
        = 0 := by
      rw [map_sub, hvw, sub_self]
    rw [← mfderiv_eq_fderiv] at hdiff
    obtain ⟨z, hz⟩ := hsurj t ht (v - w)
    have h1 : mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))) F (δ t) z = 0 := by
      rw [hpt t ht z, hz]
      exact hdiff
    have h2 : z = 0 := hFinj (δ t) (by rw [h1, map_zero])
    rw [h2, map_zero] at hz
    exact sub_eq_zero.mp hz.symm
  · -- the range
    intro t ht
    show LinearMap.range (fderiv ℝ G (u t) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (2 * n)))
      = LinearMap.range ((mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))) F (δ t)
          : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).toLinearMap)
    rw [(key t ht).2.1]
    exact (range_mfderiv_eq_range_fderiv_chart F hF c (key t ht).2.2
      (hcsm t ht) (hsymm t ht)).symm

end Work.Whitney.CutPush
