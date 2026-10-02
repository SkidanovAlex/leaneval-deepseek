import Submission.Work.Tubular.DiscManifold.OrthoFrame

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-!
# Smoothness of the normal frame and of the trivialization

The orthonormal frame `orthTubeFrame`, the trivialization `insF` and its inverse `readF` are `C¹` in
the base point, read in a chart of the base; consequently the change of trivialization
`frameChange C i j x = readF C j x ∘ insF C i x` is `C¹` as well.  These are exactly the
smoothness statements needed for the transition functions of the normal disc bundle.
-/

open scoped Manifold ContDiff Topology InnerProduct InnerProductSpace
open Function Filter

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} {ε : ℝ}

/-- The chart-cover set of the frame, read in a chart of the base. -/
def chartCover (E : EmbeddingData V (8 + k)) (i : CoverIdx V k) (x₀ : V.pt) : Set (Euc 8) :=
  (chartAt (Euc 8) x₀).target ∩ (chartAt (Euc 8) x₀).symm ⁻¹' coverBaseSet E.e i

theorem contDiffOn_tubeFrame_chart {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : CoverIdx V k) (x₀ : V.pt) (l : Fin k) :
    ContDiffOn ℝ 1 (fun y : Euc 8 => tubeFrame C i ((chartAt (Euc 8) x₀).symm y) l)
      (chartCover E i x₀) := by
  have h1 : ContMDiffOn (𝓡 8) 𝓘(ℝ, Euc (8 + k)) 1 (fun x : V.pt => tubeFrame C i x l)
      (coverBaseSet E.e i) := contMDiffOn_tubeFrame C i l
  have h2 : ContMDiffOn (𝓡 8) (𝓡 8) 1 (fun y : Euc 8 => (chartAt (Euc 8) x₀).symm y)
      (chartCover E i x₀) := (contMDiffOn_chart_symm (x := x₀)).mono Set.inter_subset_left
  have h3 := h1.comp h2 (fun y hy => hy.2)
  exact (contMDiffOn_iff_contDiffOn).mp h3

theorem contDiffOn_orthTubeFrame_chart {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : CoverIdx V k) (x₀ : V.pt) (l : Fin k) :
    ContDiffOn ℝ 1 (fun y : Euc 8 => orthTubeFrame C i ((chartAt (Euc 8) x₀).symm y) l)
      (chartCover E i x₀) :=
  DiscManifold.contDiffOn_gramSchmidtNormed
    (fun l => contDiffOn_tubeFrame_chart C i x₀ l)
    (fun y hy => tubeFrame_linearIndependent C i hy.2) l

theorem contDiffOn_insF_chart {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : CoverIdx V k) (x₀ : V.pt) :
    ContDiffOn ℝ 1 (fun p : Euc 8 × Euc k => insF C i ((chartAt (Euc 8) x₀).symm p.1) p.2)
      (chartCover E i x₀ ×ˢ Set.univ) := by
  rw [show (fun p : Euc 8 × Euc k => insF C i ((chartAt (Euc 8) x₀).symm p.1) p.2)
      = fun p => ∑ l : Fin k,
          euclCLM k p.2 l • orthTubeFrame C i ((chartAt (Euc 8) x₀).symm p.1) l by
    funext p; rw [insF_apply]]
  refine ContDiffOn.sum fun l _ => ?_
  have h1 : ContDiffOn ℝ 1 (fun p : Euc 8 × Euc k => euclCLM k p.2 l)
      (chartCover E i x₀ ×ˢ Set.univ) := by
    have h0 : ContDiffOn ℝ 1
        (fun p : Euc 8 × Euc k => (ContinuousLinearMap.proj l) ((euclCLM k) p.2))
        (chartCover E i x₀ ×ˢ Set.univ) :=
      (((ContinuousLinearMap.proj l).contDiff.comp (euclCLM k).contDiff).contDiffOn).comp
        contDiffOn_snd (fun p _ => Set.mem_univ _)
    exact h0.congr fun p _ => rfl
  have h2 : ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc k => orthTubeFrame C i ((chartAt (Euc 8) x₀).symm p.1) l)
      (chartCover E i x₀ ×ˢ Set.univ) :=
    (contDiffOn_orthTubeFrame_chart C i x₀ l).comp contDiffOn_fst (fun p hp => hp.1)
  exact h1.smul h2

theorem contDiffOn_readF_chart {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : CoverIdx V k) (x₀ : V.pt) :
    ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc (8 + k) => readF C i ((chartAt (Euc 8) x₀).symm p.1) p.2)
      (chartCover E i x₀ ×ˢ Set.univ) := by
  have hcoord : ∀ l : Fin k, ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc (8 + k) =>
        euclCLM k (readF C i ((chartAt (Euc 8) x₀).symm p.1) p.2) l)
      (chartCover E i x₀ ×ˢ Set.univ) := by
    intro l
    have hbase : ContDiffOn ℝ 1
        (fun p : Euc 8 × Euc (8 + k) =>
          ⟪orthTubeFrame C i ((chartAt (Euc 8) x₀).symm p.1) l, p.2⟫_ℝ)
        (chartCover E i x₀ ×ˢ Set.univ) :=
      ((contDiffOn_orthTubeFrame_chart C i x₀ l).comp contDiffOn_fst
        (fun p hp => hp.1)).inner ℝ contDiffOn_snd
    exact hbase.congr fun p hp => readF_coord C i hp.1.2 p.2 l
  have hpi : ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc (8 + k) =>
        euclCLM k (readF C i ((chartAt (Euc 8) x₀).symm p.1) p.2))
      (chartCover E i x₀ ×ˢ Set.univ) := contDiffOn_pi' hcoord
  have hcomp : ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc (8 + k) =>
        (EuclideanSpace.equiv (Fin k) ℝ).symm
          (euclCLM k (readF C i ((chartAt (Euc 8) x₀).symm p.1) p.2)))
      (chartCover E i x₀ ×ˢ Set.univ) :=
    ((EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff).contDiffOn.comp hpi
      (fun p _ => Set.mem_univ _)
  exact hcomp.congr fun p _ => (EuclideanSpace.equiv (Fin k) ℝ).symm_apply_apply _

/-- **The change of trivialization** `readF C j x ∘ insF C i x`.  It is the linear map comparing
the `i`-th and the `j`-th trivialization of the normal bundle at `x`. -/
def frameChange {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i j : CoverIdx V k)
    (x : V.pt) : Euc k →L[ℝ] Euc k :=
  (readF C j x).comp (insF C i x)

theorem contDiffOn_frameChange_chart {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i j : CoverIdx V k) (x₀ : V.pt) :
    ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc k => frameChange C i j ((chartAt (Euc 8) x₀).symm p.1) p.2)
      ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) := by
  have hcoord : ∀ l : Fin k, ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc k =>
        euclCLM k (frameChange C i j ((chartAt (Euc 8) x₀).symm p.1) p.2) l)
      ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) := by
    intro l
    have hfst : ContDiffOn ℝ 1 (fun p : Euc 8 × Euc k => p.1)
        (chartCover E j x₀ ×ˢ Set.univ) :=
      (contDiffOn_fst : ContDiffOn ℝ 1 (fun p : Euc 8 × Euc k => p.1) Set.univ).mono
        (Set.subset_univ _)
    have h1 : ContDiffOn ℝ 1
        (fun p : Euc 8 × Euc k => orthTubeFrame C j ((chartAt (Euc 8) x₀).symm p.1) l)
        ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) :=
      ((contDiffOn_orthTubeFrame_chart C j x₀ l).comp hfst
        (fun p hp => hp.1)).mono (Set.prod_mono Set.inter_subset_right Set.Subset.rfl)
    have h2 : ContDiffOn ℝ 1
        (fun p : Euc 8 × Euc k => insF C i ((chartAt (Euc 8) x₀).symm p.1) p.2)
        ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) :=
      (contDiffOn_insF_chart C i x₀).mono (Set.prod_mono Set.inter_subset_left Set.Subset.rfl)
    refine (h1.inner ℝ h2).congr fun p hp => ?_
    exact readF_coord C j hp.1.2.2 (insF C i ((chartAt (Euc 8) x₀).symm p.1) p.2) l
  have hpi : ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc k =>
        euclCLM k (frameChange C i j ((chartAt (Euc 8) x₀).symm p.1) p.2))
      ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) := contDiffOn_pi' hcoord
  have hcomp : ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc k =>
        (EuclideanSpace.equiv (Fin k) ℝ).symm
          (euclCLM k (frameChange C i j ((chartAt (Euc 8) x₀).symm p.1) p.2)))
      ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) :=
    ((EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff).contDiffOn.comp hpi
      (fun p _ => Set.mem_univ _)
  exact hcomp.congr fun p _ => (EuclideanSpace.equiv (Fin k) ℝ).symm_apply_apply _

/-- Joint continuity of the trivialization `(x, c) ↦ insF C i x c` over the chart cover. -/
theorem continuousOn_insF {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k) :
    ContinuousOn (fun p : V.pt × Euc k => insF C i p.1 p.2)
      (coverBaseSet E.e i ×ˢ Set.univ) := by
  refine continuousOn_of_locally_continuousOn fun p₀ hp₀ => ?_
  refine ⟨(chartAt (Euc 8) p₀.1).source ×ˢ Set.univ,
    (chartAt (Euc 8) p₀.1).open_source.prod isOpen_univ, ⟨mem_chart_source _ _, Set.mem_univ _⟩, ?_⟩
  have hc : ContinuousOn
      (fun p : Euc 8 × Euc k => insF C i ((chartAt (Euc 8) p₀.1).symm p.1) p.2)
      (chartCover E i p₀.1 ×ˢ Set.univ) := (contDiffOn_insF_chart C i p₀.1).continuousOn
  have hchart : ContinuousOn
      (fun p : V.pt × Euc k => ((chartAt (Euc 8) p₀.1) p.1, p.2))
      ((coverBaseSet E.e i ×ˢ Set.univ) ∩ ((chartAt (Euc 8) p₀.1).source ×ˢ Set.univ)) :=
    ((chartAt (Euc 8) p₀.1).continuousOn_toFun.comp continuousOn_fst
      (fun p hp => hp.2.1)).prodMk continuousOn_snd
  have hmaps : Set.MapsTo (fun p : V.pt × Euc k => ((chartAt (Euc 8) p₀.1) p.1, p.2))
      ((coverBaseSet E.e i ×ˢ Set.univ) ∩ ((chartAt (Euc 8) p₀.1).source ×ˢ Set.univ))
      (chartCover E i p₀.1 ×ˢ Set.univ) := by
    intro p hp
    refine ⟨⟨(chartAt (Euc 8) p₀.1).map_source hp.2.1, ?_⟩, Set.mem_univ _⟩
    show (chartAt (Euc 8) p₀.1).symm ((chartAt (Euc 8) p₀.1) p.1) ∈ coverBaseSet E.e i
    rw [(chartAt (Euc 8) p₀.1).left_inv hp.2.1]
    exact hp.1.1
  exact (hc.comp hchart hmaps).congr fun p hp => by
    show insF C i p.1 p.2
      = insF C i ((chartAt (Euc 8) p₀.1).symm ((chartAt (Euc 8) p₀.1) p.1)) p.2
    rw [(chartAt (Euc 8) p₀.1).left_inv hp.2.1]

/-- Joint continuity of the inverse trivialization `(x, v) ↦ readF C i x v` over the chart cover. -/
theorem continuousOn_readF {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k) :
    ContinuousOn (fun p : V.pt × Euc (8 + k) => readF C i p.1 p.2)
      (coverBaseSet E.e i ×ˢ Set.univ) := by
  refine continuousOn_of_locally_continuousOn fun p₀ hp₀ => ?_
  refine ⟨(chartAt (Euc 8) p₀.1).source ×ˢ Set.univ,
    (chartAt (Euc 8) p₀.1).open_source.prod isOpen_univ, ⟨mem_chart_source _ _, Set.mem_univ _⟩, ?_⟩
  have hc : ContinuousOn
      (fun p : Euc 8 × Euc (8 + k) => readF C i ((chartAt (Euc 8) p₀.1).symm p.1) p.2)
      (chartCover E i p₀.1 ×ˢ Set.univ) := (contDiffOn_readF_chart C i p₀.1).continuousOn
  have hchart : ContinuousOn
      (fun p : V.pt × Euc (8 + k) => ((chartAt (Euc 8) p₀.1) p.1, p.2))
      ((coverBaseSet E.e i ×ˢ Set.univ) ∩ ((chartAt (Euc 8) p₀.1).source ×ˢ Set.univ)) :=
    ((chartAt (Euc 8) p₀.1).continuousOn_toFun.comp continuousOn_fst
      (fun p hp => hp.2.1)).prodMk continuousOn_snd
  have hmaps : Set.MapsTo (fun p : V.pt × Euc (8 + k) => ((chartAt (Euc 8) p₀.1) p.1, p.2))
      ((coverBaseSet E.e i ×ˢ Set.univ) ∩ ((chartAt (Euc 8) p₀.1).source ×ˢ Set.univ))
      (chartCover E i p₀.1 ×ˢ Set.univ) := by
    intro p hp
    refine ⟨⟨(chartAt (Euc 8) p₀.1).map_source hp.2.1, ?_⟩, Set.mem_univ _⟩
    show (chartAt (Euc 8) p₀.1).symm ((chartAt (Euc 8) p₀.1) p.1) ∈ coverBaseSet E.e i
    rw [(chartAt (Euc 8) p₀.1).left_inv hp.2.1]
    exact hp.1.1
  exact (hc.comp hchart hmaps).congr fun p hp => by
    show readF C i p.1 p.2
      = readF C i ((chartAt (Euc 8) p₀.1).symm ((chartAt (Euc 8) p₀.1) p.1)) p.2
    rw [(chartAt (Euc 8) p₀.1).left_inv hp.2.1]

end

end Work.Tubular
