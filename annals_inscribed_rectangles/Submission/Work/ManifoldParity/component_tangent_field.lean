import Mathlib
import Submission.Work.ManifoldParity.Defs
import Submission.Work.ManifoldParity.GraphManifold
import Submission.Work.ManifoldParity.curve_tangent_chart
import Submission.Work.ManifoldParity.GraphInclusion
import Submission.Work.ManifoldParity.OpensInclusion
import Submission.Work.ManifoldParity.CircleParam
import Submission.Work.ManifoldParity.exists_continuous_tangent_field
import Submission.Work.OneDim.classify_connected_one_manifold

/-!
# A continuous non-vanishing tangent field along a connected component

Let `W ⊆ ℝⁿ` be locally the graph of a smooth function over some coordinate axis
(`Work.ManifoldParity.HasLocalGraphCharts`).  The target of this file,
`Work.ManifoldParity.component_tangent_field`, exhibits for every `p : ↥W` a continuous field `U` on
the image of the connected component of `p` in `↥W` which is nowhere zero there and is parallel to
the tangent of *every* graph chart of `W` at its points.

The proof splits according to whether the component is compact:

* **compact component.**  Then `K := Subtype.val '' connectedComponent p` is a compact subset of `ℝⁿ`
  and, since a connected component of a locally-graph set is *open* in `↥W`
  (`Work.ManifoldParity.isOpen_connectedComponent_graph`), `K` is itself locally a graph: the graph
  charts of `W` restrict to `K` after intersecting their domain with an ambient open set `O` with
  `O ∩ W ⊆ K`.  The already proved compact chapter
  `Work.ManifoldParity.exists_continuous_tangent_field` produces the field, and the restricted charts
  give the parallelism with the charts of `W`.

* **non-compact component.**  Then `↥(connectedComponent p)` is a connected smooth `1`-manifold
  without boundary which is not compact, so `Work.OneDim.classify_connected_one_manifold` makes it
  diffeomorphic to `ℝ`.  Composing the ambient inclusion -- smooth with injective manifold derivative
  by `Work.ManifoldParity.contMDiff_subtype_val_graph` and
  `Work.ManifoldParity.mfderiv_subtype_val_injective` -- with that diffeomorphism gives a smooth map
  `γ : ℝ → ℝⁿ` which is an *embedding* with range `Subtype.val '' connectedComponent p` and nowhere
  vanishing velocity.  Transporting the velocity back along `γ` (a homeomorphism onto its range)
  gives the field, and the parallelism with the graph charts is the chain rule
  `Work.ManifoldParity.curve_tangent_chart`.
-/

namespace Work.ManifoldParity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Topology Manifold

variable {n : ℕ}

/-- **An open subset of a subtype is, near each of its points, the trace of an open subset of the
ambient space.** -/
theorem exists_isOpen_subset_of_isOpen_subtype {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {C : Set ↥K} (hC : IsOpen C) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K)
    (hxC : (⟨x, hx⟩ : ↥K) ∈ C) :
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ x ∈ O ∧
      ∀ y : ↥K, (y : EuclideanSpace ℝ (Fin n)) ∈ O → y ∈ C := by
  obtain ⟨O, hOo, hOeq⟩ := (Topology.IsInducing.subtypeVal.isOpen_iff).mp hC
  refine ⟨O, hOo, ?_, ?_⟩
  · have h : (⟨x, hx⟩ : ↥K) ∈ (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) ⁻¹' O := by
      rw [hOeq]; exact hxC
    simpa using h
  · intro y hy
    have h : y ∈ (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) ⁻¹' O := hy
    rw [hOeq] at h
    exact h

theorem component_tangent_field {n : ℕ}
    (W : Set (EuclideanSpace ℝ (Fin n)))
    (hW : Work.ManifoldParity.HasLocalGraphCharts W)
    (p : ↥W) :
    ∃ U : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContinuousOn U ((Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) '' (connectedComponent p)) ∧
      (∀ y ∈ (Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) '' (connectedComponent p), U y ≠ 0) ∧
      (∀ y ∈ (Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) '' (connectedComponent p),
        ∀ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ → EuclideanSpace ℝ (Fin n)),
          Work.ManifoldParity.IsGraphChart W i V η → y ∈ V → ∃ c : ℝ, c ≠ 0 ∧
            U y = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (y i)) (1 : ℝ))) := by
  classical
  by_cases hcomp : IsCompact (connectedComponent p)
  · -- ## The component is compact
    have hKcpt : IsCompact
        ((Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) '' (connectedComponent p)) :=
      hcomp.image continuous_subtype_val
    have hKgraph : ∀ x ∈ ((Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) '' (connectedComponent p)),
        ∃ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin n)))
          (η : ℝ → EuclideanSpace ℝ (Fin n)),
          IsOpen V ∧ x ∈ V ∧ ContDiff ℝ ctSmooth η ∧ (∀ t, η t i = 0) ∧
          ∀ y ∈ V, (y ∈ ((Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) '' (connectedComponent p))
            ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i)) := by
      rintro x ⟨w, hw, rfl⟩
      letI := graphChartedSpace W hW
      have hCopen : IsOpen (connectedComponent p : Set ↥W) :=
        isOpen_connectedComponent_graph W hW p
      obtain ⟨O, hOo, hxO, hOW⟩ :=
        exists_isOpen_subset_of_isOpen_subtype (K := W) hCopen w.2 hw
      obtain ⟨i, V, η, hchart, hxV⟩ := hW (w : EuclideanSpace ℝ (Fin n)) w.2
      refine ⟨i, O ∩ V, η, hOo.inter hchart.1, ⟨hxO, hxV⟩, hchart.2.1, hchart.2.2.1, ?_⟩
      intro y hy
      obtain ⟨hyO, hyV⟩ := hy
      constructor
      · intro hyK
        obtain ⟨w', hw'C, rfl⟩ := hyK
        exact (hchart.2.2.2 _ hyV).mp w'.2
      · intro hyeq
        have hyW : y ∈ W := (hchart.2.2.2 y hyV).mpr hyeq
        exact ⟨⟨y, hyW⟩, hOW ⟨y, hyW⟩ hyO, rfl⟩
    obtain ⟨U, hcont, hne, hpar⟩ := exists_continuous_tangent_field _ hKcpt hKgraph
    refine ⟨U, hcont, hne, ?_⟩
    rintro y ⟨w, hw, rfl⟩ i V η hchart hyV
    letI := graphChartedSpace W hW
    have hCopen : IsOpen (connectedComponent p : Set ↥W) := isOpen_connectedComponent_graph W hW p
    obtain ⟨O, hOo, hyO, hOW⟩ := exists_isOpen_subset_of_isOpen_subtype (K := W) hCopen w.2 hw
    have hV'o : IsOpen (O ∩ V) := hOo.inter hchart.1
    have hyV' : (w : EuclideanSpace ℝ (Fin n)) ∈ O ∩ V := ⟨hyO, hyV⟩
    have hgr' : ∀ z ∈ O ∩ V,
        (z ∈ ((Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) '' (connectedComponent p))
          ↔ z = (z i) • EuclideanSpace.single i (1:ℝ) + η (z i)) := by
      intro z hz
      obtain ⟨hzO, hzV⟩ := hz
      constructor
      · intro hzK
        obtain ⟨w', hw'C, rfl⟩ := hzK
        exact (hchart.2.2.2 _ hzV).mp w'.2
      · intro hzeq
        have hzW : z ∈ W := (hchart.2.2.2 z hzV).mpr hzeq
        exact ⟨⟨z, hzW⟩, hOW ⟨z, hzW⟩ hzO, rfl⟩
    exact hpar (w : EuclideanSpace ℝ (Fin n)) ⟨w, hw, rfl⟩ i (O ∩ V) η hV'o hyV'
      hchart.2.1 hchart.2.2.1 hgr'
  · -- ## The component is not compact: it is diffeomorphic to `ℝ`
    letI := graphChartedSpace W hW
    haveI hgr := hasGroupoid_graph W hW
    haveI hism : IsManifold (modelWithCornersSelf ℝ ME1) ctSmooth ↥W := IsManifold.mk' _ _ _
    set Cx : TopologicalSpace.Opens ↥W :=
      ⟨connectedComponent p, isOpen_connectedComponent_graph W hW p⟩ with hCxdef
    haveI : IsManifold (modelWithCornersSelf ℝ ME1) ctSmooth ↥Cx := IsManifold.mk' _ _ _
    haveI : ConnectedSpace ↥Cx :=
      isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := p))
    have hnec : ¬ CompactSpace ↥Cx := fun hc => hcomp (isCompact_iff_compactSpace.mpr hc)
    rcases Work.OneDim.classify_connected_one_manifold (C := ↥Cx) with ⟨⟨G⟩⟩ | ⟨⟨G⟩⟩
    · -- ## The component is `ℝ`
      -- ### the parametrisation in the manifold `↥W`
      let γm : ℝ → ↥W := fun t => ((G t : ↥Cx) : ↥W)
      have hγm_cd : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
          ctSmooth γm :=
        (contMDiff_subtype_val (U := Cx) (n := ctSmooth)).comp G.contMDiff
      have hγm_inj : Function.Injective γm := fun a b hab => G.injective (Subtype.ext hab)
      have hγm_range : Set.range γm = (connectedComponent p : Set ↥W) := by
        ext z
        constructor
        · rintro ⟨t, rfl⟩
          exact (G t).2
        · intro hz
          obtain ⟨w, hw⟩ := G.surjective ⟨z, hz⟩
          exact ⟨w, congrArg (fun y : ↥Cx => (y : ↥W)) hw⟩
      have hγm_mf : ∀ t : ℝ,
          mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1) γm t 1 ≠ 0 := by
        intro t hv
        have hchain : mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1) γm t
            = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
                (Subtype.val : ↥Cx → ↥W) (G t)) ∘SL
              (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
                (G : ℝ → ↥Cx) t) :=
          mfderiv_comp t
            ((Manifold.IsSmoothEmbedding.of_opens (n := ctSmooth) Cx).contMDiff.contMDiffAt
              |>.mdifferentiableAt (by simp))
            (G.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        rw [hchain] at hv
        have hinj1 : Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ ME1) (G : ℝ → ↥Cx) t) :=
          ((G.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (n := ctSmooth) (by simp)
            t).toLinearEquiv).injective
        have hinj2 : Function.Injective (mfderiv (modelWithCornersSelf ℝ ME1)
            (modelWithCornersSelf ℝ ME1) (Subtype.val : ↥Cx → ↥W) (G t)) :=
          mfderiv_subtypeVal_opens_injective Cx (G t)
        have hzero : (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
            (G : ℝ → ↥Cx) t) (1 : ℝ) = 0 := by
          apply hinj2
          rw [map_zero]
          exact hv
        have h10 : (1 : ℝ) = 0 := hinj1 (by rw [hzero, map_zero])
        exact one_ne_zero h10
      -- ### the ambient curve
      let γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => (γm t : EuclideanSpace ℝ (Fin n))
      have hγ_cd : ContMDiff (modelWithCornersSelf ℝ ℝ)
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ctSmooth γ :=
        (contMDiff_subtype_val_graph W hW).comp hγm_cd
      have hγ_sm : ContDiff ℝ ctSmooth γ := contMDiff_iff_contDiff.mp hγ_cd
      have hγ_mf : ∀ t : ℝ,
          mfderiv (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) γ t 1 ≠ 0 := by
        intro t hv
        have hchain : mfderiv (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) γ t
            = (mfderiv (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                (Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) (γm t)) ∘SL
              (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1) γm t) :=
          mfderiv_comp t
            ((contMDiff_subtype_val_graph W hW).contMDiffAt.mdifferentiableAt (by simp))
            (hγm_cd.contMDiffAt.mdifferentiableAt (by simp))
        rw [hchain] at hv
        refine hγm_mf t ?_
        apply mfderiv_subtype_val_injective W hW (γm t)
        rw [map_zero]
        exact hv
      have hγ_deriv : ∀ t : ℝ, fderiv ℝ γ t 1 ≠ 0 := fun t h0 => hγ_mf t (by
        rw [mfderiv_eq_fderiv]; exact h0)
      have hγ_inj : Function.Injective γ := fun a b hab => hγm_inj (Subtype.ext hab)
      have hγ_range : Set.range γ =
          (Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) '' (connectedComponent p) := by
        have hcomp' : γ = (Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) ∘ γm := rfl
        rw [hcomp', Set.range_comp, hγm_range]
      have hγm_emb : Topology.IsEmbedding γm :=
        (Topology.IsEmbedding.subtypeVal).comp G.toHomeomorph.isEmbedding
      have hγ_emb : Topology.IsEmbedding γ :=
        (Topology.IsEmbedding.subtypeVal).comp hγm_emb
      -- ### the transport of the velocity along `γ`
      let U : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y =>
        if h : y ∈ Set.range γ then
          fderiv ℝ γ (hγ_emb.toHomeomorph.symm ⟨y, h⟩) 1 else 0
      have hU_apply : ∀ (y : EuclideanSpace ℝ (Fin n)) (h : y ∈ Set.range γ),
          U y = fderiv ℝ γ (hγ_emb.toHomeomorph.symm ⟨y, h⟩) 1 := fun y h => dif_pos h
      have hU_eval : ∀ t : ℝ, U (γ t) = fderiv ℝ γ t 1 := by
        intro t
        have hmem : γ t ∈ Set.range γ := ⟨t, rfl⟩
        have hsymm : hγ_emb.toHomeomorph.symm ⟨γ t, hmem⟩ = t := by
          have h1 : (⟨γ t, hmem⟩ : Set.range γ) = ⟨γ t, mem_range_self t⟩ := Subtype.ext rfl
          rw [h1]
          exact hγ_emb.toHomeomorph_symm_apply t
        rw [hU_apply _ hmem, hsymm]
      have hfderiv_cont : Continuous (fun t : ℝ => fderiv ℝ γ t 1) :=
        (hγ_sm.continuous_fderiv (by simp)).clm_apply continuous_const
      have hU_cont : ContinuousOn U (Set.range γ) := by
        rw [continuousOn_iff_continuous_domRestrict]
        refine (hfderiv_cont.comp hγ_emb.toHomeomorph.symm.continuous).congr ?_
        intro z
        show fderiv ℝ γ (hγ_emb.toHomeomorph.symm z) 1 = U (z : EuclideanSpace ℝ (Fin n))
        rw [hU_apply _ z.2]
      have hU_ne : ∀ y ∈ (Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) '' (connectedComponent p),
          U y ≠ 0 := by
        rintro y ⟨w, hw, rfl⟩
        have hmem : (w : EuclideanSpace ℝ (Fin n)) ∈ Set.range γ := by
          rw [hγ_range]
          exact ⟨w, hw, rfl⟩
        rw [hU_apply _ hmem]
        exact hγ_deriv _
      have hU_par : ∀ y ∈ (Subtype.val : ↥W → EuclideanSpace ℝ (Fin n)) '' (connectedComponent p),
          ∀ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin n)))
            (η : ℝ → EuclideanSpace ℝ (Fin n)),
            IsGraphChart W i V η → y ∈ V → ∃ c : ℝ, c ≠ 0 ∧
              U y = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (y i)) (1 : ℝ)) := by
        rintro y ⟨w, hw, rfl⟩ i V η hchart hyV
        have hmem : (w : EuclideanSpace ℝ (Fin n)) ∈ Set.range γ := by
          rw [hγ_range]
          exact ⟨w, hw, rfl⟩
        have hγt : γ (hγ_emb.toHomeomorph.symm ⟨(w : EuclideanSpace ℝ (Fin n)), hmem⟩) =
            (w : EuclideanSpace ℝ (Fin n)) := by
          have h2 : ((hγ_emb.toHomeomorph
              (hγ_emb.toHomeomorph.symm ⟨(w : EuclideanSpace ℝ (Fin n)), hmem⟩) :
                Set.range γ) : EuclideanSpace ℝ (Fin n)) = (w : EuclideanSpace ℝ (Fin n)) :=
            congrArg (Subtype.val)
              (hγ_emb.toHomeomorph.apply_symm_apply ⟨(w : EuclideanSpace ℝ (Fin n)), hmem⟩)
          exact h2
        obtain ⟨c, hc, hce⟩ := curve_tangent_chart W i V η hchart γ hγ_sm
          (fun s => (γm s).2) _ (by rw [hγt]; exact hyV) (hγ_deriv _)
        refine ⟨c, hc, ?_⟩
        rw [hU_apply _ hmem, hce, hγt]
      refine ⟨U, ?_, hU_ne, hU_par⟩
      rw [← hγ_range]
      exact hU_cont
    · -- ## The circle case contradicts the non-compactness of the component
      exact absurd G.toHomeomorph.compactSpace hnec

end

end Work.ManifoldParity
