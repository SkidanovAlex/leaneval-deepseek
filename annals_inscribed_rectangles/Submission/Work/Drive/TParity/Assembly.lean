import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.FlowDefs
import Submission.Work.Drive.TParity.FlowSetupK3
import Submission.Work.Drive.TParity.graph_data_K3
import Submission.Work.Drive.TParity.exists_tangential_field3
import Submission.Work.Drive.TParity.face_data_K3
import Submission.Work.Drive.TParity.K3_mapsTo_flowV
import Submission.Work.Drive.TParity.exists_flowCover3
import Submission.Work.Drive.TParity.finite_bK3
import Submission.Work.Drive.ManifoldParity.FlowSetupPairing

/-!
# The parity of the boundary triple intersections in the nine-box

This is the assembly of the mod-2 parity argument for the triple intersection of three transverse
`3`-chains in a smooth `4`-manifold, in the coordinates of the nine-box `ℝ⁹ = ℝ³ × ℝ³ × ℝ³`.

The pieces are

* `Work.Drive.TParity.graph_data_K3` + `Work.Drive.TParity.exists_tangential_field3`: a smooth,
  compactly supported tangent field `V` along the triple intersection set, non-zero on it;
* `Work.Drive.TParity.face_data_K3`: at every boundary triple intersection the field crosses the
  corresponding face of the box transversally;
* `Work.Drive.TParity.K3_mapsTo_flowV`: the flow of `V` preserves the triple intersection set while
  it stays in the box;
* `Work.Drive.TParity.exists_flowCover3`: a finite cover of the intersection set by flow charts;
* `Work.Drive.even_ncard_boundary`: the abstract pairing of the boundary points of a tangentially
  flowed compact set, which gives that their number is even;
* `Work.Drive.TParity.finite_bK3`: finiteness of the boundary triple intersections.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The three face parts are pairwise disjoint.**  Under the face hypothesis, at a boundary triple
intersection point exactly one coordinate of exactly one block is on a face, so two distinct blocks
cannot both be on a face. -/
theorem S3_pairwise_disjoint (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hface : faceHyp D) {k k' : Fin 3} (hkk : k ≠ k') : Disjoint (S3 D k) (S3 D k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨hbox, hm, hf⟩ := mem_S3.mp hx
  obtain ⟨-, -, hf'⟩ := mem_S3.mp hx'
  have hbdry : x ∈ Submission.Drive.unitBoxBdry 8 :=
    (mem_unitBoxBdry8_iff x).mpr ⟨hbox, k, (onBlockFace_iff_of_mem x hbox k).mp hf⟩
  obtain ⟨k₀, i₀, hi₀, hoth, hoth', -, -, -⟩ := hface x hbox hm hbdry
  -- a coordinate on a face has to be the distinguished one
  have hkey : ∀ {l : Fin 3} {j : Fin 3}, (x (Work.Drive.bIdx l j) = 0 ∨ x (Work.Drive.bIdx l j) = 1) →
      l = k₀ := by
    intro l j hj
    by_cases hl : l = k₀
    · exact hl
    · exfalso
      have hmem := hoth' l hl j
      rcases hj with h | h
      · rw [h] at hmem
        exact absurd hmem.1 (by norm_num)
      · rw [h] at hmem
        exact absurd hmem.2 (by norm_num)
  obtain ⟨j, hj⟩ := hf
  obtain ⟨j', hj'⟩ := hf'
  exact hkk ((hkey hj).trans (hkey hj').symm)

/-- **The parity of the boundary triple intersections, in the nine-box.**  The boundary part of the
triple intersection set of three transverse `3`-chains in a smooth `4`-manifold is finite, and the
sum of the three labelled counts is even. -/
theorem bK3_even (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    (htrans : transHyp D) (hface : faceHyp D) :
    (bK3 D).Finite ∧
      Even ((S3 D 0).ncard + (S3 D 1).ncard + (S3 D 2).ncard) := by
  -- a tangent field along the triple intersection set
  obtain ⟨V, hV, hVs, hVne, hVtan⟩ :=
    exists_tangential_field3 D hD (graph_data_K3 D hD htrans)
  -- its face condition
  have hVface : Vface D V := face_data_K3 D hD htrans hface V hVtan hVne
  -- the flow of `V` preserves the intersection set
  have hmapsTo : ∀ x ∈ K3 D, ∀ t : ℝ,
      (∀ u ∈ Set.uIcc (0 : ℝ) t, flowV8 V hV hVs u x ∈ Submission.Drive.unitBox 8) →
      flowV8 V hV hVs t x ∈ K3 D :=
    fun x hx t hbox => K3_mapsTo_flowV D hD htrans V hV hVs hVtan hVface x hx t hbox
  -- a finite cover by flow charts
  obtain ⟨Cov⟩ := exists_flowCover3 D hD htrans V hV hVs hVtan hVne hmapsTo
  have hface' : ∀ b ∈ (K3_setup D V hV hVs hmapsTo).K ∩ Submission.Drive.unitBoxBdry 8,
      ∃ i : Fin 9, (b i = 0 ∨ b i = 1) ∧ (∀ j, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (K3_setup D V hV hVs hmapsTo).W b i ≠ 0 := by
    intro b hb
    exact hVface b hb.1 hb.2
  -- the abstract parity of the boundary points
  have heven : Even ((bK3 D).ncard) := by
    have h := even_ncard_boundary (K3_setup D V hV hVs hmapsTo) Cov hface'
    have hset : (K3_setup D V hV hVs hmapsTo).K ∩ Submission.Drive.unitBoxBdry 8 = bK3 D := by
      rw [K3_setup_K]
      ext x
      constructor
      · rintro ⟨⟨hbox, hm⟩, hb⟩
        exact ⟨hbox, hm, hb⟩
      · rintro ⟨hbox, hm, hb⟩
        exact ⟨⟨hbox, hm⟩, hb⟩
    rwa [hset] at h
  -- finiteness, and the splitting of the count over the three blocks
  have hfin : (bK3 D).Finite := finite_bK3 D hD htrans hface
  have hf0 : (S3 D 0).Finite :=
    hfin.subset (by rw [bK3_eq_union]; exact fun x hx => Or.inl (Or.inl hx))
  have hf1 : (S3 D 1).Finite :=
    hfin.subset (by rw [bK3_eq_union]; exact fun x hx => Or.inl (Or.inr hx))
  have hf2 : (S3 D 2).Finite :=
    hfin.subset (by rw [bK3_eq_union]; exact fun x hx => Or.inr hx)
  have hd01 : Disjoint (S3 D 0) (S3 D 1) := S3_pairwise_disjoint D hface (by decide)
  have hd02 : Disjoint (S3 D 0) (S3 D 2) := S3_pairwise_disjoint D hface (by decide)
  have hd12 : Disjoint (S3 D 1) (S3 D 2) := S3_pairwise_disjoint D hface (by decide)
  have hd012 : Disjoint (S3 D 0 ∪ S3 D 1) (S3 D 2) := by
    rw [Set.disjoint_left]
    rintro x (hx | hx) hy
    · exact Set.disjoint_left.mp hd02 hx hy
    · exact Set.disjoint_left.mp hd12 hx hy
  rw [bK3_eq_union] at heven
  rw [Set.ncard_union_eq hd012 (hf0.union hf1) hf2,
    Set.ncard_union_eq hd01 hf0 hf1] at heven
  exact ⟨hfin, heven⟩

end

end Work.Drive.TParity
