import Mathlib
import Submission.Work.Sard.weak_interior_empty_open
import Submission.Work.Projection.dimH_image_le_of_contDiffOn

namespace Work.Sard

open Metric Set Filter
open scoped Topology ContDiff ENNReal

/-! ### Auxiliary lemmas

The proof of the target theorem is in two steps.

* **Model case.**  A `C¹` map `G : 𝔼^m → 𝔼^n` raises Hausdorff dimension at most to the dimension of
  its source, so the image of *any* set has Hausdorff dimension at most `m`; if `m < n` this is
  strictly less than `n`, and a set of Hausdorff dimension `< n` in `𝔼^n` has empty interior.
* **Manifold case.**  Charts are homeomorphisms onto open subsets of `𝔼^n`, hence open maps, and the
  composite of `g` with a chart is again `C¹`.  A nonempty open subset of `g '' K` therefore produces
  a nonempty open subset of `G '' S` for a `C¹` map `G : 𝔼^m → 𝔼^n`, contradicting the model case. -/

/-- A set whose Hausdorff dimension is strictly smaller than the dimension of the ambient
finite-dimensional real vector space has empty interior. -/
lemma interior_eq_empty_of_dimH_lt_fin {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {s : Set F}
    (h : dimH s < ((Module.finrank ℝ F : ℕ) : ℝ≥0∞)) : interior s = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  exact dense_compl_of_dimH_lt_finrank h

/-- **The Euclidean model case.**  If `m < n` and `G : 𝔼^m → 𝔼^n` is `C¹` on an open set `U`, then
`G` maps any subset of `U` to a set with empty interior.  (The image has Hausdorff dimension at most
`m`, and `m < n`.) -/
lemma interior_image_eq_empty_of_contDiffOn_fin_lt {m n : ℕ} (hmn : m < n)
    {G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    {S : Set (EuclideanSpace ℝ (Fin m))} (hS : S ⊆ U) : interior (G '' S) = ∅ := by
  refine interior_eq_empty_of_dimH_lt_fin ?_
  rw [finrank_euclideanSpace_fin]
  have hle : dimH (G '' S) ≤ (m : ℝ≥0∞) := by
    have h := Work.Projection.dimH_image_le_of_contDiffOn hU hG hS
    rwa [finrank_euclideanSpace_fin] at h
  exact lt_of_le_of_lt hle (by exact_mod_cast hmn)

/-- **The image of a lower-dimensional `C^∞` map has empty interior.**  For `m < n` and a `C^∞` map
`g` from `𝔼^m` into a smooth `n`-manifold `M`, the image of any set has empty interior.  (This is the
`m < n` case of Sard's theorem: the image of a smooth map from a lower-dimensional source is a null
set.) -/
theorem interior_image_eq_empty_of_contMDiff_of_lt
    {m n : ℕ} (hmn : m < n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (g : EuclideanSpace ℝ (Fin m) → M)
    (hg : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (K : Set (EuclideanSpace ℝ (Fin m))) :
    interior (g '' K) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro p hp
  rw [mem_interior_iff_mem_nhds] at hp
  obtain ⟨V, hVK, hVopen, hpV⟩ := mem_nhds_iff.mp hp
  set c := chartAt (EuclideanSpace ℝ (Fin n)) p with hc
  have hp_src : p ∈ c.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) p
  set W : Set M := V ∩ c.source with hW
  have hWopen : IsOpen W := hVopen.inter c.open_source
  have hpW : p ∈ W := ⟨hpV, hp_src⟩
  -- the set of parameters whose image lies in the chart source
  set S : Set (EuclideanSpace ℝ (Fin m)) := K ∩ g ⁻¹' c.source with hS
  have hU : IsOpen (g ⁻¹' c.source) := c.open_source.preimage hg.continuous
  have hSsub : S ⊆ g ⁻¹' c.source := inter_subset_right
  -- the composite `c ∘ g` is `C¹` on that set
  have hcomp : ContDiffOn ℝ 1 (c ∘ g) (g ⁻¹' c.source) := by
    have h1 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) g
        (g ⁻¹' c.source) := hg.contMDiffOn
    have h2 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c
        c.source := contMDiffOn_chart
    have h3 := h2.comp h1 subset_rfl
    have hle : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
    exact (h3.of_le hle).contDiffOn
  have hmain : interior ((c ∘ g) '' S) = ∅ :=
    interior_image_eq_empty_of_contDiffOn_fin_lt hmn hU hcomp hSsub
  -- the chart image of `W` is a nonempty open subset of the model image
  have hopen_cW : IsOpen (c '' W) := c.isOpen_image_of_subset_source hWopen inter_subset_right
  have hmem_cW : c p ∈ c '' W := ⟨p, hpW, rfl⟩
  have hsub : c '' W ⊆ (c ∘ g) '' S := by
    rintro y ⟨w, hw, rfl⟩
    obtain ⟨hwV, hwsrc⟩ := hw
    obtain ⟨k, hkK, hgk⟩ := hVK hwV
    refine ⟨k, ⟨hkK, ?_⟩, ?_⟩
    · show g k ∈ c.source
      rw [hgk]
      exact hwsrc
    · simp only [Function.comp_apply, hgk]
  have hmem : c p ∈ interior ((c ∘ g) '' S) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hopen_cW.mem_nhds hmem_cW) hsub
  rw [hmain] at hmem
  exact hmem

end Work.Sard
