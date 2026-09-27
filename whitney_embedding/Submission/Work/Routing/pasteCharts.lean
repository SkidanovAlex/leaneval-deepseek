import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

namespace Work.Routing

open Set

/-- Two charts of the maximal atlas `C^∞`-compatible with the model `𝓡 n` can be pasted on
disjoint open sets whose images are disjoint: the map which agrees with the first chart on `U`
and with the second chart on `V` is again a chart of the maximal atlas. -/
theorem pasteCharts {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    {c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (h₁ : c₁ ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    (h₂ : c₂ ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    {U V : Set M} (hUo : IsOpen U) (hVo : IsOpen V)
    (hdisj : Disjoint U V) (himg : Disjoint (c₁ '' U) (c₂ '' V))
    (hUsub : U ⊆ c₁.source) (hVsub : V ⊆ c₂.source) :
    ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder M ∧
      (∀ m ∈ U, c m = c₁ m) ∧ (∀ m ∈ V, c m = c₂ m) := by
  classical
  let f : M → EuclideanSpace ℝ (Fin n) := fun m => if m ∈ U then c₁ m else c₂ m
  let g : EuclideanSpace ℝ (Fin n) → M := fun y => if y ∈ c₁ '' U then c₁.symm y else c₂.symm y
  have hfU : ∀ m ∈ U, f m = c₁ m := fun m hm => by simp [f, hm]
  have hfV : ∀ m ∈ V, f m = c₂ m := fun m hm => by
    have hmU : m ∉ U := (Set.disjoint_right.mp hdisj) hm
    simp [f, hmU]
  have hgU : ∀ y ∈ c₁ '' U, g y = c₁.symm y := fun y hy => by
    dsimp only [g]; rw [if_pos hy]
  have hgV : ∀ y ∈ c₂ '' V, g y = c₂.symm y := fun y hy => by
    have hyU : y ∉ c₁ '' U := (Set.disjoint_right.mp himg) hy
    dsimp only [g]; rw [if_neg hyU]
  have hct : c₁ '' U ⊆ c₁.target := (image_mono hUsub).trans (le_of_eq c₁.image_source_eq_target)
  have hdt : c₂ '' V ⊆ c₂.target := (image_mono hVsub).trans (le_of_eq c₂.image_source_eq_target)
  have hopenU : IsOpen (c₁ '' U) := c₁.isOpen_image_of_subset_source hUo hUsub
  have hopenV : IsOpen (c₂ '' V) := c₂.isOpen_image_of_subset_source hVo hVsub
  have hmap_source : ∀ ⦃x⦄, x ∈ U ∪ V → f x ∈ c₁ '' U ∪ c₂ '' V := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ⟨x, hx, (hfU x hx).symm⟩
    · exact Or.inr ⟨x, hx, (hfV x hx).symm⟩
  have hmap_target : ∀ ⦃y⦄, y ∈ c₁ '' U ∪ c₂ '' V → g y ∈ U ∪ V := by
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨m, hm, rfl⟩ := hy
      refine Or.inl ?_
      rw [hgU _ ⟨m, hm, rfl⟩, c₁.left_inv (hUsub hm)]
      exact hm
    · obtain ⟨m, hm, rfl⟩ := hy
      refine Or.inr ?_
      rw [hgV _ ⟨m, hm, rfl⟩, c₂.left_inv (hVsub hm)]
      exact hm
  have hleft : ∀ ⦃x⦄, x ∈ U ∪ V → g (f x) = x := by
    intro x hx
    rcases hx with hx | hx
    · rw [hfU x hx, hgU _ ⟨x, hx, rfl⟩, c₁.left_inv (hUsub hx)]
    · have hfx : f x = c₂ x := hfV x hx
      rw [hgV _ ⟨x, hx, hfx.symm⟩, hfx, c₂.left_inv (hVsub hx)]
  have hright : ∀ ⦃y⦄, y ∈ c₁ '' U ∪ c₂ '' V → f (g y) = y := by
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨m, hm, rfl⟩ := hy
      rw [hgU _ ⟨m, hm, rfl⟩, c₁.left_inv (hUsub hm), hfU m hm]
    · obtain ⟨m, hm, rfl⟩ := hy
      rw [hgV _ ⟨m, hm, rfl⟩, c₂.left_inv (hVsub hm), hfV m hm]
  have hcontf : ContinuousOn f (U ∪ V) := by
    rw [continuousOn_union_iff_of_isOpen hUo hVo]
    exact ⟨(c₁.continuousOn.mono hUsub).congr (fun x hx => hfU x hx),
           (c₂.continuousOn.mono hVsub).congr (fun x hx => hfV x hx)⟩
  have hcontg : ContinuousOn g (c₁ '' U ∪ c₂ '' V) := by
    rw [continuousOn_union_iff_of_isOpen hopenU hopenV]
    exact ⟨(c₁.continuousOn_symm.mono hct).congr (fun y hy => hgU y hy),
           (c₂.continuousOn_symm.mono hdt).congr (fun y hy => hgV y hy)⟩
  let pe : PartialEquiv M (EuclideanSpace ℝ (Fin n)) :=
    PartialEquiv.mk f g (U ∪ V) (c₁ '' U ∪ c₂ '' V) hmap_source hmap_target hleft hright
  let ph : PartialHomeomorph M (EuclideanSpace ℝ (Fin n)) := PartialHomeomorph.mk pe hcontf hcontg
  let φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    { toPartialHomeomorph := ph
      open_source := hUo.union hVo
      open_target := hopenU.union hopenV }
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    constructor
    · change ContMDiffOn (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.smoothOrder) f (U ∪ V)
      rw [contMDiffOn_union_iff_of_isOpen hUo hVo]
      exact ⟨((contMDiffOn_of_mem_maximalAtlas h₁).mono hUsub).congr (fun x hx => hfU x hx),
             ((contMDiffOn_of_mem_maximalAtlas h₂).mono hVsub).congr (fun x hx => hfV x hx)⟩
    · change ContMDiffOn (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.smoothOrder) g (c₁ '' U ∪ c₂ '' V)
      rw [contMDiffOn_union_iff_of_isOpen hopenU hopenV]
      exact ⟨((contMDiffOn_symm_of_mem_maximalAtlas h₁).mono hct).congr (fun y hy => hgU y hy),
             ((contMDiffOn_symm_of_mem_maximalAtlas h₂).mono hdt).congr (fun y hy => hgV y hy)⟩
  · intro m hm; exact hfU m hm
  · intro m hm; exact hfV m hm

end Work.Routing
