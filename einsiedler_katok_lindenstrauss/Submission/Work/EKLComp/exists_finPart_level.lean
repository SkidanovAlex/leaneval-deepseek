import Mathlib
import Submission.Work.EKLComp.USCBasic
import Submission.Work.EKLComp.FinPartLevel
import Submission.Work.EKLComp.levelCell_disjoint
import Submission.Work.EKLComp.levelCell_cover
import Submission.Work.EKLComp.levelCell_measurable
import Submission.Work.EKLComp.frontier_levelCell_levelCore
import Submission.Work.EKLComp.finPart_snoc_fields


namespace Work.EKLComp

open MeasureTheory Set

/- ---------- helper lemmas of my own ---------- -/

private lemma frontier_const_lt_subset {α : Type*} [TopologicalSpace α] (f : α → ℝ) (hf : Continuous f)
    (c : ℝ) : frontier {x | c < f x} ⊆ {x | f x = c} := by
  intro x hx
  have hx' : c = f x := frontier_lt_subset_eq (f := fun _ : α => c) (g := f)
    continuous_const hf hx
  simpa using hx'.symm

private lemma frontier_le_const_subset {α : Type*} [TopologicalSpace α] (f : α → ℝ) (hf : Continuous f)
    (c : ℝ) : frontier {x | f x ≤ c} ⊆ {x | f x = c} :=
  frontier_le_subset_eq hf continuous_const

/- ---------- the main theorem ---------- -/

theorem exists_finPart_level (μ : MeasureTheory.Measure Work.EKLContract.X3) {ι : Type*}
    [Fintype ι] (Φ : ι → Work.EKLContract.X3 → ℝ) (hΦ : ∀ i, Continuous (Φ i)) {c : ℝ}
    (hc : ∀ i, μ (Φ i ⁻¹' ({c} : Set ℝ)) = 0) :
    ∃ P : Work.EKLContract.FinPart Work.EKLContract.X3,
      (∀ k, μ (frontier (P.parts k)) = 0) ∧
      ∀ k, (∃ i, P.parts k ⊆ {x | c < Φ i x}) ∨ (P.parts k ⊆ {x | ∀ i, Φ i x ≤ c}) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let U : ι → Set Work.EKLContract.X3 := fun i => {x | c < Φ i x}
  let C : ι → Set Work.EKLContract.X3 := fun i => {x | Φ i x ≤ c}
  have hUC : ∀ i, C i = (U i)ᶜ := by
    intro i
    ext x
    simp only [C, U, Set.mem_ofPred_eq, Set.mem_compl_iff]
    exact not_lt.symm
  have hUmeas : ∀ i, MeasurableSet (U i) :=
    fun i => (isOpen_lt continuous_const (hΦ i)).measurableSet
  have hCmeas : ∀ i, MeasurableSet (C i) :=
    fun i => (isClosed_le (hΦ i) continuous_const).measurableSet
  have hUfr : ∀ i, μ (frontier (U i)) = 0 := by
    intro i
    refine measure_mono_null ?_ (hc i)
    intro x hx
    have h2 : x ∈ {x | Φ i x = c} := frontier_const_lt_subset (Φ i) (hΦ i) c hx
    simpa using h2
  have hCfr : ∀ i, μ (frontier (C i)) = 0 := by
    intro i
    rw [hUC i, frontier_compl]
    refine measure_mono_null ?_ (hc i)
    intro x hx
    have h2 : x ∈ {x | Φ i x = c} := frontier_const_lt_subset (Φ i) (hΦ i) c hx
    simpa using h2
  obtain ⟨hcellMeas, hcoreMeas⟩ := levelCell_measurable e U C hUmeas hCmeas
  obtain ⟨hdisjCell, hdisjCore⟩ := levelCell_disjoint e U C hUC
  obtain ⟨hcellFr, hcoreFr⟩ := frontier_levelCell_levelCore μ e U C hUfr hCfr
  have hcover : ∀ x : Work.EKLContract.X3,
      x ∈ levelCore C ∨ ∃ m : Fin (Fintype.card ι), x ∈ levelCell e U C m :=
    fun x => levelCell_cover e U C hUC x
  obtain ⟨hpartsMeas, hpartsDisj, hpartsCover⟩ :=
    finPart_snoc_fields (levelCell e U C) (levelCore C) hcellMeas hcoreMeas hdisjCell hdisjCore hcover
  let A : Fin (Fintype.card ι) → Set Work.EKLContract.X3 := levelCell e U C
  let G : Set Work.EKLContract.X3 := levelCore C
  let P : Work.EKLContract.FinPart Work.EKLContract.X3 :=
    { n := Fintype.card ι + 1
      parts := (Fin.snoc A G : Fin (Fintype.card ι + 1) → Set Work.EKLContract.X3)
      measurable := hpartsMeas
      disjoint := hpartsDisj
      cover := hpartsCover }
  have hP_parts : P.parts = (Fin.snoc A G : Fin (Fintype.card ι + 1) → Set Work.EKLContract.X3) := rfl
  have hPlast : P.parts (Fin.last (Fintype.card ι)) = G := by
    rw [hP_parts, Fin.snoc_last]
  have hPcast : ∀ m : Fin (Fintype.card ι), P.parts (Fin.castSucc m) = A m := fun m => by
    rw [hP_parts, Fin.snoc_castSucc]
  refine ⟨P, ?_, ?_⟩
  · intro k
    refine Fin.lastCases ?_ ?_ k
    · rw [hPlast]
      exact hcoreFr
    · intro m
      rw [hPcast m]
      exact hcellFr m
  · intro k
    refine Fin.lastCases ?_ ?_ k
    · rw [hPlast]
      refine Or.inr ?_
      intro x hx
      have hx' : ∀ j, x ∈ C j := by
        simpa only [G, levelCore, Set.mem_iInter] using hx
      simp only [Set.mem_ofPred_eq]
      intro i
      simpa [C] using hx' i
    · intro m
      rw [hPcast m]
      refine Or.inl ⟨e.symm m, ?_⟩
      intro x hx
      simp only [A, levelCell, Set.mem_inter_iff] at hx
      have h2 : x ∈ U (e.symm m) := hx.1
      simpa [U] using h2

end Work.EKLComp
