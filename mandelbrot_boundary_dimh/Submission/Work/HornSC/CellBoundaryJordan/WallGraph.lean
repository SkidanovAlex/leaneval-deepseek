import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.DartGraph

/-!
# The wall graph of a finite family of lattice cells

`wallSet A` is the union of the unit grid segments separating a cell of `A` from a cell outside
`A`.  Each such segment carries a canonical orientation (east for horizontal segments, north for
vertical ones); the resulting set of oriented steps is `wallStepFinset A`, and `wallDarts A` is
its symmetric closure.  This file sets up the corresponding `DartGraph` and the relation between
darts and the closed segments `adjSeg`.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

/-! ## Candidate lattice points -/

/-- The lattice points `u` at which a horizontal wall segment of `A` can start: the cell below
`u` or the cell above `u` belongs to `A`. -/
def hCand (A : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) := A ∪ A.image (fun p => (p.1, p.2 + 1))

/-- The lattice points `u` at which a vertical wall segment of `A` can start. -/
def vCand (A : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) := A ∪ A.image (fun p => (p.1 + 1, p.2))

lemma mem_hCand {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} :
    u ∈ hCand A ↔ u ∈ A ∨ (u.1, u.2 - 1) ∈ A := by
  rw [hCand, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨p, hp, hpu⟩)
    · exact Or.inl h
    · refine Or.inr ?_
      have hpe : (u.1, u.2 - 1) = p := by
        rw [← hpu]; simp
      rwa [hpe]
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨(u.1, u.2 - 1), h, by simp⟩

lemma mem_vCand {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} :
    u ∈ vCand A ↔ u ∈ A ∨ (u.1 - 1, u.2) ∈ A := by
  rw [vCand, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨p, hp, hpu⟩)
    · exact Or.inl h
    · refine Or.inr ?_
      have hpe : (u.1 - 1, u.2) = p := by
        rw [← hpu]; simp
      rwa [hpe]
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨(u.1 - 1, u.2), h, by simp⟩

lemma hWallAt_mem_hCand {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} (h : hWallAt A u) :
    u ∈ hCand A := by
  rw [mem_hCand]
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

lemma vWallAt_mem_vCand {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} (h : vWallAt A u) :
    u ∈ vCand A := by
  rw [mem_vCand]
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-! ## Wall steps -/

/-- The horizontal wall steps of `A`, oriented east. -/
noncomputable def hSteps (A : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := by
  classical
  exact ((hCand A).filter (hWallAt A)).image (fun u => (u, (u.1 + 1, u.2)))

/-- The vertical wall steps of `A`, oriented north. -/
noncomputable def vSteps (A : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := by
  classical
  exact ((vCand A).filter (vWallAt A)).image (fun u => (u, (u.1, u.2 + 1)))

/-- The wall steps of `A`: the unit steps whose segment is a wall of `A`, oriented canonically. -/
noncomputable def wallStepFinset (A : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := hSteps A ∪ vSteps A

/-- The dart set of the wall graph of `A`. -/
noncomputable def wallDarts (A : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  wallStepFinset A ∪ (wallStepFinset A).image Prod.swap

lemma mem_hSteps {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)} :
    e ∈ hSteps A ↔ ∃ u, hWallAt A u ∧ e = (u, (u.1 + 1, u.2)) := by
  classical
  rw [hSteps, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, hue⟩
    rw [Finset.mem_filter] at hu
    exact ⟨u, hu.2, hue.symm⟩
  · rintro ⟨u, hu, heu⟩
    exact ⟨u, Finset.mem_filter.mpr ⟨hWallAt_mem_hCand hu, hu⟩, heu.symm⟩

lemma mem_vSteps {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)} :
    e ∈ vSteps A ↔ ∃ u, vWallAt A u ∧ e = (u, (u.1, u.2 + 1)) := by
  classical
  rw [vSteps, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, hue⟩
    rw [Finset.mem_filter] at hu
    exact ⟨u, hu.2, hue.symm⟩
  · rintro ⟨u, hu, heu⟩
    exact ⟨u, Finset.mem_filter.mpr ⟨vWallAt_mem_vCand hu, hu⟩, heu.symm⟩

lemma mem_wallStepFinset {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)} :
    e ∈ wallStepFinset A ↔ (∃ u, hWallAt A u ∧ e = (u, (u.1 + 1, u.2))) ∨
      (∃ u, vWallAt A u ∧ e = (u, (u.1, u.2 + 1))) := by
  rw [wallStepFinset, Finset.mem_union, mem_hSteps, mem_vSteps]

lemma mem_wallDarts {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)} :
    e ∈ wallDarts A ↔ e ∈ wallStepFinset A ∨ e.swap ∈ wallStepFinset A := by
  rw [wallDarts, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨s, hs, hs'⟩)
    · exact Or.inl h
    · right
      have hse : e.swap = s := by rw [← hs']; exact Prod.swap_swap s
      rwa [hse]
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨e.swap, h, by simp⟩

lemma hSteps_unitStep {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)} (he : e ∈ hSteps A) :
    IsUnitStep e := by
  obtain ⟨u, _, heu⟩ := mem_hSteps.mp he
  rw [heu]; exact Or.inl rfl

lemma vSteps_unitStep {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)} (he : e ∈ vSteps A) :
    IsUnitStep e := by
  obtain ⟨u, _, heu⟩ := mem_vSteps.mp he
  rw [heu]; exact Or.inr rfl

lemma wallStepFinset_unitStep {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ wallStepFinset A) : IsUnitStep e := by
  rcases mem_wallStepFinset.mp he with ⟨u, h, heu⟩ | ⟨u, h, heu⟩
  · rw [heu]; exact Or.inl rfl
  · rw [heu]; exact Or.inr rfl

lemma hSteps_subset_wallSet {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)} (he : e ∈ hSteps A) :
    stepSeg e ⊆ wallSet A := by
  obtain ⟨u, hu, heu⟩ := mem_hSteps.mp he
  rw [heu, stepSeg_of_eq_east rfl]
  exact fun z hz => Or.inl (mem_hWallSet.mpr ⟨u, hu, hz⟩)

lemma vSteps_subset_wallSet {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)} (he : e ∈ vSteps A) :
    stepSeg e ⊆ wallSet A := by
  obtain ⟨u, hu, heu⟩ := mem_vSteps.mp he
  rw [heu, stepSeg_of_eq_north rfl]
  exact fun z hz => Or.inr (mem_vWallSet.mpr ⟨u, hu, hz⟩)

lemma wallStepFinset_subset_wallSet {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ wallStepFinset A) : stepSeg e ⊆ wallSet A := by
  rcases mem_wallStepFinset.mp he with ⟨u, h, heu⟩ | ⟨u, h, heu⟩
  · rw [heu]; exact hSteps_subset_wallSet (mem_hSteps.mpr ⟨u, h, rfl⟩)
  · rw [heu]; exact vSteps_subset_wallSet (mem_vSteps.mpr ⟨u, h, rfl⟩)

lemma wallSet_subset_wallStepFinset (A : Finset (ℤ × ℤ)) {z : ℂ} (hz : z ∈ wallSet A) :
    ∃ e ∈ wallStepFinset A, z ∈ stepSeg e := by
  rcases hz with hz | hz
  · obtain ⟨u, hu, hzu⟩ := mem_hWallSet.mp hz
    refine ⟨(u, (u.1 + 1, u.2)), ?_, ?_⟩
    · rw [wallStepFinset]
      exact Finset.mem_union_left _ (mem_hSteps.mpr ⟨u, hu, rfl⟩)
    · rw [stepSeg_of_eq_east rfl]; exact hzu
  · obtain ⟨u, hu, hzu⟩ := mem_vWallSet.mp hz
    refine ⟨(u, (u.1, u.2 + 1)), ?_, ?_⟩
    · rw [wallStepFinset]
      exact Finset.mem_union_right _ (mem_vSteps.mpr ⟨u, hu, rfl⟩)
    · rw [stepSeg_of_eq_north rfl]; exact hzu

/-! ## Darts versus segments -/

lemma adjSeg_east_wg (u : ℤ × ℤ) : adjSeg u (u.1 + 1, u.2) = hSeg u := by
  have hsub : (lpt (u.1 + 1, u.2) - lpt u : ℂ) = 1 := by apply Complex.ext <;> simp [lpt]
  rw [adjSeg, segment_eq_image' ℝ]
  ext z
  simp only [Set.mem_image, Set.mem_Icc, mem_hSeg]
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    rw [show (lpt u + θ • (lpt (u.1 + 1, u.2) - lpt u) : ℂ) = lpt u + θ by rw [hsub]; simp]
    exact ⟨by simp, by simp; linarith, by simp; linarith⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨z.re - (u.1 : ℝ), ⟨by simp; linarith, by simp; linarith⟩, ?_⟩
    rw [show (lpt u + (z.re - (u.1 : ℝ)) • (lpt (u.1 + 1, u.2) - lpt u) : ℂ) =
      lpt u + (z.re - (u.1 : ℝ)) by rw [hsub]; simp]
    apply Complex.ext <;> simp [lpt] <;> linarith

lemma adjSeg_north_wg (u : ℤ × ℤ) : adjSeg u (u.1, u.2 + 1) = vSeg u := by
  have hsub : (lpt (u.1, u.2 + 1) - lpt u : ℂ) = Complex.I := by
    apply Complex.ext <;> simp [lpt]
  rw [adjSeg, segment_eq_image' ℝ]
  ext z
  simp only [Set.mem_image, Set.mem_Icc, mem_vSeg]
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    rw [show (lpt u + θ • (lpt (u.1, u.2 + 1) - lpt u) : ℂ) = lpt u + θ * Complex.I by
      rw [hsub]; simp]
    exact ⟨by simp, by simp; linarith, by simp; linarith⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨z.im - (u.2 : ℝ), ⟨by simp; linarith, by simp; linarith⟩, ?_⟩
    rw [show (lpt u + (z.im - (u.2 : ℝ)) • (lpt (u.1, u.2 + 1) - lpt u) : ℂ) =
      lpt u + (z.im - (u.2 : ℝ)) * Complex.I by rw [hsub]; simp]
    apply Complex.ext <;> simp [lpt] <;> linarith

lemma adjSeg_comm (a b : ℤ × ℤ) : adjSeg a b = adjSeg b a := by
  rw [adjSeg, adjSeg, segment_symm]

lemma adjSeg_stepSeg_of_mem_wallStepFinset {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ wallStepFinset A) : adjSeg e.1 e.2 = stepSeg e := by
  rcases mem_wallStepFinset.mp he with ⟨u, h, heu⟩ | ⟨u, h, heu⟩
  · rw [heu]; rw [stepSeg_of_eq_east rfl, adjSeg_east_wg]
  · rw [heu]; rw [stepSeg_of_eq_north rfl, adjSeg_north_wg]

lemma wallDarts_adjSeg_subset {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ wallDarts A) : adjSeg e.1 e.2 ⊆ wallSet A := by
  rcases mem_wallDarts.mp he with he | he
  · rw [adjSeg_stepSeg_of_mem_wallStepFinset he]
    exact wallStepFinset_subset_wallSet he
  · have h := adjSeg_stepSeg_of_mem_wallStepFinset he
    have h2 : e.swap = (e.2, e.1) := rfl
    rw [h2] at h
    rw [adjSeg_comm, h]
    exact wallStepFinset_subset_wallSet he

/-! ## The wall graph -/

lemma isUnitAdj_of_isUnitStep {e : (ℤ × ℤ) × (ℤ × ℤ)} (h : IsUnitStep e) : IsUnitAdj e.1 e.2 := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))

lemma isUnitAdj_of_isUnitStep_swap {e : (ℤ × ℤ) × (ℤ × ℤ)} (h : IsUnitStep e.swap) :
    IsUnitAdj e.1 e.2 := by
  rcases h with h | h
  · refine Or.inr (Or.inl ?_)
    simp only [Prod.swap] at h
    have h1 : e.1.1 = e.2.1 + 1 := by simpa using congrArg (fun p : ℤ × ℤ => p.1) h
    have h2 : e.1.2 = e.2.2 := by simpa using congrArg (fun p : ℤ × ℤ => p.2) h
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst, Prod.snd] <;> omega
  · refine Or.inr (Or.inr (Or.inr ?_))
    simp only [Prod.swap] at h
    have h1 : e.1.1 = e.2.1 := by simpa using congrArg (fun p : ℤ × ℤ => p.1) h
    have h2 : e.1.2 = e.2.2 + 1 := by simpa using congrArg (fun p : ℤ × ℤ => p.2) h
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst, Prod.snd] <;> omega

lemma wallDarts_isUnitAdj {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ wallDarts A) : IsUnitAdj e.1 e.2 := by
  rcases mem_wallDarts.mp he with he | he
  · exact isUnitAdj_of_isUnitStep (wallStepFinset_unitStep he)
  · exact isUnitAdj_of_isUnitStep_swap (wallStepFinset_unitStep he)

/-- The wall graph of `A`. -/
noncomputable def wallDartGraph (A : Finset (ℤ × ℤ)) : DartGraph (ℤ × ℤ) where
  D := wallDarts A
  symm := by
    intro e he
    rw [mem_wallDarts] at he ⊢
    rcases he with he | he
    · exact Or.inr (by rwa [Prod.swap_swap])
    · exact Or.inl he
  noLoop := by
    intro e he h
    rw [mem_wallDarts] at he
    rcases he with he | he
    · rcases mem_wallStepFinset.mp he with ⟨u, hu, hfu⟩ | ⟨u, hu, hfu⟩
      · rw [hfu] at h
        have h1 : u.1 = u.1 + 1 := by simpa using congrArg (fun p : ℤ × ℤ => p.1) h
        omega
      · rw [hfu] at h
        have h1 : u.2 = u.2 + 1 := by simpa using congrArg (fun p : ℤ × ℤ => p.2) h
        omega
    · rcases mem_wallStepFinset.mp he with ⟨u, hu, hfu⟩ | ⟨u, hu, hfu⟩
      · have h' : e.swap.1 = e.swap.2 := h.symm
        rw [hfu] at h'
        have h1 : u.1 = u.1 + 1 := by simpa using congrArg (fun p : ℤ × ℤ => p.1) h'
        omega
      · have h' : e.swap.1 = e.swap.2 := h.symm
        rw [hfu] at h'
        have h1 : u.2 = u.2 + 1 := by simpa using congrArg (fun p : ℤ × ℤ => p.2) h'
        omega

end Work.HornSC.CellBoundaryJordan
