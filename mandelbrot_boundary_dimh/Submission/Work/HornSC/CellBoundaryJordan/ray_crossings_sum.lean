import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.GridCycleAux
import Submission.Work.HornSC.CellBoundaryJordan.WallGraph
import Submission.Work.HornSC.CellBoundaryJordan.RayDefs

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- A unit grid segment meets the ray `t ↦ rayPt a ε t` (with `ε > 0`) in at most one parameter. -/
lemma rayPt_adjSeg_inj {a : ℂ} {ε : ℝ} (hε : 0 < ε) {p q : ℤ × ℤ} (h : IsUnitAdj p q)
    {t₁ t₂ : ℝ} (h1 : rayPt a ε t₁ ∈ adjSeg p q) (h2 : rayPt a ε t₂ ∈ adjSeg p q) :
    t₁ = t₂ := by
  rcases h with h | h | h | h
  · rw [h, adjSeg_east_wg] at h1 h2
    rw [mem_hSeg] at h1 h2
    have e1 := h1.1
    have e2 := h2.1
    rw [rayPt_im] at e1 e2
    have hε' : ε * t₁ = ε * t₂ := by linarith
    exact mul_left_cancel₀ (ne_of_gt hε) hε'
  · rw [h, adjSeg_west] at h1 h2
    rw [mem_hSeg] at h1 h2
    have e1 := h1.1
    have e2 := h2.1
    rw [rayPt_im] at e1 e2
    have hε' : ε * t₁ = ε * t₂ := by linarith
    exact mul_left_cancel₀ (ne_of_gt hε) hε'
  · rw [h, adjSeg_north_wg] at h1 h2
    rw [mem_vSeg] at h1 h2
    have e1 := h1.1
    have e2 := h2.1
    rw [rayPt_re] at e1 e2
    linarith
  · rw [h, adjSeg_south] at h1 h2
    rw [mem_vSeg] at h1 h2
    have e1 := h1.1
    have e2 := h2.1
    rw [rayPt_re] at e1 e2
    linarith

theorem ray_crossings_sum (A : Finset (ℤ × ℤ)) {m : ℕ} {k : Fin m → ℕ} {u : Fin m → ℕ → ℤ × ℤ}
    (hstep : ∀ i, ∀ j, j < k i → IsUnitAdj (u i j) (u i (j + 1)))
    (hdisj : ∀ i i', i ≠ i' → ∀ j j', j < k i → j' < k i' →
      adjSeg (u i j) (u i (j + 1)) ≠ adjSeg (u i' j') (u i' (j' + 1)))
    (hunion : (⋃ i, ⋃ j ∈ {j : ℕ | j < k i}, adjSeg (u i j) (u i (j + 1))) = wallSet A)
    {a : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hgen : ∀ t : ℝ, 0 < t → ∀ m n : ℤ,
      a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ≠ (m : ℂ) + (n : ℂ) * Complex.I) :
    ∃ (S : Finset ℝ) (T : Fin m → Finset ℝ),
      (∀ t : ℝ, t ∈ S ↔ 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈ wallSet A) ∧
      (∀ i : Fin m, ∀ t : ℝ, t ∈ T i ↔ 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈
        ⋃ j ∈ {j : ℕ | j < k i}, adjSeg (u i j) (u i (j + 1))) ∧
      S.card = ∑ i, (T i).card ∧
      (∀ t : ℝ, t ∈ S ↔ ∃ i : Fin m, t ∈ T i) := by
  classical
  -- the ray never meets a lattice point for `t > 0`
  have hNL : ∀ t : ℝ, 0 < t → NonLattice (rayPt a ε t) := by
    intro t ht p q
    simpa only [rayPt, rayDir] using hgen t ht p q
  -- finiteness of the per-segment parameter sets
  have hSegFin : ∀ (p q : ℤ × ℤ), IsUnitAdj p q →
      ({t : ℝ | rayPt a ε t ∈ adjSeg p q} : Set ℝ).Finite :=
    fun p q hpq => Set.Subsingleton.finite (fun t₁ ht₁ t₂ ht₂ => rayPt_adjSeg_inj hε hpq ht₁ ht₂)
  -- finiteness of the per-`i` parameter sets
  have hTfin : ∀ i : Fin m,
      (⋃ j ∈ {j : ℕ | j < k i}, {t : ℝ | rayPt a ε t ∈ adjSeg (u i j) (u i (j + 1))}).Finite := by
    intro i
    refine Set.Finite.biUnion (Set.finite_Iio (k i)) ?_
    intro j hj
    exact hSegFin (u i j) (u i (j + 1)) (hstep i j hj)
  have hTfin2 : ∀ i : Fin m,
      ({t : ℝ | 0 < t ∧ rayPt a ε t ∈
        (⋃ j ∈ {j : ℕ | j < k i}, adjSeg (u i j) (u i (j + 1)))} : Set ℝ).Finite := by
    intro i
    refine (hTfin i).subset ?_
    rintro t ⟨htpos, htmem⟩
    rw [Set.mem_iUnion] at htmem
    obtain ⟨j, htmem⟩ := htmem
    rw [Set.mem_iUnion] at htmem
    obtain ⟨hj, hjmem⟩ := htmem
    exact Set.mem_biUnion hj hjmem
  let T : Fin m → Finset ℝ := fun i => (hTfin2 i).toFinset
  have hTmem : ∀ (i : Fin m) (t : ℝ), t ∈ T i ↔
      0 < t ∧ rayPt a ε t ∈ (⋃ j ∈ {j : ℕ | j < k i}, adjSeg (u i j) (u i (j + 1))) := by
    intro i t
    exact Set.Finite.mem_toFinset (hTfin2 i)
  let S : Finset ℝ := Finset.univ.biUnion T
  have hSmem : ∀ t : ℝ, t ∈ S ↔ ∃ i : Fin m, t ∈ T i := by
    intro t
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and]
  have hdisjT : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) T := by
    intro i _ i' _ hne
    change Disjoint (T i) (T i')
    rw [Finset.disjoint_iff_ne]
    intro r hr r' hr' hrr'
    obtain ⟨hrpos, hrmem⟩ := (hTmem i r).mp hr
    obtain ⟨_, hr'mem⟩ := (hTmem i' r').mp hr'
    rw [Set.mem_iUnion] at hrmem
    obtain ⟨j, hrmem⟩ := hrmem
    rw [Set.mem_iUnion] at hrmem
    obtain ⟨hj, hjmem⟩ := hrmem
    rw [Set.mem_iUnion] at hr'mem
    obtain ⟨j', hr'mem⟩ := hr'mem
    rw [Set.mem_iUnion] at hr'mem
    obtain ⟨hj', hj'mem⟩ := hr'mem
    rw [← hrr'] at hj'mem
    exact hdisj i i' hne j j' hj hj'
      (adjSeg_eq_of_mem_of_not_lattice (hstep i j hj) (hstep i' j' hj') hjmem hj'mem
        (fun p => (hNL r hrpos).notMem_lpt p))
  refine ⟨S, T, ?_, ?_, ?_, ?_⟩
  · intro t
    have h : (t ∈ S) ↔ 0 < t ∧ rayPt a ε t ∈ wallSet A := by
      rw [hSmem t]
      constructor
      · rintro ⟨i, hi⟩
        obtain ⟨hpos, hmem⟩ := (hTmem i t).mp hi
        exact ⟨hpos, hunion ▸ Set.mem_iUnion.mpr ⟨i, hmem⟩⟩
      · rintro ⟨hpos, hmem⟩
        rw [← hunion] at hmem
        rw [Set.mem_iUnion] at hmem
        obtain ⟨i, hmem⟩ := hmem
        exact ⟨i, (hTmem i t).mpr ⟨hpos, hmem⟩⟩
    simpa only [rayPt, rayDir] using h
  · intro i t
    have h := hTmem i t
    simpa only [rayPt, rayDir] using h
  · rw [Finset.card_biUnion hdisjT]
  · intro t
    exact hSmem t

end Work.HornSC.CellBoundaryJordan
