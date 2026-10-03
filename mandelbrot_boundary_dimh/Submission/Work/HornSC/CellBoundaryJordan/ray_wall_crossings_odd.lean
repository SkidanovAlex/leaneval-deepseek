import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.RayDefs
import Submission.Work.HornSC.CellBoundaryJordan.ray_crossing_parity
import Submission.Work.HornSC.CellBoundaryJordan.ball_subset_cellUnion_of_notMem_wallSet
import Submission.Work.HornSC.CellBoundaryJordan.cellUnion_flip_of_mem_wallSet
import Submission.Work.HornSC.CellBoundaryJordan.rayPt_eventually_notMem_cellUnion

/-!
# Odd crossing number of a generic ray with the wall set of a finite union of cells

A ray issued from an interior point of `cellUnion A` in a direction with positive real and
imaginary parts, that never meets a lattice point, meets the wall set `wallSet A` in an odd
number of points.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- A continuous curve that passes through an open set stays in it for a while. -/
lemma exists_delta_of_open {γ : ℝ → ℂ} (hγ : Continuous γ) {U : Set ℂ} (hU : IsOpen U)
    {t : ℝ} (ht : γ t ∈ U) : ∃ δ > 0, ∀ s, |s - t| < δ → γ s ∈ U := by
  have hopen : IsOpen (γ ⁻¹' U) := hU.preimage hγ
  obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopen t ht
  exact ⟨δ, hδpos, fun s hs => hδ (show s ∈ Metric.ball t δ from by
    rw [Metric.mem_ball, Real.dist_eq]; exact hs)⟩

theorem ray_wall_crossings_odd (A : Finset (ℤ × ℤ)) {a : ℂ} {ε : ℝ} (hε : 0 < ε)
    (ha : a ∈ interior (cellUnion A))
    (hgen : ∀ t : ℝ, 0 < t → ∀ m n : ℤ,
      a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ≠ (m : ℂ) + (n : ℂ) * Complex.I)
    (hfin : {t : ℝ | 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈ wallSet A}.Finite) :
    Odd hfin.toFinset.card := by
  classical
  set S := hfin.toFinset with hSdef
  have hSmem : ∀ t : ℝ, t ∈ S ↔ 0 < t ∧ rayPt a ε t ∈ wallSet A := by
    intro t
    simp [hSdef, Set.Finite.mem_toFinset, rayPt, rayDir]
  have hSpos : ∀ t ∈ S, 0 < t := fun t ht => ((hSmem t).mp ht).1
  obtain ⟨Tesc, hTesc⟩ := rayPt_eventually_notMem_cellUnion A a ε
  set T : ℝ := max Tesc ((∑ s ∈ S, s) + 1) with hTdef
  have hTS : ∀ t ∈ S, 0 < t ∧ t < T := by
    intro t ht
    refine ⟨hSpos t ht, ?_⟩
    have h1 : t ≤ ∑ s ∈ S, s :=
      Finset.single_le_sum (fun s hs => le_of_lt (hSpos s hs)) ht
    rw [hTdef]
    have h2 : (∑ s ∈ S, s) + 1 ≤ max Tesc ((∑ s ∈ S, s) + 1) := le_max_right _ _
    linarith
  have hTpos : 0 < T := by
    rw [hTdef]
    have h1 : 0 ≤ ∑ s ∈ S, s := Finset.sum_nonneg (fun s hs => le_of_lt (hSpos s hs))
    have h2 : (∑ s ∈ S, s) + 1 ≤ max Tesc ((∑ s ∈ S, s) + 1) := le_max_right _ _
    linarith
  have hTescT : Tesc ≤ T := by rw [hTdef]; exact le_max_left _ _
  have hγcont : Continuous (fun s : ℝ => rayPt a ε s) := by
    simp only [rayPt]; fun_prop
  have hloc : ∀ t ∈ Set.Icc (0 : ℝ) T, t ∉ S → ∃ δ > 0, ∀ s, |s - t| < δ →
      ((rayPt a ε s ∈ cellUnion A) ↔ (rayPt a ε t ∈ cellUnion A)) := by
    intro t ht htS
    have hgood : rayPt a ε t ∈ interior (cellUnion A) ∨ rayPt a ε t ∉ cellUnion A := by
      rcases eq_or_lt_of_le ht.1 with h0 | htpos
      · left
        rw [← h0]
        simpa [rayPt, rayDir] using ha
      · by_cases hineq : rayPt a ε t ∈ cellUnion A
        · left
          have hnotwall : rayPt a ε t ∉ wallSet A := by
            intro hw
            exact htS ((hSmem t).mpr ⟨htpos, hw⟩)
          obtain ⟨r, hr, hball⟩ := ball_subset_cellUnion_of_notMem_wallSet hineq hnotwall
          have hball' : Metric.ball (rayPt a ε t) r ⊆ cellUnion A := fun w hw =>
            hball w (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
          exact interior_maximal hball' Metric.isOpen_ball (Metric.mem_ball_self hr)
        · right; exact hineq
    rcases hgood with hint | hout
    · obtain ⟨δ, hδpos, hδ⟩ := exists_delta_of_open hγcont isOpen_interior hint
      refine ⟨δ, hδpos, fun s hs =>
        ⟨fun _ => interior_subset hint, fun _ => interior_subset (hδ s hs)⟩⟩
    · obtain ⟨δ, hδpos, hδ⟩ :=
        exists_delta_of_open hγcont (isClosed_cellUnion A).isOpen_compl hout
      refine ⟨δ, hδpos, fun s hs => ⟨fun hc => absurd hc (hδ s hs), fun hc => absurd hc hout⟩⟩
  have hflip : ∀ t ∈ S, ∃ δ > 0, ∀ s, 0 < s → s < δ →
      ((rayPt a ε (t + s) ∈ cellUnion A) ↔ ¬ (rayPt a ε (t - s) ∈ cellUnion A)) := by
    intro t htS
    have htpos : 0 < t := ((hSmem t).mp htS).1
    have hzw : rayPt a ε t ∈ wallSet A := ((hSmem t).mp htS).2
    have hnl : NonLattice (rayPt a ε t) := by
      intro m n hc
      exact hgen t htpos m n (by simpa [rayPt, rayDir] using hc)
    have hvr : 0 < (rayDir ε).re := by simp [rayDir]
    have hvi : 0 < (rayDir ε).im := by simpa [rayDir] using hε
    obtain ⟨δ, hδpos, hδ⟩ := cellUnion_flip_of_mem_wallSet hzw hnl hvr hvi
    refine ⟨δ, hδpos, fun s hs0 hsδ => ?_⟩
    have e1 : rayPt a ε (t + s) = rayPt a ε t + (s : ℂ) * rayDir ε := by
      simp only [rayPt, Complex.ofReal_add]; ring
    have e2 : rayPt a ε (t - s) = rayPt a ε t - (s : ℂ) * rayDir ε := by
      simp only [rayPt, Complex.ofReal_sub]; ring
    rw [e1, e2]
    exact hδ s hs0 hsδ
  have hP0 : rayPt a ε 0 ∈ cellUnion A := by
    simpa [rayPt, rayDir] using interior_subset ha
  have hPT : ¬ (rayPt a ε T ∈ cellUnion A) := hTesc T hTescT
  have hodd : Odd S.card := odd_card_of_flip hTpos hTS hloc hflip hP0 hPT
  exact hSdef ▸ hodd

end Work.HornSC.CellBoundaryJordan
