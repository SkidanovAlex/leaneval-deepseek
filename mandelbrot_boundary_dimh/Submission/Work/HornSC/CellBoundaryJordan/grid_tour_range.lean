import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_basic

/-!
# The range of the polygonal tour

`tourOn u k` maps `[0,1]` onto the closed polygonal curve `cycleSet k u = ⋃ i < k, adjSeg (u i) (u (i+1))`,
and the periodic tour `tour u k` maps `ℝ` into it.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

lemma mem_cycleSet {k : ℕ} {u : ℕ → ℤ × ℤ} {z : ℂ} :
    z ∈ cycleSet k u ↔ ∃ i : ℕ, i < k ∧ z ∈ adjSeg (u i) (u (i + 1)) := by
  constructor
  · intro hz
    rw [cycleSet, Set.mem_iUnion] at hz
    obtain ⟨i, hz⟩ := hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨hi, hz⟩ := hz
    exact ⟨i, hi, hz⟩
  · rintro ⟨i, hi, hz⟩
    rw [cycleSet, Set.mem_iUnion]
    exact ⟨i, Set.mem_iUnion.mpr ⟨hi, hz⟩⟩

lemma edgeIdx_le {k : ℕ} {t : ℝ} (ht : t ≤ 1) : edgeIdx k t ≤ k := by
  rw [edgeIdx]
  have h1 : ((k : ℝ) * t) ≤ ((k : ℝ)) := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  calc ⌊(k : ℝ) * t⌋₊ ≤ ⌊(k : ℝ)⌋₊ := Nat.floor_mono h1
    _ = k := Nat.floor_natCast k

lemma edgeIdx_lt {k : ℕ} (hk : 0 < k) {t : ℝ} (h0 : 0 ≤ t) (ht : t < 1) :
    edgeIdx k t < k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : (0 : ℝ) ≤ (k : ℝ) * t := by positivity
  have hlt : (k : ℝ) * t < (k : ℝ) := by nlinarith
  have h1 : ((⌊(k : ℝ) * t⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) * t := Nat.floor_le hx
  rw [edgeIdx]
  have h2 : ((⌊(k : ℝ) * t⌋₊ : ℕ) : ℝ) < (k : ℝ) := lt_of_le_of_lt h1 hlt
  exact_mod_cast h2

lemma tourOn_mem_cycleSet {k : ℕ} (hk : 0 < k) (u : ℕ → ℤ × ℤ) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : tourOn u k t ∈ cycleSet k u := by
  rcases eq_or_lt_of_le h1 with h | h
  · subst h
    rw [tourOn_one]
    refine mem_cycleSet.mpr ⟨k - 1, by omega, ?_⟩
    rw [adjSeg, show k - 1 + 1 = k by omega]
    exact right_mem_segment ℝ _ _
  · have hjlt : edgeIdx k t < k := edgeIdx_lt hk h0 h
    have hge : (edgeIdx k t : ℝ) ≤ (k : ℝ) * t := by
      rw [edgeIdx]
      exact Nat.floor_le (show (0 : ℝ) ≤ (k : ℝ) * t by positivity)
    have hle : (k : ℝ) * t ≤ (edgeIdx k t : ℝ) + 1 := by
      rw [edgeIdx]
      exact le_of_lt (Nat.lt_floor_add_one ((k : ℝ) * t))
    rw [tourOn_affine hjlt hge hle]
    refine mem_cycleSet.mpr ⟨edgeIdx k t, hjlt, ?_⟩
    rw [adjSeg, segment_eq_image']
    exact ⟨(k : ℝ) * t - (edgeIdx k t : ℝ), ⟨by linarith, by linarith⟩, rfl⟩

lemma cycleSet_subset_tourOn_range {k : ℕ} (hk : 0 < k) (u : ℕ → ℤ × ℤ) :
    cycleSet k u ⊆ tourOn u k '' Set.Icc (0 : ℝ) 1 := by
  intro z hz
  rw [mem_cycleSet] at hz
  obtain ⟨i, hi, hz⟩ := hz
  rw [adjSeg, segment_eq_image'] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨(i + θ) / k, ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (add_nonneg (by positivity) hθ.1) hk'.le
  · rw [div_le_one hk']
    have hi' : ((i : ℝ) + 1) ≤ (k : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hi
    linarith [hθ.2]
  · have hkt : (k : ℝ) * ((i + θ) / k) = (i : ℝ) + θ := by
      field_simp
    rw [tourOn_affine (u := u) (k := k) (j := i) (by omega)
      (by rw [hkt]; linarith [hθ.1]) (by rw [hkt]; linarith [hθ.2]), hkt]
    rw [show (i : ℝ) + θ - (i : ℝ) = θ by ring]

lemma tour_add_one (u : ℕ → ℤ × ℤ) (k : ℕ) (t : ℝ) : tour u k (t + 1) = tour u k t := by
  rw [tour, tour, Int.fract_add_one]

lemma tour_eq_tourOn {k : ℕ} (u : ℕ → ℤ × ℤ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    tour u k t = tourOn u k t := by
  rw [tour, Int.fract_eq_self.mpr ⟨h0, h1⟩]

lemma tour_mem_cycleSet {k : ℕ} (hk : 0 < k) (u : ℕ → ℤ × ℤ) (t : ℝ) :
    tour u k t ∈ cycleSet k u := by
  rw [tour]
  exact tourOn_mem_cycleSet hk u (Int.fract_nonneg t) (le_of_lt (Int.fract_lt_one t))

end Work.HornSC.CellBoundaryJordan
