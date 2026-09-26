import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Defs
import Submission.Work.BoxShrink.PinchOff.IB.Components

namespace Work.Peel

open Set Metric

noncomputable section

/-- The period lattice `2π(ℤ + iℤ)` of the parameter plane is closed under negation. -/
theorem periodLattice_neg {ν : ℂ} (hν : ν ∈ Work.BoxShrink.PinchOff.periodLattice) :
    -ν ∈ Work.BoxShrink.PinchOff.periodLattice := by
  rw [Work.BoxShrink.PinchOff.mem_periodLattice] at hν ⊢
  obtain ⟨a, b, rfl⟩ := hν
  refine ⟨-a, -b, ?_⟩
  apply Complex.ext
  · simp [Work.BoxShrink.PinchOff.periodPt]
  · simp [Work.BoxShrink.PinchOff.periodPt]

/-- **Uniform separation of a compact set from its nonzero period-translates.**

If `K ⊆ ℂ` is compact and no two points of `K` differ by a nonzero element of the period lattice,
then `K + ν` stays at a positive distance from `K`, uniformly over all nonzero lattice elements
`ν`.  The proof splits the lattice into a bounded part (finitely many points) and an unbounded
part, where the distance is bounded below by `‖ν‖` minus the diameter of `K`. -/
theorem exists_gap_of_isCompact
    {K : Set ℂ} (hKc : IsCompact K)
    (hsep : ∀ u ∈ K, ∀ v ∈ K, ∀ ν ∈ Work.BoxShrink.PinchOff.periodLattice, u - v = ν → ν = 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ ν ∈ Work.BoxShrink.PinchOff.periodLattice, ν ≠ 0 →
      ∀ u ∈ K, ∀ v ∈ K, η ≤ dist (u + ν) v := by
  classical
  -- a bound for the diameter of `K`
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hKc.isBounded
  -- the lattice elements that are not "far away"
  set B : Set ℂ := {ν ∈ Work.BoxShrink.PinchOff.periodLattice | ‖ν‖ ≤ C + 1} with hBdef
  have hBfin : B.Finite := by
    rw [hBdef]
    exact Work.BoxShrink.PinchOff.finite_periodLattice_ball (C + 1)
  -- for a single nonzero lattice element the gap over `K × K` is positive
  have key : ∀ ν : ℂ, ν ∈ B → ν ≠ 0 →
      ∃ η' : ℝ, 0 < η' ∧ ∀ p ∈ K ×ˢ K, η' ≤ dist (p.1 + ν) p.2 := by
    intro ν hνB hν0
    obtain ⟨η', hη'pos, hη'le⟩ := (hKc.prod hKc).exists_forall_le'
      (f := fun p : ℂ × ℂ => dist (p.1 + ν) p.2) (a := 0)
      (by
        apply Continuous.continuousOn
        exact (continuous_fst.add continuous_const).dist continuous_snd)
      (by
        intro p hp
        rw [Set.mem_prod] at hp
        rw [dist_pos]
        intro hcon
        have hνΛ : ν ∈ Work.BoxShrink.PinchOff.periodLattice := (hBdef ▸ hνB).1
        have hneg : -ν ∈ Work.BoxShrink.PinchOff.periodLattice := periodLattice_neg hνΛ
        have hdiff : p.1 - p.2 = -ν := by rw [← hcon]; ring
        have hzero := hsep p.1 hp.1 p.2 hp.2 (-ν) hneg hdiff
        exact hν0 (neg_eq_zero.mp hzero))
    exact ⟨η', hη'pos, hη'le⟩
  -- package the gaps into a function
  let m : ℂ → ℝ := fun ν =>
    if h : ν ∈ B ∧ ν ≠ 0 then Classical.choose (key ν h.1 h.2) else 1
  have hm_pos : ∀ ν, ν ∈ B → ν ≠ 0 → 0 < m ν := by
    intro ν hνB hν0
    have h : ν ∈ B ∧ ν ≠ 0 := ⟨hνB, hν0⟩
    simp only [m]
    rw [dif_pos h]
    exact (Classical.choose_spec (key ν h.1 h.2)).1
  have hm_bound : ∀ ν, ν ∈ B → ν ≠ 0 →
      ∀ u ∈ K, ∀ v ∈ K, m ν ≤ dist (u + ν) v := by
    intro ν hνB hν0 u hu v hv
    have h : ν ∈ B ∧ ν ≠ 0 := ⟨hνB, hν0⟩
    simp only [m]
    rw [dif_pos h]
    exact (Classical.choose_spec (key ν h.1 h.2)).2 (u, v) (Set.mem_prod.mpr ⟨hu, hv⟩)
  -- the minimum over the finitely many bounded lattice elements (and `1`)
  let t : Finset ℂ := hBfin.toFinset.filter (fun ν => ν ≠ 0)
  let s : Finset ℝ := insert (1 : ℝ) (t.image m)
  have hsne : s.Nonempty := ⟨1, Finset.mem_insert_self 1 (t.image m)⟩
  refine ⟨s.min' hsne, ?_, ?_⟩
  · -- positivity
    have hmem : s.min' hsne ∈ s := Finset.min'_mem s hsne
    rcases Finset.mem_insert.mp hmem with h1 | him
    · rw [h1]; exact one_pos
    · rw [Finset.mem_image] at him
      obtain ⟨ν, hνt, hνeq⟩ := him
      rw [Finset.mem_filter] at hνt
      obtain ⟨hνfin, hν0⟩ := hνt
      have hνB : ν ∈ B := (hBfin.mem_toFinset).mp hνfin
      have hpos := hm_pos ν hνB hν0
      rw [hνeq] at hpos
      exact hpos
  · intro ν hνΛ hν0 u hu v hv
    by_cases hcase : ‖ν‖ ≤ C + 1
    · -- bounded lattice element: use the finite minimum
      have hνB : ν ∈ B := by rw [hBdef]; exact ⟨hνΛ, hcase⟩
      have hle : s.min' hsne ≤ m ν := by
        apply Finset.min'_le
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨ν, ?_, rfl⟩
        rw [Finset.mem_filter]
        exact ⟨(hBfin.mem_toFinset).mpr hνB, hν0⟩
      have hb := hm_bound ν hνB hν0 u hu v hv
      linarith
    · -- far away: the distance is at least one
      push_neg at hcase
      have hle1 : s.min' hsne ≤ 1 := Finset.min'_le s 1 (Finset.mem_insert_self 1 (t.image m))
      have hCuv : dist u v ≤ C := hC hu hv
      have hdist : 1 ≤ dist (u + ν) v := by
        rw [dist_eq_norm]
        have hsub : u + ν - v = ν + (u - v) := by ring
        rw [hsub]
        have h1 : ‖ν‖ - ‖u - v‖ ≤ ‖ν + (u - v)‖ := norm_sub_le_norm_add ν (u - v)
        have h2 : ‖u - v‖ = dist u v := by rw [dist_eq_norm]
        rw [h2] at h1
        linarith
      linarith

theorem exists_gap_periodLattice_image
    (f : C(Metric.closedBall (0 : ℂ) 1, ℂ))
    (hsep : ∀ u, u ∈ ⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0 : ℂ) 1) →
      ∀ v, v ∈ ⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0 : ℂ) 1) →
      ∀ ν, ν ∈ Work.BoxShrink.PinchOff.periodLattice → u - v = ν → ν = 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ ν ∈ Work.BoxShrink.PinchOff.periodLattice, ν ≠ 0 →
      ∀ u, u ∈ ⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0 : ℂ) 1) →
      ∀ v, v ∈ ⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0 : ℂ) 1) →
      η ≤ dist (u + ν) v := by
  have hpre : (Subtype.val ⁻¹' (Metric.closedBall (0 : ℂ) 1) : Set ↥(Metric.closedBall (0 : ℂ) 1))
      = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact x.2
  have hKc : IsCompact (⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0 : ℂ) 1)) := by
    have hrange : ⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0 : ℂ) 1) = Set.range ⇑f := by
      rw [hpre, Set.image_univ]
    rw [hrange]
    haveI : CompactSpace ↥(Metric.closedBall (0 : ℂ) 1) :=
      isCompact_iff_compactSpace.mp (ProperSpace.isCompact_closedBall (0 : ℂ) 1)
    exact isCompact_range f.continuous
  exact exists_gap_of_isCompact hKc hsep

end

end Work.Peel
