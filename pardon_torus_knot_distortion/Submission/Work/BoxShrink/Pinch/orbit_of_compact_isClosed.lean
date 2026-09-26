import Mathlib
import Submission.Work.BoxShrink.Pinch.PlanePathDefs

namespace Work.BoxShrink.Pinch

set_option linter.unusedVariables false

open Work.TorusCover

noncomputable section

/-- The quotient map `ℝ² → (ℝ/2πℤ)²` onto the standard torus, in coordinates. -/
private def pinchTorusProj (p : ℝ × ℝ) : AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi) :=
  ((p.1 : AddCircle (2 * Real.pi)), (p.2 : AddCircle (2 * Real.pi)))

private lemma pinchTorusProj_continuous : Continuous pinchTorusProj := by
  unfold pinchTorusProj
  continuity

/-- `pinchTorusProj` identifies exactly the points differing by a period shift `2πk`. -/
private lemma pinchTorusProj_eq_iff (p j : ℝ × ℝ) :
    pinchTorusProj p = pinchTorusProj j ↔ ∃ k : ℤ × ℤ, p = j + periodShift k := by
  constructor
  · intro h
    have h1 : (p.1 : AddCircle (2 * Real.pi)) = (j.1 : AddCircle (2 * Real.pi)) := by
      simpa [pinchTorusProj] using congrArg Prod.fst h
    have h2 : (p.2 : AddCircle (2 * Real.pi)) = (j.2 : AddCircle (2 * Real.pi)) := by
      simpa [pinchTorusProj] using congrArg Prod.snd h
    rw [QuotientAddGroup.eq_iff_sub_mem] at h1 h2
    rw [AddSubgroup.mem_zmultiples_iff] at h1 h2
    obtain ⟨n, hn⟩ := h1
    obtain ⟨m, hm⟩ := h2
    refine ⟨(n, m), ?_⟩
    ext
    · simp only [periodShift, Prod.fst_add]
      have : (n : ℝ) * (2 * Real.pi) = p.1 - j.1 := by simpa using hn
      linarith
    · simp only [periodShift, Prod.snd_add]
      have : (m : ℝ) * (2 * Real.pi) = p.2 - j.2 := by simpa using hm
      linarith
  · rintro ⟨k, rfl⟩
    have h1 : ((j + periodShift k).1 : AddCircle (2 * Real.pi)) =
        (j.1 : AddCircle (2 * Real.pi)) := by
      simp only [Prod.fst_add, periodShift]
      rw [show j.1 + (k.1 : ℝ) * (2 * Real.pi) = j.1 + (k.1 : ℤ) • (2 * Real.pi) from by simp]
      rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero, add_zero]
    have h2 : ((j + periodShift k).2 : AddCircle (2 * Real.pi)) =
        (j.2 : AddCircle (2 * Real.pi)) := by
      simp only [Prod.snd_add, periodShift]
      rw [show j.2 + (k.2 : ℝ) * (2 * Real.pi) = j.2 + (k.2 : ℤ) • (2 * Real.pi) from by simp]
      rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero, add_zero]
    simp only [pinchTorusProj]
    rw [h1, h2]

/-- The union of the lattice translates of a set `F` is the preimage under the torus projection of
the image of `F`. -/
theorem iUnion_translate_eq_preimage {F : Set (ℝ × ℝ)} :
    (⋃ k : ℤ × ℤ, (fun p : ℝ × ℝ => p + periodShift k) '' F)
      = pinchTorusProj ⁻¹' (pinchTorusProj '' F) := by
  ext p
  constructor
  · intro hp
    rw [Set.mem_iUnion] at hp
    obtain ⟨k, j, hj, hjk⟩ := hp
    exact ⟨j, hj, ((pinchTorusProj_eq_iff p j).mpr ⟨k, hjk.symm⟩).symm⟩
  · intro hp
    obtain ⟨j, hj, hq⟩ := hp
    obtain ⟨k, hk⟩ := (pinchTorusProj_eq_iff p j).mp hq.symm
    exact Set.mem_iUnion.mpr ⟨k, j, hj, hk.symm⟩

/-- The orbit of a compact set `F ⊆ ℝ²` under the period lattice is closed. -/
theorem orbit_of_compact_isClosed {F : Set (ℝ × ℝ)} (hF : IsCompact F)
    (hdisj : ∀ k k' : ℤ × ℤ, k ≠ k' →
      Disjoint ((fun p : ℝ × ℝ => p + Work.TorusCover.periodShift k) '' F)
        ((fun p : ℝ × ℝ => p + Work.TorusCover.periodShift k') '' F)) :
    IsClosed (⋃ k : ℤ × ℤ, (fun p : ℝ × ℝ => p + Work.TorusCover.periodShift k) '' F) := by
  rw [iUnion_translate_eq_preimage]
  exact ((hF.image pinchTorusProj_continuous).isClosed).preimage pinchTorusProj_continuous

end

end Work.BoxShrink.Pinch
