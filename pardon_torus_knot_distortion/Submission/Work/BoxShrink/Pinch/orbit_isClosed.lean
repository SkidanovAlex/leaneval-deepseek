import Mathlib
import Submission.Work.BoxShrink.Pinch.PlanePathDefs

/-!
# The orbit of the trace of a periodic curve is closed

The trace `J` of a continuous `2π`-periodic curve `γ : ℝ → ℝ²` is compact (it is the image of
`[0, 2π]` under `γ`).  Hence its orbit

`orbit J = ⋃_{k ∈ ℤ²} (J + 2πk)`

is closed: spatially it is the preimage of the compact (hence closed) subset `Q '' J` of the
torus `T² = (ℝ/2πℤ)²` under the quotient map `Q : ℝ² → T²`, which is continuous.

The proof below implements exactly this: `Q` identifies two points of `ℝ²` precisely when they
differ by a period `periodShift k`, so `orbit J = Q ⁻¹' (Q '' J)`, and `Q '' J` is compact.
-/

namespace Work.BoxShrink.Pinch

open Work.TorusCover

noncomputable section

/-- The quotient map `ℝ² → (ℝ/2πℤ)²` onto the standard torus, in coordinates. -/
private def circleProj (p : ℝ × ℝ) : AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi) :=
  ((p.1 : AddCircle (2 * Real.pi)), (p.2 : AddCircle (2 * Real.pi)))

private lemma circleProj_continuous : Continuous circleProj := by
  unfold circleProj
  continuity

/-- `circleProj` identifies exactly the points differing by a period shift `2πk`. -/
private lemma circleProj_eq_iff (p j : ℝ × ℝ) :
    circleProj p = circleProj j ↔ ∃ k : ℤ × ℤ, p = j + periodShift k := by
  constructor
  · intro h
    have h1 : (p.1 : AddCircle (2 * Real.pi)) = (j.1 : AddCircle (2 * Real.pi)) := by
      simpa [circleProj] using congrArg Prod.fst h
    have h2 : (p.2 : AddCircle (2 * Real.pi)) = (j.2 : AddCircle (2 * Real.pi)) := by
      simpa [circleProj] using congrArg Prod.snd h
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
    simp only [circleProj]
    rw [h1, h2]

/-- The trace of a `2π`-periodic curve is the image of `[0, 2π]` under the curve. -/
theorem range_eq_image_Icc_of_periodic {γ : ℝ → ℝ × ℝ}
    (hper : Function.Periodic γ (2 * Real.pi)) :
    Set.range γ = γ '' Set.Icc 0 (2 * Real.pi) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    have h2π : (0:ℝ) < 2 * Real.pi := by positivity
    refine ⟨Int.fract (t / (2 * Real.pi)) * (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
    · exact mul_nonneg (Int.fract_nonneg _) (le_of_lt h2π)
    · exact le_of_lt (by
        simpa using mul_lt_mul_of_pos_right (Int.fract_lt_one (t / (2 * Real.pi))) h2π)
    · have htf : Int.fract (t / (2 * Real.pi)) * (2 * Real.pi) +
            (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) = t := by
        have h2π' : (2 * Real.pi : ℝ) ≠ 0 := by positivity
        calc Int.fract (t / (2 * Real.pi)) * (2 * Real.pi) +
              (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)
            = (Int.fract (t / (2 * Real.pi)) + (⌊t / (2 * Real.pi)⌋ : ℝ)) *
                (2 * Real.pi) := by ring
          _ = (t / (2 * Real.pi)) * (2 * Real.pi) := by rw [Int.fract_add_floor]
          _ = t := by field_simp
      have hn := (hper.int_mul ⌊t / (2 * Real.pi)⌋)
        (Int.fract (t / (2 * Real.pi)) * (2 * Real.pi))
      rw [htf] at hn
      exact hn.symm
  · exact Set.image_subset_range _ _

/-- The orbit of the trace of a continuous `2π`-periodic curve is closed. -/
theorem orbit_range_isClosed {γ : ℝ → ℝ × ℝ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) :
    IsClosed (orbit (Set.range γ)) := by
  have hcomp : IsCompact (Set.range γ) := by
    rw [range_eq_image_Icc_of_periodic hper]
    exact isCompact_Icc.image hcont
  have horbit : orbit (Set.range γ) = circleProj ⁻¹' (circleProj '' Set.range γ) := by
    ext p
    constructor
    · intro hp
      obtain ⟨j, hj, k, hk⟩ := mem_orbit_iff.mp hp
      exact ⟨j, hj, ((circleProj_eq_iff p j).mpr ⟨k, hk⟩).symm⟩
    · intro hp
      obtain ⟨j, hj, hq⟩ := hp
      obtain ⟨k, hk⟩ := (circleProj_eq_iff p j).mp hq.symm
      exact mem_orbit_iff.mpr ⟨j, hj, k, hk⟩
  rw [horbit]
  exact (hcomp.image circleProj_continuous).isClosed.preimage circleProj_continuous

theorem orbit_isClosed {J : Set (ℝ × ℝ)} (hJ : ∃ (γ : ℝ → ℝ × ℝ), Continuous γ ∧
    Function.Periodic γ (2 * Real.pi) ∧ Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧ Set.range γ = J) :
    IsClosed (Work.BoxShrink.Pinch.orbit J) := by
  obtain ⟨γ, hcont, hper, -, hrange⟩ := hJ
  have h := orbit_range_isClosed hcont hper
  rw [hrange] at h
  exact h

end

end Work.BoxShrink.Pinch
