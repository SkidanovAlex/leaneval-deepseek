import Mathlib
import Submission.Work.ShafarevichKoch.RatCoeff

namespace Work.ShafarevichKoch.Bockstein

/-- In `ℚ/ℤ` the elements killed by `2` are exactly `0` and the class of `1/2`. -/
theorem two_smul_eq_zero_iff (x : Work.ShafarevichKoch.QZ) :
    (2 : ℕ) • x = 0 ↔ x = 0 ∨ x = QuotientAddGroup.mk (1 / 2 : ℚ) := by
  have hnorm : (AddSubgroup.zmultiples (1 : ℚ)).Normal := inferInstance
  -- Apply the criterion to a representative `q` of `x`: doubling corresponds to doubling `q`,
  -- and `q` resp. `q - 1/2` lies in `ℤ` exactly when the class of `q` is `0` resp. the class
  -- of `1/2`.
  have key : ∀ q : ℚ, (QuotientAddGroup.mk (2 * q) : Work.ShafarevichKoch.QZ) = 0 ↔
      (QuotientAddGroup.mk q : Work.ShafarevichKoch.QZ) = 0 ∨
        (QuotientAddGroup.mk q : Work.ShafarevichKoch.QZ) =
          QuotientAddGroup.mk (1 / 2 : ℚ) := by
    intro q
    rw [@QuotientAddGroup.eq_zero_iff ℚ _ (AddSubgroup.zmultiples (1 : ℚ)) hnorm (2 * q),
      @QuotientAddGroup.eq_zero_iff ℚ _ (AddSubgroup.zmultiples (1 : ℚ)) hnorm q,
      @QuotientAddGroup.eq_iff_sub_mem ℚ _ (AddSubgroup.zmultiples (1 : ℚ)) hnorm q (1 / 2)]
    simp only [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul, mul_one]
    constructor
    · -- `2 * q ∈ ℤ`: the witness `n` is even (`q ∈ ℤ`) or odd (`q - 1/2 ∈ ℤ`)
      rintro ⟨n, hn⟩
      rcases Int.even_or_odd n with hev | hod
      · left
        rw [even_iff_exists_two_mul] at hev
        obtain ⟨m, hm⟩ := hev
        have h1 : ((2 * m : ℤ) : ℚ) = 2 * (m : ℚ) := by push_cast; ring
        have h2 : ((n : ℤ) : ℚ) = ((2 * m : ℤ) : ℚ) := by rw [hm]
        rw [h1] at h2
        refine ⟨m, ?_⟩
        exact mul_left_cancel₀ two_ne_zero (by linarith)
      · right
        obtain ⟨m, hm⟩ := hod
        have h1 : ((2 * m + 1 : ℤ) : ℚ) = 2 * (m : ℚ) + 1 := by push_cast; ring
        have h2 : ((n : ℤ) : ℚ) = ((2 * m + 1 : ℤ) : ℚ) := by rw [hm]
        rw [h1] at h2
        refine ⟨m, ?_⟩
        exact mul_left_cancel₀ two_ne_zero (by linarith)
    · -- conversely both cases give an integrality witness for `2 * q`
      rintro (⟨n, hn⟩ | ⟨n, hn⟩)
      · refine ⟨2 * n, ?_⟩
        push_cast
        rw [hn]
      · refine ⟨2 * n + 1, ?_⟩
        push_cast
        rw [hn]
        ring
  refine QuotientAddGroup.induction_on x ?_
  intro q
  have h2 : (2 : ℕ) • (QuotientAddGroup.mk q : Work.ShafarevichKoch.QZ) =
      QuotientAddGroup.mk (2 * q) := by
    have h : (2 : ℕ) • (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) q) =
        QuotientAddGroup.mk (2 * q) := by
      rw [← map_nsmul]
      simp [nsmul_eq_mul]
    simpa using h
  rw [h2]
  exact key q

end Work.ShafarevichKoch.Bockstein
