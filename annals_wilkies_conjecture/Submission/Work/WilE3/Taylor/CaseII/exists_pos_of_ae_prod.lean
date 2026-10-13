import Mathlib

open MeasureTheory

namespace Work.WilE3.Taylor.CaseII

/-- From an almost-everywhere property `P` on `(Fin k → ℝ) × ℝ` one can extract a point
`(v, d)` with `d > 0` at which `P` holds: the set of points with positive second coordinate
is open (hence positive measure), while the set where `P` fails is null. -/
theorem exists_pos_of_ae_prod {k : ℕ} {P : (Fin k → ℝ) × ℝ → Prop}
    (hP : ∀ᵐ vd : (Fin k → ℝ) × ℝ, P vd) : ∃ (v : Fin k → ℝ) (d : ℝ), 0 < d ∧ P (v, d) := by
  -- The set where `P` fails is null.
  have hnull : (volume : Measure ((Fin k → ℝ) × ℝ)) {vd | ¬ P vd} = 0 := by
    rwa [MeasureTheory.ae_iff] at hP
  -- The set of points with positive second coordinate is open and nonempty, hence positive.
  have hpos : (volume : Measure ((Fin k → ℝ) × ℝ)) {vd | 0 < vd.2} ≠ 0 := by
    have hopen : IsOpen {vd : (Fin k → ℝ) × ℝ | 0 < vd.2} :=
      isOpen_Ioi.preimage continuous_snd
    have hne : ({vd : (Fin k → ℝ) × ℝ | 0 < vd.2}).Nonempty :=
      ⟨(0, 1), by simp⟩
    exact hopen.measure_ne_zero volume hne
  -- Otherwise the positive set would sit inside the null set where `P` fails.
  by_contra hcon
  apply hpos
  apply MeasureTheory.measure_mono_null _ hnull
  intro vd hv
  rcases vd with ⟨v, d⟩
  intro hPd
  exact hcon ⟨v, d, hv, hPd⟩

end Work.WilE3.Taylor.CaseII
