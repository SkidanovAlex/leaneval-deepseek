import Mathlib
import Submission.Work.KMTPlan.A6.MZBlockZero

namespace Work.KMTAreas.A7

/-- The arithmetic symbol `m_Ẑ P q α₁ α₂ = q⁻¹ ∑_{n<q} e(n α₁) e(P(n) α₂)` vanishes at the
second frequency `α₂ = 0` for a non-zero `q`-torsion first frequency `α₁`.

Indeed `m_Ẑ P q α₁ 0 = q⁻¹ ∑_{n<q} e(n α₁)` is a geometric series in the character value
`ω = e(α₁)`: `ω^q = e(q α₁) = 1` while `ω ≠ 1` because `α₁ ≠ 0`. -/
theorem fibre_mZ_zero (P : Polynomial ℤ) {q : ℕ} (hq : 0 < q) {α₁ : Work.Analysis.IonescuWainger.Circle} (hs : q • α₁ = 0) (hne : α₁ ≠ 0) : Work.KMTAreas.A7.mZ P q α₁ 0 = 0 := by
  exact Work.KMTPlan.A6.MZBlockZero P q 1 Nat.one_pos (one_dvd q) α₁ 0
    (by simpa using hne) (by simp) hs

end Work.KMTAreas.A7
