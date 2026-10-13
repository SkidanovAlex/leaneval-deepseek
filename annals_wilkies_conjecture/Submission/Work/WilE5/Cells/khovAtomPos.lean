import Mathlib
import Submission.Work.WilE5.Basic

namespace Work.WilE5.Cells

open WilkiesDesign WilkiesDesign.E

/-- Evaluating the Khovanskii atom `(f+ε)²(f-ε)²` at a point is positive exactly when
`eaEval c f x` avoids both `ε` and `-ε`. -/
theorem khovAtomPos {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (ε : ℝ)
    (f : WilkiesDesign.E.EAPoly k r) (x : Fin k → ℝ) :
    0 < WilkiesDesign.E.eaEval c ((f + MvPolynomial.C ε) ^ 2 * (f - MvPolynomial.C ε) ^ 2) x ↔
      WilkiesDesign.E.eaEval c f x ≠ ε ∧ WilkiesDesign.E.eaEval c f x ≠ -ε := by
  have h : WilkiesDesign.E.eaEval c
        ((f + MvPolynomial.C ε) ^ 2 * (f - MvPolynomial.C ε) ^ 2) x
      = (WilkiesDesign.E.eaEval c f x + ε) ^ 2
        * (WilkiesDesign.E.eaEval c f x - ε) ^ 2 := by
    simp [eaEval, MvPolynomial.eval_C]
  rw [h, ← mul_pow, sq_pos_iff, mul_ne_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun hh => h2 (by rw [hh]; ring), fun hh => h1 (by rw [hh]; ring)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hh => h2 (by linarith), fun hh => h1 (by linarith)⟩

end Work.WilE5.Cells
