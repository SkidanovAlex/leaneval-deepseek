import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Coordinate

/-!
# PERT: the two elementary ingredients of the orbit relation `PertData.orbit`

* `piExp_eq_iff`: `piExp x = piExp y ↔ x = y + k` for some `k : ℤ` — this is how the hypothesis
  `piExp (R̃_f^m w) = piExp w'` of (4.2.3) produces the integer exponent `n := w' - R̃_f^m w`.
* `iterate_phi`: along a walk on which the Abel equation `φ (t+1) = f (φ t)` holds,
  `f^[n] (φ z) = φ (z + n)` — this is how the Abel equation of `φ_f` is turned into the conclusion
  `f^[n] (φ w) = φ w'` of (4.2.3).
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

/-- `piExp x = piExp y` iff `x` and `y` differ by an integer. -/
theorem piExp_eq_iff (x y : ℂ) : piExp x = piExp y ↔ ∃ k : ℤ, x = y + k := by
  have hne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero]
  constructor
  · intro h
    have hexp : Complex.exp (2 * Real.pi * I * x) = Complex.exp (2 * Real.pi * I * y) := by
      simpa only [piExp] using h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    refine ⟨n, ?_⟩
    have h2 : (2 * Real.pi * I) * (x - y - n) = 0 := by linear_combination hn
    have h3 : x - y - n = 0 := by
      rcases mul_eq_zero.mp h2 with h4 | h4
      · exact absurd h4 hne
      · exact h4
    linear_combination h3
  · rintro ⟨k, rfl⟩
    have hk : 2 * Real.pi * I * (y + k) = 2 * Real.pi * I * y + (k : ℂ) * (2 * Real.pi * I) := by
      ring
    simp only [piExp]
    rw [hk, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Along a walk where the Abel equation holds, iterating `f` corresponds to translating the
argument of `φ`. -/
theorem iterate_phi {f φ : ℂ → ℂ} {z : ℂ} (k : ℕ)
    (h : ∀ i : ℕ, i < k → φ (z + i + 1) = f (φ (z + i))) :
    f^[k] (φ z) = φ (z + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : ∀ i : ℕ, i < k → φ (z + i + 1) = f (φ (z + i)) := fun i hi => h i (by omega)
    rw [Function.iterate_succ_apply', ih hk]
    have hlast : φ (z + k + 1) = f (φ (z + k)) := h k (by omega)
    rw [← hlast]
    push_cast
    ring_nf

end

end Work.Pert
