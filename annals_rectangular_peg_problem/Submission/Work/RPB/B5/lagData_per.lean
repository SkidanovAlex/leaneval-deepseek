import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPV.VBasic

namespace Work.RPB.B5

open Complex Real

/-- `Tk 1` (a shift of the angle `q₂` by `2π`) is the same as advancing the phase argument of
`levelPt` by `2π`: `levelPt` realises `q₂ = a` through `exp (-a·i)`, which is invariant under
`a ↦ a + 2π`. -/
theorem levelPt_Tk (u : ℂ) (σ a : ℝ) :
    Work.RPV.Tk 1 (Work.RPV.levelPt u σ a) = Work.RPV.levelPt u σ (a + 2 * Real.pi) := by
  have hexp : Complex.exp (-((a + 2 * Real.pi : ℝ) : ℂ) * I) = Complex.exp (-(a : ℂ) * I) := by
    rw [show -((a + 2 * Real.pi : ℝ) : ℂ) * I
        = -(a : ℂ) * I + ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [Work.RPV.Tk, Work.RPV.levelPt, hexp]
  norm_num

/-- `basePt` (the `x ≤ 0` half of `lagPt`) has the `2π`-quasiperiodicity in `t` that gives the
`Tk 1`-shift of the angle.  Both branches already satisfy it: the collar through
`Γc τ σ (t+2π) = Γc τ σ t`, `Ac τ σ (t+2π) = Ac τ σ t + 2π` and `levelPt_Tk`, the chord chart
through the `2π`-periodicity of `rho` and `hWper`. -/
theorem basePt_per (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac rho : ℝ → ℝ → ℝ → ℝ)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hΓper : ∀ τ σ t, Γc τ σ (t + 2 * Real.pi) = Γc τ σ t)
    (hAper : ∀ τ σ t, Ac τ σ (t + 2 * Real.pi) = Ac τ σ t + 2 * Real.pi)
    (hrhoper : ∀ τ x t, rho τ x (t + 2 * Real.pi) = rho τ x t) :
    ∀ τ x t, basePt W Γc Ac rho τ x (t + 2 * Real.pi)
      = Work.RPV.Tk 1 (basePt W Γc Ac rho τ x t) := by
  intro τ x t
  simp only [basePt, collarPt]
  by_cases hx : x ≤ -Real.sqrt 2
  · simp only [hx, ite_true]
    rw [hΓper, hAper, ← levelPt_Tk]
  · simp only [hx, ite_false]
    rw [hrhoper, hWper]

theorem lagData_per (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (D : Work.RPB.B5.LagData CI a) :
    ∀ τ x t, Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x (t + 2 * Real.pi)
      = Work.RPV.Tk 1 (Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x t) := by
  have hbase := basePt_per D.W D.Γc D.Ac D.rho D.hWper D.hΓper D.hAper D.hrhoper
  intro τ x t
  by_cases hx : x ≤ 0
  · -- left half: `lagPt` *is* `basePt`
    rw [lagPt, lagPt, if_pos hx, if_pos hx]
    exact hbase τ x t
  · -- right half: `lagPt` is `tau π` of the reflected left point, and `tau π` commutes with `Tk 1`
    rw [lagPt, lagPt, if_neg hx, if_neg hx]
    have h1 : basePt D.W D.Γc D.Ac D.rho τ (-x) (t + 2 * Real.pi - Real.pi)
        = Work.RPV.Tk 1 (basePt D.W D.Γc D.Ac D.rho τ (-x) (t - Real.pi)) := by
      have ht : t + 2 * Real.pi - Real.pi = (t - Real.pi) + 2 * Real.pi := by ring
      rw [ht]
      exact hbase τ (-x) (t - Real.pi)
    rw [h1]
    exact (Work.RPV.Tk_tau 1 Real.pi _).symm

end Work.RPB.B5
