import Mathlib

namespace Work.TMC14Core

/-- If the real part of `Q` at `0` is negative, then it stays negative in a
neighbourhood of `0`: continuity of `E ↦ (Q.eval E).re` at `0`. -/
theorem exists_delta_re_neg (Q : Polynomial ℂ) (h : (Q.eval (0 : ℂ)).re < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ E : ℝ, |E| < δ → (Q.eval (E : ℂ)).re < 0 := by
  have hcont : Continuous fun E : ℝ => (Q.eval (E : ℂ)).re :=
    Complex.continuous_re.comp ((Polynomial.continuous Q).comp Complex.continuous_ofReal)
  have hopen : IsOpen {E : ℝ | (Q.eval (E : ℂ)).re < 0} := by
    have := isOpen_lt hcont (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    simpa using this
  have hmem : (0 : ℝ) ∈ {E : ℝ | (Q.eval (E : ℂ)).re < 0} := by
    simpa using h
  rcases Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem) with ⟨ε, hε, hsub⟩
  refine ⟨ε, hε, fun E hE => ?_⟩
  exact hsub (by rw [Metric.mem_ball, Real.dist_eq]; simpa using hE)

end Work.TMC14Core
