import Mathlib

namespace Work.L2F.Props.oddsub

/-- If `t` is a `2 × 2` matrix over a field that is not a scalar matrix, then the
identity matrix and `t` are linearly independent: any relation `a • 1 + b • t = 0`
forces `a = 0` and `b = 0`. -/
theorem smul_one_add_smul_eq_zero (F : Type*) [Field F]
    (t : Matrix (Fin 2) (Fin 2) F)
    (ht : ∀ c : F, t ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) (a b : F)
    (h : a • (1 : Matrix (Fin 2) (Fin 2) F) + b • t = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have hb' : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
    have h1 : (b⁻¹ * a) • (1 : Matrix (Fin 2) (Fin 2) F) + t = 0 := by
      have := congrArg (fun m => b⁻¹ • m) h
      simpa [smul_add, smul_smul, hb'] using this
    have h2 : t = (-(b⁻¹ * a)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      have h3 := eq_neg_of_add_eq_zero_right h1
      simpa [neg_smul] using h3
    exact ht (-(b⁻¹ * a)) h2
  subst hb
  refine ⟨?_, rfl⟩
  have h' := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 0 0) h
  simpa using h'

end Work.L2F.Props.oddsub
