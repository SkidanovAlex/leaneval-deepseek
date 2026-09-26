import Mathlib
import Submission.Work.Asymptotics.gaussian_bound

namespace Work.Asymptotics

/-- The `l`-th derivative of the complex Gaussian `x ↦ exp(-π x²)` is bounded by a constant
times `(1 + |r|)^l exp(-π r²)`.  This is the specialization to `a = π` of
`Work.Asymptotics.iteratedDeriv_exp_neg_sq_bound`, which expresses the `l`-th derivative as
`P_l(s) exp(-π s²)` with `P_l` a polynomial of degree `≤ l`. -/
theorem gaussian_deriv_bound (l : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
    ‖iteratedDeriv l (fun x : ℝ => ((Real.exp (-(Real.pi * x ^ 2)) : ℝ) : ℂ)) r‖
      ≤ C * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2)) := by
  refine ⟨((l + 1 : ℕ) : ℝ) * (Nat.factorial (l + 2) : ℝ) * (1 + Real.pi) ^ (2 * l),
    ?_, ?_⟩
  · positivity
  · intro r
    have hfun : (fun x : ℝ => ((Real.exp (-(Real.pi * x ^ 2)) : ℝ) : ℂ))
        = fun s : ℝ => Complex.exp (-((Real.pi : ℂ) * (s : ℂ) ^ 2)) := by
      funext s
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hfun]
    have h := iteratedDeriv_exp_neg_sq_bound l (Real.pi : ℂ) r
    have hnorm : ‖(Real.pi : ℂ)‖ = Real.pi :=
      (RCLike.norm_ofReal Real.pi : ‖(Real.pi : ℂ)‖ = |Real.pi|).trans
        (abs_of_pos Real.pi_pos)
    rw [hnorm, Complex.ofReal_re] at h
    refine le_trans h ?_
    have harg : -(Real.pi) * r ^ 2 = -(Real.pi * r ^ 2) := by ring
    rw [harg]

end Work.Asymptotics
