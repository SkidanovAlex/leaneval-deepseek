import Mathlib

namespace Work.EQ.Ladf

/-- The open annulus `{z : ℂ | α < ‖z‖ ∧ ‖z‖ < b}` (which for `α = 0` is a punctured
disc) is connected.  It is the continuous image of the connected set
`ℝ × (α, b)` under the polar-coordinate parametrisation `(θ, ρ) ↦ ρ * exp (θ * I)`. -/
theorem isConnected_openAnnulus {α b : ℝ} (hα : 0 ≤ α) (h : α < b) :
    IsConnected {z : ℂ | α < ‖z‖ ∧ ‖z‖ < b} := by
  -- radial parametrisation of the annulus by angle and radius
  have hset : (fun p : ℝ × ℝ => (p.2 : ℂ) * Complex.exp ((p.1 : ℂ) * Complex.I)) ''
      (Set.univ ×ˢ Set.Ioo α b) = {z : ℂ | α < ‖z‖ ∧ ‖z‖ < b} := by
    ext z
    constructor
    · -- every point of the image has norm `p.2 ∈ (α, b)`
      rintro ⟨p, hp, rfl⟩
      obtain ⟨-, hp2⟩ := hp
      rw [Set.mem_Ioo] at hp2
      have h2 : (0 : ℝ) < p.2 := lt_of_le_of_lt hα hp2.1
      have hnorm : ‖(p.2 : ℂ) * Complex.exp ((p.1 : ℂ) * Complex.I)‖ = p.2 := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          show ‖(p.2 : ℂ)‖ = |p.2| by simp, abs_of_pos h2]
      change α < ‖(p.2 : ℂ) * Complex.exp ((p.1 : ℂ) * Complex.I)‖ ∧
        ‖(p.2 : ℂ) * Complex.exp ((p.1 : ℂ) * Complex.I)‖ < b
      rw [hnorm]
      exact hp2
    · -- conversely every `z` with norm in `(α, b)` is hit, via its argument and norm
      intro hz
      rw [Set.mem_ofPred_eq] at hz
      refine ⟨(Complex.arg z, ‖z‖), ?_, ?_⟩
      · exact ⟨Set.mem_univ _, hz⟩
      · exact Complex.norm_mul_exp_arg_mul_I z
  rw [← hset]
  exact (isConnected_univ.prod (isConnected_Ioo h)).image
    (fun p : ℝ × ℝ => (p.2 : ℂ) * Complex.exp ((p.1 : ℂ) * Complex.I))
    (by fun_prop)

end Work.EQ.Ladf
