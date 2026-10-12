import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.sum_annOfE_normSq_le_nPlusC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.Frame

/-- Expansion of the squared norm of a finite linear combination with **real** coefficients:
`‖∑ i, a i • u i‖ ^ 2 = ∑ i ∑ j, (a i * a j) * re ⟪u i, u j⟫`.

(The real-coefficient restriction is essential: with complex coefficients a conjugation
appears, cf. `inner_smul_left`.) -/
theorem norm_sq_sum_smul_real {ι H : Type*} [Fintype ι] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (u : ι → H) (a : ι → ℝ) :
    ‖∑ i : ι, ((a i : ℝ) : ℂ) • u i‖ ^ 2
      = ∑ i : ι, ∑ j : ι, (a i * a j) * (inner ℂ (u i) (u j)).re := by
  have hinner :
      inner ℂ (∑ i : ι, ((a i : ℝ) : ℂ) • u i) (∑ i : ι, ((a i : ℝ) : ℂ) • u i)
        = ∑ i : ι, ∑ j : ι,
            (starRingEnd ℂ ((a i : ℝ) : ℂ)) * ((a j : ℝ) : ℂ) * inner ℂ (u i) (u j) := by
    simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [hinner]
  rw [RCLike.re_to_complex]
  simp only [Complex.re_sum, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- The `(C * δ_{ij})` part of the quadratic form: only the diagonal survives. -/
theorem sum_ite_mul_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ℝ) (r : ι → ι → ℝ) :
    (∑ i : ι, ∑ j : ι, (C * (if i = j then (1 : ℝ) else 0)) * r i j)
      = C * ∑ i : ι, r i i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem frame_diff_form {ι κ H : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (f : κ → ι → ℝ) (C : ℝ) (u : ι → H) :
    (∑ i : ι, ∑ j : ι, (C * (if i = j then (1 : ℝ) else 0) - ∑ k : κ, f k i * f k j)
        * (inner ℂ (u i) (u j)).re)
      = C * ∑ i : ι, ‖u i‖ ^ 2
        - ∑ k : κ, ‖∑ i : ι, ((f k i : ℝ) : ℂ) • u i‖ ^ 2 := by
  -- The `C * δ` part.
  have hA : (∑ i : ι, ∑ j : ι, (C * (if i = j then (1 : ℝ) else 0))
        * (inner ℂ (u i) (u j)).re)
      = C * ∑ i : ι, (inner ℂ (u i) (u i)).re :=
    sum_ite_mul_diag C (fun i j => (inner ℂ (u i) (u j)).re)
  -- The Gram part, reindexed with `k` outermost.
  have hB : (∑ i : ι, ∑ j : ι, (∑ k : κ, f k i * f k j) * (inner ℂ (u i) (u j)).re)
      = ∑ k : κ, ∑ i : ι, ∑ j : ι, (f k i * f k j) * (inner ℂ (u i) (u j)).re := by
    simp only [Finset.sum_mul]
    exact Finset.sum_comm_cycle
  -- `re ⟪u i, u i⟫ = ‖u i‖ ^ 2`.
  have hC : (∑ i : ι, (inner ℂ (u i) (u i)).re) = ∑ i : ι, ‖u i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← RCLike.re_to_complex]
    exact inner_self_eq_norm_sq (u i)
  -- Split the quadratic form into its two pieces.
  have hsplit :
      (∑ i : ι, ∑ j : ι, (C * (if i = j then (1 : ℝ) else 0) - ∑ k : κ, f k i * f k j)
          * (inner ℂ (u i) (u j)).re)
        = (∑ i : ι, ∑ j : ι, (C * (if i = j then (1 : ℝ) else 0))
              * (inner ℂ (u i) (u j)).re)
          - (∑ i : ι, ∑ j : ι, (∑ k : κ, f k i * f k j)
              * (inner ℂ (u i) (u j)).re) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hsplit, hA, hB, hC]
  -- Expand each `‖∑ i, f k i • u i‖ ^ 2`.
  rw [show (∑ k : κ, ‖∑ i : ι, ((f k i : ℝ) : ℂ) • u i‖ ^ 2)
      = ∑ k : κ, ∑ i : ι, ∑ j : ι, (f k i * f k j) * (inner ℂ (u i) (u j)).re from
    Finset.sum_congr rfl (fun k _ => norm_sq_sum_smul_real u (f k))]

end Work.BoseBoxFock.Frame
