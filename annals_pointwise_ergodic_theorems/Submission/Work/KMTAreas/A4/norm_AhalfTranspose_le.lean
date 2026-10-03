import Mathlib
import Submission.Work.Analysis.InverseTheory.Transpose

namespace Work.KMTAreas.A4

/-- Pointwise bound for the first dual function: if `‖h‖ ≤ Mh` and `‖g‖ ≤ Mg` pointwise then
`‖Ã_N^*(h,g)(x)‖ ≤ Mh * Mg` for every `x`. -/
theorem norm_AhalfTranspose_le (N : ℕ) (P : Polynomial ℤ) (h g : ℤ → ℂ) {Mh Mg : ℝ}
    (hMh : 0 ≤ Mh) (hMg : 0 ≤ Mg) (hhb : ∀ x : ℤ, ‖h x‖ ≤ Mh)
    (hgb : ∀ x : ℤ, ‖g x‖ ≤ Mg) (x : ℤ) :
    ‖Work.Analysis.InverseTheory.AhalfTranspose N P h g x‖ ≤ Mh * Mg := by
  have hMfg : 0 ≤ Mh * Mg := mul_nonneg hMh hMg
  have hsum_le : ∀ s : Finset ℕ,
      ‖∑ n ∈ s, h (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))‖
        ≤ (s.card : ℝ) * (Mh * Mg) := by
    intro s
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ n ∈ s, ‖h (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))‖ ≤ Mh * Mg :=
      fun n _ => by
        rw [norm_mul]
        exact mul_le_mul (hhb _) (hgb _) (norm_nonneg _) hMh
    calc ∑ n ∈ s, ‖h (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))‖
        ≤ ∑ _n ∈ s, Mh * Mg := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * (Mh * Mg) := by rw [Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [Work.Analysis.InverseTheory.AhalfTranspose, hMfg]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcard : (((Finset.Ioc (N / 2) N).card : ℕ) : ℝ) ≤ (N : ℝ) := by
    have h1 : (Finset.Ioc (N / 2) N).card ≤ N := by
      calc (Finset.Ioc (N / 2) N).card ≤ (Finset.Ioc 0 N).card :=
            Finset.card_le_card fun m hm => by
              simp only [Finset.mem_Ioc] at hm ⊢; omega
        _ = N := by simp
    exact_mod_cast h1
  rw [Work.Analysis.InverseTheory.AhalfTranspose, norm_mul]
  have hscalar : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [show (((N : ℝ)⁻¹ : ℝ) : ℂ) = ((N : ℂ))⁻¹ by push_cast; ring]
    rw [norm_inv, Complex.norm_natCast]
  rw [hscalar]
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
          h (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))‖
      ≤ (N : ℝ)⁻¹ * (((Finset.Ioc (N / 2) N).card : ℝ) * (Mh * Mg)) :=
        mul_le_mul_of_nonneg_left (hsum_le _) (inv_nonneg.mpr hNpos.le)
    _ = ((N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ)) * (Mh * Mg) := by ring
    _ ≤ 1 * (Mh * Mg) := by
        refine mul_le_mul_of_nonneg_right ?_ hMfg
        calc (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ)⁻¹ * (N : ℝ) :=
              mul_le_mul_of_nonneg_left hcard (inv_nonneg.mpr hNpos.le)
          _ = 1 := inv_mul_cancel₀ hNpos.ne'
    _ = Mh * Mg := one_mul _

end Work.KMTAreas.A4
