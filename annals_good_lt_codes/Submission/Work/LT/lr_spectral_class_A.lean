import Mathlib
import Submission.Work.LT.lr_local_defs
import Submission.Work.LT.lr_mixing
import Submission.Work.LT.lr_walk_mean_zero
import Submission.Work.LT.classOpB_quad_form
import Submission.Work.LT.sqrt_mul_le_half
import Submission.Work.LT.classOpB_layer_reduce

namespace Work.LT

open scoped BigOperators

/-- **Bilinear bound on mean-zero layers.** -/
lemma classOpB_centred_bound {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G) (μ : ℝ)
    (hμ : 0 ≤ μ) (hB : rightExpander B μ) (a0 a1 : G → ℝ) (h1 : ∑ g, a1 g = 0) :
    ∑ g, a0 g * ((∑ j, a1 (g * B j)) / (Δ : ℝ))
      ≤ μ / 2 * ((∑ g, a0 g ^ 2) + (∑ g, a1 g ^ 2)) := by
  have hcs := lrMixing_cauchy_schwarz B μ hμ hB a0 a1 h1
  have hA : 0 ≤ ∑ g, a0 g ^ 2 := Finset.sum_nonneg (fun g _ => sq_nonneg _)
  have hB2 : 0 ≤ ∑ g, a1 g ^ 2 := Finset.sum_nonneg (fun g _ => sq_nonneg _)
  have hAM : Real.sqrt ((∑ g, a0 g ^ 2) * (∑ g, a1 g ^ 2))
      ≤ ((∑ g, a0 g ^ 2) + (∑ g, a1 g ^ 2)) / 2 := sqrt_mul_le_half hA hB2
  have hAM2 : μ * Real.sqrt ((∑ g, a0 g ^ 2) * (∑ g, a1 g ^ 2))
      ≤ μ / 2 * ((∑ g, a0 g ^ 2) + (∑ g, a1 g ^ 2)) := by
    calc μ * Real.sqrt ((∑ g, a0 g ^ 2) * (∑ g, a1 g ^ 2))
        ≤ μ * (((∑ g, a0 g ^ 2) + (∑ g, a1 g ^ 2)) / 2) :=
          mul_le_mul_of_nonneg_left hAM hμ
      _ = μ / 2 * ((∑ g, a0 g ^ 2) + (∑ g, a1 g ^ 2)) := by ring
  linarith [hcs, hAM2]

/-- **Spectral gap of the label-class walk of A-edges.** Identify the set of A-edges with a fixed
label `i` with `Fin 2 × G` via `(β,g) ↦` the A-edge `(β,g,i)`; the parallel move sends
`(0,g) ↦ (1, g*B j)` and `(1,g) ↦ (0, g*(B j)⁻¹)` for a uniformly random `j`. This is
`classOpB`. For mean-zero `s` its quadratic form is at most `μ‖s‖²`, which follows from
`rightExpander B μ` applied to the mean-zero parts of the two layers: the alternating part
`χ(β,g) = (-1)^β` is an eigenvector with eigenvalue `-1` and contributes `-2|G|q² ≤ μ·2|G|q²`. -/
theorem lr_spectral_class_A {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G) (μ : ℝ)
    (hB : rightExpander B μ) (hμ : 0 ≤ μ) :
    ∀ s : Fin 2 × G → ℝ, (∑ p, s p) = 0 →
      ∑ p, s p * classOpB B s p ≤ μ * ∑ p, s p ^ 2 := by
  intro s hs
  classical
  rcases Nat.eq_zero_or_pos Δ with hΔ0 | hΔpos
  · subst hΔ0
    have hzero : ∀ p : Fin 2 × G, classOpB B s p = 0 := by
      intro p
      simp [classOpB]
    have h0 : (∑ p : Fin 2 × G, s p * classOpB B s p) = 0 :=
      Finset.sum_eq_zero (fun p _ => by rw [hzero p, mul_zero])
    rw [h0]
    exact mul_nonneg hμ (Finset.sum_nonneg (fun p _ => sq_nonneg (s p)))
  · have hmeanz : (∑ g, s (0, g)) + (∑ g, s (1, g)) = 0 := by
      have h := hs
      rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
      exact h
    have ha1sum : (∑ g, (s (1, g) - (∑ g, s (1, g)) / (Fintype.card G : ℝ))) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
      ring
    have hred := classOpB_layer_reduce B hΔpos (fun g => s (0, g)) (fun g => s (1, g)) hmeanz
    have hcen := classOpB_centred_bound B μ hμ hB
      (fun g => s (0, g) - (∑ g, s (0, g)) / (Fintype.card G : ℝ))
      (fun g => s (1, g) - (∑ g, s (1, g)) / (Fintype.card G : ℝ)) ha1sum
    have hA : (∑ g, (s (0, g) - (∑ g, s (0, g)) / (Fintype.card G : ℝ)) ^ 2)
        ≤ ∑ g, s (0, g) ^ 2 := by
      simpa using lrMixing_centered_sq_le (fun g => s (0, g))
    have hB2 : (∑ g, (s (1, g) - (∑ g, s (1, g)) / (Fintype.card G : ℝ)) ^ 2)
        ≤ ∑ g, s (1, g) ^ 2 := by
      simpa using lrMixing_centered_sq_le (fun g => s (1, g))
    have hmain : (∑ g, s (0, g) * ((∑ j, s (1, g * B j)) / (Δ : ℝ)))
        ≤ μ / 2 * ((∑ g, s (0, g) ^ 2) + (∑ g, s (1, g) ^ 2)) := by
      refine le_trans hred (le_trans hcen ?_)
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ μ / 2)
      linarith
    have hnorm : (∑ p : Fin 2 × G, s p ^ 2) = (∑ g, s (0, g) ^ 2) + (∑ g, s (1, g) ^ 2) := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [classOpB_quad_form B s, hnorm]
    linarith [hmain]

end Work.LT
