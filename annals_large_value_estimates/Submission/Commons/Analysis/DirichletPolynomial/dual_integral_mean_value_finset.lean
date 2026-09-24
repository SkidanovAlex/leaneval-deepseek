import Mathlib
import Submission.Commons.Analysis.DirichletPolynomial.dual_integral_mean_value
import Submission.Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies

namespace Commons.Analysis.DirichletPolynomial

open scoped BigOperators

/-- A sum over a finset `S` may be reindexed as a sum over `Fin S.card`, using the
noncomputable equivalence `Finset.equivFin`. -/
private lemma sum_finset_eq_sum_fin {ι : Type*} {M : Type*} [AddCommMonoid M]
    (S : Finset ι) (f : ι → M) :
    (∑ i ∈ S, f i) = ∑ k : Fin S.card, f (S.equivFin.symm k).1 := by
  rw [← Finset.sum_attach]
  rw [show S.attach = Finset.univ by simp]
  rw [← Equiv.sum_comp (S.equivFin).symm (fun i : {x // x ∈ S} => f i.1)]

theorem dual_integral_mean_value_finset :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ {ι : Type*} (S : Finset ι) (t : ι → ℝ) (c : ι → ℂ),
        (∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|) →
        ‖∫ x in (N : ℝ)..(2 * (N : ℝ)), ‖∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2‖ ≤
          C * (N : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := dual_integral_mean_value
  refine ⟨C, hCpos, ?_⟩
  intro N hN ι S t c hsep
  classical
  let t' : Fin S.card → ℝ := fun k => t (S.equivFin.symm k).1
  let c' : Fin S.card → ℂ := fun k => c (S.equivFin.symm k).1
  have hsep' : ∀ i j : Fin S.card, i ≠ j → 1 ≤ |t' i - t' j| := by
    intro i j hij
    have hne : (S.equivFin.symm i).1 ≠ (S.equivFin.symm j).1 := by
      intro h
      exact hij (S.equivFin.symm.injective (Subtype.ext h))
    exact hsep _ (S.equivFin.symm i).2 _ (S.equivFin.symm j).2 hne
  have hsum : ∀ x : ℝ,
      (∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ)))
        = ∑ k : Fin S.card, c' k * (x : ℂ) ^ (Complex.I * (t' k : ℂ)) := by
    intro x
    rw [sum_finset_eq_sum_fin S (fun i => c i * (x : ℂ) ^ (Complex.I * (t i : ℂ)))]
  have hInt : (∫ x in (N : ℝ)..(2 * (N : ℝ)),
        ‖∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2)
      = ∫ x in (N : ℝ)..(2 * (N : ℝ)),
          ‖∑ k : Fin S.card, c' k * (x : ℂ) ^ (Complex.I * (t' k : ℂ))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hsum x]
  have hnorm : (∑ k : Fin S.card, ‖c' k‖ ^ 2) = ∑ i ∈ S, ‖c i‖ ^ 2 := by
    rw [sum_finset_eq_sum_fin S (fun i => ‖c i‖ ^ 2)]
  have hb := hC N hN S.card t' c' hsep'
  calc ‖∫ x in (N : ℝ)..(2 * (N : ℝ)),
          ‖∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2‖
      = ‖∫ x in (N : ℝ)..(2 * (N : ℝ)),
          ‖∑ k : Fin S.card, c' k * (x : ℂ) ^ (Complex.I * (t' k : ℂ))‖ ^ 2‖ := by
        rw [hInt]
    _ ≤ C * (N : ℝ) * ∑ k : Fin S.card, ‖c' k‖ ^ 2 := hb
    _ = C * (N : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2 := by rw [hnorm]

end Commons.Analysis.DirichletPolynomial
