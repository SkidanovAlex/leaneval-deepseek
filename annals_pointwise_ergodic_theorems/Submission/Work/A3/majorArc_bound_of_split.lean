import Mathlib
import Submission.Work.A3.majorArc_split
import Submission.Work.A3.setIntegral_le_sum_of_subset

/-!
# The major-arc energy bound from the three-region split (Area A3)

The major arcs `majorArcSet Q N η` split into

* the **large-denominator** arcs `q ≥ N^γ` (`largeArcSet`),
* the **transition** region of the arcs with `q ≤ N^γ` (`transitionArcSet`, `|β|N^d` below the
  block/integral crossover), and
* the **deep shoulder** `deepArcSet` of the same arcs,

and the integrals over the three pieces are subadditive.  This module assembles the major-arc
energy bound from the three piecewise bounds; the three pieces themselves are
`A3/largeArc_energy_contribution`, `A3/transitionArc_energy_contribution` (via
`A3/transitionArc_bound`) and `A3/deepArc_energy_contribution` (which needs the deep-shoulder
input `(DEEP')` of `NOTES_A3_deepShoulder_SESSION.md`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- Continuity of the polynomial exponential sum in the frequency. -/
theorem continuous_expSum (Q : Polynomial ℤ) (N : ℕ) :
    Continuous fun θ : ℝ => expSum Q N θ := by
  unfold expSum
  refine continuous_finsetSum _ fun n hn => ?_
  fun_prop

/-- The major-arc energy bound, assembled from the three region-wise bounds. -/
theorem majorArc_bound_of_split (Q : Polynomial ℤ) (hd : 2 ≤ Q.natDegree)
    {η γ : ℝ} (hγη : γ ≤ η) {s : ℕ} (hs : 1 ≤ s)
    (hLarge : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ θ in largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s)
        ≤ C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree))
    (hTrans : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ θ in transitionArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s)
        ≤ C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree))
    (hDeep : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ θ in deepArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s)
        ≤ C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ θ in majorArcSet Q N η ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s)
        ≤ C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) := by
  obtain ⟨C₁, hC₁, hL⟩ := hLarge
  obtain ⟨C₂, hC₂, hT⟩ := hTrans
  obtain ⟨C₃, hC₃, hD⟩ := hDeep
  set M : ℝ := max C₁ (max C₂ C₃) with hM
  have hC₁M : C₁ ≤ M := le_max_left _ _
  have hC₂M : C₂ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC₃M : C₃ ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hMpos : 0 < M := lt_of_lt_of_le hC₁ hC₁M
  refine ⟨max 1 (3 ^ (1 / (2 * (s : ℝ))) * M), by positivity, ?_⟩
  intro N hN
  have hg : Continuous fun θ : ℝ => expSum Q N θ := continuous_expSum Q N
  have hgnn : ∀ x : ℝ, 0 ≤ ‖expSum Q N x‖ ^ (2 * s) := fun x => by positivity
  have hEm (E : Set ℝ) : IntegrableOn (fun θ : ℝ => ‖expSum Q N θ‖ ^ (2 * s))
      (E ∩ Set.Icc (0 : ℝ) 1) := by
    have hcont : Continuous fun θ : ℝ => ‖expSum Q N θ‖ ^ (2 * s) :=
      (continuous_norm.comp hg).pow (2 * s)
    exact (hcont.integrableOn_Icc).mono_set Set.inter_subset_right
  have hsub : majorArcSet Q N η ∩ Set.Icc (0 : ℝ) 1 ⊆
      (largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1) ∪
        ((transitionArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1) ∪
          (deepArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1)) := by
    intro x hx
    rcases majorArcSet_subset_split Q N hγη hx.1 with h | h
    · exact Or.inl ⟨h, hx.2⟩
    · rcases h with h | h
      · exact Or.inr (Or.inl ⟨h, hx.2⟩)
      · exact Or.inr (Or.inr ⟨h, hx.2⟩)
  have hmain := setIntegral_le_sum_of_subset hsub hgnn
    (hEm (largeArcSet Q N η γ)) (hEm (transitionArcSet Q N γ)) (hEm (deepArcSet Q N γ))
  have h1 := hL N hN
  have h2 := hT N hN
  have h3 := hD N hN
  have h1' : C₁ ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)
      ≤ M ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC₁.le hC₁M _) (by positivity)
  have h2' : C₂ ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)
      ≤ M ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC₂.le hC₂M _) (by positivity)
  have h3' : C₃ ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)
      ≤ M ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC₃.le hC₃M _) (by positivity)
  have hs' : (0 : ℝ) < (s : ℝ) := by positivity
  have h3eq : ((3 : ℝ) ^ (1 / (2 * (s : ℝ)))) ^ (2 * s) = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (1 / (2 * (s : ℝ)))) (2 * s),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hexp : (1 / (2 * (s : ℝ))) * ((2 * s : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [hexp, Real.rpow_one]
  have h3M : (3 : ℝ) * M ^ (2 * s) ≤ (max 1 (3 ^ (1 / (2 * (s : ℝ))) * M)) ^ (2 * s) := by
    have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ (1 / (2 * (s : ℝ))) * M := by positivity
    calc (3 : ℝ) * M ^ (2 * s)
        = ((3 : ℝ) ^ (1 / (2 * (s : ℝ))) * M) ^ (2 * s) := by
          rw [mul_pow, h3eq]
      _ ≤ (max 1 (3 ^ (1 / (2 * (s : ℝ))) * M)) ^ (2 * s) :=
          pow_le_pow_left₀ hbase (le_max_right _ _) _
  have hsum : C₁ ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)
      + (C₂ ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree))
      + (C₃ ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree))
      ≤ (max 1 (3 ^ (1 / (2 * (s : ℝ))) * M)) ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) := by
    have hNnn : (0 : ℝ) ≤ (N : ℝ) ^ (2 * s - Q.natDegree) := by positivity
    calc C₁ ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)
        + (C₂ ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree))
        + (C₃ ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree))
        ≤ M ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)
          + (M ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree))
          + (M ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)) := by linarith
      _ = 3 * M ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) := by ring
      _ ≤ (max 1 (3 ^ (1 / (2 * (s : ℝ))) * M)) ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) :=
          mul_le_mul_of_nonneg_right h3M hNnn
  linarith [hmain, h1, h2, h3, hsum]

end

end Work.A3
