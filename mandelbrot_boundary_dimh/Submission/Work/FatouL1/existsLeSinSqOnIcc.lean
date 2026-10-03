import Mathlib

namespace Work.FatouL1

theorem existsLeSinSqOnIcc {p q : ℝ} (hp : -1 < p) (hq : q < 0) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ Set.Icc p q, m ≤ Real.sin (Real.pi * x) ^ 2 := by
  by_cases hpq : p ≤ q
  · obtain ⟨x₀, hx₀, hmin⟩ :=
      isCompact_Icc.exists_isMinOn ⟨p, Set.left_mem_Icc.mpr hpq⟩
        (by fun_prop : ContinuousOn (fun x : ℝ => Real.sin (Real.pi * x) ^ 2)
          (Set.Icc p q))
    refine ⟨Real.sin (Real.pi * x₀) ^ 2, ?_, ?_, ?_⟩
    · have hx₀lt : x₀ < 0 := lt_of_le_of_lt hx₀.2 hq
      have hx₀gt : -1 < x₀ := lt_of_lt_of_le hp hx₀.1
      have hneg : Real.sin (Real.pi * x₀) < 0 := by
        apply Real.sin_neg_of_neg_of_neg_pi_lt
        · nlinarith [Real.pi_pos]
        · nlinarith [Real.pi_pos]
      exact sq_pos_of_neg hneg
    · exact Real.sin_sq_le_one _
    · intro x hx
      exact hmin hx
  · refine ⟨1, one_pos, le_rfl, ?_⟩
    intro x hx
    push Not at hpq
    linarith [hx.1, hx.2, hpq]

end Work.FatouL1
