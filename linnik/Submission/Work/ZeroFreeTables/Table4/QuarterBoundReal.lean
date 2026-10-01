import Mathlib
import Submission.Work.LinnikAreas.area1

namespace Work.ZeroFreeTables.Table4

/-- HB Lemma 2.5 with `φ = 1/4` for real characters: for `χ` a non-principal character of
modulus `N` with `χ ^ 2 = 1` (so `orderOf χ ≤ 2`) and `1 - 1/k ≤ σ ≤ 1 + loglog N / log N`,

`‖L(σ + it, χ)‖ ≤ C_b (1+|t|) N^{(1/4)(1-σ)(1+1/k)+ε'}`.

The analytic input is the cube-free Burgess character-sum bound of HB Lemma 2.1 in the form
`cubefree_charSum_all_k` (for every `k ≥ 3`), fed into
`LFunction_bound_quarter_of_bounded_order` (the `φ = 1/4` partial-summation chain of HB §2 for
characters of order bounded by `M`), together with the elementary fact that `χ ^ 2 = 1` forces
`orderOf χ ∣ 2`. -/
theorem QuarterBoundReal (k : ℕ) (hk : 3 ≤ k) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
        ∀ σ t : ℝ, 1 - 1 / (k : ℝ) ≤ σ →
          σ ≤ 1 + Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            Cb * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') * (1 + |t|) := by
  -- the cube-free Burgess character-sum input, for every `k ≥ 3` (HB Lemma 2.1)
  obtain ⟨CB, hCB, hB0⟩ := Work.LinnikAreas.cubefree_charSum_all_k (ε' / 4) (by positivity) k (by omega)
  have hB : ∀ {u : ℕ} [NeZero u] (ψ : DirichletCharacter ℂ u), ψ.IsPrimitive → ψ ≠ 1 →
      (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u) →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ u →
        ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤
          CB * (u : ℝ) ^ ((((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2)) + ε' / 4)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
    intro u _ ψ hp hψ hcf N H hN hH hHu
    exact hB0 hcf ψ hp hψ hN hH hHu
  -- HB §2 with `φ = 1/4` for characters of order at most `M = 2`
  obtain ⟨C, hC, hbound⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_bound_quarter_of_bounded_order
      hε' k hk 2 (by norm_num) hCB hB
  refine ⟨C, hC, ?_⟩
  intro N _inst χ hχ hsq σ t hσlo hσhi
  -- `χ ^ 2 = 1` and `χ ≠ 1` give `orderOf χ = 2 ≤ M`
  have hord : orderOf χ ≤ 2 := by
    have hdvd : orderOf χ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    exact Nat.le_of_dvd (by norm_num) hdvd
  exact hbound χ hχ hord σ t hσlo hσhi

end Work.ZeroFreeTables.Table4
