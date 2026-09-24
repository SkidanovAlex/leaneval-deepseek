import Mathlib
import Submission.Commons.Analysis.ExponentialSums.third_derivative_middle_bound
import Submission.Commons.Analysis.Real.le_sqrt_mul_rpow_neg_sixth
import Submission.Commons.Data.Int.Finset.norm_Icc_sum_le

open Complex
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

namespace Commons.Analysis.ExponentialSums

scoped notation "exp" => Complex.exp

/-- additive character e(x) = exp(2π i x) -/
noncomputable def ch (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma norm_ch_le_one (x : ℝ) : ‖ch x‖ ≤ 1 := by
  unfold ch
  rw [Complex.norm_exp_ofReal_mul_I]

noncomputable def Ssum (f : ℝ → ℝ) (n : ℤ) : ℂ := ch (f (n : ℝ))

lemma norm_Ssum (f : ℝ → ℝ) (n : ℤ) : ‖Ssum f n‖ ≤ 1 := norm_ch_le_one (f (n : ℝ))

lemma trivial_bound {a : ℤ} {M : ℕ} (f : ℝ → ℝ) :
    ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), Ssum f n‖ ≤ (M : ℝ) := by
  exact Commons.Data.Int.Finset.norm_Icc_sum_le (a := a) (N := M) (w := Ssum f) (norm_Ssum f)

lemma le_mul_rpow_sixth {M : ℕ} {l : ℝ} (hl1 : 1 ≤ l) :
    (M : ℝ) ≤ (M : ℝ) * l ^ (1 / 6 : ℝ) := by
  by_cases hM0 : M = 0
  · subst hM0
    simp
  · have hlr : 1 ≤ l ^ (1 / 6 : ℝ) := Real.one_le_rpow hl1 (by norm_num)
    have hM0' : 0 ≤ (M : ℝ) := by positivity
    calc
      (M : ℝ) = (M : ℝ) * 1 := by ring
      _ ≤ (M : ℝ) * l ^ (1 / 6 : ℝ) := mul_le_mul_of_nonneg_left hlr hM0'

/-- van der Corput third derivative test (two-sided, α-uniform).  Let `α ≥ 1`.
For `f` three times continuously differentiable on `[a, a+M]` (`M ≥ 1`) with
`λ ≤ f''' ≤ α·λ` throughout (`0 < λ`), there is a constant `C` (depending on
`α` but not on `a, M, f, λ`) such that

    ‖Σ_{a<n≤a+M} exp(2πi·f(n))‖ ≤ C·(M·λ^{1/6} + M^{1/2}·λ^{−1/6}).

The two-sided (ratio-`α`) hypothesis on the *third* derivative is essential. -/
theorem third_derivative_test {α : ℝ} (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a : ℤ} {M : ℕ} (_hM : 1 ≤ M) (f : ℝ → ℝ) {l : ℝ} (_hl : 0 < l)
        (_hf : ContDiffOn ℝ 3 f (Set.Icc (a : ℝ) ((a : ℝ) + (M : ℝ))))
        (_hppp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + (M : ℝ)) →
          l ≤ deriv (deriv (deriv f)) x ∧ deriv (deriv (deriv f)) x ≤ α * l),
        ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)),
            exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * I)‖
          ≤ C * ((M : ℝ) * l ^ (1 / 6 : ℝ) +
              Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ))) := by
  rcases third_derivative_middle_bound hα with ⟨Cmid, hCmidpos, hCmidmain⟩
  refine ⟨max 1 Cmid, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro a M hM f l hl hf hppp
  have hCge1 : (1 : ℝ) ≤ max 1 Cmid := le_max_left 1 Cmid
  have hCgeC : Cmid ≤ max 1 Cmid := le_max_right 1 Cmid
  by_cases hcase1 : 1 ≤ l
  · calc
      ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)),
          exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * I)‖
          = ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), Ssum f n‖ := by
            simp [Ssum, ch]
      _ ≤ (M : ℝ) := trivial_bound f
      _ ≤ (M : ℝ) * l ^ (1 / 6 : ℝ) := le_mul_rpow_sixth hcase1
      _ ≤ max 1 Cmid * ((M : ℝ) * l ^ (1 / 6 : ℝ) +
            Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ))) := by
            have hB : 0 ≤ Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ)) := by positivity
            have hA : 0 ≤ (M : ℝ) * l ^ (1 / 6 : ℝ) := by positivity
            nlinarith
  · have hl1 : l < 1 := lt_of_not_ge hcase1
    by_cases hcase2 : (M : ℝ) ^ 3 * l ≤ 1
    · calc
        ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)),
            exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * I)‖
            = ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), Ssum f n‖ := by
              simp [Ssum, ch]
        _ ≤ (M : ℝ) := trivial_bound f
        _ ≤ Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ)) :=
              Commons.Analysis.Real.le_sqrt_mul_rpow_neg_sixth hM hl hcase2
        _ ≤ max 1 Cmid * ((M : ℝ) * l ^ (1 / 6 : ℝ) +
              Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ))) := by
              have hB : 0 ≤ Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ)) := by positivity
              have hA : 0 ≤ (M : ℝ) * l ^ (1 / 6 : ℝ) := by positivity
              nlinarith
    · have hmid : (1 : ℝ) < (M : ℝ) ^ 3 * l := lt_of_not_ge hcase2
      have hM2 : 2 ≤ M := by
        by_contra hnot
        have hMle1 : M ≤ 1 := by omega
        have hM1 : M = 1 := by omega
        subst M
        norm_num at hmid
        linarith
      have hS := hCmidmain (a := a) (M := M) hM2 f (l := l) hl hf hppp (le_of_lt hmid) hl1
      have hX : 0 ≤ (M : ℝ) * l ^ (1 / 6 : ℝ) +
            Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ)) := by positivity
      calc
        ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)),
            exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * I)‖
            ≤ Cmid * ((M : ℝ) * l ^ (1 / 6 : ℝ) +
                Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ))) := hS
        _ ≤ max 1 Cmid * ((M : ℝ) * l ^ (1 / 6 : ℝ) +
              Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ))) := by
              exact mul_le_mul_of_nonneg_right hCgeC hX

end Commons.Analysis.ExponentialSums
