import Mathlib
import Submission.Work.Asymptotics.highPartDefs
import Submission.Work.Asymptotics.psi1_contDiff_omega
import Submission.Work.Asymptotics.ExpBdd_mul
import Submission.Work.Asymptotics.ExpBdd_exp_neg
import Submission.Work.Asymptotics.norm_iteratedDeriv_cast_le
import Submission.Work.Asymptotics.norm_iteratedDeriv_cast_add_one_le

namespace Work.Asymptotics

open scoped Topology

/-- `hiA` and `hiB` satisfy `ExpBdd 1 1`, i.e. all their iterated derivatives are bounded by a
fixed multiple of `(1+|x|)·e^{-x}`.

Both functions are of the form `p · ψ_C · e^{-λ}` with `p` one of the two elementary polynomial
factors `λ` or `λ+1`.  The proof multiplies the `ExpBdd 1 0` estimate for `e^{-λ}`
(`ExpBdd_exp_neg`) with the `ExpBdd 0 1` estimate for the polynomial factor times `ψ_C`; the
latter is the Leibniz sum of the crude bound `‖ψ_C^{(m)}‖ ≤ 2` for all orders `m` (a hypothesis
of the statement) against the bound `‖p^{(i)}‖ ≤ 1 + |λ|` for the polynomial factor.  The
closing step is the multiplicativity of `ExpBdd` (`ExpBdd_mul`): rates `c` and polynomial
degrees `N` add. -/
theorem ExpBdd_hiA_hiB
    (hpsi : ∀ (m : ℕ) (x : ℝ), ‖iteratedDeriv m Work.Asymptotics.psiC x‖ ≤ 2) :
    Work.Asymptotics.ExpBdd 1 1 Work.Asymptotics.hiA ∧
      Work.Asymptotics.ExpBdd 1 1 Work.Asymptotics.hiB := by
  have hcd : ContDiff ℝ ⊤ psiC := psi1_contDiff_omega
  -- The polynomial factor times `psiC` is `ExpBdd 0 1`, with constant `2^(j+1)` at order `j`.
  have key : ∀ (p : ℝ → ℂ), ContDiff ℝ ⊤ p →
      (∀ i x, ‖iteratedDeriv i p x‖ ≤ 1 + |x|) → ExpBdd 0 1 (p * psiC) := by
    intro p hp_cd hp
    refine ⟨hp_cd.mul hcd, fun j => ⟨2 ^ (j + 1), by positivity, fun x => ?_⟩⟩
    rw [iteratedDeriv_mul (hp_cd.contDiffAt.of_le (le_top : ((j : ℕ) : WithTop ℕ∞) ≤ ⊤))
      (hcd.contDiffAt.of_le (le_top : ((j : ℕ) : WithTop ℕ∞) ≤ ⊤))]
    calc ‖∑ i ∈ Finset.range (j + 1),
            ↑(j.choose i) * iteratedDeriv i p x * iteratedDeriv (j - i) psiC x‖
        ≤ ∑ i ∈ Finset.range (j + 1),
            ‖↑(j.choose i) * iteratedDeriv i p x * iteratedDeriv (j - i) psiC x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (1 + |x|) * 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_natCast]
          have hk : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
          have hA : ‖iteratedDeriv i p x‖ ≤ 1 + |x| := hp i x
          have hB : ‖iteratedDeriv (j - i) psiC x‖ ≤ 2 := hpsi (j - i) x
          have h1 : (j.choose i : ℝ) * ‖iteratedDeriv i p x‖ ≤
              (j.choose i : ℝ) * (1 + |x|) := mul_le_mul_of_nonneg_left hA hk
          have h2 : 0 ≤ (j.choose i : ℝ) * (1 + |x|) := by positivity
          exact mul_le_mul h1 hB (norm_nonneg _) h2
      _ = 2 ^ (j + 1) * (1 + |x|) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          rw [pow_succ]
          ring
      _ = 2 ^ (j + 1) * (1 + |x|) ^ 1 * Real.exp (-(0 * x)) := by simp
  have hA : ExpBdd 0 1 ((fun x : ℝ => (x : ℂ)) * psiC) :=
    key _ Complex.ofRealCLM.contDiff norm_iteratedDeriv_cast_le
  have hB0 : ExpBdd 0 1 ((fun x : ℝ => (x : ℂ) + 1) * psiC) :=
    key _ (by simpa using (Complex.ofRealCLM.contDiff.add contDiff_const))
      norm_iteratedDeriv_cast_add_one_le
  have hB : ExpBdd 0 1 (psiC * (fun x : ℝ => (x : ℂ) + 1)) := by
    rw [mul_comm]; exact hB0
  constructor
  · have h := ExpBdd_mul hA ExpBdd_exp_neg
    have hfun : ((fun x : ℝ => (x : ℂ)) * psiC) * (fun x : ℝ => Complex.exp (-(x : ℂ))) =
        hiA := by
      funext x; simp only [Pi.mul_apply, hiA]
    rw [hfun] at h
    simpa using h
  · have h := ExpBdd_mul hB ExpBdd_exp_neg
    have hfun : (psiC * (fun x : ℝ => (x : ℂ) + 1)) * (fun x : ℝ => Complex.exp (-(x : ℂ))) =
        hiB := by
      funext x; simp only [Pi.mul_apply, hiB]
    rw [hfun] at h
    simpa using h

end Work.Asymptotics
