import Mathlib
import Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_DhExplicit_kMultInvSqSummable
import Submission.Work.LinnikAreas.TuranOther.xiTermKernelDecay

open scoped BigOperators

namespace Work.LinnikAreas.TuranOther

/-- Multiplicity-weighted zero sum of the completion `Ξ` of the Riemann zeta function, weighted by
the `(k+1)`-st power of the kernel `1/(t - u)` and evaluated at a point `t` with `re t > 1`, is
summable for every `k ≥ 1`.  The zeros of `Ξ` all have real part at most `1`, so they keep a
uniform distance `t.re - 1` from `t`; the kernel then decays like `1/(1 + ‖u‖²)` along the zeros
(the delegated `xiTermKernelDecay`), and the multiplicity-weighted inverse-square zero sum of `Ξ`
has uniformly bounded finite partial sums (`xiMultInvSqSum_le`). -/
private lemma summable_of_kernel_bound (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re)
    (hkernel : ∃ c : ℝ, 0 < c ∧ ∀ u : ℂ, t.re - 1 ≤ ‖t - u‖ →
      (1 / ‖t - u‖) ^ (k + 1) ≤ c / (1 + ‖u‖ ^ 2)) :
    Summable (fun u : ℂ =>
      ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℕ) : ℂ) * (1 / (t - u)) ^ (k + 1)) := by
  obtain ⟨c, hcpos, hkernel⟩ := hkernel
  obtain ⟨C, hC⟩ := Work.LinnikAreas.DhExplicit.xiMultInvSqSum_le
  -- Zeros of `Ξ` have real part at most `1`, hence are at distance `≥ re t - 1` from `t`.
  have hdist : ∀ u : ℂ, analyticOrderNatAt Work.LinnikAreas.DhK.Xi u ≠ 0 →
      t.re - 1 ≤ ‖t - u‖ := by
    intro u hu
    have hzu : Work.LinnikAreas.DhK.Xi u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hu
    have hure : u.re ≤ 1 := Work.LinnikAreas.DhK.Xi_zero_re_le_one hzu
    have hre : t.re - 1 ≤ (t - u).re := by rw [Complex.sub_re]; linarith
    exact le_trans hre (Complex.re_le_norm _)
  -- Pointwise domination by the multiplicity-weighted inverse-square kernel.
  have hpt : ∀ u : ℂ,
      ‖(((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℕ) : ℂ) * (1 / (t - u)) ^ (k + 1))‖
        ≤ c * ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (1 / (1 + ‖u‖ ^ 2))) := by
    intro u
    by_cases h0 : analyticOrderNatAt Work.LinnikAreas.DhK.Xi u = 0
    · simp [h0]
    · have hd := hdist u h0
      have hkern := hkernel u hd
      have hkern' : (1 / ‖t - u‖) ^ (k + 1) ≤ c * (1 / (1 + ‖u‖ ^ 2)) := by
        have h1 : c * (1 / (1 + ‖u‖ ^ 2)) = c / (1 + ‖u‖ ^ 2) :=
          (div_eq_mul_one_div c (1 + ‖u‖ ^ 2)).symm
        rw [h1]
        exact hkern
      rw [norm_mul, Complex.norm_natCast, norm_pow, norm_div, norm_one]
      rw [show c * (↑(analyticOrderNatAt Work.LinnikAreas.DhK.Xi u) * (1 / (1 + ‖u‖ ^ 2)))
          = ↑(analyticOrderNatAt Work.LinnikAreas.DhK.Xi u) * (c * (1 / (1 + ‖u‖ ^ 2))) by ring]
      exact mul_le_mul_of_nonneg_left hkern' (Nat.cast_nonneg _)
  -- Uniform bound on the finite partial sums of the norm.
  have hsum : Summable (fun u : ℂ =>
      ‖(((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℕ) : ℂ) * (1 / (t - u)) ^ (k + 1))‖) := by
    apply summable_of_sum_le (c := c * C)
    · intro u; exact norm_nonneg _
    · intro S
      calc ∑ u ∈ S, ‖(((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℕ) : ℂ) *
              (1 / (t - u)) ^ (k + 1))‖
          ≤ ∑ u ∈ S, c * ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) *
              (1 / (1 + ‖u‖ ^ 2))) :=
            Finset.sum_le_sum (fun u _ => hpt u)
        _ = c * ∑ u ∈ S, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) *
              (1 / (1 + ‖u‖ ^ 2)) := by
            rw [Finset.mul_sum]
        _ ≤ c * C := mul_le_mul_of_nonneg_left (hC S) (le_of_lt hcpos)
  exact hsum.of_norm

theorem xiZeroSumSummable (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun u : ℂ =>
      ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℕ) : ℂ) * (1 / (t - u)) ^ (k + 1)) :=
  summable_of_kernel_bound k hk ht (xiTermKernelDecay k hk ht)

end Work.LinnikAreas.TuranOther
