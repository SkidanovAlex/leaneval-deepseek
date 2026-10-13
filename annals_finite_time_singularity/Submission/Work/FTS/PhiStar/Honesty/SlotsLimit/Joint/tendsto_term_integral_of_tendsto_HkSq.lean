import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.term_integral_le_HkSq
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.mixed_sub_eqOn
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.Joint

/-- **Continuity of the slot integral along the Cauchy family.**

If the approximating data `A n` are `C^∞` on the open quadrant `Q0`, the differences
`A n - A m` lie in `ℋ^k` and their `ℋ^k`-norm squares tend to `0` along
`Filter.atTop ×ˢ Filter.atTop`, then for every sub-slot `(j,i)` of level `k`
(the pure slots `i = 0`, `j ≤ k` and the mixed slots `1 ≤ i`, `i + j ≤ k`) the weighted
`L²`-norms of the differences of the sub-slots tend to `0` as well:

`∫_{Q0} (D_z^jD_θ^i(A n) - D_z^jD_θ^i(A m))² · (termWeight α i)² → 0`.

The proof is the plain squeeze: on the open quadrant the sub-slot of a difference is the
difference of the sub-slots (`mixed_sub_eqOn`, which uses only that `D_z`, `D_θ` are honest
differential operators there), so the integral in question is one of the summands of the
level-`k` integrand and is therefore dominated by the whole `HkSq α k (A n - A m)`
(`term_integral_le_HkSq`), while being nonnegative. -/
theorem tendsto_term_integral_of_tendsto_HkSq {α : ℝ} {k : ℕ} {A : ℕ → ℝ → ℝ → ℝ} (j i : ℕ)
    (hij : (i = 0 ∧ j ≤ k) ∨ (1 ≤ i ∧ i + j ≤ k))
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (A n))
    (hmemsub : ∀ n m : ℕ, Work.Spaces.HkMem α k (fun z θ => A n z θ - A m z θ))
    (h : Filter.Tendsto (fun nm : ℕ × ℕ => Work.Spaces.HkSq α k
        (fun z θ => A nm.1 z θ - A nm.2 z θ)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0)) :
    Filter.Tendsto (fun nm : ℕ × ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        (Work.Spaces.mixed j i (A nm.1) p.1 p.2
            - Work.Spaces.mixed j i (A nm.2) p.1 p.2) ^ 2
          * (Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i p.1 p.2) ^ 2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
  have hQ0 : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  refine squeeze_zero (fun nm => ?_) (fun nm => ?_) h
  · -- the integral is nonnegative
    exact MeasureTheory.setIntegral_nonneg hQ0
      (fun p _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · -- and it is dominated by the whole `ℋ^k`-norm of the difference
    have hsm_sub : Work.FTS.EllipticEst.SmoothOpen (fun z θ => A nm.1 z θ - A nm.2 z θ) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl (hsm nm.1) (hsm nm.2)
    have hb := term_integral_le_HkSq α k hsm_sub (hmemsub nm.1 nm.2) j i hij
    -- On `Q0` the `(j,i)`-sub-slot of the difference is the difference of the sub-slots, so
    -- the integrand here is `(mixed j i (A n - A m) · termWeight)²`.
    have heqon : Set.EqOn
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i (fun z θ => A nm.1 z θ - A nm.2 z θ)
            p.1 p.2 * Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i p.1 p.2) ^ 2)
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i (A nm.1) p.1 p.2
            - Work.Spaces.mixed j i (A nm.2) p.1 p.2) ^ 2
            * (Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      have h1 : Work.Spaces.mixed j i (fun z θ => A nm.1 z θ - A nm.2 z θ) p.1 p.2
          = Work.Spaces.mixed j i (A nm.1) p.1 p.2
            - Work.Spaces.mixed j i (A nm.2) p.1 p.2 :=
        mixed_sub_eqOn (hsm nm.1) (hsm nm.2) j i hp
      show (Work.Spaces.mixed j i (fun z θ => A nm.1 z θ - A nm.2 z θ) p.1 p.2
          * Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i p.1 p.2) ^ 2
        = (Work.Spaces.mixed j i (A nm.1) p.1 p.2
            - Work.Spaces.mixed j i (A nm.2) p.1 p.2) ^ 2
          * (Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i p.1 p.2) ^ 2
      rw [h1, mul_pow]
    rw [← MeasureTheory.setIntegral_congr_fun hQ0 heqon]
    exact hb

end Work.FTS.PhiStar.Honesty.SlotsLimit.Joint
