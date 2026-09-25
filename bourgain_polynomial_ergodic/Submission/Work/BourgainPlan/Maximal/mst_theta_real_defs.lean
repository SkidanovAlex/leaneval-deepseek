import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstThetaEpsDefs

/-!
# The real-variable form of MST's `(C2)` (interface)

`MSTThetaRealMult P r A` is the *real-variable* (untruncated) form of Mirek–Stein–Trojan's input
`(C2)`: the signed lacunary combination of the differences of the polynomial averaging operators
`A_N h (x) = ∫₀¹ h (x − P(N t)) dt`, along the lacunary blocks `N_j = 2^{j·2^i}`, is bounded on
`L^{2r}(ℝ)` by `A`, uniformly in the level `i`, the number of blocks `M` and the signs `‖ε j‖ ≤ 1`.

This is the honest content of MST's citation "the multiplier `Θ` corresponds to a continuous
singular Radon transform; thus `Θ` defines a bounded operator on `L^r(ℝ^d)` for any `r ∈ (1,∞)`,
with a bound independent of the sign sequence" (arXiv:1512.07518, §4.4 and Theorem 17), and it is
the real-variable statement whose `circleLift`-truncation is the target
`Work.BourgainPlan.Maximal.MSTThetaRawMult` of `Maximal/mst_theta_raw.lean` (the two are related by
the identity `circleLift (Θ_ε ∘ iwRep) = 1_{Ioc (-1/2) (1/2]} · (Θ_ε ∘ Neg.neg)` off `x = 1/2`,
i.e. by composing the real-variable multiplier with the interval (Dirichlet) multiplier
`1_{(-1/2,1/2)}` — see `Maximal/iwmult_const`).
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal Topology

namespace Work.BourgainPlan.Maximal

/-- **The real-variable form of MST's `(C2)`.**  For `‖ε j‖ ≤ 1`, the signed sum of the differences
of the polynomial averaging operators `x ↦ ∫₀¹ h (x − P (2^{k} t)) dt` over the blocks
`k ∈ [j·2^i, (j+1)·2^i)` is an `L^{2r}(ℝ)`-bounded operator with constant `A`, uniformly in `i`,
`M` and `ε`. -/
def MSTThetaRealMult (P : Polynomial ℤ) (r : ℕ) (A : ℝ) : Prop :=
  ∀ (i M : ℕ) (ε : ℕ → ℂ), (∀ j : ℕ, ‖ε j‖ ≤ 1) →
    ∀ (h : ℝ → ℂ), MeasureTheory.Integrable h →
      ∫⁻ x : ℝ, ‖∑ j ∈ Finset.range M, ε j *
          ((∫ t in (0:ℝ)..1, h (x - (toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t)))
            - (∫ t in (0:ℝ)..1, h (x - (toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t))))‖ₑ
          ^ (2 * (r : ℝ)) ∂MeasureTheory.volume
        ≤ ENNReal.ofReal (A ^ (2 * (r : ℝ)))
          * ∫⁻ x : ℝ, ‖h x‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume

end Work.BourgainPlan.Maximal
