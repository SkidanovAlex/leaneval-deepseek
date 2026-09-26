import Mathlib
import Submission.Work.Asymptotics.Funnel24Tail.Tref24FunnelBound
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KhatE1.Kdev24Base
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Asymptotics.KhatE1.Bracket24Defs
import Submission.Work.Asymptotics.KhatE1.Kdev24BracketSharp

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

/-!
# The sharp remainder of the `d = 24` funnel deviation: the leading term

The target `Kdev24Lead` bounds the sharp remainder of the `d = 24` funnel deviation

  `Kdev ℓ 24 τ z = K̂^{(24)}(τ,z) - (𝒢₊^{(24)}(τ,z) - 𝒢₋^{(24)}(τ,z))/2`

after its leading `E(z)¹`-term, `KdevLead24 ℓ τ · E(z)` with `E(z) = Ept z`, has been
subtracted: on the funnel strip (`τ ∈ 𝔽`, `0 ≤ Re z ≤ 1`, `Im z = t ≥ Im τ + 1`),

  `‖Kdev ℓ 24 τ z - KdevLead24 ℓ τ · E(z)‖ ≤ C ‖q(τ)‖ (scale τ)^N (1+t)^M e^{-2πt}`,

where `q(τ) = qParamFun τ`, `scale τ = 1 + (Im τ)⁻¹ + ‖τ‖` and `e^{-2πt} = ‖E(z)‖²`.

The file records the *explicit bracket form* of the statement (`Bracket24`) and proves that
the target follows from the bound for that bracket.  The identity

  `Bracket24 ℓ τ z = 2 · (Kdev ℓ 24 τ z - KdevLead24 ℓ τ · E(z))`

is the proved `Kdev24RemCore_key` (`Submission/Work/Asymptotics/KhatE1/Kdev24RemCore.lean`),
which assembles the two exact decompositions
`Compact.KPlus24_diff` (the `K₊`-side) and
`Compact.tail_identity`/`Compact.decomp24_sum`/`Compact.Tref24_eq` (the `K₋`-side) together
with `R24_p0_eq_e1combo24`.

## Structure of the remaining core (the second-order `τ`-atom algebra)

Write `E = Ept z` (`‖E‖ = e^{-πt}`), `q_z = E² = qParamFun z`, and let
`q(τ) = qParamFun τ` (`‖q(τ)‖ = e^{-2π Im τ}`), so that on the strip
(`0 ≤ Re z ≤ 1`, `Im z = t ≥ Im τ + 1`) one has `‖q(τ)‖ ≤ e^{-2π} e^{-2πt} = e^{-2π}‖E‖²`.

The bracket is an *explicit* finite expression,

  `Bracket24 = P1 + (3456π)⁻¹[T2 + D]`,

with

* `P1 = K₊^{(24)} - 𝒢₊^{(24)} = -cK z²(ΣSm)/(Sh)`, the five remainder groups `Sm1 … Sm5`
  (`Compact.KPlus24_diff`); each `Smᵢ` carries a *deviation factor* (`Φ-Φref`, `q_z/Δ-1`,
  `d1 = Δ⁻¹-q_z⁻¹-24`, `U-Uref`, `E₄³(1-E₄³)`, `Th0`), hence is `O(q_z)`;
* `T2 = E·(R24 - R24_p0) = E²(XcR24_q1+R24_p1) + E³R24_p2 + E⁴(XcR24_q3+R24_p3)
  + E⁵R24_p4 + E⁶R24_p5` (`Compact.R24`, `Compact.Tref24_eq`);
* `D = Dev24Sum - Am24·E = Y - E(R24_p0+Am24)`, where
  `Y = (Sh)⁻¹(brMinus + Sh·br0) = Tref24 + Dev24Sum`
  (`Compact.tail_identity`, `Compact.decomp24_sum`) and `Dev24Sum = Dev1+…+Dev7`
  (`Compact.kminus_tail_main`) is a sum of products of the cusp deviations
  `dDelta, dW, dL, dD2, dE10, dE14, dSinv` with reference factors.

**Weights.**  A term carrying `E^k` and atoms of `τ`-growth `e^{2πm Im τ}` (one power of `j`)
has weight `e^{-πkt+2πm Im τ}`; on the strip this is `≤ (scale τ)^N (1+t)^M ‖q(τ)‖ e^{-2πt}`
as soon as `k ≥ 2m+2`, so the mechanism `‖E‖^k e^{2π Im τ} ≤ ‖E‖² e^{-2π}` (`k ≥ 2`) of
`Funnel24Tail.Tref24FunnelBound` / `EtailE` controls every term whose `j`-power is at most
the `E`-power minus two.  Since every individual piece above only satisfies the *natural*
weight `‖q(τ)‖⁻¹‖E‖²` (`KPlus24SharpStrip`, `Funnel24Tail.coeff_bounds`, `KMinusFunnelAtoms`),
the content of the bracket bound is that the coefficients of `E^k` in the three pieces
cancel: for `k = 2` down to `O(‖q(τ)‖)`, for `k = 3` to `O(‖q(τ)‖^{1/2})`, for `k = 4,5` to
`O(1)` (multiplied by `(scale τ)^N(1+t)^M`); the orders `k ≥ 6` are dominated without
cancellation.  The first two orders are the ones documented in the workspace as *missing*
(`Kdev_cusp0_strip_sharp`, `KhatE1Core.Kdev8_matching_bridge`: "the coefficients … cancel only
after substituting `ψ₂ = ξ₂𝓛 + (ξ₂|₂S)𝓛_S`, `ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` and using Jacobi's quartic
identity"), the `d = 8` analogue being `KhatE1.KdevE2fun_funnel` (`E²`-coefficient) plus
`KhatE1.KdevBracket_rest` (higher orders).

The identity `[Dev24Sum]_{E¹} = Am24` (equivalently `[Y]_{E¹} = E1combo24 + Am24`) is the
statement `KhatE1.Dev24Sum_E1`; the `E²`-coefficient identity is the `d = 24` analogue of
`KhatE1.KdevE2` and is *not* proved yet.
-/

noncomputable section

/- **The `K₋`-side of the ledger, in the `Am24` normalisation.**

Once `Submission/Work/Asymptotics/KhatE1/Dev24Sum_E1.lean` compiles (it is being extended by a
sibling right now), this is a one-liner:

```
import Submission.Work.Asymptotics.KhatE1.Dev24Sum_E1

theorem Dev24SumAm24Sharp (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Compact.Dev24Sum ℓ τ z - Am24 ℓ τ * Work.Residues.Ept z‖
          ≤ C * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * ‖Work.Residues.Ept z‖ ^ 2 := by
  simpa only [Am24] using Dev24Sum_E1 ℓ
```

(`Am24 ℓ τ` is definitionally the coefficient `-73728 Δ(τ) - 384(ψ₂E₁₀ - ψ₄E₈)` written out in
`Dev24Sum_E1`.)  It is commented out rather than imported because that module is currently
mid-edit and does not yet build. -/

/-- **The reduction of the target to the sharp bracket bound.** -/
theorem Kdev24Lead_of_bracket (ℓ : Work.Kernels.LogLambdaData) (h : Bracket24Sharp ℓ) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ 24 τ z
            - Work.Asymptotics.KhatE1.KdevLead24 ℓ τ * Work.Residues.Ept z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, ?_⟩
  intro τ z t hF ht hz0 hz1 hzim
  have hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0 :=
    Sh_ne_zero_of_im_ge' τ z hF.2 (by rw [hzim]; exact ht)
  have hkey := Bracket24_eq_two_KdevRem ℓ τ z hSh
  have hb' := hb τ z t hF ht hz0 hz1 hzim
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hnorm : ‖Work.Asymptotics.Kdev ℓ 24 τ z
      - Work.Asymptotics.KhatE1.KdevLead24 ℓ τ * Work.Residues.Ept z‖
      = ‖Bracket24 ℓ τ z‖ / 2 := by
    have hbr : ‖Bracket24 ℓ τ z‖ = 2 * ‖Work.Asymptotics.Kdev ℓ 24 τ z
        - Work.Asymptotics.KhatE1.KdevLead24 ℓ τ * Work.Residues.Ept z‖ := by
      rw [hkey, norm_mul, h2]
    rw [hbr]
    ring
  rw [hnorm]
  have hC0 : (0 : ℝ) ≤ C := hC.le
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hs0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N
  have ht0 : (0 : ℝ) ≤ (1 + t) ^ M := by
    apply Real.rpow_nonneg
    have := hF.2
    linarith
  have he0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
  have hX : (0 : ℝ) ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hq0) hs0) ht0) he0
  linarith [hb', hX]

theorem Kdev24Lead (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ 24 τ z
            - Work.Asymptotics.KhatE1.KdevLead24 ℓ τ * Work.Residues.Ept z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) :=
  Kdev24Lead_of_bracket ℓ (Kdev24BracketSharp ℓ)

end

end Work.Asymptotics.KhatE1
