import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Kdev8_matching_bridge
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KMinusFunnelAtoms
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8TailSharpFleet

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

set_option maxHeartbeats 8000000

/-!
# The cleared bracket of the funnel deviation (isolated core)

The target bounds the *cleared* residual

  `Δ(τ) · Sh(τ,z) · (Kdev8Bracket ℓ τ z - 2 · KdevE2 ℓ τ z · E(z)²)`

by `C ‖q(τ)‖² ‖E(z)‖² (scale τ)^N (1+t)^M` on the funnel strip `-1 ≤ Re z ≤ 2`,
`t = Im z ≥ Im τ + 1`, `E(z) = Ept z`.  This file:

* proves the exact clearing identity `Δ(τ)·Sh(τ,z) = Δ(τ)E₄(z)³ - Δ(z)E₄(τ)³`
  (`DeltaFun_mul_Sh`) and the resulting uniform bound
  `‖Δ(τ)·Sh(τ,z)‖ ≤ 27‖q(τ)‖` on the strip (`DeltaFun_mul_Sh_bound`);
* records the reduction `KdevBracket_cleared_core_of_sharp`: the target follows from the
  *sharp funnel bracket tail bound*

    `∃ C N M, ... ‖Kdev8Bracket ℓ τ z - 2·KdevE2 ℓ τ z·E(z)²‖
        ≤ C ‖q(τ)‖ (scale τ)^N (1+t)^M exp(-2πt)`

  on the same strip (the statement isolated, under the names `KdevBracket_rest`,
  `KdevBracket_rest_core`, as the open core of the whole `KhatE1` chapter).

The single remaining gap is therefore the sharp bracket tail bound, which by
`Kdev8Bracket_eq_two_KdevRem` is the statement that the `E(z)^k`-coefficients of the explicit
bracket `Kdev8Bracket` satisfy `KhatE1.KdevRem_strip_sharp`; the `E(z)²`-coefficient of the
bracket is the *proved* `KhatE1.KdevE2_strip_bound`, so what is missing is the matching
("cancellation") of the higher coefficients `k ≥ 3` of the explicit bracket

  `Kdev8Bracket = tailC⁻¹(Φ₁+Φ₂+Φ₃) + (3456π)⁻¹(Ept z·(R8 - R8_p0) + Dev8Sum)`.

Concretely, writing `X = Kdev8Bracket - 2·KdevE2·E(z)²` and expanding in `E = Ept z`,

  `X = K₊tail + (3456π)⁻¹(b₂E³ + b₃E⁴ + b₄E⁵ + b₅E⁶ + Dev8Sum)`

with `b_k = Xc·R8_q k + R8_p k` and `K₊tail = K₊part - [K₊part]_{E²}E²`; the `E³`-coefficient
of `X` is `(3456π)⁻¹(b₂ + [Dev8Sum]_{E³})`, and the required `O(‖q‖·scale^N)` estimate is
exactly the cancellation of the `j·ψ`-monomials of `R8_p2` against the `E³`-coefficient of
`Dev8Sum = dSinv·brMinus + Sinvref·Dev8Raw`, e.g.
`[DevC1]_{E³} = ψ₄(-55296 + 480 j(τ))`, `[DevB1]_{E³} = -480 ψ₂ E₁₄/Δ`,
`[DevA1]_{E³} = -3456 E₄(τ)·[dL]_{E³}`, with the identity `j(W) = E1combo8 - 576(2E₄-ψ₄)`
(`W = ψ₄ - ψ₂E₆/E₄`) reducing the whole combination to
`Y := b₂ + [Dev8Sum]_{E³} = -2985984·E₄ - 8847360·ψ₄ + 24(j-876)·E1combo8 - 3456·E₄·λ`
(`λ = [dL]_{E³}`), which is `O(‖q(τ)‖(scale τ)^N)` by `E1combo8_bound` and the first/second
order expansions `ψ₄ = 2Λ₀ - (288Λ₀+744)q + O(q²)`, `E1combo8/q = 737280Λ₀ + 124416 + 144λ + O(q)`
of the `KhatE1` chapter.
-/

/-- **The clearing factor is explicit.**  Multiplying `Sh` by `Δ(τ)` removes the pole of
`j(τ) = E₄(τ)³/Δ(τ)`: `Δ(τ)Sh(τ,z) = Δ(τ)E₄(z)³ - Δ(z)E₄(τ)³`. -/
theorem DeltaFun_mul_Sh (τ z : ℍ) :
    Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z
      = Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3
        - Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3 := by
  rw [Work.Asymptotics.Compact.Sh,
    ← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
  ring

/-- **The clearing factor is `O(‖q(τ)‖)` on the funnel strip.** -/
theorem DeltaFun_mul_Sh_bound (τ z : ℍ) (t : ℝ) (hτ : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) (hz : z.im = t) :
    ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z‖
      ≤ 27 * ‖Work.Kernels.qParamFun τ‖ := by
  have hτ2 : (2 : ℝ) ≤ τ.im := hτ.2
  have ht3 : (3 : ℝ) ≤ t := by linarith
  have hz3 : (3 : ℝ) ≤ z.im := by rw [hz]; exact ht3
  have hz2 : (2 : ℝ) ≤ z.im := by linarith
  have hzt2 : (1 : ℝ) ≤ z.im := by linarith
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have h1 : ‖Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3‖
      ≤ (27 / 4) * ‖Work.Kernels.qParamFun τ‖ := by
    rw [norm_mul]
    have hE4z : ‖Work.Kernels.E4Fun z‖ ≤ 3 / 2 := Work.Asymptotics.Funnel24.norm_E4_le hz2
    have hE4z3 : ‖Work.Kernels.E4Fun z ^ 3‖ ≤ 27 / 8 := by
      rw [norm_pow]
      have hp := pow_le_pow_left₀ (norm_nonneg (Work.Kernels.E4Fun z)) hE4z 3
      norm_num at hp ⊢
      exact hp
    have hD : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * ‖Work.Kernels.qParamFun τ‖ :=
      Work.Asymptotics.DeltaFun_funnel_le τ hτ
    calc ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E4Fun z ^ 3‖
        ≤ (2 * ‖Work.Kernels.qParamFun τ‖) * (27 / 8) :=
          mul_le_mul hD hE4z3 (norm_nonneg _) (by positivity)
      _ = (27 / 4) * ‖Work.Kernels.qParamFun τ‖ := by ring
  have h2 : ‖Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3‖
      ≤ (27 / 4) * ‖Work.Kernels.qParamFun τ‖ := by
    rw [norm_mul]
    have hDz : ‖Work.Kernels.DeltaFun z‖ ≤ 2 * Real.exp (-(2 * Real.pi * t)) := by
      have h := Work.Asymptotics.DeltaFun_upper_sharp z hzt2
      rwa [hz] at h
    have hE4c : ‖Work.Kernels.E4Fun τ ^ 3‖ ≤ 27 / 8 :=
      Work.Asymptotics.E4cube_funnel_le τ hτ
    have hexp : Real.exp (-(2 * Real.pi * t))
        ≤ Real.exp (-(2 * Real.pi)) * ‖Work.Kernels.qParamFun τ‖ := by
      rw [Work.Asymptotics.norm_qParamFun]
      have hsplit : -(2 * Real.pi * t)
          = -(2 * Real.pi * (t - τ.im)) + -(2 * Real.pi * τ.im) := by ring
      rw [hsplit, Real.exp_add]
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])) (Real.exp_nonneg _)
    have hsmall : Real.exp (-(2 * Real.pi)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
    have hD1 : ‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.E4Fun τ ^ 3‖
        ≤ (2 * Real.exp (-(2 * Real.pi * t))) * (27 / 8) :=
      mul_le_mul hDz hE4c (norm_nonneg _) (by positivity)
    refine le_trans hD1 ?_
    calc (2 * Real.exp (-(2 * Real.pi * t))) * (27 / 8)
        ≤ (2 * (Real.exp (-(2 * Real.pi)) * ‖Work.Kernels.qParamFun τ‖)) * (27 / 8) :=
          mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
      _ = (27 / 4) * (Real.exp (-(2 * Real.pi)) * ‖Work.Kernels.qParamFun τ‖) := by ring
      _ ≤ (27 / 4) * (1 * ‖Work.Kernels.qParamFun τ‖) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hsmall hq0
      _ = (27 / 4) * ‖Work.Kernels.qParamFun τ‖ := by ring
  rw [DeltaFun_mul_Sh]
  calc ‖Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3
        - Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3‖
      ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3‖
        + ‖Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3‖ := norm_sub_le _ _
    _ ≤ (27 / 4) * ‖Work.Kernels.qParamFun τ‖ + (27 / 4) * ‖Work.Kernels.qParamFun τ‖ :=
        add_le_add h1 h2
    _ = (27 / 2) * ‖Work.Kernels.qParamFun τ‖ := by ring
    _ ≤ 27 * ‖Work.Kernels.qParamFun τ‖ := by linarith

/-- **The isolated sharp funnel bracket tail** (the open core of the `KhatE1` chapter): the
explicit bracket `Kdev8Bracket` with its `E(z)²`-coefficient removed is one power of `E(z)` and
one power of `‖q(τ)‖` smaller.  Equivalent to `KhatE1.KdevBracket_rest` /
`KhatE1Core.KdevBracket_rest_core` (`Kdev8Bracket = 2·KdevRem`, `KdevBracket_rest_of_sharp`). -/
theorem Kdev8Bracket_tail_aux (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) :=
  Work.Asymptotics.KhatE1.Kdev8TailSharpFleet ℓ

theorem KdevBracket_cleared_core (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
            (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
              - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Residues.Ept z‖ ^ 2
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := Kdev8Bracket_tail_aux ℓ
  refine ⟨27 * C1, N1, M1, by positivity, hN1, hM1, ?_⟩
  intro τ z t hF ht h1z h2z hzt
  have hclr := DeltaFun_mul_Sh_bound τ z t hF ht hzt
  have hX := hb1 τ z t hF ht h1z h2z hzt
  have hE : ‖Work.Residues.Ept z‖ ^ 2 = Real.exp (-(2 * Real.pi * t)) := by
    rw [Work.Residues.norm_Ept, hzt]
    rw [show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
      rw [sq, ← Real.exp_add]; congr 1; ring]
  have hstep : 27 * ‖Work.Kernels.qParamFun τ‖
      * (C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
          * Real.exp (-(2 * Real.pi * t)))
      ≤ (27 * C1) * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Residues.Ept z‖ ^ 2
          * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1 := by
    rw [← hE]
    exact le_of_eq (by ring)
  rw [norm_mul]
  exact le_trans (mul_le_mul hclr hX (norm_nonneg _) (by positivity)) hstep

end Work.Asymptotics.KhatE1Core

/-!
## Progress notes (current stretch) -- the refined roadmap

**State.**  The target `KdevBracket_cleared_core` is proved in this file from the sharp bracket
bound `Kdev8Bracket_tail_aux`, which is supplied by the axiom-clean theorem
`KhatE1.Kdev8TailSharpFleet` of the cycle-free copy chain `KhatE1Sharp/` (see the final addendum
at the end of this file).  The *new* infrastructure proved in this stretch:

* `KhatE1Core.StripAtoms` : the cusp truncations of the `z`-atoms on the strip `3 ≤ Im z`,
  `E₂,E₄,E₆,E₈,E₁₀ = (trunc) + O(q³)`, `Δ = q - 24q² + 252q³ + O(q⁴)`, with `q = qParamFun z`,
  together with the `ring` identities making the truncations of the products consistent
  (`E4tr_sq`, `E4tr_mul_E6tr`, `E4tr_sq_mul_E6tr`, `E4tr_cube`), and the elementary norm lemmas
  (`norm_mul_dev`, `norm_sq_dev`, `norm_const_qpow_le`, ...) needed to bound the remainders of
  any polynomial combination.

**The precise shape of the remaining obligation.**  Work with the *cleared* residual

  `Y := Δ(τ)·Sh(τ,z)·Wres`,  `Wres := Kdev8Bracket ℓ τ z - 2·KdevE2 ℓ τ z·(Ept z)²`,

which is exactly the left-hand side of the target.  Substituting the proved decompositions
(`Kdev8Bracket_eq_two_KdevRem`, `Compact.Tref8_eq`, `Compact.decomp8`, `R8_p0_eq_e1combo8`) one
has the *polynomial* (denominator-free) identity

  `Wres = P₊ + (3456π)⁻¹·(Ept z·R8 + Dev8Sum) - 2·KdevLead·Ept z - 2·KdevE2·(Ept z)²`,
  `P₊ := tailC⁻¹(Φ₁+Φ₂+Φ₃)`,  `Ept z·R8 + Dev8Sum = Tref8 + Dev8Sum`,

and hence

  `Y = ΔτSh·P₊ + F·ΔτSh·(Ept z·R8) + F·ΔτSh·Dev8Sum - 2KdevLead·ΔτSh·Ept z
        - 2KdevE2·ΔτSh·(Ept z)²`,  `F := (3456π)⁻¹`,

in which *every* `Sh` is to be replaced by the clearing identity
`ΔτSh = Δτ·E₄(z)³ - Δ(z)·E₄(τ)³` and every product `Δτ·j(τ)` by `E₄(τ)³`
(`ClassicalFacts.DeltaFun_mul_jInvariantFun`).  With the atom truncations of `StripAtoms` this
is a polynomial in `e := Ept z`, `z`, and the `τ`-atoms, of `j(τ)`-degree `≤ 1`.

**Why `k ≥ 8` is free.**  On the funnel strip one has `‖e‖² = qParamFun z =: q_z`,
`‖qParamFun τ‖ =: q_τ`, `q_z ≤ e^{-2π} q_τ`, and `q_τ ≤ e^{-4π} < 1`.  If the cleared
coefficient of `e^k` is `c_k` and the crude bound `‖c_k‖ ≤ C q_τ^{-1} (scale τ)^N (1+t)^M`
holds (which is what the `j(τ)`-degree `≤ 1` gives), then

  `‖Y‖ ≤ Σ_k ‖c_k‖ q_z^{k/2} ≤ C q_τ^{-1} (scale)^N (1+t)^M q_z^4/(1-q_z^{1/2})`,

and `q_z^3 ≤ q_τ^3` shows this is `≤ C q_τ² q_z (scale)^N (1+t)^M` -- the target -- **provided**
the orders `k ≤ 7` are handled separately.  The required per-order strengths are

  `‖c_k‖ ≤ C q_τ^{3-k/2} (scale τ)^N (1+t)^M`   (equivalently `‖a_k‖ ≤ C q_τ^{1-k/2}` for the
  coefficients `a_k = [Wres]_{e^k}`),

and the crude bound `q_τ^{-1}` already suffices for `k ≥ 8`; the delicate orders are `k = 3,…,7`.

**What is already done.**

* `k = 0,1,2`: `[Wres]_{e^0} = [Wres]_{e^1} = 0` trivially and `[Wres]_{e^2} = 0` is the proved
  `KhatE1.Kdev8BracketE2_eq_two_KdevE2` (the `E(z)²`-coefficient identity), recorded as
  `KhatE1.KdevBracketClearedRestBound`/`KhatE1.KdevE2_strip_bound`.
* `k = 3`: `KhatE1Core.KdevA3_bound` (+ `KhatE1.KdevA3_eq`) proves
  `‖KdevA3 ℓ τ‖ ≤ C q_τ (scale τ)^N`, and `3456π·KdevA3 = (24j-21024)·E1combo8
    - 2949120 E₄(τ) - 8847360 ψ₄(τ)`; because `[ΔτSh]_{q_z^0} = Δτ` this gives
  `‖c_3‖ ≤ C q_τ² (scale τ)^N ≤ C q_τ^{3/2}`, i.e. the `k = 3` requirement with room to spare.
* the `τ`-side inputs: `KhatE1.EisensteinThreeTerm`, `KhatE1Core.jq_second_order`,
  `KhatE1Core.E1combo8_second_order`, `KhatE1Core.psi_second_order` (`ψ₂`, `ψ₄` to `q²`),
  `KhatE1Core.JmulBig` (multiplication by `j(τ)` costs exactly one power of `q_τ`),
  `KhatE1Core.BigCalc` (the `O((scale τ)^N ‖q_τ‖^k)` calculus), and the `z`-atom deviations
  `KhatE1Core.zAtomDevFourthOrder`, `KhatE1Core.zAtomDevEisensteinFourthOrder`.

**What remains** (in the order of decreasing delicacy), all of it the "second-order `τ`-atom
algebra" of the CKMRV paper:

1. `k = 4`: `‖c_4‖ ≤ C q_τ (scale τ)^N (1+t)^M`.  `c_4` collects
   `[ΔτSh·P₊]_{e⁴}`, `F·Δτ·b_3` (with `b_3 = Xc·R8_q3 + R8_p3`), `F·[ΔτSh]_{q_z^1}·b_1`,
   `F·Δτ·[Dev8Sum]_{e⁴}` with `[Dev8Sum]_{e⁴} = ((j-720)² - 179280 - 24j)·br8ref_0
     + [Dev8Raw]_{e⁴}` (`br8ref_0 = -3456E₄(τ)Xc ℓ z + 1728ψ₄(τ)`; the `e⁴`-coefficients of
   `DevA1,DevA2,DevB1,DevB2,DevC1,DevC2` are recorded in `.kdevdir/NOTES.md` §"a_4" and were
   verified numerically to 12 digits, up to one `z`-free constant), and
   `-2[KdevE2]_{q_z^0}[ΔτSh]_{q_z^1} - 2[KdevE2]_{q_z^1}Δτ`.  The matching uses
   `E1combo8 = j(ψ₄ - ψ₂E₆/E₄) + 576(2E₄ - ψ₄)`, `Δτ·j(τ) = E₄(τ)³`, `E₁₄ = E₄²E₆`,
   `ψ₄ - ψ₂E₆/E₄ = 1152(Λ-1)q_τ + O(q_τ² scale^N)` and `E1combo8 = (737280Λ+122880)q_τ
     + O(q_τ² scale^N)`.
2. `k = 5,6,7`: the same, with progressively weaker requirements
   (`q_τ^{1/2}`, `1`, `q_τ^{-1/2}`), i.e. one, then zero, then no power of `q_τ` has to cancel.
3. the assembled bound `‖Y‖ ≤ C q_τ² q_z (scale τ)^N (1+t)^M` from the crude bound for `k ≥ 8`
   plus items 1-2 (the `Σ_k` argument recorded above), followed by
   `‖ΔτSh‖ ≥ (1/32) q_τ` (`KhatE1.Delta_mul_Sh_ge_strip`) to reach `Kdev8Bracket_tail_aux`.

**Weight calculus.**  The bookkeeping is best done with the multiplicative weights
`Wt p q τ t = exp (-π(p t - q Im τ))` and the domination relation `Wdom` of
`Submission/Work/Asymptotics/KMFDWeight.lean` (proved there for the `d = 24` funnel estimate):
the target weight is `Wt 2 (-4)` (`q_τ² q_z = exp (-2πt - 4π Im τ)`), `e = Ept z` has weight
`Wt 1 0`, `q = qParamFun z` has weight `Wt 2 0`, `Δ(τ)` has weight `Wt 0 2`, `j(τ)` and
`1/Δ(τ)` have weight `Wt 0 (-2)`.  A term of weight `Wt p q` is dominated by the target whenever
`p ≥ 2` and `q ≤ -4`; the terms are grouped precisely so that the pieces that fail this test are
the ones that cancel in the identities of items 1-2.


**Delegation queue (reviewed, correct as stated, not yet proved).**

* `Asymptotics/KhatE1Core/dSinvSecondOrder` : the second-order cusp expansion of
  `dSinv τ z = (Sh τ z)⁻¹ - (1 + (j(τ)-720)q_z)`; the coefficient `(j-720)² - 179280 - 24j`
  and the error shape `(‖q_z‖/‖q_τ‖)³` were verified by two reviewers (and numerically).
  Needed for the *uncleared* route (`Dev8Sum = dSinv·br8ref + …`).
* `Asymptotics/KhatE1Core/E8_sub_E4cube_order` : `E₈(z) - E₄(z)³ = -240 q_z + O(q_z²)` and
  `E₁₀(z) - E₄(z)³ = -984 q_z + O(q_z²)` on `Im z ≥ 3` (reviewed twice as correct; the
  sufficient `O(‖q_z‖)` form is easiest: `‖E₈(z) - E₄(z)³ + 240 q_z‖ ≤ C‖q_z‖`).  Proof route:
  `E₄(z) = E4tr q + d` with `‖d‖ ≤ C₄‖q‖³`, expand `E₄(z)²(1-E₄(z))`, use
  `E4tr_sq`/`E4tr_cube` for the truncation part and `norm_const_qpow_le_one`/`qpow_le_self`
  (both in `KhatE1Core.StripAtoms`) for the `q^k → q` reduction.

**Proved in this stretch and importable now** (all axiom-clean):

* `KhatE1Core.StripAtoms` : the truncations `E2tr, E4tr, E6tr, E8tr, E10tr, E14tr, Dtr, E4cuber`,
  their product-consistency identities, `stripAtom_trunc` (the six `z`-atom truncations with
  `O(q³)`/`O(q⁴)` remainders on `Im z ≥ 3`), and the elementary norm lemmas
  (`E4tr_norm_le`, `E6tr_norm_le`, `norm_sq_dev`, `norm_mul_dev`, `norm_mul_dev_left`,
  `norm_add3_le`, `norm_add4_le`, `norm_add_dev`, `norm_const_qpow_le`,
  `norm_const_qpow_le_one`, `qpow_le_self`).
* `KhatE1Core.PhiCleared` : `inv_J_eq` (`1/(j(τ)-j(z)) = -Δ(z)/Sh`), `Delta_mul_Sh_mul_PhiDiv`,
  `Delta_mul_Sh_mul_PhiCorr` — the clearing of the `Φ₂`/`Φ₃` poles.
* `KhatE1Core.ClearedCombos` : the reference factorizations
  `E8ref·Wref - E6ref·D2ref = e(-24 + 1152e + 4224e² - 61056e³)`,
  `1728·E8ref·Wref - (E8ref·Wref - E6ref·D2ref) = 1728 - 13800e + 869760e² - 6639744e³
    + 19967616e⁴`, `E10ref·𝓛ref = Xc - 8e + (12-264Xc)e² + 2112e³ - 3168e⁴`,
  the `j(τ)`-free regrouping `Delta_mul_psi4block`, `Delta_mul_br8ref`,
  `Delta_mul_Delta_mul_j` (`Δ(τ)(Δ(z)j(τ)) = Δ(z)E₄(τ)³`).

**The `k = 4` landing site (state after the last stretch).**  The cleared residual
`Y := Δ(τ)Sh(τ,z)·Wres` is the left-hand side of the target, and `Wres` is already
`Work.Asymptotics.KhatE1.Wres`; the assembly identity `Y` = (cleared `Φ`-part) + `(3456π)⁻¹`
(cleared `K₋`-part) `- 2KdevLead·ΔτSh·e - 2KdevE2·ΔτSh·e²` is the *proved*
`KhatE1.KdevBracketClearedResidual_eq`.  Every denominator in it is now cleared by a proved
`ring` identity, so the `E(z)⁴`-coefficient can be read off from explicit polynomials:

* `KhatE1Core.PhiCleared` : `ΔτSh·Φ₂ = -φ₂E₁₄z²Δz`, `ΔτSh·Φ₃ = -Δτ·(…)` (`Φ₁` needs no clearing);
* `KhatE1Core.ClearedCombos` :
  `Delta_mul_br8ref` (`Δ(τ)·br8ref`, `j(τ)`-free), `Delta_mul_Dev8Raw` (`Δ(τ)·Dev8Raw`,
  `j(τ)`-free), `Delta_mul_Sh_mul_Sinvref` and `Delta_mul_Sh_mul_dSinv`
  (`Δ(τ)Sh·Sinvref`, `Δ(τ)Sh·dSinv`, with the single surviving `Δ(z)j(τ)·e²` term isolated),
  `Delta_mul_Delta_mul_j`, `E8ref_mul_sub`, `E8ref_Wref_1728`, `E10ref_mul_Lref`,
  `Delta_mul_psi4block`;
* `KhatE1Core.StripAtoms` : the truncations `E2tr … Dtr`, `E4cuber` and `stripAtom_trunc`
  (`E₂,E₄,E₆,E₈,E₁₀ = (trunc) + O(q³)`, `Δ = q - 24q² + 252q³ + O(q⁴)` on `Im z ≥ 3`).

Recipe for `k = 4` (and then `5, 6, 7`): write `Y` with the above identities, replace each
`z`-atom by its truncation at `q_z^{10}` (so that the remainder contributes only for
`k ≥ 20`, where the crude bound `q_τ^{-1}` suffices), expand the resulting *polynomial in
`e = Ept z`* with `ring`, and bound its coefficient of `e⁴` by `C q_τ scale^N(1+t)^M`
(the required strength; `[ΔτSh]_{e^0} = Δτ` and `[Wres]_{e^2} = 0` reduce it to
`‖[Wres]_{e⁴}‖ ≤ C scale^N(1+t)^M`).  The elementary cancellations to invoke are
`E1combo8 = j(ψ₄ - ψ₂E₆/E₄) + 576(2E₄ - ψ₄)` (definitional), `E₆/E₄ = 1 - 744q_τ + O(q_τ²)`,
`ψ₄ - ψ₂E₆/E₄ = 1152(Λ-1)q_τ + O(q_τ² scale^N)` (from `psi_second_order`), and
`E8_sub_E4cube_order` / `E10_sub_E4cube_order` (reviewed, pending).
-/

/-!
## Progress notes (session N+1): the `E(z)^4`-coefficient, corrected

**The `E(z)^4`-coefficient of the bracket is now correct.**  `KhatE1Core.KdevA4num` is defined in
`KhatE1Core/KdevA4.lean` as

  `3456π · tailC⁻¹ · Phi4 τ z + (β₄ + (j(τ)-720)·β₂ + γ·β₀ + Dev4)`,

i.e. `3456π · [Kdev8Bracket]_{e^4}` (where `β₀ = -3456·Xc·E₄ + 1728ψ₄`, `β₂`, `β₄` are the
`e^0,e^2,e^4`-coefficients of `br8ref`, `β₄+(j-720)β₂ = [Ept z · R8]_{e^4} = Xc·R8_q3 + R8_p3`,
`γ = (j-720)² - 179280 - 24j`, and `Dev4 = [Dev8Raw]_{e^4}`); `KdevA4 = (3456π)⁻¹·KdevA4num`.

Two errors of the previous stretch were found and fixed:

* **double counting.**  The earlier definition added the explicit `Xc·R8_q3 + R8_p3` *in addition
  to* the group `β₄ + (j-720)·β₂` — and these are the *same* quantity (`β₄+(j-720)β₂ = b₃ =
  Xc·R8_q3+R8_p3`, verified numerically).  Fixed: the group is written once.  (`Kminus4_eq` and
  `KdevA4_eq` in the same directory are proved from this corrected spelling; both are
  axiom-clean.)
* **the `C²` sign in `Phi4`.**  `Phi4` (the `e^4`-coefficient of the `K₊`-correction
  `Φ₁+Φ₂+Φ₃`) is generated from the atom expansions, and it inherits the sign of
  `phitVec z 2 = z²((E₂|₂S)(z))²`.  Using `E₂(-1/z) = z²E₂(z) - (6i/π)z` one gets

    `phitVec z 2 = z²E₂(z)² - 2(6i/π)zE₂(z) + (6i/π)²`   (`+C²`, `C = 6i/π`),

  whereas the generated `Phi4` carried the opposite sign on the three monomials containing `C²`
  and no `z` (`55440·E₆·C²·τ`, `-984·E₆·j·C²·τ`, `E₆·j²·C²·τ`).  With the wrong sign,
  `KdevA4num/(3456π)` is `~10^22` at `τ = 4i` instead of `~10^-3`; with the corrected sign it
  matches the independent high-precision fit of `[2·KdevRem]_{e^4}` — which is
  `2.4536867717741e-4·z² - 4.7975338866727e-4·i·z - 6.8323457110122e-5` at `τ = 4i` — to twelve
  significant digits (checked numerically at `z = 5i, 0.5+5i, 2+5i`).  The same three signs were
  flipped in the RHSs of `Kplus4_eq` and `KdevA4_eq`.

**Numerical caution.**  At large `Im τ` the atom combination `ψ₄ - ψ₂E₆/E₄ = 1152(Λ-1)q_τ + …`
(and hence `E1combo8 = j(ψ₄-P)+576(2E₄-ψ₄)`) is a cancellation of size `|Λ| ~ π Im τ` against a
quantity of size `q_τ`; evaluating it needs `log10(π Im τ) - log10(q_τ) +` digits, i.e. about
`300` decimal digits at `Im τ ~ 32`.  With insufficient precision one sees spurious exponential
growth of `KdevA4` and of `Kdev8Bracket`.  With `mp.dps = 300` the values are

    |KdevA4num|/(3456π) at (τ = iT, z = 0.5 + i(T+1)):
      T=2 : 8.1e+1,   T=4 : -3.7e-3,   T=8 : -5.4e-13,   T=16 : -7.1e-34,   T=24 : -3.7e-55,

i.e. `KdevA4 = O(q_τ (scale τ)^N (1+t)^M)` — well within the requirement
`‖KdevA4‖ ≤ C (scale τ)^N (1+t)^M` of the `k = 4` rung (session's delegated/attempted
`Asymptotics/KhatE1Core/KdevA4_bound`).

**Roadmap for the remaining orders.**  With `Y := Δ(τ)Sh(τ,z)·Wres` and `Wres = Σ_k a_k e^k`
(`e = Ept z`), `[Y]_{e^k} = Σ_j [ΔτSh]_{e^{2j}} a_{k-2j}`, so it is enough to prove

  `‖a_k‖ ≤ C q_τ^{2-k/2} (scale τ)^N (1+t)^M`  for `k = 3,…,7`  and  `‖a_k‖ ≤ C q_τ^{-2}(...)` for
  `k ≥ 8`   (`a_2 = 0` and `a_0 = a_1 = 0` are proved).

`a_3` is `KhatE1.KdevA3` (`KhatE1Core.KdevA3_bound`, proved: `Big 1`); `a_4` is `KdevA4` above.
The `j`-powers of `a_k` are bounded by `k/2`, so the `j^m`-coefficients of `KdevA4num` (as a
`j`-polynomial, degree two) must satisfy `‖A_m‖ ≤ C q_τ^m (scale τ)^N (1+t)^M`; clearing the
pole with `Δ(τ)j(τ) = E₄(τ)³` (`A_m Δ^m` is `j`-free) turns this into a statement about the
explicit cusp-expansion cancellation of the same kind as `KhatE1.z2coef_bound`.
-/

/-!
## Addendum: the `j`-decomposition and the plan for the `k = 4` bound

`KhatE1Core/KdevA4j.lean` defines `KdevA4j0, KdevA4j1, KdevA4j2` (the `j⁰, j¹, j²`-coefficients
of `KdevA4num`, `j = jInvariantFun τ`; the `E₁₄/Δ = j·(E₆/E₄)`-substitution makes them
`j`-free) and states `KdevA4num_eq_jdecomp` — checked numerically to eight significant digits at
`τ = 4i`, `z ∈ {0.5+5i, 1.5+5i}` (the Lean proof of that algebraic identity is in `KhatE1Core/KdevA4j.lean`;
the file is not imported here).  The route to `KdevA4_bound` is then

* `A₀ := KdevA4j0`: bound directly from the atom estimates (`E₄, E₆` bounded on the funnel,
  `E₂` moderate, `‖Xc‖ ≤ π‖z‖ + ‖cuspC‖`, `‖z‖ ≤ 2(1+t)`, `‖ψ₄‖ ≤ C(scale τ)^N` from
  `Work.Asymptotics.psi_InP`), giving `‖A₀‖ ≤ C(scale τ)^N(1+t)^M`;
* `A₁ := KdevA4j1`: `Δ(τ)j(τ) = E₄(τ)³` turns `Δ·A₁` into a `j`-free polynomial in
  `(z, τ, Δ, E₂, E₄, E₆, E₆/E₄, ψ₂, ψ₄, Xc)` whose cusp expansion should start at `q_τ²`
  (verified symbolically: `[Δ·A₁]_{q^j} = 0` for `j = 0,1`), giving `‖A₁‖ ≤ C q_τ(scale τ)^N(1+t)^M`;
* `A₂ := KdevA4j2`: likewise `[Δ²·A₂]_{q^j} = 0` for `j < 4`, giving
  `‖A₂‖ ≤ C q_τ²(scale τ)^N(1+t)^M`;

and then `‖KdevA4num‖ ≤ (‖A₂‖‖j‖² + ‖A₁‖‖j‖ + ‖A₀‖) ≤ C(scale τ)^N(1+t)^M` using
`‖j(τ)‖ ≤ C‖q_τ‖⁻¹` (`KhatE1.kdevA4_norm_j_le`).  Numerical caution: the cusp-expansion checks
and the evaluation of `ψ₄-ψ₂E₆/E₄ = 1152(Λ-1)q_τ+…` must be done with at least
`log10(‖Λ‖) - log10(q_τ) + 10` correct decimal digits (≥ 300 at `τ = 32i`).
-/

/-!
## Addendum 2: the `j`-decomposition does NOT localise the cancellation

`KdevA4num_eq_jdecomp` is now **proved** (`KhatE1Core/KdevA4j.lean`, axiom-clean):
`KdevA4num = KdevA4j2·j² + KdevA4j1·j + KdevA4j0`.  However, high-precision data
(`mp.dps = 300`, `τ = iT`, `z = 0.5+i(T+1)`) show that the individual coefficients are **large**,
so the decomposition does *not* reduce the bound to separate coefficient estimates:

  T= 4 : |A0| = 9.8e10,  |A1|·q_τ = 2.6e-3,  |A2|·q_τ² = 3.9e-25
  T= 8 : |A0| = 1.0e12,  |A1|·q_τ = 3.4e-13, |A2|·q_τ² = 7.4e-57
  T=12 : |A0| = 3.6e12,  |A1|·q_τ = 1.5e-23, |A2|·q_τ² = 4.8e-89
  T=24 : |A0| = 3.1e13,  |A1|·q_τ = 2.2e-55, |A2|·q_τ² = 2.3e-186

so `A₁ ≈ q_τ^{-1}`-sized and `A₂ ≈ q_τ^{-1}`-sized, and it is the *combination*
`A₁j + A₂j² = O(1)` (equivalently `A₁ + A₂j = O(q_τ)`) that is small: `A₁` and `A₂` are
individually far larger than any `q_τ`-weighted bound allows.  (Indeed `|KdevA4|` itself decays
like `q_τ^{0.97}`, not like `q_τ`.)  Hence the `k=4` bound must be proved on the *sum*
`KdevA4num`, not coefficient-by-coefficient; the weighted statements
`‖A₁‖ ≤ C q_τ (…)` and `‖A₂‖ ≤ C q_τ² (…)` are **false** as they stand, and the surviving useful
statement is `KdevA4_bound` (`‖KdevA4‖ ≤ C (scale τ)^N (1+t)^M`), which is true with room to spare.
-/

/-!
## Final addendum: how the sharp bracket bound was closed

The single obligation of this file was the sharp funnel tail

  `‖Kdev8Bracket ℓ τ z - 2·KdevE2 ℓ τ z·Ept z²‖ ≤ C‖q(τ)‖(scale τ)^N(1+t)^M e^{-2πt}`,

proved by the fleet as `KhatE1.Kdev8TailSharpFleet` from the three function-level estimates of
the doubly-cleared residual (`KhatE1Core.WresPolyPol_bound`, `KhatE1.Kdev8WresPolyDevBound`,
`KhatE1Core.WresDevBound`) via `KhatE1.Kdev8BracketTail_of_three`.

At the time of writing, the *original* modules carrying that chain were caught in a build cycle
(`KhatE1.KdevBracketClearedRestBound` imported `KhatE1.Kdev8TailSharp` while
`KhatE1.Kdev8ABDefs` imported `KhatE1.KdevBracketClearedRestBound`), so no client could import
the sharp bound at all.  To decouple this file from that transient state, the chain has been
duplicated here — with the same declaration names, in namespace `Work.Asymptotics.KhatE1` /
`KhatE1Core`, but in modules that never import the original ones — under
`Submission/Work/Asymptotics/KhatE1Sharp/`:

* `KhatE1Sharp.KdevA3Defs` : a local copy of `KhatE1.KdevA3`, `KhatE1.KdevA3_eq` (breaking the
  edge `KhatE1Core.KdevA3_bound → KhatE1.KdevBracket_cleared`);
* `KhatE1Sharp.KdevA3_bound`, `KhatE1Sharp.Kdev8ABDefs`, `KhatE1Sharp.Kdev8WresExpansion`,
  `KhatE1Sharp.Kdev8WresZAtoms`, `KhatE1Sharp.Kdev8WresTailPoly`,
  `KhatE1Sharp.Kdev8WresAssembly`, `KhatE1Sharp.Kdev8WresTailGlue`,
  `KhatE1Sharp.Kdev8WresHighTrunc`, `KhatE1Sharp.Kdev8WresDeviationBounds`,
  `KhatE1Sharp.Kdev8WresDevPieces`, `KhatE1Sharp.Kdev8WresPolyDevBound`,
  `KhatE1Sharp.WresPolyBound_core`, `KhatE1Sharp.WresDevBound`,
  `KhatE1Sharp.Kdev8TailSharpFleet`, `KhatE1Sharp.Kdev8TailSharp` : copies of the corresponding
  modules whose imports are redirected to the copies above, and in which the cycle-causing
  import `KhatE1.KdevBracketClearedRestBound` is replaced by a local copy of the single theorem
  `KhatE1.Kdev8Bracket_eq_cleared` that was needed from it.

The resulting module `KhatE1Sharp.Kdev8TailSharpFleet` is cycle-free, free of placeholders, and
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`; it is imported above and is
the sole non-Mathlib input of `Kdev8Bracket_tail_aux`.
-/
