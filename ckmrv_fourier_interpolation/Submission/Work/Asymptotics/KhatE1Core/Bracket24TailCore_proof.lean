import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24TailCore
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2Prime_bound
import Submission.Work.Asymptotics.KhatE1Core.Bracket24P24Bound
import Submission.Work.Asymptotics.KhatE1Core.Bracket24B35Core
import Submission.Work.Asymptotics.KhatE1Core.Bracket24ExpansionHold_proof


/-!
# The split-form tail bound `Bracket24TailCore`

The target `Work.Asymptotics.KhatE1Core.Bracket24TailCore ℓ` bounds

  `‖KPlus24Group ℓ τ z + KMinus24Group ℓ τ z - (Ept z)² · Bracket24E2' ℓ τ z‖`

by `C ‖q(τ)‖ (scale τ)^N (1+t)^M e^{-2πt}` on the funnel strip
(`τ ∈ 𝔽`, `0 ≤ Re z ≤ 1`, `Im z = t ≥ Im τ + 1`).

## Structure

By the *proved* `Sh_mul_Bracket24_master`, `KPlus24Group + KMinus24Group = Sh τ z · Bracket24`,
so this is the sharp `d = 24` bracket bound; by the *proved* `Bracket24E2Prime_bound` it is
equivalent to the bound on the two groups alone.  Its content is the *cancellation* between the
`K₊`-group and the `K₋`-bracket, whose only available form is the `E(z)`-expansion of
`Sh·Bracket24`.  Writing `E = Ept z` (`‖E‖² = e^{-2πt} ≤ e^{-2π}‖q(τ)‖` on the strip), the
expansion statement is the remainder bound `Bracket24ExpansionHold` below, in which
`B₂ = Bracket24E2'`, `B₃ = KhatE1.Bracket24B3` and `B₅ = KhatE1.Bracket24B5` are the model's
`E(z)²`-, `E(z)³`- and `E(z)⁵`-coefficients.  Together with the *proved*
`Bracket24E2Prime_bound`, `Bracket24B3_bound` and `Bracket24B5_bound`, and the elementary
`‖E‖³, ‖E‖⁵ ≤ ‖E‖²`, it yields the target (`Bracket24TailCore_proof`).

`Bracket24ExpansionHold` is the single remaining obligation; it is the coefficient-wise
analysis of the `d = 24` bracket (the `E(z)²`- and `E(z)³`-coefficient identities, the
second-order `τ`-atom cancellation at `E(z)⁴` — the `d = 24` analogue of
`KhatE1Core.KdevA4plusBound` — and the crude `j(τ)`-degree-≤ 1 estimate at the orders `≥ 6`).
-/


/-
## Route for `Bracket24ExpansionHold` (notes for the next stretch)

`X := KPlus24Group + KMinus24Group` equals `Sh τ z · Bracket24 ℓ τ z` (proved), and both groups
are given in the *reference + deviation* form of the workspace, so the `E(z)`-expansion of `X`
needs no new truncation theory on the τ-side:

* `KMinus24Group'` (proved equal to `KMinus24Group`) is
  `(3456π)⁻¹(kmfd_BR + kmfd_dev - Sh · E · (E1combo24 + Am24))`, with the *proved* finite
  expansion `kmfd_BR = Σ_{k=1}^{8} c_k E^k` (`KMFDDefs.kmfd_BR_expansion`) — an *identity*, no
  analysis — and `kmfd_dev` a sum of products of the deviations `kmfd_dA`, `dDelta`, `dW`,
  `dSinv`, `dSh`, `j(z) - kmfd_jref`, each of which is `O(‖E‖^m)` with `m ≥ 2` in the `Wdom`
  calculus of `KMFDShapes`/`KMFDZDevs`;
* `KPlus24Group = -c z² Σ_{i≤5} Sm_i` is built from the named deviations `Φ - Φref`,
  `q_z/Δ(z) - 1`, `d1 = 1/Δ(z) - E⁻² - 24`, `U - Uref`, `1 - E4(z)³`, `Th0`
  (`K24FDefs`), again `O(‖E‖^m)` with explicit leading coefficients;
* the `z`-atom truncations used by these deviations are *proved*: `KhatE1Core.stripAtom_trunc`
  (`E₂, E₄, E₆, E₈, E₁₀` up to `q_z²` with `O(q_z³)` and `Δ` with `O(q_z⁴)` remainders on
  `Im z ≥ 3`), `KhatE1Core.ZAtomsSecondOrder` (the `θ`-atoms `W`, `U² - V²` to `O(E⁶)`),
  `KhatE1.cusp_L_fourth` (`𝓛` to `O(E⁵)`), `KhatE1Core.dSinv_fourth`, and
  `Work.Asymptotics.KhatE1.InvShGeomTail` for the geometric `1/Sh`-tails (ratio `e^{-2π}`);
  the inverse `1/Δ(z)` is `E⁻²(1 + 24E² + 324E⁴ + …)` with a geometric tail (`|24 q_z| ≤ 24e^{-6π}`).

The expansion then gives `X = Σ_{k≤K} C_k E^k + R` with `C_k` *explicit* polynomials in the
`τ`-atoms and in `z`, `S0`, `Xc`, and `R` a sum of terms carrying one of the deviation/tail
factors above.  The remaining work is

1. the *coefficient identities* `C₂ = Bracket24E2'`, `C₃ = KhatE1.Bracket24B3`,
   `C₅ = KhatE1.Bracket24B5` (finite `ring` checks against the model's coefficients, which are
   the polynomials generated in `KhatE1Core.Bracket24BCoeffs`);
2. the `E(z)⁴`-coefficient bound `‖C₄‖ ≤ C (scale τ)^N (1+t)^M` — the `d = 24` analogue of
   `KhatE1Core.KdevA4plusBound`, using `Δ(τ)j(τ)² = E₄(τ)³j(τ)` and the near-identity
   `ψ₄E₈ - ψ₂E₁₀ = O(‖q‖(scale τ)^N)` (`KhatE1Core.Bracket24B7Bound_proof` is the worked model
   of this step for `k = 7`, and `KhatE1Core.Bracket24P24Bound` for the second-order
   cancellation of the even coefficients);
3. the crude `BoundQ` bound for the orders `k ≥ 6` (each monomial of `C_k` has `j(τ)`-degree
   `≤ 2`, and the `Δ(τ)j(τ)²`-monomials are `E₄(τ)³j(τ)`).

*Refinement of the route.*  Both groups are *algebraic* in the named deviations, so the
expansion can be organised without any new truncation theory: write `Xtrunc` for the
expression obtained from `X` by replacing every *named* deviation (`kmfd_dA`, `dDelta`, `dW`,
`dD2`, `dL`, `dE14`, `dE10`, `dSinv`, `dSh`, `j(z) - kmfd_jref`, and the deviations
`Φ - Φref`, `q_z/Δ(z) - 1`, `d1`, `U - Uref`, `1 - E₄(z)³` of `K24FDefs`) by its *explicit
truncation to the order needed by its cofactor* and every reference by itself.  Then

  `X = Xtrunc + R_struct`,  `Xtrunc - B₂E² - B₃E³ - B₅E⁵ = R_high`

with `R_struct` a sum of products of *deviation tails* (`O(‖E‖^m)` with `m` large enough for
the cofactor's `‖q‖`-power: e.g. `‖q‖⁻²‖E‖⁸ ≤ ‖q‖⁻¹‖E‖⁶` needs `8 ≥ 6`, so a cofactor of
weight `‖q‖⁻²` forces the truncation to `O(‖E‖⁸)`) times *bounded* cofactors, and `R_high` a
sum of monomials of `E`-degree `≥ 6` whose `j(τ)`-degree is at most one.  The second identity
is a *finite* `ring` check (the versions of `C₂`, `C₃`, `C₅` generated from `.mine24/model.py`
coincide with `Bracket24E2'`, `KhatE1.Bracket24B3`, `KhatE1.Bracket24B5` by the fleet's
independent validation), and the bounds on the monomials of `R_high` are the `BoundQ`
bookkeeping already used for `KhatE1Core.Bracket24B7Bound`.

The refined `z`-atom deviations needed by `Xtrunc` are being proved in
`Work.Asymptotics.KhatE1Core.invDeltaSecondOrder` (`1/Δ(z) = q⁻¹ + 24 + 324q + O(q²)`) and
`Work.Asymptotics.KhatE1Core.ZDevRefined`
(`dW = -32E³ + O(E⁴)`, `dD2 = 448E³ + O(E⁴)`, `dE6 = -16632q² + O(q³)`,
`dE8 = 61920q² + O(q³)`, `dE10 = -135432q² + O(q³)`); the remaining ones
(`dSinv = (j-720)² - 179280 - 24j` at `q²`, `dSh = 6480q² + O(q³)`, `E2S - S0 = -24q + O(q²)`,
`dE14 = -196632q² + O(q³)`) are direct consequences of the workspace's *proved* sixth- and
third-order atom expansions (`KhatE1.ZAtomsSecondOrder`, `KhatE1.SecondOrderAtomIdentities`,
`StripAtoms.stripAtom_trunc`).
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- **The `E(z)`-expansion remainder of `Sh·Bracket24 = KPlus24Group + KMinus24Group`** (the
single remaining obligation of the split-form tail bound).

`Bracket24E2'`, `Bracket24B3`, `Bracket24B5` are the `E(z)²`-, `E(z)³`- and `E(z)⁵`-coefficients
of the bracket, so the remainder starts at `E(z)⁴`; its `E(z)⁴`-coefficient is
`O((scale τ)^N(1+t)^M)` (the second-order `τ`-atom cancellation, the `d = 24` analogue of
`KhatE1Core.KdevA4plusBound`) and the orders `≥ 6` are `O(‖q(τ)‖⁻¹(scale τ)^N(1+t)^M)` by the
crude `j(τ)`-degree-≤ 1 estimate (using `Δ(τ)j(τ)² = E₄(τ)³j(τ)` and
`ψ₄E₈ - ψ₂E₁₀ = O(‖q‖(scale τ)^N)`). -/
theorem Bracket24ExpansionHold (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
            + Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
            - Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z * (Work.Residues.Ept z) ^ 2
            - Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3
            - Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Work.Residues.Ept z‖ ^ 6
                  + ‖Work.Residues.Ept z‖ ^ 4) :=
  Work.Asymptotics.KhatE1Core.Bracket24ExpansionHold_proof ℓ

lemma shape_mono_tail {C Q s u N M N' M' : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hs : 1 ≤ s) (hu : 1 ≤ u)
    (hN : N ≤ N') (hM : M ≤ M') :
    C * Q * s ^ N * u ^ M ≤ C * Q * s ^ N' * u ^ M' := by
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu
  have h1 : s ^ N ≤ s ^ N' := Real.rpow_le_rpow_of_exponent_le hs hN
  have h2 : u ^ M ≤ u ^ M' := Real.rpow_le_rpow_of_exponent_le hu hM
  calc C * Q * s ^ N * u ^ M = (C * Q) * (s ^ N * u ^ M) := by ring
    _ ≤ (C * Q) * (s ^ N' * u ^ M') := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hQ)
        exact mul_le_mul h1 h2 (Real.rpow_nonneg hu0 _) (Real.rpow_nonneg hs0 _)
    _ = C * Q * s ^ N' * u ^ M' := by ring

lemma E4_ne_zero_funnel (τ : UpperHalfPlane) (hτ : Work.Asymptotics.Funnel τ) :
    Work.Kernels.E4Fun τ ≠ 0 := by
  intro h0
  have h := Work.FunnelNumerics.E4_sub_one_le τ hτ.2
  rw [h0, zero_sub, norm_neg, norm_one] at h
  norm_num at h

lemma Bracket24B3_eq_reduced (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane)
    (hD : Work.Kernels.DeltaFun τ ≠ 0) (hE4 : Work.Kernels.E4Fun τ ≠ 0) :
    Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ =
      -((84106543104 : ℂ) * Work.Kernels.DeltaFun τ
          + 225780 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ
          + 8940 * Work.Asymptotics.E1combo24 ℓ τ
          - (Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ / Work.Kernels.DeltaFun τ)
        / (88560 * (Real.pi : ℂ)) := by
  rw [Work.Asymptotics.KhatE1.Bracket24B3_eq_red ℓ τ hD hE4, P24F]
  field_simp
  ring

lemma Bracket24B5_eq_reduced (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane)
    (hD : Work.Kernels.DeltaFun τ ≠ 0) (hE4 : Work.Kernels.E4Fun τ ≠ 0) :
    Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ =
      -((5866622484480 : ℂ) * Work.Kernels.DeltaFun τ
          + 5702403 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ
          + 834309 * Work.Asymptotics.E1combo24 ℓ τ
          + (28 / 5) * (Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ / Work.Kernels.DeltaFun τ)
        / (20664 * (Real.pi : ℂ)) := by
  rw [Work.Asymptotics.KhatE1.Bracket24B5_eq_red ℓ τ hD hE4, P24F]
  field_simp
  ring

theorem Bracket24B3_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.Bracket24B3_reduced_big ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  rw [Bracket24B3_eq_reduced ℓ τ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
    (E4_ne_zero_funnel τ hτ)]
  simpa using h τ hτ

theorem Bracket24B5_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.Bracket24B5_reduced_big ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  rw [Bracket24B5_eq_reduced ℓ τ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
    (E4_ne_zero_funnel τ hτ)]
  simpa using h τ hτ

end

end Work.Asymptotics.KhatE1Core

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

theorem Bracket24TailCore_proof (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1Core.Bracket24TailCore ℓ := by
  obtain ⟨C₁, N₁, M₁, hC₁, hN₁, hM₁, hexp⟩ := Bracket24ExpansionHold ℓ
  obtain ⟨C₃, N₃, hC₃, hN₃, hB3⟩ := Bracket24B3_bound ℓ
  obtain ⟨C₅, N₅, hC₅, hN₅, hB5⟩ := Bracket24B5_bound ℓ
  refine ⟨2 * C₁ + C₃ + C₅ + 1, max N₁ (max N₃ N₅), max M₁ 0,
    by positivity, le_trans hN₁ (le_max_left _ _), le_trans hM₁ (le_max_left _ _), ?_⟩
  intro τ z t hF ht hz0 hz1 hzim
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have hu1 : (1 : ℝ) ≤ 1 + t := by have h2 := hF.2; linarith
  have hu0 : (0 : ℝ) ≤ 1 + t := by linarith
  have he0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
  have hEt : ‖Work.Residues.Ept z‖ = Real.exp (-(Real.pi * t)) := by
    rw [Work.Residues.norm_Ept, hzim]
  have hE2e : ‖Work.Residues.Ept z‖ ^ 2 = Real.exp (-(2 * Real.pi * t)) := by
    rw [hEt, show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
      rw [sq, ← Real.exp_add]; congr 1; ring]
  have hE1 : ‖Work.Residues.Ept z‖ ≤ 1 := by
    rw [hEt, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, ht, hF.2]
  have hE0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have key4 : ‖Work.Residues.Ept z‖ ^ 4
      ≤ ‖Work.Kernels.qParamFun τ‖ * Real.exp (-(2 * Real.pi * t)) := by
    have h : ‖Work.Residues.Ept z‖ ^ 4 = Real.exp (-(4 * Real.pi * t)) := by
      rw [hEt]
      rw [show Real.exp (-(Real.pi * t)) ^ 4 = Real.exp (-(4 * Real.pi * t)) by
        rw [← Real.exp_nat_mul]; congr 1; ring]
    have hqn : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) :=
      Work.Asymptotics.norm_qParamFun τ
    rw [h, hqn, ← Real.exp_add]
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos, ht]
  have key6 : (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Work.Residues.Ept z‖ ^ 6
      ≤ ‖Work.Kernels.qParamFun τ‖ * Real.exp (-(2 * Real.pi * t)) := by
    have h : ‖Work.Residues.Ept z‖ ^ 6 = Real.exp (-(6 * Real.pi * t)) := by
      rw [hEt]
      rw [show Real.exp (-(Real.pi * t)) ^ 6 = Real.exp (-(6 * Real.pi * t)) by
        rw [← Real.exp_nat_mul]; congr 1; ring]
    have hqn : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) :=
      Work.Asymptotics.norm_qParamFun τ
    rw [h, hqn, inv_mul_eq_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg, ← Real.exp_add,
      ← Real.exp_add]
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos, ht]
  have hN3 : N₃ ≤ max N₁ (max N₃ N₅) :=
    le_trans (le_max_left N₃ N₅) (le_max_right N₁ (max N₃ N₅))
  have hN5 : N₅ ≤ max N₁ (max N₃ N₅) :=
    le_trans (le_max_right N₃ N₅) (le_max_right N₁ (max N₃ N₅))
  have hM0 : (0 : ℝ) ≤ max M₁ 0 := le_max_right M₁ 0
  have hmono : ∀ {A N' M' : ℝ}, 0 ≤ A → N' ≤ max N₁ (max N₃ N₅) → M' ≤ max M₁ 0 →
      A * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N' * (1 + t) ^ M'
        * Real.exp (-(2 * Real.pi * t))
      ≤ A * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N₁ (max N₃ N₅))
        * (1 + t) ^ (max M₁ 0) * Real.exp (-(2 * Real.pi * t)) :=
    fun hA h1 h2 => mul_le_mul_of_nonneg_right (shape_mono_tail hA hq0 hs1 hu1 h1 h2) he0
  have hp1 : ‖Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
        + Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
        - Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z * (Work.Residues.Ept z) ^ 2
        - Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3
        - Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5‖
      ≤ (2 * C₁) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N₁ (max N₃ N₅))
          * (1 + t) ^ (max M₁ 0) * Real.exp (-(2 * Real.pi * t)) := by
    have hsum : (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Work.Residues.Ept z‖ ^ 6
          + ‖Work.Residues.Ept z‖ ^ 4
        ≤ 2 * (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(2 * Real.pi * t))) := by
      linarith [key4, key6]
    have hb := hexp τ z t hF ht hz0 hz1 hzim
    have hstep : C₁ * (Work.Kernels.scale τ) ^ N₁ * (1 + t) ^ M₁
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Work.Residues.Ept z‖ ^ 6
              + ‖Work.Residues.Ept z‖ ^ 4)
        ≤ C₁ * (Work.Kernels.scale τ) ^ N₁ * (1 + t) ^ M₁
            * (2 * (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(2 * Real.pi * t)))) := by
      refine mul_le_mul_of_nonneg_left hsum ?_
      have h1 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N₁ := Real.rpow_nonneg hs0 N₁
      have h2 : (0 : ℝ) ≤ (1 + t) ^ M₁ := Real.rpow_nonneg hu0 M₁
      positivity
    have hEq : C₁ * (Work.Kernels.scale τ) ^ N₁ * (1 + t) ^ M₁
          * (2 * (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(2 * Real.pi * t))))
        = (2 * C₁) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N₁
            * (1 + t) ^ M₁ * Real.exp (-(2 * Real.pi * t)) := by ring
    refine le_trans (le_trans hb hstep) ?_
    rw [hEq]
    exact hmono (by linarith) (le_max_left _ _) (le_max_left _ _)
  have hp3 : ‖Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3‖
      ≤ C₃ * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N₁ (max N₃ N₅))
          * (1 + t) ^ (max M₁ 0) * Real.exp (-(2 * Real.pi * t)) := by
    have h3 : ‖Work.Residues.Ept z‖ ^ 3 ≤ Real.exp (-(2 * Real.pi * t)) := by
      calc ‖Work.Residues.Ept z‖ ^ 3 ≤ ‖Work.Residues.Ept z‖ ^ 2 :=
            pow_le_pow_of_le_one hE0 hE1 (by norm_num)
        _ = Real.exp (-(2 * Real.pi * t)) := hE2e
    have hb := hB3 τ hF
    rw [norm_mul, norm_pow]
    have hstep : ‖Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ‖ * ‖Work.Residues.Ept z‖ ^ 3
        ≤ C₃ * (Work.Kernels.scale τ) ^ N₃ * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(2 * Real.pi * t)) :=
      mul_le_mul hb h3 (by positivity) (by positivity)
    refine le_trans hstep ?_
    have hEq : C₃ * (Work.Kernels.scale τ) ^ N₃ * ‖Work.Kernels.qParamFun τ‖
          * Real.exp (-(2 * Real.pi * t))
        = C₃ * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N₃ * (1 + t) ^ (0 : ℝ)
            * Real.exp (-(2 * Real.pi * t)) := by
      rw [Real.rpow_zero, mul_one]; ring
    rw [hEq]
    exact hmono hC₃.le hN3 hM0
  have hp5 : ‖Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5‖
      ≤ C₅ * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N₁ (max N₃ N₅))
          * (1 + t) ^ (max M₁ 0) * Real.exp (-(2 * Real.pi * t)) := by
    have h5 : ‖Work.Residues.Ept z‖ ^ 5 ≤ Real.exp (-(2 * Real.pi * t)) := by
      calc ‖Work.Residues.Ept z‖ ^ 5 ≤ ‖Work.Residues.Ept z‖ ^ 2 :=
            pow_le_pow_of_le_one hE0 hE1 (by norm_num)
        _ = Real.exp (-(2 * Real.pi * t)) := hE2e
    have hb := hB5 τ hF
    rw [norm_mul, norm_pow]
    have hstep : ‖Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ‖ * ‖Work.Residues.Ept z‖ ^ 5
        ≤ C₅ * (Work.Kernels.scale τ) ^ N₅ * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(2 * Real.pi * t)) :=
      mul_le_mul hb h5 (by positivity) (by positivity)
    refine le_trans hstep ?_
    have hEq : C₅ * (Work.Kernels.scale τ) ^ N₅ * ‖Work.Kernels.qParamFun τ‖
          * Real.exp (-(2 * Real.pi * t))
        = C₅ * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N₅ * (1 + t) ^ (0 : ℝ)
            * Real.exp (-(2 * Real.pi * t)) := by
      rw [Real.rpow_zero, mul_one]; ring
    rw [hEq]
    exact hmono hC₅.le hN5 hM0
  have hdecomp : Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
      + Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
      - (Work.Residues.Ept z) ^ 2 * Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z
      = (Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
          + Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
          - Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z * (Work.Residues.Ept z) ^ 2
          - Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3
          - Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5)
        + Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3
        + Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5 := by ring
  rw [hdecomp]
  calc ‖(Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
        + Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
        - Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z * (Work.Residues.Ept z) ^ 2
        - Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3
        - Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5)
        + Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3
        + Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5‖
      ≤ ‖(Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
            + Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
            - Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z * (Work.Residues.Ept z) ^ 2
            - Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3
            - Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5)
          + Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3‖
        + ‖Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5‖ :=
        norm_add_le _ _
    _ ≤ (‖Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
            + Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
            - Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z * (Work.Residues.Ept z) ^ 2
            - Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3
            - Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5‖
          + ‖Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3‖)
        + ‖Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5‖ := by
        have := norm_add_le (Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
            + Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
            - Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z * (Work.Residues.Ept z) ^ 2
            - Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3
            - Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5)
          (Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3)
        linarith [this]
    _ ≤ ((2 * C₁) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N₁ (max N₃ N₅))
            * (1 + t) ^ (max M₁ 0) * Real.exp (-(2 * Real.pi * t))
          + C₃ * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N₁ (max N₃ N₅))
            * (1 + t) ^ (max M₁ 0) * Real.exp (-(2 * Real.pi * t)))
        + C₅ * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N₁ (max N₃ N₅))
            * (1 + t) ^ (max M₁ 0) * Real.exp (-(2 * Real.pi * t)) := by
        linarith [hp1, hp3, hp5]
    _ = (2 * C₁ + C₃ + C₅) * ‖Work.Kernels.qParamFun τ‖
          * (Work.Kernels.scale τ) ^ (max N₁ (max N₃ N₅)) * (1 + t) ^ (max M₁ 0)
          * Real.exp (-(2 * Real.pi * t)) := by ring
    _ ≤ (2 * C₁ + C₃ + C₅ + 1) * ‖Work.Kernels.qParamFun τ‖
          * (Work.Kernels.scale τ) ^ (max N₁ (max N₃ N₅)) * (1 + t) ^ (max M₁ 0)
          * Real.exp (-(2 * Real.pi * t)) := by
        have hb : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N₁ (max N₃ N₅))
            * (1 + t) ^ (max M₁ 0) * Real.exp (-(2 * Real.pi * t)) := by positivity
        nlinarith [hb]

end

end Work.Asymptotics.KhatE1Core
