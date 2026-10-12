import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7.Control3Q_of_estimates
import Submission.Work.BoseB7.Q3_split
import Submission.Work.BoseB7.dNumOpR_mono
import Submission.Work.BoseB7.spectLe_nOp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.Control3Q_of_estimates_at` — FS `thm:Control3Q` from the three estimates *at*

`Control3Q_of_estimates` (`Control3Q_of_estimates.lean`) is the *conditional*
assembly of FS `thm:Control3Q` (`eq:Q3Cancels`): given the three estimates of
`lem:EstimatesOnQ3-js` (`EstQ3one`, `EstQ3twoThree`, `EstQ3four`), FS's
arithmetic `ErrDominated`, **and** three further operator-theoretic inputs —

* `hsplit : Q₃ = Q₃⁽¹⁾+Q₃⁽²⁾+Q₃⁽³⁾+Q₃⁽⁴⁾` (FS `lem:EstimatesOnQ3-js`, the
  Bogoliubov substitution),
* `hkin : ⟨f, ∫_{P_H}𝒟 b†b f⟩ ≤ ⟨f, ∫𝒟 b†b f⟩` (the `P_H`-to-`all` monotonicity
  of the diagonalised kinetic operator),
* `hgap : ⟨f, (b/100)ℓ⁻²n₊ f⟩ ≤ ⟨f, (b/100)(ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H) f⟩`
  (the gap word is larger than its `n₊` part),

the theorem follows.  The present module proves that **at FS's own hypotheses**
all three extra inputs are *theorems* — `EstHyp F E` (the kernel hypotheses
already assumed by the three estimates) supplies everything:

* `hsplit` is `Q3_split F E h` (`Q3_split.lean`);
* `hkin` is `dNumOpR_mono` (`dNumOpR_mono.lean`) applied to the inclusion
  `P_H ⊆ all`, with `𝒟 ≥ 0` from `EstHyp.Bsmall` and `Dcoef_nonneg`;
* `hgap` is the arithmetic identity
  `(b/100)(ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H) - (b/100)ℓ⁻²n₊ = (b/100)ε_T(dℓ)⁻²·n₊^H`
  together with the non-negativity of `n₊^H` as a quadratic form
  (`bp_nPlusH_nonneg`) and of the coefficient `(b/100)ε_T(dℓ)⁻²`
  (`EstHyp.b_nonneg`, `EstHyp.eT_nonneg`, and `x^(-2:ℝ) ≥ 0` for *every* real
  `x`, `rpow_neg_two_nonneg`).

So `Control3Q_of_estimates_at` is exactly `Control3Q_of_estimates` with the
three inputs discharged, i.e. the honest statement of FS §10's assembly: the
three estimates are the *only* mathematical input left.

## Contents

* `rpow_neg_two_nonneg` — `0 ≤ x^(-2:ℝ)` for every real `x` (no sign hypothesis).
* `bp_regionSum_nonneg` — a region sum of positive operators with nonnegative
  weights has nonnegative quadratic form.
* `bp_nPlusH_nonneg` — `0 ≤ ⟨f, n₊^H f⟩`.
* `gapOp_quadform_le` — `hgap` at FS's hypotheses.
* `Control3Q_of_estimates_at` — the assembly.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

/-- `x^(-2:ℝ) ≥ 0` for **every** real `x`: the exponent is an (even, negative)
integer, so the real power is the usual integer power by `Real.rpow_intCast`, and
`x^(-2) = (x²)⁻¹ ≥ 0`.  (No hypothesis on the sign of `x` is needed; note that
`Real.rpow_neg` would require `0 ≤ x`.) -/
lemma rpow_neg_two_nonneg (x : ℝ) : 0 ≤ x ^ (-(2 : ℝ)) := by
  rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  simp only [zpow_neg, zpow_ofNat]
  exact inv_nonneg.mpr (sq_nonneg x)

/-- A region sum `regionSum R w op = Σ_{i ∈ R, i ≠ 0} w i • op i` of operators
each of which is nonnegative as a quadratic form, with nonnegative weights, is
nonnegative as a quadratic form. -/
lemma bp_regionSum_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (R : Mode → Prop) [DecidablePred R]
    (w : Mode → ℝ) (hw : ∀ i, 0 ≤ w i) (op : Mode → F.H →ₗ[ℝ] F.H)
    (hop : ∀ i (f : F.H), 0 ≤ F.bp (op i f) f) (f : F.H) :
    0 ≤ F.bp (F.regionSum R w op f) f := by
  simp only [FockData.regionSum, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hop i f))

/-- FS §7's `n₊^H = Σ Q 1_{(d⁻²ℓ⁻¹,∞)}(√-Δ) Q`, i.e.
`nPlusH E = Σ_{i ∈ R} nOp i`, is nonnegative as a quadratic form: it is a sum of
the positive operators `n_i = a_i†a_i`. -/
lemma bp_nPlusH_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (E : Q3Env Mode) (f : F.H) :
    0 ≤ F.bp (F.nPlusH E f) f :=
  bp_regionSum_nonneg F ((nPlusHRegion E.ell E.d) ∘ F.kmom) (fun _ => 1)
    (fun _ => zero_le_one) F.nOp (fun i f => bp_nOp_nonneg F i f) f

/-- **The gap-word domination `hgap` at FS's hypotheses.**  The gap word is
`gapOp E = ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H` (`eq:DefT`), so
`(b/100)gapOp E - (1/100)(bℓ⁻²)n₊ = (b/100)ε_T(dℓ)⁻²·n₊^H`, and the latter is
nonnegative as a quadratic form because `b ≥ 0`, `ε_T ≥ 0`, `(dℓ)^(-2:ℝ) ≥ 0`
(`rpow_neg_two_nonneg`) and `n₊^H` is a sum of positive operators
(`bp_nPlusH_nonneg`). -/
lemma gapOp_quadform_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (h : EstHyp F E) (f : F.H) :
    F.bp (((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus f) f
      ≤ F.bp (((E.b / 100) • F.gapOp E) f) f := by
  -- the operator identity: the difference of the two words is the `n₊^H` part
  have hop : ((E.b / 100) • F.gapOp E -
        ((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus)
      = ((E.b / 100) * (E.eT * (E.d * E.ell) ^ (-(2 : ℝ)))) • F.nPlusH E := by
    ext g
    simp only [FockData.gapOp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply]
    module
  -- ... whose quadratic form is nonnegative
  have hnn : 0 ≤ F.bp (((E.b / 100) • F.gapOp E -
      ((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus) f) f := by
    rw [hop]
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    refine mul_nonneg ?_ (bp_nPlusH_nonneg F E f)
    exact mul_nonneg (div_nonneg h.b_nonneg (by norm_num))
      (mul_nonneg h.eT_nonneg (rpow_neg_two_nonneg _))
  -- hence the difference of the two quadratic forms is nonnegative
  have hsub : F.bp (((E.b / 100) • F.gapOp E -
        ((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus) f) f
      = F.bp (((E.b / 100) • F.gapOp E) f) f -
        F.bp ((((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus) f) f := by
    simp only [LinearMap.sub_apply, map_sub, LinearMap.sub_apply]
  rw [hsub] at hnn
  exact sub_nonneg.mp hnn

/-- **FS `thm:Control3Q` from the three estimates, at FS's hypotheses.**
`EstHyp F E` is the kernel hypothesis of `lem:EstimatesOnQ3-js` (already assumed
by the three estimates); from it the three auxiliary inputs of
`Control3Q_of_estimates` are theorems:

* `Q₃ = Q₃⁽¹⁾+Q₃⁽²⁾+Q₃⁽³⁾+Q₃⁽⁴⁾` — `Q3_split`;
* the `P_H`-to-`all` monotonicity of `∫ 𝒟_k b_k†b_k dk` — `dNumOpR_mono` with
  `𝒟 ≥ 0` from `EstHyp.Bsmall` (`|ℬ| ≤ 𝒜 ⟹ 𝒟 ≥ 0`) and the inclusion
  `P_H ⊆ all`;
* the gap domination — `gapOp_quadform_le`.

Hence the three estimates plus FS's arithmetic `ErrDominated` give
`Control3Q F E C` with no further input. -/
theorem Control3Q_of_estimates_at {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (h : Work.BoseB7.EstHyp F E) {C1 C23 C4 C : ℝ}
    (hdom : Work.BoseB7.ErrDominated E C1 C23 C4 C)
    (h1 : Work.BoseB7.EstQ3one F E C1) (h23 : Work.BoseB7.EstQ3twoThree F E C23)
    (h4 : Work.BoseB7.EstQ3four F E C4) :
    Work.BoseB7.Control3Q F E C := by
  -- (i) FS `lem:EstimatesOnQ3-js`: the splitting of `Q₃`
  have hsplit : F.Q3 E = F.Q3one E + F.Q3two E + F.Q3three E + F.Q3four E :=
    Q3_split F E h
  -- (ii) `𝒟_k ≥ 0` (FS `thm:BogHamDiag` with `eq:BoverA`), hence the `P_H`-to-`all`
  -- monotonicity of the diagonalised kinetic operator
  have hD : ∀ i : Mode, 0 ≤ E.D i := fun i =>
    FockData.Dcoef_nonneg (by linarith [h.Bsmall i, abs_nonneg (E.B i)])
  have hkin : ∀ f : F.H, F.bp (F.dNumOpR E (F.PH E.KH E.aScat) f) f ≤
      F.bp (F.dNumOpR E (fun _ => True) f) f := fun f =>
    dNumOpR_mono F E (R := F.PH E.KH E.aScat) (R' := fun _ => True)
      (fun _ _ => trivial) hD f
  -- (iii) the gap word dominates its `n₊` part
  have hgap : ∀ f : F.H,
      F.bp (((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus f) f ≤
        F.bp (((E.b / 100) • F.gapOp E) f) f := fun f => gapOp_quadform_le F E h f
  exact Control3Q_of_estimates F E hsplit hkin hgap hdom h1 h23 h4

end Work.BoseB7
