import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Submission.Work.BoseB7A.SubstHyp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Q3fourT_eq_weight_sum` — FS `lem:EstimatesOnQ3-js`, piece 4, in the θ-mode slot

`T.Q3fourT E` is the double sum over the low-momentum slot `s ∈ excited Mode` and the
high-momentum slot `k ∈ P_H` of

`-(f_L(s)Ŵ₁(k)α_k q3Denom s k) • ([b_{s−k}, b_{−k}†] ∘ (ã_s† + ã_s))`,

and `[b_{s−k}, b_{−k}†]` is the *scalar* `ccrK (s−k) (−k) − α_{s−k}α_{−k}ccrK k (k−s)`
(`bCommutator_eq`) which FS `eq:Commutator_general` rewrites into the `χ̂`-combination

`(1 − α_{s−k}α_{−k})χ̂²(s) − χ̂(s−k)χ̂(−k) + α_{s−k}α_{−k}χ̂(k)χ̂(k−s)`.

Summing the scalar over `k` identifies `T.Q3fourT E` with the *linear* word
`(z/ℓ³) Σ_s q3fourWeightSplit(s) • (ã_s† + ã_s)`.  This is the θ-mode analogue of
`BoseB7.Q3four_eq_weight_sum`; the only change is that the `s`-slot carries FS's
`ã_s` rather than the χ-mode `a_s`, so the whole (B7) argument applies verbatim with
`a_aDag`/`a` replaced by `ta`/`taDag` — the scalar commutator never sees them.

`SubstHyp` is the only hypothesis used, via its single field `hasKernel`
(FS `eq:Commutator_general`); no parity/denominator field is needed here.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

theorem Q3fourT_eq_weight_sum {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (h : Work.BoseB7A.SubstHyp F T E) :
    T.Q3fourT E = (E.z / E.ell ^ 3) • ∑ s ∈ Work.BoseB7.excited Mode,
      (F.q3fourWeightSplit E s) • (T.taDag s + T.ta s) := by
  -- unfold the word `Q₃⁽⁴⁾` and cancel the common prefactor `z/ℓ³`
  rw [Work.BoseB7A.TildeData.Q3fourT]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  -- the `k`-sum at fixed `s`: turn the right-hand coefficient into a `k`-sum too
  rw [Work.BoseB7.FockData.q3fourWeightSplit, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k _
  -- `[b_{s−k}, b_{−k}†]` is the scalar `ccrK (s−k) (−k) − α_{s−k}α_{−k}ccrK k (k−s)`
  rw [Work.BoseB7.bCommutator_eq F E s k]
  -- FS `eq:Commutator_general` turns the scalar into the FS `χ̂`-combination
  have hw : F.ccrK (s - k) (-k) - E.alpha (s - k) * E.alpha (-k) * F.ccrK k (k - s) =
      (1 - E.alpha (s - k) * E.alpha (-k)) * E.hatChiSq s
        - E.hatChi (s - k) * E.hatChi (-k)
        + E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s)) := by
    rw [h.hasKernel (s - k) (-k), h.hasKernel k (k - s),
      show (s - k) - (-k) = s from by abel, show k - (k - s) = s from by abel]
    ring
  rw [hw]
  -- both sides are now a scalar times `(ã_s† + ã_s)`; what is left is scalar arithmetic
  ext f
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, Module.End.one_apply, smul_smul]
  rw [mul_comm]

end Work.BoseB7A
