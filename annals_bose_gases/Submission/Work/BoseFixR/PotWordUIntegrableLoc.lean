import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.integrableOn_chemP_loc
import Submission.Work.BoseFixR.integrableOn_wPairC_pair_loc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.PotWordUIntegrableLoc`

The bare multiplicative word of FS `eq:Def_HB`,

    potWordU N v g ℓ μ 0 x = -μ Σ_i ∫_y w_{1}(x_i,y) dy + Σ_{i<j} w(x_i,x_j),

is **integrable on the box `abox N ℓ`** for `0 < ℓ` and *locally integrable* `v`, `g` —
with no support-radius/diluteness hypothesis (`R ≤ ℓ·r₀`) and no global `L¹`-hypothesis.

This is the "no support hypothesis" form of `Work.BoseFixB2.Pot.potWordU_integrable` /
`Work.BoseFixB2.Energy.potWordU_integrable_b2`, and it is what
`Work.BoseFixR.PotSplit` consumes.

## Why it is true (and why only local integrability is needed)

`wLoc ℓ h 0` is the χ-renormalised kernel `wPairC ℓ h a b = χ_ℓ(a)·h(a−b)/(χ⋆χ)_ℓ(a−b)·χ_ℓ(b)`.
The quotient `h/(χ⋆χ)_ℓ` is a *singular* factor — `(χ⋆χ)_ℓ` vanishes for `‖z‖ ≥ ℓ` — so a pointwise
bound by `|h|` is impossible and one must use the cancellation of the two `χ_ℓ` factors against the
denominator **inside the joint integral**: with our choice of `χ` (`chiBump.rOut = 1/2`) we have
`chiScale ℓ a ≠ 0 → ‖a‖ ≤ ℓ/2`, so when both cutoffs are live, `‖a − b‖ ≤ ℓ`: the numerator `h` is
only ever probed on the compact ball `closedBall 0 ℓ`.  Hence *local* integrability of `h`
suffices; `lintegral_wPairC_acube_le` is exactly that statement.

## Structure

1. `n` particles: `potWordU` is rewritten as `Σ_i (−μ)·chemP ℓ g (x i) + Σ_{i<j} wPairC ℓ v (x i) (x j)`
   (`chemP ℓ g a = ∫_y wPairC ℓ g a y`); this uses the definitional identity `wLoc 0 = wPairC`
   (`Work.BoseFixR.wLoc_zero_eq_wPairC`).
2. The one-body terms are integrable on the box (`Work.BoseFixR.integrableOn_chemP_loc`); the
   Bochner integral is compared with its `enorm` majorant `chemQ` and the `∫⁻`-bound of
   `lintegral_wPairC_acube_le` is applied over `acube ℓ` after peeling one coordinate.
3. The pair terms are integrable on the box (`Work.BoseFixR.integrableOn_wPairC_pair_loc`);
   peel two coordinates and apply `lintegral_wPairC_acube_le` over `acube ℓ × acube ℓ`.
4. Finite sums of integrable functions are integrable.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BoseFixR

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem PotWordUIntegrableLoc {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {v g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : MeasureTheory.LocallyIntegrable v) (hg : MeasureTheory.LocallyIntegrable g) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => Work.BoseKinLoc.potWordU N v g ℓ μ 0 x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  -- the pointwise block form of the bare word
  have hpot : ∀ x : Submission.BoseGases.X N,
      Work.BoseKinLoc.potWordU N v g ℓ μ 0 x
        = (∑ i : Fin N, (-μ) * chemP ℓ g (x i))
          + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
              Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2) := by
    intro x
    have hc : (∑ i : Fin N, ∫ y : E3, Submission.BoseGases.wLoc ℓ g 0 (x i) y)
        = ∑ i : Fin N, chemP ℓ g (x i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [chemP_eq_wLoc_integral]
    have hp : (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
          Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2))
        = ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
            Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2) := by
      apply Finset.sum_congr rfl
      intro ij _
      exact wLoc_zero_eq_wPairC ℓ v (x ij.1.1) (x ij.1.2)
    rw [Work.BoseKinLoc.potWordU, hc, hp, Finset.mul_sum]
  refine MeasureTheory.Integrable.congr (f := fun x : Submission.BoseGases.X N =>
      (∑ i : Fin N, (-μ) * chemP ℓ g (x i))
        + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
            Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2)) ?_ ?_
  · exact (MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin N))
        (fun i _ => (integrableOn_chemP_loc hℓ hg i).const_mul (-μ))).add
      (MeasureTheory.integrable_finsetSum
        (Finset.univ : Finset {ij : Fin N × Fin N | ij.1 < ij.2})
        (fun ij _ => integrableOn_wPairC_pair_loc hℓ hv (ne_of_lt ij.2)))
  · exact Filter.Eventually.of_forall (fun x => (hpot x).symm)

end Work.BoseFixR
