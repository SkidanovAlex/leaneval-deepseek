import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0ProjOpPartitionEigen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0ProjOp_pairing_sum`

The **pairing-sum (partition) identity** for the subset idempotents of the `n₀` spectral layer.

With `P_S := n0ProjOp volA A S` (the FS box-subset idempotent of `eq:HBU`, the slot iteration
`n0Iter` over `S`), the identity

  `∫_{B} Ψ · (P_S Ψ)  =  Σ_T ∫_{B} (P_T Ψ) · (P_S Ψ)`

is the integrated form of the partition of unity `Σ_T P_T Ψ = Ψ` (`n0ProjOp_sum_eq`, which holds
*pointwise for every* `Ψ`, with no commutation hypothesis).  Nothing about projections,
orthogonality or eigen-properties is used: the whole content is

1. the pointwise expansion `Ψ x · (P_S Ψ) x = Σ_T (P_T Ψ x · (P_S Ψ) x)` obtained by multiplying
   the partition of unity by `(P_S Ψ) x`, and
2. finiteness of the sum, i.e. **integrability of the terms on the box**.  The box is of finite
   measure and each `P_T Ψ` is measurable and bounded on it (`BoxNice.iter`, the closure of
   `BoxNice` under the slot iteration), so `integrableOn_mul_of_bound` supplies the hypothesis of
   `integral_finsetSum`.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

open Submission.BoseGases

theorem n0ProjOp_pairing_sum {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨc : Continuous Ψ)
    (S : Finset (Fin N)) :
    (∫ x in Submission.BoseGases.abox N ℓ, Ψ x * (Work.BoseFixB1S.n0ProjOp volA A S Ψ x))
      = ∑ T : Finset (Fin N), ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.n0ProjOp volA A T Ψ x * Work.BoseFixB1S.n0ProjOp volA A S Ψ x := by
  -- `Ψ` is measurable and bounded on the box.
  have hΨn : BoxNice ℓ Ψ := BoxNice.of_continuous hℓ hΨc
  -- hence so is every slot iterate, in particular `P_S Ψ`.
  have hSn : BoxNice ℓ (n0ProjOp volA A S Ψ) :=
    hΨn.iter hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S)) (List.ofFn (fun i : Fin N => i))
  obtain ⟨hSm, CS, hCS⟩ := hSn
  -- the individual terms of the right-hand sum are integrable on the box.
  have hint : ∀ T : Finset (Fin N), Integrable
      (fun x => n0ProjOp volA A T Ψ x * n0ProjOp volA A S Ψ x)
      ((MeasureTheory.volume : Measure (X N)).restrict (abox N ℓ)) := by
    intro T
    obtain ⟨hTm, CT, hCT⟩ :=
      hΨn.iter hℓ hvol hA hvolA hAc (fun i => decide (i ∈ T)) (List.ofFn (fun i : Fin N => i))
    exact integrableOn_mul_of_bound hℓ hTm hSm hCT hCS
  -- the pointwise identity: the partition of unity, multiplied by `(P_S Ψ) x`.
  have hpt : ∀ x : X N, Ψ x * (n0ProjOp volA A S Ψ x)
      = ∑ T : Finset (Fin N), n0ProjOp volA A T Ψ x * n0ProjOp volA A S Ψ x := by
    intro x
    have h1 : (∑ T : Finset (Fin N), n0ProjOp volA A T Ψ x) = Ψ x := by
      have h := congrFun (n0ProjOp_sum_eq volA A Ψ) x
      simpa [Finset.sum_apply] using h
    rw [← h1, Finset.sum_mul]
  rw [funext hpt]
  exact integral_finsetSum Finset.univ (fun T _ => hint T)

end Work.BoseFixB1S
