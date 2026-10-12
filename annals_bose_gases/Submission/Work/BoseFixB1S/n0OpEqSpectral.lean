import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0BoxPIndFinsetSum
import Submission.Work.BoseFixB1S.n0ProjOpPartitionEigen
import Submission.Work.BoseFixB1S.n0SumCardFiber
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0OpEqSpectral`

The **functional calculus for `n₀` at the identity**, on the analysis box.

With `P_{B,i} = UBBInputs8.boxPInd volA A i` (FS `eq:HBU`), `n₀ = Σ_i P_{B,i}` (`n0Op`) and the
Lagrange idempotents `n0LagrangeOp volA A k` of `n0ProjOpPartitionEigen`, this file proves that a
*continuous* state `Ψ` is a.e. (on the box `abox N ℓ`) the Lagrange decomposition of `n₀`:

  `n₀Ψ = Σ_{k ≤ N} k • (n0LagrangeOp k Ψ)`,

i.e. `n0Op = n0FunOp (fun r => r)` on the box.  Together with the `√`-instance
(`g = fun r => Real.sqrt (r+1)`) this is the spectral input the sharp FS completion of squares
consumes.

## Proof

`Ψ = Σ_S n0ProjOp S Ψ` as functions (`n0ProjOp_sum_eq`, pure composition algebra, no measure
theory).  On the box the eigen-property `P_j (n0ProjOp S Ψ) = 1_S(j) · n0ProjOp S Ψ`
(`n0IterEigen`) holds *pointwise*.  What is needed on top is that `P_j` is additive over the
finite sum `Σ_S n0ProjOp S Ψ` of box-bounded states — this is
`Work.BoseFixB1S.n0BoxPIndFinsetSum` (integral of a finite sum, then distribute the constant
factors).  Summing the eigen-property over `j` and swapping the two finite sums gives
`n₀Ψ = Σ_S (card S) • (n0ProjOp S Ψ)`, and the regrouping by cardinality
(`Work.BoseFixB1S.n0SumCardFiber`) turns this into the stated `Σ_{k ≤ N} k • (n0LagrangeOp k Ψ)`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

theorem n0OpEqSpectral {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨc : Continuous Ψ) :
    (fun x => Work.BoseFixB1S.n0Op volA A Ψ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
        fun x => ∑ k ∈ Finset.range (N + 1),
          (k : ℝ) * ((Work.BoseFixB1S.n0LagrangeOp volA A k) Ψ x) := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hΨc.continuousOn
  have hG : GoodState ℓ Ψ :=
    ⟨hΨc.measurable, C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  have hφG : ∀ S : Finset (Fin N), GoodState ℓ (n0ProjOp volA A S Ψ) := fun S =>
    BoxNice.iter hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S)) hG
      (List.ofFn (fun i : Fin N => i))
  filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
  have hmain : n0Op volA A Ψ x
      = ∑ S : Finset (Fin N), (S.card : ℝ) * n0ProjOp volA A S Ψ x := by
    calc n0Op volA A Ψ x
        = ∑ j : Fin N, UBBInputs8.boxPInd volA A j Ψ x := rfl
      _ = ∑ j : Fin N, UBBInputs8.boxPInd volA A j
            (∑ S : Finset (Fin N), n0ProjOp volA A S Ψ) x := by
          apply Finset.sum_congr rfl
          intro j _
          rw [n0ProjOp_sum_eq]
      _ = ∑ j : Fin N, ∑ S : Finset (Fin N),
            UBBInputs8.boxPInd volA A j (n0ProjOp volA A S Ψ) x := by
          apply Finset.sum_congr rfl
          intro j _
          exact n0BoxPIndFinsetSum hℓ hvol hA hvolA hAc Finset.univ
            (fun S => n0ProjOp volA A S Ψ) (fun S _ => hφG S) j hx
      _ = ∑ j : Fin N, ∑ S : Finset (Fin N),
            (if j ∈ S then n0ProjOp volA A S Ψ x else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro S _
          exact n0IterEigen hℓ hvol hA hvolA hAc S hG j x hx
      _ = ∑ S : Finset (Fin N), ∑ j : Fin N,
            (if j ∈ S then n0ProjOp volA A S Ψ x else 0) := Finset.sum_comm
      _ = ∑ S : Finset (Fin N), (S.card : ℝ) * n0ProjOp volA A S Ψ x := by
          apply Finset.sum_congr rfl
          intro S _
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [hmain]
  simp only [n0LagrangeOp]
  exact n0SumCardFiber (fun S => n0ProjOp volA A S Ψ x)

end Work.BoseFixB1S
