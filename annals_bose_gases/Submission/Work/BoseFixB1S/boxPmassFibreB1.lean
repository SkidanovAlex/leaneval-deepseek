import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.pMassFibSharpB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxPmassFibreB1` — the fibre-weighted `P`-side mass identity

For the FS box projections `P_{B,i} = UBBInputs8.boxPInd volA A i`, the spectral state
`U_i := g(n₀)(P_{B,i}Φ)` with `g(r) = √(r+1) − √c`, and a fibre weight `fib` that is *merely*
measurable and bounded on `A` (no global integrability assumed), the slot sum of the
`fib(xᵢ)`-weighted squares of `U_i` is exactly the fibre average `⦵_A(fib) = (∫_A fib)/volA` times
the unweighted slot sum:

    Σᵢ ∫_{abox N ℓ} fib(xᵢ)·U_i²  =  ((∫_A fib)/volA) · Σᵢ ∫_{abox N ℓ} U_i² .

## Math

Boundedness of `fib` on `A` (which is contained in the cube `acube ℓ` of finite volume) upgrades to
`IntegrableOn fib A` (`IntegrableOn.of_bound`), and then the *per-slot fibre identity*
`Work.BoseFixB1S.perSlotFibIdentity` (proved in `pMassFibSharpB1`) gives the equality slot by slot,
exactly as in the first half of `pMassFibSharpB1`'s proof.  Summing the `N` (or `0`) identities over
the slots and factoring out the constant `⦵_A(fib)` (`Finset.mul_sum`) finishes.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The fibre is integrable on `A` when it is measurable and bounded on `A`, since `A ⊆ acube ℓ`
has finite volume.  (The hypothesis of the target bounds `fib` on `A`, not on the whole cube.) -/
theorem pMassFib_integrableOn_of_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) {fib : E3 → ℝ} (hfm : Measurable fib) {Cf : ℝ}
    (hfb : ∀ z ∈ A, |fib z| ≤ Cf) : IntegrableOn fib A := by
  refine IntegrableOn.of_bound (volume_A_lt_top hℓ hAc) hfm.aestronglyMeasurable |Cf| ?_
  rw [ae_restrict_iff' hA]
  exact Filter.Eventually.of_forall (fun z hz => by
    rw [Real.norm_eq_abs]
    exact le_trans (hfb z hz) (le_abs_self Cf))

theorem boxPmassFibreB1 {N : ℕ} {ℓ volA c : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hc : 0 ≤ c)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib) {Cf : ℝ}
    (hfb : ∀ z ∈ A, |fib z| ≤ Cf)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        fib (x i) * (Work.BoseFixB1S.n0FunOp volA A
          (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (Work.UBBInputs8.boxPInd volA A i Φ)) x ^ 2)
      = ((∫ z in A, fib z) / volA)
        * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (Work.UBBInputs8.boxPInd volA A i Φ)) x ^ 2) := by
  classical
  have hfibA : IntegrableOn fib A :=
    pMassFib_integrableOn_of_bound hℓ hA hAc hfm hfb
  rcases N with _ | n
  · -- no slots: both sides vanish
    simp
  · -- the per-slot fibre identity, summed over the slots
    have hper : ∀ i : Fin (n + 1),
        (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            fib (x i) * (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
          = ((∫ z in A, fib z) / volA) *
              ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.BoseFixB1S.n0FunOp volA A
                  (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                  (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2 :=
      fun i => Work.BoseFixB1S.perSlotFibIdentity hℓ hvol hA hvolA hAc hfibA i hΦc
    calc (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            fib (x i) * (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
        = ∑ i : Fin (n + 1), ((∫ z in A, fib z) / volA) *
              ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.BoseFixB1S.n0FunOp volA A
                  (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                  (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2 :=
            Finset.sum_congr rfl (fun i _ => hper i)
      _ = ((∫ z in A, fib z) / volA) *
            ∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.BoseFixB1S.n0FunOp volA A
                (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2 :=
            (Finset.mul_sum _ _ _).symm

end Work.BoseFixB1S
