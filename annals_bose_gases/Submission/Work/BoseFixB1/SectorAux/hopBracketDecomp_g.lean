import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.SectorAux.GoodStateSpectralPieces
import Submission.Work.BoseFixB1S.hopBracketDecomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorAux.hopBracketDecomp_g`

The FS `eq:Q1n0` **bracket identity** at the box projections of the sliding box, in the weaker
state class `GoodState ℓ` (measurable, bounded on the analysis box) rather than the continuous
one used by the sibling `Work.BoseFixB1S.hopBracketDecomp`.

With `n₀Φ = rungF volA A Φ = Σ_j P_jΦ` (the state of FS `eq:Q1n0`) and `m = μ·volA`,

    Pᵢ(n₀Φ) − (1 + m)·PᵢΦ
      = Σ_{p ∈ hopPairSet i} (|p.1| − 1 − m)·ψ_p ,   ψ_p = boxCompT volA A p.1 p.2 Φ ,

where `hopPairSet i` is the set of disjoint pairs `(S,T)` with `i ∈ S` (`HopDefs`).  The proof is
the exact analogue of `Work.BoseFixB1S.hopBracketDecomp` with the `GoodState` versions of the two
spectral inputs (`boxPInd_eq_sum_boxCompT_goodState`, `boxPInd_boxCompT_goodState`) in place of
the continuous ones; linearity of `Pᵢ` over the finite sum is `boxPInd_finset_sum_gen` (whose
integrability side conditions come from `GoodState` via `slotInt_of_bound`).
-/

namespace Work.BoseFixB1.SectorAux

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem hopBracketDecomp_g {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb) (i : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i (Work.BoseFixB1.rungF volA A Φ) x
        - (1 + μ * volA) * (Work.UBBInputs8.boxPInd volA A i Φ x)
      = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          ((p.1.card : ℝ) - 1 - μ * volA) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
  intro x hx
  classical
  have hΦg : Work.BoseFixB1S.GoodState ℓ Φ := ⟨hΦm, Cb, hΦb⟩
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) :=
    fun p => Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦg
  have hset : Work.BoseFixB1S.hopPairSet i
      = (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1) := rfl
  -- Scalar pull-out for the box projection.
  have hsmul : ∀ (c : ℝ) (Ψ : Submission.BoseGases.X N → ℝ),
      Work.UBBInputs8.boxPInd volA A i (fun y => c * Ψ y) x
        = c * Work.UBBInputs8.boxPInd volA A i Ψ x := by
    intro c Ψ
    simp only [Work.UBBInputs8.boxPInd]
    rw [MeasureTheory.integral_const_mul]
    ring
  -- The joint-component expansion of `n₀Φ = rungF volA A Φ`.
  have hdecomp : ∀ y ∈ Submission.BoseGases.abox N ℓ,
      Work.BoseFixB1.rungF volA A Φ y
        = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
            (p.1.card : ℝ) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y := by
    intro y hy
    simp only [Work.BoseFixB1.rungF]
    rw [Work.BoseFixB1S.sum_card_mul_eq_sum_j (N := N)
      (fun p => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine (boxPInd_eq_sum_boxCompT_goodState hℓ hvol hA hvolA hAc hΦg j y hy).trans ?_
    rw [Finset.sum_filter]
  -- (a) `PᵢΦ = Σ_{p ∋ i} ψ_p`.
  have hPi : Work.UBBInputs8.boxPInd volA A i Φ x
      = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
    rw [hset]
    exact boxPInd_eq_sum_boxCompT_goodState hℓ hvol hA hvolA hAc hΦg i x hx
  -- (b) `Pᵢ(n₀Φ) = Σ_{p ∋ i} |p.1|·ψ_p`.
  have hPeig : Work.UBBInputs8.boxPInd volA A i (Work.BoseFixB1.rungF volA A Φ) x
      = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          (p.1.card : ℝ) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
    rw [hset]
    rw [Work.BoseFixB1S.agreeBox_boxPInd hA hAc i hdecomp x hx]
    have hInt : ∀ p ∈ Work.BoseFixB1S.disjPairs N,
        IntegrableOn (fun z => (p.1.card : ℝ) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ
          (Function.update x i z)) A volume := by
      intro p _
      obtain ⟨C, hC⟩ := (hG p).2
      exact Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx
        (f := fun y => (p.1.card : ℝ) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y)
        (measurable_const.mul (hG p).1)
        (fun y hy => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hC y hy) (abs_nonneg _))
    rw [Work.BoseFixB1S.boxPInd_finset_sum_gen volA A i x (Work.BoseFixB1S.disjPairs N)
      (fun p => fun y => (p.1.card : ℝ) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y) hInt]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hsmul, boxPInd_boxCompT_goodState hℓ hvol hA hvolA hAc p.1 p.2 hΦg i x hx]
    by_cases hi : i ∈ p.1 <;> simp [hi]
  rw [hPeig, hPi, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

end Work.BoseFixB1.SectorAux
