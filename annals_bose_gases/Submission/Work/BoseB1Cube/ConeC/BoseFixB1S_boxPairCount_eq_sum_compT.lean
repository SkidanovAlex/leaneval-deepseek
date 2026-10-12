import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxQCount_eq_sum_compT
import Submission.Work.BoseFixB1S.boxFlatCount_eq_sum_compT
import Submission.Work.BoseFixB1S.boxPInd_finset_sum_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The counting identity on `pairSet` -/

/-- The number of ordered pairs `(i,j)` of **distinct** indices with `i, j ∈ S`, weighted by `c`:
`Σ_{q ∈ pairSet N} [q.1 ∈ S][q.2 ∈ S]·c = |S|(|S| − 1)·c`. -/
theorem sum_pairSet_ite_mem_sq {N : ℕ} (S : Finset (Fin N)) (c : ℝ) :
    (∑ q ∈ pairSet N, (if q.1 ∈ S ∧ q.2 ∈ S then c else 0))
      = ((S.card : ℝ) * ((S.card : ℝ) - 1)) * c := by
  classical
  have h1 : (∑ q ∈ pairSet N, (if q.1 ∈ S ∧ q.2 ∈ S then c else 0))
      = (∑ q ∈ pairSet N, (if q.1 ∈ S ∧ q.2 ∈ S then (1 : ℝ) else 0)) * c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : q.1 ∈ S ∧ q.2 ∈ S <;> simp [h]
  have h2 : (∑ q ∈ pairSet N, (if q.1 ∈ S ∧ q.2 ∈ S then (1 : ℝ) else 0))
      = ((S.offDiag).card : ℝ) := by
    have hset : (pairSet N).filter (fun q => q.1 ∈ S ∧ q.2 ∈ S) = S.offDiag :=
      Finset.ext (fun q => by
        simp only [Finset.mem_filter, Finset.mem_offDiag, pairSet, Finset.mem_univ, true_and]
        tauto)
    rw [Finset.sum_boole, hset]
  rw [h1, h2, Finset.offDiag_card]
  by_cases hc : S.card = 0
  · simp [hc]
  · have h1 : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr hc
    have h2 : S.card * S.card - S.card = S.card * (S.card - 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [h2, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_one]

/-- **The counting/swap identity of the pair count.**  Summing over the ordered pairs
`q ∈ pairSet N` the mass of the components whose `P`-slot set contains *both* entries of `q`
and exchanging the two finite sums gives, for each component, the multiplicity
`|p.1|(|p.1| − 1)` of ordered index pairs it carries. -/
theorem sum_pairSet_filter_disjPairs {N : ℕ}
    (F : Finset (Fin N) × Finset (Fin N) → ℝ) :
    (∑ q ∈ pairSet N,
        ∑ p ∈ (disjPairs N).filter (fun p => q.1 ∈ p.1 ∧ q.2 ∈ p.1), F p)
      = ∑ p ∈ disjPairs N, ((p.1.card : ℝ) * ((p.1.card : ℝ) - 1)) * F p := by
  classical
  calc (∑ q ∈ pairSet N,
          ∑ p ∈ (disjPairs N).filter (fun p => q.1 ∈ p.1 ∧ q.2 ∈ p.1), F p)
      = ∑ q ∈ pairSet N, ∑ p ∈ disjPairs N,
            (if q.1 ∈ p.1 ∧ q.2 ∈ p.1 then F p else 0) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.sum_filter]
    _ = ∑ p ∈ disjPairs N, ∑ q ∈ pairSet N,
            (if q.1 ∈ p.1 ∧ q.2 ∈ p.1 then F p else 0) := Finset.sum_comm
    _ = ∑ p ∈ disjPairs N, ((p.1.card : ℝ) * ((p.1.card : ℝ) - 1)) * F p := by
        apply Finset.sum_congr rfl
        intro p _
        exact sum_pairSet_ite_mem_sq p.1 (F p)

/-! ## 2. The single-ordered-pair spectral identity -/

/-- **The per-ordered-pair spectral identity** `(★★)`: on the box,
`PᵢPⱼΦ = Σ_{p : i, j ∈ p.1} ψ_p`, and the joint components of distinct disjoint pairs are
orthogonal there, so the box `L²`-norm of `PᵢPⱼΦ` is the sum of the squared norms of the
components whose `P`-slot set contains both `i` and `j`. -/
theorem integral_sq_boxPInd_pair_eq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) (i j : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
      = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.1),
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  have hΦG : GoodState ℓ Φ := goodState_of_continuous hℓ hΦc
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      GoodState ℓ (boxCompT volA A p.1 p.2 Φ) :=
    fun p => goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦG
  -- the pointwise component decomposition of `PᵢPⱼΦ` on the box
  have hpt : ∀ x ∈ abox N ℓ,
      UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Φ) x
        = ∑ p ∈ (disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.1),
            boxCompT volA A p.1 p.2 Φ x := by
    intro x hx
    have hPj := boxPInd_eq_sum_boxCompT hℓ hvol hA hvolA hAc hΦc j
    calc UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Φ) x
        = UBBInputs8.boxPInd volA A i
            (fun y => ∑ p ∈ (disjPairs N).filter (fun p => j ∈ p.1),
              boxCompT volA A p.1 p.2 Φ y) x :=
            agreeBox_boxPInd hA hAc i hPj x hx
      _ = ∑ p ∈ (disjPairs N).filter (fun p => j ∈ p.1),
            UBBInputs8.boxPInd volA A i (boxCompT volA A p.1 p.2 Φ) x :=
            boxPInd_finset_sum_gen volA A i x
              ((disjPairs N).filter (fun p => j ∈ p.1))
              (fun p => boxCompT volA A p.1 p.2 Φ)
              (fun p _ => slotInt_of_bound hℓ hA hAc i x hx (hG p).1 (hG p).2.choose_spec)
      _ = ∑ p ∈ (disjPairs N).filter (fun p => j ∈ p.1),
            (if i ∈ p.1 then boxCompT volA A p.1 p.2 Φ x else 0) :=
            Finset.sum_congr rfl
              (fun p _ => boxPInd_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦc i x hx)
      _ = ∑ p ∈ (disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.1),
            boxCompT volA A p.1 p.2 Φ x := by
            conv_lhs => rw [Finset.sum_filter (s := disjPairs N) (p := fun p => j ∈ p.1)
              (f := fun p => if i ∈ p.1 then boxCompT volA A p.1 p.2 Φ x else 0)]
            conv_rhs => rw [Finset.sum_filter (s := disjPairs N)
              (p := fun p => i ∈ p.1 ∧ j ∈ p.1)
              (f := fun p => boxCompT volA A p.1 p.2 Φ x)]
            apply Finset.sum_congr rfl
            intro p _
            by_cases hi : i ∈ p.1 <;> by_cases hj : j ∈ p.1 <;> simp [hi, hj]
  calc (∫ x in abox N ℓ,
          (UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
      = ∫ x in abox N ℓ,
          (∑ p ∈ (disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.1),
            boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          setIntegral_congr_fun (abox_measurable N ℓ) (fun x hx => by rw [hpt x hx])
    _ = ∑ p ∈ (disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.1),
          ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          integral_sum_compT_sq hℓ hvol hA hvolA hAc hΦc _
            (fun p hp => mem_disjPairs.mp (Finset.mem_filter.mp hp).1)

/-! ## 3. The pair-condensate count -/

theorem boxPairCount_eq_sum_compT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    Work.BoseFixB1S.boxPairCount volA ℓ A Φ
      = ∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
            (fun p => Disjoint p.1 p.2),
          ((p.1.card : ℝ) * ((p.1.card : ℝ) - 1))
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  show (∑ q ∈ pairSet N,
      ∫ x in abox N ℓ,
        (UBBInputs8.boxPInd volA A q.1 (UBBInputs8.boxPInd volA A q.2 Φ) x) ^ 2)
    = ∑ p ∈ disjPairs N,
          ((p.1.card : ℝ) * ((p.1.card : ℝ) - 1))
            * ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2
  calc (∑ q ∈ pairSet N,
        ∫ x in abox N ℓ,
          (UBBInputs8.boxPInd volA A q.1 (UBBInputs8.boxPInd volA A q.2 Φ) x) ^ 2)
      = ∑ q ∈ pairSet N,
          ∑ p ∈ (disjPairs N).filter (fun p => q.1 ∈ p.1 ∧ q.2 ∈ p.1),
            ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
        Finset.sum_congr rfl
          (fun q _ => integral_sq_boxPInd_pair_eq hℓ hvol hA hvolA hAc hΦc q.1 q.2)
    _ = ∑ p ∈ disjPairs N,
          ((p.1.card : ℝ) * ((p.1.card : ℝ) - 1))
            * ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
        sum_pairSet_filter_disjPairs
          (fun p => ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2)

end Work.BoseFixB1S
