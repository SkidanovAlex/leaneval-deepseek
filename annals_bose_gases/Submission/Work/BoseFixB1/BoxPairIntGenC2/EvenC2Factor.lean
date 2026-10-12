import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxPairIntGenC2.EvenC2Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.EvenC2Factor`

The factorization of the peeled box pair fibre into the two box indicators and the
*indicator-free* fibre:

    `boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z
        = 1_A(y)·1_A(z)·evenC2Free volA ℓ A Φ i j' y z`   for `y, z ∈ acube ℓ`.

It is the pointwise form of `Work.BoseFixB1S.boxPInd_twoMean` and
`Work.BoseFixB1S.boxQInd_boxQInd_twoMean` on the doubly inserted configuration.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The peeled box pair fibre at the pair `(i, i.succAbove j')`, unfolded. -/
lemma evenC2_fibre_unfold {N : ℕ} (volA ℓ : ℝ) {A : Set E3}
    (Φ : Submission.BoseGases.X (N + 2) → ℝ) (i : Fin (N + 2)) (j' : Fin (N + 1))
    (y z : E3) :
    Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z
      = ∫ r2 in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ)
              (Submission.BoseGases.ins2 i j' y z r2))
            * (Work.UBBInputs8.boxQInd volA A (i.succAbove j')
                (Work.UBBInputs8.boxQInd volA A i Φ)
                (Submission.BoseGases.ins2 i j' y z r2)) := by
  have hs : Submission.BoseGases.sucAboveInv i (i.succAbove j') (Fin.ne_succAbove i j') = j' :=
    Fin.succAbove_right_injective
      (Submission.BoseGases.succAbove_sucAboveInv i (i.succAbove j') (Fin.ne_succAbove i j'))
  rw [Work.BoseFixB1.boxPairFibreFun, dif_pos (Fin.ne_succAbove i j'), hs]

/-- **The factorization of the peeled fibre.**  For `y, z` in the cube the peeled box pair fibre
is the two box indicators times the indicator-free fibre. -/
theorem evenC2_factorization {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1))
    {y z : E3} (hy : y ∈ Submission.BoseGases.acube ℓ) (hz : z ∈ Submission.BoseGases.acube ℓ) :
    Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z
      = Work.BoseFixB1S.Aind A y * Work.BoseFixB1S.Aind A z
        * evenC2Free volA ℓ A Φ i j' y z := by
  have hij : i ≠ i.succAbove j' := Fin.ne_succAbove i j'
  have hij' : i.succAbove j' ≠ i := hij.symm
  rw [evenC2_fibre_unfold, evenC2Free]
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ) fun r2 hr2 => ?_
  have hx : Submission.BoseGases.ins2 i j' y z r2 ∈ Submission.BoseGases.abox (N + 2) ℓ :=
    Submission.BoseGases.ins2_mem_abox i j' hy hz hr2
  have hP := Work.BoseFixB1S.boxPInd_twoMean volA A hij (Φ := Φ)
    (Submission.BoseGases.ins2 i j' y z r2)
  have hQ := Work.BoseFixB1S.boxQInd_boxQInd_twoMean hℓ hvolpos hA hvolA hAc hij' hΦc
    (Submission.BoseGases.ins2 i j' y z r2) hx
  have hxy : Submission.BoseGases.ins2 i j' y z r2 i = y :=
    Submission.BoseGases.ins2_apply_i i j' y z r2
  have hxz : Submission.BoseGases.ins2 i j' y z r2 (i.succAbove j') = z :=
    Submission.BoseGases.ins2_apply_succ i j' y z r2
  have hcomm := @Work.BoseFixB1S.twoMean_comm (N + 2) ℓ volA hℓ A hA hAc (i.succAbove j') i hij'
    Φ hΦc (Submission.BoseGases.ins2 i j' y z r2)
  rw [hP, hQ, hxy, hxz, hcomm]
  simp only [evenC2Integrand]
  have hAy : Work.BoseFixB1S.Aind A y = A.indicator (fun _ => (1 : ℝ)) y := rfl
  have hAz : Work.BoseFixB1S.Aind A z = A.indicator (fun _ => (1 : ℝ)) z := rfl
  rw [hAy, hAz]
  by_cases hyA : y ∈ A
  · rw [Set.indicator_of_mem hyA]
    by_cases hzA : z ∈ A
    · rw [Set.indicator_of_mem hzA]
      ring
    · rw [Set.indicator_of_notMem hzA]
      ring
  · rw [Set.indicator_of_notMem hyA]
    ring

end Work.BoseFixB1.BoxPairIntGenC2
