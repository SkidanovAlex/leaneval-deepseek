import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0PairingZeroNice
import Submission.Work.BoseFixB1S.n0ProjOpOrthB1
import Submission.Work.BoseFixB1S.n0SpectralMomentsB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

open Submission.BoseGases

theorem sqIntegralProjSumLe {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin N) {w : Submission.BoseGases.X N → ℝ} (hw : Work.BoseFixB1S.GoodState ℓ w)
    (hwfix : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i w x = w x)
    (c : Finset (Fin N) → ℝ)
    (hc : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => i ∈ S), |c S| ≤ 1) :
    ∫ x in Submission.BoseGases.abox N ℓ,
        (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => i ∈ S),
          c S * Work.BoseFixB1S.n0ProjOp volA A S w x) ^ 2
      ≤ ∫ x in Submission.BoseGases.abox N ℓ, w x ^ 2 := by
  classical
  obtain ⟨hwm, Cw, hwb⟩ := hw
  have hwG : GoodState ℓ w := ⟨hwm, Cw, hwb⟩
  -- the index set: the subsets of slots containing `i`
  set s : Finset (Finset (Fin N)) := Finset.univ.filter (fun S : Finset (Fin N) => i ∈ S) with hs
  -- pairwise integrability and orthogonality of the sector functions `P_S w`
  have hint : ∀ p ∈ s, ∀ q ∈ s, IntegrableOn
      (fun x : Submission.BoseGases.X N => n0ProjOp volA A p w x * n0ProjOp volA A q w x)
      (abox N ℓ) volume :=
    fun p _ q _ => n0ProjOp_pairing_integrableB1 hℓ hvol hA hvolA hAc hwG p q
  have horth : ∀ p ∈ s, ∀ q ∈ s, p ≠ q →
      (∫ x in abox N ℓ, n0ProjOp volA A p w x * n0ProjOp volA A q w x) = 0 :=
    fun p _ q _ hpq => n0PairingZeroNice hℓ hvol hA hvolA hAc hwm hwb hpq
  -- weighted Parseval on the orthogonal family
  have hW := boxSqSumWeightedOrthB1_self (s := s)
    (f := fun S : Finset (Fin N) => n0ProjOp volA A S w) (c := c) hint horth
  -- Pythagoras on the same family
  have hpy := integral_sq_sum_of_orth (s := s)
    (f := fun S : Finset (Fin N) => n0ProjOp volA A S w) hint horth
  -- the one-slot identity: the sectors containing `i` resolve `P_{B,i}w = w`
  have hsq : ∀ x ∈ abox N ℓ, (∑ p ∈ s, n0ProjOp volA A p w x) = w x := by
    intro x hx
    rw [← n0ProjOp_pInd_sum_filter hℓ hvol hA hvolA hAc hwG i x hx, hwfix x hx]
  have hsqint : (∫ x in abox N ℓ, (∑ p ∈ s, n0ProjOp volA A p w x) ^ 2)
      = ∫ x in abox N ℓ, w x ^ 2 :=
    setIntegral_congr_fun (abox_measurable N ℓ) (fun x hx => by rw [hsq x hx])
  calc (∫ x in abox N ℓ,
        (∑ p ∈ s, c p * n0ProjOp volA A p w x) ^ 2)
      = ∑ p ∈ s, c p ^ 2 * (∫ x in abox N ℓ, n0ProjOp volA A p w x ^ 2) := hW
    _ ≤ ∑ p ∈ s, ∫ x in abox N ℓ, n0ProjOp volA A p w x ^ 2 :=
        Finset.sum_le_sum (fun p hp =>
          mul_le_of_le_one_left (integral_nonneg (fun x => sq_nonneg _))
            (sq_le_one_iff_abs_le_one (c p) |>.mpr (hc p hp)))
    _ = ∫ x in abox N ℓ, (∑ p ∈ s, n0ProjOp volA A p w x) ^ 2 := hpy.symm
    _ = ∫ x in abox N ℓ, w x ^ 2 := hsqint

end Work.BoseFixB1S
