import Mathlib
import Submission.Work.TMComp.C7Aux.rtlSchedule
import Submission.Work.TMComp.C7Aux.rtl_card_le
import Submission.Work.TMC7Core.Scale.rtlWeightPointwise
import Submission.Work.TMC7Core.Scale.rtlFiberSumLe
import Submission.Work.TMC7Core.Scale.rtlExpGeomSum
import Submission.Work.TMC7Core.Scale.rtlSumFinalArith

namespace Work.TMC7Core.Scale

theorem rtlSumEpsOwn (A cκ b C₀ : ℝ) (Q : ℕ → ℕ) (k N₀ Sb S : ℕ)
    (hA : 0 < A) (hcκ : 0 < cκ) (hb : 0 < b) (hC₀ : 0 ≤ C₀) (hSb : 4 * b / cκ < Sb)
    (hQ1 : ∀ i ≤ k, 1 ≤ Q i)
    (hmono : ∀ i < k, Q i < Q (i+1))
    (hgrowth : ∀ i < k, (Q (i+1) : ℝ) ≤ Real.exp (b * (Q i : ℝ)))
    (hA0 : A * (Q 0 : ℝ) ≤ (N₀ : ℝ))
    (hbig : ∀ i ≤ k, Real.log 10 ≤ cκ * (Q i : ℝ) / 4)
    (hbig2 : ∀ i ≤ k, 2 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)))
    (hS : ∀ t < S, Work.TMComp.C7Aux.rtli A cκ Q k N₀ t < k) :
    (∑ t ∈ Finset.range S,
        (9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q (Work.TMComp.C7Aux.rtli A cκ Q k N₀ t) : ℝ) / 2))
          + 4 * C₀ / (Work.TMComp.C7Aux.rtlMM cκ Q (Work.TMComp.C7Aux.rtli A cκ Q k N₀ t) : ℝ)))
      ≤ (Sb + 1) * (76 * C₀ + 9) * Real.exp (-(cκ * (Q 0 : ℝ) / 2))
          / (1 - Real.exp (-(cκ / 2))) := by
  have hcard : ∀ i < k, ((Finset.range S).filter
      (fun t => Work.TMComp.C7Aux.rtli A cκ Q k N₀ t = i)).card ≤ Sb :=
    fun i hi => Work.TMComp.C7Aux.rtl_card_le A cκ b Q k N₀ Sb hA hcκ hb hQ1 hgrowth hA0
      hbig hbig2 hSb hi S
  have hB₀ : (0 : ℝ) ≤ 76 * C₀ + 9 := by linarith
  have hWnn : ∀ i < k, 0 ≤ 9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q i : ℝ) / 2))
      + 4 * C₀ / (Work.TMComp.C7Aux.rtlMM cκ Q i : ℝ) := by
    intro i hi
    have h41 : (0 : ℝ) ≤ 4 * C₀ + 1 := by linarith
    have hE : (0 : ℝ) ≤ Real.exp (-(cκ * (Q i : ℝ) / 2)) := (Real.exp_pos _).le
    have hMM : (1 : ℝ) ≤ (Work.TMComp.C7Aux.rtlMM cκ Q i : ℝ) := by
      exact_mod_cast Work.TMComp.C7Aux.rtlMM_pos cκ Q (hQ1 i (le_of_lt hi))
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) h41) hE)
      (div_nonneg (by linarith) (by linarith))
  have hWpt : ∀ i < k, 9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q i : ℝ) / 2))
      + 4 * C₀ / (Work.TMComp.C7Aux.rtlMM cκ Q i : ℝ)
      ≤ (76 * C₀ + 9) * Real.exp (-(cκ * (Q i : ℝ) / 2)) :=
    fun i hi => rtlWeightPointwise cκ C₀ Q i hcκ hC₀ (hQ1 i (le_of_lt hi)) (hbig2 i (le_of_lt hi))
  have hsum : (∑ t ∈ Finset.range S,
        (9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q (Work.TMComp.C7Aux.rtli A cκ Q k N₀ t) : ℝ) / 2))
          + 4 * C₀ / (Work.TMComp.C7Aux.rtlMM cκ Q (Work.TMComp.C7Aux.rtli A cκ Q k N₀ t) : ℝ)))
      ≤ (Sb : ℝ) * ∑ i ∈ Finset.range k, (76 * C₀ + 9) * Real.exp (-(cκ * (Q i : ℝ) / 2)) :=
    rtlFiberSumLe k S Sb (fun t => Work.TMComp.C7Aux.rtli A cκ Q k N₀ t)
      (fun i => 9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q i : ℝ) / 2))
        + 4 * C₀ / (Work.TMComp.C7Aux.rtlMM cκ Q i : ℝ))
      (fun i => (76 * C₀ + 9) * Real.exp (-(cκ * (Q i : ℝ) / 2))) hS hcard hWnn hWpt
  have hgeo := rtlExpGeomSum cκ (76 * C₀ + 9) Q k hcκ hB₀ hmono
  have hfin := rtlSumFinalArith cκ C₀ (Q 0) Sb hcκ hC₀
  calc (∑ t ∈ Finset.range S,
        (9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q (Work.TMComp.C7Aux.rtli A cκ Q k N₀ t) : ℝ) / 2))
          + 4 * C₀ / (Work.TMComp.C7Aux.rtlMM cκ Q (Work.TMComp.C7Aux.rtli A cκ Q k N₀ t) : ℝ)))
      ≤ (Sb : ℝ) * ∑ i ∈ Finset.range k, (76 * C₀ + 9) * Real.exp (-(cκ * (Q i : ℝ) / 2)) :=
        hsum
    _ ≤ (Sb : ℝ) * ((76 * C₀ + 9) * Real.exp (-(cκ * (Q 0 : ℝ) / 2))
          * (1 - Real.exp (-(cκ / 2)))⁻¹) :=
        mul_le_mul_of_nonneg_left hgeo (Nat.cast_nonneg Sb)
    _ ≤ (Sb + 1) * (76 * C₀ + 9) * Real.exp (-(cκ * (Q 0 : ℝ) / 2))
          / (1 - Real.exp (-(cκ / 2))) := hfin

end Work.TMC7Core.Scale
