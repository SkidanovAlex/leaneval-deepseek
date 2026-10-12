import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRow_pairSlot_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairSlot_twoDouble`

The χ-row pair slot form `pairSlot` (`Submission/Work/BoseBoxFock/chiRowDefs.lean`) is **twice** the
double slot sum

    `Σ_{i,j} ∫_{abox} (P_iΦ)(x)·w(x_i)·(P_jΦ)(x)` .

Indeed `pairSlot = pairHalfOne + pairHalfTwo` and `pairHalfOne = pairHalfTwo`
(`chiRow_pairSlot_split`), while the *second* orientation `pairHalfTwo` is computed directly as the
double slot sum by the box slot self-adjointness `aP_sym_sum_pt_of_boundOn` (the inner pair weight
`w(x_i)·Σ_j P_jΦ` is only measurable, bounded on the box — never continuous).  Hence
`pairSlot = 2·Σ_{i,j}∫(P_iΦ)w(x_i)(P_jΦ)`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- **`pairHalfTwo` is the double slot sum.**  The `|e₀⟩⟨η_w| ∘ n₀` orientation of the pair slot
form, expanded through the slot self-adjointness over the box. -/
lemma pairHalfTwo_eq_doubleSum {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ}
    (hΦc : Continuous Φ) {w : Sp → ℝ} (hwm : Measurable w) {K : ℝ} (hw : ∀ x, |w x| ≤ K) :
    pairHalfTwo n ℓ w Φ
      = ∑ i : Fin n, ∑ j : Fin n,
          ∫ x in abox n ℓ, (aP ℓ i Φ x) * w (x i) * (aP ℓ j Φ x) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg (w 0)) (hw 0)
  choose C hC0 hCb using fun j : Fin n => exists_bound_aP (ℓ := ℓ) hℓ j hΦc
  -- measurability of the second pair weight
  have hW2m : ∀ i : Fin n, Measurable (pairWtTwo n ℓ w Φ i) := fun i =>
    (hwm.comp (measurable_pi_apply i)).mul
      (Finset.measurable_sum _ (fun j _ => (aP_continuous hℓ j hΦc).measurable))
  -- bounds on the box
  have hW2b : ∀ i : Fin n, ∀ x ∈ abox n ℓ, |pairWtTwo n ℓ w Φ i x| ≤ K * ∑ j : Fin n, C j := by
    intro i x hx
    have hS : |∑ j : Fin n, aP ℓ j Φ x| ≤ ∑ j : Fin n, C j := by
      calc |∑ j : Fin n, aP ℓ j Φ x| ≤ ∑ j : Fin n, |aP ℓ j Φ x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin n, C j := Finset.sum_le_sum (fun j _ => hCb j x hx)
    calc |pairWtTwo n ℓ w Φ i x| = |w (x i)| * |∑ j : Fin n, aP ℓ j Φ x| := abs_mul _ _
      _ ≤ K * ∑ j : Fin n, C j := mul_le_mul (hw (x i)) hS (abs_nonneg _) hK
  have hD2 : 0 ≤ K * ∑ j : Fin n, C j :=
    mul_nonneg hK (Finset.sum_nonneg (fun j _ => hC0 j))
  -- the slot self-adjointness distributes the outer sum
  have hTwoL : pairHalfTwo n ℓ w Φ
      = ∑ i : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ x) * pairWtTwo n ℓ w Φ i x := by
    rw [pairHalfTwo_eq]
    exact aP_sym_sum_pt_of_boundOn (n := n) (ℓ := ℓ) (F := pairWtTwo n ℓ w Φ)
      hℓ hΦc hW2m hD2 hW2b
  -- expansion of the pair weight inside the slot integral
  have hTwoL2 : (∑ i : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ x) * pairWtTwo n ℓ w Φ i x)
      = ∑ i : Fin n, ∑ j : Fin n,
          ∫ x in abox n ℓ, (aP ℓ i Φ x) * w (x i) * (aP ℓ j Φ x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∫ x in abox n ℓ, (aP ℓ i Φ x) * pairWtTwo n ℓ w Φ i x)
        = ∫ x in abox n ℓ, ∑ j : Fin n, (aP ℓ i Φ x) * w (x i) * (aP ℓ j Φ x) from by
      apply integral_congr_ae
      filter_upwards with x
      rw [show pairWtTwo n ℓ w Φ i x = w (x i) * (∑ j : Fin n, aP ℓ j Φ x) from rfl,
        ← mul_assoc, Finset.mul_sum]]
    rw [integral_finsetSum]
    intro j _
    exact integrableOn_cont_slot_bounded hℓ i (aP_continuous hℓ i hΦc)
      (aP_continuous hℓ j hΦc) hwm hw
  exact hTwoL.trans hTwoL2

theorem pairSlot_twoDouble {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hwm : Measurable w) {K : ℝ}
    (hw : ∀ x, |w x| ≤ K) :
    Work.BoseBoxFock.pairSlot n ℓ w Φ
      = 2 * ∑ i : Fin n, ∑ j : Fin n,
          ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x * w (x i) * (Submission.BoseGases.aP ℓ j Φ x) := by
  obtain ⟨hsplit, hheq⟩ := chiRow_pairSlot_split hℓ hΦc hwm hw
  have hhalf := pairHalfTwo_eq_doubleSum (n := n) (ℓ := ℓ) hℓ hΦc hwm hw
  rw [hsplit, hheq, hhalf]
  ring

end Work.BoseBoxFock
