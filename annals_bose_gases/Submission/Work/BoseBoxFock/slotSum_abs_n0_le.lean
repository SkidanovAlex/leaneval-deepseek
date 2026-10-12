import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotSum_abs_n0_le`

The slot-sum bound for the condensate projections `Pᵢ = aP ℓ i` on the centred box
`abox n ℓ`:

    ∑_i ∫_{abox n ℓ} |PᵢΦ| · |∑_j PⱼΦ|  ≤  n² · ∫_{abox n ℓ} Φ² .

Proof (elementary, no smoothness needed beyond continuity of `Φ`):

* pointwise `|PᵢΦ| · |∑_j PⱼΦ| ≤ Σ_j |PᵢΦ|·|PⱼΦ|` and the integral of the finite sum is the
  finite sum of the integrals, reducing the left-hand side to the *pair* sum
  `Σ_{i,j} ∫ |PᵢΦ · PⱼΦ|`;
* each ordered pair contributes at most `∫ Φ²` by the pointwise AM–GM
  `2|a||b| ≤ a² + b²` together with the corpus contraction `aP_sq_le`
  (`∫(PᵢΦ)² ≤ ∫ Φ²`, `Submission/Q0Sector.lean`);
* there are `n²` ordered pairs.

The constant is sharp: for constant `Φ` both sides equal `n² ∫ Φ²`.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

open Submission.BoseGases

theorem slotSum_abs_n0_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ i Φ x| * |(∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ x)|
      ≤ (n : ℝ) ^ 2 * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  have hPc : ∀ j : Fin n, Continuous (fun x : X n => aP ℓ j Φ x) := fun j => aP_continuous hℓ j hΦc
  have hScont : Continuous (fun x : X n => |∑ j : Fin n, aP ℓ j Φ x|) :=
    (continuous_finsetSum _ (fun j _ => hPc j)).abs
  -- Each ordered pair contributes at most `∫ Φ²`.
  have hpair : ∀ i j : Fin n,
      (∫ x in abox n ℓ, |aP ℓ i Φ x| * |aP ℓ j Φ x|) ≤ ∫ x in abox n ℓ, (Φ x) ^ 2 := by
    intro i j
    have hii : IntegrableOn (fun x : X n => (aP ℓ i Φ x) ^ 2) (abox n ℓ) volume :=
      integrableOn_abox_of_continuous hℓ ((hPc i).pow 2)
    have hjj : IntegrableOn (fun x : X n => (aP ℓ j Φ x) ^ 2) (abox n ℓ) volume :=
      integrableOn_abox_of_continuous hℓ ((hPc j).pow 2)
    have hf_int : IntegrableOn (fun x : X n => |aP ℓ i Φ x| * |aP ℓ j Φ x|) (abox n ℓ) volume :=
      integrableOn_abox_of_continuous hℓ (((hPc i).abs).mul ((hPc j).abs))
    have hg_int : IntegrableOn
        (fun x : X n => ((aP ℓ i Φ x) ^ 2 + (aP ℓ j Φ x) ^ 2) / 2) (abox n ℓ) volume :=
      integrableOn_abox_of_continuous hℓ ((((hPc i).pow 2).add ((hPc j).pow 2)).div_const 2)
    have hstep : (∫ x in abox n ℓ, |aP ℓ i Φ x| * |aP ℓ j Φ x|)
        ≤ ∫ x in abox n ℓ, ((aP ℓ i Φ x) ^ 2 + (aP ℓ j Φ x) ^ 2) / 2 := by
      refine MeasureTheory.integral_mono hf_int hg_int (fun x => ?_)
      have h := two_mul_le_add_sq |aP ℓ i Φ x| |aP ℓ j Φ x|
      rw [sq_abs, sq_abs] at h
      linarith
    have hval : (∫ x in abox n ℓ, ((aP ℓ i Φ x) ^ 2 + (aP ℓ j Φ x) ^ 2) / 2)
        = ((∫ x in abox n ℓ, (aP ℓ i Φ x) ^ 2)
            + (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2)) / 2 := by
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_add hii.integrable hjj.integrable]
    have hmain : (∫ x in abox n ℓ, ((aP ℓ i Φ x) ^ 2 + (aP ℓ j Φ x) ^ 2) / 2)
        ≤ ∫ x in abox n ℓ, (Φ x) ^ 2 := by
      rw [hval]
      have hi := aP_sq_le hℓ i hΦc
      have hj := aP_sq_le hℓ j hΦc
      linarith
    exact le_trans hstep hmain
  -- Termwise: `|PᵢΦ| · |∑_j PⱼΦ|` integrates to at most the row `Σ_j ∫ |PᵢΦ·PⱼΦ|`.
  have hterm : ∀ i : Fin n,
      (∫ x in abox n ℓ, |aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|)
      ≤ ∑ j : Fin n, ∫ x in abox n ℓ, |aP ℓ i Φ x| * |aP ℓ j Φ x| := by
    intro i
    have hi_cont : Continuous (fun x : X n => |aP ℓ i Φ x|) := (hPc i).abs
    have hL_int : IntegrableOn
        (fun x : X n => |aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|) (abox n ℓ) volume :=
      integrableOn_abox_of_continuous hℓ (hi_cont.mul hScont)
    have hR_int : IntegrableOn
        (fun x : X n => ∑ j : Fin n, |aP ℓ i Φ x| * |aP ℓ j Φ x|) (abox n ℓ) volume :=
      integrableOn_abox_of_continuous hℓ
        (continuous_finsetSum _ (fun j _ => hi_cont.mul (hPc j).abs))
    calc
      (∫ x in abox n ℓ, |aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|)
          ≤ ∫ x in abox n ℓ, ∑ j : Fin n, |aP ℓ i Φ x| * |aP ℓ j Φ x| := by
            refine MeasureTheory.integral_mono hL_int hR_int (fun x => ?_)
            have h1 : |∑ j : Fin n, aP ℓ j Φ x| ≤ ∑ j : Fin n, |aP ℓ j Φ x| :=
              Finset.abs_sum_le_sum_abs (fun j => aP ℓ j Φ x) Finset.univ
            have h2 : 0 ≤ |aP ℓ i Φ x| := abs_nonneg _
            calc |aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|
                ≤ |aP ℓ i Φ x| * (∑ j : Fin n, |aP ℓ j Φ x|) :=
                  mul_le_mul_of_nonneg_left h1 h2
              _ = ∑ j : Fin n, |aP ℓ i Φ x| * |aP ℓ j Φ x| := Finset.mul_sum _ _ _
      _ = ∑ j : Fin n, ∫ x in abox n ℓ, |aP ℓ i Φ x| * |aP ℓ j Φ x| := by
            rw [MeasureTheory.integral_finsetSum]
            exact fun j _ => integrableOn_abox_of_continuous hℓ (hi_cont.mul (hPc j).abs)
  calc
    ∑ i : Fin n, (∫ x in abox n ℓ, |aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|)
        ≤ ∑ i : Fin n, ∑ j : Fin n, (∫ x in abox n ℓ, |aP ℓ i Φ x| * |aP ℓ j Φ x|) :=
          Finset.sum_le_sum (fun i _ => hterm i)
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (∫ x in abox n ℓ, (Φ x) ^ 2) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
    _ = (n : ℝ) ^ 2 * ∫ x in abox n ℓ, (Φ x) ^ 2 := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp only [nsmul_eq_mul]
          ring

end Work.BoseBoxFock
