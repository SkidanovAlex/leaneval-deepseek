import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumA1ZeroSmall
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.t1SlotTermZ
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.RowAdzCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-- The double binomial sum is the constant `2^a·2^b`. -/
theorem rowA_choose_sum {a b : ℕ} (Y : ℝ) :
    (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ)) * Y)
      = ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * Y := by
  have hchoose : ∀ n : ℕ,
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
    intro n
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  calc (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ)) * Y)
      = ∑ i ∈ Finset.range (a + 1),
          (∑ j ∈ Finset.range (b + 1), (a.choose i : ℝ) * (b.choose j : ℝ)) * Y := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.sum_mul]
    _ = (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (a.choose i : ℝ) * (b.choose j : ℝ)) * Y := by rw [Finset.sum_mul]
    _ = ((∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ))
          * (∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ))) * Y := by
        rw [← Finset.sum_mul_sum]
    _ = ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * Y := by rw [hchoose a, hchoose b]

/-- **The assembly of the row**: the Leibniz expansion, the per-slot integrability and bounds,
Fubini, and the binomial summation. -/
theorem rowA_core {α K : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    {f A : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hAso : Work.FTS.EllipticEst.SmoothOpen A)
    (hm6 : Work.Spaces.HkMem α 6 f) (hm7 : Work.Spaces.HkMem α 7 f)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ)))
    (hab : a + b ≤ 6) :
    |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Work.Spaces.Dz f z θ) f|
      ≤ 320 * K * Work.Spaces.HkSq α 6 f := by
  have hpt := rowA_piece_expansion (f := f) (A := A) (ρ := ρ) (a := a) (b := b) hso hAso
  have hPint : ∀ i ∈ Finset.range (a + 1), ∀ j ∈ Finset.range (b + 1),
      MeasureTheory.Integrable (rowA_piece f A ρ a b i j) pqm := by
    intro i hi j hj
    have hia : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hjb : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases h00 : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h00
      exact (rowA_slot00 hα0 hα1 hK hso hAso hm6 hm7 hρ hAbd hab).1
    · exact (rowA_slot_bound hα0 hα1 hK hso hAso hm6 hρ hAbd hab hia hjb (by omega)).1
  have hIntSum : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ)) * rowA_piece f A ρ a b i j p) pqm := by
    refine MeasureTheory.integrable_finsetSum _ fun i hi => ?_
    refine MeasureTheory.integrable_finsetSum _ fun j hj => ?_
    exact (hPint i hi j hj).const_mul _
  have hIntTot : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) pqm := hIntSum.congr hpt.symm
  have hbridge : Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => A z θ * Work.Spaces.Dz f z θ) f
      = ∫ p, ρ p.1 p.2
          * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2 ∂pqm := by
    rw [Work.FTS.TransportS.slotPairing]
    exact (MeasureTheory.integral_prod _ hIntTot).symm
  have hsplit : (∫ p, ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2 ∂pqm)
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ))
            * (∫ p, rowA_piece f A ρ a b i j p ∂pqm) := by
    rw [MeasureTheory.integral_congr_ae hpt]
    rw [MeasureTheory.integral_finsetSum _ (fun i hi => MeasureTheory.integrable_finsetSum _
      (fun j hj => (hPint i hi j hj).const_mul _))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun j hj => (hPint i hi j hj).const_mul _)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [MeasureTheory.integral_const_mul]
  have hslot : ∀ i ∈ Finset.range (a + 1), ∀ j ∈ Finset.range (b + 1),
      |∫ p, rowA_piece f A ρ a b i j p ∂pqm| ≤ 5 * K * Work.Spaces.HkSq α 6 f := by
    intro i hi j hj
    have hia : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hjb : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases h00 : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h00
      exact (rowA_slot00 hα0 hα1 hK hso hAso hm6 hm7 hρ hAbd hab).2
    · have h := (rowA_slot_bound hα0 hα1 hK hso hAso hm6 hρ hAbd hab hia hjb (by omega)).2
      have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
      nlinarith [h, hK, hSnn]
  have hsum : ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ))
          * |∫ p, rowA_piece f A ρ a b i j p ∂pqm|
        ≤ 320 * K * Work.Spaces.HkSq α 6 f := by
    calc ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ))
            * |∫ p, rowA_piece f A ρ a b i j p ∂pqm|
        ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ)) * (5 * K * Work.Spaces.HkSq α 6 f) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          exact mul_le_mul_of_nonneg_left (hslot i hi j hj) (by positivity)
      _ = ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * (5 * K * Work.Spaces.HkSq α 6 f) :=
          rowA_choose_sum _
      _ ≤ 64 * (5 * K * Work.Spaces.HkSq α 6 f) := by
          have h2 : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤ 64 := by
            rw [← pow_add]
            calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) hab
              _ = 64 := by norm_num
          exact mul_le_mul_of_nonneg_right h2
            (mul_nonneg (mul_nonneg (by norm_num) hK) (Work.Spaces.HkSq_nonneg α 6 f))
      _ = 320 * K * Work.Spaces.HkSq α 6 f := by ring
  calc |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Work.Spaces.Dz f z θ) f|
      = |∫ p, ρ p.1 p.2
          * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2 ∂pqm| := by rw [hbridge]
    _ = |∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ))
            * (∫ p, rowA_piece f A ρ a b i j p ∂pqm)| := by rw [hsplit]
    _ ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ))
            * |∫ p, rowA_piece f A ρ a b i j p ∂pqm| := by
        calc |∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              ((a.choose i : ℝ) * (b.choose j : ℝ))
                * (∫ p, rowA_piece f A ρ a b i j p ∂pqm)|
            ≤ ∑ i ∈ Finset.range (a + 1), |∑ j ∈ Finset.range (b + 1),
                ((a.choose i : ℝ) * (b.choose j : ℝ))
                  * (∫ p, rowA_piece f A ρ a b i j p ∂pqm)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
                |((a.choose i : ℝ) * (b.choose j : ℝ))
                  * (∫ p, rowA_piece f A ρ a b i j p ∂pqm)| :=
              Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
                ((a.choose i : ℝ) * (b.choose j : ℝ))
                  * |∫ p, rowA_piece f A ρ a b i j p ∂pqm| := by
              refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
              rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ 320 * K * Work.Spaces.HkSq α 6 f := hsum

/-- The arithmetic majorant: `320·K·|f|²_{ℋ⁶} ≤ 400·K·α^{-3}(1+Xn)⁴(1+|f|²_{ℋ⁶})`. -/
theorem rowA_majorant {α K : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    {f : ℝ → ℝ → ℝ} :
    320 * K * Work.Spaces.HkSq α 6 f
      ≤ 400 * K * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) := by
  have hS : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hXn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hX : 1 ≤ (1 + Work.FTS.Nonlin.Xn α f) ^ 4 := one_le_pow₀ (by linarith)
  have hα3 : 1 ≤ α ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt hα0)]
    exact (one_le_inv₀ (Real.rpow_pos_of_pos hα0 3)).mpr
      (Real.rpow_le_one (le_of_lt hα0) hα1 (by norm_num))
  have hA : 1 ≤ α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 :=
    one_le_mul_of_one_le_of_one_le hα3 hX
  have hstep1 : 320 * K * Work.Spaces.HkSq α 6 f ≤ 400 * K * Work.Spaces.HkSq α 6 f :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hK) hS
  have hstep2 : 400 * K * Work.Spaces.HkSq α 6 f
      ≤ 400 * K * (1 + Work.Spaces.HkSq α 6 f) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hstep3 : 400 * K * (1 + Work.Spaces.HkSq α 6 f)
      ≤ 400 * K * (1 + Work.Spaces.HkSq α 6 f)
          * (α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4) :=
    le_mul_of_one_le_right (by positivity) hA
  refine hstep1.trans (hstep2.trans (hstep3.trans (le_of_eq ?_)))
  ring

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP.DomAQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Work.FTS.StrongPersist.H6Rows.Npair6BWork (PM)

/-- The product measure `PM` is the restriction of Lebesgue measure to the closed quadrant. -/
theorem PM_eq_restrict :
    PM = MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [PM, MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]

/-- **The `L²` mass of the product slot.**  If the pointwise Leibniz bound of `D_z^bD_θ^a(A·Q)`
is available in the flat-priced shape, and the angular profile `E` of the dominating function
has `∫_{Iθ} E ≤ B`, then the leaf-weighted square of the slot is integrable with mass at most
`(KA·KQ)²·B`. -/
theorem domAQ {α : ℝ} {A Q : ℝ → ℝ → ℝ} {KA KQ : ℝ} {a b : ℕ}
    {ρ : ℝ → ℝ → ℝ} {E : ℝ → ℝ} {B : ℝ}
    (hKA0 : 0 ≤ KA) (hKQ0 : 0 ≤ KQ)
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hQ : Work.FTS.EllipticEst.SmoothOpen Q)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hDg : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * E p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) PM ∧
      (∫ p, (Work.Spaces.w p.1) ^ 2 * E p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2 ∂PM) ≤ B)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ) ^ 2
        ≤ (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2 * E θ * (z ^ 2 / (1 + z) ^ 3) ^ 2)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ρ p.1 p.2 * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2) PM ∧
    (∫ p, ρ p.1 p.2
        * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2 ∂PM)
        ≤ (KA * KQ) ^ 2 * B := by
  have hc0 : 0 ≤ (KA * KQ) ^ 2 := sq_nonneg _
  have hDgc : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (KA * KQ) ^ 2 * ((Work.Spaces.w p.1) ^ 2 * E p.2
        * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2)) PM := hDg.1.const_mul _
  have hvalDg : (∫ p, (KA * KQ) ^ 2 * ((Work.Spaces.w p.1) ^ 2 * E p.2
        * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) ∂PM) ≤ (KA * KQ) ^ 2 * B := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hDg.2 hc0
  have hptae : ∀ᵐ p ∂PM, ρ p.1 p.2
      * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2
      ≤ (KA * KQ) ^ 2 * ((Work.Spaces.w p.1) ^ 2 * E p.2
        * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) := by
    exact Work.FTS.StrongPersist.H6Rows.Npair6BWork.ae_of_forall_Qd
      (fun z θ hz hθ0 hθ1 => hpt z θ hz hθ0 hθ1)
  have hnn : ∀ᵐ p ∂PM, 0 ≤ ρ p.1 p.2
      * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2 :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.ae_of_forall_Qd
      (fun z θ hz hθ0 hθ1 =>
        mul_nonneg (Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_nonneg hρ z θ hz hθ0 hθ1)
          (sq_nonneg _))
  have hptn : ∀ᵐ p ∂PM, ‖ρ p.1 p.2
      * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2‖
      ≤ (KA * KQ) ^ 2 * ((Work.Spaces.w p.1) ^ 2 * E p.2
        * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) := by
    filter_upwards [hptae, hnn] with p hp hn
    rw [Real.norm_of_nonneg hn]
    exact hp
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ρ p.1 p.2 * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2) PM :=
    (Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_leafW hρ).mul
      ((Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_mixed (smoothOpen_mul hA hQ) b a).pow 2)
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ρ p.1 p.2 * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2) PM :=
    hDgc.mono' hmeas hptn
  refine ⟨hint, ?_⟩
  calc (∫ p, ρ p.1 p.2
        * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2 ∂PM)
      ≤ ∫ p, (KA * KQ) ^ 2 * ((Work.Spaces.w p.1) ^ 2 * E p.2
          * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) ∂PM :=
        MeasureTheory.integral_mono_ae hint hDgc hptae
    _ ≤ (KA * KQ) ^ 2 * B := hvalDg

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP.zWeight_flat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP

/-- Off `z = 0` the `z`-weight of the "flat price" collapses to `(1+z)^{-2}`:
`w(z)² · (z²/(1+z)³)² = (1+z)^{-2}`. -/
theorem w_sq_mul_flat_sq (z : ℝ) (hz : z ≠ 0) :
    (Work.Spaces.w z) ^ 2 * (z ^ 2 / (1 + z) ^ 3) ^ 2 = ((1 + z) ^ 2)⁻¹ := by
  rw [Work.Spaces.w]
  field_simp

/-- The line `{z = 0}` is null in `ℝ²`. -/
theorem volume_fst_eq_zero : (volume : Measure (ℝ × ℝ)) {p | p.1 = 0} = 0 := by
  have h : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ Set.univ := by ext p; simp
  rw [h, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
  simp

theorem zWeight_flat (b : ℝ → ℝ) (B : ℝ)
    (hbint : MeasureTheory.IntegrableOn b Work.Spaces.Iθ)
    (hble : (∫ θ in Work.Spaces.Iθ, b θ) ≤ B) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * b p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) ∧
    (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        (Work.Spaces.w p.1) ^ 2 * b p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) ≤ B := by
  set s : Set (ℝ × ℝ) := Work.Spaces.Iz ×ˢ Work.Spaces.Iθ with hs
  -- null set where the pointwise collapse fails
  have hae0 : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using volume_fst_eq_zero
  -- a.e. the integrand is `b θ · (1+z)^{-2}`
  have hae : (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * b p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2)
      =ᵐ[volume.restrict s]
      (fun p : ℝ × ℝ => ((1 + p.1) ^ 2)⁻¹ * b p.2) := by
    filter_upwards [hae0.filter_mono MeasureTheory.ae_restrict_le] with p hp
    calc (Work.Spaces.w p.1) ^ 2 * b p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2
        = ((Work.Spaces.w p.1) ^ 2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) * b p.2 := by ring
      _ = ((1 + p.1) ^ 2)⁻¹ * b p.2 := by rw [w_sq_mul_flat_sq p.1 hp]
  -- the `z`-factor `(1+z)^{-2}` is integrable on `Iz` with integral `1`
  have hGint : IntegrableOn (fun p : ℝ × ℝ => ((1 + p.1) ^ 2)⁻¹ * b p.2) s := by
    rw [hs]
    exact Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
      (f := fun z : ℝ => ((1 + z) ^ 2)⁻¹) (g := b)
      integrableOn_inv_sq_Iz hbint
  have hvalG : ∫ p in s, ((1 + p.1) ^ 2)⁻¹ * b p.2
      = (∫ z in Work.Spaces.Iz, ((1 + z) ^ 2)⁻¹) * (∫ θ in Work.Spaces.Iθ, b θ) := by
    rw [hs, Measure.volume_eq_prod ℝ ℝ]
    exact setIntegral_prod_mul (fun z : ℝ => ((1 + z) ^ 2)⁻¹) b
      Work.Spaces.Iz Work.Spaces.Iθ
  constructor
  · exact hGint.congr hae.symm
  · calc ∫ p in s, (Work.Spaces.w p.1) ^ 2 * b p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2
        = ∫ p in s, ((1 + p.1) ^ 2)⁻¹ * b p.2 := integral_congr_ae hae
      _ = (∫ z in Work.Spaces.Iz, ((1 + z) ^ 2)⁻¹) * (∫ θ in Work.Spaces.Iθ, b θ) := hvalG
      _ = 1 * (∫ θ in Work.Spaces.Iθ, b θ) := by rw [integral_inv_sq_Iz]
      _ ≤ B := by simpa using hble

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarDthAux.SummandPt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The pointwise bound of a Leibniz summand with a non-trivial index.**  For `(i,j) ≠ (0,0)`
with `i ≤ a`, `j ≤ b`, `a + b ≤ 6`, the flat priced coefficient slot `D_z^jD_θ^iA` pairs with the
two `f`-slots into at most `2·KA·HkIntegrand α 6 f`. -/
theorem summandPt {α KA : ℝ} {A f : ℝ → ℝ → ℝ} {a b i j : ℕ} {q z θ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hKA0 : 0 ≤ KA)
    (hflat : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
          (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1))
    (hf6 : Work.Spaces.HkMem α 6 f)
    (hia : i ≤ a) (hjb : j ≤ b) (hne : ¬(i = 0 ∧ j = 0)) (hab : a + b ≤ 6)
    (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |Work.FTS.TransportS.SlotT2.canonW q z θ
        * Work.Spaces.mixed j i A z θ
        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ 2 * KA * Work.Spaces.HkIntegrand α 6 f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
  have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hij6 : j + i ≤ 6 := by omega
  have hX := hflat j i hij6 z θ hz hθ0 hθ1
  have hcnn : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
    Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
  have hIk : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hzfac0 : 0 ≤ z / (1 + z) := div_nonneg hz.le (by linarith)
  have hzfac1 : z / (1 + z) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hYord : (a - i + 1) + (b - j) ≤ 6 := by omega
  have hYη : (a - i + 1) = 0 → q ≤ Work.Spaces.eta := fun h => absurd h (by omega)
  have hYle : Work.FTS.TransportS.SlotT2.canonW q z θ
      * (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α q f (a - i + 1) (b - j)
      hqγ hYη hYord hθIoo
  have hZle : Work.FTS.TransportS.SlotT2.canonW q z θ
      * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α q f a b
      hqγ hqη (by omega) hθIoo
  have hAM : 2 * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
        * |Work.Spaces.mixed b a f z θ|
      ≤ (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2
        + (Work.Spaces.mixed b a f z θ) ^ 2 := by
    have h := sq_nonneg (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
      - |Work.Spaces.mixed b a f z θ|)
    rw [sub_sq, sq_abs, sq_abs] at h
    linarith
  have habs : |Work.FTS.TransportS.SlotT2.canonW q z θ
        * Work.Spaces.mixed j i A z θ
        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      = Work.FTS.TransportS.SlotT2.canonW q z θ
        * |Work.Spaces.mixed j i A z θ|
        * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
        * |Work.Spaces.mixed b a f z θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcnn]
  rw [habs]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- `i = 0`, hence `j ≥ 1`: use the weight `q` itself for both `f`-slots
    subst hi0
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr fun h => hne ⟨rfl, h⟩
    have hX' : |Work.Spaces.mixed j 0 A z θ| ≤ KA * (z / (1 + z)) := by
      have h := hX
      have hif : (if (1 : ℕ) ≤ 0 then
          (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else (1 : ℝ)) = 1 :=
        if_neg (by norm_num)
      rw [hif, mul_one] at h
      simpa using h
    have hws : Work.FTS.TransportS.SlotT2.canonW q z θ
          * |Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
          * |Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      have hAM' : 2 * |Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ|
          ≤ (Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ) ^ 2
            + (Work.Spaces.mixed b a f z θ) ^ 2 := by
        have h := sq_nonneg (|Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
          - |Work.Spaces.mixed b a f z θ|)
        rw [sub_sq, sq_abs, sq_abs] at h
        linarith
      have h := mul_le_mul_of_nonneg_left hAM' hcnn
      have hY' := hYle
      have hZ' := hZle
      linarith
    calc Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j 0 A z θ|
          * |Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ KA * (z / (1 + z)) * Work.FTS.TransportS.SlotT2.canonW q z θ
          * |Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
          * |Work.Spaces.mixed b a f z θ| := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
            (abs_nonneg _)
          calc Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j 0 A z θ|
              ≤ Work.FTS.TransportS.SlotT2.canonW q z θ * (KA * (z / (1 + z))) :=
                mul_le_mul_of_nonneg_left hX' hcnn
            _ = KA * (z / (1 + z)) * Work.FTS.TransportS.SlotT2.canonW q z θ := by ring
      _ = KA * (z / (1 + z)) * (Work.FTS.TransportS.SlotT2.canonW q z θ
            * |Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ|) := by ring
      _ ≤ KA * (z / (1 + z)) * Work.Spaces.HkIntegrand α 6 f z θ :=
          mul_le_mul_of_nonneg_left hws (mul_nonneg hKA0 hzfac0)
      _ ≤ KA * 1 * Work.Spaces.HkIntegrand α 6 f z θ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzfac1 hKA0) hIk
      _ = KA * Work.Spaces.HkIntegrand α 6 f z θ := by ring
      _ ≤ 2 * KA * Work.Spaces.HkIntegrand α 6 f z θ := by
          have : 0 ≤ KA * Work.Spaces.HkIntegrand α 6 f z θ := mul_nonneg hKA0 hIk
          linarith
  · -- `1 ≤ i`: the flat price with the `γ`-weight
    have hi1 : 1 ≤ i := hipos
    have hYleγ : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α (Work.Spaces.gam α) f
        (a - i + 1) (b - j) le_rfl
        (fun h => absurd h (by omega)) hYord hθIoo
    have hZleγ : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α (Work.Spaces.gam α) f a b
        le_rfl (fun h => absurd h (by omega)) (by omega) hθIoo
    have hX' : |Work.Spaces.mixed j i A z θ|
        ≤ KA * (z / (1 + z)) * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      have h := hX
      rw [if_pos hi1] at h
      exact h
    have hwq : Work.FTS.TransportS.SlotT2.canonW q z θ
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        ≤ 2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ :=
      canonWMulFlatAgm hα0 hα1 hqγ hz hθ0 hθ1
    have hcγnn : 0 ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ :=
      Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
    have hγw : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
          * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
          * |Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      have h := mul_le_mul_of_nonneg_left hAM hcγnn
      have hY' := hYleγ
      have hZ' := hZleγ
      linarith
    calc Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ Work.FTS.TransportS.SlotT2.canonW q z θ
            * (KA * (z / (1 + z))
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hX' hcnn) (abs_nonneg _)) (abs_nonneg _)
      _ = KA * (z / (1 + z)) * (Work.FTS.TransportS.SlotT2.canonW q z θ
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ| := by ring
      _ ≤ KA * (z / (1 + z))
            * (2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ)
            * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ| := by
          have hwq' : KA * (z / (1 + z))
                * (Work.FTS.TransportS.SlotT2.canonW q z θ
                    * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              ≤ KA * (z / (1 + z))
                * (2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ) :=
            mul_le_mul_of_nonneg_left hwq (mul_nonneg hKA0 hzfac0)
          calc KA * (z / (1 + z))
                * (Work.FTS.TransportS.SlotT2.canonW q z θ
                    * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ|
              = (KA * (z / (1 + z))
                  * (Work.FTS.TransportS.SlotT2.canonW q z θ
                      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
                * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ| := by ring
            _ ≤ (KA * (z / (1 + z))
                  * (2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ))
                * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ| :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwq' (abs_nonneg _))
                  (abs_nonneg _)
            _ = KA * (z / (1 + z))
                * (2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ)
                * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ| := by ring
      _ = KA * (z / (1 + z)) * (2 * (Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
              * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
              * |Work.Spaces.mixed b a f z θ|)) := by ring
      _ ≤ KA * (z / (1 + z)) * (2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hγw (by norm_num))
            (mul_nonneg hKA0 hzfac0)
      _ ≤ 2 * KA * Work.Spaces.HkIntegrand α 6 f z θ := by
          have h2 : KA * (z / (1 + z)) * (2 * Work.Spaces.HkIntegrand α 6 f z θ)
              ≤ KA * 1 * (2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzfac1 hKA0) (by linarith)
          linarith

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarDthAux.ZeroSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The transport term, slicewise.**  For `0 ≤ q ≤ γ` (with `q ≤ η` when `a = 0`), a flat
priced coefficient `A` and `v = D_z^bD_θ^af`,

`|∫_θ canonW q z θ·A z θ·D_θ(v) z θ·v z θ| ≤ C·KA·(z/(1+z))·∫_θ canonW q z θ·(v z θ)²`,

uniformly in `z ∈ Iz`.  This is `T1SixAux.hardSlotSliceSixZero` at the two-constant data
`K1 = KA·z/(1+z)` for `|A|` and `K2 = KA·(z/(1+z))·(α+σ)σ^{α/5} ≤ 2K1` for `|D_θA|`. -/
theorem dthZeroSliceAux : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (KA : ℝ) (a b : ℕ) (q : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      0 ≤ KA →
      (∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) →
      0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      a + b ≤ 6 →
      ∀ z ∈ Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
          ≤ C * KA * (z / (1 + z)) *
              ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2 := by
  obtain ⟨Chard, hChardpos, hhard⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero
  refine ⟨3 * Chard, by positivity, ?_⟩
  intro α hα A f KA a b q hA hfsm hf6 hKA0 hflat hq0 hqγ hqη hab z hz
  obtain ⟨hα0, hα1⟩ := hα
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- `z = 0`: both sides vanish
    subst hz0
    have hL : (fun θ : ℝ => Work.FTS.TransportS.SlotT2.canonW q 0 θ * A 0 θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a f) 0 θ
        * Work.Spaces.mixed b a f 0 θ) = fun _ => (0 : ℝ) := by
      funext θ
      rw [Work.FTS.TransportS.SlotT2.canonW_zero_z]; ring
    rw [hL, MeasureTheory.integral_zero, abs_zero]
    simp
  · have hz0 : 0 ≤ z := hzpos.le
    have hzfac0 : 0 ≤ z / (1 + z) := div_nonneg hz0 (by linarith)
    have hzfac1 : z / (1 + z) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hZsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.mixed b a f) := hfsm.mixed b a
    have hq2 : q ≤ 2 := by
      have h1 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
      linarith
    have hKf0 : 0 ≤ 2 * KA * (z / (1 + z)) := by positivity
    -- `|A z θ| ≤ 2 KA z/(1+z)`
    have hAb : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
        |A z θ| ≤ 2 * KA * (z / (1 + z)) := by
      intro θ hθ0 hθ1
      have h := hflat 0 0 (by norm_num) z θ hzpos hθ0 hθ1
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] at h
      have hif : (if (1 : ℕ) ≤ 0 then
          (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else (1 : ℝ)) = 1 :=
        if_neg (by norm_num)
      rw [hif, mul_one] at h
      have hfac : 0 ≤ KA * (z / (1 + z)) := mul_nonneg hKA0 hzfac0
      linarith
    -- `|D_θA z θ| ≤ 2 KA z/(1+z)`
    have hDb : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dth A z θ| ≤ 2 * KA * (z / (1 + z)) := by
      intro θ hθ0 hθ1
      have h := hflat 0 1 (by norm_num) z θ hzpos hθ0 hθ1
      have hif : (if (1 : ℕ) ≤ 1 then
          (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else (1 : ℝ))
          = (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := if_pos le_rfl
      rw [hif] at h
      have hs : 0 ≤ Real.sin (2 * θ) :=
        (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
      have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hgain : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
        have h1 : (α + Real.sin (2 * θ)) ≤ 2 := by linarith
        have h2 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs hs1 (by linarith)
        have h3 : (0 : ℝ) ≤ α + Real.sin (2 * θ) := by linarith
        calc (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
            ≤ (α + Real.sin (2 * θ)) * 1 := mul_le_mul_of_nonneg_left h2 h3
          _ ≤ 2 := by linarith
      have hDth : Work.Spaces.Dth A z θ = Work.Spaces.mixed 0 1 A z θ := rfl
      rw [hDth]
      calc |Work.Spaces.mixed 0 1 A z θ|
          ≤ KA * (z / (1 + z))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := h
        _ ≤ KA * (z / (1 + z)) * 2 :=
            mul_le_mul_of_nonneg_left hgain (mul_nonneg hKA0 hzfac0)
        _ = 2 * KA * (z / (1 + z)) := by ring
    have hint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        Work.Spaces.Iθ :=
      Work.FTS.StrongPersist.N6Trans.T1SixAux.slotSliceIntegrable α q hfsm hf6 hqγ hqη hab hz
    have hmain := hhard q (2 * KA * (z / (1 + z))) z A (Work.Spaces.mixed b a f)
      hq0 hq2 hKf0 hz hA hZsm hAb hDb hint
    have hJnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2 :=
      MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => mul_nonneg (Work.FTS.TransportS.SlotT2.canonW_nonneg hθ) (sq_nonneg _)))
    calc |∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
        ≤ Chard * (2 * KA * (z / (1 + z)))
            * ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2 := hmain
      _ ≤ 3 * Chard * KA * (z / (1 + z))
            * ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2 := by
          have h1 : Chard * (2 * KA * (z / (1 + z))) ≤ 3 * Chard * KA * (z / (1 + z)) := by
            have := hChardpos.le
            nlinarith [hzfac0, hKA0]
          exact mul_le_mul_of_nonneg_right h1 hJnn
      _ = (3 * Chard) * KA * (z / (1 + z))
            * ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2 := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
