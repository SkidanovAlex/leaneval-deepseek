import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.RowAdzBounds

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
