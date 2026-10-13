/-
# `T6Coef.rowDthCoef` — the `A · D_θ f` coefficient row of the level-six pairing

```
∃ C, 0 < C ∧ ∀ α ∈ Ioc 0 1, ∀ (A f : Fn) (K0 K4 K6 M : ℝ) (a b : ℕ) (ρ),
  CoefData α A K0 K4 K6 → DatData α f M → a + b ≤ 6 → IsLeafW α a ρ →
  |slotPairing ρ a b (A · D_θ f) f|
    ≤ C α^{-3} ((1+K0+K4)(1+HkSq α 6 f) + (K4+K6)(1+M)(1+HkNorm α 6 f))
```

The two analytic pieces are delegated:

* `RowDth.zeroTermDth` — the `(i,j) = (0,0)` transport summand
  `∫∫ ρ A D_θ(D_z^bD_θ^af) D_z^bD_θ^af`, bounded by `C α^{-1/2}(K0+K4)(1+HkSq α 6 f)`;
* `RowDth.perTermDthMine` — every other Leibniz summand
  `∫∫ ρ (D_z^jD_θ^iA) (D_z^{b-j}D_θ^{a-i+1}f) (D_z^bD_θ^af)`, bounded by
  `C α^{-1/2}((1+K0+K4)(1+HkSq α 6 f) + (K4+K6)(1+M)(1+HkNorm α 6 f))`.

This file is the assembly: the pointwise Leibniz expansion (`leibnizRem6`), the splitting of the
iterated integral (both pieces are integrable by the integrability conjuncts of the two lemmas),
the binomial-sum bookkeeping and the arithmetic (`α^{-1/2} ≤ α^{-3}`, `K0+K4 ≤ 1+K0+K4`).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt2
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Integ
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.perTermDthMine
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.zeroTermDth
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

set_option maxHeartbeats 1600000

theorem rowDthCoef : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨C1, hC1pos, hper⟩ := RowDth.perTermDthMine
  obtain ⟨C2, hC2pos, hzer⟩ := RowDth.zeroTermDth
  refine ⟨C2 + 64 * C1, by positivity, ?_⟩
  intro α hαmem A f K0 K4 K6 M a b ρ hcoef hdat hab hleaf
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hK0nn : 0 ≤ K0 :=
    le_trans (abs_nonneg (A 1 (Real.pi / 4)))
      (hcoef.val 1 (Real.pi / 4) (by norm_num) (by positivity)
        (by linarith [Real.pi_pos]))
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hcoef.n6
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hSq6nn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hC1nn : 0 ≤ C1 := hC1pos.le
  have hC2nn : 0 ≤ C2 := hC2pos.le
  have hzer' := hzer α hαmem A f K0 K4 K6 M a b ρ hcoef hdat hab hleaf
  -- ## the pointwise Leibniz expansion on the open quadrant
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
        = A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              (if i = 0 ∧ j = 0 then 0
                else ((a.choose i : ℝ) * (b.choose j : ℝ))
                  * (Work.Spaces.mixed j i A z θ
                      * Work.Spaces.mixed (b - j) (a - i + 1) f z θ)) := by
    intro z θ hz hθ0 hθ1
    have h := Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6 (f := A) (g := f)
      hcoef.sm hdat.sm a b z θ hz hθ0 hθ1
    linarith
  -- ## the pointwise identity for the full integrand
  have hfull : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
          * Work.Spaces.mixed b a f z θ
        = ρ z θ * A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ
          + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              (if i = 0 ∧ j = 0 then 0
                else ((a.choose i : ℝ) * (b.choose j : ℝ))
                  * (ρ z θ * Work.Spaces.mixed j i A z θ
                      * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                      * Work.Spaces.mixed b a f z θ)) := by
    intro z θ hz hθ0 hθ1
    rw [hpt z θ hz hθ0 hθ1]
    rw [show ρ z θ * (A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
                (if i = 0 ∧ j = 0 then 0
                  else ((a.choose i : ℝ) * (b.choose j : ℝ))
                    * (Work.Spaces.mixed j i A z θ
                        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ)))
          * Work.Spaces.mixed b a f z θ
        = ρ z θ * A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ
          + ρ z θ * (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
                (if i = 0 ∧ j = 0 then 0
                  else ((a.choose i : ℝ) * (b.choose j : ℝ))
                    * (Work.Spaces.mixed j i A z θ
                        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ)))
            * Work.Spaces.mixed b a f z θ from by ring]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : i = 0 ∧ j = 0
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  -- ## the θ-slice identity for z > 0
  have hslice : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a
            (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
          * Work.Spaces.mixed b a f z θ)
        = (∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
          + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              (if i = 0 ∧ j = 0 then 0
                else ((a.choose i : ℝ) * (b.choose j : ℝ))
                  * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed j i A z θ
                      * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                      * Work.Spaces.mixed b a f z θ)) := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := by
      simp only [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
    have hae : (fun θ : ℝ => ρ z θ * Work.Spaces.mixed b a
            (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
          * Work.Spaces.mixed b a f z θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => ρ z θ * A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ
            + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
                (if i = 0 ∧ j = 0 then 0
                  else ((a.choose i : ℝ) * (b.choose j : ℝ))
                    * (ρ z θ * Work.Spaces.mixed j i A z θ
                        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                        * Work.Spaces.mixed b a f z θ))) := by
      rw [RowDth.restrict_Iθ_eq_Ioo]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact hfull z θ hz hθ.1 hθ.2
    rw [MeasureTheory.integral_congr_ae hae]
    have h2int : MeasureTheory.IntegrableOn (fun θ : ℝ =>
          ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then 0
              else ((a.choose i : ℝ) * (b.choose j : ℝ))
                * (ρ z θ * Work.Spaces.mixed j i A z θ
                    * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                    * Work.Spaces.mixed b a f z θ))) Work.Spaces.Iθ := by
      refine MeasureTheory.integrable_finsetSum _ (fun i hi => ?_)
      refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
      · simp only [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).1
          z hzIz).const_mul _
    rw [MeasureTheory.integral_add (hzer'.1 z hzIz) h2int]
    congr 1
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        by_cases h : i = 0 ∧ j = 0
        · simp only [if_pos h, MeasureTheory.integral_zero]
        · simp only [if_neg h]
          rw [MeasureTheory.integral_const_mul]
      · intro j hj
        by_cases h : i = 0 ∧ j = 0
        · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
        · simp only [if_neg h]
          have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).1
            z hzIz).const_mul _
    · intro i hi
      refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
      · simp only [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).1
          z hzIz).const_mul _
  -- ## the double-integral identity
  have hdouble : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
        * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed b a f z θ)
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ)
        + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then 0
              else ((a.choose i : ℝ) * (b.choose j : ℝ))
                * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed j i A z θ
                    * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)) := by
    have hzae : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
          * Work.Spaces.mixed b a f z θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
            + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
                (if i = 0 ∧ j = 0 then 0
                  else ((a.choose i : ℝ) * (b.choose j : ℝ))
                    * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed j i A z θ
                        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                        * Work.Spaces.mixed b a f z θ))) := by
      rw [RowDth.restrict_Iz_eq_Ioi]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun z hz => hslice z hz)
    rw [MeasureTheory.integral_congr_ae hzae]
    have hSint : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range (a + 1),
          ∑ j ∈ Finset.range (b + 1),
                (if i = 0 ∧ j = 0 then 0
                  else ((a.choose i : ℝ) * (b.choose j : ℝ))
                    * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed j i A z θ
                        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                        * Work.Spaces.mixed b a f z θ))) Work.Spaces.Iz := by
      refine MeasureTheory.integrable_finsetSum _ (fun i hi => ?_)
      refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
      · simp only [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).2.1).const_mul _
    rw [MeasureTheory.integral_add hzer'.2.1 hSint]
    congr 1
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        by_cases h : i = 0 ∧ j = 0
        · simp only [if_pos h, MeasureTheory.integral_zero]
        · simp only [if_neg h]
          rw [MeasureTheory.integral_const_mul]
      · intro j hj
        by_cases h : i = 0 ∧ j = 0
        · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
        · simp only [if_neg h]
          have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).2.1).const_mul _
    · intro i hi
      refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
      · simp only [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).2.1).const_mul _
  -- ## the bound on the remainder sum
  have hsumBound : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0
            else ((a.choose i : ℝ) * (b.choose j : ℝ))
              * |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|))
      ≤ 64 * C1 * (α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by
    have hQ0 : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by positivity
    have hP0 : 0 ≤ C1 * α ^ (-(1 / 2 : ℝ))
        * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
            + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
      mul_nonneg (mul_nonneg hC1nn (Real.rpow_nonneg hα0.le _)) hQ0
    have hstep : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0
            else ((a.choose i : ℝ) * (b.choose j : ℝ))
              * |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|))
        ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ)) * (C1 * α ^ (-(1 / 2 : ℝ))
                * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                    + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by
      refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
      by_cases h : i = 0 ∧ j = 0
      · rw [if_pos h]
        exact mul_nonneg (by positivity) hP0
      · rw [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).2.2
    refine le_trans hstep ?_
    have hbinom : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ))) = (2 : ℝ) ^ a * (2 : ℝ) ^ b := by
      rw [← Finset.sum_mul_sum]
      congr 1
      · exact_mod_cast Nat.sum_range_choose a
      · exact_mod_cast Nat.sum_range_choose b
    have hpow : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤ 64 := by
      rw [← pow_add]
      calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 :=
            pow_le_pow_right₀ (by norm_num) hab
        _ = 64 := by norm_num
    have hsum_eq : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ)) * (C1 * α ^ (-(1 / 2 : ℝ))
                * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                    + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))))
        = ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * (C1 * α ^ (-(1 / 2 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                  + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by
      rw [← hbinom]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.sum_mul]
    rw [hsum_eq]
    calc ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * (C1 * α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)))
        ≤ 64 * (C1 * α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) :=
          mul_le_mul_of_nonneg_right hpow hP0
      _ = 64 * C1 * (α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by ring
  -- ## the bound on the hard term plus the remainder
  have hmain : |(∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ)
        + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then 0
              else ((a.choose i : ℝ) * (b.choose j : ℝ))
                * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed j i A z θ
                    * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                    * Work.Spaces.mixed b a f z θ))|
      ≤ C2 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then 0
              else ((a.choose i : ℝ) * (b.choose j : ℝ))
                * |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed j i A z θ
                    * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                    * Work.Spaces.mixed b a f z θ|) := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · exact hzer'.2.2
    · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum (fun i hi => ?_)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h, abs_zero]
        exact le_refl 0
      · simp only [if_neg h]
        rw [abs_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a.choose i : ℝ)),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.choose j : ℝ))]
  -- ## assembly
  rw [Work.FTS.TransportS.slotPairing]
  rw [hdouble]
  refine le_trans hmain (le_trans (add_le_add le_rfl hsumBound) ?_)
  -- ## the arithmetic
  have hα3 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(3 : ℝ) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  have hαle : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hBnn : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by positivity
  have hKle : (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
      ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
    have h1 : (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (0 : ℝ) ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by positivity
    linarith
  have hterm1 : C2 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
      ≤ C2 * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by
    have h3 : α ^ (-(1 / 2 : ℝ)) * ((K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
      calc α ^ (-(1 / 2 : ℝ)) * ((K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
          ≤ α ^ (-(3 : ℝ)) * ((K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) :=
            mul_le_mul_of_nonneg_right hαle (by positivity)
        _ ≤ α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
            mul_le_mul_of_nonneg_left hKle (Real.rpow_nonneg hα0.le _)
    calc C2 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        = C2 * (α ^ (-(1 / 2 : ℝ)) * ((K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) := by ring
      _ ≤ C2 * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := mul_le_mul_of_nonneg_left h3 hC2nn
  have hterm2 : 64 * C1 * (α ^ (-(1 / 2 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)))
      ≤ 64 * C1 * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hαle hBnn) (by positivity)
  have hsplit : (C2 + 64 * C1) * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))
      = C2 * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)))
        + 64 * C1 * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by ring
  linarith [hterm1, hterm2, hsplit]

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
