/-
# `T6Coef.rowDthWlInf` — the `D_θ` row with a `𝒲^{6,∞}`-priced coefficient

```
∃ C, 0 < C ∧ ∀ α ∈ Ioc 0 1, ∀ (A f : Fn) (K M : ℝ) (a b : ℕ) (ρ),
  SmoothOpen A → WlInfMem α 6 A → WlInf α 6 A ≤ K → DatData α f M →
  a + b ≤ 6 → IsLeafW α a ρ →
  |slotPairing ρ a b (A · D_θ f) f| ≤ C α^{-2}(1+K)(1+M)(1+HkSq α 6 f)
```

The pointwise Leibniz expansion `leibnizRem6` splits `mixed b a (A · D_θ f)` into the transport
term `A · D_θ(mixed b a f)` and the remainder; the two pieces are estimated separately by

* `RowDthW.hardTermWlInf` — the transport summand (the angular integration by parts of
  `N6Trans.T1SixAux.hardSlotSliceSixZero`, with `Kf := 2K` drawn from the `𝒲^{6,∞}`-bound of
  `A`);
* `RowDthW.PerTerm.perTermWlInf` — every other Leibniz summand (Cauchy–Schwarz, both `f`-slots
  being canonical `ℋ⁶`-slots).

This file is the assembly: the pointwise expansion, the splitting of the iterated integral
(both pieces are integrable by the integrability conjuncts of the two lemmas), the binomial
bookkeeping and the arithmetic (`α^{-2} ≥ 1`, `M ≥ 0`).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW.hardTermWlInf
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW.PerTerm.perTermWlInf

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

/-- The two angular endpoints of `Iθ` are null. -/
theorem restrict_Iθ_eq_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
  Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo

/-- `Iz = [0,∞)` agrees with `(0,∞)` up to a null set. -/
theorem restrict_Iz_eq_Ioi :
    volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
  have h : Set.Ioi (0 : ℝ) =ᵐ[volume] Set.Ici (0 : ℝ) := Ioi_ae_eq_Ici
  simpa [Work.Spaces.Iz] using (MeasureTheory.Measure.restrict_congr_set h).symm

theorem rowDthWlInf : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(2 : ℝ)) * (1 + K) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨CH, hCHpos, hHard⟩ := RowDthW.hardTermWlInf
  obtain ⟨CP, hCPpos, hPer⟩ := RowDthW.PerTerm.perTermWlInf
  refine ⟨CH + 64 * CP + 1, by positivity, ?_⟩
  intro α hαmem A f K M a b ρ hsmA hWmem hWK hdat hab hleaf
  have hα : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 A := Work.Spaces.WlInf_nonneg α 6 A hWmem
  have hK0 : 0 ≤ K := le_trans hWnn hWK
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hCHnn : 0 ≤ CH := hCHpos.le
  have hCPnn : 0 ≤ CP := hCPpos.le
  have hres := hHard α hαmem A f K M a b ρ hsmA hWmem hWK hdat hab hleaf
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
      hsmA hdat.sm a b z θ hz hθ0 hθ1
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
      rw [restrict_Iθ_eq_Ioo]
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
        exact ((hPer α hαmem A f K M a b i j ρ hsmA hWmem hWK hdat hab hleaf hi' hj' h).1
          z hzIz).const_mul _
    rw [MeasureTheory.integral_add (hres.1 z hzIz) h2int]
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
          exact ((hPer α hαmem A f K M a b i j ρ hsmA hWmem hWK hdat hab hleaf hi' hj' h).1
            z hzIz).const_mul _
    · intro i hi
      refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
      · simp only [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact ((hPer α hαmem A f K M a b i j ρ hsmA hWmem hWK hdat hab hleaf hi' hj' h).1
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
      rw [restrict_Iz_eq_Ioi]
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
        exact ((hPer α hαmem A f K M a b i j ρ hsmA hWmem hWK hdat hab hleaf hi' hj' h).2.1).const_mul _
    rw [MeasureTheory.integral_add hres.2.1 hSint]
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
          exact ((hPer α hαmem A f K M a b i j ρ hsmA hWmem hWK hdat hab hleaf hi' hj' h).2.1).const_mul _
    · intro i hi
      refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
      · simp only [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact ((hPer α hαmem A f K M a b i j ρ hsmA hWmem hWK hdat hab hleaf hi' hj' h).2.1).const_mul _
  -- ## the bound on the remainder sum
  have hper0 : 0 ≤ CP * (1 + K) * (1 + Work.Spaces.HkSq α 6 f) := by positivity
  have hsumBound : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0
            else ((a.choose i : ℝ) * (b.choose j : ℝ))
              * |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|))
      ≤ 64 * CP * (1 + K) * (1 + Work.Spaces.HkSq α 6 f) := by
    have hstep : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0
            else ((a.choose i : ℝ) * (b.choose j : ℝ))
              * |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|))
        ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (((a.choose i : ℝ) * (b.choose j : ℝ))
              * (CP * (1 + K) * (1 + Work.Spaces.HkSq α 6 f))) := by
      refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
      by_cases h : i = 0 ∧ j = 0
      · rw [if_pos h]
        exact mul_nonneg (by positivity) hper0
      · rw [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact mul_le_mul_of_nonneg_left
          (hPer α hαmem A f K M a b i j ρ hsmA hWmem hWK hdat hab hleaf hi' hj' h).2.2
          (by positivity)
    refine le_trans hstep ?_
    have hbinom : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ))) = (2 : ℝ) ^ a * (2 : ℝ) ^ b := by
      rw [← Finset.sum_mul_sum]
      congr 1
      · exact_mod_cast Nat.sum_range_choose a
      · exact_mod_cast Nat.sum_range_choose b
    have hpow : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤ 64 := by
      rw [← pow_add]
      calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) hab
        _ = 64 := by norm_num
    have hsum_eq : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (((a.choose i : ℝ) * (b.choose j : ℝ))
              * (CP * (1 + K) * (1 + Work.Spaces.HkSq α 6 f))))
        = ((2 : ℝ) ^ a * (2 : ℝ) ^ b)
            * (CP * (1 + K) * (1 + Work.Spaces.HkSq α 6 f)) := by
      rw [← hbinom]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.sum_mul]
    rw [hsum_eq]
    calc ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * (CP * (1 + K) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ 64 * (CP * (1 + K) * (1 + Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_right hpow hper0
      _ = 64 * CP * (1 + K) * (1 + Work.Spaces.HkSq α 6 f) := by ring
  -- ## assembly
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
      ≤ CH * (1 + K) * (1 + Work.Spaces.HkSq α 6 f)
        + 64 * CP * (1 + K) * (1 + Work.Spaces.HkSq α 6 f) := by
    refine le_trans (abs_add_le _ _) (add_le_add hres.2.2 ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun i hi => Finset.abs_sum_le_sum_abs _ _)) ?_
    refine le_trans (Finset.sum_le_sum (fun i hi =>
      Finset.sum_le_sum (fun j hj => ?_))) hsumBound
    by_cases h : i = 0 ∧ j = 0
    · rw [if_pos h, if_pos h]; simp
    · rw [if_neg h, if_neg h, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a.choose i : ℝ)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.choose j : ℝ))]
  have harith : CH * (1 + K) * (1 + Work.Spaces.HkSq α 6 f)
        + 64 * CP * (1 + K) * (1 + Work.Spaces.HkSq α 6 f)
      ≤ (CH + 64 * CP + 1) * α ^ (-(2 : ℝ)) * (1 + K) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have hαr : (1 : ℝ) ≤ α ^ (-(2 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (show -(2 : ℝ) ≤ 0 by norm_num)
      rwa [Real.rpow_zero] at h
    have hF1 : (1 : ℝ) ≤ α ^ (-(2 : ℝ)) * (1 + M) :=
      one_le_mul_of_one_le_of_one_le hαr (by linarith)
    have hAnn : 0 ≤ (1 + K) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_nonneg (by linarith) (by linarith)
    have hBnn : 0 ≤ (CH + 64 * CP + 1) * ((1 + K) * (1 + Work.Spaces.HkSq α 6 f)) :=
      mul_nonneg (by linarith) hAnn
    calc CH * (1 + K) * (1 + Work.Spaces.HkSq α 6 f)
          + 64 * CP * (1 + K) * (1 + Work.Spaces.HkSq α 6 f)
        = (CH + 64 * CP) * ((1 + K) * (1 + Work.Spaces.HkSq α 6 f)) := by ring
      _ ≤ (CH + 64 * CP + 1) * ((1 + K) * (1 + Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_right (by linarith) hAnn
      _ ≤ (CH + 64 * CP + 1) * ((1 + K) * (1 + Work.Spaces.HkSq α 6 f))
            * (α ^ (-(2 : ℝ)) * (1 + M)) :=
          le_mul_of_one_le_right hBnn hF1
      _ = (CH + 64 * CP + 1) * α ^ (-(2 : ℝ)) * (1 + K) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by ring
  rw [Work.FTS.TransportS.slotPairing]
  rw [hdouble]
  exact le_trans hmain harith

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
