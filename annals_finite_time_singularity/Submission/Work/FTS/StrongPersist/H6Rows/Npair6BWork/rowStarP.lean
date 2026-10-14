import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.summand_le_easy
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowMulSupAux.basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarDthAux.ZeroSlice
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumA1ZeroSmall
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.ExcPairBranches
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarDth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# `rowStarDth`: the flat-priced `A · D_θ f` row of the level-six `N`-pairing

The pairing `slotPairing ρ a b (fun z θ => A z θ * D_θ f z θ) f` with `ρ` a leaf weight of the
slot `(a,b)` (`a + b ≤ 6`), the coefficient field `A` priced *flat*
(`|D_z^jD_θ^iA| ≤ KA·z/(1+z)·(if 1 ≤ i then (α + sin 2θ)·sin(2θ)^{α/5} else 1)`) and the datum
`f` in the class `DatData α f M`, is bounded by `C α^{-3}(1+KA)(1+M)(1+HkSq α 6 f)`.

`D_z^bD_θ^a (A·D_θ f)` expands by Leibniz into the sum
`∑_{i≤a, j≤b} C(a,i)C(b,j)·(D_z^jD_θ^iA)·(D_z^{b-j}D_θ^{a-i+1}f)`; the `(0,0)` summand is the
*transport* term, bounded slicewise by an angular integration by parts (`dthZeroSliceAux`) and
then by `slotEnergyZOuter`, while every other summand is bounded pointwise by
`2·KA·HkIntegrand α 6 f` (`summandPt`). -/

theorem rowStarDth : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (KA M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => A z θ * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Cs, hCspos, hslice⟩ := dthZeroSliceAux
  refine ⟨64 * (Cs + 2) + 1, by positivity, ?_⟩
  intro α hαmem A f KA M a b ρ hA hdat hflat hab hleaf
  obtain ⟨hα0, hα1⟩ := hαmem
  obtain ⟨hfsm, hf6, hf7, hvan, haxis, hbdd⟩ := hdat
  -- `KA ≥ 0`
  have hKA0 : 0 ≤ KA := by
    have h := hflat 0 0 (by norm_num) 1 (Real.pi / 4) (by norm_num)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] at h
    have hif : (if (1 : ℕ) ≤ 0 then
        (α + Real.sin (2 * (Real.pi / 4))) * (Real.sin (2 * (Real.pi / 4))) ^ (α / 5)
        else (1 : ℝ)) = 1 := if_neg (by norm_num)
    rw [hif, mul_one] at h
    have h2 : (1 : ℝ) / (1 + 1) = 1 / 2 := by norm_num
    rw [h2] at h
    nlinarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hM0 : 0 ≤ M := le_trans (Real.sqrt_nonneg _) hbdd
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  obtain ⟨q, hρeq, hq0, hqγ, hqη⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.leafW_canon_cases hα0 hleaf
  rw [hρeq]
  have hzfac_le : ∀ z : ℝ, 0 ≤ z → z / (1 + z) ≤ 1 := by
    intro z hz; rw [div_le_one (by linarith)]; linarith
  -- the pointwise bound `|A| ≤ KA` on the open quadrant
  have hAval : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ KA := by
    intro z θ hz hθ0 hθ1
    have h := hflat 0 0 (by norm_num) z θ hz hθ0 hθ1
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] at h
    have hif : (if (1 : ℕ) ≤ 0 then
        (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else (1 : ℝ)) = 1 :=
      if_neg (by norm_num)
    rw [hif, mul_one] at h
    calc |A z θ| ≤ KA * (z / (1 + z)) := h
      _ ≤ KA * 1 := mul_le_mul_of_nonneg_left (hzfac_le z hz.le) hKA0
      _ = KA := by ring
  -- ## the Leibniz identity
  have hleib : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
        = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) f z θ) :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.leibniz_Dth hA hfsm b a
  have hΦeq : (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2)
      =ᵐ[PM] (fun p : ℝ × ℝ => ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
                  * Work.Spaces.mixed j i A p.1 p.2
                  * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2)) := by
    refine ae_of_forall_Qd fun z θ hz hθ0 hθ1 => ?_
    show Work.FTS.TransportS.SlotT2.canonW q z θ
        * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed b a f z θ
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (Work.FTS.TransportS.SlotT2.canonW q z θ
                  * Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                  * Work.Spaces.mixed b a f z θ)
    rw [hleib z θ hz hθ0 hθ1]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    refine Finset.sum_congr rfl fun j hj => ?_
    ring
  -- the transport-term integrand
  have hT1int : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
        * Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) PM := by
    obtain ⟨hHi6, -⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (α := α) (k := 6) hfsm hf6
    obtain ⟨hHi7, -⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (α := α) (k := 7) hfsm hf7
    refine ((hHi7.add hHi6).const_mul (KA / 2)).mono' ?_ ?_
    · refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
      exact (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul hA.continuousOn).mul
        ((hfsm.mixed b a).Dth.continuousOn)).mul (hfsm.mixed b a).continuousOn
    · filter_upwards [ae_PM_Q0] with p hp
      rw [Real.norm_eq_abs]
      exact Work.FTS.StrongPersist.H6Rows.Npair6Aux.zeroTerm_integrand_le α q hKA0 hqγ hqη hab
        hAval hfsm hp.1 ⟨hp.2.1, hp.2.2⟩
  have haeeq00 : (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
        * A p.1 p.2 * Work.Spaces.mixed b (a + 1) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2)
      =ᵐ[PM] fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
        * A p.1 p.2 * Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2 := by
    refine ae_of_forall_Qd fun z θ hz hθ0 hθ1 => ?_
    show Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
        * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ
      = Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ
    rw [Work.FTS.StrongPersist.N6Trans.T1Hon.Dth_mixed_eq hfsm b a hz ⟨hθ0, hθ1⟩]
  -- ## integrability of the individual summands
  have hIntW : ∀ i ∈ Finset.range (a + 1), ∀ j ∈ Finset.range (b + 1),
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
        * Work.Spaces.mixed j i A p.1 p.2
        * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) PM := by
    intro i hi j hj
    have hia : i ≤ a := by have := Finset.mem_range.mp hi; omega
    have hjb : j ≤ b := by have := Finset.mem_range.mp hj; omega
    by_cases h00 : i = 0 ∧ j = 0
    · obtain ⟨hi0, hj0⟩ := h00
      subst hi0; subst hj0
      show MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
        * A p.1 p.2 * Work.Spaces.mixed b (a + 1) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) PM
      exact hT1int.congr haeeq00.symm
    · have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
          * Work.Spaces.mixed j i A p.1 p.2
          * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          (hA.mixed j i).continuousOn).mul
          (hfsm.mixed (b - j) (a - i + 1)).continuousOn).mul (hfsm.mixed b a).continuousOn)
      have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ‖(fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
            * Work.Spaces.mixed j i A p.1 p.2
            * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2) (z, θ)‖
          ≤ (2 * KA) * Work.Spaces.HkIntegrand α 6 f z θ := by
        intro z θ hz hθ0 hθ1
        rw [Real.norm_eq_abs]
        exact summandPt hα0 hα1 hKA0 hflat hf6 hia hjb h00 hab hqγ hqη hz hθ0 hθ1
      exact (Work.FTS.StrongPersist.N6TP.summand_ae_package (α := α) (g := f)
        (F := fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
          * Work.Spaces.mixed j i A p.1 p.2
          * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) (M := 2 * KA)
        hfsm hf6 hcont hpt).1
  -- ## the value bounds of the individual summands
  have hBdW : ∀ i ∈ Finset.range (a + 1), ∀ j ∈ Finset.range (b + 1),
      |∫ p, (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
          * Work.Spaces.mixed j i A p.1 p.2
          * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) ∂PM|
        ≤ (Cs + 2) * KA * Work.Spaces.HkSq α 6 f := by
    intro i hi j hj
    have hia : i ≤ a := by have := Finset.mem_range.mp hi; omega
    have hjb : j ≤ b := by have := Finset.mem_range.mp hj; omega
    by_cases h00 : i = 0 ∧ j = 0
    · obtain ⟨hi0, hj0⟩ := h00
      subst hi0; subst hj0
      show |∫ p, (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed b (a + 1) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) ∂PM| ≤ (Cs + 2) * KA * Work.Spaces.HkSq α 6 f
      rw [MeasureTheory.integral_congr_ae haeeq00]
      rw [MeasureTheory.integral_prod _ hT1int]
      -- the slice energy
      obtain ⟨hJint, hJbd⟩ :=
        Work.FTS.StrongPersist.N6Trans.T1SixAux.slotEnergyZOuter
          (α := α) (q := q) (g := f) hfsm hf6 hq0 hqγ hqη hab
      have hJnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2 :=
        fun z _ => MeasureTheory.integral_nonneg_of_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => mul_nonneg (Work.FTS.TransportS.SlotT2.canonW_nonneg hθ) (sq_nonneg _)))
      have hsl := hslice α ⟨hα0, hα1⟩ A f KA a b q hA hfsm hf6 hKA0 hflat hq0 hqγ hqη hab
      have hpt : ∀ z ∈ Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ|
          ≤ Cs * KA * (∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
              * (Work.Spaces.mixed b a f z θ) ^ 2) := by
        intro z hz'
        have h := hsl z hz'
        have h1 : Cs * KA * (z / (1 + z)) * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2)
            ≤ Cs * KA * (∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2) := by
          have hfac : z / (1 + z) ≤ 1 := hzfac_le z (Set.mem_Ici.mp hz')
          have hnn : 0 ≤ (Cs * KA) * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2) :=
            mul_nonneg (mul_nonneg hCspos.le hKA0) (hJnn z hz')
          nlinarith [hfac, hnn]
        linarith
      have hstep : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ|)
          ≤ ∫ z in Work.Spaces.Iz, Cs * KA * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => abs_nonneg _)
          (hJint.const_mul (Cs * KA))
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
      have hfin0 : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ| ≤ Cs * KA * Work.Spaces.HkSq α 6 f := by
        refine (MeasureTheory.abs_integral_le_integral_abs).trans (hstep.trans ?_)
        rw [MeasureTheory.integral_const_mul]
        exact mul_le_mul_of_nonneg_left hJbd (mul_nonneg hCspos.le hKA0)
      refine hfin0.trans ?_
      have : 0 ≤ KA * Work.Spaces.HkSq α 6 f := mul_nonneg hKA0 hSq0
      nlinarith [hCspos, hKA0, hSq0]
    · have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
          * Work.Spaces.mixed j i A p.1 p.2
          * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          (hA.mixed j i).continuousOn).mul
          (hfsm.mixed (b - j) (a - i + 1)).continuousOn).mul (hfsm.mixed b a).continuousOn)
      have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ‖(fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
            * Work.Spaces.mixed j i A p.1 p.2
            * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2) (z, θ)‖
          ≤ (2 * KA) * Work.Spaces.HkIntegrand α 6 f z θ := by
        intro z θ hz hθ0 hθ1
        rw [Real.norm_eq_abs]
        exact summandPt hα0 hα1 hKA0 hflat hf6 hia hjb h00 hab hqγ hqη hz hθ0 hθ1
      refine (Work.FTS.StrongPersist.N6TP.summand_ae_package (α := α) (g := f)
        (F := fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
          * Work.Spaces.mixed j i A p.1 p.2
          * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) (M := 2 * KA)
        hfsm hf6 hcont hpt).2.trans ?_
      have : 0 ≤ KA * Work.Spaces.HkSq α 6 f := mul_nonneg hKA0 hSq0
      nlinarith [hCspos, hKA0, hSq0]
  -- ## the assembly
  have hIntSum : MeasureTheory.Integrable (fun p : ℝ × ℝ => ∑ i ∈ Finset.range (a + 1),
      ∑ j ∈ Finset.range (b + 1), ((a.choose i : ℝ) * (b.choose j : ℝ))
        * (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
            * Work.Spaces.mixed j i A p.1 p.2
            * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2)) PM := by
    refine rowMulSupAux.integrable_finset_sum _ fun i hi => ?_
    refine rowMulSupAux.integrable_finset_sum _ fun j hj => ?_
    exact (hIntW i hi j hj).const_mul _
  have hIntΦ : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) PM :=
    hIntSum.congr hΦeq.symm
  have hsp := slotPairing_eq_prod (ρv := Work.FTS.TransportS.SlotT2.canonW q) a b
    (u := fun z θ => A z θ * Work.Spaces.Dth f z θ) (v := f) hIntΦ
  have hIntInner : ∀ i ∈ Finset.range (a + 1), MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ))
          * (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
              * Work.Spaces.mixed j i A p.1 p.2
              * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2)) PM := by
    intro i hi
    refine rowMulSupAux.integrable_finset_sum _ fun j hj => ?_
    exact (hIntW i hi j hj).const_mul _
  have hsplit : (∫ p, Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2 ∂PM)
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ))
            * (∫ p, (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
                * Work.Spaces.mixed j i A p.1 p.2
                * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2) ∂PM) := by
    rw [MeasureTheory.integral_congr_ae hΦeq]
    rw [MeasureTheory.integral_finsetSum _ hIntInner]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun j hj => (hIntW i hi j hj).const_mul _)]
    exact Finset.sum_congr rfl fun j hj => MeasureTheory.integral_const_mul _ _
  have hcoef : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
      ((a.choose i : ℝ) * (b.choose j : ℝ))) ≤ 64 := by
    have hch : ∀ n : ℕ, (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : ℝ))
        = (2 : ℝ) ^ n := by
      intro n
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
      norm_num
    have hfull : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℕ) : ℝ) * ((b.choose j : ℕ) : ℝ)) = (2 : ℝ) ^ (a + b) := by
      rw [← Finset.sum_mul_sum, hch a, hch b, ← pow_add]
    calc (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ)))
        = (2 : ℝ) ^ (a + b) := hfull
      _ ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) hab
      _ = 64 := by norm_num
  have hsumBd : |∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ))
          * (∫ p, (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
              * Work.Spaces.mixed j i A p.1 p.2
              * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2) ∂PM)|
      ≤ 64 * (Cs + 2) * KA * Work.Spaces.HkSq α 6 f := by
    have hstep : |∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ))
            * (∫ p, (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
                * Work.Spaces.mixed j i A p.1 p.2
                * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2) ∂PM)|
        ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ))
            * ((Cs + 2) * KA * Work.Spaces.HkSq α 6 f) := by
      calc |∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (∫ p, (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
                  * Work.Spaces.mixed j i A p.1 p.2
                  * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2) ∂PM)|
          ≤ ∑ i ∈ Finset.range (a + 1),
              |∑ j ∈ Finset.range (b + 1), ((a.choose i : ℝ) * (b.choose j : ℝ))
                * (∫ p, (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
                    * Work.Spaces.mixed j i A p.1 p.2
                    * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
                    * Work.Spaces.mixed b a f p.1 p.2) ∂PM)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              |((a.choose i : ℝ) * (b.choose j : ℝ))
                * (∫ p, (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
                    * Work.Spaces.mixed j i A p.1 p.2
                    * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
                    * Work.Spaces.mixed b a f p.1 p.2) ∂PM)| :=
            Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              ((a.choose i : ℝ) * (b.choose j : ℝ))
                * |∫ p, (Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
                    * Work.Spaces.mixed j i A p.1 p.2
                    * Work.Spaces.mixed (b - j) (a - i + 1) f p.1 p.2
                    * Work.Spaces.mixed b a f p.1 p.2) ∂PM| := by
            refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
            rw [abs_mul]
            congr 1
            exact abs_of_nonneg (by positivity)
        _ ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              ((a.choose i : ℝ) * (b.choose j : ℝ))
                * ((Cs + 2) * KA * Work.Spaces.HkSq α 6 f) := by
            refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
            exact mul_le_mul_of_nonneg_left (hBdW i hi j hj) (by positivity)
    refine hstep.trans ?_
    have h1 : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ))
          * ((Cs + 2) * KA * Work.Spaces.HkSq α 6 f))
        = (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ)))
          * ((Cs + 2) * KA * Work.Spaces.HkSq α 6 f) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_mul]
    rw [h1]
    refine (mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ Cs + 2) hKA0) hSq0)).trans (le_of_eq ?_)
    ring
  have hfin : |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.SlotT2.canonW q) a b
        (fun z θ => A z θ * Work.Spaces.Dth f z θ) f|
      ≤ 64 * (Cs + 2) * KA * Work.Spaces.HkSq α 6 f := by
    rw [hsp, hsplit]
    exact hsumBd
  refine hfin.trans ?_
  -- the final arithmetic
  have hα3 : 1 ≤ α ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg hα0.le]
    rw [one_le_inv₀ (Real.rpow_pos_of_pos hα0 3)]
    exact Real.rpow_le_one hα0.le hα1 (by norm_num)
  have hprod : KA * Work.Spaces.HkSq α 6 f
      ≤ (1 + KA) * (1 + Work.Spaces.HkSq α 6 f) := by nlinarith [hKA0, hSq0]
  have hC0 : 0 ≤ 64 * (Cs + 2) := by positivity
  have hbig : 64 * (Cs + 2) * KA * Work.Spaces.HkSq α 6 f
      ≤ (64 * (Cs + 2) + 1) * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have hαM : 1 ≤ α ^ (-(3 : ℝ)) * (1 + M) := by nlinarith [hα3, hM0]
    have hbase : 0 ≤ (1 + KA) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_nonneg (by linarith) (by linarith)
    have step1 : 64 * (Cs + 2) * (KA * Work.Spaces.HkSq α 6 f)
        ≤ 64 * (Cs + 2) * ((1 + KA) * (1 + Work.Spaces.HkSq α 6 f)) :=
      mul_le_mul_of_nonneg_left hprod hC0
    have step2 : 64 * (Cs + 2) * ((1 + KA) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ (64 * (Cs + 2) + 1) * (α ^ (-(3 : ℝ)) * (1 + M))
            * ((1 + KA) * (1 + Work.Spaces.HkSq α 6 f)) := by
      have h1 : 64 * (Cs + 2) ≤ (64 * (Cs + 2) + 1) * (α ^ (-(3 : ℝ)) * (1 + M)) := by
        calc 64 * (Cs + 2) ≤ 64 * (Cs + 2) + 1 := by linarith
          _ ≤ (64 * (Cs + 2) + 1) * (α ^ (-(3 : ℝ)) * (1 + M)) :=
              le_mul_of_one_le_right (by positivity) hαM
      exact mul_le_mul_of_nonneg_right h1 hbase
    calc 64 * (Cs + 2) * KA * Work.Spaces.HkSq α 6 f
        = 64 * (Cs + 2) * (KA * Work.Spaces.HkSq α 6 f) := by ring
      _ ≤ 64 * (Cs + 2) * ((1 + KA) * (1 + Work.Spaces.HkSq α 6 f)) := step1
      _ ≤ (64 * (Cs + 2) + 1) * (α ^ (-(3 : ℝ)) * (1 + M))
            * ((1 + KA) * (1 + Work.Spaces.HkSq α 6 f)) := step2
      _ = (64 * (Cs + 2) + 1) * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by ring
  exact hbig

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## §1. Small helpers

The flat-price star row is proved by a "min-split" Cauchy–Schwarz: the two decay factors
`z/(1+z)` and `z/(1+z)²` of the two coefficient slots are combined into
`(z²/(1+z)³)²`, whose `w²`-weighted integral collapses to `∫ (1+z)^{-2} = 1`. -/

/-- `(z/(1+z))²·(z/(1+z)²)² = (z²/(1+z)³)²`. -/
theorem pq_sq_eq {z : ℝ} (hz1 : 1 + z ≠ 0) :
    ((z / (1 + z)) * (z / (1 + z) ^ 2)) ^ 2 = (z ^ 2 / (1 + z) ^ 3) ^ 2 := by
  rw [show (z / (1 + z)) * (z / (1 + z) ^ 2) = z ^ 2 / (1 + z) ^ 3 by field_simp]

/-- The two angular powers of the `a ≥ 1` case combine:
`σ^{-γ}·(8192·σ^{α/5})² = 8192²·σ^{-1+3α/10}`. -/
theorem gam_sigma_combine {σ α : ℝ} (hσ : 0 < σ) :
    σ ^ (-(Work.Spaces.gam α)) * ((8192 : ℝ) * σ ^ (α / 5)) ^ 2
      = (8192 : ℝ) ^ 2 * σ ^ (-1 + 3 * α / 10) := by
  have h2 : (σ ^ (α / 5)) ^ 2 = σ ^ (2 * α / 5) := by
    rw [← Real.rpow_natCast (σ ^ (α / 5)) 2, ← Real.rpow_mul hσ.le]
    congr 1
    ring
  have h3 : σ ^ (-(Work.Spaces.gam α)) * σ ^ (2 * α / 5) = σ ^ (-1 + 3 * α / 10) := by
    rw [← Real.rpow_add hσ]
    congr 1
    rw [Work.Spaces.gam]
    ring
  rw [mul_pow, h2, ← h3]
  ring

/-- The pointwise input of the two-weight Cauchy–Schwarz for the pairing `ρ·X·Z`. -/
theorem abs_mul_one_sq_le {ρ X Z : ℝ} (hρ : 0 ≤ ρ) :
    |ρ * X * 1 * Z| ≤ 1 * (Real.sqrt (ρ * X ^ 2) * Real.sqrt (ρ * Z ^ 2)) := by
  have hs : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ
  have h1 : Real.sqrt (ρ * X ^ 2) = Real.sqrt ρ * |X| := by
    rw [Real.sqrt_mul hρ, Real.sqrt_sq_eq_abs]
  have h2 : Real.sqrt (ρ * Z ^ 2) = Real.sqrt ρ * |Z| := by
    rw [Real.sqrt_mul hρ, Real.sqrt_sq_eq_abs]
  have hA : |ρ * X * 1 * Z| = ρ * |X| * |Z| := by
    rw [abs_mul, abs_mul, abs_mul, abs_one, abs_of_nonneg hρ]
    ring
  rw [hA, h1, h2, one_mul]
  have h7 : ρ * |X| ≤ (Real.sqrt ρ * Real.sqrt ρ) * |X| :=
    mul_le_mul_of_nonneg_right (le_of_eq hs.symm) (abs_nonneg X)
  calc ρ * |X| * |Z| = (ρ * |X|) * |Z| := by ring
    _ ≤ ((Real.sqrt ρ * Real.sqrt ρ) * |X|) * |Z| := mul_le_mul_of_nonneg_right h7 (abs_nonneg Z)
    _ = Real.sqrt ρ * |X| * (Real.sqrt ρ * |Z|) := by ring

/-! ## §2. The `zWeight_flat` estimate in product-measure form -/

/-- `FlatP.zWeight_flat` transported to the product measure `PM` of `(dz|Iz) ⊗ (dθ|Iθ)`. -/
theorem zWeight_flat_PM {E : ℝ → ℝ} {B : ℝ}
    (hbint : MeasureTheory.IntegrableOn E Work.Spaces.Iθ)
    (hble : (∫ θ in Work.Spaces.Iθ, E θ) ≤ B) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * E p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) PM ∧
    (∫ p, (Work.Spaces.w p.1) ^ 2 * E p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2 ∂PM) ≤ B := by
  obtain ⟨h1, h2⟩ := FlatP.zWeight_flat E B hbint hble
  rw [FlatP.PM_eq_restrict]
  exact ⟨h1, h2⟩

/-! ## §3. The final arithmetic -/

/-- **The final arithmetic.**  With `D₀ = 819200²`, the Cauchy–Schwarz output
`√((KA·KQ)²·D₀/α)·√(H)` is bounded by `10⁷·α^{-3}·(1+KA)(1+KQ)(1+M)(1+H)` for
`α ∈ (0,1]` and nonnegative data. -/
theorem final_arith {α KA KQ M H : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hKA0 : 0 ≤ KA) (hKQ0 : 0 ≤ KQ) (hM0 : 0 ≤ M) (hH0 : 0 ≤ H) :
    Real.sqrt ((KA * KQ) ^ 2 * (((819200 : ℝ) ^ 2) / α)) * Real.sqrt H
      ≤ 10000000 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M) * (1 + H) := by
  have hy1 : (1 : ℝ) ≤ 1 / α := by rw [one_le_div hα0]; exact hα1
  have hrpow : α ^ (-(3 : ℝ)) = (1 / α) ^ 3 := by
    have h3 : α ^ (3 : ℝ) = α ^ 3 := Real.rpow_natCast α 3
    rw [Real.rpow_neg hα0.le, h3, one_div, inv_pow]
  have hsqrt1 : Real.sqrt ((1 : ℝ) / α) ≤ α ^ (-(3 : ℝ)) := by
    rw [hrpow, Real.sqrt_le_left (by positivity)]
    have h5 : (1 : ℝ) ≤ (1 / α) ^ 5 := one_le_pow₀ hy1
    nlinarith [hy1, h5]
  have hsqrtD : Real.sqrt (((819200 : ℝ) ^ 2) / α) = 819200 * Real.sqrt (1 / α) := by
    rw [show ((819200 : ℝ) ^ 2) / α = (819200 : ℝ) ^ 2 * (1 / α) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (819200 : ℝ) ^ 2), Real.sqrt_sq (by norm_num)]
  have h1 : Real.sqrt ((KA * KQ) ^ 2 * (((819200 : ℝ) ^ 2) / α))
      = (KA * KQ) * (819200 * Real.sqrt (1 / α)) := by
    rw [Real.sqrt_mul (sq_nonneg (KA * KQ)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hKA0 hKQ0), hsqrtD]
  have e2 : Real.sqrt H ≤ 1 + H := by nlinarith [Real.sq_sqrt hH0, Real.sqrt_nonneg H]
  have e3 : KA * KQ ≤ (1 + KA) * (1 + KQ) := by nlinarith
  have e4 : (819200 : ℝ) ≤ 10000000 * (1 + M) := by nlinarith
  have hnA : (0 : ℝ) ≤ 1 + KA := by linarith
  have hnQ : (0 : ℝ) ≤ 1 + KQ := by linarith
  have hnH : (0 : ℝ) ≤ 1 + H := by linarith
  calc Real.sqrt ((KA * KQ) ^ 2 * (((819200 : ℝ) ^ 2) / α)) * Real.sqrt H
      = (KA * KQ) * (819200 * Real.sqrt (1 / α)) * Real.sqrt H := by rw [h1]
    _ ≤ ((1 + KA) * (1 + KQ)) * (819200 * α ^ (-(3 : ℝ))) * (1 + H) := by
        have hb : 819200 * Real.sqrt (1 / α) ≤ 819200 * α ^ (-(3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrt1 (by norm_num)
        have h12 : (KA * KQ) * (819200 * Real.sqrt (1 / α))
            ≤ ((1 + KA) * (1 + KQ)) * (819200 * α ^ (-(3 : ℝ))) :=
          mul_le_mul e3 hb (by positivity) (by positivity)
        exact mul_le_mul h12 e2 (Real.sqrt_nonneg H) (by positivity)
    _ ≤ 10000000 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M) * (1 + H) := by
        have hfac : (0 : ℝ) ≤ (1 + KA) * (1 + KQ) * α ^ (-(3 : ℝ)) * (1 + H) := by positivity
        have h := mul_le_mul_of_nonneg_right e4 hfac
        calc ((1 + KA) * (1 + KQ)) * (819200 * α ^ (-(3 : ℝ))) * (1 + H)
            = 819200 * ((1 + KA) * (1 + KQ) * α ^ (-(3 : ℝ)) * (1 + H)) := by ring
          _ ≤ (10000000 * (1 + M)) * ((1 + KA) * (1 + KQ) * α ^ (-(3 : ℝ)) * (1 + H)) := h
          _ = 10000000 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M) * (1 + H) := by ring

/-! ## §4. The row -/

theorem rowStarP : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A Q f : Work.FTS.Galerkin.Fn) (KA KQ M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen Q →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) →
      (∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i Q z θ| ≤ KQ * (z / (1 + z) ^ 2) *
            (if 1 ≤ i then (Real.sin (2 * θ)) ^ (α / 3) else 1)) →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Q z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by
  refine ⟨10000000, by norm_num, ?_⟩
  intro α hα A Q f KA KQ M a b ρ hA hQ hdat hAdec hQdec hab hleaf
  obtain ⟨hα0, hα1⟩ := hα
  -- nonnegativity of the two prices
  have hka : 0 ≤ KA := by
    have h := hAdec 0 0 (by omega) 1 (Real.pi / 4) (by norm_num)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] at h
    have h2 : (1 : ℝ) / (1 + 1) = 1 / 2 := by norm_num
    rw [h2] at h
    rw [if_neg (by norm_num : ¬ 1 ≤ (0 : ℕ))] at h
    nlinarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hkq : 0 ≤ KQ := by
    have h := hQdec 0 0 (by omega) 1 (Real.pi / 4) (by norm_num)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] at h
    have h2 : (1 : ℝ) / (1 + 1) ^ 2 = 1 / 4 := by norm_num
    rw [h2] at h
    rw [if_neg (by norm_num : ¬ 1 ≤ (0 : ℕ))] at h
    nlinarith [abs_nonneg (Q 1 (Real.pi / 4))]
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX : Work.FTS.EllipticEst.SmoothOpen (fun z θ => A z θ * Q z θ) :=
    FlatP.smoothOpen_mul hA hQ
  have habs := FlatP.abs_mixed_mul_le hα0 hα1 hA hQ hAdec hQdec hab
  -- the `L²` mass of the product slot
  have hpmass : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ρ p.1 p.2 * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2) PM ∧
      (∫ p, ρ p.1 p.2
          * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2 ∂PM)
        ≤ (KA * KQ) ^ 2 * (((819200 : ℝ) ^ 2) / α) := by
    rcases le_or_gt 1 a with ha1 | ha1
    · -- ## `1 ≤ a`: the angular profile `8192²·σ^{-1+3α/10}`
      have hσ := Work.Spaces.sin_two_rpow (-1 + 3 * α / 10) (by linarith) (by nlinarith)
      have hbint : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-1 + 3 * α / 10))
          Work.Spaces.Iθ := hσ.1.const_mul _
      have hble : (∫ θ in Work.Spaces.Iθ,
            (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-1 + 3 * α / 10))
          ≤ (8192 : ℝ) ^ 2 * (10000 / α) := by
        rw [MeasureTheory.integral_const_mul]
        have h := hσ.2
        have hp1 : -1 + 3 * α / 10 + 1 = 3 * α / 10 := by ring
        rw [hp1] at h
        have h2 : 100 / (3 * α / 10) = 1000 / (3 * α) := by
          field_simp
          ring
        rw [h2] at h
        have h3 : 1000 / (3 * α) ≤ 10000 / α := by
          rw [div_le_div_iff₀ (by positivity) hα0]
          nlinarith
        exact le_trans (mul_le_mul_of_nonneg_left h (by norm_num))
          (mul_le_mul_of_nonneg_left h3 (by norm_num))
      have hDg := zWeight_flat_PM hbint hble
      have hdom := FlatP.domAQ (a := a) (b := b) (E := fun θ : ℝ =>
            (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-1 + 3 * α / 10))
          (B := (8192 : ℝ) ^ 2 * (10000 / α)) hka hkq hA hQ hleaf hDg ?_
      · refine ⟨hdom.1, le_trans hdom.2 (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))⟩
        rw [show (8192 : ℝ) ^ 2 * (10000 / α) = ((819200 : ℝ) ^ 2) / α by ring]
      · intro z θ hz hθ0 hθ1
        have hσp : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
        have hz1 : (1 + z) ≠ 0 := by positivity
        have hρle := leafW_le_canonW_gam hα0 hleaf z θ hz hθ0 hθ1
        have hρle' : ρ z θ
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          simpa only [leafGam_eq_canonW, FlatP.canonW_eq] using hρle
        have habs' := habs z θ hz hθ0 hθ1
        rw [if_pos ha1] at habs'
        have hXsq : (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ) ^ 2
            ≤ (KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2)
                * (8192 * (Real.sin (2 * θ)) ^ (α / 5))) ^ 2 :=
          sq_le_sq' (by linarith [abs_le.mp habs']) (abs_le.mp habs').2
        have hw0 : 0 ≤ (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσp.le _)
        calc ρ z θ * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ) ^ 2
            ≤ ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                * (KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2)
                    * (8192 * (Real.sin (2 * θ)) ^ (α / 5))) ^ 2 :=
              le_trans (mul_le_mul_of_nonneg_right hρle' (sq_nonneg _))
                (mul_le_mul_of_nonneg_left hXsq hw0)
          _ = (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (8192 * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2)
                * ((z / (1 + z)) * (z / (1 + z) ^ 2)) ^ 2) := by ring
          _ = (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-1 + 3 * α / 10))
                * ((z / (1 + z)) * (z / (1 + z) ^ 2)) ^ 2) := by
              rw [gam_sigma_combine hσp]
          _ = (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-1 + 3 * α / 10))
                * (z ^ 2 / (1 + z) ^ 3) ^ 2) := by
              rw [pq_sq_eq hz1]
    · -- ## `a = 0`: the angular profile `8192²·σ^{-η}`
      have ha0 : a = 0 := by omega
      subst ha0
      have hσ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
        (by norm_num [Work.Spaces.eta])
      have hbint : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          Work.Spaces.Iθ := hσ.1.const_mul _
      have hble : (∫ θ in Work.Spaces.Iθ,
            (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ (8192 : ℝ) ^ 2 * 10000 := by
        rw [MeasureTheory.integral_const_mul]
        have h := hσ.2
        have hp1 : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by norm_num [Work.Spaces.eta]
        rw [hp1] at h
        rw [show (100 : ℝ) / (1 / 100) = 10000 by norm_num] at h
        exact mul_le_mul_of_nonneg_left h (by norm_num)
      have hDg := zWeight_flat_PM hbint hble
      have hdom := FlatP.domAQ (a := 0) (b := b) (E := fun θ : ℝ =>
            (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          (B := (8192 : ℝ) ^ 2 * 10000) hka hkq hA hQ hleaf hDg ?_
      · refine ⟨hdom.1, le_trans hdom.2 (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))⟩
        rw [show (8192 : ℝ) ^ 2 * 10000 = ((819200 : ℝ) ^ 2) by ring]
        rw [le_div_iff₀ hα0]
        nlinarith
      · intro z θ hz hθ0 hθ1
        have hz1 : (1 + z) ≠ 0 := by positivity
        have hρle := leafW_le_canonW_eta hleaf z θ hz hθ0 hθ1
        have hρle' : ρ z θ
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          simpa only [leafEta_eq_canonW, FlatP.canonW_eq] using hρle
        have hσnn : 0 ≤ Real.sin (2 * θ) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
        have habs' := habs z θ hz hθ0 hθ1
        rw [if_neg (by omega : ¬ 1 ≤ (0 : ℕ))] at habs'
        have hXsq : (Work.Spaces.mixed b 0 (fun z θ => A z θ * Q z θ) z θ) ^ 2
            ≤ (KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2) * 8192) ^ 2 :=
          sq_le_sq' (by linarith [abs_le.mp habs']) (abs_le.mp habs').2
        have hw0 : 0 ≤ (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσnn _)
        calc ρ z θ * (Work.Spaces.mixed b 0 (fun z θ => A z θ * Q z θ) z θ) ^ 2
            ≤ ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                * (KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2) * 8192) ^ 2 :=
              le_trans (mul_le_mul_of_nonneg_right hρle' (sq_nonneg _))
                (mul_le_mul_of_nonneg_left hXsq hw0)
          _ = (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                * ((z / (1 + z)) * (z / (1 + z) ^ 2)) ^ 2) := by ring
          _ = (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                * (z ^ 2 / (1 + z) ^ 3) ^ 2) := by
              rw [pq_sq_eq hz1]
  -- the `L²` mass of the datum slot
  have hfmass : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2) PM ∧
      (∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2 ∂PM)
        ≤ Work.Spaces.HkSq α 6 f :=
    val_le_HkSq hdat.sm hdat.h6 (leafW_nonneg hleaf)
      (fun z θ hz hθ0 hθ1 => FlatP.fSlot_le_HkIntegrand hα0 hab hleaf hz hθ0 hθ1)
      ((aesm_leafW hleaf).mul ((aesm_mixed hdat.sm b a).pow 2))
  -- the Cauchy–Schwarz pairing
  obtain ⟨hint, hbd⟩ := rowSummand_core
    (α := α) (KY := 1) (AX := (KA * KQ) ^ 2 * (((819200 : ℝ) ^ 2) / α))
    (AZ := Work.Spaces.HkSq α 6 f)
    (f := f) (X := fun z θ => Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ)
    (Y := fun _ _ => (1 : ℝ)) (Z := fun z θ => Work.Spaces.mixed b a f z θ)
    (ρv := ρ) (ρ₁ := ρ) (ρ₂ := ρ)
    (by norm_num) (by positivity) hSq0 (leafW_nonneg hleaf) hpmass.1 hfmass.1
    hpmass.2 hfmass.2
    (ae_of_forall_Qd fun z θ hz hθ0 hθ1 => leafW_nonneg hleaf z θ hz hθ0 hθ1)
    (ae_of_forall_Qd fun z θ hz hθ0 hθ1 => leafW_nonneg hleaf z θ hz hθ0 hθ1)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hpmass.1.aestronglyMeasurable)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hfmass.1.aestronglyMeasurable)
    (aesm_leafW hleaf) (aesm_mixed hX b a) aestronglyMeasurable_const (aesm_mixed hdat.sm b a)
    (fun z θ hz hθ0 hθ1 =>
      abs_mul_one_sq_le (leafW_nonneg hleaf z θ hz hθ0 hθ1))
  -- convert `∫ ρ·X·Z` into the slot pairing
  have hEq : (fun p : ℝ × ℝ => ρ p.1 p.2
        * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2)
        * (1 : ℝ) * Work.Spaces.mixed b a f p.1 p.2)
      = fun p : ℝ × ℝ => ρ p.1 p.2
        * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2)
        * Work.Spaces.mixed b a f p.1 p.2 := by
    funext p; ring
  have hint' : MeasureTheory.Integrable (Function.uncurry (fun z θ => ρ z θ
      * Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ
      * Work.Spaces.mixed b a f z θ)) PM := by
    have h : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2)
        * Work.Spaces.mixed b a f p.1 p.2) PM := hint.congr (by rw [hEq])
    exact h
  rw [slotPairing_eq_prod (ρv := ρ) (u := fun z θ => A z θ * Q z θ) (v := f) a b hint']
  rw [← hEq]
  refine le_trans hbd (le_trans (le_of_eq (by ring)) (final_arith hα0 hα1 hka hkq hM0 hSq0))

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
