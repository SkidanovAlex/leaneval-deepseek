import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.Blocks.IMC.cs_integral_mul_le
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.TransportS.HardDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

-- The product measure `(volume ↾ Iz) ⊗ (volume ↾ Iθ)` on which the slot pairing lives,
-- written once so that the proof below stays readable.  This is *notation only*: it
-- introduces no declaration and the theorem statement is unchanged.
local notation "μP" => MeasureTheory.Measure.prod (MeasureTheory.volume.restrict Work.Spaces.Iz)
  (MeasureTheory.volume.restrict Work.Spaces.Iθ)

theorem slotPairCS :
    ∀ (α : ℝ) (A f X Y Z : ℝ → ℝ → ℝ) (ρ : ℝ → ℝ → ℝ) (k : ℕ) (B : ℝ),
      α ∈ Set.Ioc 0 1 → k ≤ 6 →
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α k A →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      0 ≤ B →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ) →
      ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2 * |X p.1 p.2| * |Z p.1 p.2|)
        Work.FTS.LocData.Qd →
      ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2)
        Work.FTS.LocData.Qd →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Y z θ| ≤ B) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * |X z θ| * |Z z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α k A z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2
          * Z p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ B * (Real.sqrt (Work.Spaces.HkSq α k A)
            * Real.sqrt (Work.Spaces.HkSq α 6 f)) := by
  intro α A f X Y Z ρ k B _hα _hk hsmA hmA hsmf hmf hB hρnn _hcontAZ hcontXYZ hY hpt
  -- The two `ℋ^k`-integrands are product-integrable with integrals `HkSq`.
  obtain ⟨hintA, hvalA⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsmA hmA
  obtain ⟨hintF, hvalF⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsmf hmf
  -- Almost every point of the product measure lies in the open quadrant, where the
  -- pointwise hypotheses live.
  have haeQd : ∀ᵐ p ∂μP, p ∈ Work.FTS.LocData.Qd := by
    have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
    have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2)).symm
    have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
        =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume] Work.FTS.LocData.Qd :=
      MeasureTheory.Measure.set_prod_ae_eq hz hθ
    have hμQd : μP = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
        Work.FTS.LocData.Qd := by
      rw [← MeasureTheory.Measure.restrict_congr_set hprod,
        ← MeasureTheory.Measure.prod_restrict]
    rw [hμQd]
    exact MeasureTheory.ae_restrict_mem ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)
  -- The pointwise domination almost everywhere: fold the `|Y| ≤ B` and the
  -- Cauchy–Schwarz input `ρ |X| |Z| ≤ √(HkIntegrand α k A) √(HkIntegrand α 6 f)`.
  have hdom : ∀ᵐ p ∂μP, ‖ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2‖ ≤
      B * (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) := by
    filter_upwards [haeQd] with p hp
    have hz : 0 < p.1 := hp.1
    have hθ1 : 0 < p.2 := hp.2.1
    have hθ2 : p.2 < Real.pi / 2 := hp.2.2
    rw [Real.norm_eq_abs]
    have hAZnn : 0 ≤ ρ p.1 p.2 * |X p.1 p.2| * |Z p.1 p.2| :=
      mul_nonneg (mul_nonneg (hρnn p.1 p.2 hz hθ1 hθ2) (abs_nonneg _)) (abs_nonneg _)
    calc |ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2|
        = (ρ p.1 p.2 * |X p.1 p.2| * |Z p.1 p.2|) * |Y p.1 p.2| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hρnn p.1 p.2 hz hθ1 hθ2)]
          ring
      _ ≤ (ρ p.1 p.2 * |X p.1 p.2| * |Z p.1 p.2|) * B :=
          mul_le_mul_of_nonneg_left (hY p.1 p.2 hz hθ1 hθ2) hAZnn
      _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) * B :=
          mul_le_mul_of_nonneg_right (hpt p.1 p.2 hz hθ1 hθ2) hB
      _ = B * (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) := by ring
  have hdomAbs : ∀ᵐ p ∂μP, |ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2| ≤
      B * (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) := by
    simpa only [Real.norm_eq_abs] using hdom
  -- Measurability and square-integrability of the two square roots.
  have hAmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)) μP :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hintA.aestronglyMeasurable
  have hFmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) μP :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hintF.aestronglyMeasurable
  have hAsq : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2) ^ 2) μP :=
    hintA.congr (Filter.Eventually.of_forall
      (fun p => (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k A p.1 p.2)).symm))
  have hFsq : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2) ^ 2) μP :=
    hintF.congr (Filter.Eventually.of_forall
      (fun p => (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 6 f p.1 p.2)).symm))
  have hAlp : MeasureTheory.MemLp
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)) 2 μP :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAmeas).mpr hAsq
  have hFlp : MeasureTheory.MemLp
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) 2 μP :=
    (MeasureTheory.memLp_two_iff_integrable_sq hFmeas).mpr hFsq
  -- The product of the two square roots is integrable (Hölder), so the dominating
  -- function of the slot pairing is integrable.
  have hprodint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) μP :=
    MeasureTheory.memLp_one_iff_integrable.mp (hAlp.mul hFlp)
  have hdomInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => B * (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2))) μP :=
    hprodint.const_mul B
  have hmeasXYZ : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2) μP :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontXYZ
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2) μP :=
    hdomInt.mono' hmeasXYZ hdom
  -- Cauchy–Schwarz for the two square roots, with the `HkSq` identification.
  have hcs := Work.Blocks.IMC.cs_integral_mul_le μP hAmeas hFmeas hAsq hFsq
  have eA : (∫ p, Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2) ^ 2 ∂μP)
      = Work.Spaces.HkSq α k A := by
    rw [← hvalA]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun p => Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k A p.1 p.2)))
  have eF : (∫ p, Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2) ^ 2 ∂μP)
      = Work.Spaces.HkSq α 6 f := by
    rw [← hvalF]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun p => Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 6 f p.1 p.2)))
  have hle : (∫ p, Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2) ∂μP) ≤
      Real.sqrt (Work.Spaces.HkSq α k A) * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
    rw [eA, eF] at hcs
    exact le_trans (le_abs_self _) hcs
  have h1 : |∫ p, ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2 ∂μP| ≤
      B * (∫ p, Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2) ∂μP) := by
    calc |∫ p, ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2 ∂μP|
        ≤ ∫ p, |ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2| ∂μP :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ p, B * (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) ∂μP :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun p => abs_nonneg _)) hdomInt hdomAbs
      _ = B * (∫ p, Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2) ∂μP) :=
          MeasureTheory.integral_const_mul B
            (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
              * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2))
  exact ⟨hInt, le_trans h1 (mul_le_mul_of_nonneg_left hle hB)⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
