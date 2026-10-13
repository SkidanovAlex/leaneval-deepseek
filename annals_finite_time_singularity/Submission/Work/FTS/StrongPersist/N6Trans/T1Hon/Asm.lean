import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Cont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The per-slot `T1` transport bound in the honest class.** -/
theorem slotPairing_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.DecayAll 4 g →
      ∀ (a b : ℕ), a + b ≤ 4 → ∀ (q : ℝ),
        (a = 0 → q = 0 ∨ q = Work.Spaces.eta) →
        (1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) →
        |Work.FTS.TransportS.slotPairing (t1W q) a b
            (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
          ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
              * Work.Spaces.HkSq α 4 g := by
  obtain ⟨CH, hCHpos, hCH⟩ := HardSlotLemGen
  obtain ⟨CE, hCEpos, hCE⟩ := EasyLeibIntBound
  refine ⟨CH + 36 * CE, by nlinarith [hCHpos, hCEpos], ?_⟩
  intro α f g hα hα1 hf hmf hg hmg hdg a b hab q hq0 hqa
  obtain ⟨hEEint, hEEle⟩ := SlotWeightHkSq α g a b q hα hα1 hg hmg hab hq0 hqa
  obtain ⟨hELint, hELle⟩ := hCE α f g hα hα1 hf hmf hg hmg hdg
  set u : ℝ → ℝ → ℝ := fun z θ => f z θ * Work.Spaces.Dth g z θ with hu
  -- ### integrability of the easy majorant
  have hSEint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => slotEasySum α f g a b p.1 p.2) Work.FTS.H2.pm :=
    MeasureTheory.Integrable.mono' hELint
      (Work.FTS.H2.aesm_of_Qd (continuousOn_slotEasySum α hf hg a b))
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (slotEasySum_nonneg α f g a b p.1 p.2)]
        exact slotEasySum_le_EasyLeib hab p.1 p.2)
  have hEAint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => t1EasyAbs q f g a b p.1 p.2) Work.FTS.H2.pm :=
    MeasureTheory.Integrable.mono' (hSEint.const_mul 36)
      (Work.FTS.H2.aesm_of_Qd (continuousOn_t1EasyAbs hf hg a b q))
      (by
        filter_upwards [ae_pm_mem_Qd_T1Hon] with p hp
        rw [Real.norm_of_nonneg (t1EasyAbs_nonneg q f g a b p.1 p.2)]
        exact t1EasyAbs_le hα hab hq0 hqa hp.1 hp.2)
  -- ### the `z`-integral of the easy majorant
  have hEz_int : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ)
      (volume.restrict Work.Spaces.Iz) := hEAint.integral_prod_left
  have hEz_le : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ)
      ≤ 36 * (CE / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g) := by
    rw [MeasureTheory.integral_integral hEAint]
    have h1 : ∫ p, t1EasyAbs q f g a b p.1 p.2 ∂Work.FTS.H2.pm
        ≤ ∫ p, (36 : ℝ) * slotEasySum α f g a b p.1 p.2 ∂Work.FTS.H2.pm :=
      MeasureTheory.integral_mono_ae hEAint (hSEint.const_mul 36)
        (by
          filter_upwards [ae_pm_mem_Qd_T1Hon] with p hp
          exact t1EasyAbs_le hα hab hq0 hqa hp.1 hp.2)
    have h2 : ∫ p, (36 : ℝ) * slotEasySum α f g a b p.1 p.2 ∂Work.FTS.H2.pm
        = 36 * ∫ p, slotEasySum α f g a b p.1 p.2 ∂Work.FTS.H2.pm :=
      MeasureTheory.integral_const_mul 36 _
    have h3 : ∫ p, slotEasySum α f g a b p.1 p.2 ∂Work.FTS.H2.pm
        ≤ ∫ p, Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2 ∂Work.FTS.H2.pm :=
      MeasureTheory.integral_mono_ae hSEint hELint
        (Filter.Eventually.of_forall fun p => slotEasySum_le_EasyLeib hab p.1 p.2)
    calc ∫ p, t1EasyAbs q f g a b p.1 p.2 ∂Work.FTS.H2.pm
        ≤ ∫ p, (36 : ℝ) * slotEasySum α f g a b p.1 p.2 ∂Work.FTS.H2.pm := h1
      _ = 36 * ∫ p, slotEasySum α f g a b p.1 p.2 ∂Work.FTS.H2.pm := h2
      _ ≤ 36 * ∫ p, Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2 ∂Work.FTS.H2.pm :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ ≤ 36 * (CE / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g) := mul_le_mul_of_nonneg_left hELle (by norm_num)
  -- ### the `z`-integral of the hard bound
  have hHb_int : MeasureTheory.Integrable
      (fun z => CH / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
        * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
      (volume.restrict Work.Spaces.Iz) :=
    hEEint.const_mul (CH / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f)
  have hHb_le : (∫ z in Work.Spaces.Iz, CH / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.Spaces.HkNorm α 4 f
        * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
      ≤ CH / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hEEle
      (mul_nonneg (div_nonneg hCHpos.le (Real.sqrt_nonneg _))
        (Work.Spaces.HkNorm_nonneg α 4 f))
  -- ### the Leibniz identity
  have hId : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      t1W q z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a g z θ
        = t1Hard q f g a b z θ + t1Easy q f g a b z θ := by
    intro z θ hz hθ
    rw [hu]
    have hlei := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a f
      (fun z θ => Work.Spaces.Dth g z θ) hf (hg.Dth) z θ hz hθ.1 hθ.2
    have hsplit : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
            * (Work.Spaces.mixed b1 a1 f z θ
               * Work.Spaces.mixed (b - b1) (a - a1) (Work.Spaces.Dth g) z θ))
        = (f z θ * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ)
          + (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
              (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
                ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
                  * (Work.Spaces.mixed b1 a1 f z θ
                     * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ))) := by
      rw [sum_split_zero a b (fun a1 b1 => ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
        * (Work.Spaces.mixed b1 a1 f z θ
           * Work.Spaces.mixed (b - b1) (a - a1) (Work.Spaces.Dth g) z θ))]
      congr 1
      · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
          Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero]
        rw [mixed_Dth, ← Dth_mixed_eq hg b a hz hθ]
      · refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun b1 _ => ?_
        by_cases hh : a1 = 0 ∧ b1 = 0
        · rw [if_pos hh, if_pos hh]
        · rw [if_neg hh, if_neg hh]
          rw [mixed_Dth]
    rw [hlei, hsplit]
    simp only [t1Hard, t1Easy, t1Leib]
    ring
  -- ### the pointwise-in-`z` bound
  have hpt : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      |∫ θ in Work.Spaces.Iθ, t1W q z θ * Work.Spaces.mixed b a u z θ
          * Work.Spaces.mixed b a g z θ|
        ≤ (CH / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ) := by
    filter_upwards [ae_Iz_pos, hEAint.prod_right_ae] with z hzpos hEaz
    have hEz_nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ :=
      MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ _ => t1EasyAbs_nonneg q f g a b z θ))
    have hHb_nn : 0 ≤ CH / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
        * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) :=
      mul_nonneg (mul_nonneg (div_nonneg hCHpos.le (Real.sqrt_nonneg _))
        (Work.Spaces.HkNorm_nonneg α 4 f))
        (mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => mul_nonneg (sq_nonneg _)
              (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)))))
    have hTe_int : MeasureTheory.Integrable (fun θ => t1Easy q f g a b z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.Integrable.mono' hEaz
        (Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => t1Easy q f g a b p.1 p.2)
          (continuousOn_t1Easy hf hg a b q) hzpos)
        (Filter.Eventually.of_forall fun θ => by
          rw [Real.norm_eq_abs]; exact abs_t1Easy_le q f g a b z θ)
    have hhard : |∫ θ in Work.Spaces.Iθ, t1Hard q f g a b z θ|
        ≤ CH / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) :=
      hCH α f g q hα hα1 hf hmf hg hmg hdg a b hab hq0 hqa z
        (Set.mem_Ici.mpr hzpos.le)
    have heasy : |∫ θ in Work.Spaces.Iθ, t1Easy q f g a b z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ :=
      le_trans MeasureTheory.abs_integral_le_integral_abs
        (MeasureTheory.integral_mono_ae hTe_int.abs hEaz
          (Filter.Eventually.of_forall fun θ => abs_t1Easy_le q f g a b z θ))
    have hcongr : (∫ θ in Work.Spaces.Iθ, t1W q z θ * Work.Spaces.mixed b a u z θ
          * Work.Spaces.mixed b a g z θ)
        = ∫ θ in Work.Spaces.Iθ, (t1Hard q f g a b z θ + t1Easy q f g a b z θ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [ae_Iθ_mem_Ioo] with θ hθ
      exact hId z θ hzpos hθ
    by_cases hAint : MeasureTheory.Integrable (fun θ => t1Hard q f g a b z θ)
        (volume.restrict Work.Spaces.Iθ)
    · rw [hcongr, MeasureTheory.integral_add hAint hTe_int]
      exact le_trans (abs_add_le _ _) (add_le_add hhard heasy)
    · have hnot : ¬ MeasureTheory.Integrable
          (fun θ => t1Hard q f g a b z θ + t1Easy q f g a b z θ)
          (volume.restrict Work.Spaces.Iθ) := fun hh =>
        hAint ((hh.sub hTe_int).congr (Filter.Eventually.of_forall fun θ => by
          simp only [Pi.sub_apply, Pi.add_apply]; ring))
      rw [hcongr, MeasureTheory.integral_undef hnot, abs_zero]
      exact add_nonneg hHb_nn hEz_nn
  -- ### assembly
  have hmain : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        t1W q z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a g z θ|
      ≤ ∫ z in Work.Spaces.Iz, ((CH / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ)) := by
    refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
    have hrhs : MeasureTheory.Integrable
        (fun z => (CH / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ))
        (volume.restrict Work.Spaces.Iz) := hHb_int.add hEz_int
    by_cases hI : MeasureTheory.Integrable
        (fun z => |∫ θ in Work.Spaces.Iθ, t1W q z θ * Work.Spaces.mixed b a u z θ
          * Work.Spaces.mixed b a g z θ|) (volume.restrict Work.Spaces.Iz)
    · exact MeasureTheory.integral_mono_ae hI hrhs hpt
    · rw [MeasureTheory.integral_undef hI]
      refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun z => ?_)
      have h1 : 0 ≤ CH / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
          * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) :=
        mul_nonneg (mul_nonneg (div_nonneg hCHpos.le (Real.sqrt_nonneg _))
          (Work.Spaces.HkNorm_nonneg α 4 f))
          (mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
              (fun θ hθ => mul_nonneg (sq_nonneg _)
                (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)))))
      have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ :=
        MeasureTheory.integral_nonneg_of_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ _ => t1EasyAbs_nonneg q f g a b z θ))
      exact add_nonneg h1 h2
  have hslot : Work.FTS.TransportS.slotPairing (t1W q) a b u g
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          t1W q z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a g z θ := rfl
  calc |Work.FTS.TransportS.slotPairing (t1W q) a b u g|
      = |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          t1W q z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a g z θ| := by
        rw [hslot]
    _ ≤ ∫ z in Work.Spaces.Iz, ((CH / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ)) := hmain
    _ = (∫ z in Work.Spaces.Iz, CH / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ) :=
        MeasureTheory.integral_add hHb_int hEz_int
    _ ≤ (CH / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
            * Work.Spaces.HkSq α 4 g)
          + 36 * (CE / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
              * Work.Spaces.HkSq α 4 g) := add_le_add hHb_le hEz_le
    _ = (CH + 36 * CE) / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g := by ring

end

end Work.FTS.StrongPersist.N6Trans.T1Hon
