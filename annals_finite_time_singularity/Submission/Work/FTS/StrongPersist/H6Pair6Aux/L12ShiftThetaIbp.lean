import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! The three `IntegrableOn (Iz ×ˢ Iθ)` hypotheses of
`Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp` for the `k = 0` slot of the `L₁₂·D_θ` expansion,
together with the product/outer/slice integrability of the bare leaf-weighted slot. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option maxHeartbeats 1600000

theorem ibp_integrable_fts {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem6 : Work.Spaces.HkMem α 6 f)
    (hmem7 : Work.Spaces.HkMem α 7 f) (h0 : Work.Construction.L12 f 0 = 0)
    {a b : ℕ} (hab : a + b ≤ 6) {q : ℝ}
    (hqle : q ≤ Work.Spaces.gam α) (hq0 : a = 0 → q ≤ Work.Spaces.eta) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.mixed b a f z θ ^ 2
          * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ
          * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.mixed b a f z θ ^ 2
          * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ MeasureTheory.Integrable
        (Function.uncurry (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    ∧ MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz
    ∧ (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ) := by
  obtain ⟨C₄, hC₄pos, hC₄⟩ := L12Sup4
  set P : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hP
  -- a.e. positivity of `z`
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have hEq : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
    rw [MeasureTheory.Measure.restrict_congr_set hEq]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  -- `|L₁₂ f|` is bounded by the `ℋ⁴`-norm
  have hC : ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 f z| ≤ C₄ * Work.Spaces.HkNorm α 4 f := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h | h
    · rw [← h, h0, abs_zero]
      exact mul_nonneg (le_of_lt hC₄pos) (Work.Spaces.HkNorm_nonneg α 4 f)
    · have hh := hC₄ α f hα hα1 hO hmem6 h0 0 (by norm_num) z h
      simpa using hh
  have hK0 : 0 ≤ C₄ * Work.Spaces.HkNorm α 4 f :=
    le_trans (abs_nonneg (Work.Construction.L12 f 1))
      (hC 1 (Set.mem_Ici.mpr (by norm_num)))
  have hQ0 : ∀ᵐ p ∂P, p ∈ Work.FTS.EllipticEst.Q0 := by
    rw [hP]; exact ae_prod_mem_Q0
  have hsin_pos : ∀ᵐ p ∂P, 0 < Real.sin (2 * p.2) :=
    hQ0.mono fun p hp => by
      obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin_nn : ∀ᵐ p ∂P, 0 ≤ Real.sin (2 * p.2) :=
    hsin_pos.mono fun _ h => le_of_lt h
  -- the leaf-slot domination, a.e.
  have hleaf6 : ∀ᵐ p ∂P, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
      * (Work.Spaces.mixed b a f p.1 p.2) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hQ0] with p hp
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact leafdom_rpow hα hab hqle hq0 (Set.mem_Ici.mpr (le_of_lt hz)) ⟨h1, h2⟩
  have hleaf7 : ∀ᵐ p ∂P, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
      * (Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
      ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
    filter_upwards [hQ0] with p hp
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact leafdom_rpow hα (k := 7) (by omega) hqle (fun hc => absurd hc (by omega))
      (Set.mem_Ici.mpr (le_of_lt hz)) ⟨h1, h2⟩
  have hcomm : ∀ᵐ p ∂P, Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
      = Work.Spaces.mixed b (a + 1) f p.1 p.2 := by
    rw [hP]; exact dth_mixed_ae_eq hO a b
  -- integrability of the two level-`6`/`7` integrands
  have hI6 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 f p.1 p.2) P := by
    rw [hP]; exact (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hO hmem6).1
  have hI7 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 7 f p.1 p.2) P := by
    rw [hP]; exact (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hO hmem7).1
  have hmono67 : ∀ᵐ p ∂P,
      Work.Spaces.HkIntegrand α 6 f p.1 p.2 ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 :=
    Filter.Eventually.of_forall fun p => Work.Spaces.HkIntegrand_mono α 6 f p.1 p.2
  -- continuity inputs
  have hL12c : ContinuousOn
      (fun z => Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    (continuousOn_L12 hO hmem6).mul continuousOn_w_sq
  have hhc : ContinuousOn (Function.uncurry (Work.Spaces.mixed b a f))
      Work.FTS.EllipticEst.Q0 := (hO.mixed b a).continuousOn
  have hsqc : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.mixed b a f z θ ^ 2))
      Work.FTS.EllipticEst.Q0 := continuousOn_uncurry_sq hhc
  have hdhc : ContinuousOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.mixed b a f)))
      Work.FTS.EllipticEst.Q0 := (hO.mixed b a).Dth.continuousOn
  have hphc : ContinuousOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
        * Work.Spaces.mixed b a f z θ)) Work.FTS.EllipticEst.Q0 := by
    have h := continuousOn_uncurry_mul hdhc hhc
    simpa using h
  -- the singular weight is nonnegative a.e. in `θ` (for the slice integrals)
  have hsin_nn_θ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ Real.sin (2 * θ) :=
    (Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ).mono fun θ hθ =>
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
  -- integrands
  have hm0 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2 ^ 2)
        Work.FTS.EllipticEst.Q0 := hsqc
    have h2 : ContinuousOn
        (fun p : ℝ × ℝ => Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      hL12c.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_sin_two_rpow_neg q).comp continuous_snd.continuousOn (fun p hp => hp.2)
    exact (h1.mul h2).mul h3
  have hm1 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ
        * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      exact continuousOn_uncurry_mul hdhc hhc
    have h2 : ContinuousOn
        (fun p : ℝ × ℝ => Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      hL12c.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_sin_two_rpow_neg q).comp continuous_snd.continuousOn (fun p hp => hp.2)
    exact (h1.mul h2).mul h3
  have hm2 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q))) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2 ^ 2)
        Work.FTS.EllipticEst.Q0 := hsqc
    have h2 : ContinuousOn
        (fun p : ℝ × ℝ => Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      hL12c.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Real.cos (2 * p.2))
        Work.FTS.EllipticEst.Q0 := by fun_prop
    have h4 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_sin_two_rpow_neg q).comp continuous_snd.continuousOn (fun p hp => hp.2)
    exact ((h1.mul h2).mul h3).mul h4
  -- the a.e. domination for each of the three integrands
  have hbd0 : ∀ᵐ p ∂P, ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
        * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        * (Real.sin (2 * p.2)) ^ (-q)‖
      ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hQ0, hleaf6, hsin_nn] with p hp hle hσ0
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hσq : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg hσ0 (-q)
    have hW : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hsq : 0 ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2 := sq_nonneg _
    have hLn : |Work.Construction.L12 f p.1| ≤ C₄ * Work.Spaces.HkNorm α 4 f :=
      hC p.1 (Set.mem_Ici.mpr (le_of_lt hz))
    have e1 : |Work.Spaces.mixed b a f p.1 p.2 ^ 2|
        = Work.Spaces.mixed b a f p.1 p.2 ^ 2 := abs_of_nonneg hsq
    have e2 : |(Real.sin (2 * p.2)) ^ (-q)| = (Real.sin (2 * p.2)) ^ (-q) := abs_of_nonneg hσq
    have e3 : |(Work.Spaces.w p.1) ^ 2| = (Work.Spaces.w p.1) ^ 2 := abs_of_nonneg hW
    have hkey : ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)‖
        = Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, e1, e2, e3]
    rw [hkey]
    calc Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)
        ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * ((C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLn hW) hsq) hσq
      _ = (C₄ * Work.Spaces.HkNorm α 4 f) * ((Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-q) * Work.Spaces.mixed b a f p.1 p.2 ^ 2) := by ring
      _ ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 6 f p.1 p.2 :=
          mul_le_mul_of_nonneg_left hle hK0
  have hbd1 : ∀ᵐ p ∂P, ‖Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2
        * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        * (Real.sin (2 * p.2)) ^ (-q)‖
      ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
    filter_upwards [hQ0, hleaf7, hleaf6, hcomm, hsin_nn, hmono67]
      with p hp hle7 hle6 hcm hσ0 hm67
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hσq : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg hσ0 (-q)
    have hW : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hsq : 0 ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2 := sq_nonneg _
    have hLn : |Work.Construction.L12 f p.1| ≤ C₄ * Work.Spaces.HkNorm α 4 f :=
      hC p.1 (Set.mem_Ici.mpr (le_of_lt hz))
    have e1 : |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2| =
        |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2| := abs_mul _ _
    have e2 : |(Work.Spaces.w p.1) ^ 2| = (Work.Spaces.w p.1) ^ 2 := abs_of_nonneg hW
    have e3 : |(Real.sin (2 * p.2)) ^ (-q)| = (Real.sin (2 * p.2)) ^ (-q) := abs_of_nonneg hσq
    have hkey : ‖Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2
          * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)‖
        = |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, e2, e3]
    rw [hkey]
    have hD : |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
        = |Work.Spaces.mixed b (a + 1) f p.1 p.2| := by rw [hcm]
    have ham : |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
        ≤ ((Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
            + Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2 := by
      rw [hD]
      nlinarith [sq_nonneg (|Work.Spaces.mixed b (a + 1) f p.1 p.2|
        - |Work.Spaces.mixed b a f p.1 p.2|),
        sq_abs (Work.Spaces.mixed b (a + 1) f p.1 p.2),
        sq_abs (Work.Spaces.mixed b a f p.1 p.2)]
    have hs1 : |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
        ≤ (((Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
            + Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2)
          * ((C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w p.1) ^ 2) :=
      mul_le_mul ham (mul_le_mul_of_nonneg_right hLn hW) (by positivity) (by positivity)
    calc |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)
        ≤ ((((Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
            + Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2)
          * ((C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w p.1) ^ 2))
          * (Real.sin (2 * p.2)) ^ (-q) := mul_le_mul_of_nonneg_right hs1 hσq
      _ = (C₄ * Work.Spaces.HkNorm α 4 f)
          * (((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f p.1 p.2 ^ 2) / 2
            + ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
              * Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2) := by ring
      _ ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * ((Work.Spaces.HkIntegrand α 7 f p.1 p.2) / 2
            + (Work.Spaces.HkIntegrand α 7 f p.1 p.2) / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          exact add_le_add (div_le_div_of_nonneg_right hle7 (by norm_num))
            (div_le_div_of_nonneg_right (hle6.trans hm67) (by norm_num))
      _ = (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by ring
  have hbd2 : ∀ᵐ p ∂P, ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
        * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)‖
      ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hQ0, hleaf6, hsin_nn] with p hp hle hσ0
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hσq : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg hσ0 (-q)
    have hW : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hsq : 0 ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2 := sq_nonneg _
    have hLn : |Work.Construction.L12 f p.1| ≤ C₄ * Work.Spaces.HkNorm α 4 f :=
      hC p.1 (Set.mem_Ici.mpr (le_of_lt hz))
    have e1 : |Work.Spaces.mixed b a f p.1 p.2 ^ 2|
        = Work.Spaces.mixed b a f p.1 p.2 ^ 2 := abs_of_nonneg hsq
    have e2 : |(Work.Spaces.w p.1) ^ 2| = (Work.Spaces.w p.1) ^ 2 := abs_of_nonneg hW
    have e3 : |(Real.sin (2 * p.2)) ^ (-q)| = (Real.sin (2 * p.2)) ^ (-q) := abs_of_nonneg hσq
    have hkey : ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
          * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)‖
        = Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * |Real.cos (2 * p.2)| * (Real.sin (2 * p.2)) ^ (-q) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, e1, e2, e3]
    rw [hkey]
    have hs1 : Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
        ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * ((C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w p.1) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLn hW) hsq
    calc Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * |Real.cos (2 * p.2)| * (Real.sin (2 * p.2)) ^ (-q)
        ≤ (Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * ((C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w p.1) ^ 2))
          * 1 * (Real.sin (2 * p.2)) ^ (-q) :=
          mul_le_mul (mul_le_mul hs1 (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity))
            le_rfl (by positivity) (by positivity)
      _ = (C₄ * Work.Spaces.HkNorm α 4 f) * ((Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-q) * Work.Spaces.mixed b a f p.1 p.2 ^ 2) := by ring
      _ ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 6 f p.1 p.2 :=
          mul_le_mul_of_nonneg_left hle hK0
  -- the fourth conjunct: the bare leaf-weighted slot
  have hm3 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      continuousOn_w_sq.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_sin_two_rpow_neg q).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2 ^ 2)
        Work.FTS.EllipticEst.Q0 := hsqc
    exact (h1.mul h2).mul h3
  have hbd3 : ∀ᵐ p ∂P, ‖(Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (Work.Spaces.mixed b a f p.1 p.2) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hleaf6, hsin_nn] with p hle hσ0
    have hσq : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg hσ0 (-q)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hσq)
      (sq_nonneg _))]
    exact hle
  -- the first three conjuncts
  have hProd : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P :=
    MeasureTheory.Integrable.mono' (hI6.const_mul (C₄ * Work.Spaces.HkNorm α 4 f)) hm0 hbd0
  have hProd1 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ
        * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P :=
    MeasureTheory.Integrable.mono' (hI7.const_mul (C₄ * Work.Spaces.HkNorm α 4 f)) hm1 hbd1
  have hProd2 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q))) P :=
    MeasureTheory.Integrable.mono' (hI6.const_mul (C₄ * Work.Spaces.HkNorm α 4 f)) hm2 hbd2
  -- the fourth conjunct: the bare leaf-weighted slot
  have hbd3 : ∀ᵐ p ∂P, ‖(Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (Work.Spaces.mixed b a f p.1 p.2) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hleaf6, hsin_nn] with p hle hσ0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg hσ0 _)) (sq_nonneg _))]
    exact hle
  have hm3 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) P := by
    rw [hP]
    refine (aesm_uncurry_mul (continuousOn_w_sq) (continuousOn_sin_two_rpow_neg q) hsqc).congr ?_
    filter_upwards with p
    show (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * Work.Spaces.mixed b a f p.1 p.2 ^ 2
      = (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * Work.Spaces.mixed b a f p.1 p.2 ^ 2
    rfl
  have hProd3 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) P :=
    MeasureTheory.Integrable.mono' hI6 hm3 hbd3
  -- conjuncts 5 and 6 from conjunct 4
  have hOut : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz := by
    have hsplit := (MeasureTheory.integrable_prod_iff hm3).mp hProd3
    have hfun : (fun z : ℝ => ∫ θ, ‖Function.uncurry (fun z θ =>
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) (z, θ)‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      funext z
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hsin_nn_θ] with θ hθ
      show ‖(Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2‖
        = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg hθ _)) (sq_nonneg _))]
      ring
    rw [hfun] at hsplit
    exact hsplit.2
  have hSlice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ := by
    filter_upwards [hProd3.prod_right_ae, hzpos] with z hz hzp
    have hcoe : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      have h1 : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
      rw [h1]
      exact pow_ne_zero 2 (div_ne_zero (by positivity) (pow_ne_zero 2 (ne_of_gt hzp)))
    refine (hz.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr (Filter.Eventually.of_forall ?_)
    intro θ
    have hinv : ((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2 = 1 := inv_mul_cancel₀ hcoe
    calc ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
        = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2) * ((Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
      _ = (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a f z θ) ^ 2 := by
          rw [hinv, one_mul]
  have hconv : ∀ F : ℝ × ℝ → ℝ, MeasureTheory.Integrable F P →
      MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    intro F hF
    rw [MeasureTheory.IntegrableOn,
      show (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) from
        (MeasureTheory.Measure.prod_restrict Work.Spaces.Iz Work.Spaces.Iθ).symm]
    exact hF
  exact ⟨hconv _ hProd, hconv _ hProd1, hconv _ hProd2, hProd3, hOut, hSlice⟩



end Work.FTS.StrongPersist.H6Pair6Aux
