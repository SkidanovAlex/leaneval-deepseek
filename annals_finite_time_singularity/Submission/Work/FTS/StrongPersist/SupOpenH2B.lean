import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.SupOpenH2Defs
import Submission.Work.FTS.StrongPersist.SupOpenH2Z
import Submission.Work.H2.T1Q.SliceSupOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

theorem zavg_B {α : ℝ} {h : ℝ → ℝ → ℝ} (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen h)
    (hmem : Work.Spaces.HkMem α 2 h) {z₀ : ℝ} (hz₀ : 0 < z₀) :
    (Work.Spaces.w z₀) ^ 2 * z₀ * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dth h z₀ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ 9 * Work.Spaces.HkSq α 2 h := by
  have hγne : Work.Spaces.gam α ≠ 0 := gam_ne_zero hα
  set sm0 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.mixed 0 1 h z θ * Work.Spaces.Wt α z θ) ^ 2 with hsm0def
  set sm1 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.mixed 1 1 h z θ * Work.Spaces.Wt α z θ) ^ 2 with hsm1def
  set Φ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.Dth h z θ * (Work.Spaces.w z * Real.sqrt z)
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) with hΦdef
  set Φ' : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.pz (Work.Spaces.Dth h) z θ
    * (Work.Spaces.w z * Real.sqrt z) + Work.Spaces.Dth h z θ * dWsq z)
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) with hΦ'def
  have hsm0c : ContinuousOn (Function.uncurry sm0) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hsm0def]
    exact (((hso.mixed 0 1).continuousOn).mul (continuousOn_Wt α)).pow 2
  have hsm1c : ContinuousOn (Function.uncurry sm1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hsm1def]
    exact (((hso.mixed 1 1).continuousOn).mul (continuousOn_Wt α)).pow 2
  have hSle0 : ∀ z θ, sm0 z θ ≤ Work.Spaces.HkIntegrand α 2 h z θ := by
    intro z θ; rw [hsm0def]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 2 h z θ 1 0 (by norm_num) (by norm_num)
  have hSle1 : ∀ z θ, sm1 z θ ≤ Work.Spaces.HkIntegrand α 2 h z θ := by
    intro z θ; rw [hsm1def]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 2 h z θ 1 1 (by norm_num) (by norm_num)
  have hinner0 : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => sm0 z θ) Work.Spaces.Iθ :=
    slot_inner hsm0c hmem (fun _ _ => sq_nonneg _) hSle0
  have hinner1 : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => sm1 z θ) Work.Spaces.Iθ :=
    slot_inner hsm1c hmem (fun _ _ => sq_nonneg _) hSle1
  have houter0 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sm0 z θ) Work.Spaces.Iz :=
    slot_outer hsm0c hmem (fun _ _ => sq_nonneg _) hSle0
  have houter1 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sm1 z θ) Work.Spaces.Iz :=
    slot_outer hsm1c hmem (fun _ _ => sq_nonneg _) hSle1
  have hIS0 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sm0 z θ) (Set.Ioi 0) :=
    houter0.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz))
  have hIS1 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sm1 z θ) (Set.Ioi 0) :=
    houter1.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz))
  have hL2Sq0 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, sm0 z θ)
      ≤ Work.Spaces.HkSq α 2 h := by
    have h := Work.Spaces.L2Sq_mixed_le_HkSq α 2 h hmem 1 0 (by norm_num) (by norm_num)
    simpa only [Work.Spaces.L2Sq, hsm0def] using h
  have hL2Sq1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, sm1 z θ)
      ≤ Work.Spaces.HkSq α 2 h := by
    have h := Work.Spaces.L2Sq_mixed_le_HkSq α 2 h hmem 1 1 (by norm_num) (by norm_num)
    simpa only [Work.Spaces.L2Sq, hsm1def] using h
  have hΦcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hΦdef]
    show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth h p.1 p.2
      * (Work.Spaces.w p.1 * Real.sqrt p.1) * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) _
    exact (((hso.Dth).continuousOn.mul continuousOn_w_mul_sqrt)).mul (continuousOn_sin_pow _)
  have hΦ'cont : ContinuousOn (Function.uncurry Φ') (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hΦ'def]
    show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.Dth h) p.1 p.2
      * (Work.Spaces.w p.1 * Real.sqrt p.1) + Work.Spaces.Dth h p.1 p.2 * dWsq p.1)
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) _
    exact (((((hso.Dth).pz).continuousOn.mul continuousOn_w_mul_sqrt).add
      (((hso.Dth).continuousOn).mul continuousOn_dWsq))).mul (continuousOn_sin_pow _)
  have hderiv : ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ z ∈ Set.Ioi 0,
      HasDerivAt (fun z' => Φ z' θ) (Φ' z θ) z := by
    intro θ hθ z hz
    rw [hΦdef, hΦ'def]
    exact (((hso.Dth).hasDerivAt_slice hθ hz).mul (hasDerivAt_dWsq hz)).mul_const _
  -- unfold identities
  have hsm0u : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed 0 1 h z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.Dth h z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    intro z hz θ hθ
    rw [show Work.Spaces.mixed 0 1 h z θ = Work.Spaces.Dth h z θ from rfl]
    rw [sm_unfold_gen (Work.Spaces.Dth h z θ) hθ hγne]
  have hsm1u : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed 1 1 h z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * z ^ 2 * ((Work.Spaces.pz (Work.Spaces.Dth h) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    intro z hz θ hθ
    rw [show Work.Spaces.mixed 1 1 h z θ = z * Work.Spaces.pz (Work.Spaces.Dth h) z θ from rfl]
    rw [sm_unfold_gen (z * Work.Spaces.pz (Work.Spaces.Dth h) z θ) hθ hγne]
    ring
  have hbnd : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Work.Spaces.Iθ, Φ' z θ ^ 2
      ≤ (2 / z) * sm1 z θ + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sm0 z θ := by
    intro z hz θ hθ
    rw [hΦ'def, hsm0def, hsm1def]
    have hsplit : ((Work.Spaces.pz (Work.Spaces.Dth h) z θ * (Work.Spaces.w z * Real.sqrt z)
          + Work.Spaces.Dth h z θ * dWsq z)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        ≤ 2 * (Work.Spaces.pz (Work.Spaces.Dth h) z θ * (Work.Spaces.w z * Real.sqrt z)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
          + 2 * (Work.Spaces.Dth h z θ * dWsq z
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
      nlinarith [sq_nonneg (Work.Spaces.pz (Work.Spaces.Dth h) z θ * (Work.Spaces.w z * Real.sqrt z)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
        - Work.Spaces.Dth h z θ * dWsq z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))]
    refine hsplit.trans ?_
    have hpu := sqmul_unfold (Work.Spaces.pz (Work.Spaces.Dth h) z θ) hz hθ hγne
    have hdu : (Work.Spaces.Dth h z θ * dWsq z
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Work.Spaces.w z) ^ 2 * ((z - 3) ^ 2 / (4 * z * (1 + z) ^ 2))
            * ((Work.Spaces.Dth h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      rw [mul_sin_neg_half_sq (x := Work.Spaces.Dth h z θ * dWsq z) hθ hγne,
          show (Work.Spaces.Dth h z θ * dWsq z) ^ 2
            = (Work.Spaces.Dth h z θ) ^ 2 * (dWsq z) ^ 2 from by ring,
          dWsq_sq_id hz]
      ring
    have h2 : 2 * (Work.Spaces.pz (Work.Spaces.Dth h) z θ * (Work.Spaces.w z * Real.sqrt z)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (2 / z) * (Work.Spaces.mixed 1 1 h z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hpu]
      rw [show Work.Spaces.mixed 1 1 h z θ = z * Work.Spaces.pz (Work.Spaces.Dth h) z θ from rfl]
      rw [sm_unfold_gen (z * Work.Spaces.pz (Work.Spaces.Dth h) z θ) hθ hγne]
      field_simp
      try ring
    have h3 : 2 * (Work.Spaces.Dth h z θ * dWsq z
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2))
            * (Work.Spaces.mixed 0 1 h z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hdu]
      rw [show Work.Spaces.mixed 0 1 h z θ = Work.Spaces.Dth h z θ from rfl]
      rw [sm_unfold_gen (Work.Spaces.Dth h z θ) hθ hγne]
      field_simp
      try ring
    rw [h2, h3]
  -- ## the `h`-slot conclusion
  have hG_pt : ∀ z ∈ Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z
      ≤ 2 * (∫ θ in Work.Spaces.Iθ, sm1 z θ) + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sm0 z θ) := by
    intro z hz
    have hmaj : IntegrableOn (fun θ => (2 / z) * sm1 z θ
        + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sm0 z θ) Work.Spaces.Iθ :=
      ((hinner1 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _).add
        ((hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _)
    have hle : (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, ((2 / z) * sm1 z θ
            + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sm0 z θ) :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hmaj
        (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
          fun θ hθ => hbnd z hz θ hθ)
    rw [MeasureTheory.integral_add ((hinner1 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _)
        ((hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul] at hle
    have h1 : (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z
        ≤ ((2 / z) * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
            + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, sm0 z θ)) * z :=
      mul_le_mul_of_nonneg_right hle hz.le
    have h2 : ((2 / z) * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
            + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, sm0 z θ)) * z
        = 2 * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
          + (z * ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2))) * (∫ θ in Work.Spaces.Iθ, sm0 z θ) := by
      have hz0 : z ≠ 0 := ne_of_gt hz
      have hz1 : (1 + z) ≠ 0 := by
        have : (0:ℝ) < 1 + z := by linarith [show (0:ℝ) < z from hz]
        exact ne_of_gt this
      field_simp
      try ring
    rw [h2] at h1
    have hzC : z * ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) ≤ 9 / 2 := by
      have h := abs_div_ge_le hz
      have hz0 : z ≠ 0 := ne_of_gt hz
      have hz1 : (1 + z) ≠ 0 := by
        have : (0:ℝ) < 1 + z := by linarith [show (0:ℝ) < z from hz]
        exact ne_of_gt this
      have hkey : z * ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2))
          = ((z - 3) ^ 2 / (1 + z) ^ 2) / 2 := by
        field_simp
        try ring
      rw [hkey]
      linarith
    have hb0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, sm0 z θ := integral_nonneg fun θ => sq_nonneg _
    have hb1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, sm1 z θ := integral_nonneg fun θ => sq_nonneg _
    nlinarith [h1, hzC, hb0, hb1]
  have hF_eq : ∀ z ∈ Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z
      = ∫ θ in Work.Spaces.Iθ, sm0 z θ := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) = z * (∫ θ in Work.Spaces.Iθ, sm0 z θ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
      simp only [hΦdef, hsm0def]
      rw [sqmul_unfold (Work.Spaces.Dth h z θ) hz hθ hγne, hsm0u z hz θ hθ]
      ring
    rw [h1, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  have hFin : ∀ z ∈ Set.Ioi 0, IntegrableOn (fun θ => Φ z θ ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have heq : ∀ θ ∈ Work.Spaces.Iθ, Φ z θ ^ 2 = z * sm0 z θ := by
      intro θ hθ
      simp only [hΦdef, hsm0def]
      rw [sqmul_unfold (Work.Spaces.Dth h z θ) hz hθ hγne, hsm0u z hz θ hθ]
      ring
    have hbase : IntegrableOn (fun θ => z * sm0 z θ) Work.Spaces.Iθ :=
      (hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul z
    exact IntegrableOn.congr_fun hbase (fun θ hθ => (heq θ hθ).symm) measurableSet_Icc
  have hGin : ∀ z ∈ Set.Ioi 0, IntegrableOn (fun θ => Φ' z θ ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have hmaj : IntegrableOn (fun θ => (2 / z) * sm1 z θ
        + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sm0 z θ) Work.Spaces.Iθ :=
      ((hinner1 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _).add
        ((hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _)
    refine Integrable.mono' hmaj ?_ ?_
    · have h2 := Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry Φ') hΦ'cont hz
      exact h2.pow 2
    · rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
      exact Eventually.of_forall fun θ hθ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hbnd z hz θ hθ
  have hFint : IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z) (Set.Ioi 0) :=
    IntegrableOn.congr_fun hIS0 (fun z hz => (hF_eq z hz).symm) measurableSet_Ioi
  have hGint : IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z) (Set.Ioi 0) := by
    have hmaj : IntegrableOn (fun z => 2 * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
        + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sm0 z θ)) (Set.Ioi 0) :=
      ((hIS1.const_mul 2).add (hIS0.const_mul (9 / 2)))
    have haesm : AEStronglyMeasurable (fun z => (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z)
        (volume.restrict (Set.Ioi 0)) := by
      have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => Φ' p.1 p.2 ^ 2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
        have h3 := (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry Φ') hΦ'cont).pow 2
        have heq : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
          rw [Work.Spaces.Iz]
          exact MeasureTheory.Measure.restrict_congr_set
            (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
        rwa [heq]
      have h4 := hjoint.integral_prod_right'
      have heq2 : (fun z => ∫ θ, Φ' z θ ^ 2 ∂(volume.restrict Work.Spaces.Iθ))
          = (fun z => ∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) := by
        funext z; rfl
      rw [heq2] at h4
      exact h4.mul aestronglyMeasurable_id
    refine Integrable.mono' hmaj haesm ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun z hz => by
      rw [Real.norm_of_nonneg (mul_nonneg (integral_nonneg fun θ => sq_nonneg _) hz.le)]
      exact hG_pt z hz
  have hZ := SupOpenH2Z (z₀ := z₀) hz₀ hΦcont hΦ'cont hderiv hFin hGin hFint hGint
  have hLHS : (∫ θ in Work.Spaces.Iθ, Φ z₀ θ ^ 2)
      = (Work.Spaces.w z₀) ^ 2 * z₀ * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dth h z₀ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    simp only [hΦdef]
    rw [sqmul_unfold (Work.Spaces.Dth h z₀ θ) hz₀ hθ hγne]
    try ring
  have hR1 : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z)
      ≤ Work.Spaces.HkSq α 2 h := by
    rw [show (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z)
        = ∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm0 z θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun z hz => hF_eq z hz]
    rw [show (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm0 z θ))
        = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, sm0 z θ) from
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    exact hL2Sq0
  have hR2 : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z)
      ≤ (13 / 2) * Work.Spaces.HkSq α 2 h := by
    have hle : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z)
        ≤ ∫ z in Set.Ioi 0, (2 * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
            + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sm0 z θ)) :=
      MeasureTheory.integral_mono_of_nonneg
        (ae_restrict_of_forall_mem measurableSet_Ioi fun z hz =>
          mul_nonneg (integral_nonneg fun θ => sq_nonneg _) hz.le)
        (((hIS1.const_mul 2).add (hIS0.const_mul (9 / 2))))
        (ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => hG_pt z hz)
    have hsplit : (∫ z in Set.Ioi 0, (2 * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
          + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sm0 z θ)))
        = 2 * (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm1 z θ))
          + (9 / 2) * (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm0 z θ)) := by
      rw [MeasureTheory.integral_add (hIS1.const_mul 2) (hIS0.const_mul (9 / 2)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hsplit] at hle
    have hA : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm1 z θ))
        = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, sm1 z θ) :=
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
    have hB : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm0 z θ))
        = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, sm0 z θ) :=
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
    rw [hA, hB] at hle
    linarith [hle, hL2Sq0, hL2Sq1]
  have hnn : 0 ≤ Work.Spaces.HkSq α 2 h := Work.Spaces.HkSq_nonneg α 2 h
  calc (Work.Spaces.w z₀) ^ 2 * z₀ * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dth h z₀ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (∫ θ in Work.Spaces.Iθ, Φ z₀ θ ^ 2) := hLHS.symm
    _ ≤ 2 * (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z)
          + (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z) := hZ
    _ ≤ 2 * Work.Spaces.HkSq α 2 h + (13 / 2) * Work.Spaces.HkSq α 2 h := by
        linarith [hR1, hR2]
    _ ≤ 9 * Work.Spaces.HkSq α 2 h := by linarith

end Work.FTS.StrongPersist
