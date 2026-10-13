/-
# `c0_pos` : the zero mode of the far bump is positive

`c0 = L₁₂(Gfar)(0) = ∫_{s>0} ∫_{θ∈[0,π/2]} K(θ)·Gfar(s,θ)/s dθ ds`, where
`Gfar = famRaw 0 0 3 40 80 1 5` is the designated far bump of
`Submission/Work/FTS/GalBasis/Defs.lean`:

`Gfar s θ = (stp 3 40 s * ustp 3 80 s) * (stp 3 1 θ * ustp 3 5 θ)`

is a nonnegative product of four smooth steps, equal to `1` on the open rectangle
`s ∈ (41/4, 79/4)`, `θ ∈ (1/2, 1)` (which lies inside the quadrant) and vanishing off
`(10, 20) × (1/4, 5/4)`.  Since `K(θ) = 3 sin θ cos²θ ≥ 0` on `[0, π/2]` and `K(θ) > 0`
on `[1/2, 1]`, the double integrand is nonnegative everywhere and strictly positive on a
set of positive measure (`(11,19) × (1/2,1)`, say), so `c0 > 0`.  `K(θ) = 3 sinθ cos²θ ≥ 0`
on `[0, π/2]` and `K(θ) > 0` on `[1/2, 1]`.

The proof is a two-step measure-theoretic positivity argument:

* the *inner* integral `c0F s = ∫_θ K(θ)Gfar(s,θ)/s` is positive for `s ∈ [11,19]`
  (`setIntegral_pos_iff_support_of_nonneg_ae`: its support contains the interval
  `[1/2,1]`, of positive measure); the integrability of the inner integrand is
  `ContinuousOn.integrableOn_compact`;
* the *outer* integral `c0 = ∫_{s>0} c0F s` is positive by
  `setIntegral_pos_iff_support_of_nonneg_ae`: the support of `c0F` contains `[11,19]`
  (of measure `8`).  Its two hypotheses are `c0F ≥ 0` and `IntegrableOn c0F (Ioi 0)`;
  the latter comes from `c0F = 0` off `[10,20]`, the bound `‖c0F s‖ ≤ 3/10·(π/2)`
  (`norm_setIntegral_le_of_norm_le_const`) and the strong measurability of `c0F` as a
  parametric integral (`StronglyMeasurable.integral_prod_right`, the uncurried integrand
  being *globally* continuous because `famZ 3 40 80 s = 0` for `s ≤ 10`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.GalBasis.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis
open Work.FTS.Galerkin (Fn galFun)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

/-! ## Elementary facts about the far bump `Gfar` -/

/-- The far bump is the product of its `z`- and `θ`-steps. -/
theorem Gfar_eq_mul (z θ : ℝ) : Gfar z θ = famZ 3 40 80 z * famTh 3 1 5 θ := by
  simp only [Gfar, famRaw, pow_zero, one_mul]

theorem famZ_3_40_80_nonneg (z : ℝ) : 0 ≤ famZ 3 40 80 z :=
  mul_nonneg (stp_nonneg 3 40 z) (ustp_nonneg 3 80 z)

theorem famTh_3_1_5_nonneg (θ : ℝ) : 0 ≤ famTh 3 1 5 θ :=
  mul_nonneg (stp_nonneg 3 1 θ) (ustp_nonneg 3 5 θ)

theorem famZ_3_40_80_le_one (z : ℝ) : famZ 3 40 80 z ≤ 1 := by
  have h1 := stp_nonneg 3 40 z
  have h2 := stp_le_one 3 40 z
  have h3 := ustp_nonneg 3 80 z
  have h4 := ustp_le_one 3 80 z
  simp only [famZ]
  nlinarith

theorem famTh_3_1_5_le_one (θ : ℝ) : famTh 3 1 5 θ ≤ 1 := by
  have h1 := stp_nonneg 3 1 θ
  have h2 := stp_le_one 3 1 θ
  have h3 := ustp_nonneg 3 5 θ
  have h4 := ustp_le_one 3 5 θ
  simp only [famTh]
  nlinarith

theorem Gfar_nonneg (z θ : ℝ) : 0 ≤ Gfar z θ := by
  rw [Gfar_eq_mul]
  exact mul_nonneg (famZ_3_40_80_nonneg z) (famTh_3_1_5_nonneg θ)

theorem Gfar_le_one (z θ : ℝ) : Gfar z θ ≤ 1 := by
  rw [Gfar_eq_mul]
  have h1 := famZ_3_40_80_nonneg z
  have h2 := famZ_3_40_80_le_one z
  have h3 := famTh_3_1_5_nonneg θ
  have h4 := famTh_3_1_5_le_one θ
  nlinarith

theorem Gfar_abs_le_one (z θ : ℝ) : |Gfar z θ| ≤ 1 := by
  rw [abs_of_nonneg (Gfar_nonneg z θ)]
  exact Gfar_le_one z θ

/-- The `z`-step equals `1` on the plateau `[41/4, 79/4]`. -/
theorem famZ_3_40_80_eq_one {z : ℝ} (h1 : 41 / 4 ≤ z) (h2 : z ≤ 79 / 4) :
    famZ 3 40 80 z = 1 := by
  rw [famZ, stp_eq_one (n := 3) (m := 40) (t := z) (by push_cast; linarith),
    ustp_eq_one (n := 3) (m := 80) (t := z) (by push_cast; linarith), mul_one]

/-- The `θ`-step equals `1` on the plateau `[1/2, 1]`. -/
theorem famTh_3_1_5_eq_one {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 1) :
    famTh 3 1 5 θ = 1 := by
  rw [famTh, stp_eq_one (n := 3) (m := 1) (t := θ) (by push_cast; linarith),
    ustp_eq_one (n := 3) (m := 5) (t := θ) (by push_cast; linarith), mul_one]

/-- `Gfar = 1` on the rectangle `[41/4, 79/4] × [1/2, 1]`. -/
theorem Gfar_eq_one_of_mem {z θ : ℝ} (h1 : 41 / 4 ≤ z) (h2 : z ≤ 79 / 4)
    (h3 : 1 / 2 ≤ θ) (h4 : θ ≤ 1) : Gfar z θ = 1 := by
  rw [Gfar_eq_mul, famZ_3_40_80_eq_one h1 h2, famTh_3_1_5_eq_one h3 h4, one_mul]

/-- `Gfar` vanishes for `z ≤ 10`. -/
theorem Gfar_eq_zero_of_le {z θ : ℝ} (h : z ≤ 10) : Gfar z θ = 0 := by
  rw [Gfar_eq_mul, famZ, famTh,
    stp_eq_zero (n := 3) (m := 40) (t := z) (by push_cast; linarith)]
  ring

/-- `Gfar` vanishes for `z ≥ 20`. -/
theorem Gfar_eq_zero_of_ge {z θ : ℝ} (h : 20 ≤ z) : Gfar z θ = 0 := by
  rw [Gfar_eq_mul, famZ, famTh,
    ustp_eq_zero (n := 3) (m := 80) (t := z) (by push_cast; linarith)]
  ring

/-! ## The angular weight `K` on `[0, π/2]` -/

theorem Spaces_K_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [Real.pi_pos]⟩
  rw [Work.Spaces.K]
  positivity

theorem Spaces_K_pos {θ : ℝ} (hθ : θ ∈ Set.Icc (1 / 2 : ℝ) 1) : 0 < Work.Spaces.K θ := by
  obtain ⟨h1, h2⟩ := hθ
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  rw [Work.Spaces.K]
  positivity

theorem Spaces_K_abs_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hs := Real.abs_sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hc0 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg h3, abs_of_nonneg hc0]
  nlinarith [abs_nonneg (Real.sin θ)]

/-! ## The angular slice of `Gfar` and the radial density `c0F` -/

theorem continuous_Gfar_slice (s : ℝ) : Continuous (fun θ : ℝ => Gfar s θ) := by
  rw [Gfar]
  unfold famRaw famZ famTh stp ustp
  fun_prop

/-- The radial density of `c0`: `c0F s = ∫_θ K(θ)·Gfar(s,θ)/s`. -/
def c0F (s : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Gfar s θ / s

theorem c0_eq_integral_c0F : c0 = ∫ s in Set.Ioi 0, c0F s := by
  simp only [c0, c0F, Work.Construction.L12, Work.FM.L12, Work.FM.L12dens, Work.Spaces.Iθ]

theorem c0F_eq_zero_of_le {s : ℝ} (hs : s ≤ 10) : c0F s = 0 := by
  rw [c0F]
  refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun θ _ => ?_)
  rw [Gfar_eq_zero_of_le hs]
  ring

theorem c0F_eq_zero_of_ge {s : ℝ} (hs : 20 ≤ s) : c0F s = 0 := by
  rw [c0F]
  refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun θ _ => ?_)
  rw [Gfar_eq_zero_of_ge hs]
  ring

theorem c0F_nonneg (s : ℝ) : 0 ≤ c0F s := by
  rcases le_or_gt s 10 with hs | hs
  · rw [c0F_eq_zero_of_le hs]
  · have hspos : 0 < s := by linarith
    rw [c0F]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact div_nonneg (mul_nonneg (Spaces_K_nonneg hθ) (Gfar_nonneg s θ)) hspos.le

/-- **The inner integral is positive** for `s ∈ [11,19]`: the support of the θ-integrand
contains the interval `[1/2,1]`, on which `Gfar s · = 1` and `K > 0`. -/
theorem c0F_pos {s : ℝ} (hs1 : 11 ≤ s) (hs2 : s ≤ 19) : 0 < c0F s := by
  have hs : 0 < s := by linarith
  have hvol : (0 : ENNReal) < volume (Set.Icc (1 / 2 : ℝ) 1) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.K θ * Gfar s θ / s)
      Work.Spaces.Iθ := by
    apply Continuous.continuousOn
    have hG : Continuous (fun θ : ℝ => Gfar s θ) := continuous_Gfar_slice s
    have hK : Continuous Work.Spaces.K := by unfold Work.Spaces.K; fun_prop
    exact (hK.mul hG).div_const s
  have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => Work.Spaces.K θ * Gfar s θ / s) := by
    change ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ Work.Spaces.K θ * Gfar s θ / s
    rw [Work.Spaces.Iθ, ae_restrict_iff' measurableSet_Icc]
    exact Eventually.of_forall (fun θ hθ =>
      div_nonneg (mul_nonneg (Spaces_K_nonneg hθ) (Gfar_nonneg s θ)) hs.le)
  have hsub : Set.Icc (1 / 2 : ℝ) 1 ⊆
      Function.support (fun θ : ℝ => Work.Spaces.K θ * Gfar s θ / s) ∩ Work.Spaces.Iθ := by
    intro θ hθ
    refine ⟨Function.mem_support.mpr ?_, ?_⟩
    · have hG : Gfar s θ = 1 :=
        Gfar_eq_one_of_mem (by linarith) (by linarith) hθ.1 hθ.2
      rw [hG, mul_one]
      exact div_ne_zero (ne_of_gt (Spaces_K_pos hθ)) (ne_of_gt hs)
    · exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_gt_three]⟩
  rw [c0F]
  exact (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn
    (ContinuousOn.integrableOn_compact isCompact_Icc hcont)).mpr
    (lt_of_lt_of_le hvol (measure_mono hsub))

/-- The uniform bound `‖c0F s‖ ≤ (3/10)·(π/2)` on `s ≥ 10` (`|K| ≤ 3`, `0 ≤ Gfar ≤ 1`,
`1/s ≤ 1/10`, `∫_θ 1 = π/2`). -/
theorem c0F_bound {s : ℝ} (hs : 10 ≤ s) : ‖c0F s‖ ≤ 3 / 10 * (π / 2) := by
  have hspos : 0 < s := by linarith
  have hfin : volume Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Work.Spaces.Iθ) (f := fun θ : ℝ => Work.Spaces.K θ * Gfar s θ / s)
    (C := 3 / 10) hfin ?_
  · have hreal : MeasureTheory.Measure.real volume Work.Spaces.Iθ = π / 2 := by
      have h0 : (0 : ℝ) ≤ Real.pi / 2 - 0 := by linarith [Real.pi_pos]
      rw [MeasureTheory.Measure.real_def, Work.Spaces.Iθ, Real.volume_Icc,
        ENNReal.toReal_ofReal h0]
      ring
    rw [hreal] at h
    rw [c0F]
    exact h
  · intro θ _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hspos, abs_mul]
    rw [div_le_iff₀ hspos]
    have h1 : |Work.Spaces.K θ| * |Gfar s θ| ≤ 3 := by
      calc |Work.Spaces.K θ| * |Gfar s θ| ≤ 3 * 1 :=
            mul_le_mul (Spaces_K_abs_le_three θ) (Gfar_abs_le_one s θ)
              (abs_nonneg _) (by norm_num)
        _ = 3 := by norm_num
    nlinarith

/-! ## Measurability and integrability of `c0F` -/

/-- The radial factor `s ↦ famZ 3 40 80 s / s` is continuous: it vanishes identically on
`(-∞, 10]` and is a quotient of continuous functions away from `0`. -/
theorem continuous_famZ_div_3_40_80 :
    Continuous (fun s : ℝ => famZ 3 40 80 s / s) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ => famZ 3 40 80 s / s) := by
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
      have hs' : s < 1 := hs
      have h0 : famZ 3 40 80 s = 0 := by
        unfold famZ
        rw [stp_eq_zero (n := 3) (m := 40) (t := s) (by push_cast; linarith)]
        ring
      rw [h0, zero_div]
    exact continuousAt_const.congr hev
  · have hfamZ : Continuous (famZ 3 40 80) := by unfold famZ stp ustp; fun_prop
    exact hfamZ.continuousAt.div continuousAt_id (by simpa using hx)

theorem c0F_stronglyMeasurable : StronglyMeasurable c0F := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      (famZ 3 40 80 p.1 / p.1) * (Work.Spaces.K p.2 * famTh 3 1 5 p.2)) := by
    have hJ : Continuous (fun s : ℝ => famZ 3 40 80 s / s) := continuous_famZ_div_3_40_80
    have hKTh : Continuous (fun θ : ℝ => Work.Spaces.K θ * famTh 3 1 5 θ) := by
      unfold famTh stp ustp Work.Spaces.K
      fun_prop
    have heq : (fun p : ℝ × ℝ =>
          (famZ 3 40 80 p.1 / p.1) * (Work.Spaces.K p.2 * famTh 3 1 5 p.2))
        = fun p : ℝ × ℝ => (fun s => famZ 3 40 80 s / s) p.1
            * (fun θ => Work.Spaces.K θ * famTh 3 1 5 θ) p.2 := rfl
    rw [heq]
    exact (hJ.comp continuous_fst).mul (hKTh.comp continuous_snd)
  have hsm : StronglyMeasurable (fun s : ℝ => ∫ θ,
      (famZ 3 40 80 s / s) * (Work.Spaces.K θ * famTh 3 1 5 θ)
      ∂(volume.restrict Work.Spaces.Iθ)) :=
    StronglyMeasurable.integral_prod_right hcont.stronglyMeasurable
  have hEq : (fun s : ℝ => ∫ θ,
      (famZ 3 40 80 s / s) * (Work.Spaces.K θ * famTh 3 1 5 θ)
      ∂(volume.restrict Work.Spaces.Iθ)) = c0F := by
    funext s
    rw [c0F]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun θ => ?_))
    simp only [Gfar, famRaw, pow_zero, one_mul]
    ring
  simpa only [hEq] using hsm

theorem c0F_integrable : Integrable c0F := by
  have hint : MeasureTheory.IntegrableOn c0F (Set.Icc (10 : ℝ) 20) volume := by
    refine MeasureTheory.IntegrableOn.of_bound (μ := volume) (s := Set.Icc (10 : ℝ) 20)
      (f := c0F) ?_ ?_ (3 / 10 * (π / 2)) ?_
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    · exact c0F_stronglyMeasurable.aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Icc]
      exact Eventually.of_forall (fun s hs => c0F_bound hs.1)
  refine hint.integrable_of_forall_notMem_eq_zero (fun s hs => ?_)
  rcases le_or_gt s 10 with h | h
  · exact c0F_eq_zero_of_le h
  · have h20 : 20 ≤ s := by
      by_contra hc
      exact hs ⟨le_of_lt h, le_of_lt (not_le.mp hc)⟩
    exact c0F_eq_zero_of_ge h20

/-! ## Positivity of `c0` -/

theorem c0_pos : 0 < c0 := by
  rw [c0_eq_integral_c0F]
  have hvol : (0 : ENNReal) < volume (Set.Icc (11 : ℝ) 19) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hsub : Set.Icc (11 : ℝ) 19 ⊆ Function.support c0F ∩ Set.Ioi 0 := by
    intro s hs
    refine ⟨Function.mem_support.mpr (ne_of_gt (c0F_pos hs.1 hs.2)), ?_⟩
    show (0 : ℝ) < s
    linarith [hs.1]
  exact (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall c0F_nonneg) c0F_integrable.integrableOn).mpr
    (lt_of_lt_of_le hvol (measure_mono hsub))

end Work.FTS.GalBasis
