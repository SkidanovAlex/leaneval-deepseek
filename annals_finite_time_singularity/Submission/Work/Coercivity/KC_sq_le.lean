import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Coercivity.C0Defs
import Submission.Work.Coercivity.C0Ih_le
import Submission.Work.Coercivity.C0D_le
import Submission.Work.Coercivity.sq_integral_mul_le
import Submission.Work.Coercivity.rpow_neg_sq
import Submission.Work.Coercivity.Dth_gam_prod_facts
import Submission.Work.Coercivity.KC0_eq_double
import Submission.Work.Coercivity.KC1_eq_double
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The product measure of the quadrant `[0,∞) × [0,π/2]` (measure `dz dθ`). -/
abbrev muQ : Measure (ℝ × ℝ) :=
  (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)

/-- The `D_θ f`-factor of the Cauchy–Schwarz decomposition of the `KC0`/`KC1` estimates:
`A = D_θ f · w · sin(2θ)^{-γ/2}` with `γ = gam α`. -/
abbrev DthWt (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Spaces.Dth f p.1 p.2 * Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2))

/-- The angular factor dual to `DthWt` in the `KC0` estimate:
`v₀ = 3 K(θ) · z/(1+z)³ · sin(2θ)^{γ/2}`. -/
abbrev Kv (α : ℝ) : ℝ × ℝ → ℝ :=
  fun p => 3 * Spaces.K p.2 * p.1 / (1 + p.1) ^ 3 * (Real.sin (2 * p.2)) ^ (Spaces.gam α / 2)

/-- The angular factor dual to `DthWt` in the `KC1` estimate:
`v₁ = C0g(θ) · z/(1+z)³ · sin(2θ)^{γ/2}`. -/
abbrev C0gv (α : ℝ) : ℝ × ℝ → ℝ :=
  fun p => C0g p.2 * p.1 / (1 + p.1) ^ 3 * (Real.sin (2 * p.2)) ^ (Spaces.gam α / 2)

/-! ## Elementary angular and radial facts -/

private lemma continuous_K : Continuous Spaces.K := by
  unfold Spaces.K; fun_prop

private lemma continuous_C0g : Continuous C0g := by
  unfold C0g; fun_prop

/-- For `x ≥ 0`, the square of `x ^ (γ/2)` is `x ^ γ`. -/
private lemma rpow_half_sq (x γ : ℝ) (hx : 0 ≤ x) : (x ^ (γ / 2)) ^ 2 = x ^ γ := by
  rw [← Real.rpow_natCast (x ^ (γ / 2)) 2]
  calc (x ^ (γ / 2)) ^ (2 : ℝ) = x ^ ((γ / 2) * 2) := (Real.rpow_mul hx (γ / 2) 2).symm
    _ = x ^ γ := by rw [show γ / 2 * 2 = γ by ring]

/-- For `s > 0`, `s^{-γ/2}·s^{γ/2} = 1`. -/
private lemma rpow_neg_half_mul (γ : ℝ) {s : ℝ} (hs : 0 < s) :
    s ^ (-(γ / 2)) * s ^ (γ / 2) = 1 := by
  rw [Real.rpow_neg (le_of_lt hs) (γ / 2)]
  exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hs _))

/-- `sin(2θ) = 0` implies `sin θ = 0` or `cos θ = 0`. -/
private lemma sin_eq_zero_or_cos_eq_zero_of_sin_two_eq_zero {θ : ℝ}
    (h : Real.sin (2 * θ) = 0) : Real.sin θ = 0 ∨ Real.cos θ = 0 := by
  have hs := Real.sin_two_mul θ
  rw [h] at hs
  have h2 : Real.sin θ * Real.cos θ = 0 := by linarith
  exact mul_eq_zero.mp h2

/-- `K(θ) = 3 sinθ cos²θ` vanishes whenever `sin(2θ) = 0`. -/
private lemma K_eq_zero_of_sin_two_eq_zero {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Spaces.K θ = 0 := by
  rcases sin_eq_zero_or_cos_eq_zero_of_sin_two_eq_zero h with h4 | h4
  · simp [Spaces.K, h4]
  · simp [Spaces.K, h4]

/-- `C0g(θ)` vanishes whenever `sin(2θ) = 0`. -/
private lemma C0g_eq_zero_of_sin_two_eq_zero {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    C0g θ = 0 := by
  rcases sin_eq_zero_or_cos_eq_zero_of_sin_two_eq_zero h with h4 | h4
  · simp [C0g, h4]
  · simp [C0g, h4]

/-- `w(z)·z/(1+z)³ = 1/(z(1+z))` for `z ≥ 0`. -/
private lemma w_mul_z_div (z : ℝ) (hz : 0 ≤ z) :
    Spaces.w z * (z / (1 + z) ^ 3) = 1 / (z * (1 + z)) := by
  rcases eq_or_lt_of_le hz with h | h
  · subst h; simp [Spaces.w]
  · have h1 : z ≠ 0 := ne_of_gt h
    have h2 : (1 : ℝ) + z ≠ 0 := by positivity
    rw [Spaces.w]
    field_simp

/-- Almost every point of the quadrant lies in `Iz ×ˢ Iθ`. -/
private lemma ae_mem_quadrant : ∀ᵐ p ∂muQ, p ∈ Spaces.Iz ×ˢ Spaces.Iθ := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => p ∈ Spaces.Iz ×ˢ Spaces.Iθ)
    (measurableSet_Ici.prod measurableSet_Icc)]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with x hx
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with y hy
  exact ⟨hx, hy⟩

/-! ## The two pointwise identities -/

/-- **Pointwise identity for `KC0`.**  On the quadrant, the product of the two
Cauchy–Schwarz factors is the integrand of `KC0_eq_double`. -/
private lemma DthWt_mul_Kv (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 ≤ z) (hθ : θ ∈ Spaces.Iθ) :
    DthWt α f (z, θ) * Kv α (z, θ)
      = Spaces.Dth f z θ * (3 * Spaces.K θ) / (z * (1 + z)) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hγ : Spaces.gam α ≠ 0 := by simp only [Spaces.gam]; linarith
  have hne1 : -(Spaces.gam α / 2) ≠ 0 := by intro hc; exact hγ (by linarith)
  have hne2 : Spaces.gam α / 2 ≠ 0 := by intro hc; exact hγ (by linarith)
  rcases eq_or_lt_of_le hs0 with hs | hs
  · have hs' : Real.sin (2 * θ) = 0 := hs.symm
    have hK : Spaces.K θ = 0 := K_eq_zero_of_sin_two_eq_zero hs'
    have h1 : Real.sin (2 * θ) ^ (-(Spaces.gam α / 2)) = 0 := by
      rw [hs']; exact Real.zero_rpow hne1
    have h2 : Real.sin (2 * θ) ^ (Spaces.gam α / 2) = 0 := by
      rw [hs']; exact Real.zero_rpow hne2
    simp only [DthWt, Kv]
    rw [h1, h2, hK]
    ring
  · have hprod : Real.sin (2 * θ) ^ (-(Spaces.gam α / 2)) * Real.sin (2 * θ) ^ (Spaces.gam α / 2)
        = 1 := rpow_neg_half_mul (Spaces.gam α) hs
    have hw : Spaces.w z * (z / (1 + z) ^ 3) = 1 / (z * (1 + z)) := w_mul_z_div z hz
    simp only [DthWt, Kv]
    calc (Spaces.Dth f z θ * Spaces.w z * Real.sin (2 * θ) ^ (-(Spaces.gam α / 2)))
          * (3 * Spaces.K θ * z / (1 + z) ^ 3 * Real.sin (2 * θ) ^ (Spaces.gam α / 2))
        = (Spaces.Dth f z θ * (3 * Spaces.K θ)) * (Spaces.w z * (z / (1 + z) ^ 3))
            * (Real.sin (2 * θ) ^ (-(Spaces.gam α / 2))
              * Real.sin (2 * θ) ^ (Spaces.gam α / 2)) := by ring
      _ = (Spaces.Dth f z θ * (3 * Spaces.K θ)) * (1 / (z * (1 + z))) * 1 := by
          rw [hw, hprod]
      _ = Spaces.Dth f z θ * (3 * Spaces.K θ) / (z * (1 + z)) := by ring

/-- **Pointwise identity for `KC1`.**  On the quadrant, the product of the two
Cauchy–Schwarz factors is the integrand of `KC1_eq_double`. -/
private lemma DthWt_mul_C0gv (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 ≤ z) (hθ : θ ∈ Spaces.Iθ) :
    DthWt α f (z, θ) * C0gv α (z, θ)
      = Spaces.Dth f z θ * C0g θ / (z * (1 + z)) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hγ : Spaces.gam α ≠ 0 := by simp only [Spaces.gam]; linarith
  have hne1 : -(Spaces.gam α / 2) ≠ 0 := by intro hc; exact hγ (by linarith)
  have hne2 : Spaces.gam α / 2 ≠ 0 := by intro hc; exact hγ (by linarith)
  rcases eq_or_lt_of_le hs0 with hs | hs
  · have hs' : Real.sin (2 * θ) = 0 := hs.symm
    have hC : C0g θ = 0 := C0g_eq_zero_of_sin_two_eq_zero hs'
    have h1 : Real.sin (2 * θ) ^ (-(Spaces.gam α / 2)) = 0 := by
      rw [hs']; exact Real.zero_rpow hne1
    have h2 : Real.sin (2 * θ) ^ (Spaces.gam α / 2) = 0 := by
      rw [hs']; exact Real.zero_rpow hne2
    simp only [DthWt, C0gv]
    rw [h1, h2, hC]
    ring
  · have hprod : Real.sin (2 * θ) ^ (-(Spaces.gam α / 2)) * Real.sin (2 * θ) ^ (Spaces.gam α / 2)
        = 1 := rpow_neg_half_mul (Spaces.gam α) hs
    have hw : Spaces.w z * (z / (1 + z) ^ 3) = 1 / (z * (1 + z)) := w_mul_z_div z hz
    simp only [DthWt, C0gv]
    calc (Spaces.Dth f z θ * Spaces.w z * Real.sin (2 * θ) ^ (-(Spaces.gam α / 2)))
          * (C0g θ * z / (1 + z) ^ 3 * Real.sin (2 * θ) ^ (Spaces.gam α / 2))
        = (Spaces.Dth f z θ * C0g θ) * (Spaces.w z * (z / (1 + z) ^ 3))
            * (Real.sin (2 * θ) ^ (-(Spaces.gam α / 2))
              * Real.sin (2 * θ) ^ (Spaces.gam α / 2)) := by ring
      _ = (Spaces.Dth f z θ * C0g θ) * (1 / (z * (1 + z))) * 1 := by
          rw [hw, hprod]
      _ = Spaces.Dth f z θ * C0g θ / (z * (1 + z)) := by ring

/-- For two reals, `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (1 / 2) * (a ^ 2 + b ^ 2) := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-! ## The radial factor `z/(1+z)³` -/

/-- Pointwise majorant for the radial factor: `(s/(1+s)³)² ≤ (1+s)^{-4}` for `s ≥ 0`. -/
private lemma zc3_sq_le (s : ℝ) (hs : 0 ≤ s) :
    (s / (1 + s) ^ 3) ^ 2 ≤ (1 + s) ^ (-4 : ℝ) := by
  have hs1 : (0 : ℝ) < 1 + s := by linarith
  have h4 : (1 + s) ^ (-4 : ℝ) = (1 + s) ^ 2 / (1 + s) ^ 6 := by
    rw [Real.rpow_neg (le_of_lt hs1)]
    simp
    field_simp
  rw [h4, div_pow, show ((1 + s) ^ 3) ^ 2 = (1 + s) ^ 6 by rw [← pow_mul]]
  exact div_le_div_of_nonneg_right
    (by nlinarith [hs, sq_nonneg s] : s ^ 2 ≤ (1 + s) ^ 2) (by positivity)

private lemma integrableOn_zc3_sq :
    MeasureTheory.IntegrableOn (fun s : ℝ => (s / (1 + s) ^ 3) ^ 2) Spaces.Iz := by
  have hbase : MeasureTheory.IntegrableOn (fun s : ℝ => (1 + s) ^ (-4 : ℝ)) (Set.Ioi (0 : ℝ)) := by
    simpa only [add_comm] using (integrableOn_add_rpow_Ioi_of_lt (a := (-4 : ℝ)) (m := 1) (c := 0)
      (by norm_num) (by norm_num))
  have hcont : ContinuousOn (fun s : ℝ => (s / (1 + s) ^ 3) ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine ContinuousOn.pow (ContinuousOn.div continuousOn_id ?_ ?_) 2
    · exact (ContinuousOn.add continuousOn_const continuousOn_id).pow 3
    · intro s hs
      have : (0 : ℝ) < 1 + s := by linarith [show (0 : ℝ) < s from hs]
      positivity
  have hIoi : MeasureTheory.IntegrableOn (fun s : ℝ => (s / (1 + s) ^ 3) ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' hbase (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact zc3_sq_le s (le_of_lt hs)
  rw [Spaces.Iz]
  change Integrable (fun s : ℝ => (s / (1 + s) ^ 3) ^ 2) (volume.restrict (Set.Ici (0 : ℝ)))
  rw [← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := 0))]
  exact hIoi

private lemma integral_zc3_sq_le : ∫ s in Spaces.Iz, (s / (1 + s) ^ 3) ^ 2 ≤ 1 / 16 := by
  have h2 : (∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s) * Spaces.w s)) ^ 2)
      = ∫ s in Set.Ioi (0 : ℝ), (s / (1 + s) ^ 3) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    have hs1 : (0 : ℝ) < 1 + s := by linarith
    rw [Spaces.w]
    field_simp
  have h3 : (∫ s in Spaces.Iz, (s / (1 + s) ^ 3) ^ 2)
      = ∫ s in Set.Ioi (0 : ℝ), (s / (1 + s) ^ 3) ^ 2 := by
    rw [Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
  rw [h3, ← h2]
  change C0D ≤ 1 / 16
  exact C0D_le

/-! ## The angular factors -/

/-- The angular factor of the `KC0` estimate. -/
abbrev thetaK (α : ℝ) (θ : ℝ) : ℝ :=
  (3 * Spaces.K θ) ^ 2 * (Real.sin (2 * θ)) ^ (Spaces.gam α)

/-- The angular factor of the `KC1` estimate. -/
abbrev thetaC (α : ℝ) (θ : ℝ) : ℝ :=
  (C0g θ) ^ 2 * (Real.sin (2 * θ)) ^ (Spaces.gam α)

/-- `volume Iθ` is finite. -/
private lemma volume_Iθ_ne_top : volume Spaces.Iθ ≠ ⊤ := by
  rw [Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

private lemma thetaK_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ thetaK α θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)

private lemma thetaC_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ thetaC α θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)

private lemma aesm_sin_rpow (α : ℝ) (hα : 0 < α) :
    AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Spaces.gam α))
      (volume.restrict Spaces.Iθ) :=
  (ContinuousOn.rpow_const
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
      (fun _ _ => Or.inr (by simp only [Spaces.gam]; linarith))).aestronglyMeasurable
    measurableSet_Icc

private lemma aesm_thetaK (α : ℝ) (hα : 0 < α) :
    AEStronglyMeasurable (thetaK α) (volume.restrict Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable (fun θ : ℝ => (3 * Spaces.K θ) ^ 2)
      (volume.restrict Spaces.Iθ) :=
    (((continuous_const.mul continuous_K).pow 2).continuousOn).aestronglyMeasurable measurableSet_Icc
  have h2 := aesm_sin_rpow α hα
  exact h1.mul h2

private lemma aesm_thetaC (α : ℝ) (hα : 0 < α) :
    AEStronglyMeasurable (thetaC α) (volume.restrict Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable (fun θ : ℝ => (C0g θ) ^ 2) (volume.restrict Spaces.Iθ) :=
    ((continuous_C0g.pow 2).continuousOn).aestronglyMeasurable measurableSet_Icc
  have h2 := aesm_sin_rpow α hα
  exact h1.mul h2

/-- `(3 K(θ))² ≤ 81` everywhere. -/
private lemma threeK_sq_le (θ : ℝ) : (3 * Spaces.K θ) ^ 2 ≤ 81 := by
  have h1 : |Spaces.K θ| ≤ 3 := by
    have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hcos : |Real.cos θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact Real.cos_sq_le_one θ
    calc |Spaces.K θ| = 3 * |Real.sin θ| * |Real.cos θ ^ 2| := by
          unfold Spaces.K
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      _ ≤ 3 * 1 * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hsin (by norm_num)) hcos
            (abs_nonneg _) (by norm_num)
      _ = 3 := by norm_num
  have h2 : |3 * Spaces.K θ| ≤ 9 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    linarith
  calc (3 * Spaces.K θ) ^ 2 = |3 * Spaces.K θ| ^ 2 := (sq_abs _).symm
    _ ≤ 9 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = 81 := by norm_num

private lemma integrableOn_thetaK (α : ℝ) (hα : 0 < α) :
    MeasureTheory.IntegrableOn (thetaK α) Spaces.Iθ := by
  refine Integrable.mono'
    (MeasureTheory.integrableOn_const (s := Spaces.Iθ) (C := (81 : ℝ)) volume_Iθ_ne_top)
    (aesm_thetaK α hα) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (thetaK_nonneg α hθ)]
  have hr : (Real.sin (2 * θ)) ^ (Spaces.gam α) ≤ 1 :=
    Real.rpow_le_one hs0 (Real.sin_le_one _) (by simp only [Spaces.gam]; linarith)
  calc thetaK α θ = (3 * Spaces.K θ) ^ 2 * (Real.sin (2 * θ)) ^ (Spaces.gam α) := rfl
    _ ≤ 81 * 1 := mul_le_mul (threeK_sq_le θ) hr (Real.rpow_nonneg hs0 _) (by norm_num)
    _ = 81 := by ring

private lemma integrableOn_thetaC (α : ℝ) (hα : 0 < α) :
    MeasureTheory.IntegrableOn (thetaC α) Spaces.Iθ := by
  refine Integrable.mono' ((continuous_C0g.pow 2).continuousOn.integrableOn_Icc)
    (aesm_thetaC α hα) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (thetaC_nonneg α hθ)]
  have hr : (Real.sin (2 * θ)) ^ (Spaces.gam α) ≤ 1 :=
    Real.rpow_le_one hs0 (Real.sin_le_one _) (by simp only [Spaces.gam]; linarith)
  calc thetaC α θ = (C0g θ) ^ 2 * (Real.sin (2 * θ)) ^ (Spaces.gam α) := rfl
    _ ≤ (C0g θ) ^ 2 * 1 := mul_le_mul_of_nonneg_left hr (sq_nonneg _)
    _ = (C0g θ) ^ 2 := by ring

private lemma integral_thetaK_le (α : ℝ) (hα : 0 < α) :
    ∫ θ in Spaces.Iθ, thetaK α θ ≤ 729 := by
  have hb : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), thetaK α θ ≤ (81 : ℝ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hr : (Real.sin (2 * θ)) ^ (Spaces.gam α) ≤ 1 :=
      Real.rpow_le_one hs0 (Real.sin_le_one _) (by simp only [Spaces.gam]; linarith)
    calc thetaK α θ = (3 * Spaces.K θ) ^ 2 * (Real.sin (2 * θ)) ^ (Spaces.gam α) := rfl
      _ ≤ 81 * 1 := mul_le_mul (threeK_sq_le θ) hr (Real.rpow_nonneg hs0 _) (by norm_num)
      _ = 81 := by ring
  have hnn : 0 ≤ᵐ[volume.restrict Spaces.Iθ] thetaK α := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact thetaK_nonneg α hθ
  have hmono := MeasureTheory.integral_mono_of_nonneg hnn
    (MeasureTheory.integrableOn_const (s := Spaces.Iθ) (C := (81 : ℝ)) volume_Iθ_ne_top) hb
  have h81 : ∫ θ in Spaces.Iθ, (81 : ℝ) = 81 * (π / 2) := by
    rw [Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [h81] at hmono
  nlinarith [hmono, Real.pi_lt_d2]

private lemma integral_thetaC_le (α : ℝ) (hα : 0 < α) :
    ∫ θ in Spaces.Iθ, thetaC α θ ≤ 729 := by
  have hb : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), thetaC α θ ≤ (C0g θ) ^ 2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hr : (Real.sin (2 * θ)) ^ (Spaces.gam α) ≤ 1 :=
      Real.rpow_le_one hs0 (Real.sin_le_one _) (by simp only [Spaces.gam]; linarith)
    calc thetaC α θ = (C0g θ) ^ 2 * (Real.sin (2 * θ)) ^ (Spaces.gam α) := rfl
      _ ≤ (C0g θ) ^ 2 * 1 := mul_le_mul_of_nonneg_left hr (sq_nonneg _)
      _ = (C0g θ) ^ 2 := by ring
  have hnn : 0 ≤ᵐ[volume.restrict Spaces.Iθ] thetaC α := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact thetaC_nonneg α hθ
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (C0g θ) ^ 2) Spaces.Iθ :=
    (continuous_C0g.pow 2).continuousOn.integrableOn_Icc
  have hmono := MeasureTheory.integral_mono_of_nonneg hnn hint hb
  have hC0Ih : (∫ θ in Spaces.Iθ, (C0g θ) ^ 2) = C0Ih := rfl
  rw [hC0Ih] at hmono
  exact hmono.trans C0Ih_le

/-! ## The `KC0`/`KC1` angular factors on the quadrant -/

private lemma Kv_sq_eq (α : ℝ) (p : ℝ × ℝ) (hp : p ∈ Spaces.Iz ×ˢ Spaces.Iθ) :
    Kv α p ^ 2 = (p.1 / (1 + p.1) ^ 3) ^ 2 * thetaK α p.2 := by
  have hθ := hp.2
  have hs0 : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsq : ((Real.sin (2 * p.2)) ^ (Spaces.gam α / 2)) ^ 2
      = (Real.sin (2 * p.2)) ^ (Spaces.gam α) := rpow_half_sq _ _ hs0
  simp only [Kv, thetaK]
  rw [mul_pow, hsq]
  ring

private lemma C0gv_sq_eq (α : ℝ) (p : ℝ × ℝ) (hp : p ∈ Spaces.Iz ×ˢ Spaces.Iθ) :
    C0gv α p ^ 2 = (p.1 / (1 + p.1) ^ 3) ^ 2 * thetaC α p.2 := by
  have hθ := hp.2
  have hs0 : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsq : ((Real.sin (2 * p.2)) ^ (Spaces.gam α / 2)) ^ 2
      = (Real.sin (2 * p.2)) ^ (Spaces.gam α) := rpow_half_sq _ _ hs0
  simp only [C0gv, thetaC]
  rw [mul_pow, hsq]
  ring

private lemma aesm_Kv (α : ℝ) : AEStronglyMeasurable (Kv α) muQ := by
  have hK : Measurable (fun p : ℝ × ℝ => 3 * Spaces.K p.2) :=
    (continuous_K.measurable.const_mul 3).comp measurable_snd
  have hz : Measurable (fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 3) := by fun_prop
  have hs : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Spaces.gam α / 2)) := by
    fun_prop
  have hm : Measurable (fun p : ℝ × ℝ => (3 * Spaces.K p.2) * (p.1 / (1 + p.1) ^ 3)
      * (Real.sin (2 * p.2)) ^ (Spaces.gam α / 2)) := (hK.mul hz).mul hs
  refine hm.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Kv]
  ring

private lemma aesm_C0gv (α : ℝ) : AEStronglyMeasurable (C0gv α) muQ := by
  have hC : Measurable (fun p : ℝ × ℝ => C0g p.2) :=
    continuous_C0g.measurable.comp measurable_snd
  have hz : Measurable (fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 3) := by fun_prop
  have hs : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Spaces.gam α / 2)) := by
    fun_prop
  have hm : Measurable (fun p : ℝ × ℝ => C0g p.2 * (p.1 / (1 + p.1) ^ 3)
      * (Real.sin (2 * p.2)) ^ (Spaces.gam α / 2)) := (hC.mul hz).mul hs
  refine hm.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [C0gv]
  ring

private lemma integrable_Kv_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Integrable (fun p => Kv α p ^ 2) muQ := by
  have hprod : Integrable (fun p : ℝ × ℝ => (p.1 / (1 + p.1) ^ 3) ^ 2 * thetaK α p.2) muQ :=
    integrableOn_zc3_sq.mul_prod (integrableOn_thetaK α hα)
  refine hprod.congr ?_
  filter_upwards [ae_mem_quadrant] with p hp
  exact (Kv_sq_eq α p hp).symm

private lemma integrable_C0gv_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Integrable (fun p => C0gv α p ^ 2) muQ := by
  have hprod : Integrable (fun p : ℝ × ℝ => (p.1 / (1 + p.1) ^ 3) ^ 2 * thetaC α p.2) muQ :=
    integrableOn_zc3_sq.mul_prod (integrableOn_thetaC α hα)
  refine hprod.congr ?_
  filter_upwards [ae_mem_quadrant] with p hp
  exact (C0gv_sq_eq α p hp).symm

private lemma integral_Kv_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ p, Kv α p ^ 2 ∂muQ ≤ 729 / 16 := by
  have heq : (fun p : ℝ × ℝ => Kv α p ^ 2)
      =ᵐ[muQ] fun p : ℝ × ℝ => (p.1 / (1 + p.1) ^ 3) ^ 2 * thetaK α p.2 := by
    filter_upwards [ae_mem_quadrant] with p hp
    exact Kv_sq_eq α p hp
  have h1 : ∫ p, Kv α p ^ 2 ∂muQ
      = (∫ s in Spaces.Iz, (s / (1 + s) ^ 3) ^ 2) * (∫ θ in Spaces.Iθ, thetaK α θ) := by
    rw [MeasureTheory.integral_congr_ae heq]
    exact MeasureTheory.integral_prod_mul (fun s : ℝ => (s / (1 + s) ^ 3) ^ 2) (thetaK α)
  rw [h1]
  have hAn : 0 ≤ ∫ s in Spaces.Iz, (s / (1 + s) ^ 3) ^ 2 :=
    integral_nonneg (fun s => sq_nonneg _)
  have hBn : 0 ≤ ∫ θ in Spaces.Iθ, thetaK α θ :=
    integral_nonneg_of_ae (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact thetaK_nonneg α hθ)
  have hA := integral_zc3_sq_le
  have hB := integral_thetaK_le α hα
  nlinarith [hA, hB, hAn, hBn]

private lemma integral_C0gv_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ p, C0gv α p ^ 2 ∂muQ ≤ 729 / 16 := by
  have heq : (fun p : ℝ × ℝ => C0gv α p ^ 2)
      =ᵐ[muQ] fun p : ℝ × ℝ => (p.1 / (1 + p.1) ^ 3) ^ 2 * thetaC α p.2 := by
    filter_upwards [ae_mem_quadrant] with p hp
    exact C0gv_sq_eq α p hp
  have h1 : ∫ p, C0gv α p ^ 2 ∂muQ
      = (∫ s in Spaces.Iz, (s / (1 + s) ^ 3) ^ 2) * (∫ θ in Spaces.Iθ, thetaC α θ) := by
    rw [MeasureTheory.integral_congr_ae heq]
    exact MeasureTheory.integral_prod_mul (fun s : ℝ => (s / (1 + s) ^ 3) ^ 2) (thetaC α)
  rw [h1]
  have hAn : 0 ≤ ∫ s in Spaces.Iz, (s / (1 + s) ^ 3) ^ 2 :=
    integral_nonneg (fun s => sq_nonneg _)
  have hBn : 0 ≤ ∫ θ in Spaces.Iθ, thetaC α θ :=
    integral_nonneg_of_ae (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact thetaC_nonneg α hθ)
  have hA := integral_zc3_sq_le
  have hB := integral_thetaC_le α hα
  nlinarith [hA, hB, hAn, hBn]

/-! ## The energy is nonnegative -/

private lemma Ewgam_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) : 0 ≤ CT.Ewgam α g := by
  simp only [CT.Ewgam, Spaces.Iz, Spaces.Iθ]
  refine integral_nonneg (fun z => ?_)
  refine integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hs0 _)

/-! ## The two halves of the estimate -/

private lemma KC0_sq_le_aux (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hs : Spaces.SmoothNbhd f)
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ => (Spaces.Dth f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) Spaces.Iθ)
    (hQ : MeasureTheory.IntegrableOn (fun z => ∫ θ in Spaces.Iθ, (Spaces.Dth f z θ) ^ 2
        * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) Spaces.Iz) :
    (CT.KC0 f) ^ 2 ≤ 100 * CT.Ewgam α (Spaces.Dth f) := by
  obtain ⟨hAaesm, hAint, hAval⟩ := Dth_gam_prod_facts α hα hα1 f hs hsl hQ
  have hv0aesm : AEStronglyMeasurable (Kv α) muQ := aesm_Kv α
  have hv0int : Integrable (fun p => Kv α p ^ 2) muQ := integrable_Kv_sq α hα hα1
  have hv0bd : ∫ p, Kv α p ^ 2 ∂muQ ≤ 729 / 16 := integral_Kv_sq_le α hα hα1
  have hprodint : Integrable (fun p : ℝ × ℝ => DthWt α f p * Kv α p) muQ := by
    have hmaj : Integrable (fun p : ℝ × ℝ => (1 / 2) * (DthWt α f p ^ 2 + Kv α p ^ 2)) muQ :=
      (hAint.add hv0int).const_mul (1 / 2)
    have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => DthWt α f p * Kv α p) muQ :=
      hAaesm.mul hv0aesm
    refine Integrable.mono' hmaj haesm ?_
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact abs_mul_le_half_sq _ _
  have hfub : ∫ p, DthWt α f p * Kv α p ∂muQ
      = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ,
          Spaces.Dth f z θ * (3 * Spaces.K θ) / (z * (1 + z)) := by
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => DthWt α f p * Kv α p) hprodint]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact DthWt_mul_Kv α hα f hz hθ
  have hKC0 : CT.KC0 f = ∫ p, DthWt α f p * Kv α p ∂muQ := by
    rw [KC0_eq_double]
    exact hfub.symm
  have hcs := sq_integral_mul_le muQ (DthWt α f) (Kv α) hAaesm hv0aesm hAint hv0int
  have hEg : 0 ≤ CT.Ewgam α (Spaces.Dth f) := Ewgam_nonneg α (Spaces.Dth f)
  calc (CT.KC0 f) ^ 2 = (∫ p, DthWt α f p * Kv α p ∂muQ) ^ 2 := by rw [hKC0]
    _ ≤ (∫ p, DthWt α f p ^ 2 ∂muQ) * (∫ p, Kv α p ^ 2 ∂muQ) := hcs
    _ = CT.Ewgam α (Spaces.Dth f) * (∫ p, Kv α p ^ 2 ∂muQ) := by rw [hAval]
    _ ≤ CT.Ewgam α (Spaces.Dth f) * (729 / 16) := mul_le_mul_of_nonneg_left hv0bd hEg
    _ ≤ 100 * CT.Ewgam α (Spaces.Dth f) := by nlinarith [hEg]

private lemma KC1_sq_le_aux (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hs : Spaces.SmoothNbhd f)
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ => (Spaces.Dth f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) Spaces.Iθ)
    (hQ : MeasureTheory.IntegrableOn (fun z => ∫ θ in Spaces.Iθ, (Spaces.Dth f z θ) ^ 2
        * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) Spaces.Iz) :
    (CT.KC1 f) ^ 2 ≤ 100 * CT.Ewgam α (Spaces.Dth f) := by
  obtain ⟨hAaesm, hAint, hAval⟩ := Dth_gam_prod_facts α hα hα1 f hs hsl hQ
  have hv1aesm : AEStronglyMeasurable (C0gv α) muQ := aesm_C0gv α
  have hv1int : Integrable (fun p => C0gv α p ^ 2) muQ := integrable_C0gv_sq α hα hα1
  have hv1bd : ∫ p, C0gv α p ^ 2 ∂muQ ≤ 729 / 16 := integral_C0gv_sq_le α hα hα1
  have hprodint : Integrable (fun p : ℝ × ℝ => DthWt α f p * C0gv α p) muQ := by
    have hmaj : Integrable (fun p : ℝ × ℝ => (1 / 2) * (DthWt α f p ^ 2 + C0gv α p ^ 2)) muQ :=
      (hAint.add hv1int).const_mul (1 / 2)
    have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => DthWt α f p * C0gv α p) muQ :=
      hAaesm.mul hv1aesm
    refine Integrable.mono' hmaj haesm ?_
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact abs_mul_le_half_sq _ _
  have hfub : ∫ p, DthWt α f p * C0gv α p ∂muQ
      = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * C0g θ / (z * (1 + z)) := by
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => DthWt α f p * C0gv α p) hprodint]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact DthWt_mul_C0gv α hα f hz hθ
  have hcomm : (∫ s in Spaces.Iz, ∫ θ in Spaces.Iθ, C0g θ * Spaces.Dth f s θ / (s * (1 + s)))
      = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * C0g θ / (z * (1 + z)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with z
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with θ
    ring
  have hKC1 : CT.KC1 f = -(∫ p, DthWt α f p * C0gv α p ∂muQ) := by
    rw [KC1_eq_double f hs, hfub, hcomm]
  have hcs := sq_integral_mul_le muQ (DthWt α f) (C0gv α) hAaesm hv1aesm hAint hv1int
  have hEg : 0 ≤ CT.Ewgam α (Spaces.Dth f) := Ewgam_nonneg α (Spaces.Dth f)
  have hcs' : (∫ p, DthWt α f p * C0gv α p ∂muQ) ^ 2
      ≤ (∫ p, DthWt α f p ^ 2 ∂muQ) * (∫ p, C0gv α p ^ 2 ∂muQ) := hcs
  calc (CT.KC1 f) ^ 2 = (∫ p, DthWt α f p * C0gv α p ∂muQ) ^ 2 := by rw [hKC1]; ring
    _ ≤ (∫ p, DthWt α f p ^ 2 ∂muQ) * (∫ p, C0gv α p ^ 2 ∂muQ) := hcs'
    _ = CT.Ewgam α (Spaces.Dth f) * (∫ p, C0gv α p ^ 2 ∂muQ) := by rw [hAval]
    _ ≤ CT.Ewgam α (Spaces.Dth f) * (729 / 16) := mul_le_mul_of_nonneg_left hv1bd hEg
    _ ≤ 100 * CT.Ewgam α (Spaces.Dth f) := by nlinarith [hEg]

theorem KC_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ), Work.Spaces.SmoothNbhd f →
      (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.Dth f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth f z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iz →
      (Work.Coercivity.CT.KC0 f) ^ 2 ≤ C * Work.Coercivity.CT.Ewgam α (Work.Spaces.Dth f)
      ∧ (Work.Coercivity.CT.KC1 f) ^ 2 ≤ C * Work.Coercivity.CT.Ewgam α (Work.Spaces.Dth f) := by
  refine ⟨100, by norm_num, ?_⟩
  intro f hs hsl hQ
  exact ⟨KC0_sq_le_aux α hα hα1 f hs hsl hQ, KC1_sq_le_aux α hα hα1 f hs hsl hQ⟩

end Work.Coercivity
