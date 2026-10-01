/-
# P9F — the real-axis Laplace transform of HB Lemma 7.1's test function

`tf71F_real_eq`: for real `z ≠ 0`, `θ ∈ (0, π/2)`, `λ > 0`,

  `∫₀^{2γ} e^{-zt} f(t) dt = tf71Fr θ λ z`,

where `f` is the test function of HB Lemma 7.1 (`tf71f`, the closed form `tf71cf` on
`[0,2γ]`) and `tf71Fr` is the closed form recorded in `Defs`.

The proof splits the integrand against the five elementary Laplace integrals
(`∫ e^{-zt}`, `∫ t e^{-zt}`, `∫ e^{-zt}cos(ζt)`, `∫ e^{-zt}sin(ζt)`, `∫ t e^{-zt}cos(ζt)`,
proved in the sibling modules `integral_exp_neg_mul*`), using the addition formulas for
`sin(2θ - ζt)` and `sin(θ - ζt)` and the end-point identities `ζ·2γ = 2θ`,
`sin (2θ) = tf71s2 θ`, `cos (2θ) = tf71c2 θ`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9F.Defs
import Submission.Work.ZeroFreeTables.testFn71_defs
import Submission.Work.ZeroFreeTables.P9F.integral_exp_neg_mul
import Submission.Work.ZeroFreeTables.P9F.integral_exp_neg_mul_id
import Submission.Work.ZeroFreeTables.P9F.integral_exp_neg_mul_cos
import Submission.Work.ZeroFreeTables.P9F.integral_exp_neg_mul_sin
import Submission.Work.ZeroFreeTables.P9F.integral_exp_neg_mul_id_cos

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables.P9F

/-! ## Auxiliary trig identities for the parameters `ζ = λ tan θ`, `γ = θ/ζ` -/

theorem tf71F_ζ_mul_twoγ {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) :
    tf71ζ θ lam * (2 * tf71γ θ lam) = 2 * θ := by
  rw [show tf71ζ θ lam * (2 * tf71γ θ lam) = 2 * (tf71ζ θ lam * tf71γ θ lam) from by ring,
    tf71ζ_mul_γ hθ0 hθ1 hlam]

theorem tf71F_s2_eq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    tf71s2 θ = Real.sin (2 * θ) := by
  have hc : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo
      (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], hθ1⟩)
    linarith
  have h1 : 1 + Real.tan θ ^ 2 = (Real.cos θ)⁻¹ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [tf71s2, h1, Real.tan_eq_sin_div_cos, Real.sin_two_mul]
  field_simp

theorem tf71F_c2_eq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    tf71c2 θ = Real.cos (2 * θ) := by
  have hc : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo
      (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], hθ1⟩)
    linarith
  have h1 : 1 + Real.tan θ ^ 2 = (Real.cos θ)⁻¹ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [tf71c2, h1, Real.tan_eq_sin_div_cos, Real.cos_two_mul]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem tf71F_Bcf_eq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    tf71Bcf θ = 2 * (Real.cos θ / Real.sin θ) - Real.cos (2 * θ) / Real.sin (2 * θ) := by
  have hc : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo
      (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], hθ1⟩)
    linarith
  have ht : Real.tan θ ≠ 0 := ne_of_gt (tf71_tan_pos hθ0 hθ1)
  have h2 : 2 * (Real.cos θ / Real.sin θ) = 2 / Real.tan θ := by
    rw [Real.tan_eq_sin_div_cos]
    try field_simp
  have h3 : Real.cos (2 * θ) / Real.sin (2 * θ) = (1 - Real.tan θ ^ 2) / (2 * Real.tan θ) := by
    rw [← tf71F_c2_eq hθ0 hθ1, ← tf71F_s2_eq hθ0 hθ1, tf71c2, tf71s2]
    field_simp
    try ring
  rw [h2, h3, tf71Bcf]
  field_simp
  ring

/-! ## The expansion of the closed form as a five-term linear combination

Writing `A = λ(1+tan²θ)` for the prefactor of `tf71cf` and `Bcf = tf71Bcf θ`, the closed
form on `[0,2γ]` equals

  `A·[A(γ - t/2)cos(ζt) + λ(2γ - t) + (sin(2θ-ζt))/sin(2θ) - 2 - 2 sin(θ-ζt)/sin θ]`,

and expanding the sines of differences turns `e^{-zt}·tf71cf θ λ t` into the five-term
combination below. -/

/-- Coefficient of `e^{-zt}·t·cos(ζt)`. -/
def tf71Fc1 (θ lam : ℝ) : ℝ :=
  -((lam * (1 + Real.tan θ ^ 2)) * (lam * (1 + Real.tan θ ^ 2)) / 2)

/-- Coefficient of `e^{-zt}·cos(ζt)`. -/
def tf71Fc2 (θ lam : ℝ) : ℝ :=
  lam * (1 + Real.tan θ ^ 2) * ((lam * (1 + Real.tan θ ^ 2)) * tf71γ θ lam - 1)

/-- Coefficient of `e^{-zt}·sin(ζt)`. -/
def tf71Fc3 (θ lam : ℝ) : ℝ := lam * (1 + Real.tan θ ^ 2) * tf71Bcf θ

/-- Coefficient of `e^{-zt}`. -/
def tf71Fc4 (θ lam : ℝ) : ℝ :=
  lam * (1 + Real.tan θ ^ 2) * (2 * lam * tf71γ θ lam - 2)

/-- Coefficient of `e^{-zt}·t`. -/
def tf71Fc5 (θ lam : ℝ) : ℝ := -((lam * (1 + Real.tan θ ^ 2)) * lam)

theorem tf71F_pointwise (θ lam z : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hsinθ : Real.sin θ ≠ 0) (hsin2θ : Real.sin (2 * θ) ≠ 0) (t : ℝ) :
    Real.exp (-(z * t)) * tf71cf θ lam t =
      tf71Fc1 θ lam * (Real.exp (-(z * t)) * (t * Real.cos (tf71ζ θ lam * t)))
      + tf71Fc2 θ lam * (Real.exp (-(z * t)) * Real.cos (tf71ζ θ lam * t))
      + tf71Fc3 θ lam * (Real.exp (-(z * t)) * Real.sin (tf71ζ θ lam * t))
      + tf71Fc4 θ lam * Real.exp (-(z * t))
      + tf71Fc5 θ lam * (Real.exp (-(z * t)) * t) := by
  rw [tf71cf, tf71Fc1, tf71Fc2, tf71Fc3, tf71Fc4, tf71Fc5, tf71F_Bcf_eq hθ0 hθ1,
    Real.sin_sub, Real.sin_sub]
  field_simp
  ring

/-! ## Linearity of the interval integral for a five-term combination -/

theorem tf71F_integral_linear5 (c1 c2 c3 c4 c5 p q : ℝ) (f1 f2 f3 f4 f5 : ℝ → ℝ)
    (h1 : IntervalIntegrable f1 MeasureTheory.volume p q)
    (h2 : IntervalIntegrable f2 MeasureTheory.volume p q)
    (h3 : IntervalIntegrable f3 MeasureTheory.volume p q)
    (h4 : IntervalIntegrable f4 MeasureTheory.volume p q)
    (h5 : IntervalIntegrable f5 MeasureTheory.volume p q) :
    ∫ t in p..q, (c1 * f1 t + c2 * f2 t + c3 * f3 t + c4 * f4 t + c5 * f5 t)
      = c1 * (∫ t in p..q, f1 t) + c2 * (∫ t in p..q, f2 t) + c3 * (∫ t in p..q, f3 t)
        + c4 * (∫ t in p..q, f4 t) + c5 * (∫ t in p..q, f5 t) := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  all_goals
    (repeat' apply IntervalIntegrable.add) <;>
    (first
      | exact h1.const_mul c1
      | exact h2.const_mul c2
      | exact h3.const_mul c3
      | exact h4.const_mul c4
      | exact h5.const_mul c5)

/-! ## The five elementary integrals, in the normalisations of `Defs` -/

theorem tf71F_integral_I4 (θ lam z : ℝ) (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (-(z * t)) = tf71I4 θ lam z := by
  rw [integral_exp_neg_mul z (2 * tf71γ θ lam) hz]
  simp only [tf71I4, tf71Ec]

theorem tf71F_integral_I5 (θ lam z : ℝ) (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (-(z * t)) * t = tf71I5 θ lam z := by
  rw [integral_exp_neg_mul_id z (2 * tf71γ θ lam) hz]
  simp only [tf71I5, tf71Ec]

theorem tf71F_integral_Jc (θ lam z : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) :
    ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (-(z * t)) * Real.cos (tf71ζ θ lam * t)
      = tf71Jc θ lam z := by
  have hζne : tf71ζ θ lam ≠ 0 := ne_of_gt (tf71ζ_pos hθ0 hθ1 hlam)
  rw [integral_exp_neg_mul_cos z (tf71ζ θ lam) (2 * tf71γ θ lam) hζne,
    tf71F_ζ_mul_twoγ hθ0 hθ1 hlam, ← tf71F_s2_eq hθ0 hθ1, ← tf71F_c2_eq hθ0 hθ1]
  simp only [tf71Jc, tf71Ec, tf71Dc, tf71ζ]
  try ring

theorem tf71F_integral_Js (θ lam z : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) :
    ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (-(z * t)) * Real.sin (tf71ζ θ lam * t)
      = tf71Js θ lam z := by
  have hζne : tf71ζ θ lam ≠ 0 := ne_of_gt (tf71ζ_pos hθ0 hθ1 hlam)
  rw [integral_exp_neg_mul_sin z (tf71ζ θ lam) (2 * tf71γ θ lam) hζne,
    tf71F_ζ_mul_twoγ hθ0 hθ1 hlam, ← tf71F_s2_eq hθ0 hθ1, ← tf71F_c2_eq hθ0 hθ1]
  simp only [tf71Js, tf71Ec, tf71Dc, tf71ζ]
  try ring

theorem tf71F_integral_Kc (θ lam z : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) :
    ∫ t in (0:ℝ)..(2 * tf71γ θ lam),
        Real.exp (-(z * t)) * (t * Real.cos (tf71ζ θ lam * t)) = tf71Kc θ lam z := by
  have hζne : tf71ζ θ lam ≠ 0 := ne_of_gt (tf71ζ_pos hθ0 hθ1 hlam)
  rw [integral_exp_neg_mul_id_cos z (tf71ζ θ lam) (2 * tf71γ θ lam) hζne,
    tf71F_ζ_mul_twoγ hθ0 hθ1 hlam, ← tf71F_s2_eq hθ0 hθ1, ← tf71F_c2_eq hθ0 hθ1]
  simp only [tf71Kc, tf71Ec, tf71Dc, tf71ζ]
  try ring

/-! ## The main identity -/

theorem tf71F_real_eq (θ lam z : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (-(z * t)) * tf71f θ lam t = tf71Fr θ lam z := by
  have hγ : 0 < tf71γ θ lam := tf71γ_pos hθ0 hθ1 hlam
  have hx0 : (0:ℝ) ≤ 2 * tf71γ θ lam := by linarith
  have hsinθ : Real.sin θ ≠ 0 := tf71_sinθ_ne hθ0 hθ1
  have hsin2θ : Real.sin (2 * θ) ≠ 0 := tf71_sin2θ_ne hθ0 hθ1
  -- the test function agrees with the closed form `tf71cf` on `[0, 2γ]`
  have hf_eq : ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (-(z * t)) * tf71f θ lam t
      = ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (-(z * t)) * tf71cf θ lam t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx0] at ht
    show Real.exp (-(z * t)) * tf71f θ lam t = Real.exp (-(z * t)) * tf71cf θ lam t
    rw [tf71f, if_pos ht.1, min_eq_left ht.2]
  -- integrability of the five elementary integrands
  have hint1 : IntervalIntegrable
      (fun t : ℝ => Real.exp (-(z * t)) * (t * Real.cos (tf71ζ θ lam * t)))
      MeasureTheory.volume (0:ℝ) (2 * tf71γ θ lam) :=
    (by fun_prop : Continuous
      (fun t : ℝ => Real.exp (-(z * t)) * (t * Real.cos (tf71ζ θ lam * t)))).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun t : ℝ => Real.exp (-(z * t)) * Real.cos (tf71ζ θ lam * t))
      MeasureTheory.volume (0:ℝ) (2 * tf71γ θ lam) :=
    (by fun_prop : Continuous
      (fun t : ℝ => Real.exp (-(z * t)) * Real.cos (tf71ζ θ lam * t))).intervalIntegrable _ _
  have hint3 : IntervalIntegrable
      (fun t : ℝ => Real.exp (-(z * t)) * Real.sin (tf71ζ θ lam * t))
      MeasureTheory.volume (0:ℝ) (2 * tf71γ θ lam) :=
    (by fun_prop : Continuous
      (fun t : ℝ => Real.exp (-(z * t)) * Real.sin (tf71ζ θ lam * t))).intervalIntegrable _ _
  have hint4 : IntervalIntegrable (fun t : ℝ => Real.exp (-(z * t)))
      MeasureTheory.volume (0:ℝ) (2 * tf71γ θ lam) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(z * t)))).intervalIntegrable _ _
  have hint5 : IntervalIntegrable (fun t : ℝ => Real.exp (-(z * t)) * t)
      MeasureTheory.volume (0:ℝ) (2 * tf71γ θ lam) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(z * t)) * t)).intervalIntegrable _ _
  -- split the integral into the five pieces
  have hsplit : ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (-(z * t)) * tf71cf θ lam t
      = tf71Fc1 θ lam
          * (∫ t in (0:ℝ)..(2 * tf71γ θ lam),
              Real.exp (-(z * t)) * (t * Real.cos (tf71ζ θ lam * t)))
        + tf71Fc2 θ lam
          * (∫ t in (0:ℝ)..(2 * tf71γ θ lam),
              Real.exp (-(z * t)) * Real.cos (tf71ζ θ lam * t))
        + tf71Fc3 θ lam
          * (∫ t in (0:ℝ)..(2 * tf71γ θ lam),
              Real.exp (-(z * t)) * Real.sin (tf71ζ θ lam * t))
        + tf71Fc4 θ lam
          * (∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (-(z * t)))
        + tf71Fc5 θ lam
          * (∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (-(z * t)) * t) := by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      tf71Fc1 θ lam * (Real.exp (-(z * t)) * (t * Real.cos (tf71ζ θ lam * t)))
      + tf71Fc2 θ lam * (Real.exp (-(z * t)) * Real.cos (tf71ζ θ lam * t))
      + tf71Fc3 θ lam * (Real.exp (-(z * t)) * Real.sin (tf71ζ θ lam * t))
      + tf71Fc4 θ lam * Real.exp (-(z * t))
      + tf71Fc5 θ lam * (Real.exp (-(z * t)) * t))
      (fun t _ => tf71F_pointwise θ lam z hθ0 hθ1 hsinθ hsin2θ t)]
    exact tf71F_integral_linear5 _ _ _ _ _ 0 (2 * tf71γ θ lam) _ _ _ _ _
      hint1 hint2 hint3 hint4 hint5
  rw [hf_eq, hsplit, tf71F_integral_Kc θ lam z hθ0 hθ1 hlam,
    tf71F_integral_Jc θ lam z hθ0 hθ1 hlam, tf71F_integral_Js θ lam z hθ0 hθ1 hlam,
    tf71F_integral_I4 θ lam z hz, tf71F_integral_I5 θ lam z hz]
  simp only [tf71Fc1, tf71Fc2, tf71Fc3, tf71Fc4, tf71Fc5, tf71Fr]
  ring

end Work.ZeroFreeTables.P9F
