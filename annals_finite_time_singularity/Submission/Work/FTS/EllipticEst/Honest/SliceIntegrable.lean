/-
Work module: `SliceIntegrable`.

The integrability on the open angular interval `Iθo = (0, π/2)` of the seven integrands of
the `θ`-integration by parts behind `Work.FTS.EllipticEst.Honest.SliceIbpTheta`:

`sig η θ * (f' θ)²`, `sig η θ * f θ * f'' θ`, `sigD η θ * f θ * f' θ`,
`rho η θ * f θ * f' θ`, `rhoD η θ * (f θ)²`, `(f θ)² * sig η θ`,
`(f θ)² cos²(2θ) sin(2θ)^{-(2+η)}`.

Every one of them is pointwise dominated on `Iθo` by `K * sin(2θ)^{-η}` for an explicit
`K ≥ 0`: the weights satisfy `sig η θ = sin(2θ)^{-η}`,
`sigD η θ = -2η cos(2θ) sin(2θ)^{-η-1}` (and `sin(2θ)^{-η-1}·sin(2θ) = sin(2θ)^{-η}`),
`rho η θ = cos(2θ) sin(2θ)^{-η-1}`,
`rhoD η θ = -2 sin(2θ)^{-η} - 2(η+1) cos²(2θ) sin(2θ)^{-(2+η)}`
(and `sin(2θ)^{-(2+η)}·sin²(2θ) = sin(2θ)^{-η}`); the function `f` and its first two
derivatives are bounded on `Iθo` by the hypotheses, and `|f| ≤ C·min(θ, π/2-θ) ≤
(Cπ/4)·sin(2θ)` by Jordan's inequality.  Since `η < 1`, `sin(2θ)^{-η}` is integrable on
`Iθo`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.SliceIbpDefs
import Submission.Work.Elliptic.integrableOn_of_rpow_majorant
import Submission.Work.Spaces.sin_rpow_le_majorant_pi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option linter.unusedVariables false

/-! ## Elementary facts about the open interval `Iθo = (0, π/2)` -/

/-- `sin(2θ)` is positive on `Iθo`. -/
private lemma sin_two_pos_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Jordan's inequality on the two halves of `Iθo`: `min θ (π/2-θ) ≤ (π/4) sin(2θ)`. -/
private lemma min_le_pi_div_four_sin_two {θ : ℝ} (hθ : θ ∈ Iθo) :
    min θ (Real.pi / 2 - θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases le_total θ (Real.pi / 4) with h | h
  · have hmin : min θ (Real.pi / 2 - θ) = θ := min_eq_left (by linarith)
    rw [hmin]
    have hj := Real.mul_le_sin (by linarith : (0:ℝ) ≤ 2 * θ) (by linarith : 2 * θ ≤ Real.pi / 2)
    have he : 2 / Real.pi * (2 * θ) = 4 / Real.pi * θ := by ring
    rw [he] at hj
    have hmul := mul_le_mul_of_nonneg_left hj (by positivity : (0:ℝ) ≤ Real.pi / 4)
    have he2 : Real.pi / 4 * (4 / Real.pi * θ) = θ := by field_simp
    calc θ = Real.pi / 4 * (4 / Real.pi * θ) := he2.symm
      _ ≤ Real.pi / 4 * Real.sin (2 * θ) := hmul
  · have hmin : min θ (Real.pi / 2 - θ) = Real.pi / 2 - θ := min_eq_right (by linarith)
    rw [hmin]
    have hsin : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
      rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
    rw [hsin]
    have hj := Real.mul_le_sin (by linarith : (0:ℝ) ≤ 2 * (Real.pi / 2 - θ))
      (by linarith : 2 * (Real.pi / 2 - θ) ≤ Real.pi / 2)
    have he : 2 / Real.pi * (2 * (Real.pi / 2 - θ)) = 4 / Real.pi * (Real.pi / 2 - θ) := by ring
    rw [he] at hj
    have hmul := mul_le_mul_of_nonneg_left hj (by positivity : (0:ℝ) ≤ Real.pi / 4)
    have he2 : Real.pi / 4 * (4 / Real.pi * (Real.pi / 2 - θ)) = Real.pi / 2 - θ := by field_simp
    calc Real.pi / 2 - θ = Real.pi / 4 * (4 / Real.pi * (Real.pi / 2 - θ)) := he2.symm
      _ ≤ Real.pi / 4 * Real.sin (2 * (Real.pi / 2 - θ)) := hmul

/-- The two endpoint bounds for `f` give `|f θ| ≤ (Cπ/4) sin(2θ)` on `Iθo`. -/
private lemma abs_f_le {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb1 : ∀ θ ∈ Iθo, |f θ| ≤ C * θ) (hb2 : ∀ θ ∈ Iθo, |f θ| ≤ C * (Real.pi / 2 - θ))
    {θ : ℝ} (hθ : θ ∈ Iθo) :
    |f θ| ≤ C * (Real.pi / 4) * Real.sin (2 * θ) := by
  have hmin : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := by
    rw [mul_min_of_nonneg _ _ hC]
    exact le_min (hb1 θ hθ) (hb2 θ hθ)
  calc |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hmin
    _ ≤ C * ((Real.pi / 4) * Real.sin (2 * θ)) :=
        mul_le_mul_of_nonneg_left (min_le_pi_div_four_sin_two hθ) hC
    _ = C * (Real.pi / 4) * Real.sin (2 * θ) := by ring

/-- `s^(-a-1) · s = s^(-a)` for `s > 0`. -/
private lemma rpow_neg_sub_one_mul {s a : ℝ} (hs : 0 < s) : s ^ (-a - 1) * s = s ^ (-a) := by
  nth_rewrite 2 [← Real.rpow_one s]
  rw [← Real.rpow_add hs (-a - 1) 1]
  rw [show (-a - 1 : ℝ) + 1 = -a by ring]

/-- `s^2 · s^(-(2+η)) = s^(-η)` for `s > 0`. -/
private lemma rpow_sq_mul_neg_two {s η : ℝ} (hs : 0 < s) :
    s ^ 2 * s ^ (-(2 + η)) = s ^ (-η) := by
  rw [← Real.rpow_natCast s 2]
  rw [← Real.rpow_add hs ((2 : ℕ) : ℝ) (-(2 + η))]
  rw [show ((2 : ℕ) : ℝ) + (-(2 + η)) = -η by push_cast; ring]

/-! ## The integrability of the singular weight and the domination principle -/

/-- `θ ↦ sin(2θ)^p` is integrable on the open interval `Iθo` for `p > -1`. -/
private lemma integrableOn_sin_rpow_Ioo {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Iθo volume := by
  by_cases hp0 : 0 ≤ p
  · -- nonnegative exponent: the integrand is bounded by `1` on the finite interval
    have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Iθo :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun θ _ => Or.inr hp0)
    refine MeasureTheory.Integrable.mono' (f := fun θ : ℝ => (Real.sin (2 * θ)) ^ p)
      (g := fun _ : ℝ => (1 : ℝ))
      (MeasureTheory.integrableOn_const (s := Iθo) (C := (1 : ℝ)) ?_) ?_ ?_
    · rw [Iθo, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    · exact hcont.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sin_two_pos_Iθo hθ).le p)]
      exact Real.rpow_le_one (sin_two_pos_Iθo hθ).le (Real.sin_le_one _) hp0
  · -- negative exponent: compare with the integrable endpoint majorant
    simp only [not_le] at hp0
    have hq : 0 < -p := by linarith
    have hq1 : -p < 1 := by linarith
    have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Iθo :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_Iθo hθ)))
    refine (Work.Elliptic.integrableOn_of_rpow_majorant (η := -p) hq.le hq1
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) (-p)) hcont
      ?_).mono_set Ioo_subset_Icc_self
    intro θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sin_two_pos_Iθo hθ).le p)]
    simpa only [neg_neg] using
      Work.Spaces.sin_rpow_le_majorant_pi (-p) θ hq ⟨hθ.1.le, hθ.2.le⟩

/-- A function on `Iθo` dominated pointwise by `K · sin(2θ)^p` with `p > -1` is integrable. -/
private lemma integrableOn_of_sin_rpow_bound {u : ℝ → ℝ} {K p : ℝ} (hK : 0 ≤ K) (hp : -1 < p)
    (hu : ContinuousOn u Iθo)
    (h : ∀ θ ∈ Iθo, |u θ| ≤ K * (Real.sin (2 * θ)) ^ p) :
    IntegrableOn u Iθo volume := by
  have hbase : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (volume.restrict Iθo) :=
    integrableOn_sin_rpow_Ioo hp
  have hmaj : Integrable (fun θ : ℝ => K * (Real.sin (2 * θ)) ^ p) (volume.restrict Iθo) :=
    hbase.const_mul K
  refine MeasureTheory.Integrable.mono' (f := u)
    (g := fun θ : ℝ => K * (Real.sin (2 * θ)) ^ p) hmaj ?_ ?_
  · exact hu.aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs]
    exact h θ hθ

/-! ## Continuity of the derivatives of a `C²` function on the closed interval -/

/-- The derivative of a `C²` function on `[0, π/2]` is continuous on the open interval. -/
private lemma continuousOn_deriv_Iθo {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (Real.pi / 2))) :
    ContinuousOn (deriv f) Iθo := by
  have hd : ContinuousOn (derivWithin f (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) :=
    hf.continuousOn_derivWithin (uniqueDiffOn_Icc (by positivity : (0:ℝ) < Real.pi / 2))
      (by norm_num)
  refine (hd.mono Ioo_subset_Icc_self).congr ?_
  intro θ hθ
  exact (derivWithin_of_mem_nhds (Icc_mem_nhds hθ.1 hθ.2)).symm

/-- The second derivative of a `C²` function on `[0, π/2]` is continuous on the open
interval. -/
private lemma continuousOn_deriv_deriv_Iθo {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (Real.pi / 2))) :
    ContinuousOn (deriv (deriv f)) Iθo := by
  have h2 : ContDiffOn ℝ 2 f Iθo := hf.mono Ioo_subset_Icc_self
  have h1 : ContDiffOn ℝ 1 (deriv f) Iθo := h2.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  exact h1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)

/-! ## The theorem -/

theorem SliceIntegrable (f : ℝ → ℝ) (η C : ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) (hπ : f (Real.pi / 2) = 0)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hC : 0 ≤ C)
    (hb1 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |f θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |f θ| ≤ C * (Real.pi / 2 - θ))
    (hb3 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |deriv f θ| ≤ C)
    (hb4 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |deriv (deriv f) θ| ≤ C) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Honest.sig η θ * (deriv f θ) ^ 2) Work.FTS.EllipticEst.Honest.Iθo MeasureTheory.volume ∧
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Honest.sig η θ * (f θ * deriv (deriv f) θ)) Work.FTS.EllipticEst.Honest.Iθo MeasureTheory.volume ∧
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Honest.sigD η θ * (f θ * deriv f θ)) Work.FTS.EllipticEst.Honest.Iθo MeasureTheory.volume ∧
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Honest.rho η θ * f θ * deriv f θ) Work.FTS.EllipticEst.Honest.Iθo MeasureTheory.volume ∧
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Honest.rhoD η θ * f θ ^ 2) Work.FTS.EllipticEst.Honest.Iθo MeasureTheory.volume ∧
    MeasureTheory.IntegrableOn (fun θ => f θ ^ 2 * Work.FTS.EllipticEst.Honest.sig η θ) Work.FTS.EllipticEst.Honest.Iθo MeasureTheory.volume ∧
    MeasureTheory.IntegrableOn (fun θ => f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) Work.FTS.EllipticEst.Honest.Iθo MeasureTheory.volume := by
  have hηm : -1 < -η := by linarith
  have hfC : ContinuousOn f Iθo := hf.continuousOn.mono Ioo_subset_Icc_self
  have hdfC : ContinuousOn (deriv f) Iθo := continuousOn_deriv_Iθo hf
  have hddfC : ContinuousOn (deriv (deriv f)) Iθo := continuousOn_deriv_deriv_Iθo hf
  have hsinC : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcosC : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) Iθo :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hsigp : ∀ p : ℝ, ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Iθo := fun p =>
    hsinC.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_Iθo hθ)))
  have hsigC : ContinuousOn (sig η) Iθo := hsigp (-η)
  have hsigDC : ContinuousOn (sigD η) Iθo := by
    change ContinuousOn
      (fun θ : ℝ => -2 * η * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-η - 1)) Iθo
    exact (hcosC.const_mul (-2 * η)).mul (hsigp (-η - 1))
  have hrhoC : ContinuousOn (rho η) Iθo := by
    change ContinuousOn (fun θ : ℝ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-η - 1)) Iθo
    exact hcosC.mul (hsigp (-η - 1))
  have hrhoDC : ContinuousOn (rhoD η) Iθo := by
    change ContinuousOn
      (fun θ : ℝ => -2 * (Real.sin (2 * θ)) ^ (-η)
        - 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) Iθo
    exact ((hsigp (-η)).const_mul (-2)).sub
      (((hcosC.pow 2).const_mul (2 * (η + 1))).mul (hsigp (-(2 + η))))
  have hfπ : ∀ θ ∈ Iθo, |f θ| ≤ C * (Real.pi / 4) * Real.sin (2 * θ) :=
    fun θ hθ => abs_f_le hC hb1 hb2 hθ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `sig η θ * (f' θ)²`
    refine integrableOn_of_sin_rpow_bound (K := C ^ 2) (p := -η) (sq_nonneg C) hηm ?_ ?_
    · refine (hsigC.mul (hdfC.pow 2)).congr ?_
      intro θ hθ
      simp only [Pi.mul_apply, Pi.pow_apply]
    · intro θ hθ
      have hs := sin_two_pos_Iθo hθ
      have hsp : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hs.le _
      have hd2 : (deriv f θ) ^ 2 ≤ C ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (deriv f θ)) (hb3 θ hθ) 2
        rwa [sq_abs] at h
      calc |sig η θ * (deriv f θ) ^ 2|
          = (Real.sin (2 * θ)) ^ (-η) * (deriv f θ) ^ 2 := by
            simp only [sig, abs_mul, abs_of_nonneg hsp, abs_of_nonneg (sq_nonneg (deriv f θ))]
        _ ≤ (Real.sin (2 * θ)) ^ (-η) * C ^ 2 := mul_le_mul_of_nonneg_left hd2 hsp
        _ = C ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by ring
  · -- `sig η θ * f θ * f'' θ`
    refine integrableOn_of_sin_rpow_bound (K := C ^ 2 * (Real.pi / 2)) (p := -η)
      (by positivity) hηm ?_ ?_
    · refine (hsigC.mul (hfC.mul hddfC)).congr ?_
      intro θ hθ
      simp only [Pi.mul_apply]
    · intro θ hθ
      have hs := sin_two_pos_Iθo hθ
      have hsp : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hs.le _
      have hfb : |f θ| ≤ C * (Real.pi / 2) := by
        have h1 := hb1 θ hθ
        have h2 : C * θ ≤ C * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_left (le_of_lt hθ.2) hC
        linarith
      have hff : |f θ * deriv (deriv f) θ| ≤ (C * (Real.pi / 2)) * C := by
        rw [abs_mul]
        exact mul_le_mul hfb (hb4 θ hθ) (abs_nonneg _) (mul_nonneg hC (by positivity))
      calc |sig η θ * (f θ * deriv (deriv f) θ)|
          = (Real.sin (2 * θ)) ^ (-η) * |f θ * deriv (deriv f) θ| := by
            simp only [sig, abs_mul, abs_of_nonneg hsp]
        _ ≤ (Real.sin (2 * θ)) ^ (-η) * ((C * (Real.pi / 2)) * C) :=
            mul_le_mul_of_nonneg_left hff hsp
        _ = C ^ 2 * (Real.pi / 2) * (Real.sin (2 * θ)) ^ (-η) := by ring
  · -- `sigD η θ * f θ * f' θ`
    refine integrableOn_of_sin_rpow_bound (K := 2 * η * C ^ 2 * (Real.pi / 4)) (p := -η)
      (by positivity) hηm ?_ ?_
    · refine (hsigDC.mul (hfC.mul hdfC)).congr ?_
      intro θ hθ
      simp only [Pi.mul_apply]
    · intro θ hθ
      have hs := sin_two_pos_Iθo hθ
      have hsp1 : 0 ≤ (Real.sin (2 * θ)) ^ (-η - 1) := Real.rpow_nonneg hs.le _
      have hcf : 0 ≤ C * (Real.pi / 4) * Real.sin (2 * θ) :=
        mul_nonneg (mul_nonneg hC (by positivity)) hs.le
      have hf2 : |f θ| ≤ C * (Real.pi / 4) * Real.sin (2 * θ) := hfπ θ hθ
      have hff : |f θ * deriv f θ| ≤ (C * (Real.pi / 4) * Real.sin (2 * θ)) * C := by
        rw [abs_mul]
        exact mul_le_mul hf2 (hb3 θ hθ) (abs_nonneg _) hcf
      have h1 : |sigD η θ| ≤ 2 * η * (Real.sin (2 * θ)) ^ (-η - 1) := by
        have hcos : |Real.cos (2 * θ)| ≤ 1 :=
          abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
        calc |sigD η θ| = (2 * η) * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-η - 1) := by
              simp only [sigD, abs_mul, abs_of_nonneg hsp1, abs_neg,
                abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hη0]
          _ ≤ (2 * η) * 1 * (Real.sin (2 * θ)) ^ (-η - 1) := by
              refine mul_le_mul_of_nonneg_right ?_ hsp1
              exact mul_le_mul_of_nonneg_left hcos (by linarith)
          _ = 2 * η * (Real.sin (2 * θ)) ^ (-η - 1) := by ring
      have h3 : 0 ≤ 2 * η * (Real.sin (2 * θ)) ^ (-η - 1) := mul_nonneg (by linarith) hsp1
      calc |sigD η θ * (f θ * deriv f θ)| = |sigD η θ| * |f θ * deriv f θ| := abs_mul _ _
        _ ≤ (2 * η * (Real.sin (2 * θ)) ^ (-η - 1))
              * ((C * (Real.pi / 4) * Real.sin (2 * θ)) * C) :=
            mul_le_mul h1 hff (abs_nonneg _) h3
        _ = 2 * η * C ^ 2 * (Real.pi / 4)
              * ((Real.sin (2 * θ)) ^ (-η - 1) * Real.sin (2 * θ)) := by ring
        _ = 2 * η * C ^ 2 * (Real.pi / 4) * (Real.sin (2 * θ)) ^ (-η) := by
            rw [rpow_neg_sub_one_mul hs]
  · -- `rho η θ * f θ * f' θ`
    refine integrableOn_of_sin_rpow_bound (K := C ^ 2 * (Real.pi / 4)) (p := -η)
      (by positivity) hηm ?_ ?_
    · refine ((hrhoC.mul hfC).mul hdfC).congr ?_
      intro θ hθ
      simp only [Pi.mul_apply]
    · intro θ hθ
      have hs := sin_two_pos_Iθo hθ
      have hsp1 : 0 ≤ (Real.sin (2 * θ)) ^ (-η - 1) := Real.rpow_nonneg hs.le _
      have hcf : 0 ≤ C * (Real.pi / 4) * Real.sin (2 * θ) :=
        mul_nonneg (mul_nonneg hC (by positivity)) hs.le
      have hf2 : |f θ| ≤ C * (Real.pi / 4) * Real.sin (2 * θ) := hfπ θ hθ
      have hff : |f θ| * |deriv f θ| ≤ (C * (Real.pi / 4) * Real.sin (2 * θ)) * C :=
        mul_le_mul hf2 (hb3 θ hθ) (abs_nonneg _) hcf
      have h1 : |rho η θ| ≤ (Real.sin (2 * θ)) ^ (-η - 1) := by
        have hcos : |Real.cos (2 * θ)| ≤ 1 :=
          abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
        calc |rho η θ| = |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-η - 1) := by
              simp only [rho, abs_mul, abs_of_nonneg hsp1]
          _ ≤ 1 * (Real.sin (2 * θ)) ^ (-η - 1) := mul_le_mul_of_nonneg_right hcos hsp1
          _ = (Real.sin (2 * θ)) ^ (-η - 1) := one_mul _
      calc |rho η θ * f θ * deriv f θ| = |rho η θ| * |f θ| * |deriv f θ| := by
            rw [abs_mul, abs_mul]
        _ ≤ (Real.sin (2 * θ)) ^ (-η - 1) * (C * (Real.pi / 4) * Real.sin (2 * θ)) * C :=
            mul_le_mul (mul_le_mul h1 hf2 (abs_nonneg _) hsp1) (hb3 θ hθ) (abs_nonneg _)
              (mul_nonneg hsp1 hcf)
        _ = C ^ 2 * (Real.pi / 4)
              * ((Real.sin (2 * θ)) ^ (-η - 1) * Real.sin (2 * θ)) := by ring
        _ = C ^ 2 * (Real.pi / 4) * (Real.sin (2 * θ)) ^ (-η) := by
            rw [rpow_neg_sub_one_mul hs]
  · -- `rhoD η θ * (f θ)²`
    refine integrableOn_of_sin_rpow_bound
      (K := 2 * C ^ 2 * (Real.pi / 4) ^ 2 + 2 * (η + 1) * C ^ 2 * (Real.pi / 4) ^ 2)
      (p := -η)
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C)) (sq_nonneg _))
        (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg C)) (sq_nonneg _))) hηm ?_ ?_
    · refine (hrhoDC.mul (hfC.pow 2)).congr ?_
      intro θ hθ
      simp only [Pi.mul_apply, Pi.pow_apply]
    · intro θ hθ
      have hs := sin_two_pos_Iθo hθ
      have hspn : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hs.le _
      have hsp2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(2 + η)) := Real.rpow_nonneg hs.le _
      have hsq : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
        have h1 := Real.sin_le_one (2 * θ); nlinarith [hs.le]
      have hcos2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
        have h1 := Real.cos_le_one (2 * θ); have h2 := Real.neg_one_le_cos (2 * θ)
        nlinarith [sq_nonneg (Real.cos (2 * θ))]
      have hf2 : (f θ) ^ 2 ≤ C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (f θ)) (hfπ θ hθ) 2
        rw [sq_abs] at h
        calc (f θ) ^ 2 ≤ (C * (Real.pi / 4) * Real.sin (2 * θ)) ^ 2 := h
          _ = C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by ring
      have hrhoD : |rhoD η θ|
          ≤ 2 * (Real.sin (2 * θ)) ^ (-η)
            + 2 * (η + 1) * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
        have hT : 0 ≤ 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) :=
          mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hsp2
        have hneg : -2 * (Real.sin (2 * θ)) ^ (-η)
            - 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) ≤ 0 := by
          linarith
        rw [rhoD, abs_of_nonpos hneg]
        have hle : 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))
            ≤ 2 * (η + 1) * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
          have h := mul_le_mul_of_nonneg_right hcos2 hsp2
          calc 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))
              = (2 * (η + 1))
                * ((Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) := by ring
            _ ≤ (2 * (η + 1)) * (1 * (Real.sin (2 * θ)) ^ (-(2 + η))) :=
                mul_le_mul_of_nonneg_left h (by linarith)
            _ = 2 * (η + 1) * (Real.sin (2 * θ)) ^ (-(2 + η)) := by ring
        linarith
      calc |rhoD η θ * f θ ^ 2| = |rhoD η θ| * (f θ) ^ 2 := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ))]
        _ ≤ (2 * (Real.sin (2 * θ)) ^ (-η)
              + 2 * (η + 1) * (Real.sin (2 * θ)) ^ (-(2 + η)))
              * (C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ 2) := by
            refine mul_le_mul hrhoD hf2 (sq_nonneg _) ?_
            exact add_nonneg (mul_nonneg (by norm_num) hspn) (mul_nonneg (by linarith) hsp2)
        _ = 2 * (C ^ 2 * (Real.pi / 4) ^ 2)
              * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
            + 2 * (η + 1) * (C ^ 2 * (Real.pi / 4) ^ 2)
              * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) := by ring
        _ ≤ 2 * (C ^ 2 * (Real.pi / 4) ^ 2) * (Real.sin (2 * θ)) ^ (-η)
            + 2 * (η + 1) * (C ^ 2 * (Real.pi / 4) ^ 2) * (Real.sin (2 * θ)) ^ (-η) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hspn hsq) (by positivity)
            · rw [rpow_sq_mul_neg_two hs]
        _ = (2 * C ^ 2 * (Real.pi / 4) ^ 2 + 2 * (η + 1) * C ^ 2 * (Real.pi / 4) ^ 2)
              * (Real.sin (2 * θ)) ^ (-η) := by ring
  · -- `(f θ)² * sig η θ`
    refine integrableOn_of_sin_rpow_bound (K := C ^ 2 * (Real.pi / 4) ^ 2) (p := -η)
      (by positivity) hηm ?_ ?_
    · refine ((hfC.pow 2).mul hsigC).congr ?_
      intro θ hθ
      simp only [Pi.mul_apply, Pi.pow_apply]
    · intro θ hθ
      have hs := sin_two_pos_Iθo hθ
      have hspn : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hs.le _
      have hsq : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
        have h1 := Real.sin_le_one (2 * θ); nlinarith [hs.le]
      have hf2 : (f θ) ^ 2 ≤ C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (f θ)) (hfπ θ hθ) 2
        rw [sq_abs] at h
        calc (f θ) ^ 2 ≤ (C * (Real.pi / 4) * Real.sin (2 * θ)) ^ 2 := h
          _ = C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by ring
      have hCπ : 0 ≤ C ^ 2 * (Real.pi / 4) ^ 2 := mul_nonneg (sq_nonneg C) (sq_nonneg _)
      calc |f θ ^ 2 * sig η θ| = (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
            rw [sig, abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hspn]
        _ ≤ (C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ 2)
              * (Real.sin (2 * θ)) ^ (-η) := mul_le_mul_of_nonneg_right hf2 hspn
        _ = C ^ 2 * (Real.pi / 4) ^ 2
              * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by ring
        _ ≤ C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ (-η) :=
            mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hspn hsq) hCπ
  · -- `(f θ)² cos²(2θ) sin(2θ)^{-(2+η)}`
    refine integrableOn_of_sin_rpow_bound (K := C ^ 2 * (Real.pi / 4) ^ 2) (p := -η)
      (by positivity) hηm ?_ ?_
    · refine (((hfC.pow 2).mul (hcosC.pow 2)).mul (hsigp (-(2 + η)))).congr ?_
      intro θ hθ
      simp only [Pi.mul_apply, Pi.pow_apply]
    · intro θ hθ
      have hs := sin_two_pos_Iθo hθ
      have hsp2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(2 + η)) := Real.rpow_nonneg hs.le _
      have hcos2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
        have h1 := Real.cos_le_one (2 * θ); have h2 := Real.neg_one_le_cos (2 * θ)
        nlinarith [sq_nonneg (Real.cos (2 * θ))]
      have hf2 : (f θ) ^ 2 ≤ C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (f θ)) (hfπ θ hθ) 2
        rw [sq_abs] at h
        calc (f θ) ^ 2 ≤ (C * (Real.pi / 4) * Real.sin (2 * θ)) ^ 2 := h
          _ = C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by ring
      calc |f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))|
          = (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
              abs_of_nonneg (sq_nonneg (Real.cos (2 * θ))), abs_of_nonneg hsp2]
        _ ≤ (C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ 2) * 1
              * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
            have h1 : (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
                ≤ (C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ 2) * 1 :=
              mul_le_mul hf2 hcos2 (sq_nonneg _)
                (mul_nonneg (mul_nonneg (sq_nonneg C) (sq_nonneg _)) (sq_nonneg _))
            exact mul_le_mul_of_nonneg_right h1 hsp2
        _ = C ^ 2 * (Real.pi / 4) ^ 2
              * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) := by ring
        _ = C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
            rw [rpow_sq_mul_neg_two hs]

end Work.FTS.EllipticEst.Honest
