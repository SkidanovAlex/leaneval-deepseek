/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HonSliceIntegrable7`: the seven slice integrands of the `θ`-integration by parts

For an *honest* slice datum `f` (of class `C²` only on the *open* interval `(0, π/2)`, with no
smoothness or vanishing assumed at the endpoints), satisfying the two endpoint bounds
`|f θ| ≤ C θ`, `|f θ| ≤ C (π/2 - θ)` and the derivative bound `|f' θ| ≤ C`, and with the three
weighted-square integrability hypotheses `f²σ`, `(f')²σ`, `(f'')²σ` for `σ = sin(2θ)^{-η}`, we
prove that the seven integrands of the `θ`-integration by parts are integrable on
`Iθo = (0, π/2)`:

`sig η · (f')²`, `sig η · f · f''`, `sigD η · f · f'`, `rho η · f · f'`, `rhoD η · f²`,
`f² · sig η`, `f² cos²(2θ) sin(2θ)^{-(2+η)}`.

The mechanism is uniform.  The two endpoint bounds give `|f θ| ≤ C (π/4) sin (2θ)` by Jordan's
inequality, while `sigD η = -2η cos(2θ) sin(2θ)^{-η-1}` and `rho η = cos(2θ) sin(2θ)^{-η-1}`
lose one power of `sin (2θ)` to `|f|`, and `rhoD η`'s `sin(2θ)^{-(2+η)}` loses two powers to
`f²`; so every integrand is pointwise bounded by `K · sin (2θ)^{-η}`, which is integrable on
`Iθo` because `η < 1` (`TanTheta.integrableOn_sin_two_rpow_neg`).  The second term is the only
one in which the second derivative occurs undominated; there `2|f f''| ≤ f² + (f'')²` together
with the two integrability hypotheses for `f²σ` and `(f'')²σ` does the job.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.integrableOn_abs_mul_sigma
import Submission.Work.FTS.EllipticEst.Honest.SliceIbpDefs
import Submission.Work.FTS.EllipticEst.TanTheta.integrable_wrho_products

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the open interval `Iθo = (0, π/2)` -/

/-- `sin (2θ)` is positive on `Iθo`. -/
private lemma sin_two_pos_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Jordan's inequality on the two halves of `Iθo`: `min θ (π/2 - θ) ≤ (π/4) sin (2θ)`. -/
private lemma min_le_pi_div_four_sin_two {θ : ℝ} (hθ : θ ∈ Iθo) :
    min θ (Real.pi / 2 - θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases le_total θ (Real.pi / 4) with h | h
  · have hmin : min θ (Real.pi / 2 - θ) = θ := min_eq_left (by linarith)
    rw [hmin]
    have hj := Real.mul_le_sin (by linarith : (0 : ℝ) ≤ 2 * θ)
      (by linarith : 2 * θ ≤ Real.pi / 2)
    have he : 2 / Real.pi * (2 * θ) = 4 / Real.pi * θ := by ring
    rw [he] at hj
    have hmul := mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ) ≤ Real.pi / 4)
    have he2 : Real.pi / 4 * (4 / Real.pi * θ) = θ := by field_simp
    calc θ = Real.pi / 4 * (4 / Real.pi * θ) := he2.symm
      _ ≤ Real.pi / 4 * Real.sin (2 * θ) := hmul
  · have hmin : min θ (Real.pi / 2 - θ) = Real.pi / 2 - θ := min_eq_right (by linarith)
    rw [hmin]
    have hsin : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
      rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
    rw [hsin]
    have hj := Real.mul_le_sin (by linarith : (0 : ℝ) ≤ 2 * (Real.pi / 2 - θ))
      (by linarith : 2 * (Real.pi / 2 - θ) ≤ Real.pi / 2)
    have he : 2 / Real.pi * (2 * (Real.pi / 2 - θ)) = 4 / Real.pi * (Real.pi / 2 - θ) := by ring
    rw [he] at hj
    have hmul := mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ) ≤ Real.pi / 4)
    have he2 : Real.pi / 4 * (4 / Real.pi * (Real.pi / 2 - θ)) = Real.pi / 2 - θ := by field_simp
    calc Real.pi / 2 - θ = Real.pi / 4 * (4 / Real.pi * (Real.pi / 2 - θ)) := he2.symm
      _ ≤ Real.pi / 4 * Real.sin (2 * (Real.pi / 2 - θ)) := hmul

/-- The two endpoint bounds for `f` give `|f θ| ≤ (Cπ/4) sin (2θ)` on `Iθo`. -/
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

/-! ## Domination by the singular weight -/

/-- A function on `Iθo` dominated pointwise by `K · sin (2θ)^{-η}` with `η < 1` is integrable. -/
private lemma integrableOn_of_sig_bound {η : ℝ} (hη1 : η < 1) {u : ℝ → ℝ} {K : ℝ}
    (_hK : 0 ≤ K) (hu : ContinuousOn u Iθo)
    (h : ∀ θ ∈ Iθo, |u θ| ≤ K * (Real.sin (2 * θ)) ^ (-η)) :
    IntegrableOn u Iθo volume := by
  have hbase : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η)) (volume.restrict Iθo) :=
    TanTheta.integrableOn_sin_two_rpow_neg η hη1
  have hmaj : Integrable (fun θ : ℝ => K * (Real.sin (2 * θ)) ^ (-η)) (volume.restrict Iθo) :=
    hbase.const_mul K
  refine MeasureTheory.Integrable.mono' (f := u)
    (g := fun θ : ℝ => K * (Real.sin (2 * θ)) ^ (-η)) hmaj ?_ ?_
  · exact hu.aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs]
    exact h θ hθ

/-! ## The theorem -/

theorem HonSliceIntegrable7 (η C : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (hC0 : 0 ≤ C) :
    ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C * θ) →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C * (Real.pi / 2 - θ)) →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ C) →
      MeasureTheory.IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
          (fun θ => (Real.sin (2 * θ)) ^ (-η) * (deriv f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) ∧
        MeasureTheory.IntegrableOn
          (fun θ => (Real.sin (2 * θ)) ^ (-η) * (f θ * deriv (deriv f) θ))
          (Set.Ioo 0 (Real.pi / 2)) ∧
        MeasureTheory.IntegrableOn
          (fun θ => (-2 * η * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-η - 1))
            * (f θ * deriv f θ)) (Set.Ioo 0 (Real.pi / 2)) ∧
        MeasureTheory.IntegrableOn
          (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-η - 1) * f θ * deriv f θ)
          (Set.Ioo 0 (Real.pi / 2)) ∧
        MeasureTheory.IntegrableOn
          (fun θ => (-2 * (Real.sin (2 * θ)) ^ (-η)
            - 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
            * f θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) ∧
        MeasureTheory.IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
          (Set.Ioo 0 (Real.pi / 2)) ∧
        MeasureTheory.IntegrableOn
          (fun θ => f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
          (Set.Ioo 0 (Real.pi / 2)) := by
  intro f hf hb1 hb2 hb3 h5 h6 h7
  have hfC : ContinuousOn f Iθo := hf.continuousOn
  have hdfC : ContinuousOn (deriv f) Iθo :=
    (hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn
  have hddfC : ContinuousOn (deriv (deriv f)) Iθo :=
    (hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioo (by norm_num)
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
    fun θ hθ => abs_f_le hC0 hb1 hb2 hθ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `sig η θ * (f' θ)²`
    refine integrableOn_of_sig_bound hη1 (u := fun θ : ℝ => sig η θ * (deriv f θ) ^ 2)
      (K := C ^ 2) (sq_nonneg C) (hsigC.mul (hdfC.pow 2)) ?_
    intro θ hθ
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
  · -- `sig η θ * f θ * f'' θ`: the second derivative only occurs under the two weighted-square
    -- integrability hypotheses, so we use `2 |f f''| ≤ f² + (f'')²` against `habs`.
    have habs := integrableOn_abs_mul_sigma (s := Iθo) (p := f)
      (q := fun θ : ℝ => deriv (deriv f) θ)
      (σ := fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η))
      (fun θ hθ => Real.rpow_nonneg (sin_two_pos_Iθo hθ).le _) h5 h7
    refine MeasureTheory.Integrable.mono' habs ?_ ?_
    · exact (hsigC.aestronglyMeasurable measurableSet_Ioo).mul
        ((hfC.aestronglyMeasurable measurableSet_Ioo).mul
          (hddfC.aestronglyMeasurable measurableSet_Ioo))
    · filter_upwards with θ
      refine le_of_eq ?_
      rw [Real.norm_eq_abs,
        show (Real.sin (2 * θ)) ^ (-η) * (f θ * deriv (deriv f) θ)
            = f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-η) from by ring]
  · -- `sigD η θ * f θ * f' θ`
    refine integrableOn_of_sig_bound hη1
      (u := fun θ : ℝ => sigD η θ * (f θ * deriv f θ))
      (K := 2 * η * C ^ 2 * (Real.pi / 4))
      (by positivity) (hsigDC.mul (hfC.mul hdfC)) ?_
    intro θ hθ
    have hs := sin_two_pos_Iθo hθ
    have hsp1 : 0 ≤ (Real.sin (2 * θ)) ^ (-η - 1) := Real.rpow_nonneg hs.le _
    have hcf : 0 ≤ C * (Real.pi / 4) * Real.sin (2 * θ) :=
      mul_nonneg (mul_nonneg hC0 (by positivity)) hs.le
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
    refine integrableOn_of_sig_bound hη1
      (u := fun θ : ℝ => rho η θ * f θ * deriv f θ)
      (K := C ^ 2 * (Real.pi / 4)) (by positivity) ((hrhoC.mul hfC).mul hdfC) ?_
    intro θ hθ
    have hs := sin_two_pos_Iθo hθ
    have hsp1 : 0 ≤ (Real.sin (2 * θ)) ^ (-η - 1) := Real.rpow_nonneg hs.le _
    have hcf : 0 ≤ C * (Real.pi / 4) * Real.sin (2 * θ) :=
      mul_nonneg (mul_nonneg hC0 (by positivity)) hs.le
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
    refine integrableOn_of_sig_bound hη1 (u := fun θ : ℝ => rhoD η θ * f θ ^ 2)
      (K := 2 * C ^ 2 * (Real.pi / 4) ^ 2 + 2 * (η + 1) * C ^ 2 * (Real.pi / 4) ^ 2)
      (by positivity) (hrhoDC.mul (hfC.pow 2)) ?_
    intro θ hθ
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
  · -- `(f θ)² * sig η θ`: this is the first integrability hypothesis verbatim.
    simpa only [sig] using h5
  · -- `(f θ)² cos²(2θ) sin(2θ)^{-(2+η)}`
    refine integrableOn_of_sig_bound hη1
      (u := fun θ : ℝ => f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
      (K := C ^ 2 * (Real.pi / 4) ^ 2) (by positivity)
      (((hfC.pow 2).mul (hcosC.pow 2)).mul (hsigp (-(2 + η)))) ?_
    intro θ hθ
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
