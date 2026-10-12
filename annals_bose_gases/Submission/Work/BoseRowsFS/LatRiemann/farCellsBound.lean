import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsFS.LatRiemann.cellInvNormDevClean
import Submission.Work.BoseRowsFS.LatRiemann.farCellDevLipschitz
import Submission.Work.BoseRowsFS.LatRiemann.farCellPhiZvecSum
import Submission.Work.BoseRowsFS.LatRiemann.hboxSumMajorantLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseRowsFS.LatRiemann

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! elementary helpers -/

lemma zvec_zero : Work.BoseRowsFS.zvec (0 : Fin 3 → ℤ) = 0 := by
  ext i
  simp [Work.BoseRowsFS.zvec]

lemma latPt_zero (h : ℝ) : Work.BoseRowsFS.latPt h 0 = 0 := by
  rw [Work.BoseRowsFS.zvec_smul, zvec_zero, smul_zero]

private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)

private lemma integrableOn_hbox_bdd {h : ℝ} {m : Fin 3 → ℤ} {f : ℝ³ → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ p ∈ hbox h m, ‖f p‖ ≤ C) : IntegrableOn f (hbox h m) := by
  refine MeasureTheory.IntegrableOn.of_bound ?hfin hm.aestronglyMeasurable.restrict C ?hbd
  · rw [volume_hbox]
    exact ENNReal.pow_lt_top (n := 3) ENNReal.ofReal_lt_top
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_hbox h m)] with p hp
    exact hb p hp

theorem farCellsBound {h A B C4 : ℝ} (hh : 0 < h) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC4 : 0 ≤ C4)
    {Φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hcont : Continuous Φ)
    (hΦ : ∀ p, |Φ p| ≤ A / (1 + ‖p‖) ^ 4)
    (hlip : ∀ p q, |Φ p - Φ q| ≤ B * ‖p - q‖ * (1/(1+‖p‖)^2 + 1/(1+‖q‖)^2))
    (Kr : Finset (Fin 3 → ℤ))
    (hKr : ∀ m ∈ Kr, 2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖)
    (hC4b : ∀ S : Finset (Fin 3 → ℤ), (∀ m ∈ S, m ≠ 0) →
      ∑ m ∈ S, (‖Work.BoseRowsFS.zvec m‖ ^ 4)⁻¹ ≤ C4) :
    ∑ m ∈ Kr, |(∫ p in Work.BoseRowsFS.LatRiemann.hbox h m, Φ p / ‖p‖ ^ 2)
        - h ^ 3 * Φ (Work.BoseRowsFS.latPt h m) / ‖Work.BoseRowsFS.latPt h m‖ ^ 2|
      ≤ 200 * B * h + 16 * C4 * A * h := by
  have hPhiA_all : ∀ p : ℝ³, |Φ p| ≤ A := by
    intro p
    have h4 : ((1 + ‖p‖) ^ 4)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg p]))
    calc |Φ p| ≤ A / (1 + ‖p‖) ^ 4 := hΦ p
      _ = A * ((1 + ‖p‖) ^ 4)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left h4 hA
      _ = A := mul_one A
  -- the per-cell bound
  have hcell : ∀ m ∈ Kr,
      |(∫ p in hbox h m, Φ p / ‖p‖ ^ 2) - h ^ 3 * Φ (latPt h m) / ‖latPt h m‖ ^ 2|
        ≤ (5 * h * Real.sqrt 3 / 2) * B * (∫ p in hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
          + |Φ (latPt h m)| * (16 * h ^ 5 / ‖latPt h m‖ ^ 4) := by
    intro m hmKr
    have hfarL : 2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖ := hKr m hmKr
    set P : ℝ³ := Work.BoseRowsFS.latPt h m with hP
    have hfarP : 2 * Real.sqrt 3 * h ≤ ‖P‖ := by rw [hP]; exact hfarL
    have hsqrt3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hwpos : 0 < ‖P‖ := by nlinarith
    have hm0 : m ≠ 0 := by
      intro hmz
      have h0 : P = 0 := by
        rw [hP, hmz]; exact latPt_zero h
      rw [h0, norm_zero] at hfarP
      nlinarith
    -- geometry of the cell
    have hdel : ∀ p ∈ hbox h m, ‖p - P‖ ≤ ‖P‖ / 4 := by
      intro p hp
      have h1 : ‖p - Work.BoseRowsFS.latPt h m‖ ≤ h * Real.sqrt 3 / 2 := norm_sub_latPt_le hh hp
      have h2 : h * Real.sqrt 3 / 2 ≤ ‖P‖ / 4 := by
        have he : h * Real.sqrt 3 / 2 = (2 * Real.sqrt 3 * h) / 4 := by ring
        rw [he]
        linarith [hfarP]
      rw [hP]
      linarith
    have hpnorm : ∀ p ∈ hbox h m, 3 * ‖P‖ / 4 ≤ ‖p‖ := by
      intro p hp
      have h1 := abs_norm_sub_norm_le p P
      have h2 := hdel p hp
      have h3 := (abs_le.mp h1).1
      linarith
    have hppos : ∀ p ∈ hbox h m, 0 < ‖p‖ := by
      intro p hp
      have h := hpnorm p hp
      linarith
    have hpinv : ∀ p ∈ hbox h m, 1 / ‖p‖ ^ 2 ≤ 2 / ‖P‖ ^ 2 := by
      intro p hp
      have h1 := hpnorm p hp
      have h2 : (0 : ℝ) < ‖P‖ ^ 2 := pow_pos hwpos 2
      have h3 : (0 : ℝ) < ‖p‖ ^ 2 := pow_pos (hppos p hp) 2
      rw [div_le_div_iff₀ h3 h2]
      nlinarith [norm_nonneg p, h1]
    have hPinv_pos : (0 : ℝ) < 1 / ‖P‖ ^ 2 := one_div_pos.mpr (pow_pos hwpos 2)
    -- integrability of the pieces on the cell
    have hintF : IntegrableOn (fun p : ℝ³ => Φ p / ‖p‖ ^ 2) (hbox h m) := by
      refine integrableOn_hbox_bdd (C := 2 * A / ‖P‖ ^ 2) (by fun_prop) ?_
      intro p hp
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (hppos p hp) 2)]
      calc |Φ p| / ‖p‖ ^ 2 ≤ A / ‖p‖ ^ 2 :=
            div_le_div_of_nonneg_right (hPhiA_all p) (by positivity)
        _ = A * (1 / ‖p‖ ^ 2) := by ring
        _ ≤ A * (2 / ‖P‖ ^ 2) := mul_le_mul_of_nonneg_left (hpinv p hp) hA
        _ = 2 * A / ‖P‖ ^ 2 := by ring
    have hintConst : IntegrableOn (fun p : ℝ³ => Φ P / ‖P‖ ^ 2) (hbox h m) := by
      refine integrableOn_hbox_bdd (C := A / ‖P‖ ^ 2) measurable_const ?_
      intro p hp
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖P‖ ^ 2)]
      exact div_le_div_of_nonneg_right (hPhiA_all P) (by positivity)
    have hintG : IntegrableOn (fun p : ℝ³ => (Φ p - Φ P) / ‖p‖ ^ 2) (hbox h m) := by
      refine integrableOn_hbox_bdd (C := 4 * A / ‖P‖ ^ 2) (by fun_prop) ?_
      intro p hp
      have h2A : |Φ p - Φ P| ≤ 2 * A := by
        have h1 := hPhiA_all p
        have h3 := hPhiA_all P
        calc |Φ p - Φ P| ≤ |Φ p| + |Φ P| := abs_sub_le_abs_add _ _
          _ ≤ A + A := add_le_add h1 h3
          _ = 2 * A := by ring
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (hppos p hp) 2)]
      calc |Φ p - Φ P| / ‖p‖ ^ 2 ≤ (2 * A) / ‖p‖ ^ 2 :=
            div_le_div_of_nonneg_right h2A (by positivity)
        _ = (2 * A) * (1 / ‖p‖ ^ 2) := by ring
        _ ≤ (2 * A) * (2 / ‖P‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hpinv p hp) (by linarith)
        _ = 4 * A / ‖P‖ ^ 2 := by ring
    have hintCH : IntegrableOn (fun p : ℝ³ => Φ P * (1 / ‖p‖ ^ 2 - 1 / ‖P‖ ^ 2)) (hbox h m) := by
      refine integrableOn_hbox_bdd (C := 4 * A / ‖P‖ ^ 2) (by fun_prop) ?_
      intro p hp
      have h1 : 1 / ‖p‖ ^ 2 ≤ 2 / ‖P‖ ^ 2 := hpinv p hp
      have hz : 1 / ‖P‖ ^ 2 ≤ 2 / ‖P‖ ^ 2 :=
        div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt (pow_pos hwpos 2))
      have h3 : |1 / ‖p‖ ^ 2 - 1 / ‖P‖ ^ 2| ≤ 1 / ‖p‖ ^ 2 + 1 / ‖P‖ ^ 2 := by
        have hh3 := abs_sub_le_abs_add (1 / ‖p‖ ^ 2) (1 / ‖P‖ ^ 2)
        rwa [abs_of_pos (one_div_pos.mpr (pow_pos (hppos p hp) 2)), abs_of_pos hPinv_pos] at hh3
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : |Φ P| ≤ A := hPhiA_all P
      calc |Φ P| * |1 / ‖p‖ ^ 2 - 1 / ‖P‖ ^ 2|
          ≤ A * (1 / ‖p‖ ^ 2 + 1 / ‖P‖ ^ 2) :=
            mul_le_mul h2 h3 (abs_nonneg _) hA
        _ ≤ A * (2 / ‖P‖ ^ 2 + 2 / ‖P‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (add_le_add h1 hz) hA
        _ = 4 * A / ‖P‖ ^ 2 := by ring
    -- pointwise splitting identity
    have hpt : ∀ p ∈ hbox h m, Φ p / ‖p‖ ^ 2 - Φ P / ‖P‖ ^ 2
        = (Φ p - Φ P) / ‖p‖ ^ 2 + Φ P * (1 / ‖p‖ ^ 2 - 1 / ‖P‖ ^ 2) := by
      intro p hp
      have hp0 : ‖p‖ ≠ 0 := ne_of_gt (hppos p hp)
      have hP0 : ‖P‖ ≠ 0 := ne_of_gt hwpos
      field_simp
      ring
    have hconst : (∫ p in hbox h m, Φ P / ‖P‖ ^ 2) = h ^ 3 * Φ P / ‖P‖ ^ 2 := by
      rw [MeasureTheory.setIntegral_const, real_volume_hbox (le_of_lt hh) m, smul_eq_mul]
      ring
    have hsplit : (∫ p in hbox h m, Φ p / ‖p‖ ^ 2) - h ^ 3 * Φ P / ‖P‖ ^ 2
        = (∫ p in hbox h m, (Φ p - Φ P) / ‖p‖ ^ 2)
          + Φ P * (∫ p in hbox h m, (1 / ‖p‖ ^ 2 - 1 / ‖P‖ ^ 2)) := by
      rw [← hconst, ← MeasureTheory.integral_sub hintF hintConst]
      rw [MeasureTheory.setIntegral_congr_fun (measurableSet_hbox h m)
        (fun p hp => hpt p hp)]
      rw [MeasureTheory.integral_add hintG hintCH, MeasureTheory.integral_const_mul]
    have hGbound : ‖∫ p in hbox h m, (Φ p - Φ P) / ‖p‖ ^ 2‖
        ≤ (5 * h * Real.sqrt 3 / 2) * B
          * (∫ p in hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2)) :=
      by simpa [hP] using farCellDevLipschitz hh hB hlip hm0 hfarL
    have hHbound : |∫ p in hbox h m, (1 / ‖p‖ ^ 2 - 1 / ‖P‖ ^ 2)|
        ≤ 16 * h ^ 5 / ‖P‖ ^ 4 :=
      by simpa [hP] using cellInvNormDevClean hh m hfarL
    calc |(∫ p in hbox h m, Φ p / ‖p‖ ^ 2) - h ^ 3 * Φ P / ‖P‖ ^ 2|
        = |(∫ p in hbox h m, (Φ p - Φ P) / ‖p‖ ^ 2)
            + Φ P * (∫ p in hbox h m, (1 / ‖p‖ ^ 2 - 1 / ‖P‖ ^ 2))| := by rw [hsplit]
      _ ≤ |∫ p in hbox h m, (Φ p - Φ P) / ‖p‖ ^ 2|
            + |Φ P * (∫ p in hbox h m, (1 / ‖p‖ ^ 2 - 1 / ‖P‖ ^ 2))| := abs_add_le _ _
      _ = ‖∫ p in hbox h m, (Φ p - Φ P) / ‖p‖ ^ 2‖
            + |Φ P| * |∫ p in hbox h m, (1 / ‖p‖ ^ 2 - 1 / ‖P‖ ^ 2)| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ (5 * h * Real.sqrt 3 / 2) * B
            * (∫ p in hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
          + |Φ P| * (16 * h ^ 5 / ‖P‖ ^ 4) :=
            add_le_add hGbound (mul_le_mul_of_nonneg_left hHbound (abs_nonneg _))
  -- summation
  have hstep1 : ∑ m ∈ Kr, |(∫ p in hbox h m, Φ p / ‖p‖ ^ 2)
        - h ^ 3 * Φ (latPt h m) / ‖latPt h m‖ ^ 2|
      ≤ ∑ m ∈ Kr, ((5 * h * Real.sqrt 3 / 2) * B
            * (∫ p in hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
          + |Φ (latPt h m)| * (16 * h ^ 5 / ‖latPt h m‖ ^ 4)) :=
    Finset.sum_le_sum (fun m hm => hcell m hm)
  have hstep2 : ∑ m ∈ Kr, ((5 * h * Real.sqrt 3 / 2) * B
            * (∫ p in hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
          + |Φ (latPt h m)| * (16 * h ^ 5 / ‖latPt h m‖ ^ 4))
      = (5 * h * Real.sqrt 3 / 2) * B
          * (∑ m ∈ Kr, ∫ p in hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
        + ∑ m ∈ Kr, |Φ (latPt h m)| * (16 * h ^ 5 / ‖latPt h m‖ ^ 4) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hstep3 : (5 * h * Real.sqrt 3 / 2) * B
        * (∑ m ∈ Kr, ∫ p in hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
      ≤ (5 * h * Real.sqrt 3 / 2) * B * (4 * Real.pi) :=
    mul_le_mul_of_nonneg_left (hboxSumMajorantLe hh Kr) (by positivity)
  have hstep4 : (5 * h * Real.sqrt 3 / 2) * B * (4 * Real.pi) ≤ 200 * B * h := by
    have h3 : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    have hkey : 10 * Real.sqrt 3 * Real.pi ≤ 200 := by
      have h1 : Real.sqrt 3 * Real.pi ≤ 2 * 4 :=
        mul_le_mul h3 Real.pi_le_four (le_of_lt Real.pi_pos) (by norm_num)
      linarith
    have hBh : (0 : ℝ) ≤ B * h := mul_nonneg hB (le_of_lt hh)
    have hrhs : (5 * h * Real.sqrt 3 / 2) * B * (4 * Real.pi)
        = (10 * Real.sqrt 3 * Real.pi) * (B * h) := by ring
    rw [hrhs]
    calc (10 * Real.sqrt 3 * Real.pi) * (B * h) ≤ 200 * (B * h) :=
          mul_le_mul_of_nonneg_right hkey hBh
      _ = 200 * B * h := by ring
  calc ∑ m ∈ Kr, |(∫ p in hbox h m, Φ p / ‖p‖ ^ 2)
          - h ^ 3 * Φ (latPt h m) / ‖latPt h m‖ ^ 2|
      ≤ ∑ m ∈ Kr, ((5 * h * Real.sqrt 3 / 2) * B
            * (∫ p in hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
          + |Φ (latPt h m)| * (16 * h ^ 5 / ‖latPt h m‖ ^ 4)) := hstep1
    _ = (5 * h * Real.sqrt 3 / 2) * B
          * (∑ m ∈ Kr, ∫ p in hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
        + ∑ m ∈ Kr, |Φ (latPt h m)| * (16 * h ^ 5 / ‖latPt h m‖ ^ 4) := hstep2
    _ ≤ (5 * h * Real.sqrt 3 / 2) * B * (4 * Real.pi) + 16 * C4 * A * h :=
        add_le_add hstep3 (farCellPhiZvecSum hh hA hC4 hΦ Kr hKr hC4b)
    _ ≤ 200 * B * h + 16 * C4 * A * h := add_le_add hstep4 (le_refl _)

end Work.BoseRowsFS.LatRiemann
