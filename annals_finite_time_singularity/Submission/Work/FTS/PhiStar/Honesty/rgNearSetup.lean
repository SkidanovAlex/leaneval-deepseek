/-
Development of the assembly of `radGreen_near_limits_of_le_rpow`, against the (sorry'd) statements
of the six delegated lemmas. Not on the solution path.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.rgA_value_bound
import Submission.Work.FTS.PhiStar.Honesty.rgA_step_claim
import Submission.Work.FTS.PhiStar.Honesty.rgB_value_bound
import Submission.Work.FTS.PhiStar.Honesty.rgB_step_claim
import Submission.Work.FTS.PhiStar.Honesty.rpow_neg_sub_le
import Submission.Work.FTS.PhiStar.Honesty.rpow_pos_sub_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist

set_option autoImplicit false

lemma eventually_rpow_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ z : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), z ^ a ≤ c := by
  have hlim : Tendsto (fun z : ℝ => z ^ a) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
    have h0 : ContinuousAt (fun z : ℝ => z ^ a) (0 : ℝ) :=
      Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)
    have h1 : Tendsto (fun z : ℝ => z ^ a) (nhds (0 : ℝ)) (nhds ((0 : ℝ) ^ a)) := h0.tendsto
    rw [Real.zero_rpow (ne_of_gt ha)] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have h2 : ∀ᶠ z : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), dist (z ^ a) (0 : ℝ) < c :=
    (Metric.nhds_basis_ball.tendsto_right_iff).mp hlim c hc
  filter_upwards [h2, self_mem_nhdsWithin] with z hz hzmem
  have hz0 : 0 < z := hzmem
  have hnn : 0 ≤ z ^ a := Real.rpow_nonneg hz0.le a
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hz
  linarith

/-- The constant multiplying `z^{3/2}` in the value bound for `radGreen`. -/
def rgS (α : ℝ) (m : ℕ) : ℝ :=
  1 / (rgQ α m + 3 / 2) + 1 / (rgP α m - 3 / 2)

/-- The far-field constant of the tail bound. -/
def rgCF (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
    + (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
    + δ ^ (-(2 * rgP α m + 1)) + 1

/-- The constant multiplying `ε * z^{1/2}` in the derivative bound. -/
def rgA1 (α : ℝ) (m : ℕ) : ℝ :=
  rgK α m * (rgQ α m * 2 ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2)
    + 2 ^ (rgQ α m + 1 / 2) + rgP α m * 2 ^ (rgP α m - 1) / (rgP α m - 3 / 2) + 1)

/-- The constant multiplying `rgCF * z^{p-1}` in the derivative bound. -/
def rgA2 (α : ℝ) (m : ℕ) : ℝ := rgK α m * (rgP α m * 2 ^ (rgP α m - 1))

lemma rgCF_nonneg {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ rgCF α m c δ := by
  rw [rgCF]
  have h1 : (0 : ℝ) ≤ ∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4 :=
    integral_nonneg_of_ae (ae_of_all _ fun x => div_nonneg (sq_nonneg _) (by positivity))
  have h2 : (0 : ℝ) ≤ ∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2 :=
    integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg _)
  have h3 : (0 : ℝ) ≤ δ ^ (-(2 * rgP α m + 1)) := Real.rpow_nonneg hδ.le _
  linarith

lemma rgS_pos {α : ℝ} {m : ℕ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) :
    0 < rgS α m := by
  rw [rgS]
  have hq : 0 < rgQ α m := rgQ_pos hα m
  have hp : (3 : ℝ) / 2 < rgP α m := by have := rgP_ge hα hα4 hm; linarith
  have h1 : 0 < 1 / (rgQ α m + 3 / 2) := by positivity
  have h2 : 0 < 1 / (rgP α m - 3 / 2) := by positivity
  linarith

lemma radGreen_value_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → 2 * z ≤ δ →
      ‖Work.FTS.PhiStar.Radial.radGreen α m c z‖
        ≤ rgK α m * (ε * rgS α m * z ^ ((3 : ℝ) / 2) + rgCF α m c δ * z ^ (rgP α m)) := by
  intro z hz0 h2z
  have hq : 0 < rgQ α m := rgQ_pos hα m
  have hp : 0 < rgP α m := rgP_pos hα hm
  have hK : 0 < rgK α m := rgK_pos hα m
  have hzδ : z ≤ δ := by linarith
  have hz1 : z ≤ 1 := le_trans hzδ hδ1
  have hA := rgA_value_bound (α := α) (m := m) (c := c) hα hδ hε hvy z hz0 hzδ
  have hB := rgB_value_bound (α := α) (m := m) (c := c) hα hα4 hm hδ hδ1 hε hvy hnear hfar
    z hz0 hz1
  have hB' : |rgB α m c z| ≤ ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2) + rgCF α m c δ := by
    unfold rgCF at *
    linarith [hB]
  rw [Work.FTS.EllExist.radGreen_eq]
  have hznq : (0 : ℝ) < z ^ (-(rgQ α m)) := Real.rpow_pos_of_pos hz0 _
  have hzp : (0 : ℝ) < z ^ (rgP α m) := Real.rpow_pos_of_pos hz0 _
  have hsq : (0 : ℝ) < rgQ α m + 3 / 2 := by linarith
  have hsp : (0 : ℝ) < rgP α m - 3 / 2 := by
    have := rgP_ge hα hα4 hm
    linarith
  have hzq : z ^ (-(rgQ α m)) * z ^ (rgQ α m + 3 / 2) = z ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_add hz0]
    congr 1
    ring
  have hzp' : z ^ (rgP α m) * z ^ (3 / 2 - rgP α m) = z ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_add hz0]
    congr 1
    ring
  calc ‖rgK α m * (z ^ (-(rgQ α m)) * rgA α m c z + z ^ (rgP α m) * rgB α m c z)‖
      = rgK α m * ‖z ^ (-(rgQ α m)) * rgA α m c z + z ^ (rgP α m) * rgB α m c z‖ := by
        simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hK]
    _ ≤ rgK α m * (z ^ (-(rgQ α m)) * |rgA α m c z| + z ^ (rgP α m) * |rgB α m c z|) := by
        refine mul_le_mul_of_nonneg_left ?_ hK.le
        calc ‖z ^ (-(rgQ α m)) * rgA α m c z + z ^ (rgP α m) * rgB α m c z‖
            ≤ ‖z ^ (-(rgQ α m)) * rgA α m c z‖ + ‖z ^ (rgP α m) * rgB α m c z‖ :=
              norm_add_le _ _
          _ = z ^ (-(rgQ α m)) * |rgA α m c z| + z ^ (rgP α m) * |rgB α m c z| := by
              rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hznq,
                abs_of_pos hzp]
    _ ≤ rgK α m * (z ^ (-(rgQ α m)) * (ε * z ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2))
          + z ^ (rgP α m) * (ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2)
              + rgCF α m c δ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK.le
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hA hznq.le
        · exact mul_le_mul_of_nonneg_left hB' hzp.le
    _ = rgK α m * (ε * rgS α m * z ^ ((3 : ℝ) / 2) + rgCF α m c δ * z ^ (rgP α m)) := by
        congr 1
        rw [rgS]
        rw [show z ^ (-(rgQ α m)) * (ε * z ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2))
              + z ^ (rgP α m) * (ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2)
                  + rgCF α m c δ)
            = ε * (z ^ (-(rgQ α m)) * z ^ (rgQ α m + 3 / 2)) / (rgQ α m + 3 / 2)
              + ε * (z ^ (rgP α m) * z ^ (3 / 2 - rgP α m)) / (rgP α m - 3 / 2)
              + rgCF α m c δ * z ^ (rgP α m) from by ring]
        rw [hzq, hzp']
        ring

private lemma rgA_slot_step {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2))
    {z cA h : ℝ} (hz : 0 < z) (hh : 0 < h) (hhz : h ≤ z) (hhδ : z + h ≤ δ)
    (hcA : |cA| ≤ ε * z ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2))
    (hstep : |rgA α m c (z + h) - cA| ≤ h * (ε * (2 * z) ^ (rgQ α m + 1 / 2))) :
    |(z + h) ^ (-(rgQ α m)) * rgA α m c (z + h) - z ^ (-(rgQ α m)) * cA|
      ≤ ε * h * z ^ ((1 : ℝ) / 2)
        * (rgQ α m * 2 ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2) + 2 ^ (rgQ α m + 1 / 2)) := by
  have hq : 0 < rgQ α m := rgQ_pos hα m
  have hzh : 0 < z + h := by linarith
  have hexp1 : (0 : ℝ) ≤ rgQ α m + 3 / 2 := by linarith
  have hexp2 : (0 : ℝ) ≤ rgQ α m + 1 / 2 := by linarith
  have hd := rpow_neg_sub_le (q := rgQ α m) hq hz hh hhz
  have hAh := rgA_value_bound (α := α) (m := m) (c := c) hα hδ hε hvy (z + h) hzh hhδ
  have hge : (z + h) ^ (rgQ α m + 3 / 2) ≤ (2 * z) ^ (rgQ α m + 3 / 2) :=
    Real.rpow_le_rpow (by linarith) (by linarith) hexp1
  have hA2 : |rgA α m c (z + h)| ≤ ε * (2 * z) ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2) := by
    refine le_trans hAh (div_le_div_of_nonneg_right ?_ (by linarith))
    exact mul_le_mul_of_nonneg_left hge hε
  -- the two isolated rpow identities
  have key1 : z ^ (-(rgQ α m) - 1) * (2 * z) ^ (rgQ α m + 3 / 2)
      = 2 ^ (rgQ α m + 3 / 2) * z ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hz.le]
    rw [show z ^ (-(rgQ α m) - 1) * (2 ^ (rgQ α m + 3 / 2) * z ^ (rgQ α m + 3 / 2))
          = 2 ^ (rgQ α m + 3 / 2) * (z ^ (-(rgQ α m) - 1) * z ^ (rgQ α m + 3 / 2))
          from by ring]
    rw [show z ^ (-(rgQ α m) - 1) * z ^ (rgQ α m + 3 / 2)
          = z ^ ((-(rgQ α m) - 1) + (rgQ α m + 3 / 2))
          from (Real.rpow_add hz (-(rgQ α m) - 1) (rgQ α m + 3 / 2)).symm]
    rw [show (-(rgQ α m) - 1) + (rgQ α m + 3 / 2) = ((1 : ℝ) / 2) from by ring]
  have key2 : z ^ (-(rgQ α m)) * (2 * z) ^ (rgQ α m + 1 / 2)
      = 2 ^ (rgQ α m + 1 / 2) * z ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hz.le]
    rw [show z ^ (-(rgQ α m)) * (2 ^ (rgQ α m + 1 / 2) * z ^ (rgQ α m + 1 / 2))
          = 2 ^ (rgQ α m + 1 / 2) * (z ^ (-(rgQ α m)) * z ^ (rgQ α m + 1 / 2))
          from by ring]
    rw [show z ^ (-(rgQ α m)) * z ^ (rgQ α m + 1 / 2)
          = z ^ ((-(rgQ α m)) + (rgQ α m + 1 / 2))
          from (Real.rpow_add hz (-(rgQ α m)) (rgQ α m + 1 / 2)).symm]
    rw [show (-(rgQ α m)) + (rgQ α m + 1 / 2) = ((1 : ℝ) / 2) from by ring]
  have hT1 : |(z + h) ^ (-(rgQ α m)) - z ^ (-(rgQ α m))| * |rgA α m c (z + h)|
      ≤ (rgQ α m * z ^ (-(rgQ α m) - 1) * h)
          * (ε * (2 * z) ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2)) := by
    have hb : (0 : ℝ) ≤ rgQ α m * z ^ (-(rgQ α m) - 1) * h := by
      have h1 : (0 : ℝ) < z ^ (-(rgQ α m) - 1) := Real.rpow_pos_of_pos hz _
      have h2 : (0 : ℝ) < rgQ α m * z ^ (-(rgQ α m) - 1) := mul_pos hq h1
      exact mul_nonneg h2.le hh.le
    have hc : (0 : ℝ) ≤ ε * (2 * z) ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2) := by
      refine div_nonneg ?_ (by linarith)
      exact mul_nonneg hε (Real.rpow_nonneg (by positivity) _)
    exact mul_le_mul hd hA2 (abs_nonneg _) hb
  have hT2 : z ^ (-(rgQ α m)) * |rgA α m c (z + h) - cA|
      ≤ z ^ (-(rgQ α m)) * (h * (ε * (2 * z) ^ (rgQ α m + 1 / 2))) :=
    mul_le_mul_of_nonneg_left hstep (Real.rpow_pos_of_pos hz _).le
  have h1 : (rgQ α m * z ^ (-(rgQ α m) - 1) * h)
        * (ε * (2 * z) ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2))
      = ε * h * (rgQ α m * 2 ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2)) * z ^ ((1 : ℝ) / 2) := by
    rw [show (rgQ α m * z ^ (-(rgQ α m) - 1) * h)
          * (ε * (2 * z) ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2))
        = rgQ α m * h * (ε / (rgQ α m + 3 / 2))
          * (z ^ (-(rgQ α m) - 1) * (2 * z) ^ (rgQ α m + 3 / 2)) from by ring]
    rw [key1]
    ring
  have h2 : z ^ (-(rgQ α m)) * (h * (ε * (2 * z) ^ (rgQ α m + 1 / 2)))
      = ε * h * 2 ^ (rgQ α m + 1 / 2) * z ^ ((1 : ℝ) / 2) := by
    rw [show z ^ (-(rgQ α m)) * (h * (ε * (2 * z) ^ (rgQ α m + 1 / 2)))
        = h * ε * (z ^ (-(rgQ α m)) * (2 * z) ^ (rgQ α m + 1 / 2)) from by ring]
    rw [key2]
    ring
  calc |(z + h) ^ (-(rgQ α m)) * rgA α m c (z + h) - z ^ (-(rgQ α m)) * cA|
      = |((z + h) ^ (-(rgQ α m)) - z ^ (-(rgQ α m))) * rgA α m c (z + h)
          + z ^ (-(rgQ α m)) * (rgA α m c (z + h) - cA)| := by ring_nf
    _ ≤ |((z + h) ^ (-(rgQ α m)) - z ^ (-(rgQ α m))) * rgA α m c (z + h)|
          + |z ^ (-(rgQ α m)) * (rgA α m c (z + h) - cA)| := abs_add_le _ _
    _ = |(z + h) ^ (-(rgQ α m)) - z ^ (-(rgQ α m))| * |rgA α m c (z + h)|
          + z ^ (-(rgQ α m)) * |rgA α m c (z + h) - cA| := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz _)]
    _ ≤ (rgQ α m * z ^ (-(rgQ α m) - 1) * h)
          * (ε * (2 * z) ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2))
          + z ^ (-(rgQ α m)) * (h * (ε * (2 * z) ^ (rgQ α m + 1 / 2))) :=
        add_le_add hT1 hT2
    _ = ε * h * z ^ ((1 : ℝ) / 2)
        * (rgQ α m * 2 ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2) + 2 ^ (rgQ α m + 1 / 2)) := by
        rw [h1, h2]
        ring


private lemma rgB_slot_step {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    {z cB h : ℝ} (hz : 0 < z) (hh : 0 < h) (hhz : h ≤ z) (hhδ : z + h ≤ δ)
    (hzh1 : z + h ≤ 1)
    (hcB : |cB| ≤ ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2) + rgCF α m c δ)
    (hstep : |rgB α m c (z + h) - cB| ≤ h * (ε * z ^ (1 / 2 - rgP α m))) :
    |(z + h) ^ (rgP α m) * rgB α m c (z + h) - z ^ (rgP α m) * cB|
      ≤ h * (ε * z ^ ((1 : ℝ) / 2) * (rgP α m * 2 ^ (rgP α m - 1) / (rgP α m - 3 / 2) + 1)
          + (rgCF α m c δ * (rgP α m * 2 ^ (rgP α m - 1))) * z ^ (rgP α m - 1)) := by
  have hp : 0 < rgP α m := rgP_pos hα hm
  have hp32 : (3 : ℝ) / 2 < rgP α m := by have := rgP_ge hα hα4 hm; linarith
  have hp1 : (1 : ℝ) ≤ rgP α m := by linarith
  have hp0 : (0 : ℝ) ≤ rgP α m - 1 := by linarith
  have hzh : 0 < z + h := by linarith
  have hcfg : 0 ≤ rgCF α m c δ := rgCF_nonneg hδ
  have hd := rpow_pos_sub_le (p := rgP α m) hp1 hz hh hhz
  have hBv := rgB_value_bound (α := α) (m := m) (c := c) hα hα4 hm hδ hδ1 hε hvy hnear hfar
    (z + h) hzh hzh1
  have hge : (z + h) ^ (3 / 2 - rgP α m) ≤ z ^ (3 / 2 - rgP α m) :=
    Real.rpow_le_rpow_of_nonpos hz (by linarith) (by linarith)
  have hB2 : |rgB α m c (z + h)| ≤ ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2)
      + rgCF α m c δ := by
    unfold rgCF at *
    refine le_trans hBv ?_
    have h1 : ε * (z + h) ^ (3 / 2 - rgP α m) ≤ ε * z ^ (3 / 2 - rgP α m) :=
      mul_le_mul_of_nonneg_left hge hε
    have h2 : (0 : ℝ) < rgP α m - 3 / 2 := by linarith
    have h3 : ε * (z + h) ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2)
        ≤ ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2) :=
      div_le_div_of_nonneg_right h1 h2.le
    linarith
  have keyB1 : (2 * z) ^ (rgP α m - 1) = 2 ^ (rgP α m - 1) * z ^ (rgP α m - 1) :=
    Real.mul_rpow (by norm_num) hz.le
  have keyB2 : z ^ (rgP α m - 1) * z ^ (3 / 2 - rgP α m) = z ^ ((1 : ℝ) / 2) := by
    rw [show z ^ (rgP α m - 1) * z ^ (3 / 2 - rgP α m)
          = z ^ ((rgP α m - 1) + (3 / 2 - rgP α m))
          from (Real.rpow_add hz (rgP α m - 1) (3 / 2 - rgP α m)).symm]
    rw [show (rgP α m - 1) + (3 / 2 - rgP α m) = ((1 : ℝ) / 2) from by ring]
  have keyB3 : z ^ (rgP α m) * z ^ (1 / 2 - rgP α m) = z ^ ((1 : ℝ) / 2) := by
    rw [show z ^ (rgP α m) * z ^ (1 / 2 - rgP α m)
          = z ^ (rgP α m + (1 / 2 - rgP α m))
          from (Real.rpow_add hz (rgP α m) (1 / 2 - rgP α m)).symm]
    rw [show rgP α m + (1 / 2 - rgP α m) = ((1 : ℝ) / 2) from by ring]
  have hT1 : |(z + h) ^ (rgP α m) - z ^ (rgP α m)| * |rgB α m c (z + h)|
      ≤ (rgP α m * (2 * z) ^ (rgP α m - 1) * h)
          * (ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2) + rgCF α m c δ) := by
    have hb : (0 : ℝ) ≤ rgP α m * (2 * z) ^ (rgP α m - 1) * h := by
      have h1 : (0 : ℝ) < (2 * z) ^ (rgP α m - 1) := Real.rpow_pos_of_pos (by linarith) _
      exact mul_nonneg (mul_nonneg hp.le h1.le) hh.le
    have hc : (0 : ℝ) ≤ ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2) + rgCF α m c δ := by
      refine add_nonneg ?_ hcfg
      exact div_nonneg (mul_nonneg hε (Real.rpow_nonneg hz.le _)) (by linarith)
    exact mul_le_mul hd hB2 (abs_nonneg _) hb
  have hT2 : z ^ (rgP α m) * |rgB α m c (z + h) - cB|
      ≤ z ^ (rgP α m) * (h * (ε * z ^ (1 / 2 - rgP α m))) :=
    mul_le_mul_of_nonneg_left hstep (Real.rpow_pos_of_pos hz _).le
  have h1 : (rgP α m * (2 * z) ^ (rgP α m - 1) * h)
        * (ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2))
      = ε * h * (rgP α m * 2 ^ (rgP α m - 1) / (rgP α m - 3 / 2)) * z ^ ((1 : ℝ) / 2) := by
    rw [show (rgP α m * (2 * z) ^ (rgP α m - 1) * h)
          * (ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2))
        = rgP α m * h * (ε / (rgP α m - 3 / 2))
          * ((2 * z) ^ (rgP α m - 1) * z ^ (3 / 2 - rgP α m)) from by ring]
    rw [keyB1]
    rw [show 2 ^ (rgP α m - 1) * z ^ (rgP α m - 1) * z ^ (3 / 2 - rgP α m)
          = 2 ^ (rgP α m - 1) * (z ^ (rgP α m - 1) * z ^ (3 / 2 - rgP α m)) from by ring]
    rw [keyB2]
    ring
  have h2 : (rgP α m * (2 * z) ^ (rgP α m - 1) * h) * rgCF α m c δ
      = rgCF α m c δ * (rgP α m * 2 ^ (rgP α m - 1)) * z ^ (rgP α m - 1) * h := by
    rw [keyB1]
    ring
  have h3 : z ^ (rgP α m) * (h * (ε * z ^ (1 / 2 - rgP α m))) = ε * h * z ^ ((1 : ℝ) / 2) := by
    rw [show z ^ (rgP α m) * (h * (ε * z ^ (1 / 2 - rgP α m)))
          = h * ε * (z ^ (rgP α m) * z ^ (1 / 2 - rgP α m)) from by ring]
    rw [keyB3]
    ring
  calc |(z + h) ^ (rgP α m) * rgB α m c (z + h) - z ^ (rgP α m) * cB|
      = |((z + h) ^ (rgP α m) - z ^ (rgP α m)) * rgB α m c (z + h)
          + z ^ (rgP α m) * (rgB α m c (z + h) - cB)| := by ring_nf
    _ ≤ |((z + h) ^ (rgP α m) - z ^ (rgP α m)) * rgB α m c (z + h)|
          + |z ^ (rgP α m) * (rgB α m c (z + h) - cB)| := abs_add_le _ _
    _ = |(z + h) ^ (rgP α m) - z ^ (rgP α m)| * |rgB α m c (z + h)|
          + z ^ (rgP α m) * |rgB α m c (z + h) - cB| := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz _)]
    _ ≤ (rgP α m * (2 * z) ^ (rgP α m - 1) * h)
          * (ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2) + rgCF α m c δ)
          + z ^ (rgP α m) * (h * (ε * z ^ (1 / 2 - rgP α m))) := add_le_add hT1 hT2
    _ = h * (ε * z ^ ((1 : ℝ) / 2) * (rgP α m * 2 ^ (rgP α m - 1) / (rgP α m - 3 / 2) + 1)
          + (rgCF α m c δ * (rgP α m * 2 ^ (rgP α m - 1))) * z ^ (rgP α m - 1)) := by
        rw [show (rgP α m * (2 * z) ^ (rgP α m - 1) * h)
              * (ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2) + rgCF α m c δ)
            = (rgP α m * (2 * z) ^ (rgP α m - 1) * h)
                * (ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2))
              + (rgP α m * (2 * z) ^ (rgP α m - 1) * h) * rgCF α m c δ from by ring]
        rw [h1, h2, h3]
        ring


lemma radGreen_step_decomp {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → 2 * z ≤ δ →
      ∃ c₀ : ℝ, ∃ h₀ : ℝ, 0 < h₀ ∧
        (∀ h : ℝ, 0 < h → h ≤ h₀ →
          ‖Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
              - Work.FTS.PhiStar.Radial.radGreen α m c z - c₀‖
            ≤ (rgA1 α m * ε * z ^ ((1 : ℝ) / 2) + rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1))
                * h)
        ∧ ‖c₀‖ ≤ rgK α m * (2 * ε * rgS α m * z ^ ((3 : ℝ) / 2)
            + 2 * rgCF α m c δ * z ^ (rgP α m)) := by
  intro z hz0 h2z
  unfold rgCF at *
  have hq : 0 < rgQ α m := rgQ_pos hα m
  have hp : 0 < rgP α m := rgP_pos hα hm
  have hK : 0 < rgK α m := rgK_pos hα m
  have hzδ : z ≤ δ := by linarith
  have hz1 : z ≤ 1 := le_trans hzδ hδ1
  have hcfg : 0 ≤ (∫ (x : ℝ) in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
      + (∫ (x : ℝ) in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
      + δ ^ (-(2 * rgP α m + 1)) + 1 := rgCF_nonneg hδ
  obtain ⟨cA, hcA, hA0, hApos, hAstep⟩ := rgA_step_claim hα hδ hε hvy z hz0 h2z
  obtain ⟨cB, hcB, hB0, hBpos, hBstep⟩ :=
    rgB_step_claim hα hα4 hm hδ hδ1 hε hvy hnear hfar z hz0 h2z
  refine ⟨rgK α m * (z ^ (-(rgQ α m)) * (cA - rgA α m c z) + z ^ (rgP α m) * (cB - rgB α m c z)),
    min (min hA0 hB0) z, lt_min (lt_min hApos hBpos) hz0, ?_, ?_⟩
  · intro h hh0 hhh
    have hh1 : h ≤ min hA0 hB0 := le_trans hhh (min_le_left _ _)
    have hhA : h ≤ hA0 := le_trans hh1 (min_le_left _ _)
    have hhB : h ≤ hB0 := le_trans hh1 (min_le_right _ _)
    have hhz : h ≤ z := le_trans hhh (min_le_right _ _)
    have hz2δ : z + h ≤ δ := by linarith
    have hz21 : z + h ≤ 1 := by linarith
    have hAinc := rgA_slot_step (m := m) (c := c) hα hδ hε hvy hz0 hh0 hhz hz2δ hcA
      (hAstep h hh0 hhA)
    have hcB' : |cB| ≤ ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2)
        + ((∫ (x : ℝ) in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
          + (∫ (x : ℝ) in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
          + δ ^ (-(2 * rgP α m + 1)) + 1) := by linarith [hcB]
    have hBinc := rgB_slot_step (m := m) (c := c) hα hα4 hm hδ hδ1 hε hvy hnear hfar hz0 hh0
      hhz hz2δ hz21 hcB' (hBstep h hh0 hhB)
    have hstep : ‖((z + h) ^ (-(rgQ α m)) * rgA α m c (z + h) - z ^ (-(rgQ α m)) * cA)
          + ((z + h) ^ (rgP α m) * rgB α m c (z + h) - z ^ (rgP α m) * cB)‖
        ≤ ε * h * z ^ ((1 : ℝ) / 2)
              * (rgQ α m * 2 ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2) + 2 ^ (rgQ α m + 1 / 2))
          + h * (ε * z ^ ((1 : ℝ) / 2) * (rgP α m * 2 ^ (rgP α m - 1) / (rgP α m - 3 / 2) + 1)
              + (rgCF α m c δ * (rgP α m * 2 ^ (rgP α m - 1))) * z ^ (rgP α m - 1)) :=
      le_trans (norm_add_le _ _) (add_le_add hAinc hBinc)
    rw [Work.FTS.EllExist.radGreen_eq, Work.FTS.EllExist.radGreen_eq]
    have hfac : rgK α m * ((z + h) ^ (-(rgQ α m)) * rgA α m c (z + h)
            + (z + h) ^ (rgP α m) * rgB α m c (z + h))
          - rgK α m * (z ^ (-(rgQ α m)) * rgA α m c z + z ^ (rgP α m) * rgB α m c z)
          - rgK α m * (z ^ (-(rgQ α m)) * (cA - rgA α m c z)
              + z ^ (rgP α m) * (cB - rgB α m c z))
        = rgK α m * (((z + h) ^ (-(rgQ α m)) * rgA α m c (z + h) - z ^ (-(rgQ α m)) * cA)
            + ((z + h) ^ (rgP α m) * rgB α m c (z + h) - z ^ (rgP α m) * cB)) := by ring
    rw [hfac, norm_mul, Real.norm_eq_abs, abs_of_pos hK]
    calc rgK α m * ‖((z + h) ^ (-(rgQ α m)) * rgA α m c (z + h) - z ^ (-(rgQ α m)) * cA)
              + ((z + h) ^ (rgP α m) * rgB α m c (z + h) - z ^ (rgP α m) * cB)‖
        ≤ rgK α m * (ε * h * z ^ ((1 : ℝ) / 2)
                * (rgQ α m * 2 ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2) + 2 ^ (rgQ α m + 1 / 2))
            + h * (ε * z ^ ((1 : ℝ) / 2) * (rgP α m * 2 ^ (rgP α m - 1) / (rgP α m - 3 / 2) + 1)
                + (rgCF α m c δ * (rgP α m * 2 ^ (rgP α m - 1))) * z ^ (rgP α m - 1))) :=
          mul_le_mul_of_nonneg_left hstep hK.le
      _ = (rgA1 α m * ε * z ^ ((1 : ℝ) / 2) + rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1))
            * h := by
          rw [rgA1, rgA2]
          ring
  · have hAz := rgA_value_bound (α := α) (m := m) (c := c) hα hδ hε hvy z hz0 hzδ
    have hBz := rgB_value_bound (α := α) (m := m) (c := c) hα hα4 hm hδ hδ1 hε hvy hnear hfar
      z hz0 hz1
    have hca : |cA - rgA α m c z| ≤ 2 * (ε * z ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2)) := by
      have h1 : -(ε * z ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2)) ≤ cA
          ∧ cA ≤ ε * z ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2) := abs_le.mp hcA
      have h2 : -(ε * z ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2)) ≤ rgA α m c z
          ∧ rgA α m c z ≤ ε * z ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2) := abs_le.mp hAz
      refine abs_sub_le_iff.mpr ⟨by linarith [h1.2, h2.1], by linarith [h2.2, h1.1]⟩
    have hcb : |cB - rgB α m c z| ≤ 2 * (ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2)
        + rgCF α m c δ) := by
      have hcB'' : |cB| ≤ ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2)
          + ((∫ (x : ℝ) in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
            + (∫ (x : ℝ) in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
            + δ ^ (-(2 * rgP α m + 1)) + 1) := by linarith [hcB]
      have hBz' : |rgB α m c z| ≤ ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2)
          + ((∫ (x : ℝ) in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
            + (∫ (x : ℝ) in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
            + δ ^ (-(2 * rgP α m + 1)) + 1) := by linarith [hBz]
      have h1 : -(ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2) + rgCF α m c δ) ≤ cB
          ∧ cB ≤ ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2) + rgCF α m c δ := abs_le.mp hcB''
      have h2 : -(ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2) + rgCF α m c δ) ≤ rgB α m c z
          ∧ rgB α m c z ≤ ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2) + rgCF α m c δ :=
        abs_le.mp hBz'
      refine abs_sub_le_iff.mpr ⟨by linarith [h1.2, h2.1], by linarith [h2.2, h1.1]⟩
    have hznq : (0 : ℝ) < z ^ (-(rgQ α m)) := Real.rpow_pos_of_pos hz0 _
    have hzp : (0 : ℝ) < z ^ (rgP α m) := Real.rpow_pos_of_pos hz0 _
    have hsq : (0 : ℝ) < rgQ α m + 3 / 2 := by linarith
    have hsp : (0 : ℝ) < rgP α m - 3 / 2 := by have := rgP_ge hα hα4 hm; linarith
    have keyq : z ^ (-(rgQ α m)) * z ^ (rgQ α m + 3 / 2) = z ^ ((3 : ℝ) / 2) := by
      rw [show z ^ (-(rgQ α m)) * z ^ (rgQ α m + 3 / 2)
            = z ^ ((-(rgQ α m)) + (rgQ α m + 3 / 2))
            from (Real.rpow_add hz0 (-(rgQ α m)) (rgQ α m + 3 / 2)).symm]
      rw [show (-(rgQ α m)) + (rgQ α m + 3 / 2) = ((3 : ℝ) / 2) from by ring]
    have keyp : z ^ (rgP α m) * z ^ (3 / 2 - rgP α m) = z ^ ((3 : ℝ) / 2) := by
      rw [show z ^ (rgP α m) * z ^ (3 / 2 - rgP α m)
            = z ^ (rgP α m + (3 / 2 - rgP α m))
            from (Real.rpow_add hz0 (rgP α m) (3 / 2 - rgP α m)).symm]
      rw [show rgP α m + (3 / 2 - rgP α m) = ((3 : ℝ) / 2) from by ring]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hK]
    calc rgK α m * ‖z ^ (-(rgQ α m)) * (cA - rgA α m c z)
            + z ^ (rgP α m) * (cB - rgB α m c z)‖
        ≤ rgK α m * (z ^ (-(rgQ α m)) * |cA - rgA α m c z|
            + z ^ (rgP α m) * |cB - rgB α m c z|) := by
          refine mul_le_mul_of_nonneg_left ?_ hK.le
          calc ‖z ^ (-(rgQ α m)) * (cA - rgA α m c z) + z ^ (rgP α m) * (cB - rgB α m c z)‖
              ≤ ‖z ^ (-(rgQ α m)) * (cA - rgA α m c z)‖
                + ‖z ^ (rgP α m) * (cB - rgB α m c z)‖ := norm_add_le _ _
            _ = z ^ (-(rgQ α m)) * |cA - rgA α m c z|
                + z ^ (rgP α m) * |cB - rgB α m c z| := by
                rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hznq,
                  abs_of_pos hzp]
      _ ≤ rgK α m * (z ^ (-(rgQ α m)) * (2 * (ε * z ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2)))
            + z ^ (rgP α m) * (2 * (ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2)
                + rgCF α m c δ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hK.le
          exact add_le_add (mul_le_mul_of_nonneg_left hca hznq.le)
            (mul_le_mul_of_nonneg_left hcb hzp.le)
      _ = rgK α m * (2 * ε * rgS α m * z ^ ((3 : ℝ) / 2)
            + 2 * rgCF α m c δ * z ^ (rgP α m)) := by
          congr 1
          rw [rgS]
          rw [show z ^ (-(rgQ α m)) * (2 * (ε * z ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2)))
                + z ^ (rgP α m) * (2 * (ε * z ^ (3 / 2 - rgP α m) / (rgP α m - 3 / 2)
                    + rgCF α m c δ))
              = 2 * ε * (z ^ (-(rgQ α m)) * z ^ (rgQ α m + 3 / 2)) / (rgQ α m + 3 / 2)
                + 2 * ε * (z ^ (rgP α m) * z ^ (3 / 2 - rgP α m)) / (rgP α m - 3 / 2)
                + 2 * rgCF α m c δ * z ^ (rgP α m) from by ring]
          rw [keyq, keyp]
          ring

end Work.FTS.PhiStar.Honesty
