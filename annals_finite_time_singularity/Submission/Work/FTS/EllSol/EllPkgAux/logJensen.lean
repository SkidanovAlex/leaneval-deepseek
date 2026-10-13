import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.wExpCmp
import Submission.Work.FTS.EllSol.EllPkgAux.sKer_conv_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

open Work.FTS.EllSol.PkgK5.K5c

/-! ### the weight `Ω` -/

/-- The logarithmic radial weight `Ω(s) = w(e^s)^2 e^s`. -/
def ljOm (s : ℝ) : ℝ := (Work.Spaces.w (Real.exp s)) ^ 2 * Real.exp s

lemma ljOm_nonneg (s : ℝ) : 0 ≤ ljOm s := by
  rw [ljOm]
  exact mul_nonneg (sq_nonneg _) (Real.exp_pos s).le

lemma ljOm_pos (s : ℝ) : 0 < ljOm s := by
  rw [ljOm]
  have h1 : 0 < Work.Spaces.w (Real.exp s) := by
    rw [Work.Spaces.w]
    positivity
  exact mul_pos (pow_pos h1 2) (Real.exp_pos s)

/-! ### elementary facts about the kernel `sKer` -/

lemma lj_sKer_continuous (ε : ℝ) : Continuous (sKer ε) := by
  have h : sKer ε = fun t : ℝ => (ε * sMass)⁻¹ * sBump (t / ε) := by
    funext t; rw [sKer]
  rw [h]
  exact continuous_const.mul (sBump_continuous.comp (continuous_id.div_const ε))

lemma lj_sKer_hasCompactSupport {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (sKer ε) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-ε) ε) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  have hlt : |t| < ε := by
    by_contra h
    exact ht (sKer_eq_zero_of_le_abs hε (not_lt.mp h))
  rw [abs_lt] at hlt
  exact ⟨le_of_lt hlt.1, le_of_lt hlt.2⟩

lemma lj_sKer_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (sKer ε) volume :=
  (lj_sKer_continuous ε).integrable_of_hasCompactSupport (lj_sKer_hasCompactSupport hε)

lemma lj_sKer_le_inv {ε : ℝ} (hε : 0 < ε) (t : ℝ) : sKer ε t ≤ (ε * sMass)⁻¹ := by
  rw [sKer]
  have h1 : (0 : ℝ) ≤ (ε * sMass)⁻¹ := inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le)
  calc (ε * sMass)⁻¹ * sBump (t / ε) ≤ (ε * sMass)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (sBump_le_one _) h1
    _ = (ε * sMass)⁻¹ := by ring

lemma lj_sKer_sub_eq (δ s t : ℝ) : sKer δ (s - t) = sKer δ (t - s) := by
  rw [show s - t = -(t - s) by ring, sKer_even]

lemma lj_sKer_integrable_sub {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    Integrable (fun t : ℝ => sKer δ (s - t)) volume := by
  have h : Integrable (fun t : ℝ => sKer δ (t - s)) volume := (lj_sKer_integrable hδ).comp_sub_right s
  refine h.congr ?_
  filter_upwards with t
  exact (lj_sKer_sub_eq δ s t).symm

lemma lj_sKer_integral_sub (δ : ℝ) (hδ : 0 < δ) (s : ℝ) : (∫ t : ℝ, sKer δ (s - t)) = 1 := by
  have h1 : (∫ t : ℝ, sKer δ (s - t)) = ∫ t : ℝ, sKer δ (t - s) := by
    refine integral_congr_ae ?_
    filter_upwards with t
    exact lj_sKer_sub_eq δ s t
  rw [h1, integral_sub_right_eq_self, sKer_integral_eq_one hδ]

lemma lj_ae_measurable_sKer_mul (δ s : ℝ) {ψ : ℝ → ℝ} (hψ : AEMeasurable ψ volume) :
    AEMeasurable (fun t : ℝ => sKer δ (s - t) * ψ t) volume :=
  (((lj_sKer_continuous δ).comp (continuous_const.sub continuous_id)).aemeasurable (μ := volume)).mul hψ

lemma lj_integrable_sKer_mul {δ : ℝ} (hδ : 0 < δ) {ψ : ℝ → ℝ} (hψ : Integrable ψ)
    (hψnn : ∀ t, 0 ≤ ψ t) (s : ℝ) :
    Integrable (fun t : ℝ => sKer δ (s - t) * ψ t) volume := by
  have hC : (0 : ℝ) ≤ (δ * sMass)⁻¹ := inv_nonneg.mpr (mul_nonneg hδ.le sMass_pos.le)
  refine Integrable.mono' (hψ.const_mul ((δ * sMass)⁻¹))
    (lj_ae_measurable_sKer_mul δ s hψ.aemeasurable).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (mul_nonneg (sKer_nonneg hδ (s - t)) (hψnn t))]
  exact mul_le_mul_of_nonneg_right (lj_sKer_le_inv hδ (s - t)) (hψnn t)

/-! ### the completed-square (Jensen) inequality for a probability density -/

theorem lj_sq_integral_mul_le_of_prob {α : Type*} [MeasurableSpace α] {μ : Measure α} {k A : α → ℝ}
    (hk_nn : ∀ p, 0 ≤ k p) (hk_int : Integrable k μ)
    (hA_int : Integrable (fun p => k p * A p) μ)
    (hA2_int : Integrable (fun p => k p * (A p) ^ 2) μ)
    (hk_mass : ∫ p, k p ∂μ = 1) :
    (∫ p, k p * A p ∂μ) ^ 2 ≤ ∫ p, k p * (A p) ^ 2 ∂μ := by
  set m : ℝ := ∫ p, k p * A p ∂μ with hm
  have hsq : 0 ≤ ∫ p, k p * (A p - m) ^ 2 ∂μ :=
    integral_nonneg fun p => mul_nonneg (hk_nn p) (sq_nonneg _)
  have hexp : ∫ p, k p * (A p - m) ^ 2 ∂μ = (∫ p, k p * (A p) ^ 2 ∂μ) - m ^ 2 := by
    have hI1 : Integrable (fun p => k p * (A p) ^ 2 - (2 * m) * (k p * A p)) μ :=
      hA2_int.sub (hA_int.const_mul (2 * m))
    have hI2 : Integrable (fun p => m ^ 2 * k p) μ := hk_int.const_mul (m ^ 2)
    calc ∫ p, k p * (A p - m) ^ 2 ∂μ
        = ∫ p, (k p * (A p) ^ 2 - (2 * m) * (k p * A p)) + m ^ 2 * k p ∂μ :=
          integral_congr_ae (Eventually.of_forall fun p => by ring)
      _ = (∫ p, k p * (A p) ^ 2 - (2 * m) * (k p * A p) ∂μ) + ∫ p, m ^ 2 * k p ∂μ := by
          rw [integral_add hI1 hI2]
      _ = ((∫ p, k p * (A p) ^ 2 ∂μ) - ∫ p, (2 * m) * (k p * A p) ∂μ)
            + ∫ p, m ^ 2 * k p ∂μ := by
          rw [integral_sub hA2_int (hA_int.const_mul (2 * m))]
      _ = ((∫ p, k p * (A p) ^ 2 ∂μ) - (2 * m) * ∫ p, k p * A p ∂μ)
            + m ^ 2 * ∫ p, k p ∂μ := by
          rw [integral_const_mul, integral_const_mul]
      _ = (∫ p, k p * (A p) ^ 2 ∂μ) - m ^ 2 := by
          rw [← hm, hk_mass]; ring
  linarith

/-! ### the pointwise Jensen bound -/

lemma lj_mul_sq_inv (a b : ℝ) : (a * b) ^ 2 * a⁻¹ = a * b ^ 2 := by
  by_cases ha : a = 0
  · subst ha; simp
  · field_simp

lemma lj_jensen_pointwise (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {g : ℝ → ℝ}
    (hφ : Integrable (fun t : ℝ => ljOm t * (g t) ^ 2) volume) (s : ℝ) :
    ljOm s * (∫ t : ℝ, sKer δ (s - t) * g t) ^ 2
      ≤ 5 * ∫ t : ℝ, sKer δ (s - t) * (ljOm t * (g t) ^ 2) := by
  have hφnn : ∀ t, 0 ≤ ljOm t * (g t) ^ 2 := fun t => mul_nonneg (ljOm_nonneg t) (sq_nonneg _)
  have hCnn : (0 : ℝ) ≤ (δ * sMass)⁻¹ := inv_nonneg.mpr (mul_nonneg hδ.le sMass_pos.le)
  by_cases hint : Integrable (fun t : ℝ => sKer δ (s - t) * g t) volume
  · have hks_int := lj_sKer_integrable_sub hδ s
    have hks_mass := lj_sKer_integral_sub δ hδ s
    have hm : AEMeasurable (fun t : ℝ => sKer δ (s - t) * (g t) ^ 2) volume := by
      have h1 : AEMeasurable (fun t : ℝ => (sKer δ (s - t) * g t) ^ 2) volume :=
        (hint.aemeasurable).pow_const 2
      have h2 : AEMeasurable (fun t : ℝ => (sKer δ (s - t))⁻¹) volume :=
        (((lj_sKer_continuous δ).comp (continuous_const.sub continuous_id)).aemeasurable (μ := volume)).inv
      refine (h1.mul h2).congr ?_
      filter_upwards with t
      exact lj_mul_sq_inv (sKer δ (s - t)) (g t)
    have hA2 : Integrable (fun t : ℝ => sKer δ (s - t) * (g t) ^ 2) volume := by
      refine Integrable.mono' (hφ.const_mul ((δ * sMass)⁻¹ * 5 / ljOm s))
        hm.aestronglyMeasurable ?_
      filter_upwards with t
      rw [Real.norm_of_nonneg (mul_nonneg (sKer_nonneg hδ (s - t)) (sq_nonneg (g t)))]
      by_cases hcomp : |s - t| ≤ 1 / 2
      · have hc := wExpCmp s t hcomp
        have hOs : 0 < ljOm s := ljOm_pos s
        have hle : 1 ≤ 5 * ljOm t / ljOm s := by
          refine (le_div_iff₀ hOs).mpr ?_
          simpa only [ljOm, one_mul] using hc
        calc sKer δ (s - t) * (g t) ^ 2
            ≤ (δ * sMass)⁻¹ * (g t) ^ 2 :=
              mul_le_mul_of_nonneg_right (lj_sKer_le_inv hδ (s - t)) (sq_nonneg (g t))
          _ ≤ ((δ * sMass)⁻¹ * (g t) ^ 2) * (5 * ljOm t / ljOm s) := by
                calc (δ * sMass)⁻¹ * (g t) ^ 2 = ((δ * sMass)⁻¹ * (g t) ^ 2) * 1 := by ring
                  _ ≤ ((δ * sMass)⁻¹ * (g t) ^ 2) * (5 * ljOm t / ljOm s) :=
                      mul_le_mul_of_nonneg_left hle (mul_nonneg hCnn (sq_nonneg (g t)))
          _ = ((δ * sMass)⁻¹ * 5 / ljOm s) * (ljOm t * (g t) ^ 2) := by ring
      · have hz : sKer δ (s - t) = 0 := sKer_eq_zero_of_le_abs hδ (by
          have h : 1 / 2 < |s - t| := not_le.mp hcomp
          linarith)
        rw [hz]
        simp only [zero_mul]
        exact mul_nonneg (div_nonneg (mul_nonneg hCnn (by norm_num)) (ljOm_pos s).le) (hφnn t)
    have hJ := lj_sq_integral_mul_le_of_prob (μ := volume) (k := fun t : ℝ => sKer δ (s - t))
      (A := g) (fun t => sKer_nonneg hδ (s - t)) hks_int hint hA2 hks_mass
    have hOmnn : 0 ≤ ljOm s := ljOm_nonneg s
    have h2 : ljOm s * (∫ t : ℝ, sKer δ (s - t) * (g t) ^ 2)
        = ∫ t : ℝ, ljOm s * (sKer δ (s - t) * (g t) ^ 2) := by
      rw [MeasureTheory.integral_const_mul]
    have hAOm : Integrable (fun t : ℝ => sKer δ (s - t) * (ljOm t * (g t) ^ 2)) volume :=
      lj_integrable_sKer_mul hδ hφ hφnn s
    have h3 : (∫ t : ℝ, ljOm s * (sKer δ (s - t) * (g t) ^ 2))
        ≤ ∫ t : ℝ, 5 * (sKer δ (s - t) * (ljOm t * (g t) ^ 2)) := by
      refine integral_mono_of_nonneg ?_ (hAOm.const_mul 5) ?_
      · filter_upwards with t
        exact mul_nonneg hOmnn (mul_nonneg (sKer_nonneg hδ (s - t)) (sq_nonneg _))
      · filter_upwards with t
        by_cases hcomp : |s - t| ≤ 1 / 2
        · have hc := wExpCmp s t hcomp
          calc ljOm s * (sKer δ (s - t) * (g t) ^ 2)
              = (ljOm s * sKer δ (s - t)) * (g t) ^ 2 := by ring
            _ ≤ (5 * ljOm t * sKer δ (s - t)) * (g t) ^ 2 := by
                refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
                calc ljOm s * sKer δ (s - t) = sKer δ (s - t) * ljOm s := by ring
                  _ ≤ sKer δ (s - t) * (5 * ljOm t) :=
                      mul_le_mul_of_nonneg_left hc (sKer_nonneg hδ (s - t))
                  _ = 5 * ljOm t * sKer δ (s - t) := by ring
            _ = 5 * (sKer δ (s - t) * (ljOm t * (g t) ^ 2)) := by ring
        · have hz : sKer δ (s - t) = 0 := sKer_eq_zero_of_le_abs hδ (by
            have h : 1 / 2 < |s - t| := not_le.mp hcomp
            linarith)
          rw [hz]
          simp
    have h4 : (∫ t : ℝ, 5 * (sKer δ (s - t) * (ljOm t * (g t) ^ 2)))
        = 5 * ∫ t : ℝ, sKer δ (s - t) * (ljOm t * (g t) ^ 2) :=
      MeasureTheory.integral_const_mul 5 _
    calc ljOm s * (∫ t : ℝ, sKer δ (s - t) * g t) ^ 2
        ≤ ljOm s * ∫ t : ℝ, sKer δ (s - t) * (g t) ^ 2 := mul_le_mul_of_nonneg_left hJ hOmnn
      _ = ∫ t : ℝ, ljOm s * (sKer δ (s - t) * (g t) ^ 2) := h2
      _ ≤ ∫ t : ℝ, 5 * (sKer δ (s - t) * (ljOm t * (g t) ^ 2)) := h3
      _ = 5 * ∫ t : ℝ, sKer δ (s - t) * (ljOm t * (g t) ^ 2) := h4
  · have hz : (∫ t : ℝ, sKer δ (s - t) * g t) = 0 := MeasureTheory.integral_undef hint
    have hnn : 0 ≤ ∫ t : ℝ, sKer δ (s - t) * (ljOm t * (g t) ^ 2) :=
      integral_nonneg (fun t => mul_nonneg (sKer_nonneg hδ (s - t)) (hφnn t))
    have hzero : ljOm s * (∫ t : ℝ, sKer δ (s - t) * g t) ^ 2 = 0 := by rw [hz]; ring
    rw [hzero]
    exact mul_nonneg (by norm_num) hnn

/-! ### the weighted Young inequality -/

lemma lj_mainStep (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {g : ℝ → ℝ}
    (hφ : Integrable (fun t : ℝ => ljOm t * (g t) ^ 2) volume) :
    (∫ s : ℝ, ljOm s * (∫ t : ℝ, sKer δ (s - t) * g t) ^ 2)
      ≤ 5 * ∫ t : ℝ, ljOm t * (g t) ^ 2 := by
  have hconv := sKer_conv_integral δ hδ hφ
  have hg : Integrable (fun s : ℝ => 5 * ∫ t : ℝ, sKer δ (s - t) * (ljOm t * (g t) ^ 2)) volume :=
    hconv.1.const_mul 5
  have hmain : (∫ s : ℝ, ljOm s * (∫ t : ℝ, sKer δ (s - t) * g t) ^ 2)
      ≤ ∫ s : ℝ, 5 * ∫ t : ℝ, sKer δ (s - t) * (ljOm t * (g t) ^ 2) := by
    refine integral_mono_of_nonneg ?_ hg ?_
    · filter_upwards with s
      exact mul_nonneg (ljOm_nonneg s) (sq_nonneg _)
    · filter_upwards with s
      exact lj_jensen_pointwise δ hδ hδ2 hφ s
  refine le_trans hmain ?_
  rw [MeasureTheory.integral_const_mul, hconv.2]

/-! ### the theorem -/

theorem logJensen : ∃ K : ℝ, 0 < K ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 2 → ∀ (f : ℝ → ℝ), MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (f z) ^ 2) (Set.Ioi 0) → (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) * f (Real.exp t)) ^ 2) ≤ K * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2 := by
  refine ⟨5, by norm_num, ?_⟩
  intro δ hδ hδ2 f hf
  have hφ : Integrable (fun t : ℝ => ljOm t * (f (Real.exp t)) ^ 2) volume := by
    have h := (MeasureTheory.integrable_comp_exp
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (f z) ^ 2)).mpr hf
    have hEq : (fun x : ℝ => Real.exp x • ((Work.Spaces.w (Real.exp x)) ^ 2 * (f (Real.exp x)) ^ 2))
        = fun t : ℝ => ljOm t * (f (Real.exp t)) ^ 2 := by
      funext x
      rw [smul_eq_mul, ljOm]
      ring
    rwa [hEq] at h
  have hL : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
        * (∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) * f (Real.exp t)) ^ 2)
      = ∫ s : ℝ, ljOm s * (∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (s - t) * f (Real.exp t)) ^ 2 := by
    rw [← MeasureTheory.integral_comp_exp (fun z : ℝ => (Work.Spaces.w z) ^ 2
      * (∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) * f (Real.exp t)) ^ 2)]
    refine integral_congr_ae ?_
    filter_upwards with s
    rw [Real.log_exp, smul_eq_mul, ljOm]
    ring
  have hR : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2)
      = ∫ t : ℝ, ljOm t * (f (Real.exp t)) ^ 2 := by
    rw [← MeasureTheory.integral_comp_exp (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (f z) ^ 2)]
    refine integral_congr_ae ?_
    filter_upwards with s
    rw [smul_eq_mul, ljOm]
    ring
  rw [hL, hR]
  exact lj_mainStep δ hδ hδ2 hφ

end Work.FTS.EllSol.EllPkgAux
