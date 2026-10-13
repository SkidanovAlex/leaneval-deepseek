import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.C0_sq_le_Ef
import Submission.Work.Coercivity.gamDth_l2_bound
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.Coercivity.integral_sin_two_neg_rpow_le
import Submission.Work.Coercivity.rpow_neg_sq
import Submission.Work.Coercivity.EDth_eq_wip
import Submission.Work.Coercivity.T4aux
import Submission.Work.Coercivity.L2CoercivityTransport
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

/-! ## Pointwise algebra -/

/-- Pointwise identity: the integrand of `wip (thetaW α) (T4 α f) (Dth f)` is
`(C0 f / c α)` times `T4W α f`. -/
theorem T4_integrand_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    T4 α f p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2
      = (C0 f / Spaces.c α) * T4W α f p := by
  rw [T4, thetaW, T4W, T4g]
  ring

/-- The pointwise Cauchy–Schwarz domination: on the quadrant,
`|T4W α f| ≤ 2α |T4A α · T4B α f|`. -/
theorem T4W_abs_le (α : ℝ) (hα : 0 < α) (hΓ2 : GammaPointwiseBnd α) (f : ℝ → ℝ → ℝ)
    {p : ℝ × ℝ} (hz : p.1 ∈ Spaces.Iz) (hθ : p.2 ∈ Spaces.Iθ) :
    |T4W α f p| ≤ 2 * α * |T4A α p * T4B α f p| := by
  have hsin : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hΓnn : 0 ≤ Spaces.Gam α p.2 := by
    rw [Spaces.Gam]
    exact Real.rpow_nonneg (mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
      (sq_nonneg _)) _
  have hgnn : 0 ≤ T4g p.1 := T4g_nonneg hz
  have hhnn : 0 ≤ T4h α p.2 := T4h_nonneg α p.2 hsin
  have hwnn : 0 ≤ Spaces.w p.1 := w_nonneg hz
  have hsγ : 0 ≤ (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hsin _
  have hw2 : 0 ≤ (Spaces.w p.1) ^ 2 := sq_nonneg _
  have hDθ : |DthGam α p.1 p.2| ≤ 2 * α * Spaces.Gam α p.2 := by
    rw [DthGam_eq]
    exact hΓ2 p.2 hθ
  have hsq : T4h α p.2 * T4h α p.2 = (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) := by
    rw [← sq, T4h_sq α p.2 hsin]
  have hX : 0 ≤ T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) * (Spaces.w p.1) ^ 2
      * |Spaces.Dth f p.1 p.2| := by positivity
  have hleft : |T4W α f p|
      = |DthGam α p.1 p.2| * (T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))
          * (Spaces.w p.1) ^ 2 * |Spaces.Dth f p.1 p.2|) := by
    rw [T4W]
    simp only [abs_mul]
    rw [abs_of_nonneg hgnn, abs_of_nonneg hsγ, abs_of_nonneg hw2]
    ring
  have hr1 : |T4A α p * T4B α f p|
      = Spaces.Gam α p.2 * T4g p.1 * T4h α p.2 * Spaces.w p.1
          * (T4h α p.2 * Spaces.w p.1 * |Spaces.Dth f p.1 p.2|) := by
    rw [T4A, T4B]
    simp only [abs_mul]
    rw [abs_of_nonneg hΓnn, abs_of_nonneg hgnn, abs_of_nonneg hhnn, abs_of_nonneg hwnn]
  have hright : |T4A α p * T4B α f p|
      = Spaces.Gam α p.2 * (T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))
          * (Spaces.w p.1) ^ 2 * |Spaces.Dth f p.1 p.2|) := by
    rw [hr1, ← hsq]
    ring
  rw [hleft, hright]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hDθ hX

/-! ## The two scalar estimates -/

/-- Measurability of the angular integrand. -/
theorem measurable_Gam_sq_sin (α : ℝ) :
    Measurable (fun θ : ℝ => (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by
  have h1 : Measurable (fun θ : ℝ => Spaces.Gam α θ) := measurable_Gam α
  have h2 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) :=
    (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _
  have h := (h1.mul h1).mul h2
  convert h using 1
  funext θ
  simp only [Pi.mul_apply]
  rw [pow_two]

/-- **The angular estimate.** `∫_θ Γ(θ)² sin(2θ)^{-γ} ≤ 120/(17α)`, with the integrand
integrable.  Since `Γ²  ≤ sin(2θ)^{2α/3}` (`Gam_sq_le_sin_two`) the integrand is bounded
by `sin(2θ)^{-q}` with `q = 1 - 17α/30`, and `q ∈ (0,1)` for `α ≤ 1`. -/
theorem Gam_sq_sin_neg_gam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ => (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      Spaces.Iθ ∧
    ∫ θ in Spaces.Iθ, (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      ≤ 120 / (17 * α) := by
  have hq0 : 0 < 1 - 17 * α / 30 := by linarith
  have hq1 : 1 - 17 * α / 30 < 1 := by linarith
  obtain ⟨hint, hval⟩ := integral_sin_two_neg_rpow_le (1 - 17 * α / 30) hq0 hq1
  have hne : 2 * α / 3 + -(Spaces.gam α) ≠ 0 := by
    rw [Spaces.gam]
    intro h
    linarith
  have hpoint : ∀ θ ∈ Spaces.Iθ, (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
    intro θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h1 := Gam_sq_le_sin_two α hα θ hθ
    have h2 : (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        = (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
      rw [← Real.rpow_add' hsin hne]
      congr 1
      rw [Spaces.gam]
      ring
    calc (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hsin _)
      _ = _ := h2
  have hnnpt : ∀ θ ∈ Spaces.Iθ, 0 ≤ (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
    intro θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  have hnn : 0 ≤ᵐ[volume.restrict Spaces.Iθ]
      (fun θ => (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hnnpt θ hθ
  constructor
  · refine Integrable.mono' hint (measurable_Gam_sq_sin α).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (hnnpt θ hθ)]
    exact hpoint θ hθ
  · have hmono := integral_mono_of_nonneg hnn hint (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hpoint θ hθ)
    calc ∫ θ in Spaces.Iθ, (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        ≤ ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := hmono
      _ ≤ 4 / (1 - (1 - 17 * α / 30)) := hval
      _ = 120 / (17 * α) := by
          field_simp
          ring

/-- **The radial estimate.** `∫_z (2z²/(1+z)³)² w(z)² = 4`, with the integrand
integrable: the integrand equals `4/(1+z)²` for `z ≠ 0`, and `∫_0^∞ 4/(1+z)² = 4`. -/
theorem gz_sq_w_sq_integral :
    IntegrableOn (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * (Spaces.w z) ^ 2) Spaces.Iz ∧
    ∫ z in Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * (Spaces.w z) ^ 2 = 4 := by
  have hzpos : ∀ᵐ z ∂(volume.restrict Spaces.Iz), 0 < z := by
    rw [Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
    have hset : {z : ℝ | ¬ (z ∈ Set.Ici (0 : ℝ) → 0 < z)} = {0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_Ici, Set.mem_singleton_iff, not_imp]
      constructor
      · rintro ⟨h1, h2⟩
        exact le_antisymm (not_lt.mp h2) h1
      · rintro rfl
        exact ⟨le_refl 0, lt_irrefl 0⟩
    rw [hset, Real.volume_singleton]
  have hae : (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * (Spaces.w z) ^ 2)
      =ᵐ[volume.restrict Spaces.Iz] (fun z : ℝ => 4 * (1 / (1 + z) ^ 2)) := by
    filter_upwards [hzpos] with z hz
    rw [Spaces.w]
    field_simp
    ring
  constructor
  · exact (integrable_Iz_one_div_sq.const_mul 4).congr hae.symm
  · rw [integral_congr_ae hae, integral_const_mul, integral_Iz_one_div_sq]
    norm_num

/-! ## Cauchy–Schwarz on the product space -/

/-- Cauchy–Schwarz in the form used below: for two `L²` functions `A, B` (squares
integrable, a.e. strongly measurable), the product is integrable and
`|∫ A·B| ≤ √(∫A²)·√(∫B²)`. -/
theorem integrable_mul_abs_integral_le_sqrt {μ : MeasureTheory.Measure (ℝ × ℝ)}
    (A B : ℝ × ℝ → ℝ)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hA2 : Integrable (fun p => A p ^ 2) μ) (hB2 : Integrable (fun p => B p ^ 2) μ) :
    Integrable (fun p => A p * B p) μ ∧
      |∫ p, A p * B p ∂μ| ≤ Real.sqrt (∫ p, A p ^ 2 ∂μ) * Real.sqrt (∫ p, B p ^ 2 ∂μ) := by
  have hAB : Integrable (fun p => A p * B p) μ := by
    refine Integrable.mono' (g := fun p => (1 / 2) * (A p ^ 2 + B p ^ 2)) ?_
      (hA.mul hB) ?_
    · refine ((hA2.add hB2).const_mul (1 / 2)).congr (Eventually.of_forall fun p => ?_)
      simp only [Pi.add_apply]
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : 2 * |A p| * |B p| ≤ A p ^ 2 + B p ^ 2 := by
        have h := two_mul_le_add_sq (|A p|) (|B p|)
        rw [sq_abs, sq_abs] at h
        linarith
      linarith
  refine ⟨hAB, ?_⟩
  have hAmlp : MemLp A 2 μ := (memLp_two_iff_integrable_sq hA).mpr hA2
  have hBmlp : MemLp B 2 μ := (memLp_two_iff_integrable_sq hB).mpr hB2
  have hcs := cs_integral_mul hAmlp hBmlp
  have hAn : 0 ≤ ∫ p, A p ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg (A p)
  have hBn : 0 ≤ ∫ p, B p ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg (B p)
  have h2 : |∫ p, A p * B p ∂μ| ^ 2 ≤ (∫ p, A p ^ 2 ∂μ) * (∫ p, B p ^ 2 ∂μ) := by
    rw [sq_abs]
    exact hcs
  calc |∫ p, A p * B p ∂μ| = Real.sqrt (|∫ p, A p * B p ∂μ| ^ 2) :=
        (Real.sqrt_sq (abs_nonneg _)).symm
    _ ≤ Real.sqrt ((∫ p, A p ^ 2 ∂μ) * (∫ p, B p ^ 2 ∂μ)) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (∫ p, A p ^ 2 ∂μ) * Real.sqrt (∫ p, B p ^ 2 ∂μ) := Real.sqrt_mul hAn _

/-! ## Integrability and values of the two `L²` factors -/

theorem integrable_T4A_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Integrable (fun p : ℝ × ℝ => (T4A α p) ^ 2) T4P := by
  have hz : Integrable (fun z : ℝ => (T4g z) ^ 2 * (Spaces.w z) ^ 2)
      (volume.restrict Spaces.Iz) := gz_sq_w_sq_integral.1
  have hθ : Integrable (fun θ : ℝ => (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (volume.restrict Spaces.Iθ) := (Gam_sq_sin_neg_gam α hα hα1).1
  refine (hz.mul_prod hθ).congr ?_
  filter_upwards [ae_prod_quadrant] with p hp
  exact (T4A_sq_eq α hp.2).symm

theorem integral_T4A_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ p : ℝ × ℝ, (T4A α p) ^ 2 ∂T4P = 4 * T4J α := by
  have hz : Integrable (fun z : ℝ => (T4g z) ^ 2 * (Spaces.w z) ^ 2)
      (volume.restrict Spaces.Iz) := gz_sq_w_sq_integral.1
  have hθ : Integrable (fun θ : ℝ => (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (volume.restrict Spaces.Iθ) := (Gam_sq_sin_neg_gam α hα hα1).1
  have hpt : (fun p : ℝ × ℝ => (T4A α p) ^ 2) =ᵐ[T4P]
      fun p => ((T4g p.1) ^ 2 * (Spaces.w p.1) ^ 2)
        * ((Spaces.Gam α p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) := by
    filter_upwards [ae_prod_quadrant] with p hp
    exact T4A_sq_eq α hp.2
  have hzval : (∫ z in Spaces.Iz, (T4g z) ^ 2 * (Spaces.w z) ^ 2) = 4 :=
    gz_sq_w_sq_integral.2
  rw [integral_congr_ae hpt,
    show T4P = (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) from rfl,
    integral_prod_sep _ _ hz hθ, hzval]
  rw [T4J]

theorem integrable_T4B_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    Integrable (fun p : ℝ × ℝ => (T4B α f p) ^ 2) T4P := by
  have h := integrableOn_prod (g := fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ
      * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) hi.intDthGam
  refine h.congr ?_
  filter_upwards [ae_prod_quadrant] with p hp
  exact (T4B_sq_eq α f hp.2).symm

theorem integral_T4B_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    ∫ p : ℝ × ℝ, (T4B α f p) ^ 2 ∂T4P = EDth α f := by
  have hIntOn : IntegrableOn
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ
        * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine hi.intDthGam.congr ?_
    filter_upwards with p
    simp only [Function.uncurry]
    ring
  rw [EDth_eq_wip α f,
    wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (Spaces.Dth f) (Spaces.Dth f) hIntOn]
  refine integral_congr_ae ?_
  filter_upwards [ae_prod_quadrant] with p hp
  rw [T4B_sq_eq α f hp.2]
  ring

/-! ## A.e. strong measurability and integrability of `T4W` -/

theorem aesm_Dth (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2) T4P := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Spaces.pth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_pth_quad hsm
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    change ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Spaces.pth f p.1 p.2) _
    exact hsin.mul hcont
  exact Work.Spaces.aesm_of_continuousOn_Qd _ h2

theorem aesm_T4B (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable (T4B α f) T4P := by
  have hm : Measurable (fun p : ℝ × ℝ => T4h α p.2 * Spaces.w p.1) :=
    ((measurable_T4h α).comp measurable_snd).mul ((measurable_w).comp measurable_fst)
  have h := hm.aestronglyMeasurable.mul (aesm_Dth f hsm)
  have h2 : ((fun p : ℝ × ℝ => T4h α p.2 * Spaces.w p.1)
        * fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2) = T4B α f := by
    funext p
    rw [Pi.mul_apply]
    rfl
  rw [← h2]
  exact h

theorem aesm_T4W (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable (T4W α f) T4P := by
  have h1 : Measurable (fun p : ℝ × ℝ => DthGam α p.1 p.2) := measurable_DthGam_prod α
  have h2 : Measurable (fun p : ℝ × ℝ => T4g p.1) := measurable_T4g.comp measurable_fst
  have h3 : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) :=
    (Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow_const _
  have h4 : Measurable (fun p : ℝ × ℝ => (Spaces.w p.1) ^ 2) :=
    (measurable_w.comp measurable_fst).pow_const (2 : ℕ)
  have hm : Measurable (fun p : ℝ × ℝ => DthGam α p.1 p.2 * T4g p.1
      * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) * (Spaces.w p.1) ^ 2) :=
    ((h1.mul h2).mul h3).mul h4
  have h := hm.aestronglyMeasurable.mul (aesm_Dth f hsm)
  have h2 : ((fun p : ℝ × ℝ => DthGam α p.1 p.2 * T4g p.1
        * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) * (Spaces.w p.1) ^ 2)
        * fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2) = T4W α f := by
    funext p
    rw [Pi.mul_apply]
    rfl
  rw [← h2]
  exact h

theorem integrable_T4W (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hΓ2 : GammaPointwiseBnd α)
    (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) (hi : CoerciveData α f) :
    Integrable (T4W α f) T4P := by
  have hAB : Integrable (fun p : ℝ × ℝ => T4A α p * T4B α f p) T4P :=
    (integrable_mul_abs_integral_le_sqrt (T4A α) (T4B α f) (aesm_T4A α)
      (aesm_T4B α f hsm) (integrable_T4A_sq α hα hα1) (integrable_T4B_sq α f hi)).1
  refine (hAB.abs.const_mul (2 * α)).mono' (aesm_T4W α f hsm) ?_
  filter_upwards [ae_prod_quadrant] with p hp
  rw [Real.norm_eq_abs]
  exact T4W_abs_le α hα hΓ2 f hp.1 hp.2

/-! ## The final arithmetic -/

/-- The closing arithmetic step: `1080 √α √Ef √EDth ≤ (5/28)EDth + 6·10⁶ α Ef` for
nonnegative `α, Ef, EDth`.  The quadratic form `(5/28)v² - 1080uv + 6·10⁶u²` is
positive definite (`1080² < 4·(5/28)·6·10⁶`). -/
theorem T4_final_arith (α Ef EDth : ℝ) (hα : 0 ≤ α) (hEf : 0 ≤ Ef) (hEDth : 0 ≤ EDth) :
    1080 * (Real.sqrt α * Real.sqrt Ef * Real.sqrt EDth) ≤ (5 / 28) * EDth + 6 * 10 ^ 6 * α * Ef := by
  have hx : (Real.sqrt EDth) ^ 2 = EDth := Real.sq_sqrt hEDth
  have hy : (Real.sqrt α * Real.sqrt Ef) ^ 2 = α * Ef := by
    rw [mul_pow, Real.sq_sqrt hα, Real.sq_sqrt hEf]
  nlinarith [sq_nonneg (Real.sqrt EDth - 3024 * (Real.sqrt α * Real.sqrt Ef)), hx, hy]

/-! ## The main theorem -/

theorem wip_T4_ge (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (hf : IBP f) (hfH : HardyHyp f) (hΓ2 : GammaPointwiseBnd α) (hi : CoerciveData α f) : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => T4 α f z θ * Spaces.Dth f z θ * thetaW α z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) ∧ -((5 / 28) * EDth α f + 6 * 10 ^ 6 * α * Ef f) ≤ wip (thetaW α) (T4 α f) (Spaces.Dth f) := by
  have hT4A2 : Integrable (fun p : ℝ × ℝ => (T4A α p) ^ 2) T4P := integrable_T4A_sq α hα hα1
  have hT4B2 : Integrable (fun p : ℝ × ℝ => (T4B α f p) ^ 2) T4P := integrable_T4B_sq α f hi
  have hA2val : ∫ p : ℝ × ℝ, (T4A α p) ^ 2 ∂T4P = 4 * T4J α := integral_T4A_sq α hα hα1
  have hB2val : ∫ p : ℝ × ℝ, (T4B α f p) ^ 2 ∂T4P = EDth α f := integral_T4B_sq α f hi
  have hJle : T4J α ≤ 120 / (17 * α) := (Gam_sq_sin_neg_gam α hα hα1).2
  have hJnn : 0 ≤ T4J α := by
    rw [T4J]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  obtain ⟨hABint, hABle⟩ := integrable_mul_abs_integral_le_sqrt (T4A α) (T4B α f)
    (aesm_T4A α) (aesm_T4B α f hf.smooth) hT4A2 hT4B2
  have hT4Wint : Integrable (T4W α f) T4P :=
    integrable_T4W α hα hα1 hΓ2 f hf.smooth hi
  have hT4intP : Integrable (fun p : ℝ × ℝ =>
      T4 α f p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2) T4P := by
    refine (hT4Wint.const_mul (C0 f / Spaces.c α)).congr ?_
    filter_upwards with p
    exact (T4_integrand_eq α f p).symm
  have hOn : IntegrableOn
      (Function.uncurry (fun z θ => T4 α f z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [IntegrableOn, volume_restrict_prod]
    exact hT4intP
  refine ⟨hOn, ?_⟩
  have hEDthnn : 0 ≤ EDth α f := by
    simp only [EDth, Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  have hEfnn : 0 ≤ Ef f := by
    simp only [Ef, Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  have hwip2 : wip (thetaW α) (T4 α f) (Spaces.Dth f)
      = (C0 f / Spaces.c α) * ∫ p : ℝ × ℝ, T4W α f p ∂T4P := by
    rw [wip_eq_integral_prod (thetaW α) (T4 α f) (Spaces.Dth f) hOn, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun p => T4_integrand_eq α f p)
  -- bound on `∫ T4W`
  have hWb : |∫ p : ℝ × ℝ, T4W α f p ∂T4P|
      ≤ 2 * α * ∫ p : ℝ × ℝ, |T4A α p * T4B α f p| ∂T4P := by
    have h1 : |∫ p : ℝ × ℝ, T4W α f p ∂T4P| ≤ ∫ p : ℝ × ℝ, |T4W α f p| ∂T4P :=
      abs_integral_le_integral_abs
    have h2 : ∫ p : ℝ × ℝ, |T4W α f p| ∂T4P
        ≤ ∫ p : ℝ × ℝ, 2 * α * |T4A α p * T4B α f p| ∂T4P := by
      refine integral_mono_ae hT4Wint.abs (hABint.abs.const_mul (2 * α)) ?_
      filter_upwards [ae_prod_quadrant] with p hp
      exact T4W_abs_le α hα hΓ2 f hp.1 hp.2
    have h3 : ∫ p : ℝ × ℝ, 2 * α * |T4A α p * T4B α f p| ∂T4P
        = 2 * α * ∫ p : ℝ × ℝ, |T4A α p * T4B α f p| ∂T4P := integral_const_mul _ _
    linarith
  have hABb : ∫ p : ℝ × ℝ, |T4A α p * T4B α f p| ∂T4P
      ≤ Real.sqrt (∫ p : ℝ × ℝ, (T4A α p) ^ 2 ∂T4P)
        * Real.sqrt (∫ p : ℝ × ℝ, (T4B α f p) ^ 2 ∂T4P) := by
    have hAabs : AEStronglyMeasurable (fun p : ℝ × ℝ => |T4A α p|) T4P := (aesm_T4A α).norm
    have hBabs : AEStronglyMeasurable (fun p : ℝ × ℝ => |T4B α f p|) T4P :=
      (aesm_T4B α f hf.smooth).norm
    have hAabs2 : Integrable (fun p : ℝ × ℝ => (|T4A α p|) ^ 2) T4P :=
      hT4A2.congr (Eventually.of_forall fun p => (sq_abs (T4A α p)).symm)
    have hBabs2 : Integrable (fun p : ℝ × ℝ => (|T4B α f p|) ^ 2) T4P :=
      hT4B2.congr (Eventually.of_forall fun p => (sq_abs (T4B α f p)).symm)
    obtain ⟨-, hle⟩ := integrable_mul_abs_integral_le_sqrt (fun p => |T4A α p|)
      (fun p => |T4B α f p|) hAabs hBabs hAabs2 hBabs2
    have e1 : ∫ p : ℝ × ℝ, (|T4A α p|) ^ 2 ∂T4P = ∫ p : ℝ × ℝ, (T4A α p) ^ 2 ∂T4P :=
      integral_congr_ae (Eventually.of_forall fun p => sq_abs (T4A α p))
    have e2 : ∫ p : ℝ × ℝ, (|T4B α f p|) ^ 2 ∂T4P = ∫ p : ℝ × ℝ, (T4B α f p) ^ 2 ∂T4P :=
      integral_congr_ae (Eventually.of_forall fun p => sq_abs (T4B α f p))
    have e3 : ∫ p : ℝ × ℝ, |T4A α p * T4B α f p| ∂T4P
        = |∫ p : ℝ × ℝ, |T4A α p| * |T4B α f p| ∂T4P| := by
      rw [abs_of_nonneg (integral_nonneg fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact integral_congr_ae (Eventually.of_forall fun p => abs_mul _ _)
    calc ∫ p : ℝ × ℝ, |T4A α p * T4B α f p| ∂T4P
        = |∫ p : ℝ × ℝ, |T4A α p| * |T4B α f p| ∂T4P| := e3
      _ ≤ Real.sqrt (∫ p : ℝ × ℝ, (|T4A α p|) ^ 2 ∂T4P)
            * Real.sqrt (∫ p : ℝ × ℝ, (|T4B α f p|) ^ 2 ∂T4P) := hle
      _ = Real.sqrt (∫ p : ℝ × ℝ, (T4A α p) ^ 2 ∂T4P)
            * Real.sqrt (∫ p : ℝ × ℝ, (T4B α f p) ^ 2 ∂T4P) := by rw [e1, e2]
  have hW2 : |∫ p : ℝ × ℝ, T4W α f p ∂T4P| ≤ 2 * α * (2 * Real.sqrt (T4J α)) * Real.sqrt (EDth α f) := by
    have hstep1 : 2 * α * ∫ p : ℝ × ℝ, |T4A α p * T4B α f p| ∂T4P
        ≤ 2 * α * (Real.sqrt (∫ p : ℝ × ℝ, (T4A α p) ^ 2 ∂T4P)
          * Real.sqrt (∫ p : ℝ × ℝ, (T4B α f p) ^ 2 ∂T4P)) :=
      mul_le_mul_of_nonneg_left hABb (by positivity)
    have heq : 2 * α * (Real.sqrt (∫ p : ℝ × ℝ, (T4A α p) ^ 2 ∂T4P)
          * Real.sqrt (∫ p : ℝ × ℝ, (T4B α f p) ^ 2 ∂T4P))
        = 2 * α * (2 * Real.sqrt (T4J α)) * Real.sqrt (EDth α f) := by
      rw [hA2val, hB2val]
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [show Real.sqrt (4 * T4J α) = 2 * Real.sqrt (T4J α) by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (T4J α), h4]]
      ring
    exact le_trans hWb (le_trans hstep1 (le_of_eq heq))
  have hC0c : |C0 f / Spaces.c α| ≤ 100 * Real.sqrt (Ef f) := by
    have hC0 : (C0 f) ^ 2 ≤ 100 * Ef f := C0_sq_le_Ef α hα hα1 f hf.smooth hf.intSqProd
    have h1 : |C0 f| ≤ 10 * Real.sqrt (Ef f) := by
      have h2 : Real.sqrt ((C0 f) ^ 2) ≤ Real.sqrt (100 * Ef f) := Real.sqrt_le_sqrt hC0
      rw [Real.sqrt_sq_eq_abs] at h2
      have h3 : Real.sqrt (100 * Ef f) = 10 * Real.sqrt (Ef f) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 100) (Ef f)]
        congr 1
        rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    have h2 : |(1 : ℝ) / Spaces.c α| ≤ 10 := by
      have hc := (Spaces.c_bounds α hα hα1).1
      rw [abs_of_nonneg (by positivity), div_le_iff₀ (c_pos hα hα1)]
      linarith
    calc |C0 f / Spaces.c α| = |C0 f| * |(1 : ℝ) / Spaces.c α| := by
          rw [div_eq_mul_one_div, abs_mul]
      _ ≤ (10 * Real.sqrt (Ef f)) * 10 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = 100 * Real.sqrt (Ef f) := by ring
  have hmain : |wip (thetaW α) (T4 α f) (Spaces.Dth f)|
      ≤ 1080 * (Real.sqrt α * Real.sqrt (Ef f) * Real.sqrt (EDth α f)) := by
    rw [hwip2, abs_mul]
    have hstep : |C0 f / Spaces.c α| * |∫ p : ℝ × ℝ, T4W α f p ∂T4P|
        ≤ 100 * Real.sqrt (Ef f) * (2 * α * (2 * Real.sqrt (T4J α)) * Real.sqrt (EDth α f)) :=
      mul_le_mul hC0c hW2 (abs_nonneg _) (by positivity)
    have h400 : 400 * Real.sqrt (120 / 17) ≤ 1080 := by
      have h : Real.sqrt (120 / 17) ≤ 27 / 10 := by
        rw [Real.sqrt_le_iff]
        exact ⟨by norm_num, by norm_num⟩
      linarith
    have hαJ : α * Real.sqrt (T4J α) ≤ Real.sqrt α * Real.sqrt (120 / 17) := by
      have h1 : α * Real.sqrt (T4J α) = Real.sqrt (α ^ 2 * T4J α) := by
        rw [Real.sqrt_mul (sq_nonneg α) (T4J α), Real.sqrt_sq hα.le]
      have h2 : α ^ 2 * T4J α ≤ α * (120 / 17) := by
        calc α ^ 2 * T4J α ≤ α ^ 2 * (120 / (17 * α)) :=
              mul_le_mul_of_nonneg_left hJle (sq_nonneg α)
          _ = α * (120 / 17) := by
              field_simp
              try ring
      calc α * Real.sqrt (T4J α) = Real.sqrt (α ^ 2 * T4J α) := h1
        _ ≤ Real.sqrt (α * (120 / 17)) := Real.sqrt_le_sqrt h2
        _ = Real.sqrt α * Real.sqrt (120 / 17) := Real.sqrt_mul hα.le (120 / 17)
    have hfin : 100 * Real.sqrt (Ef f) * (2 * α * (2 * Real.sqrt (T4J α)) * Real.sqrt (EDth α f))
        ≤ 1080 * (Real.sqrt α * Real.sqrt (Ef f) * Real.sqrt (EDth α f)) := by
      have hαJ' : 400 * (α * Real.sqrt (T4J α)) ≤ 400 * (Real.sqrt α * Real.sqrt (120 / 17)) := by
        linarith
      have h1 : 400 * (α * Real.sqrt (T4J α)) * Real.sqrt (Ef f)
          ≤ 400 * (Real.sqrt α * Real.sqrt (120 / 17)) * Real.sqrt (Ef f) :=
        mul_le_mul_of_nonneg_right hαJ' (Real.sqrt_nonneg _)
      have h2 : 400 * (α * Real.sqrt (T4J α)) * Real.sqrt (Ef f) * Real.sqrt (EDth α f)
          ≤ 400 * (Real.sqrt α * Real.sqrt (120 / 17)) * Real.sqrt (Ef f)
            * Real.sqrt (EDth α f) :=
        mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      have hb : 0 ≤ Real.sqrt α * Real.sqrt (Ef f) * Real.sqrt (EDth α f) := by positivity
      have h3 : 400 * (Real.sqrt α * Real.sqrt (120 / 17)) * Real.sqrt (Ef f)
            * Real.sqrt (EDth α f)
          ≤ 1080 * (Real.sqrt α * Real.sqrt (Ef f) * Real.sqrt (EDth α f)) := by
        have h := mul_le_mul_of_nonneg_right h400 hb
        calc 400 * (Real.sqrt α * Real.sqrt (120 / 17)) * Real.sqrt (Ef f) * Real.sqrt (EDth α f)
            = 400 * Real.sqrt (120 / 17)
              * (Real.sqrt α * Real.sqrt (Ef f) * Real.sqrt (EDth α f)) := by ring
          _ ≤ 1080 * (Real.sqrt α * Real.sqrt (Ef f) * Real.sqrt (EDth α f)) := h
      have hshape : 100 * Real.sqrt (Ef f)
            * (2 * α * (2 * Real.sqrt (T4J α)) * Real.sqrt (EDth α f))
          = 400 * (α * Real.sqrt (T4J α)) * Real.sqrt (Ef f) * Real.sqrt (EDth α f) := by ring
      rw [hshape]
      exact le_trans h2 h3
    linarith
  have hfin2 := T4_final_arith α (Ef f) (EDth α f) hα.le hEfnn hEDthnn
  linarith [hmain, hfin2, neg_abs_le (wip (thetaW α) (T4 α f) (Spaces.Dth f))]

end Work.Coercivity
