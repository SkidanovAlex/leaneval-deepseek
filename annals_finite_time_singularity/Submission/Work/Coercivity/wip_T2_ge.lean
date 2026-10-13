/-
# The `T₂` estimate of the angular coercivity chain

This file proves `Work.Coercivity.wip_T2_ge`: the pairing of the `D_θΓ`-term
`T₂ = -D_θΓ · (2z/(c(1+z)²)) · L₁₂(f)` of `D_θ(𝓛_Γ^T f)` against `D_θ f` with the
weight `thetaW α = w² sin(2θ)^{-γ}` is bounded below by
`-((1/14)·EDth α f + 3·10⁶·α·Ef f)`.

The proof is a single tensor Cauchy–Schwarz: after bounding the pointwise value by
`(|D_θΓ| sin(2θ)^{-γ/2}) · (20 |z⁻¹L₁₂ f|) · (|D_θ f| w sin(2θ)^{-γ/2})` (the `20`
uses `c ≥ 1/10`), Hölder in the product measure gives
`√(∫ (D_θΓ)² sin^{-γ}) · √(400 EL12z) · √(EDth) ≤ 10√α · 20·4√(Ef) · √(EDth)`,
using `gamDth_l2_bound` (the angular factor), `HardyHyp.intA` (the radial factor) and
`EL12z_le` (the Hardy inequality).  Young's inequality then splits the product with
the coefficients `1/14` on `EDth` and `800²·7/2 = 2.24·10⁶` on `α·Ef`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.gamDth_l2_bound
import Submission.Work.Coercivity.EL12z_le
import Submission.Work.Coercivity.DthGam_sq_lintegral_le
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.L12f_continuousOn
import Submission.Work.Coercivity.wip_eq_integral_prod

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

/-! ## Elementary auxiliary facts -/

/-- `sin(2θ)^{-γ/2}` squared is `sin(2θ)^{-γ}` on `Iθ`. -/
private theorem sin_half_rpow_sq {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hne : -(Spaces.gam α / 2) + -(Spaces.gam α / 2) ≠ 0 := by
    simp only [Spaces.gam]
    intro h
    linarith
  rw [sq, ← Real.rpow_add' hsin hne]
  congr 1
  rw [Spaces.gam]
  ring

/-- Almost every `θ ∈ Iθ` lies in the open interval: the two endpoints are null. -/
private theorem ae_Ioo_theta :
    ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  rw [Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  have hset : {θ : ℝ | ¬ (θ ∈ Set.Icc (0 : ℝ) (π / 2) → θ ∈ Set.Ioo 0 (π / 2))}
      = ({0} : Set ℝ) ∪ {π / 2} := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ioo, Set.mem_union, Set.mem_singleton_iff,
      not_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases not_and_or.mp h3 with h | h
      · left; exact le_antisymm (not_lt.mp h) h1
      · right; exact le_antisymm h2 (not_lt.mp h)
    · rintro (rfl | rfl)
      · exact ⟨⟨le_refl 0, by positivity⟩, by simp⟩
      · exact ⟨⟨by positivity, le_refl _⟩, by simp⟩
  rw [hset]
  exact MeasureTheory.measure_union_null (by rw [Real.volume_singleton])
    (by rw [Real.volume_singleton])

/-- Almost every point of the quadrant lies in `Iz ×ˢ Iθ`. -/
private theorem ae_prod_mem :
    ∀ᵐ p ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)),
      p.1 ∈ Spaces.Iz ∧ p.2 ∈ Spaces.Iθ := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_Ici.prod measurableSet_Icc)] with p hp
  exact Set.mem_prod.mp hp

/-- Almost every point of the quadrant has `θ` in the open interval. -/
private theorem ae_prod_mem_univ_Ioo :
    ∀ᵐ p ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)),
      p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
  refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
    (μ := volume.restrict Spaces.Iz) (ν := volume.restrict Spaces.Iθ)
    (s := Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2))
    (hs := MeasurableSet.univ.prod measurableSet_Ioo)).mpr ?_
  exact Filter.Eventually.of_forall (fun z =>
    ae_Ioo_theta.mono (fun θ hθ => Set.mem_prod.mpr ⟨Set.mem_univ z, hθ⟩))

/-- Almost every point of the quadrant has `θ` in the open interval. -/
private theorem ae_prod_Ioo :
    ∀ᵐ p ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)),
      p.2 ∈ Set.Ioo 0 (π / 2) :=
  ae_prod_mem_univ_Ioo.mono (fun _ hp => (Set.mem_prod.mp hp).2)

/-- `√(n² x) = n √x` for `n, x ≥ 0`. -/
private theorem sqrt_sq_mul {n x : ℝ} (hn : 0 ≤ n) (_hx : 0 ≤ x) :
    (n ^ 2 * x) ^ ((1 : ℝ) / 2) = n * Real.sqrt x := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_sq hn]

/-- Young's inequality in the form used at the end of the estimate. -/
private theorem amgm_sqrt {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * Real.sqrt b ≤ (7 / 2) * a ^ 2 + (1 / 14) * b := by
  nlinarith [sq_nonneg (7 * a - Real.sqrt b), Real.sq_sqrt hb]

/-! ## The tensor Cauchy–Schwarz in `ℝ≥0∞` -/

/-- **Tensor Cauchy–Schwarz.**  For `σ`-finite measures `μ` on `α` and `ν` on `β` and
measurable functions `Ge : β → ℝ≥0∞`, `Φf : α × β → ℝ≥0∞`, `Ψf : α → ℝ≥0∞` (with `Ψf`
and `∫⁻Ge²` finite),

`∫∫ Ge(θ) Φf(z,θ) Ψf(z) ≤ (∫Ge²)^{1/2} · (∫∫Φf²)^{1/2} · (∫Ψf²)^{1/2}`. -/
private theorem tensor_holder_ennreal' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν]
    (Ge : β → ENNReal) (Φf : α × β → ENNReal) (Ψf : α → ENNReal)
    (hΨfin : ∀ z, Ψf z ≠ ⊤) (hGeA : (∫⁻ θ, Ge θ ^ 2 ∂ν) ≠ ⊤)
    (hGe : AEMeasurable Ge ν) (hΦ : AEMeasurable Φf (μ.prod ν)) (hΨ : AEMeasurable Ψf μ) :
    ∫⁻ p, Ge p.2 * Φf p * Ψf p.1 ∂(μ.prod ν)
      ≤ (∫⁻ θ, Ge θ ^ 2 ∂ν) ^ ((1 : ℝ) / 2) * (∫⁻ p, Φf p ^ 2 ∂(μ.prod ν)) ^ ((1 : ℝ) / 2)
        * (∫⁻ z, Ψf z ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hm : AEMeasurable (fun p : α × β => Ge p.2 * Ψf p.1) (μ.prod ν) :=
    (AEMeasurable.comp_snd hGe).mul (AEMeasurable.comp_fst hΨ)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.prod ν) hpq hm hΦ
  set A : ENNReal := ∫⁻ θ, Ge θ ^ 2 ∂ν with hA
  set B : ENNReal := ∫⁻ z, Ψf z ^ 2 ∂μ with hB
  set C : ENNReal := ∫⁻ p, Φf p ^ 2 ∂(μ.prod ν) with hC
  have hsq : ∀ p : α × β, (Ge p.2 * Ψf p.1) ^ (2 : ℝ) = Ge p.2 ^ 2 * Ψf p.1 ^ 2 := by
    intro p
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, mul_pow]
  have hCeq : (∫⁻ p, Φf p ^ (2 : ℝ) ∂(μ.prod ν)) = C := by
    rw [hC]
    exact lintegral_congr fun p => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  have hAB : (∫⁻ p, (Ge p.2 * Ψf p.1) ^ (2 : ℝ) ∂(μ.prod ν)) = A * B := by
    rw [lintegral_congr hsq]
    have hm2 : AEMeasurable (fun p : α × β => Ge p.2 ^ 2 * Ψf p.1 ^ 2) (μ.prod ν) :=
      ((AEMeasurable.comp_snd hGe).pow_const 2).mul ((AEMeasurable.comp_fst hΨ).pow_const 2)
    rw [MeasureTheory.lintegral_prod _ hm2]
    have hinner : ∀ z : α, ∫⁻ θ, Ge θ ^ 2 * Ψf z ^ 2 ∂ν = A * Ψf z ^ 2 := by
      intro z
      rw [MeasureTheory.lintegral_mul_const' (Ψf z ^ 2) (fun θ => Ge θ ^ 2) ?_, hA]
      rw [pow_two]
      exact ENNReal.mul_ne_top (hΨfin z) (hΨfin z)
    rw [lintegral_congr hinner, hB]
    exact MeasureTheory.lintegral_const_mul' A (fun z => Ψf z ^ 2) hGeA
  rw [hAB] at hholder
  have hholder' : (∫⁻ p, (Ge p.2 * Ψf p.1) * Φf p ∂(μ.prod ν))
      ≤ (A * B) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
    rw [← hCeq]
    exact hholder
  calc ∫⁻ p, Ge p.2 * Φf p * Ψf p.1 ∂(μ.prod ν)
      = ∫⁻ p, (Ge p.2 * Ψf p.1) * Φf p ∂(μ.prod ν) := by
        refine lintegral_congr fun p => ?_
        ac_rfl
    _ ≤ (A * B) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := hholder'
    _ = (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) * C ^ ((1 : ℝ) / 2) := by
        rw [ENNReal.mul_rpow_of_nonneg A B (by norm_num)]
    _ = A ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
        ac_rfl

/-! ## The three factors of the majorant -/

/-- The `ℝ≥0∞`-version of the radial factor `20 |z⁻¹ L₁₂(f)|`. -/
private theorem lintegral_radial_eq (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    ∫⁻ z, (ENNReal.ofReal (20 * |L12f f z / z|)) ^ 2 ∂(volume.restrict Spaces.Iz)
      = ENNReal.ofReal (400 * EL12z f) := by
  have hIoi : IntegrableOn (fun z : ℝ => (L12f f z / z) ^ 2) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun (hfH.intA 1 (by norm_num)) (fun z _ => ?_) measurableSet_Ioi
    rw [div_pow]
    congr 1
    norm_num
  have hIz : Integrable (fun z : ℝ => (L12f f z / z) ^ 2) (volume.restrict Spaces.Iz) := by
    rw [Spaces.Iz, ← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact hIoi
  have hpt : ∀ z : ℝ, (ENNReal.ofReal (20 * |L12f f z / z|)) ^ 2
      = ENNReal.ofReal (400 : ℝ) * ENNReal.ofReal ((L12f f z / z) ^ 2) := by
    intro z
    rw [← ENNReal.ofReal_pow (mul_nonneg (by norm_num) (abs_nonneg _))]
    rw [show (20 * |L12f f z / z|) ^ 2 = 400 * (L12f f z / z) ^ 2 from by
      rw [mul_pow, sq_abs]; norm_num]
    exact ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 400)
  rw [lintegral_congr hpt]
  rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (400 : ℝ)) _
    ENNReal.ofReal_ne_top]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIz
    (Filter.Eventually.of_forall fun z => sq_nonneg _)]
  rw [show (∫ z in Spaces.Iz, (L12f f z / z) ^ 2) = EL12z f from by
    simp only [EL12z, L2Sqz]]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 400)]

/-- The `ℝ≥0∞`-version of the `D_θ`-factor `|D_θ f| w sin(2θ)^{-γ/2}`: its square
integrates to `EDth α f`. -/
private theorem lintegral_Edth_eq (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ)
    (hi : CoerciveData α f) :
    ∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (|Spaces.Dth f p.1 p.2| * Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2)))) ^ 2
      ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ))
      = ENNReal.ofReal (EDth α f) := by
  have hInt : Integrable (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2
      * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)))
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hi.intDthGam
  have hpt : ∀ᵐ p ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)),
      (ENNReal.ofReal (|Spaces.Dth f p.1 p.2| * Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2)))) ^ 2
      = ENNReal.ofReal (Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2
        * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) := by
    filter_upwards [ae_prod_Ioo] with p hp
    have hsin : 0 < Real.sin (2 * p.2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.1]) (by linarith [hp.2, Real.pi_pos])
    have hnn : 0 ≤ |Spaces.Dth f p.1 p.2| * Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2)) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (by rw [Spaces.w]; positivity))
        (Real.rpow_nonneg hsin.le _)
    have hσ := sin_half_rpow_sq hα ⟨le_of_lt hp.1, le_of_lt hp.2⟩
    rw [← ENNReal.ofReal_pow hnn]
    congr 1
    rw [show (|Spaces.Dth f p.1 p.2| * Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2))) ^ 2
        = |Spaces.Dth f p.1 p.2| ^ 2 * Spaces.w p.1 ^ 2
          * ((Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2))) ^ 2 from by ring,
      sq_abs, hσ]
    ring
  rw [lintegral_congr_ae hpt]
  have hnn2 : 0 ≤ᵐ[(volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)]
      (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) := by
    filter_upwards [ae_prod_Ioo] with p hp
    have hsin : 0 ≤ Real.sin (2 * p.2) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hp.1], by linarith [hp.2, Real.pi_pos]⟩
    exact mul_nonneg (mul_nonneg (mul_self_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg hsin _)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn2]
  congr 1
  rw [MeasureTheory.integral_prod _ hInt]
  have hAE : ∀ᵐ z ∂(volume.restrict Spaces.Iz),
      ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod ae_prod_Ioo
  rw [show (∫ z, ∫ θ, Spaces.Dth f z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) ∂(volume.restrict Spaces.Iθ)
        ∂(volume.restrict Spaces.Iz)) = EDth α f from by
    simp only [EDth, Spaces.L2Sq, wtGam]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hAE] with z hz
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hz] with θ hθ
    have hσ := sin_half_rpow_sq hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [show (Spaces.Dth f z θ * (Spaces.w z * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2)))) ^ 2
        = Spaces.Dth f z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) from by
      rw [← hσ]; ring]]

/-! ## A.e. strong measurability of the integrand -/

/-- `(z,θ) ↦ D_θΓ(θ)` is measurable. -/
private theorem measurable_DthGam (α : ℝ) : Measurable (fun θ : ℝ => DthGam α 0 θ) := by
  show Measurable (fun θ : ℝ => Real.sin (2 * θ) * deriv (fun t : ℝ => Spaces.Gam α t) θ)
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).mul
    (measurable_deriv (fun t : ℝ => Spaces.Gam α t))

/-- A.e. strong measurability of `T₂ f · D_θ f · thetaW α`. -/
private theorem aesm_T2G (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hfH : HardyHyp f) :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => T2 α f z θ * Spaces.Dth f z θ * thetaW α z θ))
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  -- `L₁₂(f)` is a.e. measurable on `Iz`
  have hL12 : AEMeasurable (fun z : ℝ => L12f f z) (volume.restrict Spaces.Iz) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ => L12f f z) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (L12f_continuousOn f hfH).aestronglyMeasurable measurableSet_Ioi
    have h2 : volume.restrict Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [Spaces.Iz]
      exact (Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [h2]
    exact h1.aemeasurable
  -- the angular factor, as a function of `θ`
  have hAngP : AEMeasurable (fun p : ℝ × ℝ => DthGam α 0 p.2) P :=
    AEMeasurable.comp_snd ((measurable_DthGam α).aemeasurable)
  -- the `D_θ f` factor
  have hDth : AEMeasurable (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2) P := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      have hpth := continuousOn_pth_quad hsm
      have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
      exact hsin.mul hpth
    rw [hP]
    exact (Spaces.aesm_of_continuousOn_Qd _ hcont).aemeasurable
  -- the weight
  have hw : AEMeasurable (fun p : ℝ × ℝ => Spaces.w p.1 ^ 2) P := by
    have hm : Measurable (fun z : ℝ => Spaces.w z ^ 2) := by
      show Measurable (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2)
      exact (measurable_const.add measurable_id).pow_const 2 |>.div (measurable_id.pow_const 2)
        |>.pow_const 2
    exact AEMeasurable.comp_fst (hm.aemeasurable)
  have hsig : AEMeasurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) P :=
    AEMeasurable.comp_snd
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _).aemeasurable
  -- assemble
  have hprod : AEMeasurable (fun p : ℝ × ℝ =>
      -(DthGam α 0 p.2) * (2 * p.1 / (Spaces.c α * (1 + p.1) ^ 2)) * L12f f p.1
        * Spaces.Dth f p.1 p.2 * (Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)))) P := by
    have hτ : AEMeasurable (fun p : ℝ × ℝ => 2 * p.1 / (Spaces.c α * (1 + p.1) ^ 2)) P :=
      AEMeasurable.comp_fst (((measurable_const.mul measurable_id).div
        (measurable_const.mul ((measurable_const.add measurable_id).pow_const 2))).aemeasurable)
    have hL : AEMeasurable (fun p : ℝ × ℝ => L12f f p.1) P := AEMeasurable.comp_fst hL12
    exact ((((hAngP.neg.mul hτ).mul hL).mul hDth).mul (hw.mul hsig))
  refine hprod.aestronglyMeasurable.congr ?_
  filter_upwards with p
  simp only [Function.uncurry, T2, thetaW]
  simp only [DthGam_eq]

/-! ## The pointwise comparison of the integrand with the factorised majorant -/

/-- The pointwise bound of the `T₂`-integrand by the product of the three factors. -/
private theorem abs_T2_le' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    |T2 α f z θ * Spaces.Dth f z θ * thetaW α z θ|
      ≤ |DthGam α 0 θ| * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))
        * (20 * |L12f f z / z|)
        * (|Spaces.Dth f z θ| * Spaces.w z * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))) := by
  have hc : (1 : ℝ) / 10 ≤ Spaces.c α := (Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Spaces.c α := c_pos hα hα1
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hw0 : 0 ≤ Spaces.w z := by rw [Spaces.w]; positivity
  have hzg : 0 ≤ z := hz
  rcases eq_or_lt_of_le hzg with hzero | hzpos
  · subst hzero
    simp [T2, thetaW, Spaces.w]
  · have hkey : |2 * z / (Spaces.c α * (1 + z) ^ 2)| * Spaces.w z ≤ 20 / z := by
      have h1 : |2 * z / (Spaces.c α * (1 + z) ^ 2)| * Spaces.w z
          = 2 / (Spaces.c α * z) := by
        rw [Spaces.w, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * z / (Spaces.c α * (1 + z) ^ 2))]
        field_simp
      rw [h1, div_le_iff₀ (by positivity : (0 : ℝ) < Spaces.c α * z)]
      have h2 : 20 / z * (Spaces.c α * z) = 20 * Spaces.c α := by
        field_simp
      rw [h2]
      linarith
    have hL12 : 20 * |L12f f z / z| = (20 / z) * |L12f f z| := by
      rw [abs_div, abs_of_pos hzpos]
      field_simp
    have hσ := sin_half_rpow_sq hα hθ
    have hS2nn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2)) := Real.rpow_nonneg hsin0 _
    have hS0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hsin0 _
    have hG0 : 0 ≤ |DthGam α 0 θ| := abs_nonneg _
    have hL0 : 0 ≤ |L12f f z| := abs_nonneg _
    have hD0 : 0 ≤ |Spaces.Dth f z θ| := abs_nonneg _
    have hT2 : T2 α f z θ = -(DthGam α 0 θ) * (2 * z / (Spaces.c α * (1 + z) ^ 2))
        * L12f f z := by
      rw [T2]
      rw [show DthGam α z θ = DthGam α 0 θ from by rw [DthGam_eq, DthGam_eq]]
    rw [hT2, show thetaW α z θ = Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      from rfl]
    simp only [abs_mul, abs_neg]
    rw [abs_of_nonneg (sq_nonneg (Spaces.w z)), abs_of_nonneg hS0]
    have hstep : |2 * z / (Spaces.c α * (1 + z) ^ 2)| * Spaces.w z ^ 2
        ≤ (20 / z) * Spaces.w z := by
      calc |2 * z / (Spaces.c α * (1 + z) ^ 2)| * Spaces.w z ^ 2
          = (|2 * z / (Spaces.c α * (1 + z) ^ 2)| * Spaces.w z) * Spaces.w z := by ring
        _ ≤ (20 / z) * Spaces.w z := mul_le_mul_of_nonneg_right hkey hw0
    have e1 : |DthGam α 0 θ| * |2 * z / (Spaces.c α * (1 + z) ^ 2)| * |L12f f z|
          * |Spaces.Dth f z θ| * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
        = (|2 * z / (Spaces.c α * (1 + z) ^ 2)| * Spaces.w z ^ 2)
          * (|DthGam α 0 θ| * |L12f f z| * |Spaces.Dth f z θ|
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by ring
    have e2 : |DthGam α 0 θ| * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))
          * (20 * |L12f f z / z|)
          * (|Spaces.Dth f z θ| * Spaces.w z * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2)))
        = ((20 / z) * Spaces.w z)
          * (|DthGam α 0 θ| * |L12f f z| * |Spaces.Dth f z θ|
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by
      rw [hL12, ← hσ]
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hstep
      (mul_nonneg (mul_nonneg (mul_nonneg hG0 hL0) hD0) hS0)

/-! ## The main estimate -/

theorem wip_T2_ge (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (hf : IBP f) (hfH : HardyHyp f) (hΓ2 : GammaPointwiseBnd α) (hi : CoerciveData α f) : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => T2 α f z θ * Spaces.Dth f z θ * thetaW α z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) ∧ -((1 / 14) * EDth α f + 3 * 10 ^ 6 * α * Ef f) ≤ wip (thetaW α) (T2 α f) (Spaces.Dth f) := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  set G : ℝ × ℝ → ℝ := fun p => T2 α f p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2
    with hG
  set Ge : ℝ → ENNReal := fun θ => ENNReal.ofReal (|DthGam α 0 θ|
    * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))) with hGeD
  set Phi : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (|Spaces.Dth f p.1 p.2| * Spaces.w p.1
    * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2))) with hPhiD
  set Psi : ℝ → ENNReal := fun z => ENNReal.ofReal (20 * |L12f f z / z|) with hPsiD
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) = P := by
    rw [hP, Measure.prod_restrict, ← Measure.volume_eq_prod]
  -- ## the energies are nonnegative
  have hEf_nn : 0 ≤ Ef f := by
    rw [Ef, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEDth_nn : 0 ≤ EDth α f := by
    rw [EDth, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEL12z_nn : 0 ≤ EL12z f := by
    rw [EL12z, L2Sqz]
    exact integral_nonneg fun z => sq_nonneg _
  -- ## the Hardy input `(f w)² ∈ L¹` and the bound on `EL12z`
  have hIntP_feta : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
      * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) P := by
    rw [hP, Measure.prod_restrict]
    exact hi.intFeta
  have hfw : IntegrableOn (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [IntegrableOn, hvol]
    refine hIntP_feta.mono' ?_ ?_
    · exact (aesm_f_mul_w hf.smooth).pow 2
    · filter_upwards [ae_prod_Ioo] with p hp
      have hsin : 0 < Real.sin (2 * p.2) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.1]) (by linarith [hp.2, Real.pi_pos])
      have hsig : 1 ≤ (Real.sin (2 * p.2)) ^ (-Spaces.eta) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hsin (Real.sin_le_one _)
          (by simp only [Spaces.eta]; norm_num)
      have hnorm : ‖Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2) p‖
          = (f p.1 p.2 * Spaces.w p.1) ^ 2 := by
        rw [show Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2) p
            = (f p.1 p.2 * Spaces.w p.1) ^ 2 from rfl, Real.norm_of_nonneg (sq_nonneg _)]
      rw [hnorm]
      have hnn : 0 ≤ f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 :=
        mul_nonneg (mul_self_nonneg _) (sq_nonneg _)
      calc (f p.1 p.2 * Spaces.w p.1) ^ 2
          = f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 := by ring
        _ ≤ f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
              * (Real.sin (2 * p.2)) ^ (-Spaces.eta) := by nlinarith [hnn, hsig]
  have hEL12z_le : EL12z f ≤ 16 * Ef f := EL12z_le f hfH hfw
  -- ## a.e. membership
  have hmem : ∀ᵐ p ∂P, p.1 ∈ Spaces.Iz ∧ p.2 ∈ Spaces.Iθ := by
    rw [hP]
    exact ae_prod_mem
  have hIoo : ∀ᵐ p ∂P, p.2 ∈ Set.Ioo 0 (π / 2) := by
    rw [hP]
    exact ae_prod_Ioo
  -- ## a.e. strong measurability
  have hG_aesm : AEStronglyMeasurable G P := by
    rw [hP, hG]
    exact aesm_T2G α f hf.smooth hfH
  -- ## aemeasurability of the three factors
  have hGe_aem : AEMeasurable Ge (volume.restrict Spaces.Iθ) := by
    rw [hGeD]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((measurable_DthGam α).abs).mul
        ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _)).aemeasurable
  have hPhi_aem : AEMeasurable Phi P := by
    rw [hPhiD, hP]
    apply ENNReal.measurable_ofReal.comp_aemeasurable
    have hDth : AEMeasurable (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
      have hcont : ContinuousOn (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
        have hpth := continuousOn_pth_quad hf.smooth
        have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
        exact hsin.mul hpth
      exact (Spaces.aesm_of_continuousOn_Qd _ hcont).aemeasurable
    have hw : AEMeasurable (fun p : ℝ × ℝ => Spaces.w p.1)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
      have hm : Measurable (fun z : ℝ => Spaces.w z) := by
        show Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
        exact (measurable_const.add measurable_id).pow_const 2 |>.div (measurable_id.pow_const 2)
      exact AEMeasurable.comp_fst hm.aemeasurable
    have hsig : AEMeasurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2)))
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) :=
      AEMeasurable.comp_snd
        ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _).aemeasurable
    exact (hDth.abs.mul hw).mul hsig
  have hPsi_aem : AEMeasurable Psi (volume.restrict Spaces.Iz) := by
    rw [hPsiD]
    have hcont : ContinuousOn (fun z : ℝ => L12f f z / z) (Set.Ioi (0 : ℝ)) :=
      (L12f_continuousOn f hfH).div continuousOn_id (fun z hz => ne_of_gt hz)
    have h1 : AEMeasurable (fun z : ℝ => L12f f z / z) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable
    have h2 : volume.restrict Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [Spaces.Iz]
      exact (Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [h2]
    exact ENNReal.measurable_ofReal.comp_aemeasurable ((h1.abs).const_mul 20)
  -- ## the lintegrals of the three factors
  have hGeval : (∫⁻ θ, Ge θ ^ 2 ∂(volume.restrict Spaces.Iθ)) ≤ ENNReal.ofReal (100 * α) := by
    rw [hGeD]
    exact DthGam_sq_lintegral_le α hα hα1 hΓ2
  have hPsival : (∫⁻ z, Psi z ^ 2 ∂(volume.restrict Spaces.Iz))
      = ENNReal.ofReal (400 * EL12z f) := by
    rw [hPsiD]
    exact lintegral_radial_eq f hfH
  have hPhival : (∫⁻ p, Phi p ^ 2 ∂P) = ENNReal.ofReal (EDth α f) := by
    rw [hP, hPhiD]
    exact lintegral_Edth_eq α hα f hi
  -- ## the pointwise domination
  have hdom : ∀ᵐ p ∂P, ENNReal.ofReal |G p| ≤ Ge p.2 * Phi p * Psi p.1 := by
    filter_upwards [hmem] with p hp
    obtain ⟨hz, hθ⟩ := hp
    have hsin0 : 0 ≤ Real.sin (2 * p.2) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hA0 : 0 ≤ |DthGam α 0 p.2| * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2)) :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hsin0 _)
    have hB0 : 0 ≤ |Spaces.Dth f p.1 p.2| * Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2)) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (w_nonneg hz))
        (Real.rpow_nonneg hsin0 _)
    have hreal : |G p| ≤ (|DthGam α 0 p.2| * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2)))
        * (|Spaces.Dth f p.1 p.2| * Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2)))
        * (20 * |L12f f p.1 / p.1|) := by
      have h := abs_T2_le' α hα hα1 f hz hθ
      calc |G p| = |T2 α f p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2| := rfl
        _ ≤ |DthGam α 0 p.2| * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2))
              * (20 * |L12f f p.1 / p.1|)
              * (|Spaces.Dth f p.1 p.2| * Spaces.w p.1
                * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2))) := h
        _ = (|DthGam α 0 p.2| * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2)))
              * (|Spaces.Dth f p.1 p.2| * Spaces.w p.1
                * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2)))
              * (20 * |L12f f p.1 / p.1|) := by ring
    refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
    rw [hGeD, hPhiD, hPsiD]
    rw [ENNReal.ofReal_mul (mul_nonneg hA0 hB0), ENNReal.ofReal_mul hA0]
  -- ## the tensor Cauchy–Schwarz
  have hGe_top : (∫⁻ θ, Ge θ ^ 2 ∂(volume.restrict Spaces.Iθ)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hGeval ENNReal.ofReal_lt_top)
  have hPsi_top : ∀ z, Psi z ≠ ⊤ := fun z => by rw [hPsiD]; exact ENNReal.ofReal_ne_top
  have hHold := tensor_holder_ennreal' (μ := volume.restrict Spaces.Iz)
    (ν := volume.restrict Spaces.Iθ) Ge Phi Psi hPsi_top hGe_top hGe_aem hPhi_aem hPsi_aem
  have hb1 : ∫⁻ p, ENNReal.ofReal |G p| ∂P ≤ ∫⁻ p, Ge p.2 * Phi p * Psi p.1 ∂P :=
    lintegral_mono_ae hdom
  have hb2 : ∫⁻ p, Ge p.2 * Phi p * Psi p.1 ∂P
      ≤ (∫⁻ θ, Ge θ ^ 2 ∂(volume.restrict Spaces.Iθ)) ^ ((1 : ℝ) / 2)
        * (∫⁻ p, Phi p ^ 2 ∂P) ^ ((1 : ℝ) / 2)
        * (∫⁻ z, Psi z ^ 2 ∂(volume.restrict Spaces.Iz)) ^ ((1 : ℝ) / 2) := by
    rw [← hP] at hHold
    exact hHold
  -- ## the numerical value of the bound
  have hfin : ∫⁻ p, ENNReal.ofReal |G p| ∂P
      ≤ ENNReal.ofReal (10 * Real.sqrt α) * ENNReal.ofReal (Real.sqrt (EDth α f))
        * ENNReal.ofReal (80 * Real.sqrt (Ef f)) := by
    refine le_trans (le_trans hb1 hb2) ?_
    have hA : (∫⁻ θ, Ge θ ^ 2 ∂(volume.restrict Spaces.Iθ)) ^ ((1 : ℝ) / 2)
        ≤ ENNReal.ofReal (10 * Real.sqrt α) := by
      refine le_trans (ENNReal.rpow_le_rpow hGeval (by norm_num)) ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ 100 * α)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num]
      rw [sqrt_sq_mul (by norm_num : (0 : ℝ) ≤ 10) hα.le]
    have hC : (∫⁻ p, Phi p ^ 2 ∂P) ^ ((1 : ℝ) / 2)
        ≤ ENNReal.ofReal (Real.sqrt (EDth α f)) := by
      rw [hPhival, ENNReal.ofReal_rpow_of_nonneg hEDth_nn (by norm_num : (0 : ℝ) ≤ 1 / 2),
        Real.sqrt_eq_rpow]
    have hB : (∫⁻ z, Psi z ^ 2 ∂(volume.restrict Spaces.Iz)) ^ ((1 : ℝ) / 2)
        ≤ ENNReal.ofReal (80 * Real.sqrt (Ef f)) := by
      rw [hPsival]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ 400 * EL12z f)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [show (400 : ℝ) = 20 ^ 2 by norm_num]
      rw [sqrt_sq_mul (by norm_num : (0 : ℝ) ≤ 20) hEL12z_nn]
      have hEL : Real.sqrt (EL12z f) ≤ 4 * Real.sqrt (Ef f) := by
        have h4 : (4 * Real.sqrt (Ef f)) ^ 2 = 16 * Ef f := by
          rw [mul_pow, Real.sq_sqrt hEf_nn]
          norm_num
        calc Real.sqrt (EL12z f) ≤ Real.sqrt ((4 * Real.sqrt (Ef f)) ^ 2) := by
              apply Real.sqrt_le_sqrt
              rw [h4]
              linarith
          _ = 4 * Real.sqrt (Ef f) := Real.sqrt_sq (by positivity)
      apply ENNReal.ofReal_le_ofReal
      linarith
    exact mul_le_mul' (mul_le_mul' hA hC) hB
  have hne : ENNReal.ofReal (10 * Real.sqrt α) * ENNReal.ofReal (Real.sqrt (EDth α f))
      * ENNReal.ofReal (80 * Real.sqrt (Ef f)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  -- ## integrability of the integrand
  have hIntG : Integrable G P := by
    refine ⟨hG_aesm, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have heq : (∫⁻ p, ENNReal.ofReal ‖G p‖ ∂P) = ∫⁻ p, ENNReal.ofReal |G p| ∂P :=
      lintegral_congr_ae (Filter.Eventually.of_forall fun p => by simp only [Real.norm_eq_abs])
    rw [heq]
    exact lt_of_le_of_lt hfin (lt_top_iff_ne_top.mpr hne)
  -- ## the value bound
  have hIntOn : IntegrableOn (Function.uncurry (fun z θ => T2 α f z θ * Spaces.Dth f z θ
      * thetaW α z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [IntegrableOn, hvol]
    exact hIntG
  have hwip_eq : wip (thetaW α) (T2 α f) (Spaces.Dth f) = ∫ p, G p ∂P := by
    rw [wip_eq_integral_prod (thetaW α) (T2 α f) (Spaces.Dth f) hIntOn, ← hP]
  have hAbs1 : |wip (thetaW α) (T2 α f) (Spaces.Dth f)| ≤ (∫⁻ p, ENNReal.ofReal |G p| ∂P).toReal := by
    rw [hwip_eq]
    have h1 : |∫ p, G p ∂P| ≤ ∫ p, |G p| ∂P := MeasureTheory.abs_integral_le_integral_abs
    have h2 : (∫ p, |G p| ∂P) = (∫⁻ p, ENNReal.ofReal |G p| ∂P).toReal := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntG.abs
        (Filter.Eventually.of_forall fun p => abs_nonneg _)]
      exact (ENNReal.toReal_ofReal (integral_nonneg fun p => abs_nonneg _)).symm
    linarith
  have htr : (∫⁻ p, ENNReal.ofReal |G p| ∂P).toReal
      ≤ 800 * Real.sqrt α * Real.sqrt (Ef f) * Real.sqrt (EDth α f) := by
    have h1 := ENNReal.toReal_mono hne hfin
    have h2 : (ENNReal.ofReal (10 * Real.sqrt α) * ENNReal.ofReal (Real.sqrt (EDth α f))
        * ENNReal.ofReal (80 * Real.sqrt (Ef f))).toReal
        = 10 * Real.sqrt α * Real.sqrt (EDth α f) * (80 * Real.sqrt (Ef f)) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (Real.sqrt_nonneg α)),
        ENNReal.toReal_ofReal (Real.sqrt_nonneg (EDth α f)),
        ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (Real.sqrt_nonneg (Ef f)))]
    rw [h2] at h1
    have h3 : 10 * Real.sqrt α * Real.sqrt (EDth α f) * (80 * Real.sqrt (Ef f))
        ≤ 800 * Real.sqrt α * Real.sqrt (Ef f) * Real.sqrt (EDth α f) := by
      nlinarith [Real.sqrt_nonneg α, Real.sqrt_nonneg (Ef f), Real.sqrt_nonneg (EDth α f)]
    linarith
  have hMain : |wip (thetaW α) (T2 α f) (Spaces.Dth f)|
      ≤ 800 * Real.sqrt α * Real.sqrt (Ef f) * Real.sqrt (EDth α f) :=
    le_trans hAbs1 htr
  -- ## Young's inequality
  have hAMGM : 800 * Real.sqrt α * Real.sqrt (Ef f) * Real.sqrt (EDth α f)
      ≤ (1 / 14) * EDth α f + 3 * 10 ^ 6 * α * Ef f := by
    have hy := amgm_sqrt (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 800)
      (Real.sqrt_nonneg α)) (Real.sqrt_nonneg (Ef f))) hEDth_nn
    have hsq : ((800 : ℝ) * Real.sqrt α * Real.sqrt (Ef f)) ^ 2 = 640000 * α * Ef f := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hα.le, Real.sq_sqrt hEf_nn]
      norm_num
    have hαEf : 0 ≤ α * Ef f := mul_nonneg hα.le hEf_nn
    nlinarith [hy, hsq, hαEf]
  constructor
  · rw [IntegrableOn, hvol]
    exact hIntG
  · have h1 : -(800 * Real.sqrt α * Real.sqrt (Ef f) * Real.sqrt (EDth α f))
        ≤ wip (thetaW α) (T2 α f) (Spaces.Dth f) := by
      have h2 := neg_abs_le (wip (thetaW α) (T2 α f) (Spaces.Dth f))
      linarith
    linarith

end Work.Coercivity
