import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.BSSwirl.integrable_prod_inv_norm_mul
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.Spaces.pz_mixed_mul_le_4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FTS.BSSwirl

noncomputable section

/-! ## Translation invariance -/

/-- Translation invariance of the Laplacian (vector valued). -/
theorem laplacian_comp_add_left {Ψ : R3 → R3} (y z : R3) :
    Laplacian.laplacian (fun w => Ψ (y + w)) z = Laplacian.laplacian Ψ (y + z) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (fun w => Ψ (y + w))
        (EuclideanSpace.basisFun (Fin 3) ℝ),
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis Ψ
        (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [iteratedFDeriv_comp_add_left]

/-- Translation invariance of the Laplacian, applied inside an inner product. -/
theorem laplacian_inner_comp_add_left {Ψ : R3 → R3} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (v y z : R3) :
    Laplacian.laplacian (fun w => inner ℝ v (Ψ (y + w))) z
      = inner ℝ v (Laplacian.laplacian Ψ (y + z)) := by
  have hlin : ContDiff ℝ 2 (fun w : R3 => y + w) := by
    simpa using (contDiff_const (c := y)).add (contDiff_id : ContDiff ℝ 2 (id : R3 → R3))
  have hcd : ContDiffAt ℝ 2 (fun w : R3 => Ψ (y + w)) z := by
    have h := (hΨ 2).comp hlin
    simpa [Function.comp_def] using h.contDiffAt
  have h := ContDiffAt.laplacian_CLM_comp_left (l := innerSL ℝ v) hcd
  have hfun : (fun w => inner ℝ v (Ψ (y + w))) = (innerSL ℝ v) ∘ (fun w => Ψ (y + w)) := by
    funext w
    simp only [Function.comp_apply]
    rw [innerSL_apply_apply, real_inner_comm]
  have htr : Laplacian.laplacian (fun w => Ψ (y + w))
      = fun w => Laplacian.laplacian Ψ (y + w) := by
    funext w
    exact laplacian_comp_add_left y w
  rw [hfun, h, htr]
  simp only [Function.comp_apply]
  rw [innerSL_apply_apply, real_inner_comm]


/-- Translation invariance of the (Lebesgue) integral against the singular kernel `‖x - y‖⁻¹`. -/
theorem integral_inv_norm_sub_mul_shift (y : R3) (F : R3 → ℝ) :
    ∫ x, (‖x - y‖)⁻¹ * F x = ∫ z, (‖z‖)⁻¹ * F (y + z) := by
  rw [← MeasureTheory.integral_sub_right_eq_self (fun z : R3 => (‖z‖)⁻¹ * F (y + z)) y]
  congr 1
  funext x
  abel

/-! ## The Laplacian of a vector field

`continuous_laplacian` and `hasCompactSupport_laplacian` of `integral_inv_norm_mul_laplacian` are
stated for *scalar* functions; since the vector Laplacian is defined componentwise (through the
second `iteratedFDeriv`), the vector-valued versions are needed here. -/

/-- The vector Laplacian in the standard basis is the sum of the pure second partial derivatives. -/
theorem laplacian_vec_eq_sum {Ψ : R3 → R3} (hΨ : ContDiff ℝ 2 Ψ) :
    Laplacian.laplacian Ψ = fun z => ∑ i : Fin 3,
      (fderiv ℝ (fun y => fderiv ℝ Ψ y (eb i)) z) (eb i) := by
  have hkey : ∀ (w : R3) (i : Fin 3),
      fderiv ℝ (fun y => fderiv ℝ Ψ y (eb i)) w
        = (fderiv ℝ (fderiv ℝ Ψ) w).flip (eb i) := by
    intro w i
    have h : DifferentiableAt ℝ (fderiv ℝ Ψ) w :=
      (hΨ.fderiv_right (m := 1) (by norm_num)).contDiffAt.differentiableAt (by norm_num)
    have h2 := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ Ψ)
      (u := fun _ : R3 => eb i) h (differentiableAt_const _)
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add] at h2
    exact h2
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis Ψ
        (EuclideanSpace.basisFun (Fin 3) ℝ)]
  funext w
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply, hkey w i]
  rfl

/-- The Laplacian of a `C²` vector field is continuous. -/
theorem continuous_laplacian_vec {Ψ : R3 → R3} (hΨ : ContDiff ℝ 2 Ψ) :
    Continuous (Laplacian.laplacian Ψ) := by
  rw [laplacian_vec_eq_sum hΨ]
  refine continuous_finsetSum _ fun i _ => ?_
  have hg : ContDiff ℝ 1 (fun y : R3 => fderiv ℝ Ψ y (eb i)) :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The support of the Laplacian of a vector field is contained in the support of the field. -/
theorem support_laplacian_vec_subset {Ψ : R3 → R3} :
    Function.support (Laplacian.laplacian Ψ) ⊆ tsupport Ψ := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis Ψ
        (EuclideanSpace.basisFun (Fin 3) ℝ)] at hx
  refine support_iteratedFDeriv_subset (𝕜 := ℝ) (f := Ψ) 2 ?_
  rw [Function.mem_support]
  intro h0
  exact hx (by simp [h0])

/-- The Laplacian of a compactly supported vector field is compactly supported. -/
theorem hasCompactSupport_laplacian_vec {Ψ : R3 → R3} (hc : HasCompactSupport Ψ) :
    HasCompactSupport (Laplacian.laplacian Ψ) :=
  HasCompactSupport.of_support_subset_isCompact hc support_laplacian_vec_subset

/-! ## The fundamental solution, tested against a vector -/

/-- **The inner integral of the Fubini computation.**  For smooth compactly supported `Ψ` and any
`v : ℝ³`,

  `∫ x, ‖x - y‖⁻¹ · ⟪ΔΨ x, v⟫ = -4π ⟪Ψ y, v⟫`.

This is the fundamental solution `∫ ‖z‖⁻¹ Δψ = -4π ψ 0` of the Laplacian
(`integral_inv_norm_mul_laplacian`), applied to the scalar function
`z ↦ ⟪Ψ (y + z), v⟫` after the translation `x = y + z`. -/
theorem integral_sub_inv_norm_mul_laplacian_inner {Ψ : R3 → R3}
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hΨc : HasCompactSupport Ψ) (v y : R3) :
    ∫ x, (‖x - y‖)⁻¹ * inner ℝ (Laplacian.laplacian Ψ x) v
      = -4 * Real.pi * inner ℝ (Ψ y) v := by
  have hflip : ∀ x : R3, (‖x - y‖)⁻¹ * inner ℝ (Laplacian.laplacian Ψ x) v
      = (‖x - y‖)⁻¹ * inner ℝ v (Laplacian.laplacian Ψ x) := fun x =>
    congrArg (fun t : ℝ => (‖x - y‖)⁻¹ * t)
      (real_inner_comm (Laplacian.laplacian Ψ x) v).symm
  rw [show (∫ x, (‖x - y‖)⁻¹ * inner ℝ (Laplacian.laplacian Ψ x) v)
      = ∫ x, (‖x - y‖)⁻¹ * inner ℝ v (Laplacian.laplacian Ψ x) from
    integral_congr_ae (Eventually.of_forall hflip)]
  rw [integral_inv_norm_sub_mul_shift y (fun x => inner ℝ v (Laplacian.laplacian Ψ x))]
  have hlin : ∀ n : ℕ, ContDiff ℝ n (fun z : R3 => y + z) := fun n => by
    simpa using (contDiff_const (c := y)).add (contDiff_id : ContDiff ℝ n (id : R3 → R3))
  have hφsm : ∀ n : ℕ, ContDiff ℝ n (fun z : R3 => inner ℝ v (Ψ (y + z))) := by
    intro n
    have h1 : ContDiff ℝ n (fun z : R3 => Ψ (y + z)) := by
      have h := (hΨ n).comp (hlin n)
      simpa [Function.comp_def] using h
    have hmain : ContDiff ℝ n ((innerSL ℝ v) ∘ (fun z : R3 => Ψ (y + z))) :=
      (innerSL ℝ v).contDiff.comp h1
    simpa [Function.comp_def, innerSL_apply_apply] using hmain
  have hφcs : HasCompactSupport (fun z : R3 => inner ℝ v (Ψ (y + z))) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (fun w : R3 => w - y) '' tsupport Ψ)
      (hΨc.isCompact.image (continuous_id.sub continuous_const)) ?_
    intro w hw
    refine ⟨y + w, subset_tsupport _ ?_, by abel⟩
    rw [Function.mem_support]
    intro h0
    exact (Function.mem_support.mp hw) (by simp [h0])
  have hφlap : ∀ z : R3,
      Laplacian.laplacian (fun z : R3 => inner ℝ v (Ψ (y + z))) z
        = inner ℝ v (Laplacian.laplacian Ψ (y + z)) := fun z =>
    laplacian_inner_comp_add_left hΨ v y z
  rw [show (∫ z, (‖z‖)⁻¹ * inner ℝ v (Laplacian.laplacian Ψ (y + z)))
      = ∫ z, (‖z‖)⁻¹ * Laplacian.laplacian (fun z : R3 => inner ℝ v (Ψ (y + z))) z from
    integral_congr_ae (Eventually.of_forall fun z => by
      dsimp only
      rw [hφlap z])]
  rw [integral_inv_norm_mul_laplacian hφsm hφcs]
  congr 1
  simp only [add_zero]
  exact real_inner_comm (Ψ y) v

/-! ## Joint integrability of the double integrand -/

/-- **Joint integrability.**  For bounded, a.e. strongly measurable `ω` supported in
`closedBall 0 R` and smooth compactly supported `Ψ`, the integrand
`(x, y) ↦ ‖x - y‖⁻¹ · ⟪ΔΨ x, ω y⟫` is `L¹(volume.prod volume)`.  It is dominated by
`M · sup ‖ΔΨ‖ · ‖x - y‖⁻¹` on `tsupport (ΔΨ) × closedBall 0 R`, and the Newtonian kernel is `L¹`
there (`integrable_prod_inv_norm_mul`). -/
theorem integrable_prod_inv_norm_mul_laplacian_inner {ω : R3 → R3} {R M : ℝ} (_hR : 0 ≤ R)
    (_hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    {Ψ : R3 → R3} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hΨc : HasCompactSupport Ψ) :
    Integrable (Function.uncurry
      (fun x y : R3 => (‖x - y‖)⁻¹ * inner ℝ (Laplacian.laplacian Ψ x) (ω y)))
      (volume.prod volume) := by
  have hΨ2 : ContDiff ℝ 2 Ψ := hΨ 2
  have hΔcont : Continuous (Laplacian.laplacian Ψ) := continuous_laplacian_vec hΨ2
  have hΔcs : HasCompactSupport (Laplacian.laplacian Ψ) := hasCompactSupport_laplacian_vec hΨc
  obtain ⟨C₁, hC₁⟩ := hΔcont.bounded_above_of_compact_support hΔcs
  have hC₁0 : 0 ≤ C₁ := le_trans (norm_nonneg _) (hC₁ 0)
  have hgmeas : AEStronglyMeasurable
      (fun p : R3 × R3 => inner ℝ (Laplacian.laplacian Ψ p.1) (ω p.2))
      (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : R3 × R3 => Laplacian.laplacian Ψ p.1)
        (volume.prod volume) := (hΔcont.comp continuous_fst).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : R3 × R3 => ω p.2) (volume.prod volume) :=
      hmeas.comp_snd
    exact h1.inner h2
  have hbdd_g : ∀ p : R3 × R3, ‖inner ℝ (Laplacian.laplacian Ψ p.1) (ω p.2)‖ ≤ M * C₁ := by
    intro p
    calc ‖inner ℝ (Laplacian.laplacian Ψ p.1) (ω p.2)‖
        ≤ ‖Laplacian.laplacian Ψ p.1‖ * ‖ω p.2‖ := norm_inner_le_norm _ _
      _ ≤ C₁ * M := mul_le_mul (hC₁ p.1) (hbdd p.2) (norm_nonneg _) hC₁0
      _ = M * C₁ := by ring
  have hsupp_g : ∀ p : R3 × R3, inner ℝ (Laplacian.laplacian Ψ p.1) (ω p.2) ≠ 0 →
      p.1 ∈ tsupport (Laplacian.laplacian Ψ) ∧ p.2 ∈ Metric.closedBall 0 R := by
    intro p hp
    constructor
    · by_contra hx
      rw [notMem_tsupport_iff_eventuallyEq] at hx
      have h0 : Laplacian.laplacian Ψ p.1 = 0 := hx.eq_of_nhds
      rw [h0, inner_zero_left] at hp
      exact hp rfl
    · by_contra hy
      have h0 : ω p.2 = 0 := by
        by_contra hne
        exact hy (hsupp _ hne)
      rw [h0, inner_zero_right] at hp
      exact hp rfl
  exact integrable_prod_inv_norm_mul (g := fun p : R3 × R3 =>
      inner ℝ (Laplacian.laplacian Ψ p.1) (ω p.2))
    hgmeas (C := M * C₁) (K := tsupport (Laplacian.laplacian Ψ))
    (L := Metric.closedBall 0 R) hΔcs.isCompact (isCompact_closedBall 0 R) hbdd_g hsupp_g

/-! ## The pointwise pairing and the constant -/

/-- **The pointwise pairing.**  For bounded, a.e. strongly measurable `ω` supported in
`closedBall 0 R`,

  `⟪A ω x, ΔΨ x⟫ = (4π)⁻¹ ∫ y, ‖x - y‖⁻¹ · ⟪ΔΨ x, ω y⟫`

for every `x`; consequently the same holds after integrating in `x`.  The continuous linear map
`innerSL ℝ (ΔΨ x)` is moved inside the Bochner integral defining `A ω x`. -/
theorem integral_newtonPotential_inner_laplacian_dev {ω : R3 → R3} {R M : ℝ} (_hR : 0 ≤ R)
    (hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    {Ψ : R3 → R3} (_hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (_hΨc : HasCompactSupport Ψ) :
    (∫ x, inner ℝ (newtonPotential ω x) (Laplacian.laplacian Ψ x))
      = (4 * Real.pi)⁻¹ * ∫ x, ∫ y,
          (‖x - y‖)⁻¹ * inner ℝ (Laplacian.laplacian Ψ x) (ω y) := by
  have hstep1 : ∀ x : R3, inner ℝ (newtonPotential ω x) (Laplacian.laplacian Ψ x)
      = (4 * Real.pi)⁻¹ * ∫ y, (‖x - y‖)⁻¹ * inner ℝ (Laplacian.laplacian Ψ x) (ω y) := by
    intro x
    have hInt : Integrable (fun y : R3 => (‖x - y‖)⁻¹ • ω y) :=
      integrable_inv_norm_smul hM hbdd hsupp hmeas x
    rw [newtonPotential_apply, inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    congr 1
    rw [show inner ℝ (∫ y, (‖x - y‖)⁻¹ • ω y) (Laplacian.laplacian Ψ x)
          = inner ℝ (Laplacian.laplacian Ψ x) (∫ y, (‖x - y‖)⁻¹ • ω y) from
        real_inner_comm _ _]
    simp only [← innerSL_apply_apply]
    rw [← ContinuousLinearMap.integral_comp_comm (innerSL ℝ (Laplacian.laplacian Ψ x)) hInt]
    apply integral_congr_ae
    filter_upwards with y
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [show (∫ x, inner ℝ (newtonPotential ω x) (Laplacian.laplacian Ψ x))
      = ∫ x, (4 * Real.pi)⁻¹ *
          (∫ y, (‖x - y‖)⁻¹ * inner ℝ (Laplacian.laplacian Ψ x) (ω y)) from
    integral_congr_ae (Eventually.of_forall hstep1)]
  rw [MeasureTheory.integral_const_mul]

/-! ## The main identity -/

theorem integral_newtonPotential_laplacian {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    {Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ)
    (hΨc : HasCompactSupport Ψ) :
    ∫ x, inner ℝ (Work.FTS.BSSwirl.newtonPotential ω x) (Laplacian.laplacian Ψ x)
      = - ∫ x, inner ℝ (ω x) (Ψ x) := by
  rw [integral_newtonPotential_inner_laplacian_dev hR hM hbdd hsupp hmeas hΨ hΨc]
  rw [integral_integral_swap
    (integrable_prod_inv_norm_mul_laplacian_inner hR hM hbdd hsupp hmeas hΨ hΨc)]
  rw [show (∫ y, ∫ x, (‖x - y‖)⁻¹ * inner ℝ (Laplacian.laplacian Ψ x) (ω y))
      = ∫ y, (-4 * Real.pi * inner ℝ (Ψ y) (ω y)) from
    integral_congr_ae (Eventually.of_forall fun y =>
      integral_sub_inv_norm_mul_laplacian_inner hΨ hΨc (ω y) y)]
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ y, inner ℝ (Ψ y) (ω y)) = ∫ x, inner ℝ (ω x) (Ψ x) from
    integral_congr_ae (Eventually.of_forall fun y => (real_inner_comm (Ψ y) (ω y)).symm)]
  have h4 : (4 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [inv_mul_eq_iff_eq_mul₀ h4]
  ring

end

end Work.FTS.BSSwirl
