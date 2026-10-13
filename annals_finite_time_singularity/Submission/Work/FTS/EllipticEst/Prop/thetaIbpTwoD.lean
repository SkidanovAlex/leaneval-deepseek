/-
Copyright: work module for the Elgindi finite-time singularity project.

# The two-dimensional angular integration by parts

The lemma `thetaIbpTwoD` is the `z`-integrated form of the angular integration by parts
`angIbpWild` (with the weight `sin(2θ)^{2-γ}`) applied to the angular slices `θ ↦ D_z G z θ`
of a function `G` which is smooth on the open quadrant `(0,∞) × (0,π/2)`.

The route is:

* `sliceIbpTwoD` : the identity for a *single* slice `z > 0` — the four integrability
  hypotheses of `angIbpWild` on `Iθ` plus the two boundary conditions at `θ = 0⁺` and
  `θ = (π/2)⁻` — obtained from `angIbpWild` applied to `g θ = w z * D_z G z θ` (the constant
  factor `w z` is what produces the radial weight `w z ^ 2` inside the angular integrals),
  using the Clairaut identities `pth (Dz G) = Dz (pth G)` and
  `pthIter 2 (Dz G) = Dz (pthIter 2 G)` on the open quadrant;
* the slice integrability hypotheses for a.e. `z` come from the integrability of the
  four integrands on the product `Iz ×ˢ Iθ` (Fubini, `Integrable.prod_right_ae`);
* the a.e. slice identities are then integrated in `z` (Fubini + linearity of the integral).

-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Prop.angIbpWild

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-! ## Measurability/absolute-continuity helpers for the angular interval `Iθ` -/

/-- Two functions which agree on the *open* interval `(0, π/2)` agree almost everywhere for the
restriction of Lebesgue measure to `Iθ = [0, π/2]` (they may differ at the two endpoints). -/
theorem ae_eq_top_Iθ {f g : ℝ → ℝ} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f θ = g θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), θ ∈ Work.Spaces.Iθ → f θ = g θ := by
  rw [MeasureTheory.ae_iff]
  have hle : {θ : ℝ | ¬(θ ∈ Work.Spaces.Iθ → f θ = g θ)} ⊆ ({0} ∪ {Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    simp only [Set.mem_ofPred_eq, not_imp, Work.Spaces.Iθ, Set.mem_Icc] at hθ
    obtain ⟨⟨h1, h2⟩, hne⟩ := hθ
    by_contra hc
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hc
    exact hne (h θ ⟨lt_of_le_of_ne h1 (Ne.symm hc.1), lt_of_le_of_ne h2 hc.2⟩)
  refine measure_mono_null hle ?_
  exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))

/-- Version of `ae_eq_top_Iθ` for the restricted measure on `Iθ`. -/
theorem ae_restrict_Iθ {f g : ℝ → ℝ} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f θ = g θ) :
    f =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] g := by
  show ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))), f θ = g θ
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  exact ae_eq_top_Iθ h

/-- Two functions which agree on the open interval `(0, π/2)` have the same integral over `Iθ`. -/
theorem setIntegral_Iθ_congr {f g : ℝ → ℝ} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f θ = g θ) :
    ∫ θ in Work.Spaces.Iθ, f θ = ∫ θ in Work.Spaces.Iθ, g θ :=
  MeasureTheory.setIntegral_congr_ae measurableSet_Icc (ae_eq_top_Iθ h)

/-- **Fubini for the domain `Iz ×ˢ Iθ`** (stated for the ambient Lebesgue measure on `ℝ × ℝ`). -/
theorem setIntegral_prod_IzIθ (F : ℝ × ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, F p
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F (z, θ) :=
  MeasureTheory.setIntegral_prod F hF

/-- Integrability on the product gives integrability of almost every angular slice. -/
theorem ae_integrableOn_slice_of_integrableOn_prod {F : ℝ × ℝ → ℝ} {s t : Set ℝ}
    (hF : MeasureTheory.IntegrableOn F (s ×ˢ t)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict s),
      MeasureTheory.IntegrableOn (fun θ => F (z, θ)) t := by
  have hF' : MeasureTheory.Integrable F
      ((MeasureTheory.volume.restrict s).prod (MeasureTheory.volume.restrict t)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hF
  exact MeasureTheory.Integrable.prod_right_ae hF'

/-- Integrability on the product gives integrability of the `z`-integrated slices. -/
theorem integrable_slice_integral {F : ℝ × ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, F (z, θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hF' : MeasureTheory.Integrable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hF
  exact MeasureTheory.Integrable.integral_prod_left hF'

/-- Almost every point of `Iz = [0,∞)` is positive. -/
theorem ae_pos_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
  rw [MeasureTheory.ae_iff]
  have hset : {a : ℝ | ¬(0 < a)} = Set.Iic (0 : ℝ) := by ext a; exact not_lt
  rw [hset, show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
    MeasureTheory.Measure.restrict_apply measurableSet_Iic]
  have h0 : Set.Iic (0 : ℝ) ∩ Set.Ici (0 : ℝ) = ({0} : Set ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici, Set.mem_singleton_iff]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h ▸ le_rfl, h ▸ le_rfl⟩⟩
  rw [h0]
  exact measure_singleton 0

/-! ## Slice smoothness and the Clairaut identities on the open quadrant -/

/-- The angular slice of a function which is `C^n` on the open quadrant is `C^n` on `(0,π/2)`. -/
theorem thetaSlice_contDiffOn {G : ℝ → ℝ → ℝ} {n : ℕ}
    (hjoint : ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z) : ContDiffOn ℝ n (fun θ => G z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hp : ContDiffOn ℝ n (fun θ : ℝ => (z, θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
  have h2 := hjoint.comp hp (fun θ hθ => ⟨hz, hθ⟩)
  simpa [Function.comp_def, Function.uncurry] using h2

/-- **Clairaut for `∂_θ` and `D_z`**: `∂_θ (D_z G) = D_z (∂_θ G)` on the open quadrant. -/
theorem pth_Dz_eq_of_smooth {G : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.pth (Work.Spaces.Dz G) z θ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall G).mp hS 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds h)
  have h1 : Work.Spaces.pth (Work.Spaces.Dz G) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz G) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz G z θ') θ = z * Work.Spaces.pth (Work.Spaces.pz G) z θ
    rw [deriv_const_mul_field]
    rfl
  rw [h1, ← Work.Spaces.pz_pth_comm hcd]
  rfl

/-- **Clairaut for `∂_θ²` and `D_z`**: `∂_θ² (D_z G) = D_z (∂_θ² G)` on the open quadrant. -/
theorem pthIter2_Dz_eq_of_smooth {G : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ := by
  have hev1 : ∀ᶠ y in 𝓝 (z, θ), y ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.eventually_mem h
  have hslice : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
    (Continuous.prodMk_right z).continuousAt.eventually hev1
  have hev : (fun θ' => Work.Spaces.pth (Work.Spaces.Dz G) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.Dz (Work.Spaces.pth G) z θ') := by
    filter_upwards [hslice] with θ' hθ'
    exact pth_Dz_eq_of_smooth hS (Work.FTS.EllipticEst.mem_Q0.mp hθ')
  have h2 : Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ
      = Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.pth G)) z θ :=
    EventuallyEq.deriv_eq hev
  rw [h2, pth_Dz_eq_of_smooth hS.pth h]
  rfl

/-! ## The slicewise identity -/

set_option linter.unusedVariables false in
/-- **The angular integration by parts on a single slice** `θ ↦ D_z G z θ`, `z > 0`, with the
weight `sin(2θ)^{2-γ}` and the radial weight `w z ^ 2` carried inside the angular integrals. -/
theorem sliceIbpTwoD {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ < 2) {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z)
    (i0 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (i1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dz G z θ
      * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ
      * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (i2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.Dz G z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (i3 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.Dz G z θ) ^ 2
      * (Real.cot (2 * θ)) ^ 2 * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (b0 : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
      * (Work.Spaces.Dz G z θ * Work.Spaces.pth (Work.Spaces.Dz G) z θ
        - (2 - γ) * Real.cot (2 * θ) * (Work.Spaces.Dz G z θ) ^ 2))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (b1 : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
      * (Work.Spaces.Dz G z θ * Work.Spaces.pth (Work.Spaces.Dz G) z θ
        - (2 - γ) * Real.cot (2 * θ) * (Work.Spaces.Dz G z θ) ^ 2))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      = -(∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
            * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ
            * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        - 2 * (2 - γ) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        - 2 * (2 - γ) * (γ - 1) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
            * (Real.cot (2 * θ)) ^ 2 * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - γ)) := by
  have hp : (2:ℝ) - γ < 1 := by linarith
  have hS : Work.FTS.EllipticEst.SmoothOpen G := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hDzj : ContDiffOn ℝ 2 (fun θ => Work.Spaces.Dz G z θ) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    thetaSlice_contDiffOn
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.Dz G)).mp hS.Dz 2) hz
  set g : ℝ → ℝ := fun θ => Work.Spaces.w z * Work.Spaces.Dz G z θ with hgdef
  have hgval : ∀ θ, g θ = Work.Spaces.w z * Work.Spaces.Dz G z θ := fun θ => by rw [hgdef]
  have hderivg : ∀ θ, deriv g θ = Work.Spaces.w z * Work.Spaces.pth (Work.Spaces.Dz G) z θ := by
    intro θ; rw [hgdef]; exact deriv_const_mul_field _
  have hdgfun : deriv g = fun θ => Work.Spaces.w z * Work.Spaces.pth (Work.Spaces.Dz G) z θ :=
    funext hderivg
  have hderiv2g : ∀ θ, deriv (deriv g) θ
      = Work.Spaces.w z * Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ := by
    intro θ; rw [hdgfun]; exact deriv_const_mul_field _
  have hg : ContDiffOn ℝ 2 g (Set.Ioo (0:ℝ) (Real.pi/2)) := by
    rw [hgdef]; exact contDiffOn_const.mul hDzj
  have hI : MeasureTheory.IntegrableOn
      (fun θ => deriv g θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ := by
    refine i0.congr ?_
    refine ae_restrict_Iθ (fun θ hθ => ?_)
    rw [hderivg, pth_Dz_eq_of_smooth hS (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)]
    ring
  have hP : MeasureTheory.IntegrableOn
      (fun θ => g θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ := by
    have hfun : (fun θ => g θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        = (fun θ => (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - γ)) := by
      funext θ; rw [hgval]; ring
    rw [hfun]; exact i2
  have hJ : MeasureTheory.IntegrableOn
      (fun θ => g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ := by
    refine i1.congr ?_
    refine ae_restrict_Iθ (fun θ hθ => ?_)
    rw [hderiv2g, hgval,
      pthIter2_Dz_eq_of_smooth hS (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)]
    ring
  have hC : MeasureTheory.IntegrableOn
      (fun θ => g θ ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      Work.Spaces.Iθ := by
    have hfun : (fun θ => g θ ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        = (fun θ => (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
            * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) := by
      funext θ; rw [hgval]; ring
    rw [hfun]; exact i3
  have hb0 : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
      * (g θ * deriv g θ - (2 - γ) * Real.cot (2 * θ) * (g θ) ^ 2))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := b0.const_mul ((Work.Spaces.w z) ^ 2)
    rw [mul_zero] at h
    have hfun : (fun θ => (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (2 - γ)
        * (Work.Spaces.Dz G z θ * Work.Spaces.pth (Work.Spaces.Dz G) z θ
          - (2 - γ) * Real.cot (2 * θ) * (Work.Spaces.Dz G z θ) ^ 2)))
        = (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
          * (g θ * deriv g θ - (2 - γ) * Real.cot (2 * θ) * (g θ) ^ 2)) := by
      funext θ; rw [hgval, hderivg]; ring
    rwa [hfun] at h
  have hb1 : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
      * (g θ * deriv g θ - (2 - γ) * Real.cot (2 * θ) * (g θ) ^ 2))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h := b1.const_mul ((Work.Spaces.w z) ^ 2)
    rw [mul_zero] at h
    have hfun : (fun θ => (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (2 - γ)
        * (Work.Spaces.Dz G z θ * Work.Spaces.pth (Work.Spaces.Dz G) z θ
          - (2 - γ) * Real.cot (2 * θ) * (Work.Spaces.Dz G z θ) ^ 2)))
        = (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
          * (g θ * deriv g θ - (2 - γ) * Real.cot (2 * θ) * (g θ) ^ 2)) := by
      funext θ; rw [hgval, hderivg]; ring
    rwa [hfun] at h
  have hang := angIbpWild (p := 2 - γ) hp g hg hI hP hJ hC hb0 hb1
  have hA : (∫ θ in Work.Spaces.Iθ, deriv g θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) :=
    setIntegral_Iθ_congr (fun θ hθ => by
      rw [hderivg, pth_Dz_eq_of_smooth hS (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)]
      ring)
  have hB : (∫ θ in Work.Spaces.Iθ, g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ (2 - γ))
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) :=
    setIntegral_Iθ_congr (fun θ hθ => by
      rw [hderiv2g, hgval,
        pthIter2_Dz_eq_of_smooth hS (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)]
      ring)
  have hC' : (∫ θ in Work.Spaces.Iθ, g θ ^ 2 * (Real.cot (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - γ))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) :=
    setIntegral_Iθ_congr (fun θ hθ => by rw [hgval]; ring)
  have hD : (∫ θ in Work.Spaces.Iθ, g θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) :=
    setIntegral_Iθ_congr (fun θ hθ => by rw [hgval]; ring)
  rw [hA, hB, hC', hD] at hang
  rw [show (1:ℝ) - (2 - γ) = γ - 1 by ring] at hang
  exact hang

/-! ## The two-dimensional identity -/

theorem thetaIbpTwoD {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ < 2) {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)))
    (hI0 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.Dz G p.1 p.2) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - γ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hI1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - γ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hI2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Work.Spaces.Dz G p.1 p.2
      * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) p.1 p.2
      * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - γ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hI3 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.Dz G p.1 p.2) ^ 2
      * (Real.cot (2 * p.2)) ^ 2 * (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (2 - γ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hfl0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
        * (Work.Spaces.Dz G z θ * Work.Spaces.pth (Work.Spaces.Dz G) z θ
          - (2 - γ) * Real.cot (2 * θ) * (Work.Spaces.Dz G z θ) ^ 2))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (hfl1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (2 - γ)
        * (Work.Spaces.Dz G z θ * Work.Spaces.pth (Work.Spaces.Dz G) z θ
          - (2 - γ) * Real.cot (2 * θ) * (Work.Spaces.Dz G z θ) ^ 2))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2
          * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - γ))
      = -(∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, Work.Spaces.Dz G p.1 p.2
            * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) p.1 p.2
            * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - γ))
        - 2 * (2 - γ) * (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.Dz G p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (2 - γ))
        - 2 * (2 - γ) * (γ - 1) * (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.Dz G p.1 p.2) ^ 2 * (Real.cot (2 * p.2)) ^ 2 * (Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (2 - γ)) := by
  have hs0 := ae_integrableOn_slice_of_integrableOn_prod hI0
  have hs1 := ae_integrableOn_slice_of_integrableOn_prod hI1
  have hs2 := ae_integrableOn_slice_of_integrableOn_prod hI2
  have hs3 := ae_integrableOn_slice_of_integrableOn_prod hI3
  have hInt0 := integrable_slice_integral hI0
  have hInt2 := integrable_slice_integral hI2
  have hInt3 := integrable_slice_integral hI3
  -- the slicewise identities, almost everywhere in `z`
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        = -(∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
              * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ
              * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
          - 2 * (2 - γ) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
          - 2 * (2 - γ) * (γ - 1) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * (Real.cot (2 * θ)) ^ 2 * (Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - γ)) := by
    filter_upwards [ae_pos_Iz, hs0, hs1, hs2, hs3, hfl0, hfl1] with z hz h0 h1 h2 h3 b0 b1
    exact sliceIbpTwoD hγ hγ2 hsm hz h1 h2 h0 h3 b0 b1
  rw [setIntegral_prod_IzIθ _ hI0, setIntegral_prod_IzIθ _ hI1,
    setIntegral_prod_IzIθ _ hI2, setIntegral_prod_IzIθ _ hI3]
  try simp only []
  rw [MeasureTheory.integral_congr_ae hslice]
  try simp only []
  rw [MeasureTheory.integral_sub
        (f := fun z => - (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
              * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ
              * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
            - 2 * (2 - γ) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)))
        (g := fun z => 2 * (2 - γ) * (γ - 1) * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - γ)))
        (hInt2.neg.sub (hInt0.const_mul (2 * (2 - γ))))
        (hInt3.const_mul (2 * (2 - γ) * (γ - 1)))]
  try simp only []
  rw [MeasureTheory.integral_sub
        (f := fun z => - (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
              * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ
              * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)))
        (g := fun z => 2 * (2 - γ) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)))
        hInt2.neg (hInt0.const_mul (2 * (2 - γ)))]
  try simp only []
  rw [MeasureTheory.integral_neg (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
          * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)),
      MeasureTheory.integral_const_mul (2 * (2 - γ)) (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - γ)),
      MeasureTheory.integral_const_mul (2 * (2 - γ) * (γ - 1)) (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - γ))]
  try simp only []

end Work.FTS.EllipticEst.Prop
