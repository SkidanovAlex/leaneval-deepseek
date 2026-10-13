/-
# `FTS/PhiStar/Honesty/SlotsLimit/IBPsub.Master`

The analytic core of the integration-by-parts argument for the sub-slot operators: the master
integral lemma (`∫_{ℝ²} ∂_z F = 0 = ∫_{ℝ²} ∂_θ F` for `F` of class `C¹` with compact support),
the product rules for `∂_z`/`∂_θ` when one factor is only smooth on the open quadrant, the
integrability and global-`C¹` facts for products with a test function, and the resulting plain
integration-by-parts identities `∫ ∂_z g · ψ = -∫ g · ∂_z ψ` and its `θ`-analogue.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBPsub.Closure

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## 1. The master integral lemma -/

/-- The `z`-slice of a compactly supported function on `ℝ²` is compactly supported. -/
theorem hasCompactSupport_slice_fst {F : ℝ × ℝ → ℝ} (h : HasCompactSupport F) (y : ℝ) :
    HasCompactSupport (fun x : ℝ => F (x, y)) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Prod.fst '' tsupport F) ?_ ?_
  · exact IsCompact.image h continuous_fst
  · intro x hx
    rw [Function.mem_support] at hx
    by_contra hcon
    exact hx ((notMem_tsupport_iff_eventuallyEq.mp
      (fun hmem => hcon ⟨(x, y), hmem, rfl⟩)).eq_of_nhds)

/-- The `θ`-slice of a compactly supported function on `ℝ²` is compactly supported. -/
theorem hasCompactSupport_slice_snd {F : ℝ × ℝ → ℝ} (h : HasCompactSupport F) (x : ℝ) :
    HasCompactSupport (fun y : ℝ => F (x, y)) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Prod.snd '' tsupport F) ?_ ?_
  · exact IsCompact.image h continuous_snd
  · intro y hy
    rw [Function.mem_support] at hy
    by_contra hcon
    exact hy ((notMem_tsupport_iff_eventuallyEq.mp
      (fun hmem => hcon ⟨(x, y), hmem, rfl⟩)).eq_of_nhds)

/-- **The integral of the `z`-derivative of a compactly supported `C¹` function vanishes.**
By Fubini it is the integral over the angles of `∫_z ∂_z F (z,θ) dz`, and each inner integral
vanishes by the one-dimensional fundamental theorem of calculus: the slice is compactly
supported, so its limits at `±∞` are `0`. -/
theorem master_pz_eq_zero {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F))
    (hc : HasCompactSupport (Function.uncurry F)) :
    ∫ p : ℝ × ℝ, Work.Spaces.pz F p.1 p.2 = 0 := by
  have heq : (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry F) p) (1, 0) := by
    funext p
    exact Work.Spaces.pz_eq_fderiv (hF.differentiable_one.differentiableAt)
  have hcont : Continuous (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2) := by
    rw [heq]
    exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcpt : HasCompactSupport (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2) := by
    rw [heq]; exact hc.fderiv_apply ℝ (1, 0)
  have hint : Integrable (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2) :=
    hcont.integrable_of_hasCompactSupport hcpt
  rw [show (volume : MeasureTheory.Measure (ℝ × ℝ))
      = MeasureTheory.Measure.prod (volume : MeasureTheory.Measure ℝ)
          (volume : MeasureTheory.Measure ℝ) from rfl]
  rw [MeasureTheory.integral_prod_symm _ hint]
  have hinner : ∀ θ : ℝ, ∫ z, Work.Spaces.pz F z θ = 0 := by
    intro θ
    have h1 : ContDiff ℝ 1 (fun z : ℝ => F z θ) :=
      hF.comp (contDiff_id.prodMk contDiff_const)
    refine MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun z => F z θ) (f' := fun z => Work.Spaces.pz F z θ) ?_ ?_ ?_
    · intro z
      exact (h1.differentiable_one.differentiableAt (x := z)).hasDerivAt
    · exact (h1.continuous_deriv (le_refl 1)).integrable_of_hasCompactSupport
        (hasCompactSupport_slice_fst hc θ).deriv
    · exact h1.continuous.integrable_of_hasCompactSupport (hasCompactSupport_slice_fst hc θ)
  simp [hinner]

/-- **The integral of the `θ`-derivative of a compactly supported `C¹` function vanishes.** -/
theorem master_pth_eq_zero {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F))
    (hc : HasCompactSupport (Function.uncurry F)) :
    ∫ p : ℝ × ℝ, Work.Spaces.pth F p.1 p.2 = 0 := by
  have heq : (fun p : ℝ × ℝ => Work.Spaces.pth F p.1 p.2)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry F) p) (0, 1) := by
    funext p
    exact Work.Spaces.pth_eq_fderiv (hF.differentiable_one.differentiableAt)
  have hcont : Continuous (fun p : ℝ × ℝ => Work.Spaces.pth F p.1 p.2) := by
    rw [heq]
    exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcpt : HasCompactSupport (fun p : ℝ × ℝ => Work.Spaces.pth F p.1 p.2) := by
    rw [heq]; exact hc.fderiv_apply ℝ (0, 1)
  have hint : Integrable (fun p : ℝ × ℝ => Work.Spaces.pth F p.1 p.2) :=
    hcont.integrable_of_hasCompactSupport hcpt
  rw [show (volume : MeasureTheory.Measure (ℝ × ℝ))
      = MeasureTheory.Measure.prod (volume : MeasureTheory.Measure ℝ)
          (volume : MeasureTheory.Measure ℝ) from rfl]
  rw [MeasureTheory.integral_prod _ hint]
  have hinner : ∀ z : ℝ, ∫ θ, Work.Spaces.pth F z θ = 0 := by
    intro z
    have h1 : ContDiff ℝ 1 (fun θ : ℝ => F z θ) :=
      hF.comp (contDiff_const.prodMk contDiff_id)
    refine MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun θ => F z θ) (f' := fun θ => Work.Spaces.pth F z θ) ?_ ?_ ?_
    · intro θ
      exact (h1.differentiable_one.differentiableAt (x := θ)).hasDerivAt
    · exact (h1.continuous_deriv (le_refl 1)).integrable_of_hasCompactSupport
        (hasCompactSupport_slice_snd hc z).deriv
    · exact h1.continuous.integrable_of_hasCompactSupport (hasCompactSupport_slice_snd hc z)
  simp [hinner]

/-! ## 2. Product rules, continuity and integrability -/

/-- A partial derivative vanishes at a point where the function vanishes on a neighbourhood. -/
theorem pz_eq_zero_of_eventuallyEq_zero {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : Function.uncurry F =ᶠ[𝓝 (z, θ)] 0) : Work.Spaces.pz F z θ = 0 := by
  have h' : HasFDerivAt (Function.uncurry F) (0 : ℝ × ℝ →L[ℝ] ℝ) (z, θ) :=
    (hasFDerivAt_const (0 : ℝ) (z, θ)).congr_of_eventuallyEq h
  rw [Work.Spaces.pz_eq_fderiv h'.differentiableAt, h'.fderiv]
  rfl

/-- A partial derivative vanishes at a point where the function vanishes on a neighbourhood. -/
theorem pth_eq_zero_of_eventuallyEq_zero {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : Function.uncurry F =ᶠ[𝓝 (z, θ)] 0) : Work.Spaces.pth F z θ = 0 := by
  have h' : HasFDerivAt (Function.uncurry F) (0 : ℝ × ℝ →L[ℝ] ℝ) (z, θ) :=
    (hasFDerivAt_const (0 : ℝ) (z, θ)).congr_of_eventuallyEq h
  rw [Work.Spaces.pth_eq_fderiv h'.differentiableAt, h'.fderiv]
  rfl

/-- If `ψ` vanishes at `p` then so does `g · ψ`. -/
theorem mul_eq_zero_of_uncurry_eq_zero {g ψ : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (h : Function.uncurry ψ p = 0) : g p.1 p.2 * ψ p.1 p.2 = 0 := by
  simp only [Function.uncurry] at h
  rw [h, mul_zero]

/-- If `ψ` vanishes at `p` then so does `uncurry (g · ψ)`. -/
theorem uncurry_mul_eq_zero {g ψ : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (h : Function.uncurry ψ p = 0) :
    Function.uncurry (fun z θ => g z θ * ψ z θ) p = 0 := by
  simp only [Function.uncurry] at h ⊢
  rw [h, mul_zero]

/-- The Leibniz rule for `∂_z`, where the first factor is only smooth on the open quadrant and
the second is a test function (so that everything is smooth in a neighbourhood of the support). -/
theorem pz_mul_rule {g ψ : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hψ : TestQ0 ψ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => g z θ * ψ z θ) z θ
      = Work.Spaces.pz g z θ * ψ z θ + g z θ * Work.Spaces.pz ψ z θ := by
  by_cases hp : (z, θ) ∈ Q0
  · have h1 : HasDerivAt (fun z' : ℝ => g z' θ) (Work.Spaces.pz g z θ) z :=
      hg.hasDerivAt_slice hp.2 hp.1
    have h2 : HasDerivAt (fun z' : ℝ => ψ z' θ) (Work.Spaces.pz ψ z θ) z :=
      ((hψ.smooth.comp (contDiff_id.prodMk (contDiff_const (c := θ)))).differentiable
        (by norm_num)).differentiableAt (x := z) |>.hasDerivAt
    exact (h1.mul h2).deriv
  · have hzψ : (z, θ) ∉ tsupport (Function.uncurry ψ) := fun hmem => hp (hψ.tsupp hmem)
    have h0 : Function.uncurry ψ =ᶠ[𝓝 (z, θ)] 0 := notMem_tsupport_iff_eventuallyEq.mp hzψ
    have hψ0 : ψ z θ = 0 := h0.eq_of_nhds
    have hpzψ0 : Work.Spaces.pz ψ z θ = 0 := pz_eq_zero_of_eventuallyEq_zero h0
    have hF0 : Function.uncurry (fun z θ => g z θ * ψ z θ) =ᶠ[𝓝 (z, θ)] 0 := by
      filter_upwards [h0] with p hp'
      exact uncurry_mul_eq_zero hp'
    have hpzF0 : Work.Spaces.pz (fun z θ => g z θ * ψ z θ) z θ = 0 :=
      pz_eq_zero_of_eventuallyEq_zero hF0
    rw [hpzF0, hψ0, hpzψ0]; ring

/-- The Leibniz rule for `∂_θ`, where the first factor is only smooth on the open quadrant and
the second is a test function. -/
theorem pth_mul_rule {g ψ : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hψ : TestQ0 ψ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => g z θ * ψ z θ) z θ
      = Work.Spaces.pth g z θ * ψ z θ + g z θ * Work.Spaces.pth ψ z θ := by
  by_cases hp : (z, θ) ∈ Q0
  · have h1 : HasDerivAt (fun θ' : ℝ => g z θ') (Work.Spaces.pth g z θ) θ :=
      (hg.curry_θ hp.1).differentiableOn (by simp) |>.differentiableAt
        (isOpen_Ioo.mem_nhds hp.2) |>.hasDerivAt
    have h2 : HasDerivAt (fun θ' : ℝ => ψ z θ') (Work.Spaces.pth ψ z θ) θ :=
      ((hψ.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable
        (by norm_num)).differentiableAt (x := θ) |>.hasDerivAt
    exact (h1.mul h2).deriv
  · have hzψ : (z, θ) ∉ tsupport (Function.uncurry ψ) := fun hmem => hp (hψ.tsupp hmem)
    have h0 : Function.uncurry ψ =ᶠ[𝓝 (z, θ)] 0 := notMem_tsupport_iff_eventuallyEq.mp hzψ
    have hψ0 : ψ z θ = 0 := h0.eq_of_nhds
    have hpthψ0 : Work.Spaces.pth ψ z θ = 0 := pth_eq_zero_of_eventuallyEq_zero h0
    have hF0 : Function.uncurry (fun z θ => g z θ * ψ z θ) =ᶠ[𝓝 (z, θ)] 0 := by
      filter_upwards [h0] with p hp'
      exact uncurry_mul_eq_zero hp'
    have hpthF0 : Work.Spaces.pth (fun z θ => g z θ * ψ z θ) z θ = 0 :=
      pth_eq_zero_of_eventuallyEq_zero hF0
    rw [hpthF0, hψ0, hpthψ0]; ring

/-- The partial `z`-derivative of a globally `C^∞` function is continuous. -/
theorem continuous_pz_of_contDiff {Ψ : ℝ → ℝ → ℝ}
    (h : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)) :
    Continuous (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2) := by
  have hdiff : Differentiable ℝ (Function.uncurry Ψ) :=
    h.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have heq : (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry Ψ) p) (1, 0) := by
    funext p; exact Work.Spaces.pz_eq_fderiv (hdiff p)
  rw [heq]
  exact (h.continuous_fderiv (by rw [Work.Stability.smoothOrder]; simp)).clm_apply
    continuous_const

/-- The partial `θ`-derivative of a globally `C^∞` function is continuous. -/
theorem continuous_pth_of_contDiff {Ψ : ℝ → ℝ → ℝ}
    (h : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)) :
    Continuous (fun p : ℝ × ℝ => Work.Spaces.pth Ψ p.1 p.2) := by
  have hdiff : Differentiable ℝ (Function.uncurry Ψ) :=
    h.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have heq : (fun p : ℝ × ℝ => Work.Spaces.pth Ψ p.1 p.2)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry Ψ) p) (0, 1) := by
    funext p; exact Work.Spaces.pth_eq_fderiv (hdiff p)
  rw [heq]
  exact (h.continuous_fderiv (by rw [Work.Stability.smoothOrder]; simp)).clm_apply
    continuous_const

/-- A function which is continuous on the (compact) closed support of a test function and
vanishes outside it is integrable. -/
theorem integrable_of_continuousOn_tsupport_test {H : ℝ × ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    (hψ : TestQ0 ψ) (hcont : ContinuousOn H (tsupport (Function.uncurry ψ)))
    (hsub : Function.support H ⊆ tsupport (Function.uncurry ψ)) :
    Integrable H (volume : MeasureTheory.Measure (ℝ × ℝ)) :=
  (hcont.integrableOn_compact hψ.cpt).integrable_of_forall_notMem_eq_zero (fun p hp => by
    by_contra hne
    exact hp (hsub (Function.mem_support.mpr hne)))

/-- The product of a function smooth on the open quadrant with a test function is globally `C¹`:
inside the quadrant it is a product of smooth functions, and outside the support of the test
function it vanishes identically. -/
theorem contDiff_one_mul_test {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ContDiff ℝ 1 (Function.uncurry (fun z θ => g z θ * ψ z θ)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport (Function.uncurry ψ)
  · have h1 : ContDiffAt ℝ 1 (Function.uncurry g) p :=
      (((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hg 1).contDiffAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (hψ.tsupp hp)))
    exact (h1.mul (hψ.smooth.contDiffAt.of_le (by simp))).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq (uncurry_mul_eq g ψ))
  · have h0 : Function.uncurry ψ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
    have h00 : Function.uncurry (fun z θ => g z θ * ψ z θ) =ᶠ[𝓝 p] 0 := by
      filter_upwards [h0] with q hq
      exact uncurry_mul_eq_zero hq
    exact (contDiffAt_const (c := (0 : ℝ)) (x := p)).congr_of_eventuallyEq h00

/-- **Integration by parts for the plain `z`-derivative.** -/
theorem integral_pz_mul_eq_neg {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, Work.Spaces.pz g p.1 p.2 * ψ p.1 p.2
      = -∫ p : ℝ × ℝ, g p.1 p.2 * Work.Spaces.pz ψ p.1 p.2 := by
  have hF : ContDiff ℝ 1 (Function.uncurry (fun z θ => g z θ * ψ z θ)) :=
    contDiff_one_mul_test hg hψ
  have hFc : HasCompactSupport (Function.uncurry (fun z θ => g z θ * ψ z θ)) := by
    refine hψ.cpt.mono' ?_
    intro p hp
    rw [Function.mem_support] at hp
    refine subset_closure (Function.mem_support.mpr ?_)
    intro h0
    exact hp (uncurry_mul_eq_zero h0)
  have hmaster := master_pz_eq_zero hF hFc
  have hpt : ∀ p : ℝ × ℝ, Work.Spaces.pz (fun z θ => g z θ * ψ z θ) p.1 p.2
      = Work.Spaces.pz g p.1 p.2 * ψ p.1 p.2
        + g p.1 p.2 * Work.Spaces.pz ψ p.1 p.2 :=
    fun p => pz_mul_rule hg hψ p.1 p.2
  have h1 : Integrable (fun p : ℝ × ℝ => Work.Spaces.pz g p.1 p.2 * ψ p.1 p.2) := by
    refine integrable_of_continuousOn_tsupport_test hψ ?_ ?_
    · exact (((Work.FTS.LocData.contDiffOn_pz Work.FTS.EllipticEst.isOpen_Q0 hg).continuousOn).mono
        hψ.tsupp).mul hψ.continuous.continuousOn
    · intro p hp
      rw [Function.mem_support] at hp
      refine subset_closure (Function.mem_support.mpr ?_)
      intro h0
      exact hp (mul_eq_zero_of_uncurry_eq_zero h0)
  have h2 : Integrable (fun p : ℝ × ℝ => g p.1 p.2 * Work.Spaces.pz ψ p.1 p.2) := by
    refine integrable_of_continuousOn_tsupport_test hψ ?_ ?_
    · exact (hg.continuousOn.mono hψ.tsupp).mul
        (continuous_pz_of_contDiff hψ.smooth).continuousOn
    · intro p hp
      rw [Function.mem_support] at hp
      refine tsupport_pz_subset hψ (subset_closure (Function.mem_support.mpr ?_))
      intro h0
      exact hp (mul_eq_zero_of_uncurry_eq_zero h0)
  have hsum : ∫ p : ℝ × ℝ, (Work.Spaces.pz g p.1 p.2 * ψ p.1 p.2
      + g p.1 p.2 * Work.Spaces.pz ψ p.1 p.2) = 0 := by
    rw [← hmaster]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun p => (hpt p).symm))
  rw [MeasureTheory.integral_add h1 h2] at hsum
  linarith

/-- **Integration by parts for the plain `θ`-derivative.** -/
theorem integral_pth_mul_eq_neg {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, Work.Spaces.pth g p.1 p.2 * ψ p.1 p.2
      = -∫ p : ℝ × ℝ, g p.1 p.2 * Work.Spaces.pth ψ p.1 p.2 := by
  have hF : ContDiff ℝ 1 (Function.uncurry (fun z θ => g z θ * ψ z θ)) :=
    contDiff_one_mul_test hg hψ
  have hFc : HasCompactSupport (Function.uncurry (fun z θ => g z θ * ψ z θ)) := by
    refine hψ.cpt.mono' ?_
    intro p hp
    rw [Function.mem_support] at hp
    refine subset_closure (Function.mem_support.mpr ?_)
    intro h0
    exact hp (uncurry_mul_eq_zero h0)
  have hmaster := master_pth_eq_zero hF hFc
  have hpt : ∀ p : ℝ × ℝ, Work.Spaces.pth (fun z θ => g z θ * ψ z θ) p.1 p.2
      = Work.Spaces.pth g p.1 p.2 * ψ p.1 p.2
        + g p.1 p.2 * Work.Spaces.pth ψ p.1 p.2 :=
    fun p => pth_mul_rule hg hψ p.1 p.2
  have h1 : Integrable (fun p : ℝ × ℝ => Work.Spaces.pth g p.1 p.2 * ψ p.1 p.2) := by
    refine integrable_of_continuousOn_tsupport_test hψ ?_ ?_
    · exact (((Work.FTS.LocData.contDiffOn_pth Work.FTS.EllipticEst.isOpen_Q0 hg).continuousOn).mono
        hψ.tsupp).mul hψ.continuous.continuousOn
    · intro p hp
      rw [Function.mem_support] at hp
      refine subset_closure (Function.mem_support.mpr ?_)
      intro h0
      exact hp (mul_eq_zero_of_uncurry_eq_zero h0)
  have h2 : Integrable (fun p : ℝ × ℝ => g p.1 p.2 * Work.Spaces.pth ψ p.1 p.2) := by
    refine integrable_of_continuousOn_tsupport_test hψ ?_ ?_
    · exact (hg.continuousOn.mono hψ.tsupp).mul
        (continuous_pth_of_contDiff hψ.smooth).continuousOn
    · intro p hp
      rw [Function.mem_support] at hp
      refine tsupport_pth_subset hψ (subset_closure (Function.mem_support.mpr ?_))
      intro h0
      exact hp (mul_eq_zero_of_uncurry_eq_zero h0)
  have hsum : ∫ p : ℝ × ℝ, (Work.Spaces.pth g p.1 p.2 * ψ p.1 p.2
      + g p.1 p.2 * Work.Spaces.pth ψ p.1 p.2) = 0 := by
    rw [← hmaster]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun p => (hpt p).symm))
  rw [MeasureTheory.integral_add h1 h2] at hsum
  linarith


end Work.FTS.PhiStar.Honesty.SlotsLimit
