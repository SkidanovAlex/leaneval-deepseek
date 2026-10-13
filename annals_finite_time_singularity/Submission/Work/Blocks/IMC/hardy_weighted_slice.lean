/-
The weighted slice Hardy inequality of `Work.Blocks.IMC` (block `IMC`), the `cot²`-weighted
angular Hardy estimate for the `z`-slices of a compactly supported function.

The statement: there is `CH > 0` such that for every `G : ℝ → ℝ → ℝ` which is `C^n` for every
`n` on the open strip `OStrip = (0,∞) × (-1, π/2+1)`, vanishes at the two angular boundaries
`θ = 0`, `θ = π/2` and is supported in `z ∈ [δ,R]` (`0 < δ < R`),

  `∫_z w² ∫_θ (D_zG)² cot²(2θ) σ  ≤  1/(1+η)² ∫_z w² ∫_θ (D_z∂_θG)² σ
                                        + CH ∫_z w² ∫_θ (D_zG)² σ`,

where `w z = (1+z)²/z²`, `σ θ = sin(2θ)^{-η}` (`η = 99/100`), `D_z = z∂_z`.

**Proof.**  For fixed `z > 0` the `z`-slice `u = ∂_zG(z,·)` vanishes at `θ = 0, π/2` and is
`C¹` there, so the sharp same-weight Hardy inequality `AngSecond.hardy_slice_cos2`
(`∫ f² cos²(2θ) sin(2θ)^{-(2+η)} ≤ (1/(1+η)²) ∫ (f')² sin(2θ)^{-η} + CH ∫ f² sin(2θ)^{-η}`)
applies to `u`.  Clairaut (`∂_z∂_θG = ∂_θ∂_zG` on the open strip) and
`cot²(2θ) σ θ = cos²(2θ) sin(2θ)^{-(2+η)}` on `(0,π/2)` identify the four angular integrals
with the two sides of the Hardy inequality, and the factor `z²` of `D_z` is taken out of each
angular integral.  At `z = 0` every integrand vanishes.  The resulting inequality holds
pointwise in `z ∈ Iz`, and the `z`-integrals are compared by monotonicity of the integral:
the dominating function is integrable because `G` is smooth on the compact box `[δ,R] × Iθ`
and is supported in `[δ,R]` in the radial variable.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux
import Submission.Work.FTS.EllipticEst.AngSecond.hardy_slice_cos2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.IMC

noncomputable section

set_option autoImplicit false

/-! ## Elementary angular identities -/

/-- `cot²(2θ)·σ θ = cos²(2θ)·sin(2θ)^{-(2+η)}` on the open angular interval. -/
private theorem cot_sq_thEta_eq {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ
      = (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hkey : (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
      = ((Real.sin (2 * θ)) ^ 2)⁻¹ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [show -(2 + Work.Spaces.eta) = (-2 : ℝ) + (-(Work.Spaces.eta)) by ring,
      Real.rpow_add hs, Real.rpow_neg hs.le]
    rw [show (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ 2 from Real.rpow_natCast _ 2]
  rw [hkey, Real.cot_eq_cos_div_sin, div_pow, Work.FTS.EllipticEst.thEta, div_eq_mul_inv,
    Real.rpow_neg hs.le]
  ring

/-- Almost everywhere equality on `Iθ` follows from equality on the open interval. -/
private theorem ae_eq_on_Iθ_of_Ioo {F G : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), F θ = G θ) :
    F =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] G := by
  have hset : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hset]
  exact ae_restrict_of_forall_mem measurableSet_Ioo h

/-! ## Vanishing off the radial support, and smoothness of the slices -/

/-- If `G` vanishes identically for `z ∉ [δ,R]`, then so does `∂_zG`
(the derivative only sees a neighbourhood of the point). -/
private theorem pz_vanish_off {δ R : ℝ} {G : ℝ → ℝ → ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.pz G z θ = 0 := by
  intro z hz θ
  have hnb : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R := isClosed_Icc.isOpen_compl.mem_nhds hz
  have h0 : (fun z' => G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z' hz'
    exact hsupp z' hz' θ
  simp only [Work.Spaces.pz]
  rw [h0.deriv_eq, deriv_const]

/-- If `G` vanishes identically for `z ∉ [δ,R]`, then so does `∂_z∂_θG`. -/
private theorem pz_pth_vanish_off {δ R : ℝ} {G : ℝ → ℝ → ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.pz (Work.Spaces.pth G) z θ = 0 := by
  intro z hz θ
  have hnb : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R := isClosed_Icc.isOpen_compl.mem_nhds hz
  have h0 : (fun z' => Work.Spaces.pth G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z' hz'
    simp only [Work.Spaces.pth]
    rw [show (fun θ' => G z' θ') = fun _ => (0 : ℝ) by funext θ'; exact hsupp z' hz' θ',
      deriv_const]
  simp only [Work.Spaces.pz]
  rw [h0.deriv_eq, deriv_const]

/-- The `θ`-slice of `∂_zG` at `z > 0` is `C¹` on the closed angular interval. -/
private theorem contDiffOn_pz_slice {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) Work.FTS.EllipticEst.ThetaU.OStrip)
    {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 1 (fun θ => Work.Spaces.pz G z θ) (Set.Icc 0 (Real.pi / 2)) := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz G))
      Work.FTS.EllipticEst.ThetaU.OStrip :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pz_fin (n := 1) (hsm (1 + 1))
  have hg : ContDiffOn ℝ 1 (fun θ : ℝ => (z, θ)) (Set.Icc 0 (Real.pi / 2)) := by fun_prop
  have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Icc 0 (Real.pi / 2))
      Work.FTS.EllipticEst.ThetaU.OStrip := by
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    exact ⟨hz, by linarith, by linarith [hθ.2, Real.pi_pos]⟩
  have := h1.comp hg hmaps
  simpa [Function.comp_def] using this

private theorem pz_slice_endpoint_left {G : ℝ → ℝ → ℝ} (h0 : ∀ z, G z 0 = 0) (z : ℝ) :
    Work.Spaces.pz G z 0 = 0 := by
  simp only [Work.Spaces.pz]
  rw [show (fun z' => G z' 0) = (fun _ => (0 : ℝ)) by funext z'; exact h0 z', deriv_const]

private theorem pz_slice_endpoint_right {G : ℝ → ℝ → ℝ} (hπ : ∀ z, G z (Real.pi / 2) = 0)
    (z : ℝ) : Work.Spaces.pz G z (Real.pi / 2) = 0 := by
  simp only [Work.Spaces.pz]
  rw [show (fun z' => G z' (Real.pi / 2)) = (fun _ => (0 : ℝ)) by funext z'; exact hπ z',
    deriv_const]

/-! ## Identification of the angular integrals with the Hardy quantities -/

/-- For `z > 0`, the four angular integrals occurring in the statement are `z²` times the
corresponding integrals of the slice `u = ∂_zG(z,·)` against the Hardy weights: the `cot²`
weight becomes `cos²(2θ) sin(2θ)^{-(2+η)}`, and `D_z∂_θG` becomes `z·u'` by Clairaut. -/
private theorem slice_identities {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) Work.FTS.EllipticEst.ThetaU.OStrip)
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      = z ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz G z θ) ^ 2
          * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
    ∧ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      = z ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => Work.Spaces.pz G z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    ∧ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      = z ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz G z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hIθ : ∀ θ ∈ Work.Spaces.Iθ, θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hcd : ∀ θ ∈ Work.Spaces.Iθ, ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) := by
    intro θ hθ
    exact (hsm 2).contDiffAt
      (Work.FTS.EllipticEst.ThetaU.isOpen_OStrip.mem_nhds ⟨hz, hIθ θ hθ⟩)
  refine ⟨?_, ?_, ?_⟩
  · have hc1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = z ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz G z θ) ^ 2
            * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      simp only [Work.Spaces.Dz]
      ring
    have hc2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz G z θ) ^ 2
          * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz G z θ) ^ 2
            * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine ae_eq_on_Iθ_of_Ioo (fun θ hθ => ?_)
      have h := cot_sq_thEta_eq hθ
      simp only [Work.FTS.EllipticEst.thEta] at h ⊢
      rw [mul_assoc, h, mul_assoc]
    rw [hc1, hc2]
  · rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    have hcl : Work.Spaces.pz (Work.Spaces.pth G) z θ = Work.Spaces.pth (Work.Spaces.pz G) z θ :=
      Work.Spaces.pz_pth_comm (hcd θ hθ)
    simp only [Work.Spaces.Dz, Work.FTS.EllipticEst.thEta] at hcl ⊢
    rw [hcl]
    simp only [Work.Spaces.pth]
    ring
  · rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    simp only [Work.Spaces.Dz, Work.FTS.EllipticEst.thEta]
    ring

/-! ## Integrability of the two dominating outer integrands -/

/-- The two outer integrands are integrable: they are supported in the compact interval
`[δ,R]`, where `w` is bounded and the inner integrands are bounded (smoothness on `OStrip`
plus integrability of `σ`). -/
private theorem integrable_outer_weighted_aux {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R)
    {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) Work.FTS.EllipticEst.ThetaU.OStrip)
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz)
    ∧ MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hsub : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)
      ⊆ Work.FTS.EllipticEst.ThetaU.OStrip := by
    intro p hp
    exact ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩
  have key : ∀ {K : ℝ → ℝ → ℝ},
      ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dz K)) Work.FTS.EllipticEst.ThetaU.OStrip →
      (∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.pz K z θ = 0) →
      MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz K z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro K hKcont hv
    refine Work.FTS.EllipticEst.ThetaU.integrable_outer_of_bound (δ := δ) (R := R) hδ
      (F := fun z θ => (Work.Spaces.Dz K z θ) ^ 2) ?_ ?_ ?_
    · have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.Dz K p.1 p.2) ^ 2)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ((hKcont.mono hsub).continuousOn).pow 2
      change ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.Dz K p.1 p.2) ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
      exact h1
    · intro z hz θ
      simp only [Work.Spaces.Dz, hv z hz θ, mul_zero]
      norm_num
    · have hboxCont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.Dz K p.1 p.2) ^ 2)
          (Set.Icc δ R ×ˢ Work.Spaces.Iθ) := by
        refine fun p hp => ?_
        rw [Set.mem_prod] at hp
        have hmemO : p ∈ Work.FTS.EllipticEst.ThetaU.OStrip :=
          ⟨lt_of_lt_of_le hδ hp.1.1, by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩
        have hcat : ContinuousAt (Function.uncurry (Work.Spaces.Dz K)) p :=
          hKcont.continuousOn.continuousAt
            (Work.FTS.EllipticEst.ThetaU.isOpen_OStrip.mem_nhds hmemO)
        have h2 : ContinuousAt (fun p : ℝ × ℝ => (Work.Spaces.Dz K p.1 p.2) ^ 2) p :=
          hcat.pow 2
        exact h2.continuousWithinAt
      obtain ⟨M, -, hM⟩ := Work.FTS.EllipticEst.ThetaU.exists_bound_box
        (δ := δ) (R := R) hδ hδR (f := fun z θ => (Work.Spaces.Dz K z θ) ^ 2) hboxCont
      exact ⟨M, hM⟩
  have hDzG : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dz G))
      Work.FTS.EllipticEst.ThetaU.OStrip :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 0) (hsm 1)
  have hDzPth : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth G)))
      Work.FTS.EllipticEst.ThetaU.OStrip :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 0)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 1) (hsm 2))
  exact ⟨key hDzPth (pz_pth_vanish_off hsupp), key hDzG (pz_vanish_off hsupp)⟩

/-! ## The slicewise Hardy inequality -/

/-- **The slicewise Hardy inequality.**  For every `z ∈ Iz` the `cot²`-weighted angular
integral of `D_zG` is dominated by the `η`-weighted angular integrals of `D_z∂_θG` and of
`D_zG`, with the sharp constant `1/(1+η)²`. -/
private theorem slice_ineq {G : ℝ → ℝ → ℝ} {CH : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) Work.FTS.EllipticEst.ThetaU.OStrip)
    (h0 : ∀ z, G z 0 = 0) (hπ : ∀ z, G z (Real.pi / 2) = 0)
    (hHardy : ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) → f 0 = 0 →
      f (Real.pi / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        ≤ 1 / (1 + Work.Spaces.eta) ^ 2
            * (∫ θ in Work.Spaces.Iθ,
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + CH * (∫ θ in Work.Spaces.Iθ,
              f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :
    ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        ≤ 1 / (1 + Work.Spaces.eta) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)
          + CH * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := by
  intro z hz
  have hz' : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz' with hz0 | hzpos
  · subst hz0
    simp only [Work.Spaces.Dz, zero_mul]
    simp
  · obtain ⟨h1, h2, h3⟩ := slice_identities hsm hzpos
    have hu := contDiffOn_pz_slice hsm hzpos
    have hH := hHardy (fun θ => Work.Spaces.pz G z θ) hu (pz_slice_endpoint_left h0 z)
      (pz_slice_endpoint_right hπ z)
    rw [h1, h2, h3]
    nlinarith [mul_le_mul_of_nonneg_left hH (sq_nonneg z)]

/-! ## The main theorem -/

theorem hardy_weighted_slice :
    ∃ CH : ℝ, 0 < CH ∧
      ∀ {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) (G : ℝ → ℝ → ℝ)
        (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
          (Work.FTS.EllipticEst.ThetaU.OStrip))
        (h0 : ∀ z, G z 0 = 0) (hπ : ∀ z, G z (Real.pi / 2) = 0)
        (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0),
        (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
              * Work.FTS.EllipticEst.thEta θ))
          ≤ 1 / (1 + Work.Spaces.eta) ^ 2 *
              (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ))
            + CH * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ)) := by
  obtain ⟨CH, hCHpos, hHardy⟩ := Work.FTS.EllipticEst.AngSecond.hardy_slice_cos2
  refine ⟨CH, hCHpos, fun {δ R} hδ hδR G hsm h0 hπ hsupp => ?_⟩
  have hslice := slice_ineq hsm h0 hπ hHardy
  obtain ⟨hInt1, hInt2⟩ := integrable_outer_weighted_aux hδ hδR hsm hsupp
  -- integrability of the dominating function
  have hgInt : MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2
        * (1 / (1 + Work.Spaces.eta) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ)
            + CH * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine ((hInt1.const_mul (1 / (1 + Work.Spaces.eta) ^ 2)).add
      (hInt2.const_mul CH)).congr ?_
    filter_upwards with z
    simp only [Pi.add_apply]
    ring
  have hmono : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
          * Work.FTS.EllipticEst.thEta θ))
      ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (1 / (1 + Work.Spaces.eta) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ)
            + CH * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hgInt ?_
    · filter_upwards with z
      refine mul_nonneg (sq_nonneg _) ?_
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
        with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Work.FTS.EllipticEst.thEta_nonneg hθ)
    · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iz) measurableSet_Ici]
        with z hz
      exact mul_le_mul_of_nonneg_left (hslice z hz) (sq_nonneg _)
  have hsplit : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (1 / (1 + Work.Spaces.eta) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)
          + CH * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)))
      = 1 / (1 + Work.Spaces.eta) ^ 2 *
          (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ))
        + CH * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)) := by
    have heq : (fun z => (Work.Spaces.w z) ^ 2 *
        (1 / (1 + Work.Spaces.eta) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)
          + CH * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)))
        = (fun z => 1 / (1 + Work.Spaces.eta) ^ 2
            * ((Work.Spaces.w z) ^ 2 *
              (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ))
          + CH * ((Work.Spaces.w z) ^ 2 *
              (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ))) := by
      funext z; ring
    rw [heq, MeasureTheory.integral_add (hInt1.const_mul _) (hInt2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
          * Work.FTS.EllipticEst.thEta θ))
      ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (1 / (1 + Work.Spaces.eta) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ)
            + CH * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ)) := hmono
    _ = 1 / (1 + Work.Spaces.eta) ^ 2 *
          (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ))
        + CH * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)) := hsplit

end

end Work.Blocks.IMC
