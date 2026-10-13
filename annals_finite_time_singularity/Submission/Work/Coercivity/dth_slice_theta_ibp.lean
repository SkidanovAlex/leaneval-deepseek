import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.slice_ibp
import Submission.Work.Coercivity.cos_sin_integrable
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Coercivity.sliceEtaAux

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

/-! ## Pointwise `rpow` algebra

`D_θ g = sin(2θ) · ∂_θ g`, so every `D_θ`-factor contributes a `sin(2θ)` which cancels
one unit of the negative exponent `-(gam α)`.  These identities are the algebraic
content of both the boundary vanishing and the integrability. -/

private theorem rpow_neg_mul_self_mul (s a b γ : ℝ) (hs : 0 ≤ s) (hγ0 : γ ≠ 0)
    (hγ2 : γ ≠ 2) :
    s ^ (-γ) * (s * a) * (s * b) = s ^ (2 - γ) * a * b := by
  rcases eq_or_lt_of_le hs with h0 | hpos
  · subst h0
    rw [Real.zero_rpow (neg_ne_zero.mpr hγ0),
      Real.zero_rpow (sub_ne_zero.mpr (Ne.symm hγ2))]
    ring
  · have hA : s ^ (2 - γ) = s ^ (-γ) * s ^ 2 := by
      rw [show (2:ℝ) - γ = -γ + 2 by ring, Real.rpow_add hpos]
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [hA]
    ring

private theorem rpow_neg_mul_self_sq (s u γ : ℝ) (hs : 0 ≤ s) (hγ0 : γ ≠ 0)
    (hγ2 : γ ≠ 2) :
    s ^ (-γ) * (s * u) ^ 2 = s ^ (2 - γ) * u ^ 2 := by
  rcases eq_or_lt_of_le hs with h0 | hpos
  · subst h0
    rw [Real.zero_rpow (neg_ne_zero.mpr hγ0),
      Real.zero_rpow (sub_ne_zero.mpr (Ne.symm hγ2))]
    ring
  · have hA : s ^ (2 - γ) = s ^ (-γ) * s ^ 2 := by
      rw [show (2:ℝ) - γ = -γ + 2 by ring, Real.rpow_add hpos]
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [hA]
    ring

private theorem rpow_neg_sub_one_mul_sq (s u γ : ℝ) (hs : 0 ≤ s) (hγ1 : γ ≠ 1)
    (hγ3 : γ ≠ 3) :
    s ^ (-(γ - 1)) * (s * u) ^ 2 = s ^ (3 - γ) * u ^ 2 := by
  have h1 : γ - 1 ≠ 0 := sub_ne_zero.mpr hγ1
  have h2 : γ - 1 ≠ 2 := by intro h; exact hγ3 (by linarith)
  have h := rpow_neg_mul_self_sq s u (γ - 1) hs h1 h2
  rw [show 2 - (γ - 1) = 3 - γ by ring] at h
  exact h

/-! ## Continuity of the angular slices of `∂_θ f` -/

private theorem continuousAt_pth_slice (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) {z : ℝ}
    (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    ContinuousAt (fun θ' => Spaces.pth f z θ') θ := by
  have hbox : (z, θ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) : Set (ℝ × ℝ)) := by
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_Ioi]; linarith
    · simp only [Set.mem_Ioo]; exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.pth f))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) :=
    Work.Spaces.contDiffOn_uncurry_pth hopen hsm
  have hcat : ContDiffAt ℝ ⊤ (Function.uncurry (Spaces.pth f)) (z, θ) :=
    hcd.contDiffAt (hopen.mem_nhds hbox)
  have hcont : ContinuousAt (Function.uncurry (Spaces.pth f)) (z, θ) := hcat.continuousAt
  have hcurve : ContinuousAt (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  have hcomp : ContinuousAt (fun θ' : ℝ => Function.uncurry (Spaces.pth f) (z, θ')) θ :=
    hcont.comp hcurve
  exact hcomp

/-! ## Vanishing of the boundary term `sin(2θ)^{-(γ-1)}·(D_θ f)²` at the two endpoints -/

private theorem dth_psi_tendsto_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α - 1)) * (Spaces.Dth f z θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h3 : (0:ℝ) ≤ 3 - Spaces.gam α := by simp only [Spaces.gam]; linarith
  have hne : 3 - Spaces.gam α ≠ 0 := by
    have : (0:ℝ) < 3 - Spaces.gam α := by simp only [Spaces.gam]; linarith
    linarith
  have hγ1 : Spaces.gam α ≠ 1 := by simp only [Spaces.gam]; intro h; linarith
  have hγ3 : Spaces.gam α ≠ 3 := by simp only [Spaces.gam]; intro h; linarith
  have hcont1 : Continuous (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Spaces.gam α)) :=
    (Real.continuous_rpow_const h3).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hcont2 : ContinuousAt (fun θ : ℝ => (Spaces.pth f z θ) ^ 2) 0 :=
    (continuousAt_pth_slice f hsm hz Spaces.zero_mem_Iθ).pow 2
  have hG : ContinuousAt
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Spaces.gam α) * (Spaces.pth f z θ) ^ 2) 0 :=
    hcont1.continuousAt.mul hcont2
  have hGt : Filter.Tendsto
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Spaces.gam α) * (Spaces.pth f z θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h0 : (Real.sin (2 * (0:ℝ))) ^ (3 - Spaces.gam α) * (Spaces.pth f z 0) ^ 2 = 0 := by
      rw [show (2:ℝ) * 0 = 0 by ring, Real.sin_zero, Real.zero_rpow hne, zero_mul]
    have ht := hG.tendsto
    rw [h0] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have hev : (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α - 1)) * (Spaces.Dth f z θ) ^ 2)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun θ => (Real.sin (2 * θ)) ^ (3 - Spaces.gam α) * (Spaces.pth f z θ) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0:ℝ) < Real.pi / 2))]
      with θ hθpos hθlt
    have hθ0 : (0:ℝ) < θ := hθpos
    have hθp : θ < Real.pi / 2 := hθlt
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    simp only [Spaces.Dth]
    exact rpow_neg_sub_one_mul_sq (Real.sin (2 * θ)) (Spaces.pth f z θ) (Spaces.gam α)
      (le_of_lt hsin) hγ1 hγ3
  exact hGt.congr' hev.symm

private theorem dth_psi_tendsto_zero_pi_half (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α - 1)) * (Spaces.Dth f z θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have h3 : (0:ℝ) ≤ 3 - Spaces.gam α := by simp only [Spaces.gam]; linarith
  have hne : 3 - Spaces.gam α ≠ 0 := by
    have : (0:ℝ) < 3 - Spaces.gam α := by simp only [Spaces.gam]; linarith
    linarith
  have hγ1 : Spaces.gam α ≠ 1 := by simp only [Spaces.gam]; intro h; linarith
  have hγ3 : Spaces.gam α ≠ 3 := by simp only [Spaces.gam]; intro h; linarith
  have hcont1 : Continuous (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Spaces.gam α)) :=
    (Real.continuous_rpow_const h3).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hcont2 : ContinuousAt (fun θ : ℝ => (Spaces.pth f z θ) ^ 2) (Real.pi / 2) :=
    (continuousAt_pth_slice f hsm hz Spaces.pi_half_mem_Iθ).pow 2
  have hG : ContinuousAt
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Spaces.gam α) * (Spaces.pth f z θ) ^ 2)
      (Real.pi / 2) :=
    hcont1.continuousAt.mul hcont2
  have hGt : Filter.Tendsto
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - Spaces.gam α) * (Spaces.pth f z θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h0 : (Real.sin (2 * (Real.pi / 2))) ^ (3 - Spaces.gam α)
        * (Spaces.pth f z (Real.pi / 2)) ^ 2 = 0 := by
      rw [show (2:ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, Real.zero_rpow hne, zero_mul]
    have ht := hG.tendsto
    rw [h0] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have hev : (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α - 1)) * (Spaces.Dth f z θ) ^ 2)
      =ᶠ[nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))]
      (fun θ => (Real.sin (2 * θ)) ^ (3 - Spaces.gam α) * (Spaces.pth f z θ) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (by positivity : (0:ℝ) < Real.pi / 2))]
      with θ hθlt hθpos
    have hθ0 : (0:ℝ) < θ := hθpos
    have hθp : θ < Real.pi / 2 := hθlt
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    simp only [Spaces.Dth]
    exact rpow_neg_sub_one_mul_sq (Real.sin (2 * θ)) (Spaces.pth f z θ) (Spaces.gam α)
      (le_of_lt hsin) hγ1 hγ3
  exact hGt.congr' hev.symm

/-! ## Integrability of the two angular integrands -/

private theorem sin_two_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

private theorem dth_theta_LHS_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ)
      Spaces.Iθ := by
  have hγ0 : Spaces.gam α ≠ 0 := by simp only [Spaces.gam]; intro h; linarith
  have hγ2 : Spaces.gam α ≠ 2 := by simp only [Spaces.gam]; intro h; linarith
  have h2γ : (0:ℝ) ≤ 2 - Spaces.gam α := by simp only [Spaces.gam]; linarith
  have hcont1 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Spaces.gam α)) Spaces.Iθ :=
    ((Real.continuous_rpow_const h2γ).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).continuousOn
  have hcont2 : ContinuousOn (fun θ : ℝ => Spaces.pth (Spaces.Dth f) z θ) Spaces.Iθ :=
    slice_pth_continuousOn (Spaces.Dth f) (Spaces.SmoothNbhd.Dth hsm) hz
  have hcont3 : ContinuousOn (fun θ : ℝ => Spaces.pth f z θ) Spaces.Iθ :=
    slice_pth_continuousOn f hsm hz
  have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Spaces.gam α)
      * Spaces.pth (Spaces.Dth f) z θ * Spaces.pth f z θ) Spaces.Iθ :=
    (hcont1.mul hcont2).mul hcont3
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Spaces.gam α)
      * Spaces.pth (Spaces.Dth f) z θ * Spaces.pth f z θ) Spaces.Iθ :=
    ContinuousOn.integrableOn_compact
      (show IsCompact Spaces.Iθ from isCompact_Icc) hcont
  refine hint.congr_fun ?_ (show MeasurableSet Spaces.Iθ from measurableSet_Icc)
  intro θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Iθ hθ
  simp only [Spaces.Dth]
  exact (rpow_neg_mul_self_mul (Real.sin (2 * θ)) (Spaces.pth (Spaces.Dth f) z θ)
    (Spaces.pth f z θ) (Spaces.gam α) hs hγ0 hγ2).symm

private theorem dth_theta_RHS_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2)
      Spaces.Iθ := by
  have hγ0 : Spaces.gam α ≠ 0 := by simp only [Spaces.gam]; intro h; linarith
  have hγ2 : Spaces.gam α ≠ 2 := by simp only [Spaces.gam]; intro h; linarith
  have h2γ : (0:ℝ) ≤ 2 - Spaces.gam α := by simp only [Spaces.gam]; linarith
  have hcont1 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Spaces.gam α)) Spaces.Iθ :=
    ((Real.continuous_rpow_const h2γ).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).continuousOn
  have hcontc : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) Spaces.Iθ :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hcont3 : ContinuousOn (fun θ : ℝ => (Spaces.pth f z θ) ^ 2) Spaces.Iθ :=
    (slice_pth_continuousOn f hsm hz).pow 2
  have hcont : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)
      * (Real.sin (2 * θ)) ^ (2 - Spaces.gam α) * (Spaces.pth f z θ) ^ 2) Spaces.Iθ :=
    (hcontc.mul hcont1).mul hcont3
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => Real.cos (2 * θ)
      * (Real.sin (2 * θ)) ^ (2 - Spaces.gam α) * (Spaces.pth f z θ) ^ 2) Spaces.Iθ :=
    ContinuousOn.integrableOn_compact
      (show IsCompact Spaces.Iθ from isCompact_Icc) hcont
  refine hint.congr_fun ?_ (show MeasurableSet Spaces.Iθ from measurableSet_Icc)
  intro θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Iθ hθ
  have key := rpow_neg_mul_self_sq (Real.sin (2 * θ)) (Spaces.pth f z θ) (Spaces.gam α)
    hs hγ0 hγ2
  simp only [Spaces.Dth]
  rw [show Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        * (Real.sin (2 * θ) * Spaces.pth f z θ) ^ 2
      = Real.cos (2 * θ) * ((Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        * (Real.sin (2 * θ) * Spaces.pth f z θ) ^ 2) by ring, key]
  ring

/-! ## The angular integration by parts for `D_θ f` -/

theorem dth_slice_theta_ibp (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    {z : ℝ} (hz : 0 < z) :
    ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ
      = (Spaces.gam α - 1) * ∫ θ in Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2 := by
  exact slice_ibp α hα (Spaces.Dth f) (Spaces.SmoothNbhd.Dth hsm)
    (fun z hz => dth_psi_tendsto_zero α hα hα1 f hsm hz)
    (fun z hz => dth_psi_tendsto_zero_pi_half α hα hα1 f hsm hz)
    z hz
    (dth_theta_LHS_integrable α hα hα1 f hsm hz)
    (dth_theta_RHS_integrable α hα hα1 f hsm hz)

end Work.Coercivity
