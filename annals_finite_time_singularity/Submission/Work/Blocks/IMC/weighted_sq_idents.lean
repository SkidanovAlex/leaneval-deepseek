/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted squared `L²` identities over the product measure

The three functionals `ddInt`, `dInt`, `ttInt` of
`Work.FTS.EllipticEst.interpol_defs` are written as *iterated* integrals
`∫_z ∫_θ (… ) w(z)² sin(2θ)^{-η}`.  The singularity construction instead meets them as
integrals against the product measure `(volume.restrict I_z).prod (volume.restrict I_θ)`.
This file records that the two agree, for a function which is smooth on the open strip
`(0,∞) × (-1, π/2+1)` (so that `D_zG`, `D_z²G`, `∂_θ²G` are continuous there) and is
supported in `z ∈ [δ,R]`:

  `∫_{(z,θ)} (D_z²G)² w² σ = ddInt G`,
  `∫_{(z,θ)} (D_zG)² w² σ   = dInt G`,
  `∫_{(z,θ)} (∂_θ²G)² w² σ  = ttInt G`,

where `σ = thEta`.

The engine is `Work.FTS.EllipticEst.ThetaU.iterated_eq_prod`, which identifies the iterated
and product integrals of `(z,θ) ↦ w(z)² σ(θ) F(z,θ)` under a continuity hypothesis on the
open quadrant, vanishing off `[δ,R]` in `z`, and a bound on the compact box.  The three
instantiations differ only in `F = (D_z²G)²`, `(D_zG)²`, `(∂_θ²G)²`, whose continuity on the
strip comes from `ThetaU.contDiffOn_uncurry_Dz_fin` / `contDiffOn_uncurry_pth_fin`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.interpol_defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.IMC

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Vanishing of the derived functions off the support in `z` -/

private lemma pz_eq_zero_of_vanish {G : ℝ → ℝ → ℝ} {δ R : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) (θ : ℝ) {z : ℝ}
    (hz : z ∉ Set.Icc δ R) : Work.Spaces.pz G z θ = 0 := by
  have hnb : (Set.Icc δ R)ᶜ ∈ 𝓝 z := isClosed_Icc.isOpen_compl.mem_nhds hz
  have hev : (fun z' : ℝ => G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z' hz'
    exact hsupp z' hz' θ
  show deriv (fun z' : ℝ => G z' θ) z = 0
  rw [hev.deriv_eq]
  simp

private lemma Dz_eq_zero_of_vanish {G : ℝ → ℝ → ℝ} {δ R : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) (θ : ℝ) {z : ℝ}
    (hz : z ∉ Set.Icc δ R) : Work.Spaces.Dz G z θ = 0 := by
  show z * Work.Spaces.pz G z θ = 0
  rw [pz_eq_zero_of_vanish hsupp θ hz, mul_zero]

private lemma DzDz_eq_zero_of_vanish {G : ℝ → ℝ → ℝ} {δ R : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) (θ : ℝ) {z : ℝ}
    (hz : z ∉ Set.Icc δ R) : Work.Spaces.Dz (Work.Spaces.Dz G) z θ = 0 := by
  have hnb : (Set.Icc δ R)ᶜ ∈ 𝓝 z := isClosed_Icc.isOpen_compl.mem_nhds hz
  have hev : (fun z' : ℝ => Work.Spaces.Dz G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z' hz'
    exact Dz_eq_zero_of_vanish hsupp θ hz'
  show z * deriv (fun z' : ℝ => Work.Spaces.Dz G z' θ) z = 0
  rw [hev.deriv_eq]
  simp

private lemma pth_eq_zero_of_vanish {G : ℝ → ℝ → ℝ} {δ R : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) {z : ℝ}
    (hz : z ∉ Set.Icc δ R) (θ : ℝ) : Work.Spaces.pth G z θ = 0 := by
  have hfun : (fun θ' : ℝ => G z θ') = fun _ => (0 : ℝ) := funext fun θ' => hsupp z hz θ'
  show deriv (fun θ' : ℝ => G z θ') θ = 0
  rw [hfun]
  simp

private lemma pth_pth_eq_zero_of_vanish {G : ℝ → ℝ → ℝ} {δ R : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) {z : ℝ}
    (hz : z ∉ Set.Icc δ R) (θ : ℝ) : Work.Spaces.pth (Work.Spaces.pth G) z θ = 0 := by
  have hfun : (fun θ' : ℝ => Work.Spaces.pth G z θ') = fun _ => (0 : ℝ) :=
    funext fun θ' => pth_eq_zero_of_vanish hsupp hz θ'
  show deriv (fun θ' : ℝ => Work.Spaces.pth G z θ') θ = 0
  rw [hfun]
  simp

/-! ## Bounds on the compact box -/

/-- A bound for a continuous function on the box `[δ,R] × Iθ` (no non-emptiness or
`δ < R` hypothesis: an empty box is handled by its compactness). -/
private theorem exists_bound_box_general {δ R : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Icc δ R ×ˢ Work.Spaces.Iθ)) :
    ∃ M : ℝ, ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf
  refine ⟨C, fun z hz θ hθ => ?_⟩
  have h := hC (z, θ) ⟨hz, hθ⟩
  rwa [Real.norm_eq_abs] at h

/-- Squaring a function preserves continuity in the uncurried form. -/
private theorem continuousOn_uncurry_sq {F : ℝ → ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (h : ContinuousOn (Function.uncurry F) s) :
    ContinuousOn (Function.uncurry (fun z θ => F z θ ^ 2)) s :=
  (h.pow 2).congr (fun _ _ => rfl)

/-! ## The Fubini bridge -/

/-- The iterated integral `∫_z ∫_θ F w² σ` agrees with the integral against the product
measure `(volume.restrict I_z).prod (volume.restrict I_θ)`. -/
private theorem prod_eq_iterated_aux {δ R : ℝ} (hδ : 0 < δ) {F : ℝ → ℝ → ℝ}
    (hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hF0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0)
    (hFb : ∃ Mb : ℝ, ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ Mb) :
    (∫ p : ℝ × ℝ, F p.1 p.2 * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          F z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  have h := Work.FTS.EllipticEst.ThetaU.iterated_eq_prod (δ := δ) (R := R) hδ hFc hF0 hFb
  have hstep : (∫ p : ℝ × ℝ,
        F p.1 p.2 * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ p : ℝ × ℝ,
          (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * F p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  rw [hstep, ← h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        F z θ * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ,
          F z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
  rw [show (∫ θ in Work.Spaces.Iθ,
        F z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ,
          (F z θ * Work.FTS.EllipticEst.thEta θ) * (Work.Spaces.w z) ^ 2 from by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
        ring,
    MeasureTheory.integral_mul_const]
  ring

/-! ## The three identities -/

theorem weighted_sq_idents {δ R : ℝ} (hδ : 0 < δ) {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) (Work.FTS.EllipticEst.ThetaU.OStrip))
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    (∫ p : ℝ × ℝ, (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2) ^ 2
            * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = Work.FTS.EllipticEst.ddInt G)
    ∧ (∫ p : ℝ × ℝ, (Work.Spaces.Dz G p.1 p.2) ^ 2
            * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = Work.FTS.EllipticEst.dInt G)
    ∧ (∫ p : ℝ × ℝ, (Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2) ^ 2
            * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = Work.FTS.EllipticEst.ttInt G) := by
  -- ## the geometric inclusions
  have hquad : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆
      Work.FTS.EllipticEst.ThetaU.OStrip := fun p hp =>
    ⟨hp.1, ⟨by linarith [hp.2.1, Real.pi_pos], by linarith [hp.2.2, Real.pi_pos]⟩⟩
  have hbox : Set.Icc δ R ×ˢ Work.Spaces.Iθ ⊆ Work.FTS.EllipticEst.ThetaU.OStrip :=
    fun p hp => ⟨lt_of_lt_of_le hδ hp.1.1,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩
  -- ## continuity of the derived functions on the strip
  have hcDzDz : ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz G)))
      Work.FTS.EllipticEst.ThetaU.OStrip :=
    (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 2) (hsm 3))).continuousOn
  have hcDz : ContinuousOn (Function.uncurry (Work.Spaces.Dz G))
      Work.FTS.EllipticEst.ThetaU.OStrip :=
    (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 1) (hsm 2)).continuousOn
  have hchh : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth G)))
      Work.FTS.EllipticEst.ThetaU.OStrip :=
    (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hsm 3))).continuousOn
  -- ## the radial weight is continuous on the quadrant and on the box
  have hwquad : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine ContinuousOn.pow ?_ 2
    rw [show (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p => (1 + p.1) ^ 2 / p.1 ^ 2 from rfl]
    refine ContinuousOn.div ((continuous_const.add continuous_fst).continuousOn.pow 2)
      (continuous_fst.pow 2).continuousOn ?_
    intro p hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  have hwbox : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Icc δ R ×ˢ Work.Spaces.Iθ) := by
    refine ContinuousOn.pow ?_ 2
    rw [show (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p => (1 + p.1) ^ 2 / p.1 ^ 2 from rfl]
    refine ContinuousOn.div ((continuous_const.add continuous_fst).continuousOn.pow 2)
      (continuous_fst.pow 2).continuousOn ?_
    intro p hp
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hδ hp.1.1))
  -- ## the three instantiations of the Fubini bridge
  have h1 : (∫ p : ℝ × ℝ, (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = Work.FTS.EllipticEst.ddInt G := by
    have h := prod_eq_iterated_aux (δ := δ) (R := R) hδ
      (F := fun z θ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2)
      (continuousOn_uncurry_sq (hcDzDz.mono hquad))
      (fun z hz θ => by rw [DzDz_eq_zero_of_vanish hsupp θ hz]; ring)
      (exists_bound_box_general (continuousOn_uncurry_sq (hcDzDz.mono hbox)))
    simpa only [Work.FTS.EllipticEst.ddInt, Work.FTS.EllipticEst.thEta] using h
  have h2 : (∫ p : ℝ × ℝ, (Work.Spaces.Dz G p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = Work.FTS.EllipticEst.dInt G := by
    have h := prod_eq_iterated_aux (δ := δ) (R := R) hδ
      (F := fun z θ => (Work.Spaces.Dz G z θ) ^ 2)
      (continuousOn_uncurry_sq (hcDz.mono hquad))
      (fun z hz θ => by rw [Dz_eq_zero_of_vanish hsupp θ hz]; ring)
      (exists_bound_box_general (continuousOn_uncurry_sq (hcDz.mono hbox)))
    simpa only [Work.FTS.EllipticEst.dInt, Work.FTS.EllipticEst.thEta] using h
  have h3 : (∫ p : ℝ × ℝ, (Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = Work.FTS.EllipticEst.ttInt G := by
    have h := prod_eq_iterated_aux (δ := δ) (R := R) hδ
      (F := fun z θ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2)
      (continuousOn_uncurry_sq (hchh.mono hquad))
      (fun z hz θ => by rw [pth_pth_eq_zero_of_vanish hsupp hz θ]; ring)
      (exists_bound_box_general (continuousOn_uncurry_sq (hchh.mono hbox)))
    simpa only [Work.FTS.EllipticEst.ttInt, Work.FTS.EllipticEst.thEta] using h
  exact ⟨h1, h2, h3⟩

end Work.Blocks.IMC
