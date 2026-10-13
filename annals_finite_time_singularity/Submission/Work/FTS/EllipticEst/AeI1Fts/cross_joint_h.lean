import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_slice_ae
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk
import Submission.Work.FTS.EllipticEst.H2W.SlotA.crossThetaIbp
import Submission.Work.FTS.EllipticEst.H2W.SlotA.sharpHardyOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/cross_joint_h` — the `z`-integrated cross identity of `I₁` in the class `AeData`

The target `Work.FTS.EllipticEst.AeI1Fts.cross_joint_h`: for a datum
`h : H2W.Ae.AeData α u G` together with the two `ℋ⁰`-honesties of the slots

* `U u = z ∂_z u` (`Work.FTS.EllipticEst.AeI1Fts.U`) and
* `V u = z ∂_z ∂_θ u` (`Work.FTS.EllipticEst.AeI1Fts.V`, the Clairaut twin of `∂_θ(U u)`),

and the three *almost every* `z`-integrabilities of the slice integrands (`hintA`, `hintN`,
`hintC`) of the cross identity, one has

`∫_z w(z)² ∫_θ U·V·cos(2θ)·sin(2θ)^{-1-η}
   = ∫_z w(z)² ∫_θ U²·sin(2θ)^{-η}
     + (1+η) · ∫_z w(z)² ∫_θ U²·cos²(2θ)·sin(2θ)^{-2-η}`,

i.e. the `θ`-integration by parts `CROSS = ⟨U,U⟩ + (1+η)N` of `H2W.SlotA.cross_theta_ibp`
(Elgindi, Annals **194** (2021), tex 873–890) applied slice by slice and then integrated
against the radial weight `w²`.

## Route

* For a.e. `z > 0` the slice `v := U u z ·` is `C^∞` on the open interval and the three
  integrability hypotheses of `cross_theta_ibp` are exactly `hintA`, `hintN`, `hintC` (with
  `∂_θ(U u z ·) = V u z ·` from `N_bound.slice_deriv_eq`), so the slice identity
  `cross_theta_ibp` gives the pointwise identity of the two `z`-integrands.
* The two outer integrals on the right are *integrable*:
  * `∫_z w²∫_θ U²σ` and `∫_z w²∫_θ V²σ` come from the `ℋ⁰`-honesties `hU`, `hV`
    (`HkIntegrand α 0 f = w²f²σ` on `Iθ`, then restrict `Iz` to `(0,∞)`);
  * `∫_z w²∫_θ U²cos²σ₂` needs the sharp slicewise Hardy inequality `hardy_slice_ae`
    (`∫_θ U²cos²σ₂ ≤ (1+η)^{-2}∫_θ V²σ` for a.e. `z`), the `a.e.`-strong measurability of
    the partial integral (`AEStronglyMeasurable.integral_prod_right'` applied to the joint
    integrand, which is continuous on the open quadrant) and `Integrable.mono'`.
* `MeasureTheory.integral_add` + `MeasureTheory.integral_const_mul` then split the outer
  integral of the sum.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Integrability of the weighted slice energies -/

/-- **The `w²`-weighted slice energy `∫_θ f²σ` is integrable in `z`** as soon as the `ℋ⁰`-norm
of `f` is honest: `HkIntegrand α 0 f = w²·(f²σ)` on `Iθ`, and `h.2` supplies the integrability
of the outer iterated integral over `Iz` (restricted to `(0,∞)`). -/
private theorem integrableOn_w2_slice {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (f z θ) ^ 2 * sigE θ)
      (Set.Ioi 0) := by
  have h1 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
      Work.Spaces.Iz := hf.2
  have h2 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * sigE θ) Work.Spaces.Iz := by
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun z _ => ?_) measurableSet_Ici
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [hkIntegrand_zero_eq_of_mem α f hθ]
    ring
  have h3 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθo, (f z θ) ^ 2 * sigE θ) Work.Spaces.Iz := by
    refine MeasureTheory.IntegrableOn.congr_fun h2 (fun z _ => ?_) measurableSet_Ici
    congr 1
    exact (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2))).symm
  exact h3.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz))

/-- **The `w²`-weighted `N`-slice energy `∫_θ U²cos²(2θ)σ₂` is integrable in `z`.**  The
sharp slicewise Hardy inequality `hardy_slice_ae` dominates it a.e. by `(1+η)^{-2}∫_θ V²σ`,
whose `w²`-weighted `z`-integral is integrable by `integrableOn_w2_slice`; the partial integral
is a.e. strongly measurable because the joint integrand is continuous on the open quadrant. -/
private theorem integrableOn_w2_N {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (U u)) (hV : Work.Spaces.HkMem α 0 (V u)) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      (Set.Ioi 0) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hVW := integrableOn_w2_slice (α := α) (f := V u) hV
  have hsl := hardy_slice_ae h hU hV
  -- ## a.e. strong measurability of the partial integral
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hjoint : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (U u p.1 p.2) ^ 2 * (Real.cos (2 * p.2)) ^ 2 * sig2 p.2)
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Iθo)) := by
      rw [MeasureTheory.Measure.prod_restrict]
      refine ContinuousOn.aestronglyMeasurable ?_
        (measurableSet_Ioi.prod measurableSet_Ioo)
      have hUc : ContinuousOn (fun p : ℝ × ℝ => U u p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (smoothOpen_U hS).continuousOn
      have hcos : ContinuousOn (fun p : ℝ × ℝ => (Real.cos (2 * p.2)) ^ 2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        ((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn).pow 2
      have hsig : ContinuousOn (fun p : ℝ × ℝ => sig2 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
        have hsin : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
          Real.continuous_sin.comp (continuous_const.mul continuous_snd)
        have h := hsin.continuousOn.rpow_const (p := -(2 + Work.Spaces.eta))
          (fun p hp => Or.inl (by
            obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
            exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
              (by linarith [Real.pi_pos]))))
        simpa only [sig2, Work.FTS.EllipticEst.Q0] using h
      exact ((hUc.pow 2).mul hcos).mul hsig
    have hInt := hjoint.integral_prod_right'
    have hw : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
        funext z; rw [Work.Spaces.w]
      rw [hfun]
      refine ((ContinuousOn.div ?_ ?_ ?_).pow 2).aestronglyMeasurable measurableSet_Ioi
      · fun_prop
      · fun_prop
      · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
    exact hw.mul hInt
  -- ## the domination by the integrable `V`-energy
  refine MeasureTheory.Integrable.mono'
    (hVW.const_mul (1 / (1 + Work.Spaces.eta) ^ 2)) haesm ?_
  filter_upwards [hsl] with z hz
  have hBnn : 0 ≤ ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ := by
    by_cases hint : MeasureTheory.IntegrableOn
      (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) Iθo
    · exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by
          rw [sig2]
          exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos])) _))
    · rw [MeasureTheory.integral_undef hint]
  have hVnn : 0 ≤ ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (by
        rw [sigE]
        exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])) _))
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hBnn)]
  calc (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ
      ≤ (Work.Spaces.w z) ^ 2
          * ((1 / (1 + Work.Spaces.eta) ^ 2)
              * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) :=
        mul_le_mul_of_nonneg_left hz (sq_nonneg _)
    _ = (1 / (1 + Work.Spaces.eta) ^ 2)
          * ((Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) := by ring

/-! ## The target -/

theorem cross_joint_h {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u))
    (hintA : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.AeI1Fts.U u z θ) ^ 2
        * Work.FTS.EllipticEst.AeI1Fts.sigE θ) (Set.Ioo 0 (Real.pi / 2)))
    (hintN : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.AeI1Fts.U u z θ) ^ 2
        * (Real.cos (2 * θ)) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sig2 θ)
        (Set.Ioo 0 (Real.pi / 2)))
    (hintC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.AeI1Fts.U u z θ
        * Work.FTS.EllipticEst.AeI1Fts.V u z θ * Real.cos (2 * θ)
        * Work.FTS.EllipticEst.AeI1Fts.sig1 θ) (Set.Ioo 0 (Real.pi / 2))) :
    (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
          * Real.cos (2 * θ) * Work.FTS.EllipticEst.AeI1Fts.sig1 θ)
      = (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.FTS.EllipticEst.AeI1Fts.U u z θ) ^ 2
              * Work.FTS.EllipticEst.AeI1Fts.sigE θ)
        + (1 + Work.Spaces.eta) * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Work.FTS.EllipticEst.AeI1Fts.U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
                  * Work.FTS.EllipticEst.AeI1Fts.sig2 θ) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hη : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos
  have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  -- ## integrability of the two outer integrands of the right-hand side
  have hAint : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (U u z θ) ^ 2 * sigE θ)
      (Set.Ioi 0) := integrableOn_w2_slice (α := α) (f := U u) hU
  have hBint : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      (Set.Ioi 0) := integrableOn_w2_N h hU hV
  -- ## the a.e. slicewise identity, multiplied by `w²`
  have hae : (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθo, U u z θ * V u z θ * Real.cos (2 * θ) * sig1 θ)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
      (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Iθo, (U u z θ) ^ 2 * sigE θ)
        + (1 + Work.Spaces.eta)
          * ((Work.Spaces.w z) ^ 2
              * ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)) := by
    filter_upwards [hintA, hintN, hintC, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with z hA hN hC hz
    -- the slice is `C^∞`, hence differentiable, on the open interval
    have hv : ∀ θ ∈ Iθo, HasDerivAt (fun θ' => U u z θ') (deriv (fun θ' => U u z θ') θ) θ := by
      intro θ hθ
      have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => U u z θ') Iθo :=
        (smoothOpen_U hS).curry_θ hz
      exact ((hcd.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    -- the three integrability hypotheses of the slice identity, in its own notation
    have hA' : MeasureTheory.IntegrableOn
        (fun θ => (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Iθo := by
      simpa only [sigE] using hA
    have hN' : MeasureTheory.IntegrableOn
        (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta)) Iθo := by
      refine MeasureTheory.IntegrableOn.congr_fun hN (fun θ _ => ?_) measurableSet_Ioo
      rw [sig2, show -(2 + Work.Spaces.eta) = -2 - Work.Spaces.eta by ring]
    have hC' : MeasureTheory.IntegrableOn
        (fun θ => U u z θ * deriv (fun θ' => U u z θ') θ * Real.cos (2 * θ)
          * (Real.sin (2 * θ)) ^ (-1 - Work.Spaces.eta)) Iθo := by
      refine MeasureTheory.IntegrableOn.congr_fun hC (fun θ hθ => ?_) measurableSet_Ioo
      rw [sig1, show -(1 + Work.Spaces.eta) = -1 - Work.Spaces.eta by ring,
        slice_deriv_eq hS hz hθ]
    -- the slicewise θ-integration by parts
    have hcross := Work.FTS.EllipticEst.H2W.SlotA.cross_theta_ibp Work.Spaces.eta hη hη1
      (fun θ => U u z θ) hv hA' hC' hN'
    -- rewrite its statement into the notation of the target
    have hL : (∫ θ in Iθo, U u z θ * deriv (fun θ' => U u z θ') θ * Real.cos (2 * θ)
          * (Real.sin (2 * θ)) ^ (-1 - Work.Spaces.eta))
        = ∫ θ in Iθo, U u z θ * V u z θ * Real.cos (2 * θ) * sig1 θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
      rw [sig1, show -(1 + Work.Spaces.eta) = -1 - Work.Spaces.eta by ring,
        slice_deriv_eq hS hz hθ]
    have hA'' : (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        = ∫ θ in Iθo, (U u z θ) ^ 2 * sigE θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      rw [sigE]
    have hN'' : (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta))
        = ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      rw [sig2, show -(2 + Work.Spaces.eta) = -2 - Work.Spaces.eta by ring]
    rw [hL, hA'', hN''] at hcross
    rw [hcross]
    ring
  -- ## split the outer integral
  rw [MeasureTheory.integral_congr_ae hae,
    MeasureTheory.integral_add hAint (hBint.const_mul (1 + Work.Spaces.eta)),
    MeasureTheory.integral_const_mul]

end Work.FTS.EllipticEst.AeI1Fts
