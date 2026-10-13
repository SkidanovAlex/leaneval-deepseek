/-
Copyright: work module for the Elgindi finite-time singularity project.

# `(∂_z f)²·sin(2θ)^{-η}` on a compact `z`-box, from `C⁴`-regularity only

This is the `C⁴`-regularity version of `Work.FTS.CoercivityFix.Coer1T.Hardy.pzSqSeta_box_integrable`.
The latter is stated for a datum which is `SmoothQuad` (`C^∞` on the open quadrant), a
hypothesis that is far stronger than what the estimate actually needs.  Here the only regularity
assumption is `ContDiffOn ℝ 4 (Function.uncurry f) Q0` — four continuous derivatives on the open
quadrant `Q0 = (0,∞) × (0,π/2)` — together with the weighted membership `HkMem α 4 f`.

The argument is that of the `C^∞`-version: on the compact box `[a,b] × Iθ` the target is
dominated by the first `D_z`-slot of the `ℋ⁴`-integrand,

  `(∂_z f)² sin(2θ)^{-η} ≤ (b²/(1+a)⁴) · (D_z f · w(z)/sin(2θ)^{η/2})²`
  (`Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces.pzSqSeta_le_Dz1_mul`),

which is a pointwise bound needing no regularity at all.  The only place where `C^∞`-regularity
was used in the `C^∞`-version is the *measurability* of the two integrands; `C⁴` suffices,
because the plain `z`-derivative `pz f` (of order one) is then continuous on `Q0`, hence so are
the target and the `D_z`-slot, and then
`Work.Spaces.aesm_of_continuousOn_Qd` gives a.e. strong measurability for the product measure
`(volume|_[0,∞)) × (volume|_Iθ)`.

The integrability of the dominating slot on that product measure is Tonelli
(`Work.Spaces.integrable_prod_of_iterated`): its angular slices are pointwise dominated by
`HkIntegrand α 4 f` (`hmem.1` together with `Work.Spaces.sq_le_HkIntegrand_z`) and its iterated
integral by the iterated integral of `HkIntegrand` (`hmem.2`).  Nothing beyond the `i = 1` slot
of the `ℋ⁴`-integrand is used, so `HkMem` at level `4` is more than enough; level `1` would do.

Axioms: `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.pzSqSeta_box_integrable
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge.Pieces

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Continuity on the open quadrant, from four continuous derivatives -/

/-- **The plain `z`-derivative of a `C⁴` datum on the open quadrant is continuous.**
`pz f` is the directional derivative of `Function.uncurry f` in the direction `(1,0)`, which on
the open quadrant `Q0` is `fderiv ℝ (Function.uncurry f) p (1,0)`.  Four continuous derivatives
give that `fderiv ℝ (Function.uncurry f)` is `C³` on `Q0` (via `ContDiffOn.fderivWithin` plus
`fderivWithin_of_isOpen`), hence continuous, and evaluation at the fixed vector `(1,0)`
preserves continuity. -/
private theorem continuousOn_pz_of_contDiffOn_four {f : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hfd : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry f) p)
      Work.FTS.EllipticEst.Q0 := by
    have h' := hC.fderivWithin Work.FTS.EllipticEst.isOpen_Q0.uniqueDiffOn (m := 3)
      (by norm_num)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hp]
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) p) ((1 : ℝ), (0 : ℝ)))
      Work.FTS.EllipticEst.Q0 :=
    hfd.continuousOn.clm_apply
      (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ))) _)
  refine hcont.congr ?_
  intro p hp
  exact Work.Spaces.pz_eq_fderiv ((hC.differentiableOn (by norm_num)).differentiableAt
    (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))

/-- `θ ↦ sin(2θ)^c` is continuous on the open quadrant, where `sin(2θ) > 0`. -/
private theorem continuousOn_sin_rpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      Work.FTS.EllipticEst.Q0 := by
  have hpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    rw [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hpos p hp)))

/-- The `D_z`-slot integrand `(D_z f · w/sin(2θ)^{η/2})²` of the `ℋ¹`-integrand is continuous
on the open quadrant, as soon as `pz f` is. -/
private theorem continuousOn_Dz1slot_Q0 {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2)
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.FTS.EllipticEst.Q0 := by
  have hDz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 1 f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.DzIter 1 f p.1 p.2)
        = fun p : ℝ × ℝ => p.1 * Work.Spaces.pz f p.1 p.2 := by
      funext p
      simp [Work.Spaces.DzIter, Work.Spaces.Dz]
    rw [hfun]
    exact continuousOn_fst.mul hcont
  exact (hDz.mul Work.FTS.EllipticEst.continuousOn_wdivsin_Q0).pow 2

/-- The target integrand `(∂_z f)² · sin(2θ)^{-η}` is continuous on the open quadrant, as soon
as `pz f` is. -/
private theorem continuousOn_pzSqSeta_Q0 {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2)
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pz f p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Work.FTS.EllipticEst.Q0 :=
  (hcont.pow 2).mul (continuousOn_sin_rpow_Q0 _)

/-! ## Integrability of the `D_z`-slot on the product measure -/

/-- The first `D_z`-slot of the `ℋ⁴`-integrand is integrable for the product of the two
restricted Lebesgue measures `(volume|_[0,∞)) × (volume|_Iθ)`.

`Work.Spaces.integrable_prod_of_iterated` (Tonelli) reduces this to the angular slices and the
iterated integral: both are obtained from `hmem` by the pointwise bound
`Work.Spaces.sq_le_HkIntegrand_z`, and the a.e. strong measurability of the uncurried slot
comes from its continuity on the open quadrant (`hcont`).  The value at `z = 0` is irrelevant
(the radial weight vanishes there), but it costs nothing to handle it. -/
private theorem integrable_Dz1slot_prod (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter 1 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hcont := continuousOn_Dz1slot_Q0 (continuousOn_pz_of_contDiffOn_four hC)
  have hAESM : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  refine (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ : ℝ => (Work.Spaces.DzIter 1 f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun z θ => sq_nonneg _) hAESM ?_ ?_).1
  · -- the angular slices are integrable, with the `ℋ⁴`-integrand as dominating function
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz => ?_
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · -- at `z = 0` the radial weight vanishes, so the slice is identically zero
      rw [← hz0]
      rw [show (fun θ : ℝ => (Work.Spaces.DzIter 1 f 0 θ
          * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          = fun _ : ℝ => (0 : ℝ) from by
        funext θ
        rw [Work.Spaces.w]
        norm_num]
      exact integrableOn_zero
    · refine MeasureTheory.Integrable.mono' (hmem.1 z hz) ?_ ?_
      · simpa only [Function.uncurry_apply_pair] using
          (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos)
      · rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
          rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
        exact Eventually.of_forall fun θ _ => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 1 (by norm_num)
  · -- the iterated integral is dominated by the iterated integral of `HkIntegrand`
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 1 f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      hAESM.integral_prod_right'
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    refine hmem.2.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with s hs
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
    exact MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => sq_nonneg _)
      (hmem.1 s hs)
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from by
          rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
        (fun θ _ => Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 1 (by norm_num)))

/-! ## The statement -/

theorem pzSqSeta_box_integrable_of_contDiffOn_four (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn
        (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz f s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  have hpzcont := continuousOn_pz_of_contDiffOn_four hC
  intro a b ha hab
  set K : ℝ := b ^ 2 / (1 + a) ^ 4 with hKdef
  -- the `D_z`-slot integrand, integrable on the whole domain
  have hGint := integrable_Dz1slot_prod α hC hmem
  -- the box is contained in the domain `Iz ×ˢ Iθ`
  have hsub : Set.Icc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    intro p hp
    rw [Set.mem_prod] at hp
    exact ⟨le_trans (le_of_lt ha) hp.1.1, hp.2⟩
  -- hence the `D_z`-slot integrand is integrable on the box
  have hGbox : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter 1 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict] at hGint
    exact hGint.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  refine MeasureTheory.Integrable.mono' (hGbox.const_mul K) ?_ ?_
  · -- a.e. strong measurability of the target on the box
    have hA := Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_pzSqSeta_Q0 hpzcont)
    rw [MeasureTheory.Measure.prod_restrict] at hA
    exact hA.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  · -- the pointwise box bound
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp
    obtain ⟨z, θ⟩ := p
    have hsin : 0 ≤ Real.sin (2 * θ) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
      · linarith [hθ.1]
      · linarith [hθ.2, Real.pi_pos]
    have hnn : 0 ≤ (Work.Spaces.pz f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)
    show ‖(Work.Spaces.pz f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))‖
      ≤ K * (Work.Spaces.DzIter 1 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    rw [Real.norm_of_nonneg hnn, hKdef]
    exact Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces.pzSqSeta_le_Dz1_mul
      (f := f) ha hab z hz θ hθ

end

end Work.FTS.MeridianDyn.Bridge.Pieces
