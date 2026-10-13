/-
# The angular-transport coercivity step `wip_TrV_ge`

For the angular transport term of `𝓛_Γ^T` (the paper's `3 sin(2θ) ∂_θ f/(1+z)`), the
weighted `L²` pairing is *negative* only up to the size of the weight `v` itself:

  `-(3α/10) ⟨v, v⟩_θ ≤ ⟨ -(3/(1+z)) D_θ v, v ⟩_θ`,

where `⟨g₁,g₂⟩_θ = ∫∫ g₁ g₂ · w² sin(2θ)^{-γ}` is the angular weight `thetaW α`.

Indeed `D_θ v · v = ½ D_θ(v²)`, so the angular integration by parts against
`sin(2θ)^{-γ}` (with the boundary terms of `sin(2θ)^{-(γ-1)}v²` killed by the one-sided
vanishing hypotheses at `0⁺` and `(π/2)⁻`) gives

  `∫ sin(2θ)^{-γ} D_θ v · v = (γ-1) ∫ cos(2θ) sin(2θ)^{-γ} v²`,

with `γ - 1 = α/10`.  Since `cos(2θ) ≤ 1` on `Iθ` and `1/(1+z) ≤ 1` on `Iz`, the
inequality above follows.  The one-dimensional integration by parts is
`Work.Coercivity.slice_ibp`; the passage from the slices to the iterated integral is
Fubini together with the a.e.-slice integrability extracted from the two product
integrability hypotheses.  The remaining pointwise domination of the `cos`-weighted
integrand is `Work.Coercivity.cos_sin_integrable`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.slice_ibp
import Submission.Work.Coercivity.cos_sin_integrable
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

/-- `wip_TrV_ge`: the angular transport pairing `⟨-(3/(1+z)) D_θ v, v⟩_θ` is bounded below
by `-(3α/10)⟨v,v⟩_θ`.  See the module docstring for the proof. -/
theorem wip_TrV_ge (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (v : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd v) (hvan : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α - 1)) * (v z θ) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) (hvan2 : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α - 1)) * (v z θ) ^ 2) (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0)) (hint : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => thetaW α z θ * (Spaces.Dth v z θ) * v z θ / (1 + z))) (Spaces.Iz ×ˢ Spaces.Iθ)) (hint2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => thetaW α z θ * (v z θ) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)) : -(3 * α / 10) * wip (thetaW α) v v ≤ wip (thetaW α) (fun z θ => -(3 / (1 + z)) * Spaces.Dth v z θ) v := by
  -- ## Fubini bridges: the two integrands on the product space
  let Gp : ℝ × ℝ → ℝ := fun p => thetaW α p.1 p.2 * (Spaces.Dth v p.1 p.2) * v p.1 p.2 / (1 + p.1)
  let Bp : ℝ × ℝ → ℝ := fun p => thetaW α p.1 p.2 * (v p.1 p.2) ^ 2
  have hvol : (MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hGp : MeasureTheory.Integrable Gp
      ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [hvol]; exact hint
  have hBp : MeasureTheory.Integrable Bp
      ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [hvol]; exact hint2
  -- ## a.e. slice facts
  have hGslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Gp (z, θ)) (MeasureTheory.volume.restrict Spaces.Iθ) :=
    hGp.prod_right_ae
  have hBslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Bp (z, θ)) (MeasureTheory.volume.restrict Spaces.Iθ) :=
    hBp.prod_right_ae
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz), 0 < z := by
    rw [MeasureTheory.ae_restrict_iff (p := fun z => 0 < z) measurableSet_Ioi,
      MeasureTheory.ae_iff]
    have hset : {z : ℝ | ¬ (z ∈ Spaces.Iz → 0 < z)} = {0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Spaces.Iz, Set.mem_Ici, not_imp]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) h1
      · rintro rfl; exact ⟨le_refl 0, lt_irrefl 0⟩
    rw [hset, Real.volume_singleton]
  -- ## the slice-wise inequality
  have hkey : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
        ≤ (Spaces.gam α - 1) *
            (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ)) := by
    filter_upwards [hGslice, hBslice, hzpos] with z hGz hBz hzp
    -- core integrability, obtained from the two product integrabilities
    have hKcore : MeasureTheory.Integrable
        (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (v z θ) ^ 2)
        (MeasureTheory.volume.restrict Spaces.Iθ) :=
      cos_sin_integrable α v hsm z hzp hBz
    have hIcore : MeasureTheory.Integrable
        (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth v z θ * v z θ)
        (MeasureTheory.volume.restrict Spaces.Iθ) := by
      refine (hGz.const_mul ((1 + z) / (Spaces.w z) ^ 2)).congr
        (Filter.Eventually.of_forall (fun θ => ?_))
      dsimp only [Gp, thetaW]
      have hw : Spaces.w z ≠ 0 := by
        rw [Spaces.w]; exact div_ne_zero (by positivity) (by positivity)
      have h1z : (1 : ℝ) + z ≠ 0 := by positivity
      field_simp
    -- the one-dimensional integration by parts
    have hslice := slice_ibp α hα v hsm hvan hvan2 z hzp hIcore hKcore
    -- pull the `θ`-independent factor `w z ^ 2/(1+z)` out of the slice integrals
    have h1 : (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
        = ((Spaces.w z) ^ 2 / (1 + z)) *
            (∫ θ, (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth v z θ * v z θ
              ∂(MeasureTheory.volume.restrict Spaces.Iθ)) := by
      rw [show (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
          = ∫ θ, ((Spaces.w z) ^ 2 / (1 + z)) *
              ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth v z θ * v z θ)
              ∂(MeasureTheory.volume.restrict Spaces.Iθ) from
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun θ => by dsimp only [Gp, thetaW]; ring))]
      rw [MeasureTheory.integral_const_mul]
    -- pointwise domination on `Iθ`
    have hLe : (∫ θ, ((Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (v z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Spaces.Iθ))
        ≤ (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ)) := by
      have hintL : MeasureTheory.Integrable (fun θ => ((Spaces.w z) ^ 2 / (1 + z)) *
          (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (v z θ) ^ 2))
          (MeasureTheory.volume.restrict Spaces.Iθ) :=
        (hKcore.const_mul ((Spaces.w z) ^ 2 / (1 + z))).congr
          (Filter.Eventually.of_forall (fun θ => by ring))
      refine MeasureTheory.integral_mono_ae hintL hBz ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Spaces.Iθ from measurableSet_Icc)] with θ hθ
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      have hA : 0 ≤ (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (v z θ) ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)) (sq_nonneg _)
      have hcoef : Real.cos (2 * θ) / (1 + z) ≤ 1 := by
        have h1z : 0 < 1 + z := by linarith [hzp]
        rw [div_le_iff₀ h1z]
        linarith [Real.cos_le_one (2 * θ)]
      dsimp only [Bp, thetaW]
      calc ((Spaces.w z) ^ 2 / (1 + z)) *
              (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (v z θ) ^ 2)
          = (Real.cos (2 * θ) / (1 + z)) *
              ((Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (v z θ) ^ 2) := by
            ring
        _ ≤ 1 * ((Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (v z θ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcoef hA
        _ = (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (v z θ) ^ 2 :=
            one_mul _
    calc (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
        = ((Spaces.w z) ^ 2 / (1 + z)) *
            (∫ θ, (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth v z θ * v z θ
              ∂(MeasureTheory.volume.restrict Spaces.Iθ)) := h1
      _ = ((Spaces.w z) ^ 2 / (1 + z)) *
            ((Spaces.gam α - 1) *
              (∫ θ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (v z θ) ^ 2
                ∂(MeasureTheory.volume.restrict Spaces.Iθ))) := by rw [hslice]
      _ = (Spaces.gam α - 1) *
            (∫ θ, ((Spaces.w z) ^ 2 / (1 + z)) *
              (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (v z θ) ^ 2)
              ∂(MeasureTheory.volume.restrict Spaces.Iθ)) := by
            rw [MeasureTheory.integral_const_mul]; ring
      _ ≤ (Spaces.gam α - 1) *
            (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ)) :=
            mul_le_mul_of_nonneg_left hLe (by rw [Spaces.gam]; linarith)
  -- ## integrate over `z`
  have hFz : MeasureTheory.Integrable
      (fun z => ∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
      (MeasureTheory.volume.restrict Spaces.Iz) := hGp.integral_prod_left
  have hBzI : MeasureTheory.Integrable
      (fun z => ∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
      (MeasureTheory.volume.restrict Spaces.Iz) := hBp.integral_prod_left
  have hmono : (∫ z, (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Spaces.Iz))
      ≤ (∫ z, (Spaces.gam α - 1) *
          (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Spaces.Iz)) :=
    MeasureTheory.integral_mono_ae hFz (hBzI.const_mul _) hkey
  have hmono2 : (∫ z, (Spaces.gam α - 1) *
          (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Spaces.Iz))
      = (Spaces.gam α - 1) *
          (∫ z, (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
            ∂(MeasureTheory.volume.restrict Spaces.Iz)) :=
    MeasureTheory.integral_const_mul _ _
  -- ## the two product integrals
  have hAG : (∫ p, Gp p
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)))
      = (∫ z, (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Spaces.Iz)) :=
    MeasureTheory.integral_prod Gp hGp
  have hAB : (∫ p, Bp p
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)))
      = (∫ z, (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Spaces.Iz)) :=
    MeasureTheory.integral_prod Bp hBp
  have hAGle : (∫ p, Gp p
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)))
      ≤ (Spaces.gam α - 1) * (∫ p, Bp p
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))) := by
    rw [hAG, hAB]
    linarith [hmono, hmono2]
  -- ## identify the two `wip`s with the product integrals
  have h2' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => v z θ * v z θ * thetaW α z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) :=
    hint2.congr (Filter.Eventually.of_forall (fun p => by
      dsimp only [Function.uncurry]; ring))
  have hwipB : wip (thetaW α) v v
      = (∫ p, Bp p
          ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))) := by
    rw [wip_eq_integral_prod (thetaW α) v v h2']
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [Bp]
    ring
  have hA' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (-(3 / (1 + z)) * Spaces.Dth v z θ) * v z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine (hint.const_mul (-3)).congr (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [Function.uncurry]
    ring
  have hwipA : wip (thetaW α) (fun z θ => -(3 / (1 + z)) * Spaces.Dth v z θ) v
      = -3 * (∫ p, Gp p
          ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))) := by
    rw [wip_eq_integral_prod (thetaW α) (fun z θ => -(3 / (1 + z)) * Spaces.Dth v z θ) v hA']
    rw [show (∫ p, (-(3 / (1 + p.1)) * Spaces.Dth v p.1 p.2) * v p.1 p.2 * thetaW α p.1 p.2
            ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)))
        = ∫ p, (-3) * Gp p
            ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)) from
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun p => by dsimp only [Gp]; ring))]
    rw [MeasureTheory.integral_const_mul]
  -- ## conclusion
  rw [hwipB, hwipA]
  have hBle : 3 * (∫ p, Gp p
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)))
      ≤ 3 * ((Spaces.gam α - 1) * (∫ p, Bp p
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)))) :=
    mul_le_mul_of_nonneg_left hAGle (by norm_num)
  have h5 : 3 * ((Spaces.gam α - 1) * (∫ p, Bp p
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))))
      = (3 * α / 10) * (∫ p, Bp p
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))) := by
    rw [Spaces.gam]; ring
  linarith [hBle, h5]

end Work.Coercivity
