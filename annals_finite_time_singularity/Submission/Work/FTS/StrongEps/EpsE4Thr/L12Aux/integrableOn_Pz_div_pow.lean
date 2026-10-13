import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The angular interval `Iθ = [0, π/2]` is measurable. -/
private lemma measurableSet_Iθ_fts : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

/-- **A.e. strong measurability of the `z`-slice integral.**

The uncurried integrand
`(z,θ) ↦ (D_z^k x (z,θ))² · sin(2θ)^{-η} / z⁴` is continuous on the open quadrant
(`SmoothOpen x` keeps `D_z^k x` continuous there, and the two weights are continuous on the
open quadrant because `sin(2θ) > 0` and `z ≠ 0` there), so
`Work.Spaces.aesm_of_continuousOn_Qd` together with
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` gives the a.e. strong measurability
of its angular integral. -/
private lemma aesm_integral_Pzsplit (x : Work.FTS.Galerkin.Fn) (k : ℕ)
    (hreg : Work.FTS.EllipticEst.SmoothOpen x) :
    AEStronglyMeasurable (fun z : ℝ => ∫ θ : ℝ,
        ((Work.Spaces.DzIter k x z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          / z ^ 4) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter k x p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
        / p.1 ^ 4) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).mono
        (subset_univ _)
    have hsinpow : ContinuousOn (fun p : ℝ × ℝ =>
        (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      refine hsin.rpow_const (fun p hp => Or.inl ?_)
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos]))
    exact ContinuousOn.div (ContinuousOn.mul ((hreg.DzIter k).continuousOn.pow 2) hsinpow)
      (continuousOn_fst.pow 4) (fun p hp => pow_ne_zero 4 (ne_of_gt hp.1))
  exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'

/-- **A.e. strong measurability of `z ↦ Pz x k z / z⁴` on `(0,1)`.**

For `z > 0` one may pull the factor `z^{-4}` inside the angular integral
(`MeasureTheory.integral_div`), which identifies the function with the slice integral of the
previous lemma; restricting the measure to `(0,1)` gives the claim. -/
private lemma aesm_Pz_div_pow {α : ℝ} {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) (k : ℕ) :
    AEStronglyMeasurable (fun z : ℝ => Pz x k z / z ^ 4)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Work.Spaces.Iz := fun z hz => le_of_lt hz.1
  have hA : AEStronglyMeasurable (fun z : ℝ => ∫ θ : ℝ,
      ((Work.Spaces.DzIter k x z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        / z ^ 4) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    have h1 := (aesm_integral_Pzsplit x k hx.reg).restrict (s := Set.Ioo (0 : ℝ) 1)
    rwa [MeasureTheory.Measure.restrict_restrict_of_subset hsub] at h1
  refine hA.congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
  show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter k x z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 4) = Pz x k z / z ^ 4
  rw [MeasureTheory.integral_div, Pz]

/-- **The pointwise bound `Pz x k z / z⁴ ≤ ∫_θ HkIntegrand α 10 x z θ` for `z > 0`.**

`(D_z^k x · w / sin(2θ)^{η/2})²` is a summand of `HkIntegrand α 10 x` (`k ≤ 10`), and by the
weight identity `summand_sq_eq` it equals `(D_z^k x)² · sin(2θ)^{-η} · w²`.  Integrating in `θ`
and pulling `w(z)²` out of the integral gives `w(z)² · Pz x k z ≤ ∫_θ HkIntegrand α 10 x z θ`;
on the other hand `Pz x k z / z⁴ · (1+z)⁴ = Pz x k z · w(z)²` and `(1+z)⁴ ≥ 1`. -/
private lemma Pz_div_pow_le_integral_HkIntegrand {α : ℝ} {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {k : ℕ} (hk : k ≤ 10) {z : ℝ} (hz : 0 < z) :
    Pz x k z / z ^ 4 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 10 x z θ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 10 x z θ)
      Work.Spaces.Iθ := hx.mem10.1 z hzI
  -- the pointwise bound on the angular interval
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, (Work.Spaces.DzIter k x z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 10 x z θ := by
    intro θ hθ
    rw [← summand_sq_eq x k hθ]
    exact Work.Spaces.sq_le_HkIntegrand_z α 10 x z θ k hk
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ : ℝ => (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter k x z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ_fts
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _)))
  have hle : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter k x z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => Work.Spaces.HkIntegrand α 10 x z θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ_fts (fun θ hθ => by
      have h := hpt θ hθ
      show (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter k x z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ Work.Spaces.HkIntegrand α 10 x z θ
      rw [show (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter k x z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          = (Work.Spaces.DzIter k x z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.w z) ^ 2 from by ring]
      exact h)
  have hmono : (Work.Spaces.w z) ^ 2 * Pz x k z
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 10 x z θ := by
    have hstep : (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter k x z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.DzIter k x z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
      (MeasureTheory.integral_const_mul _ _).symm
    rw [Pz, hstep]
    exact MeasureTheory.integral_mono_of_nonneg hnn hInt hle
  -- `Pz / z⁴ ≤ w² · Pz`
  have hkey : Pz x k z * (Work.Spaces.w z) ^ 2 = Pz x k z / z ^ 4 * (1 + z) ^ 4 := by
    rw [Work.Spaces.w]
    field_simp
  have hchain : Pz x k z / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 * Pz x k z := by
    have hnn2 : 0 ≤ Pz x k z / z ^ 4 :=
      div_nonneg (Pz_nonneg x k z) (pow_nonneg hz.le 4)
    have h1 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith)
    calc Pz x k z / z ^ 4 ≤ Pz x k z / z ^ 4 * (1 + z) ^ 4 :=
          le_mul_of_one_le_right hnn2 h1
      _ = Pz x k z * (Work.Spaces.w z) ^ 2 := hkey.symm
      _ = (Work.Spaces.w z) ^ 2 * Pz x k z := by ring
  exact le_trans hchain hmono

/-- **`Pz x k · z^{-4}` is integrable on `(0,1)` for a `ClassC` profile.**

Here `Pz x k z = ∫_{Iθ} (D_z^k x (z,θ))² · sin(2θ)^{-η} dθ` (`η = 99/100`,
`D_z = z ∂_z`, `Iθ = [0,π/2]`; see `Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs`).

Proof route: `ClassC α x` carries `reg : SmoothOpen x` and `mem10 : HkMem α 10 x`.  For
`z ∈ Iz` the slot `(D_z^k x z θ * (w z / sin(2θ)^{η/2}))²` is a summand of
`HkIntegrand α 10 x z θ` (`Work.Spaces.sq_le_HkIntegrand_z`, `k ≤ 4 ≤ 10`), and by
`L12Aux.summand_sq_eq` (proved in `Defs`) it equals
`(D_z^k x z θ)² * sin(2θ)^{-η} * (w z)²`.  Hence, with
`F z := ∫ θ in Iθ, (DzIter k x z θ * (w z / sin(2θ)^{η/2}))²`, one has the pointwise bound
`Pz x k z / z^4 ≤ F z` for `z ∈ (0,1)` (because `(w z)² z^4 = (1+z)^4 ≥ 1`), and
`F` is integrable on `Iz` (dominated by `z ↦ ∫ θ, HkIntegrand α 10 x z θ`, which is integrable
by `mem10.2`); see `Work.Spaces.L2Sq_DzIter_le_HkSq` and, for the measurability of `F`,
`Work.Spaces.aesm_of_continuousOn_Qd` together with
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` and
`Work.FTS.EllipticEst.SmoothOpen.continuousOn_summand`.  Restricting to `(0,1)` and applying
`MeasureTheory.Integrable.mono'` gives the claim. -/
theorem integrableOn_Pz_div_pow {α : ℝ} {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {k : ℕ} (hk : k ≤ 4) :
    MeasureTheory.IntegrableOn (fun z => Pz x k z / z ^ 4) (Set.Ioo (0 : ℝ) 1) := by
  have hk10 : k ≤ 10 := by omega
  have hmajI : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 10 x z θ)
      Work.Spaces.Iz := hx.mem10.2
  have hmaj : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 10 x z θ)
      (Set.Ioo (0 : ℝ) 1) :=
    hmajI.mono_set (fun z hz => le_of_lt hz.1)
  refine MeasureTheory.Integrable.mono' hmaj (aesm_Pz_div_pow hx k) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
  have hle := Pz_div_pow_le_integral_HkIntegrand hx hk10 hz.1
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Pz_nonneg x k z) (pow_nonneg hz.1.le 4))]
  exact hle

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
