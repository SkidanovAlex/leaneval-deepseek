import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

/-!
## The weighted two-dimensional radial self-pairing bound `dzSelf2dW`

This is the `ψ`-weighted (and unsigned) form of `Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d`:
from the one-dimensional bound `h1d` (with the weight `ψ` and the constant `D`) for every
admissible slice `Y`, we deduce the two-dimensional bound with an arbitrary (not necessarily
positive, not even a.e. non-zero) angular weight `θw`:

`|∫_z ∫_θ w(z)² θw(θ) ψ(z) ((z ∂_z V)(z,θ)) V(z,θ)| ≤ D ∫_z ∫_θ w(z)² |θw(θ)| V(z,θ)²`.

The route is the one of `dzSelf2d`: apply `h1d` to the slices `Y = V(·,θ)` for a.e. `θ`,
multiply by `|θw θ|` and integrate in `θ`, using Fubini to pass between the two orders.  Two
points differ from `dzSelf2d`:

* no positivity of `θw` is assumed, so the slicewise inequality is only needed where
  `θw θ ≠ 0`; on the remaining (possibly non-null) set the whole inner integrand vanishes
  identically because of the factor `θw θ`, and the desired inequality reduces to `0 ≤ 0`;
* the slice integrability that `hF`/`hD2` supply by Fubini is only available after dividing
  by `|θw θ|`, which is why the case split above is needed.

The cross term is *given* as product-integrable (`hcross`), so no a.e.-measurability argument
is required here (unlike in `dzSelf2d`, where it had to be manufactured).
-/

theorem dzSelf2dW {θw : ℝ → ℝ} {ψ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} {D : ℝ}
    (hD0 : 0 ≤ D)
    (h1d : ∀ (Y : ℝ → ℝ), ContDiffOn ℝ 1 Y (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2)
        (Set.Ioi 0) →
      |∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)|
        ≤ D * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)
    (hθwm : AEMeasurable θw (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hV : ∀ θ ∈ Set.Ioo 0 (π / 2), ContDiffOn ℝ 1 (fun z => V z θ) (Set.Ioi 0))
    (hVae : AEMeasurable (Function.uncurry V)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * |θw p.2| * (V p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hD2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * |θw p.2|
        * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hcross : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * θw p.2 * ψ p.1
        * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)|
      ≤ D * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2 := by
  have hΛz : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    Measure.restrict_congr_set Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Iz_ae
  have hΛθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Ith_ae
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    have h := MeasureTheory.ae_restrict_mem (μ := (MeasureTheory.volume : Measure ℝ))
      (s := Set.Ioo (0 : ℝ) (π / 2)) measurableSet_Ioo
    rwa [← hΛθ] at h
  -- slice integrability for a.e. `θ`, available where `θw θ ≠ 0`
  have hsliceF : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θw θ ≠ 0 → MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) (Set.Ioi 0) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable
          (fun z => (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.prod_left_ae hF
    filter_upwards [h1] with θ hθ hne
    have h2 : MeasureTheory.Integrable
        (fun z => |θw θ| * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hθ
    have h3 : MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (abs_ne_zero.mpr hne))
        (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)).mp h2
    rw [hΛz] at h3
    exact h3
  have hsliceD : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θw θ ≠ 0 → MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2) (Set.Ioi 0) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable
          (fun z => (Work.Spaces.w z) ^ 2 * |θw θ| * (z * Work.Spaces.pz V z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.prod_left_ae hD2
    filter_upwards [h1] with θ hθ hne
    have h2 : MeasureTheory.Integrable
        (fun z => |θw θ| * ((Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hθ
    have h3 : MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (abs_ne_zero.mpr hne))
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)).mp h2
    rw [hΛz] at h3
    exact h3
  -- the a.e.-`θ` slicewise 1-D bound
  have hkey : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)|
        ≤ D * (|θw θ| * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) := by
    filter_upwards [haeθ, hsliceF, hsliceD] with θ hmem hsf hsd
    by_cases hne : θw θ = 0
    · have hzero : (∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)) = 0 := by
        have hfun : (fun z => (Work.Spaces.w z) ^ 2 * θw θ * ψ z
              * ((z * Work.Spaces.pz V z θ) * V z θ)) = fun _ => (0 : ℝ) := by
          funext z
          rw [hne]
          ring
        rw [hfun]
        simp
      rw [hzero, abs_zero]
      simp [hne]
    · have h1 := h1d (fun z => V z θ) (hV θ hmem) (hsf hne) (hsd hne)
      have hL : (∫ z in Work.Spaces.Iz,
            (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ))
          = θw θ * (∫ z in Set.Ioi (0 : ℝ),
              (Work.Spaces.w z) ^ 2 * ψ z
                * ((z * Work.Spaces.pz V z θ) * V z θ)) := by
        rw [setIntegral_congr_set Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Iz_ae]
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
        ring
      rw [hL, abs_mul]
      calc |θw θ| * |∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * ψ z
              * ((z * Work.Spaces.pz V z θ) * V z θ)|
          ≤ |θw θ| * (D * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg (θw θ))
        _ = D * (|θw θ| * ∫ z in Set.Ioi (0 : ℝ),
              (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) := by ring
  -- integrability of the upper bound `θ ↦ D * |θw θ| * ∫_z w²V²`
  have hψint : MeasureTheory.Integrable
      (fun θ => |θw θ| * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := MeasureTheory.Integrable.integral_prod_right hF
    have hfun : (fun θ => ∫ z, (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        = fun θ => |θw θ| * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2 := by
      funext θ
      rw [show (fun z => (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2)
          = fun z => |θw θ| * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) from by
            funext z; ring]
      rw [MeasureTheory.integral_const_mul]
      rw [setIntegral_congr_set Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Iz_ae]
    rwa [hfun] at h
  have hRHSint : MeasureTheory.Integrable
      (fun θ => D * (|θw θ| * ∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hψint.const_mul D
  have hLHSint : MeasureTheory.Integrable
      (fun θ => |∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := MeasureTheory.Integrable.integral_prod_right hcross
    exact h.abs
  -- Fubini and the comparison
  have hswap : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ) :=
    MeasureTheory.integral_integral_swap hcross
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)|
      = |∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)| := by
        rw [hswap]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, D * (|θw θ| * ∫ z in Set.Ioi (0 : ℝ),
          (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) :=
        integral_mono_ae hLHSint hRHSint hkey
    _ = D * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [show (fun θ => |θw θ| * ∫ z in Set.Ioi (0 : ℝ),
              (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
            = fun θ => ∫ z in Work.Spaces.Iz,
              (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2 from by
              funext θ
              rw [show (fun z => (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2)
                  = fun z => |θw θ| * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) from by
                    funext z; ring]
              rw [MeasureTheory.integral_const_mul]
              rw [setIntegral_congr_set Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Iz_ae]]
        rw [← MeasureTheory.integral_integral_swap hF]

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
