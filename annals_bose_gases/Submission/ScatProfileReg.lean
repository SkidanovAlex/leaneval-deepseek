import ChallengeDeps
import Mathlib.Order.Interval.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.HalfLineReg
import Submission.ScatProfileGlue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Regularity of the radial scattering profile (Layer 3)

For a *radial* weak scattering solution `w` of a radial potential `v`
(`IsScatteringSolution w v`), the profile `u(r) := r · radialProfile w r`
satisfies the 1D weak equation

    ∫_{r>a} u·χ''  =  ∫_{r>a} scatH v w · χ          (∀ χ ∈ C∞c((a,∞)))

(`ScatProfileGlue.scatH_weak_eq_Ioi`), with `scatH v w` integrable on `(a,∞)`
(`ScatProfileGlue.scatH_integrable_Ioi`), and `u` locally integrable on
`(a,∞)` (`ScatProfileGlue.scat_u_locallyIntegrable_Ioi`).

Instantiating the half-line regularity theorem
(`HalfLineReg.weak_snd_regularity_Ioi`) gives: for every `a > 0`, `u` agrees
a.e. on `(a,∞)` with the `C¹` function

    U(r) := A + B·r + P(r),   P(r) := ∫_{a}^{r} (∫_{a}^{s} scatH v w t dt) ds,

whose derivative is differentiable a.e. with derivative `scatH v w r`.  Since
`u = r·f` (`f := radialProfile w`), the second-derivative identity says that
modulo the a.e. identification `U = u` one has, for `r ≠ 0`,

    U''(r) = scatH v w r = −(1/2)·r·vprof(r)·(1 − f(r))
           = (vprof(r)/2)·(U(r) − r)        a.e. on (a,∞)

i.e. the scattering-profile ODE `U'' = (v/2)(U − id)` holds a.e.  This is the
Carathéodory-regularity step that upgrades the weak equation to a classical
ODE with `L¹` coefficient, the gateway to the maximum-principle bounds
`0 ≤ u ≤ r` (hence `0 ≤ ω ≤ 1`) for the scattering solution.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real Interval

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The twice-primitive of the scattering source profile from the base point
`a`: `scatProfileP v w a r := ∫_{a}^{r}∫_{a}^{s} scatH v w`. -/
noncomputable def scatProfileP (v w : ℝ³ → ℝ) (a r : ℝ) : ℝ :=
  (∫ s : ℝ in a..r, (∫ t : ℝ in a..s, scatH v w t))

/-- **Profile regularity on a half-line.**  For a radial scattering solution
`w` of a radial potential `v` (`tsupport v ⊆ ball 0 R`, `R > 0`), for every
`a > 0` the profile `u(r) := r·radialProfile w r` agrees a.e. on `(a,∞)` with
the `C¹` function `A + B·r + scatProfileP v w a r`, whose derivative is
differentiable a.e. with derivative `scatH v w`. -/
theorem scat_profile_reg_Ioi {v w : ℝ³ → ℝ} {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hvrad : IsRadial v) (hrad : IsRadial w) (hw : IsScatteringSolution w v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) :
    ∃ A B : ℝ,
      (∀ᵐ r : ℝ, a < r →
        r * radialProfile w r = A + B * r + scatProfileP v w a r) ∧
      (∀ r : ℝ, a < r →
        HasDerivAt (fun y : ℝ => A + B * y + scatProfileP v w a y)
          (B + (∫ t : ℝ in a..r, scatH v w t)) r) ∧
      (∀ᵐ r : ℝ, a < r →
        HasDerivAt (deriv (fun y : ℝ => A + B * y + scatProfileP v w a y))
          (scatH v w r) r) := by
  let u : ℝ → ℝ := fun r => r * radialProfile w r
  have hu : MeasureTheory.LocallyIntegrableOn u (Set.Ioi a) volume := by
    simpa [u] using scat_u_locallyIntegrable_Ioi ha hrad hw
  have hh : MeasureTheory.IntegrableOn (scatH v w) (Set.Ioi a) volume :=
    scatH_integrable_Ioi hR ha hvrad hrad hw hv_supp
  have hint : ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ r : ℝ, χ r ≠ 0 → a < r) →
      (∫ x : ℝ in Set.Ioi a, u x * deriv (deriv χ) x) =
      (∫ x : ℝ in Set.Ioi a, scatH v w x * χ x) := by
    intro χ hχ hχcs hχsup
    simpa [u] using scatH_weak_eq_Ioi hR ha hvrad hrad hw hv_supp χ hχ hχcs hχsup
  rcases weak_snd_regularity_Ioi (u := u) (h := scatH v w) hu hh hint with ⟨A, B, h1, h2, h3⟩
  refine ⟨A, B, ?_, ?_, ?_⟩
  · filter_upwards [h1] with r hr hra
    simpa [u, scatProfileP] using hr hra
  · intro r hr
    simpa [scatProfileP] using h2 r hr
  · filter_upwards [h3] with r hr hra
    simpa [scatProfileP] using hr hra


end Submission.BoseGases
