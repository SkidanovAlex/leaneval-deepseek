import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The angular moment `F_*(f)` is an antiderivative of `F_*(∂_z f)`.**

With `F_*(g)(r) = ∫_θ g(r,θ) sinθcos²θ dθ` (`Work.Elliptic.Fstar`) and
`∂_z f = Work.Spaces.pz f`, integrating the identity `∂_r (f(r,θ) sinθcos²θ) =
∂_z f(r,θ) sinθcos²θ` over the box `[s,z] × [0,π/2]` — first in `θ`, then in `r` —
gives

  `F_*(f)(z) - F_*(f)(s) = ∫_s^z F_*(∂_z f)(r) dr`.

The proof avoids differentiating under the `θ`-integral: for each fixed `θ` the map
`r ↦ f(r,θ)` is `C^∞` on `(0,∞)` (which contains `[s,z]` when `0 < s`), so the
fundamental theorem of calculus applies pointwise on the slice
(`SmoothOpen.curry_z`, `SmoothOpen.hasDerivAt_slice`), and the resulting iterated
integral over `[s,z] × [0,π/2]` is interchanged with Tonelli–Fubini using the
integrability of the box integrand (the hypothesis `hbox`). -/
theorem Fstar_sub_eq_integral_pz {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z)
    (hsl_s : MeasureTheory.IntegrableOn (fun θ => f s θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hsl_z : MeasureTheory.IntegrableOn (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hbox : MeasureTheory.Integrable
      (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    Work.Elliptic.Fstar f z - Work.Elliptic.Fstar f s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz f) r := by
  -- the fundamental theorem of calculus on the `z`-slice at a fixed interior angle
  have hftc_θ : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ∫ r in s..z, Work.Spaces.pz f r θ = f z θ - f s θ := by
    intro θ hθ
    have hmem : Set.Icc s z ⊆ Set.Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le hs hr.1
    have hcont : ContinuousOn (fun r => f r θ) (Set.Icc s z) :=
      (hf.curry_z hθ).continuousOn.mono hmem
    have hderiv : ∀ r ∈ Set.Ioo s z, HasDerivAt (fun r' => f r' θ) (Work.Spaces.pz f r θ) r :=
      fun r hr => hf.hasDerivAt_slice hθ (lt_of_lt_of_le hs (le_of_lt hr.1))
    have hint : IntervalIntegrable (fun r => Work.Spaces.pz f r θ) MeasureTheory.volume s z :=
      (((hf.pz).curry_z hθ).continuousOn.mono hmem).intervalIntegrable_of_Icc hsz
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsz hcont hderiv hint
  -- the pointwise identity on the angular interval (the weight vanishes at the endpoints)
  have hpoint : ∀ θ ∈ Work.Spaces.Iθ,
      f z θ * Work.Elliptic.sinCos2 θ - f s θ * Work.Elliptic.sinCos2 θ
        = ∫ r in s..z, Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    rcases eq_or_ne θ 0 with rfl | h0
    · simp [Work.Elliptic.sinCos2]
    · rcases eq_or_ne θ (π / 2) with rfl | h1
      · simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two]
      · have hθ' : θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
          ⟨lt_of_le_of_ne hθ.1 (Ne.symm h0), lt_of_le_of_ne hθ.2 h1⟩
        rw [intervalIntegral.integral_mul_const, hftc_θ θ hθ']
        ring
  -- the left hand side is the `θ`-first iterated integral
  have hL : Work.Elliptic.Fstar f z - Work.Elliptic.Fstar f s
      = ∫ θ in Work.Spaces.Iθ, ∫ r in s..z,
          Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ := by
    simp only [Work.Elliptic.Fstar]
    rw [← MeasureTheory.integral_sub hsl_z hsl_s]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
  -- the right hand side is the `r`-first iterated integral (Tonelli–Fubini, `hbox`)
  have key : (∫ θ in Work.Spaces.Iθ, ∫ r in s..z,
        Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ)
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz f) r := by
    have h1 := MeasureTheory.integral_prod_symm
      (f := Function.uncurry (fun r θ : ℝ => Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ))
      (μ := MeasureTheory.volume.restrict (Set.Ioc s z))
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hbox
    have h2 := MeasureTheory.integral_prod
      (f := Function.uncurry (fun r θ : ℝ => Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ))
      (μ := MeasureTheory.volume.restrict (Set.Ioc s z))
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hbox
    simp only [Function.uncurry_apply_pair] at h1 h2
    simp_rw [intervalIntegral.integral_of_le hsz]
    rw [← h1, h2]
    simp only [Work.Elliptic.Fstar]
  exact hL.trans key

end Work.EllipticEst.H2W
