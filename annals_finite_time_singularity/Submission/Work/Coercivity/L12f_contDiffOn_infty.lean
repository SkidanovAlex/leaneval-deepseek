/-
# `L₁₂^K(g)` is `C^∞` on `(0,∞)` for `g` smooth near the closed quadrant

The fundamental-model operator

  `L₁₂^K(g)(z) = ∫_z^∞ L12dens K g s ds`,  `L12dens K g s = ∫_θ K(θ) g(s,θ)/s dθ`

is the iterated tail integral of the angular density `L12dens K g`, which is
`C^∞` in `s` on `(0,∞)` because `g` is smooth (in this Mathlib: analytic) on a
neighbourhood of the closed quadrant and `Iθ = [0,π/2]` is compact
(`Work.Coercivity.contDiffOn_infty_integral_Itheta`).  Consequently `L₁₂^K(g)` is `C^∞`
on `(0,∞)`:

* if the density is integrable on one tail `(z₁,∞)` with `z₁ > 0`, then — by continuity of
  the density on `(0,∞)` — it is integrable on *every* tail `(z,∞)` with `z > 0`, and
  `L₁₂^K(g)` is there a genuine tail integral whose derivative is `-L12dens K g`
  (`Work.FM.hasDerivAt_L12`); by `contDiffOn_infty_iff_deriv_of_isOpen` it is `C^∞`;
* otherwise the density is non-integrable on every tail `(z,∞)`, `z > 0`, and Lean's Bochner
  integral is then the junk value `0` (`MeasureTheory.integral_undef`), so `L₁₂^K(g)`
  vanishes identically on `(0,∞)`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Coercivity.contDiffOn_infty_integral_Itheta
import Submission.Work.FM.Core2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- Note: the imports are those needed for this proof (`CTDefs` for `L12f`, `contDiffOn_infty_integral_Itheta`
-- for the smoothness of the parametric `θ`-integral, `FM.Core2` for `hasDerivAt_L12`).

namespace Work.Coercivity

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Integrability of one tail propagates to all tails -/

/-- A function continuous on `(0,∞)` which is integrable on one tail `(z₁,∞)` is integrable on
every tail `(z,∞)` with `z > 0`: the extra piece `(z, z₁]` is a compact interval contained in
`(0,∞)`, on which the (continuous) function is bounded. -/
theorem integrableOn_Ioi_of_integrableOn_Ioi {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioi 0))
    {z₁ : ℝ} (hint : IntegrableOn h (Set.Ioi z₁)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), IntegrableOn h (Set.Ioi z) := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  rcases le_total z z₁ with hle | hle
  · have hInt : IntegrableOn h (Set.Ioc z z₁) :=
      ((hcont.mono fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1, hzpos])).integrableOn_compact
        isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    rw [← Set.Ioc_union_Ioi_eq_Ioi hle]
    exact hInt.union hint
  · exact hint.mono_set (Set.Ioi_subset_Ioi hle)

/-! ## The angular density is `C^∞` -/

/-- The density `L12dens K g` is `C^∞` on `(0,∞)` for `g` smooth on a neighbourhood of the
closed quadrant: it is `z ↦ (∫_θ g(z,θ)K(θ) dθ)/z` with `K` continuous on the compact `Iθ`,
so the parametric `θ`-integral is `C^∞` by
`Work.Coercivity.contDiffOn_infty_integral_Itheta`, and division by `z ≠ 0` preserves this. -/
theorem L12dens_contDiffOn_infty (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Work.FM.L12dens Work.Spaces.K g z)
      (Set.Ioi 0) := by
  have hK : ContinuousOn Work.Spaces.K Work.Spaces.Iθ := by
    have hKc : Continuous Work.Spaces.K := by
      unfold Work.Spaces.K
      fun_prop
    exact hKc.continuousOn
  have hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ∫ θ in Work.Spaces.Iθ, g z θ * Work.Spaces.K θ) (Set.Ioi 0) :=
    contDiffOn_infty_integral_Itheta g Work.Spaces.K hg hK
  have heq : (fun z => Work.FM.L12dens Work.Spaces.K g z)
      = fun z => (∫ θ in Work.Spaces.Iθ, g z θ * Work.Spaces.K θ) / z := by
    funext z
    rw [Work.FM.L12dens, Work.Spaces.Iθ, MeasureTheory.integral_div]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun θ => mul_comm _ _)
  rw [heq]
  exact ContDiffOn.div hA contDiffOn_id fun z hz => ne_of_gt hz

/-! ## The main theorem -/

theorem L12f_contDiffOn_infty (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Coercivity.L12f g) (Set.Ioi 0) := by
  have hdens := L12dens_contDiffOn_infty g hg
  have hdens_cont : ContinuousOn (fun z => Work.FM.L12dens Work.Spaces.K g z) (Set.Ioi 0) :=
    hdens.continuousOn
  by_cases hcase : ∃ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun z => Work.FM.L12dens Work.Spaces.K g z) (Set.Ioi z)
  · -- the density is integrable on a tail: then on every tail, and `L₁₂` is its tail integral
    obtain ⟨z₁, hz₁, hint₁⟩ := hcase
    have hall := integrableOn_Ioi_of_integrableOn_Ioi hdens_cont hint₁
    have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun t => Work.Coercivity.L12f g t)
          (-(Work.FM.L12dens Work.Spaces.K g z)) z := by
      intro z hz
      have hzpos : (0 : ℝ) < z := hz
      refine Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := g) (a := z / 2) (ρ := z)
        (hall (z / 2) ?_) ?_ ?_
      · simp only [Set.mem_Ioi]; linarith
      · exact hdens_cont.continuousAt (isOpen_Ioi.mem_nhds hz)
      · linarith
    refine (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).2
      ⟨fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt, ?_⟩
    refine hdens.neg.congr fun z hz => ?_
    exact (hderiv z hz).deriv
  · -- otherwise the density is integrable on no tail and `L₁₂` is identically zero there
    push Not at hcase
    have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (0 : ℝ)) (Set.Ioi 0) :=
      contDiffOn_const
    refine h0.congr fun z hz => ?_
    show Work.Coercivity.L12f g z = 0
    simp only [Work.Coercivity.L12f, Work.FM.L12]
    exact MeasureTheory.integral_undef (hcase z hz)

end Work.Coercivity
