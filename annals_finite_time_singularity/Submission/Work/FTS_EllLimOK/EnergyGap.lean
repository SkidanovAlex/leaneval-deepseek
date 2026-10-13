/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.EnergyGap` — the Euler-gap inequality for the angular energy of the difference

Let `δ = diff Ψ Ψ'` be the difference of two box-regular profiles (`BoxReg`), solving the
homogeneous elliptic problem `bslOp α δ = 0` on the open quadrant, vanishing at the two angular
endpoints, with vanishing angular moment `Fstar δ ≡ 0`, and with the two profiles (and their
`1/cos θ`-multiples) in `ℋ⁰`.  Then the angular `L²`-mass

  `Φ(z) = PhiD Ψ Ψ' z = ∫_θ δ(z,θ)² dθ`

is a nonnegative function of `z`, twice differentiable on `(0,∞)`, integrable on `(0,∞)`, with
`Φ(z) · z^{-4}` integrable on `(0,1)`, and it satisfies the Euler gap inequality

  `α² z² Φ''(z) + α (5+α) z Φ'(z) ≥ 0`   for `z > 0`.

This is the input of `phi_eq_zero_of_euler_gap_weighted`, i.e. the last analytic step of the
uniqueness argument (`ClosedUniq3_small`): the two integrability clauses exclude the two branches
of the Euler ODE, so `Φ ≡ 0`.

## The mathematical content

`Phi_deriv` (differentiation under the angular integral, from the closed-box `C²`-regularity of
`δ`) gives `Φ'(z) = 2 ∫_θ δ ∂_zδ` and `Φ''(z) = 2 ∫_θ ((∂_zδ)² + δ ∂_zzδ)`.  Multiplying the
equation `bslOp α δ = 0` by `δ` and integrating in `θ` gives (`Lzero_integral_eq_boxReg`) the
identity `∫_θ (Lzero δ) δ = α²z² ∫_θ δ ∂_zzδ + α(5+α)z ∫_θ δ ∂_zδ`, while the `θ`-integration by
parts `Lzero_self_form` evaluates the left hand side as
`∫_θ (∂_θδ)² + (1/2) ∫_θ (δ/cos θ)² - 6 ∫_θ δ²`.  The constrained slice Poincaré gap
`coercive_slice_fts` — whose constraint is exactly the hypothesis `Fstar δ ≡ 0` — makes that
quantity nonnegative, so

  `(α²z²/2) Φ'' + (α(5+α)z/2) Φ' = ∫_θ (Lzero δ) δ + α²z² ∫_θ (∂_zδ)² ≥ 0`.

The two integrability clauses are `integrableOn_PhiD`: on `Iθ` the level-`0` weight
`w(z)² sin(2θ)^{-η}` dominates both `1` and `z^{-4}`, and the `HkMem α 0` hypotheses of `Ψ` and
`Ψ'` make its `z`-integral finite.

## Two notational repairs to the transmitted statement

The statement as transmitted does not elaborate, and two purely notational slips had to be
repaired for it to say what it was meant to say.  The statement text below is otherwise
unchanged:

* the fourth conjunct is typed `Work.FTS.EllLimOK.PhiD` in the transmitted text (dot, not
  underscore); no such constant exists (the same trap is recorded in `Dev/T1.lean`).  For
  compatibility with that text, this module declares the abbreviation
  `Work.FTS.EllLimOK.PhiD := Work.FTS_EllLimOK.PhiD` (definitionally equal, so a consumer may
  write either name);
* the file has no `open scoped Real`, so a bare `π` is *not* the notation for `Real.pi`.  Under
  the library's default `autoImplicit` it is silently auto-bound as an extra free variable, which
  would turn the statement into a claim about an *arbitrary* angular endpoint `π` — false (for
  `π = 0` the hypotheses `hsol` and `h1` degenerate and `Φ(z) = e^{-2z}` violates the Euler
  inequality for small `z`).  Adding `open scoped Real` restores `π = Real.pi`, which is what the
  statement means.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.UniqDefs
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.Phi_deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Lzero_self_form
import Submission.Work.FTS.EllipticEst.coercive_slice_fts
import Submission.Work.FTS_EllLimOK.EGap.aemeasurable_uncurry_of_boxReg
import Submission.Work.FTS_EllLimOK.EGap.Lzero_integral_eq_boxReg
import Submission.Work.FTS_EllLimOK.EGap.integrableOn_PhiD

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/- The nonexistent name `Work.FTS.EllLimOK.PhiD` occurring in the transmitted text of
`EnergyGap`, made definitionally equal to the real thing `Work.FTS_EllLimOK.PhiD`. -/
namespace Work.FTS
namespace EllLimOK
/-- Alias (definitionally equal) of `Work.FTS_EllLimOK.PhiD`, for the transmitted spelling. -/
abbrev PhiD := _root_.Work.FTS_EllLimOK.PhiD
end EllLimOK
end Work.FTS

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- On a fixed radial line `z > 0`, a box-regular function and its first two `z`-derivatives
have continuous slices on the angular interval `Iθ`. -/
theorem boxReg_slice_continuous {F : ℝ → ℝ → ℝ} (hbox : BoxReg F) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => F z θ) Work.Spaces.Iθ ∧
      ContinuousOn (fun θ => Work.Spaces.pz F z θ) Work.Spaces.Iθ ∧
      ContinuousOn (fun θ => Work.Spaces.pzIter 2 F z θ) Work.Spaces.Iθ := by
  have ha : 0 < z / 2 := by linarith
  have hab : z / 2 < 2 * z := by linarith
  have hab' : z / 2 ≤ 2 * z := le_of_lt hab
  have hzmem : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  obtain ⟨-, -, hpz, hpz2⟩ :=
    boxReg_facts (F := F) (a := z / 2) (b := 2 * z) hab (hbox (z / 2) (2 * z) ha hab')
  have hcont : ContinuousOn (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) Work.Spaces.Iθ := by fun_prop
  have hmap : Set.MapsTo (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) Work.Spaces.Iθ
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) := fun θ hθ => ⟨hzmem, hθ⟩
  have hF : ContinuousOn (fun θ => F z θ) Work.Spaces.Iθ := by
    have := ((hbox (z / 2) (2 * z) ha hab').continuousOn :
      ContinuousOn (Function.uncurry F) (cbox (z / 2) (2 * z)))
    exact this.comp hcont (fun θ hθ => ⟨⟨le_of_lt (hmap hθ).1.1, le_of_lt (hmap hθ).1.2⟩,
      (hmap hθ).2⟩)
  refine ⟨hF, ?_, ?_⟩
  · exact hpz.comp hcont hmap
  · exact hpz2.comp hcont hmap

theorem EnergyGap {α : ℝ} (hα : 0 < α) {Ψ Ψ' : ℝ → ℝ → ℝ}
    (hboxΨ : Work.FTS_EllLimOK.BoxReg Ψ) (hboxΨ' : Work.FTS_EllLimOK.BoxReg Ψ')
    (hsol : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Elliptic.bslOp α (Work.FTS_EllLimOK.diff Ψ Ψ') z θ = 0)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), Work.FTS_EllLimOK.diff Ψ Ψ' z 0 = 0)
    (h1 : ∀ z ∈ Set.Ioi (0 : ℝ), Work.FTS_EllLimOK.diff Ψ Ψ' z (π / 2) = 0)
    (horth : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Elliptic.Fstar (Work.FTS_EllLimOK.diff Ψ Ψ') z = 0)
    (hHkΨ : Work.Spaces.HkMem α 0 Ψ)
    (hHkcΨ : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ))
    (hHkΨ' : Work.Spaces.HkMem α 0 Ψ')
    (hHkcΨ' : Work.Spaces.HkMem α 0 (fun z θ => Ψ' z θ / Real.cos θ)) :
    (∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (Work.FTS_EllLimOK.PhiD Ψ Ψ') (deriv (Work.FTS_EllLimOK.PhiD Ψ Ψ') z) z) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (deriv (Work.FTS_EllLimOK.PhiD Ψ Ψ'))
          (deriv (deriv (Work.FTS_EllLimOK.PhiD Ψ Ψ')) z) z) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ Work.FTS_EllLimOK.PhiD Ψ Ψ' z) ∧
      MeasureTheory.IntegrableOn (Work.FTS.EllLimOK.PhiD Ψ Ψ') (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn (fun z => Work.FTS_EllLimOK.PhiD Ψ Ψ' z * z ^ (-4 : ℝ))
        (Set.Ioo (0 : ℝ) 1) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ α ^ 2 * z ^ 2
          * deriv (deriv (Work.FTS_EllLimOK.PhiD Ψ Ψ')) z
        + α * (5 + α) * z * deriv (Work.FTS_EllLimOK.PhiD Ψ Ψ') z) := by
  have hboxδ : BoxReg (diff Ψ Ψ') := hboxΨ.diff hboxΨ'
  obtain ⟨hPhi1, hPhi2⟩ := Phi_deriv (δ := diff Ψ Ψ') hboxδ
  obtain ⟨hintPhi, hintPhiW⟩ :=
    Work.FTS_EllLimOK.EGap.integrableOn_PhiD (α := α) hHkΨ hHkΨ'
      (Work.FTS_EllLimOK.EGap.aemeasurable_uncurry_of_boxReg hboxδ)
  refine ⟨?_, ?_, ?_, hintPhi, hintPhiW, ?_⟩
  · -- first derivative
    intro z hz
    have h2 : HasDerivAt (PhiD Ψ Ψ')
        (2 * ∫ θ in Work.Spaces.Iθ,
          diff Ψ Ψ' z θ * Work.Spaces.pz (diff Ψ Ψ') z θ) z := hPhi1 z hz
    rw [h2.deriv]
    exact h2
  · -- second derivative
    intro z hz
    have hev : deriv (PhiD Ψ Ψ') =ᶠ[𝓝 z]
        (fun s => 2 * ∫ θ in Work.Spaces.Iθ,
          diff Ψ Ψ' s θ * Work.Spaces.pz (diff Ψ Ψ') s θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
      exact (hPhi1 s hs).deriv
    have h := (hPhi2 z hz).congr_of_eventuallyEq hev
    rw [h.deriv]
    exact h
  · -- nonnegativity
    intro z hz
    exact PhiD_nonneg Ψ Ψ' z
  · -- the Euler gap inequality
    intro z hz
    obtain ⟨hs0, hs1, hs2⟩ := boxReg_slice_continuous hboxδ hz
    have hint1 : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pz (diff Ψ Ψ') z θ) ^ 2) Work.Spaces.Iθ :=
      (hs1.pow 2).integrableOn_compact isCompact_Icc
    have hint2 : MeasureTheory.IntegrableOn
        (fun θ => diff Ψ Ψ' z θ * Work.Spaces.pzIter 2 (diff Ψ Ψ') z θ) Work.Spaces.Iθ :=
      (hs0.mul hs2).integrableOn_compact isCompact_Icc
    have hd1 : deriv (PhiD Ψ Ψ') z
        = 2 * (∫ θ in Work.Spaces.Iθ,
            diff Ψ Ψ' z θ * Work.Spaces.pz (diff Ψ Ψ') z θ) := (hPhi1 z hz).deriv
    have hev : deriv (PhiD Ψ Ψ') =ᶠ[𝓝 z]
        (fun s => 2 * ∫ θ in Work.Spaces.Iθ,
          diff Ψ Ψ' s θ * Work.Spaces.pz (diff Ψ Ψ') s θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
      exact (hPhi1 s hs).deriv
    have hd2 : deriv (deriv (PhiD Ψ Ψ')) z
        = 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz (diff Ψ Ψ') z θ) ^ 2)
          + 2 * (∫ θ in Work.Spaces.Iθ,
              diff Ψ Ψ' z θ * Work.Spaces.pzIter 2 (diff Ψ Ψ') z θ) := by
      rw [Filter.EventuallyEq.deriv_eq hev, (hPhi2 z hz).deriv]
      rw [MeasureTheory.integral_add hint1 hint2]
      ring
    -- the equation integrated against the slice, and the angular self form
    have hLz := Work.FTS_EllLimOK.EGap.Lzero_integral_eq_boxReg α (diff Ψ Ψ') z hz hboxδ (hsol z hz)
    have hcomm1 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pzIter 2 (diff Ψ Ψ') z θ * diff Ψ Ψ' z θ)
        = ∫ θ in Work.Spaces.Iθ,
            diff Ψ Ψ' z θ * Work.Spaces.pzIter 2 (diff Ψ Ψ') z θ :=
      setIntegral_congr_fun measurableSet_Icc fun θ _ => mul_comm _ _
    have hcomm2 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz (diff Ψ Ψ') z θ * diff Ψ Ψ' z θ)
        = ∫ θ in Work.Spaces.Iθ,
            diff Ψ Ψ' z θ * Work.Spaces.pz (diff Ψ Ψ') z θ :=
      setIntegral_congr_fun measurableSet_Icc fun θ _ => mul_comm _ _
    have hself := Work.FTS.EllipticEst.Lzero_self_form (diff Ψ Ψ') z
      (BoxReg.slice hboxδ hz) (h0 z hz) (h1 z hz)
    -- the constrained slice Poincaré gap
    obtain ⟨c, hcpos, hclt, hcf⟩ := Work.FTS.EllipticEst.coercive_slice_fts
    have hle : (∫ θ in Work.Spaces.Iθ, (diff Ψ Ψ' z θ) ^ 2)
        ≤ c * (∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ' => diff Ψ Ψ' z θ') θ) ^ 2) :=
      hcf (fun θ => diff Ψ Ψ' z θ) (BoxReg.slice hboxδ hz) (h0 z hz) (h1 z hz) (horth z hz)
    have hnn1 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (deriv (fun θ' => diff Ψ Ψ' z θ') θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    have hnn2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (diff Ψ Ψ' z θ / Real.cos θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    have hQnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Lzero (diff Ψ Ψ') z θ * diff Ψ Ψ' z θ := by
      rw [hself]
      nlinarith [hle, hnn1, hnn2, hcpos, hclt]
    have hA1n : 0 ≤ α ^ 2 * z ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz (diff Ψ Ψ') z θ) ^ 2) :=
      mul_nonneg (mul_nonneg (sq_nonneg α) (sq_nonneg z))
        (integral_nonneg fun θ => sq_nonneg _)
    have hident : (α ^ 2 * z ^ 2 / 2) * deriv (deriv (PhiD Ψ Ψ')) z
        + (α * (5 + α) * z / 2) * deriv (PhiD Ψ Ψ') z
        = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero (diff Ψ Ψ') z θ * diff Ψ Ψ' z θ)
          + α ^ 2 * z ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz (diff Ψ Ψ') z θ) ^ 2) := by
      rw [hd1, hd2, hLz, hcomm1, hcomm2]
      ring
    have hsum : 0 ≤ (∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Lzero (diff Ψ Ψ') z θ * diff Ψ Ψ' z θ)
        + α ^ 2 * z ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz (diff Ψ Ψ') z θ) ^ 2) :=
      add_nonneg hQnn hA1n
    nlinarith [hident, hsum]

end Work.FTS_EllLimOK
