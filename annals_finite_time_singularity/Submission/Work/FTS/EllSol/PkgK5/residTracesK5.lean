/-
# `Work.FTS.EllSol.PkgK5.residTracesK5`

**The endpoint traces of the radial iterates of the residual `Ξ = EllResid α g Φg` from those
of the straightened unknown `Ψ̂ = ellShift α g Φg`.**

The exact algebraic identity of Theorem `RemovingL12` is

  `Ξ = Ψ̂ - Ḡ(α,g)·sin 2θ`,     `Ḡ = Work.Elliptic.Gbar α g`

(`EllResid_eq_ellShift_sub_Gbar_point`, `Submission/Work/FTS/EllSol/ropBasic.lean`, since
`Gsing = G_* + Ḡ` and `G_* = -(1/(4α))·L₁₂(g)`).  On the open quadrant the iterated radial
operator is additive (`Work.FTS.EllipticEst.SmoothOpen.DzIter_add`) and on a *separated* product
`(z,θ) ↦ c(z)·u(θ)` it only sees the `z`-variable (`Work.FTS.EllipticEst.DzIter_mul_of_radial`,
unconditional — no differentiability hypothesis), so for `z > 0` and `0 < θ < π/2`

  `D_z^j Ξ(z,θ) = D_z^j Ψ̂(z,θ) + (rDzIter j (-Ḡ(α,g)))(z)·sin 2θ`.

The second summand is a `θ`-constant times `sin 2θ`, hence tends to `0` at both angular
endpoints (`tendsto_const_mul_sin_two_ends` below); the first summand is the hypothesis.  This is
the trace-transfer step the `K5` interpolation family (`Submission/Work/FTS/EllSol/PkgK5/
WallDefs.lean`, `InterpFam`/`WallK5`) consumes: it is the mirror image of
`Work.FTS.ClassC.VopAux.vopTracesPointwise_classC`, where the traces of `Ψ̂` are *produced* from
the honest weak class instead of being assumed.

The only smoothness input is the `C^∞`-regularity on the open quadrant of the layer
`Ḡ(α,g)·sin 2θ`, from the all-order smoothness of the angular moment `F_*(g)` — a field of
`ClassC` — together with `HkMem α 7 g` (`gbar_contDiffOn_classC`, `smoothOpen_negGbarSin_classC`
below, whose ingredients are `Cert.Gbar_contDiffOn_Ioi` and
`FstarDivOpen.fstar_div_integrable_of_smoothOpen`).

The imports are kept deliberately light and disjoint from the modules re-declaring
`Work.FTS.EllipticEst.hasDerivAt_PsiInt` (`Fstar_Hk_le` resp. `HkMem_FstarSin_open`), so that
this module can be imported together with either family.  Everything rests on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial
import Submission.Work.FTS.EllSol.ropBasic
import Submission.Work.FTS.EllExist.SmoothOpenSep
import Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Cert.HkMem_pthIter2_EllResid

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false

/-! ## The two smoothness facts for the layer `Ḡ(α,g)·sin 2θ` -/

/-- **`Ḡ(α,g)` is `C^∞` on `(0,∞)`** for a datum of the class `C` (`SmoothOpen g`, all-order
smoothness of the angular moment `F_*(g)` and `HkMem α 7 g`). -/
theorem gbar_contDiffOn_classC {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hreg : Work.FTS.EllipticEst.SmoothOpen g)
    (hfsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0))
    (hmem : Work.Spaces.HkMem α 7 g) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α g) (Set.Ioi 0) :=
  Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α g hα hfsm
    (Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hreg hmem)

/-- **The layer `-Ḡ(α,g)·sin 2θ` is `C^∞` on the open quadrant** for a datum of the class `C`. -/
theorem smoothOpen_negGbarSin_classC {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hreg : Work.FTS.EllipticEst.SmoothOpen g)
    (hfsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0))
    (hmem : Work.Spaces.HkMem α 7 g) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ)) :=
  Work.FTS.EllExist.sep_mul_open (g := fun z => -(Work.Elliptic.Gbar α g z))
    (χ := fun θ => Real.sin (2 * θ))
    (fun m => (gbar_contDiffOn_classC hα hreg hfsm hmem m).neg) (by fun_prop)

/-! ## A constant times `sin 2θ` at the two endpoints -/

/-- A `θ`-constant times `sin 2θ` tends to `0` at the two endpoints of `(0,π/2)`. -/
theorem tendsto_const_mul_sin_two_ends (c : ℝ) :
    Filter.Tendsto (fun θ : ℝ => c * Real.sin (2 * θ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ : ℝ => c * Real.sin (2 * θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
  have hleft : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := hcont.continuousAt (x := 0)
    have h' : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhds (0 : ℝ))
        (nhds (Real.sin (2 * 0))) := h
    rw [show Real.sin (2 * 0) = 0 by norm_num] at h'
    exact h'.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hright : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    have h := hcont.continuousAt (x := Real.pi / 2)
    have h' : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhds (Real.pi / 2))
        (nhds (Real.sin (2 * (Real.pi / 2)))) := h
    rw [hsin] at h'
    exact h'.mono_left (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)))
  exact ⟨by simpa using hleft.const_mul c, by simpa using hright.const_mul c⟩

/-! ## The target -/

theorem residTracesK5 (k : ℕ) :
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      ∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro α g Φg hα hα4 hC hsmo htraces j hj z hz
  -- the layer `-(Ḡ(α,g))·sin 2θ` is `C^∞` on the open quadrant
  have hCsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ)) :=
    smoothOpen_negGbarSin_classC (α := α) (g := g) hα hC.reg hC.fsm hC.mem
  -- the functional identity `Ξ = Ψ̂ + (-Ḡ(α,g))·sin 2θ`
  have hfun : Work.Elliptic.EllResid α g Φg
      = fun z θ => Work.FTS.EllSol.ellShift α g Φg z θ
          + (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ) := by
    funext z θ
    rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point]
    simp only [Work.FTS.EllSol.ellShift_apply]
    ring
  -- the pointwise decomposition of the radial iterates on the open quadrant
  have hdecomp : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ) := by
    intro z θ hz h1 h2
    rw [hfun]
    rw [Work.FTS.EllipticEst.SmoothOpen.DzIter_add hsmo hCsm j z θ hz h1 h2]
    rw [Work.FTS.EllipticEst.DzIter_mul_of_radial j (fun z => -(Work.Elliptic.Gbar α g z))
      (fun θ => Real.sin (2 * θ)) z θ]
  -- the two one-sided limits of the two summands
  obtain ⟨htl, htr⟩ := htraces j hj z hz
  obtain ⟨hcl, hcr⟩ := tendsto_const_mul_sin_two_ends
    (Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z)
  -- the two eventual equalities, on the two one-sided filters
  have hev0 : (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ
        + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
            * Real.sin (2 * θ)) := by
    change ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity)] with θ hθ hθmem
    exact hdecomp z θ hz hθmem hθ
  have hev1 : (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ)
      =ᶠ[nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))]
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ
        + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
            * Real.sin (2 * θ)) := by
    change ∀ᶠ θ : ℝ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity)] with θ hθ hθmem
    exact hdecomp z θ hz hθ hθmem
  exact ⟨Filter.Tendsto.congr' hev0.symm (by simpa using htl.add hcl),
    Filter.Tendsto.congr' hev1.symm (by simpa using htr.add hcr)⟩

end Work.FTS.EllSol.PkgK5
