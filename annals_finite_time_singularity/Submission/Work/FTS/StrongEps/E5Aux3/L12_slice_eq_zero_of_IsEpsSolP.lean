import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FM.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Aux3/L12_slice_eq_zero_of_IsEpsSolP.lean`

**The zero mode of `L₁₂` is conserved along an `IsEpsSolP`-solution.**

The `P₀`-scheme's right-hand side is `Pz`-projected, so `L₁₂(∂_τ g)(0) = 0` at every fake time
(`PZeroAux.Pz_l12`); together with the derivative-under-the-integral lemma
`E5Aux3.hasDerivWithinAt_L12_slice_of_majorant` this says that the function

    φ(τ) = L₁₂(slice g τ)(0)

is continuous on `[0,T]`, has vanishing one-sided derivative on `(0,T)`, and starts at
`L₁₂ g₀ (0) = 0`.  Hence `φ ≡ 0`: the unmollified zero mode vanishes at every fake time.  That is
the input `hl12` of the E5 assembly needs (see `L12_Jeps_slice_tendsto_of_zero`).

The only mathematics is the elementary constancy lemma
`eq_zero_of_hasDerivWithinAt_zero_Icc` (a continuous function on `[0,T]` with vanishing
within-derivative on the interior and vanishing at `0` is zero), proved from
`monotoneOn_of_deriv_nonneg` / `antitoneOn_of_deriv_nonpos`: `φ` is simultaneously monotone and
antitone on the convex set `[0,T]`, hence constant there.
-/

open scoped Topology

namespace Work.FTS.StrongEps.E5Aux3

/-- **A continuous function on `[0,T]` with vanishing one-sided derivative on the interior and
vanishing at `0` is zero.**  The derivative is only required *within* `[0,T]` and only on the
interior `(0,T)`; no differentiability at the endpoints is assumed.

Proof: the interior of the convex set `[0,T]` is `(0,T)`, on which `deriv F = 0`
(`HasDerivWithinAt.hasDerivAt`, since `[0,T]` is a neighbourhood of an interior point).  Hence `F`
is both monotone and antitone on `[0,T]` (`monotoneOn_of_deriv_nonneg` /
`antitoneOn_of_deriv_nonpos`), so constant there. -/
theorem eq_zero_of_hasDerivWithinAt_zero_Icc {T : ℝ} {F : ℝ → ℝ}
    (hcont : ContinuousOn F (Set.Icc 0 T))
    (hder : ∀ τ ∈ Set.Ioo 0 T, HasDerivWithinAt F 0 (Set.Icc 0 T) τ)
    (h0 : F 0 = 0) : ∀ τ ∈ Set.Icc 0 T, F τ = 0 := by
  -- `[0,T]` is a neighbourhood of each of its interior points
  have hnhds : ∀ x ∈ Set.Ioo (0 : ℝ) T, Set.Icc (0 : ℝ) T ∈ 𝓝 x := fun x hx =>
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx)
      (fun y hy => ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
  -- the honest derivative vanishes on the interior
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) T, deriv F x = 0 := fun x hx =>
    ((hder x hx).hasDerivAt (hnhds x hx)).deriv
  have hdiff : DifferentiableOn ℝ F (interior (Set.Icc (0 : ℝ) T)) := fun x hx => by
    rw [interior_Icc] at hx ⊢
    exact ((hder x hx).hasDerivAt (hnhds x hx)).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ x ∈ interior (Set.Icc (0 : ℝ) T), 0 ≤ deriv F x := fun x hx => by
    rw [interior_Icc] at hx
    rw [hderiv x hx]
  have hnonpos : ∀ x ∈ interior (Set.Icc (0 : ℝ) T), deriv F x ≤ 0 := fun x hx => by
    rw [interior_Icc] at hx
    rw [hderiv x hx]
  have hmono : MonotoneOn F (Set.Icc (0 : ℝ) T) :=
    monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) T) hcont hdiff hnonneg
  have hanti : AntitoneOn F (Set.Icc (0 : ℝ) T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) T) hcont hdiff hnonpos
  intro τ hτ
  have hT : (0 : ℝ) ≤ T := le_trans hτ.1 hτ.2
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  have hconst : F τ = F 0 := by
    rcases le_total τ 0 with h | h
    · exact le_antisymm (hmono hτ h0mem h) (hanti hτ h0mem h)
    · exact (le_antisymm (hmono h0mem hτ h) (hanti h0mem hτ h)).symm
  rw [hconst, h0]

theorem L12_slice_eq_zero_of_IsEpsSolP {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hL12g0 : Work.Construction.L12 g₀ 0 = 0)
    (hder : ∀ τ ∈ Set.Ioo 0 T,
      HasDerivWithinAt (fun σ : ℝ => Work.Construction.L12 (Work.FTS.Galerkin.slice g σ) 0)
        0 (Set.Icc 0 T) τ)
    (hcont : ContinuousOn (fun σ : ℝ => Work.Construction.L12 (Work.FTS.Galerkin.slice g σ) 0)
      (Set.Icc 0 T)) :
    ∀ τ ∈ Set.Icc 0 T, Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0 := by
  refine eq_zero_of_hasDerivWithinAt_zero_Icc hcont hder ?_
  have hslice0 : Work.FTS.Galerkin.slice g 0 = g₀ :=
    funext fun z => funext fun θ => hsol.1 z θ
  rw [hslice0]
  exact hL12g0

end Work.FTS.StrongEps.E5Aux3
