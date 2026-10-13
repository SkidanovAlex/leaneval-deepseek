/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/ProjSlotDerivRaw.lean` — the projected slot derivative
from the *raw* slot derivative

`EpsE4Thr.hasDerivWithinAt_mixed_JfamP` produces the fake-time derivative of a slot of the
projected family `slice (JfamP ρ ε g) τ = Pz (J_ε (slice g τ))` from the two *mollified* inputs
`hJeps` (`∂_τ (X (J_ε (slice g τ))) = X (J_ε (epsRHSP τ))`) and `hL12`.

Here the first of the two is *discharged* by the proved `EpsE4Thr.Jeps_family_deriv`, so the only
input left at the slot level is the derivative of the **raw** slot family
`τ ↦ mixed j i (slice g τ)`, i.e.

  `hraw : ∀ s ∈ (0,T), ∀ (z,θ) ∈ Q0, HasDerivAt (fun x => mixed j i (slice g x) z θ)
            (mixed j i (epsRHSP α ρ ε Φs E g s) z θ) s`.

`hraw` is produced by `EpsE4Thr.mixed_slice_deriv` (the Volterra/FTC brick); it is stated here in
its *global* (all `(z,θ)` in the quadrant) form, which is the form the mollifier differentiation
consumes.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.ProjSlotDeriv
import Submission.Work.FTS.StrongEps.EpsE4Thr.Jeps_family_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The projected slot derivative from the raw slot derivative.**  Same conclusion as
`hasDerivWithinAt_mixed_JfamP`, with the mollified input `hJeps` replaced by the raw one (`hraw`)
plus the domination data of `Jeps_family_deriv`. -/
theorem hasDerivWithinAt_mixed_JfamP_raw {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α T ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam} {τ : ℝ}
    (hε : 0 < ε)
    (hsm : ∀ s ∈ Set.Icc 0 T,
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0)
    (hsmR : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (epsRHSP α ρ ε Φs E g τ)) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {j i : ℕ} (hji : j + i ≤ 4)
    (hτ : τ ∈ Set.Ioo 0 T)
    (hraw : ∀ s ∈ Set.Ioo 0 T, ∀ y φ : ℝ, 0 < y → φ ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (fun x => Work.Spaces.mixed j i (slice g x) y φ)
        (Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s) y φ) s)
    (hint : ∀ s ∈ Set.Icc 0 T, Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p * Work.Spaces.mixed j i (slice g s)
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) volume)
    (hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
      |Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s)
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ C)
    (hL12 : HasDerivWithinAt
      (fun s => Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g s)) 0)
      (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
        (epsRHSP α ρ ε Φs E g τ)) 0) (Set.Icc 0 T) τ) :
    HasDerivWithinAt (fun s => Work.Spaces.mixed j i (slice (JfamP ρ ε g) s) z θ)
      (Work.Spaces.mixed j i (Pz (Work.FTS.StrongEps.Jeps ρ ε
        (epsRHSP α ρ ε Φs E g τ))) z θ) (Set.Icc 0 T) τ :=
  hasDerivWithinAt_mixed_JfamP (α := α) (Φs := Φs) (E := E) (g₀ := g₀) (g := g)
    hρ hε hsm hsmR hz hθ hji hτ
    (Jeps_family_deriv hρ.moll hε hraw hz hθ hint hbd hτ) hL12

end Work.FTS.StrongEps.EpsE4Thr
