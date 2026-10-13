import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `SliceMassExternal` — the external input the Ψ-side honesty chain needs

The Ψ-side honesty of the elliptic chapter (`shiftWeakClass` clause 5, `psiSliceHonest`,
`pzIterSliceGrowth3Loc`, `pzIterSliceIntegrableInput`, `SliceSourceMassBound`) is one open
problem under four namings: the tower `Lzero U_j = D_z^j F + α²U_{j+2} + 5αU_{j+1}`
(`U_j = ∂_z^jΨ`) is upward in `j` and never closes from within the classes `WeakPos2` / `Hon`.

The correctly-strengthened hypothesis is the paper's `R²Ψ → 0` at `R = 0`, carried here in the
*ψ-weighted slice-mass* form (`ψ = sinθcos²θ`) that the reduction consumes: the masses of the
radial shifts of `Ψ` up to `∂_z⁵Ψ`, and of the source shifts up to `∂_z³F`, are locally
uniformly bounded in `z`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-- **The external input of the Ψ-side honesty chain**: for a.e. `z₀` there is a neighbourhood
on which the `ψ`-weighted `L¹` slice masses of the radial shifts `∂_z^mΨ` (`m ≤ 5`) and the
`ψ`-weighted slice integrability of the source shifts `D_z^m F` (`m ≤ 3`) hold with a single
constant `C`.  This is the known-absent hypothesis (the paper's `R²Ψ → 0` at `R = 0`), not a
consequence of `WeakPos2` or `Hon`. -/
def SliceMassExternal (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
    ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
        (∀ m : ℕ, m ≤ 5 → MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m Ψ z θ|)
            Work.Spaces.Iθ ∧
          (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m Ψ z θ|)
            ≤ C) ∧
        (∀ m : ℕ, m ≤ 3 → MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter m F z θ|)
            Work.Spaces.Iθ ∧
          (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter m F z θ|)
            ≤ C)

end Work.FTS.EllipticEst.H2W
