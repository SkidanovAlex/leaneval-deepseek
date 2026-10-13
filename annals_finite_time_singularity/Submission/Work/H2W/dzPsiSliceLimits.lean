/-
Copyright: work module for the Elgindi finite-time singularity project.

# The endpoint limits of the radial-derivative slice `∂_zΨ`

For a datum `(F, Ψ)` of the weak hypothesis class `Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ`
we prove that, for every `z > 0`, the angular slice `θ ↦ ∂_zΨ(z,θ)` tends to `0` both at the
left endpoint `θ → 0⁺` and at the right endpoint `θ → (π/2)⁻`.

This is the `k = 2` instance of `Work.FTS.EllipticEst.remov.SourceBound.dzPsiLimits`, which
handles the whole range `2 ≤ k`; the extra level of the class is only used to have the moment
chain `F_*(D_z^j Ψ) = 0` available at `j ≤ 3`, all of which is already contained in the
`k = 2` hypothesis (see `Fstar_DzIter_le_Psi`).

Sketch of that development (route of `SourceBound/dzPsiLimits.lean`, all leaves sorry-free):

* `dzSlice_contDiffOn`, `dzSlice_secondDeriv_integrableOn`, `dzSlice_sq_integrableOn` and
  `dzSlice_Lzero1_sq_integrableOn` give the four analytic hypotheses of
  `sliceTendstoZeroOfMoment` for the slice `V = θ ↦ ∂_zΨ(z,θ)`: it is `C²` on `(0,π/2)`,
  `(∂_θ²V)²·sin(2θ)^{-η}`, `V²` and `(Lzero1 V)²·sin(2θ)^{-η}` are integrable on `Iθ`
  (`Lzero1 V` is expressed through the shifted decomposition of the weak equation on the `∂_z`
  slice, so that each of its four summands is one of the `η`-weighted slots of the class);
* `dzSlice_Lzero1_moment` shows that the angular moment `∫_θ Lzero1 V · sinθcos²θ` vanishes,
  because `Lzero1 V` is a linear combination of `∂_zΨ`, `∂_zF`, `∂_z(z²∂_z²Ψ)` and `z∂_z²Ψ`,
  whose moments are the vanishing quantities `F_*(D_zΨ)`, `F_*(D_zF)`, `F_*(D_z³Ψ) = F_*(D_z²Ψ)`
  and `F_*(D_z²Ψ)`;
* `sliceTendstoZeroOfMoment` then converts the vanishing moment into the limit `0` at `0⁺`;
* at the right endpoint the limit exists (`tendsTo_atEnds_of_integrableOn_sq_deriv`) and equals
  `0` (`slice_limit_at_right_eq_zero`) because `Lzero1 V` is square-integrable with the `η`
  weight.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.remov.SourceBound.dzPsiLimits

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W

theorem dzPsiSliceLimits (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z, 0 < z →
      Filter.Tendsto (fun θ => Work.Spaces.pz Ψ z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
      ∧ Filter.Tendsto (fun θ => Work.Spaces.pz Ψ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
  Work.FTS.EllipticEst.remov.SourceBound.dzPsiLimits (le_refl 2) h

end Work.H2W
