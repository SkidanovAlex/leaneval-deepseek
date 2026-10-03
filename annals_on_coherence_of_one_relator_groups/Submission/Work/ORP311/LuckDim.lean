/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (JAZLA20 Proposition 3.11, the Følner/Lück analytic input)

# The Følner-normalised ("transversal") dimension of a window-supported subspace

`Work.ORVonNeumann.Rep.hdim` is computed on the single vector `δ₁` and is therefore a dimension
function only for subspaces invariant under the *whole* right regular action `ρ(G)`.  The pieces
of the Lück approximation argument (`U_k`, `W_k`, `L_k`, the window truncation `B^{(k)}`) are
invariant only under `ρ` of the normal subgroup `N ⊴ G`, and for those the right notion is the
**transversal sum** over a set `s` of representatives of the relevant `N`-cosets:

  `tDim n s M = ∑ g ∈ s, ∑ i : Fin n, ‖M.starProjection (hinclude n i (deltaG g))‖ ^ 2`.

For `M` invariant under `ρ(t)` (in the application: `M = ker B` for a Laurent operator `B`) this
is `s.card * hdim M` (`Work.ORP311.tDim_eq_card_mul_hdim`, via
`Work.ORP311.hdim_translate`), while for `M` contained in the span of the `δ_g`-directions it is
bounded by `n * s.card` (`Work.ORP311.tDim_le_card_of_le_span`).  The Følner/Lück inequality is
then the comparison of the two evaluations of `tDim` on the window `X_k`.
-/
import Mathlib
import Submission.Work.ORP311.hdim_translate

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORP311

open Work.ORVonNeumann

/-- **The transversal dimension**: the sum of the squared norms of the projections of the
`δ_g`-vectors (`g ∈ s`, all `n` coordinates) onto `M`. -/
noncomputable def tDim {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (s : Finset G)
    (M : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)) [M.HasOrthogonalProjection] : ℝ :=
  ∑ g ∈ s, ∑ i : Fin n,
    ‖M.starProjection (Work.ORVonNeumann.Rep.hinclude (G := G) n i
      (Work.ORVonNeumann.Rep.deltaG g))‖ ^ 2

@[simp]
theorem tDim_apply {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (s : Finset G)
    (M : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)) [M.HasOrthogonalProjection] :
    tDim (G := G) n s M = ∑ g ∈ s, ∑ i : Fin n,
      ‖M.starProjection (Work.ORVonNeumann.Rep.hinclude (G := G) n i
        (Work.ORVonNeumann.Rep.deltaG g))‖ ^ 2 := rfl



/-- **The `δ`-span of a set `Z ⊆ G`**: the closed span of the vectors `e_i ⊗ δ_g` with
`g ∈ Z`.  These are the "window-supported" subspaces of `HSum n` used by the Følner/Lück
argument (`Z = X_k`, `Z = T_k`, `Z = (X_k)^c`, `Z = X_k ∖ T_k`).  For such a `Z`,
`tDim` behaves like the trace of the finite amplification `M`<sub>`n`</sub>`(N(N)) ⊗ M_{|Z̄|}(ℂ)`
over the `N`-cosets of `Z`. -/
noncomputable def ell2Sub {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (Z : Set G) :
    Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n) :=
  (Submodule.span ℂ {x | ∃ g ∈ Z, ∃ i : Fin n,
      x = Work.ORVonNeumann.Rep.hinclude (G := G) n i
        (Work.ORVonNeumann.Rep.deltaG g)}).topologicalClosure

end Work.ORP311
