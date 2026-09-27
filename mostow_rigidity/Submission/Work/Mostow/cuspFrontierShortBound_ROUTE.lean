import Mathlib

/-!
# Route note for `Work.Mostow.cuspFrontierShortBound` (written by the requester)

TARGET.  `Γ` a lattice in `PO(n,1)`, `n ≥ 2`, `ξ ∈ parFixed Γ`, `hvan`, `θ > 0` and the elliptic
gap `hgap` at `ξ` (nontrivial elliptics of `Γ_ξ` move some unit vector of `ξ^⊥` by at least `θ`).
Then there are `ε₀ > 0` and `N` such that every point `u` of the *frontier* of the Margulis
region `cuspThinRegion Γ ξ ε` (identified, via `cuspThinRegion_eq_parDisp`, with the equation
`lev ξ u * parDisp Γ ξ (yc ξ u) = cEps ε`) has at most `N` elements `γ ∈ Γ` with
`hdist u (γ • u) < ε/2`.

## Proof route

Fix `ε ≤ ε₀` with `ε₀` small and `u` with `lev ξ u * parDisp Γ ξ (yc ξ u) = cEps ε`.
Write `L := lev ξ u` and `Y := yc ξ u`, so `L * parDisp Γ ξ Y = cEps ε`.

**(1) A short element at `u` fixes `ξ`.**  By `Work.Mostow.parDisp_pos_of_discrete`,
`parDisp Γ ξ Y > 0` and it is an `sInf` over the parabolics of `Γ_ξ`, so there is a parabolic
`q ∈ Γ` fixing `ξ` with `‖Y - flatAct ξ q Y‖ < 2 * parDisp Γ ξ Y`.  By the flat law of cosines
(`Work.Mostow.cuspHoro.cosh_hdist_eq_flatAct` shape: `cosh (hdist u (q • u)) = 1 + (L * ‖Y - flatAct ξ q Y‖)^2/2`,
using `hvan` for level preservation)
`hdist u (q • u) ≤ arcosh (1 + 2 * (cEps ε)^2)`, which is `< ε_M(1)` for `ε ≤ ε₀` with `ε₀`
chosen from `Work.Mostow.margulisCusp n hn hA hI 1`.  `Work.Mostow.margulisCusp` then gives, for
any `γ` with `hdist u (γ • u) ≤ 1`, that `bd γ ξ = ξ`.  In particular every element of
`F_u := {γ : Γ | hdist u (γ • u) < ε/2}` fixes `ξ`.

**(2) No element of `F_u` is parabolic and `F_u` is not bigger than `N`.**  For `γ ≠ γ'` in
`F_u`, put `h := γ⁻¹ γ' ∈ Γ_ξ`.  By the triangle inequality `hdist u (h • u) < ε`.  If `h` were
parabolic then `u ∈ cuspThinRegion Γ ξ ε`, i.e. `lev ξ u * parDisp Γ ξ (yc ξ u) < cEps ε` by
`Work.Mostow.cuspThinRegion_eq_parDisp`, contradicting the frontier equation.  Hence `h = 1` or
`h` is elliptic: use `Work.Mostow.stabParabOrEllip` with `bCocy h ξ = 0` (from `hvan`).

**(3) The rotation parts are `θ`-separated.**  With `A_σ := flatLin ξ (Λσ)`, `hgap` gives a unit
`y ⊥ ξ` with `θ ≤ ‖A_h y - y‖` for the nontrivial elliptic `h`, and multiplicativity of
`flatLin` on `Γ_ξ` gives `A_{γ'} = A_γ * A_h`, so that
`‖A_{γ'} y - A_γ y‖ = ‖A_h y - y‖ ≥ θ`.  Hence `‖A_γ - A_{γ'}‖ ≥ θ` in operator norm and the map
`γ ↦ A_γ` is injective on `F_u`.

**(4) Conclude.**  `Work.Mostow.rotPacking (n-1) θ hθ` bounds the cardinality of any
`θ`-separated family in `O(n-1)`; transport the flat linear parts to `E (n-1)` with the bundle
`E (n-1) ≃ₗᵢ[ℝ] E (n-1)` (there is a linear isometry equivalence `ξ^⊥ ≅ E (n-1)` on disk, e.g.
`Work.Mostow.xPerpEquiv`, used in `flatActLevelOne.lean`) to get `F_u.ncard ≤ N` for a fixed `N`
depending only on `n` and `θ`.

`Work.Mostow.frontierShortBoundUniform` on disk is the same statement phrased with
`frontier (cuspThinRegion Γ ξ ε)` in place of the equation; the two are interchangeable by
`cuspThinRegion_eq_parDisp` together with continuity of `lev ξ · parDisp Γ ξ (yc ξ ·)`.
-/

namespace Work.Mostow
end Work.Mostow
