import Mathlib
import Submission.Work.Pi6.MSS.E2cfkDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

/-- **The singular simplicial set of the fibre maps into the simplicial pullback of a base
simplex.**

For a continuous map `p : E → B` and a simplex `σ : Δ[1] ⟶ Sing B`, let `b₀ = sigmaVert σ` be the
point of `B` underlying the `0`-th vertex of `σ`.  Then `Sing p : Sing E ⟶ Sing B` and the simplex
`σ` exhibit `Sing (p⁻¹ b₀)` as the fibre of the projection `pullback.snd σ (Sing p)`: there is a
simplicial map

`κ : Sing (fibre p b₀) ⟶ pullAlong (Sing p) σ`

with `κ ≫ pullback.snd σ (Sing p) = Sing (fibreIncl p b₀)`.

Concretely, the pullback condition requires a map `a : Sing (fibre p b₀) ⟶ Δ[1]` with
`a ≫ σ = Sing (fibreIncl p b₀) ≫ Sing p`.  The right-hand side is the constant simplicial map at
the point `b₀` (`Work.SSS.sSingP_fibreIncl_comp`), and taking `a` to be the constant simplicial map
at the `0`-th vertex of `Δ[1]` makes `a ≫ σ` the constant map at `σ` evaluated at that vertex,
which is `b₀` by `Work.SSS.sigmaVert_app_ssetVertex`.  The map `κ` is then the induced map into the
pullback, and its composite with the second projection is `Sing (fibreIncl p b₀)` by the universal
property of the pullback. -/
theorem fibre_to_pullback {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    ∃ κ : Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)) ⟶
        Work.SSSR.pullAlong (Work.SSS.sSingP p) σ,
      CategoryTheory.CategoryStruct.comp κ
          (CategoryTheory.Limits.pullback.snd σ (Work.SSS.sSingP p))
        = Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.SSS.sigmaVert σ)) := by
  -- The map `a` into `Δ[1]` is the constant simplicial map at the `0`-th vertex of `Δ[1]`; the
  -- map `b` into `Sing E` is `Sing (fibreIncl p b₀)`.  Their composites with `σ` and `Sing p`
  -- agree because both are the constant map at `b₀`.
  refine ⟨CategoryTheory.Limits.pullback.lift (SSet.const (Work.SSS.ssetVertex 1))
    (Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.SSS.sigmaVert σ))) ?_, ?_⟩
  · -- Pullback condition: `SSet.const v₀ ≫ σ = Sing (fibreIncl p b₀) ≫ Sing p`.
    -- The left-hand side is constant at `σ(v₀)`, the right-hand side at `b₀ = sigmaVert σ`.
    have h1 : σ.app (Opposite.op (SimplexCategory.mk 0)) (Work.SSS.ssetVertex 1)
        = TopCat.toSSetObj₀Equiv.symm (Work.SSS.sigmaVert σ) := by
      rw [← Work.SSS.sigmaVert_app_ssetVertex σ, Equiv.symm_apply_apply]
    rw [SSet.const_comp, Work.SSS.sSingP_fibreIncl_comp, h1]
  · -- The composite with the second projection of the pullback is its second leg.
    exact CategoryTheory.Limits.pullback.lift_snd _ _ _

end Work.Pi6.MSS
