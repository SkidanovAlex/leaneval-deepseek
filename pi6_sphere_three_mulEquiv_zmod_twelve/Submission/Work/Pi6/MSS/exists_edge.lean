import Mathlib
import Submission.Work.Pi6.MSS.E2cfkDefs
import Submission.Work.RatHurewicz.ConnectivityBridge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Existence of a singular `1`-simplex of `B` joining `b` to `p e₀`

`Work.Pi6.MSS.exists_edge` produces, for a continuous map `p : C(E, B)` with `B` simply
connected (in the cube model of `Work.PiS.SimplyConn`, i.e. `π₀` and `π₁` at the base point
trivial) and any `b : B`, an edge of the singular simplicial set `Sing B`

`σ : Δ[1] ⟶ Work.SSS.sSing B`

whose `0`-th vertex is `b` (`Work.SSS.sigmaVert σ = b`) and whose `1`-st vertex is `p e₀`
(`Work.Pi6.MSS.E2cfk.lastVert σ = p e₀`, where `lastVert` is `sigmaVert` of the `0`-th face,
which picks out the vertex `1` of `Δ[1]`).

This is pure connectivity: `π₀`-triviality at `p e₀` makes `B` path connected
(`Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero`), so there is a path `γ` from `b`
to `p e₀`, and any path yields a `1`-simplex of `Sing B` whose two vertices are its endpoints.

The proof is organised as follows.  A `1`-simplex of `Sing B` is the Yoneda transpose of a
continuous map `Δ¹ = stdSimplex ℝ (Fin 2) → B`; the two lemmas `sigmaVert_eq_underlying` and
`lastVert_eq_underlying` read off the two vertices from that underlying map.  For the edge
```
  σ γ := (yonedaEquiv)⁻¹ ((toSSetObjEquivT)⁻¹ (γ ∘ h)),
  h := (stdSimplexHomeomorphUnitInterval : Δ¹ ≃ₜ I),
```
the two vertex evaluations are `γ 0` and `γ 1` (`sigmaVert_edge`, `lastVert_edge`), which are
`b` and `p e₀` for a path `γ` from `b` to `p e₀`.
-/

set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSS

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## Reading off the vertices of a singular `1`-simplex -/

/-- **The `0`-th vertex of a singular `1`-simplex.**  A `1`-simplex `σ : Δ[1] ⟶ Sing B` is the
Yoneda transpose of a continuous map `Δ¹ → B`, and `sigmaVert` is that map evaluated at the
vertex `0` of `Δ¹`. -/
lemma sigmaVert_eq_underlying
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Work.SSS.sigmaVert σ
      = ((TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk 1)))
          (SSet.yonedaEquiv σ)) (stdSimplex.vertex (0 : Fin 2)) := by
  rw [Work.SSS.sigmaVert]

/-- **The `1`-st vertex of a singular `1`-simplex.**  `lastVert σ = sigmaVert (δ₀ ≫ σ)` is the
underlying continuous map of `σ` evaluated at the vertex `1` of `Δ¹` (`δ₀ : Δ[0] ⟶ Δ[1]` is the
face which picks out the vertex `1`). -/
lemma lastVert_eq_underlying
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Work.Pi6.MSS.E2cfk.lastVert σ
      = ((TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk 1)))
          (SSet.yonedaEquiv σ)) (stdSimplex.vertex (1 : Fin 2)) := by
  have hδ : SSet.stdSimplex.δ (n := 0) 0
      = SSet.stdSimplex.map (SimplexCategory.δ (n := 0) 0) := rfl
  show Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := 0) 0 ≫ σ) = _
  rw [Work.SSS.sigmaVert, hδ,
    ← SSet.yonedaEquiv_naturality (SimplexCategory.δ (n := 0) 0) σ]
  rw [TopCat.toSSetObjEquivT_naturality_apply]
  rw [show (⟨Pi.single (0 : Fin 1) 1, single_mem_stdSimplex ℝ (0 : Fin 1)⟩ : stdSimplex ℝ (Fin 1))
      = stdSimplex.vertex (0 : Fin 1) from rfl]
  rw [stdSimplex.map_vertex]
  rw [show (⇑(ConcreteCategory.hom (SimplexCategory.δ (n := 0) 0))) (0 : Fin 1) = (1 : Fin 2)
      from rfl]

/-! ## The singular `1`-simplex attached to a path -/

/-- The homeomorphism `Δ¹ ≅ I`, as a continuous map on the standard `2`-simplex. -/
def stdSimplexToUnitInterval : C(stdSimplex ℝ (Fin 2), unitInterval) :=
  ⟨⇑stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

/-- **The singular `1`-simplex attached to a path.**  The Yoneda transpose of the continuous map
`Δ¹ → B` obtained by reparametrising `γ` along the homeomorphism `Δ¹ ≅ I`. -/
abbrev edgeSimplex (γ : C(unitInterval, B)) :
    (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B :=
  SSet.yonedaEquiv.symm ((TopCat.toSSetObjEquivT (TopCat.of B)
    (Opposite.op (SimplexCategory.mk 1))).symm (γ.comp stdSimplexToUnitInterval))

lemma edgeSimplex_yonedaEquiv (γ : C(unitInterval, B)) :
    SSet.yonedaEquiv (edgeSimplex γ) = ((TopCat.toSSetObjEquivT (TopCat.of B)
      (Opposite.op (SimplexCategory.mk 1))).symm (γ.comp stdSimplexToUnitInterval)) :=
  Equiv.apply_symm_apply _ _

lemma toSSetObjEquivT_edgeSimplex (γ : C(unitInterval, B)) :
    (TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk 1)))
        (SSet.yonedaEquiv (edgeSimplex γ)) = γ.comp stdSimplexToUnitInterval := by
  rw [edgeSimplex_yonedaEquiv]
  exact Equiv.apply_symm_apply _ _

/-- **The `0`-th vertex of the edge attached to a path** is the source of the path. -/
lemma sigmaVert_edge (γ : C(unitInterval, B)) : Work.SSS.sigmaVert (edgeSimplex γ) = γ 0 := by
  rw [sigmaVert_eq_underlying, toSSetObjEquivT_edgeSimplex, ContinuousMap.comp_apply]
  congr 1

/-- **The `1`-st vertex of the edge attached to a path** is the target of the path. -/
lemma lastVert_edge (γ : C(unitInterval, B)) :
    Work.Pi6.MSS.E2cfk.lastVert (edgeSimplex γ) = γ 1 := by
  rw [lastVert_eq_underlying, toSSetObjEquivT_edgeSimplex, ContinuousMap.comp_apply]
  congr 1

/-! ## The main statement -/

theorem exists_edge {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (e₀ : E) (hconn : Work.PiS.SimplyConn B (p e₀)) (b : B) :
    ∃ σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B,
      Work.SSS.sigmaVert σ = b ∧ Work.Pi6.MSS.E2cfk.lastVert σ = p e₀ := by
  haveI : PathConnectedSpace B :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (p e₀) hconn.1
  let γ : Path b (p e₀) := PathConnectedSpace.somePath b (p e₀)
  exact ⟨edgeSimplex γ.toContinuousMap, by rw [sigmaVert_edge]; exact γ.source,
    by rw [lastVert_edge]; exact γ.target⟩

end

end Work.Pi6.MSS
