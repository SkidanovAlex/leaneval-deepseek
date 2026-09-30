import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSSR.coherentLiftDefs
import Submission.Work.SSSR.serreE1Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- **The vertex underlying a simplex, read off at degree zero.**

`Work.SSSR.sigmaVert σ` is the point of `B` underlying the simplex `σ : Δ[n] ⟶ Sing B` (the `0`-th
vertex of its underlying continuous map), defined in `serreE1Defs.lean` via
`TopCat.toSSetObjEquivT` applied to `SSet.yonedaEquiv σ` at the `0`-th vertex of `Δ[n]`.  The same
point is obtained by looking at the value of `σ` at degree `0` on the `0`-th vertex
`Work.SSSR.ssetVertex n` of `Δ[n]`, i.e.

`TopCat.toSSetObj₀Equiv (σ.app (op ⦋0⦌) (ssetVertex n)) = sigmaVert σ`.

Proof route: `ssetVertex n = (Δ[n] : SSet).map u.op (stdIdSimplex n)` where
`u := SSet.yonedaEquiv (Work.SSSR.ssetVertex n) : ⦋0⦌ ⟶ ⦋n⦌` is the map picking the `0`-th vertex,
so by the naturality of `σ`,
`σ.app (op ⦋0⦌) (ssetVertex n) = (sSing B).map u.op (σ.app (op ⦋n⦌) (stdIdSimplex n))`, and
`σ.app (op ⦋n⦌) (stdIdSimplex n) = SSet.yonedaEquiv σ` (`SSet.yonedaEquiv_map`,
`SSet.yonedaEquiv_comp`, `stdIdSimplex = SSet.yonedaEquiv (𝟙 _)`).  Then apply
`TopCat.toSSetObjEquivT_naturality_apply` (which turns `(sSing B).map u.op` into
`stdSimplex.map u`) and `stdSimplex.map_vertex` to identify `stdSimplex.map u (the point of Δ[0])`
with the `0`-th vertex `⟨Pi.single 0 1, _⟩` of `Δ[n]`, which is how `Work.SSSR.sigmaVert` is
defined.  Useful existing lemmas: `Work.SSSR.objEquiv_stdSimplex_map`,
`Work.SSSR.obj₀Equiv_stdSimplex_map`, `Work.SSSR.ssetVertex`,
`Work.SSSR.ssetVertex_delta_apply` (`ssetVertex_delta_apply.lean`),
`TopCat.toSSetObj₀Equiv_apply`, `TopCat.toSSetObjEquivT_naturality_apply`. -/
theorem sigmaVert_app_ssetVertex {B : Type} [TopologicalSpace B] {n : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    TopCat.toSSetObj₀Equiv (σ.app (op ⦋0⦌) (Work.SSSR.ssetVertex n))
      = Work.SSSR.sigmaVert σ := by
  -- `u` is the map `⦋0⦌ ⟶ ⦋n⦌` picking out the `0`-th vertex of `Δ[n]`.
  let u : ⦋0⦌ ⟶ ⦋n⦌ := SSet.stdSimplex.objEquiv (Work.SSSR.ssetVertex n)
  -- `z` is the fundamental `n`-simplex `[id_n]` of `Δ[n]`.
  let z : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) _⦋n⦌ :=
    SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk n))
  have hz : SSet.stdSimplex.objEquiv z = 𝟙 (SimplexCategory.mk n) :=
    SSet.stdSimplex.objEquiv.apply_symm_apply _
  -- The `0`-th vertex is the `u`-image of `z`.
  have hmap : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}).map u.op z
      = Work.SSSR.ssetVertex n := by
    rw [SSet.stdSimplex.map_apply, hz, Category.comp_id]
    exact Equiv.symm_apply_apply _ _
  -- The simplex underlying `σ`, evaluated at `z`, is `SSet.yonedaEquiv σ`.
  have h2 : σ.app (op ⦋n⦌) z = SSet.yonedaEquiv σ := by
    conv_lhs => rw [← Equiv.symm_apply_apply SSet.yonedaEquiv σ]
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm (n := SimplexCategory.mk n)
        (x := SSet.yonedaEquiv σ) (m := op ⦋n⦌) (f := 𝟙 (SimplexCategory.mk n))]
    simp
  -- `u` is the monotone map sending the unique vertex of `Δ[0]` to `0`.
  have hvertex : u.toOrderHom (0 : Fin 1) = 0 := by
    show (SSet.stdSimplex.objEquiv (Work.SSSR.ssetVertex n)).toOrderHom 0 = 0
    rw [SSet.stdSimplex.objEquiv_toOrderHom_apply, ← SSet.stdSimplex.obj₀Equiv_apply]
    rw [Work.SSSR.ssetVertex, Equiv.apply_symm_apply]
  -- Naturality of `σ` computes its value on the `0`-th vertex.
  have hnat : σ.app (op ⦋0⦌) (Work.SSSR.ssetVertex n)
      = (Work.SSSR.sSing B).map u.op (SSet.yonedaEquiv σ) := by
    rw [← hmap,
      show σ.app (op ⦋0⦌) ((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}).map u.op z)
          = (Work.SSSR.sSing B).map u.op (σ.app (op ⦋n⦌) z) from
        ConcreteCategory.congr_hom (σ.naturality u.op) z,
      h2]
  rw [hnat, TopCat.toSSetObj₀Equiv_eq_T _ (⟨Pi.single (0 : Fin (⦋0⦌.len + 1)) 1, single_mem_stdSimplex ℝ (0 : Fin (⦋0⦌.len + 1))⟩ : stdSimplex ℝ (Fin (⦋0⦌.len + 1))), TopCat.toSSetObjEquivT_naturality_apply]
  rw [Work.SSSR.sigmaVert]
  congr 1
  -- It remains to identify `stdSimplex.map u (default : stdSimplex ℝ (Fin 1))` with the
  -- `0`-th vertex `⟨Pi.single 0 1, _⟩` of `Δ[n]`.
  have hd : (⟨Pi.single (0 : Fin (⦋0⦌.len + 1)) 1, single_mem_stdSimplex ℝ (0 : Fin (⦋0⦌.len + 1))⟩ : stdSimplex ℝ (Fin (⦋0⦌.len + 1))) = stdSimplex.vertex (0 : Fin 1) := by
    first | rfl | (ext i; simp [stdSimplex.vertex]) | exact Subsingleton.elim _ _
  rw [hd, stdSimplex.map_vertex]
  rw [show (⇑(ConcreteCategory.hom u)) (0 : Fin 1) = 0 from hvertex]

end Work.SSSR
