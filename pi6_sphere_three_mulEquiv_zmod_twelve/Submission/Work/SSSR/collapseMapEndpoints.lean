import Mathlib
import Submission.Work.SSSR.collapseDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open scoped Simplicial
open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
/-- Computation rule for `collapseHom`: it is `j ↦ if μ j = 0 then a j else s`. -/
lemma collapseHom_apply {s n : ℕ} (a : Fin (n + 1) →o Fin (s + 1))
    (mu : Fin (n + 1) →o Fin 2) (j : Fin (n + 1)) :
    collapseHom a mu j = if (mu j : ℕ) = 0 then a j else Fin.last s := rfl

/-- `collapseMap s` applied to an `X`-simplex of the prism, read through `objEquiv` of `Δ[s]`. -/
lemma collapseMap_app_objEquiv (s : ℕ) (X : SimplexCategoryᵒᵖ)
    (z : ((SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet) ⊗
      (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet)).obj X) :
    SSet.stdSimplex.objEquiv ((collapseMap s).app X z) =
      SimplexCategory.Hom.mk (collapseHom
        (SimplexCategory.Hom.toOrderHom (SSet.stdSimplex.objEquiv z.1))
        (SimplexCategory.Hom.toOrderHom
          (SSet.stdSimplex.objEquiv (n := SimplexCategory.mk 1) (m := X) z.2))) := rfl

/-- Naturality of `objEquiv` with respect to the simplicial structure map of `Δ[n]`. -/
lemma objEquiv_map {n : SimplexCategory} {m m' : SimplexCategoryᵒᵖ} (g : m ⟶ m')
    (y : (SSet.stdSimplex.obj n).obj m) :
    SSet.stdSimplex.objEquiv ((SSet.stdSimplex.obj n).map g y)
      = g.unop ≫ SSet.stdSimplex.objEquiv y := by
  conv_lhs => rw [← Equiv.symm_apply_apply SSet.stdSimplex.objEquiv y]
  rw [SSet.stdSimplex.map_objEquiv_symm, Equiv.apply_symm_apply]

/-- The last vertex `v_s` of `Δ[s]`, read through `objEquiv`, is the constant order hom. -/
lemma objEquiv_obj₀Equiv_symm_last (s : ℕ) :
    SSet.stdSimplex.objEquiv ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s))
      = SimplexCategory.Hom.mk (OrderHom.const (Fin (0 + 1)) (Fin.last s)) := by
  rw [SSet.stdSimplex.obj₀Equiv_symm_apply]
  rfl

/-- Computation rule for the constant map of simplicial sets, on a simplex. -/
lemma const_app_apply {X Y : SSet} (y : Y _⦋0⦌) (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    (SSet.const y).app n x = Y.map ((unop n).const ⦋0⦌ 0).op y := rfl

/-- **The two endpoints of the collapse of the prism.**
`Work.SSSR.collapseMap s : Δ[s] ⊗ Δ[1] ⟶ Δ[s]` (defined in
`Submission/Work/SSS/collapseDefs.lean`) is the map
`(a, μ) ↦ (j ↦ if μ j = 0 then a j else s)` on `n`-simplices.  Its `0`-end is the identity and
its `1`-end is the constant map at the last vertex `v_s`; equivalently, `collapseMap s` exhibits a
homotopy from `𝟙 Δ[s]` to the constant map at `v_s`.  (Note `SSet.ι₁` is `lift (𝟙 X) (const 1)`
and `(SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s) : Δ[s] _⦋0⦌` is the last vertex.)

Useful lemmas: `SSet.ι₀_app_fst`, `SSet.ι₀_app_snd_apply`, `SSet.ι₁_app_fst`,
`SSet.ι₁_app_snd_apply`, `SSet.hom_ext`, `SimplexCategory.Hom.mk_toOrderHom`,
`SimplexCategory.Hom.toOrderHom_mk`, `SSet.stdSimplex.objEquiv_symm_apply`,
`SSet.stdSimplex.objEquiv`, `SSet.const`, and possibly
`set_option backward.isDefEq.respectTransparency false in`. -/
theorem collapseMapEndpoints (s : ℕ) :
    (SSet.ι₀ ≫ Work.SSSR.collapseMap s =
      𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet)) ∧
    (SSet.ι₁ ≫ Work.SSSR.collapseMap s =
      SSet.const (X := (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet))
        ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s))) := by
  constructor
  · -- The `0`-end: `ι₀ ≫ collapseMap s = 𝟙`.
    apply SSet.hom_ext
    intro X
    cases X with
    | op Y =>
      cases Y with
      | mk n =>
        rw [SSet.comp_app, SSet.id_app]
        apply ConcreteCategory.hom_ext
        intro x
        simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply]
        apply SSet.stdSimplex.objEquiv.injective
        rw [collapseMap_app_objEquiv]
        apply SimplexCategory.Hom.ext
        ext j
        rw [SimplexCategory.Hom.toOrderHom_mk, collapseHom_apply]
        simp
  · -- The `1`-end: `ι₁ ≫ collapseMap s` is the constant map at the last vertex.
    apply SSet.hom_ext
    intro X
    cases X with
    | op Y =>
      cases Y with
      | mk n =>
        rw [SSet.comp_app]
        apply ConcreteCategory.hom_ext
        intro x
        simp only [CategoryTheory.comp_apply]
        apply SSet.stdSimplex.objEquiv.injective
        rw [collapseMap_app_objEquiv]
        have hmu : SimplexCategory.Hom.toOrderHom
              (SSet.stdSimplex.objEquiv (n := SimplexCategory.mk 1) (m := op ⦋n⦌)
                (SSet.ι₁.app (op ⦋n⦌) x).2)
            = OrderHom.const (Fin (n + 1)) 1 := by
          ext j
          simp [SSet.ι₁_app_snd_apply]
        rw [hmu]
        have hcollapse : collapseHom
            (SimplexCategory.Hom.toOrderHom (SSet.stdSimplex.objEquiv (SSet.ι₁.app (op ⦋n⦌) x).1))
            (OrderHom.const (Fin (n + 1)) 1)
            = OrderHom.const (Fin (n + 1)) (Fin.last s) := by
          ext j
          simp [collapseHom_apply]
        rw [hcollapse]
        rw [const_app_apply]
        rw [objEquiv_map]
        rw [objEquiv_obj₀Equiv_symm_last]
        rfl

end Work.SSSR
