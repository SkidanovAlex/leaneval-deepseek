import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSS.piszDefs
import Submission.Work.SSS.sSingP_fibreIncl_comp

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Auxiliary lemmas about the dictionary `TopCat.toSSetObjEquivT`

The singular simplicial set `sSing X = TopCat.toSSet.obj (TopCat.of X)` has `n`-simplices the
continuous maps `Δ_n ⟶ X`, and the dictionary is `TopCat.toSSetObjEquivT`.  The lemmas below record
the compatibility of this dictionary with (a) the map induced by a continuous map, (b) the
constant simplicial map, and (c) the simplicial operators, all at arbitrary objects `n` of
`SimplexCategoryᵒᵖ` (the last one directly in the form needed below.) -/

/-- The dictionary `TopCat.toSSetObjEquivT` turns the simplicial map `sSingP p` into the
postcomposition with the continuous map `p`. -/
lemma sSingP_toSSetObjEquiv_apply (p : C(E, B)) (n : SimplexCategoryᵒᵖ)
    (x : (Work.SSS.sSing E).obj n) :
    TopCat.toSSetObjEquivT (TopCat.of B) n ((Work.SSS.sSingP p).app n x)
      = p.comp (TopCat.toSSetObjEquivT (TopCat.of E) n x) := rfl

/-- The `n`-simplex of the constant simplicial map at `σ₀`, read through the dictionary
`TopCat.toSSetObjEquivT`, is the constant continuous map with value `TopCat.toSSetObj₀Equiv σ₀`
(general form of `Work.SSS.toSSetObjEquiv_const_apply`, for an arbitrary object `n`). -/
lemma toSSetObjEquiv_const_app {B : Type} [TopologicalSpace B]
    (σ₀ : (Work.SSS.sSing B).obj (op ⦋0⦌)) (n : SimplexCategoryᵒᵖ) (X : SSet.{0})
    (x : X.obj n) :
    TopCat.toSSetObjEquivT (TopCat.of B) n ((SSet.const (X := X) σ₀).app n x) =
      ContinuousMap.const _ (TopCat.toSSetObj₀Equiv σ₀) := by
  have happ : (SSet.const (X := X) σ₀).app n x =
      (ConcreteCategory.hom ((Work.SSS.sSing B).map ((unop n).const ⦋0⦌ 0).op)) σ₀ := by
    rw [SSet.const_app]; rfl
  ext z
  rw [happ]
  rw [TopCat.toSSetObjEquivT_naturality_apply]
  simp only [ContinuousMap.const_apply]
  exact (TopCat.toSSetObj₀Equiv_eq_T σ₀ _).symm

/-- Naturality of the dictionary `TopCat.toSSetObjEquivT` in the simplex, stated for a morphism
`f` of `SimplexCategoryᵒᵖ` (so `f.unop` is the corresponding map of the simplex category). -/
lemma toSSetObjEquiv_naturality_op {X : TopCat} {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (TopCat.toSSet.obj X).obj n) (z : stdSimplex ℝ (Fin (m.unop.len + 1))) :
    TopCat.toSSetObjEquivT X m ((TopCat.toSSet.obj X).map f x) z
      = TopCat.toSSetObjEquivT X n x (stdSimplex.map f.unop z) :=
  TopCat.toSSetObjEquivT_naturality_apply f.unop x z

/-- **A simplicial map over a constant base point factors through the fibre.**

If `w : A ⟶ Sing E` satisfies `w ≫ Sing p = const b'` (the constant simplicial map at the vertex
`b'`), then `w` lands in the sub-simplicial set `Sing (p⁻¹b')` of singular simplices of `E` over
`b'`, i.e. it factors as `v ≫ Sing (fibreIncl p b')`.

Proof route: for `a : A _⦋n⦌` the `n`-simplex `w a` of `Sing E` is a continuous map `Δ_n ⟶ E`,
whose composite with `p` is the constant simplex at `b'` (read off `hw` through
`TopCat.toSSetObjEquivT`); hence `w a` lands in the subtype `p⁻¹b'` and defines an `n`-simplex of
`Sing (p⁻¹b')`.  Continuity is `Continuous.subtype_mk`, and naturality in `n` follows from the
naturality of `w` (`SSet` morphism extensionality componentwise; useful lemmas:
`TopCat.toSSetObjEquiv_const_apply`, `TopCat.toSSetObjEquiv_naturality`). -/
theorem sSing_fibre_factor (p : C(E, B)) (b' : B) (A : SSet.{0}) (w : A ⟶ Work.SSS.sSing E)
    (hw : w ≫ Work.SSS.sSingP p = SSet.const (TopCat.toSSetObj₀Equiv.symm b')) :
    ∃ v : A ⟶ Work.SSS.sSing (Work.StemsB.fibre p b'),
      v ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p b') = w := by
  -- The evaluation form of `w`: the continuous map `Δ_n ⟶ E` underlying `w a`.
  let ev : ∀ (n : SimplexCategoryᵒᵖ), A.obj n → C(stdSimplex ℝ (Fin (n.unop.len + 1)), E) :=
    fun n a => TopCat.toSSetObjEquivT (TopCat.of E) n (w.app n a)
  -- `w a` lands over `b'`.
  have hpt : ∀ (n : SimplexCategoryᵒᵖ) (a : A.obj n) (z : stdSimplex ℝ (Fin (n.unop.len + 1))),
      p (ev n a z) = b' := by
    intro n a z
    have h1 : (Work.SSS.sSingP p).app n (w.app n a)
        = (SSet.const (X := A) (TopCat.toSSetObj₀Equiv.symm b')).app n a :=
      congrArg (fun (φ : A ⟶ Work.SSS.sSing B) => φ.app n a) hw
    have h2 := congrArg (fun x => TopCat.toSSetObjEquivT (TopCat.of B) n x) h1
    rw [sSingP_toSSetObjEquiv_apply p n (w.app n a),
        toSSetObjEquiv_const_app (TopCat.toSSetObj₀Equiv.symm b') n A a] at h2
    have h3 := congrArg (fun (g : C(stdSimplex ℝ (Fin (n.unop.len + 1)), B)) => g z) h2
    simp only [ContinuousMap.comp_apply, ContinuousMap.const_apply, Equiv.apply_symm_apply] at h3
    show p ((TopCat.toSSetObjEquivT (TopCat.of E) n (w.app n a)) z) = b'
    exact h3
  -- The underlying continuous map `Δ_n ⟶ p⁻¹b'` of the simplex `v a`.
  let mkFib : ∀ (n : SimplexCategoryᵒᵖ) (a : A.obj n),
      C(stdSimplex ℝ (Fin (n.unop.len + 1)), Work.StemsB.fibre p b') :=
    fun n a => ⟨fun z => ⟨ev n a z, hpt n a z⟩,
      Continuous.subtype_mk (ev n a).continuous (hpt n a)⟩
  -- The components of the factorisation `v`.
  let vapp : (X : SimplexCategoryᵒᵖ) → A.obj X ⟶
      (Work.SSS.sSing (Work.StemsB.fibre p b')).obj X :=
    fun n => ↾(fun a =>
      (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b')) n).symm (mkFib n a))
  have vapp_spec : ∀ (n : SimplexCategoryᵒᵖ) (a : A.obj n),
      TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b')) n (vapp n a) = mkFib n a := by
    intro n a
    simp only [vapp, ConcreteCategory.hom_ofHom]
    exact Equiv.apply_symm_apply _ _
  refine ⟨⟨vapp, ?nat⟩, ?comp⟩
  case nat =>
    -- `v` is natural in the simplex
    intro X Y f
    apply ConcreteCategory.coe_ext
    funext a
    simp only [ConcreteCategory.comp_apply]
    apply (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b')) Y).injective
    rw [vapp_spec Y ((ConcreteCategory.hom (A.map f)) a)]
    apply ContinuousMap.ext
    intro z
    rw [toSSetObjEquiv_naturality_op f ((ConcreteCategory.hom (vapp X)) a) z, vapp_spec X a]
    apply Subtype.ext
    show (ev Y ((ConcreteCategory.hom (A.map f)) a)) z
      = (ev X a) (stdSimplex.map (⇑(ConcreteCategory.hom f.unop)) z)
    have hn : (ConcreteCategory.hom (w.app Y)) ((ConcreteCategory.hom (A.map f)) a)
        = (ConcreteCategory.hom ((TopCat.toSSet.obj (TopCat.of E)).map f))
            ((ConcreteCategory.hom (w.app X)) a) :=
      NatTrans.naturality_apply w f a
    have hn2 := congrArg (fun x => TopCat.toSSetObjEquivT (TopCat.of E) Y x z) hn
    rw [toSSetObjEquiv_naturality_op f ((ConcreteCategory.hom (w.app X)) a) z] at hn2
    exact hn2
  case comp =>
    -- `v ≫ Sing (fibreIncl p b') = w`
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.coe_ext
    funext a
    simp only [SSet.comp_app, ConcreteCategory.comp_apply]
    apply (TopCat.toSSetObjEquivT (TopCat.of E) n).injective
    rw [sSingP_toSSetObjEquiv_apply (Work.StemsB.fibreIncl p b') n
          ((ConcreteCategory.hom (vapp n)) a), vapp_spec n a]
    apply ContinuousMap.ext
    intro z
    rfl

end Work.SSS
