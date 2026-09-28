import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Pullback
import Submission.Work.EmbeddedSpheres.Hurewicz.Face
import Submission.Work.StemsB.compactSupportChain

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology Simplicial unitInterval

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The `p`-th face inclusion of the standard `t`-simplex. -/
def facept (t : ℕ) (p : Fin (t + 1)) : C(stdSimplex ℝ (Fin t), stdSimplex ℝ (Fin (t + 1))) :=
  ⟨stdSimplex.map p.succAbove, stdSimplex.continuous_map p.succAbove⟩

/-! ## The abstract model of a cycle

The top cells of the model are the simplices of the support of the cycle, realized as copies of the
standard simplex; each carries one arc to the base point, and the faces that agree in `X` are glued
together.  The model is indexed by `n`, the top cells being `(n+1)`-simplices, so that their faces
are `n`-simplices and all the arities of the face maps line up definitionally. -/

/-- The data of the model: an index type of top cells, their simplices and connecting arcs. -/
structure MData (X : Type) [TopologicalSpace X] (n : ℕ) (x₀ : X) where
  Idx : Type
  finIdx : Fintype Idx
  simplexMap : Idx → Work.EmbeddedSpheres.Hurewicz.Simp (TopCat.of X) (n + 1)
  arcPath : Idx → C(unitInterval, X)
  arc_zero : ∀ i, arcPath i 0 = simplexMap i (stdSimplex.vertex (0 : Fin (n + 2)))
  arc_one : ∀ i, arcPath i 1 = x₀

attribute [instance] MData.finIdx

/-- The raw space: a copy of `Δ^{n+1}` and a copy of `Δ¹` for each top cell. -/
abbrev Raw {n : ℕ} (D : MData X n x₀) : Type :=
  (Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) ⊕ (Σ _ : D.Idx, unitInterval)

/-- The gluing relation of the model. -/
def modelRel {n : ℕ} (D : MData X n x₀) (a b : Raw D) : Prop :=
  (∃ (i j : D.Idx) (p q : Fin (n + 2)) (x : stdSimplex ℝ (Fin (n + 1))),
      a = Sum.inl ⟨i, facept (n + 1) p x⟩ ∧ b = Sum.inl ⟨j, facept (n + 1) q x⟩ ∧
        ((D.simplexMap i).comp (facept (n + 1) p)
          = (D.simplexMap j).comp (facept (n + 1) q)))
  ∨ (∃ i : D.Idx, a = Sum.inl ⟨i, stdSimplex.vertex (0 : Fin (n + 2))⟩ ∧ b = Sum.inr ⟨i, 0⟩)
  ∨ (∃ i j : D.Idx, a = Sum.inr ⟨i, 1⟩ ∧ b = Sum.inr ⟨j, 1⟩)

/-- The model space. -/
abbrev Model {n : ℕ} (D : MData X n x₀) : Type := Quotient (Relation.EqvGen.setoid (modelRel D))

/-- The copy of the top cell. -/
def topMap {n : ℕ} (D : MData X n x₀) (i : D.Idx) : C(stdSimplex ℝ (Fin (n + 2)), Model D) where
  toFun x := Quotient.mk'' (Sum.inl ⟨i, x⟩)
  continuous_toFun := continuous_quotient_mk'.comp (continuous_inl.comp continuous_sigmaMk)

/-- The copy of the arc. -/
def arcMap {n : ℕ} (D : MData X n x₀) (i : D.Idx) : C(unitInterval, Model D) where
  toFun s := Quotient.mk'' (Sum.inr ⟨i, s⟩)
  continuous_toFun := continuous_quotient_mk'.comp (continuous_inr.comp continuous_sigmaMk)

/-- The map to `X` on the raw space. -/
def toXFun {n : ℕ} (D : MData X n x₀) : Raw D → X :=
  Sum.elim (fun p => D.simplexMap p.1 p.2) (fun p => D.arcPath p.1 p.2)

theorem continuous_toXFun {n : ℕ} (D : MData X n x₀) : Continuous (toXFun D) := by
  apply Continuous.sumElim
  · rw [continuous_sigma_iff]
    intro i
    exact (D.simplexMap i).continuous
  · rw [continuous_sigma_iff]
    intro i
    exact (D.arcPath i).continuous

theorem modelRel_toX {n : ℕ} {D : MData X n x₀} {a b : Raw D} (h : modelRel D a b) :
    toXFun D a = toXFun D b := by
  rcases h with ⟨i, j, p, q, x, rfl, rfl, hs⟩ | ⟨i, ha, hb⟩ | ⟨i, j, ha, hb⟩
  · simp only [toXFun, Sum.elim_inl]
    exact congrFun (congrArg DFunLike.coe hs) x
  · subst ha; subst hb
    simp only [toXFun, Sum.elim_inl, Sum.elim_inr]
    exact (D.arc_zero i).symm
  · subst ha; subst hb
    simp only [toXFun, Sum.elim_inr]
    rw [D.arc_one i, D.arc_one j]

theorem modelRel_wellDef {n : ℕ} (D : MData X n x₀) :
    ∀ a b : Raw D, Relation.EqvGen (modelRel D) a b → toXFun D a = toXFun D b := by
  intro a b h
  induction h with
  | rel x y hr => exact modelRel_toX hr
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- The map from the model to `X`. -/
def toX {n : ℕ} (D : MData X n x₀) : C(Model D, X) where
  toFun := Quotient.lift (toXFun D) (modelRel_wellDef D)
  continuous_toFun := Continuous.quotient_lift (continuous_toXFun D) (modelRel_wellDef D)

/-! ## The boundary of a generator of the singular chains -/

/-- The generator of the singular chain complex of a space attached to a simplex. -/
noncomputable def genQ {Y : Type} [TopologicalSpace Y] (n : ℕ)
    (s : Work.EmbeddedSpheres.Hurewicz.Simp (TopCat.of Y) n) :
    (Work.Cohomology.singularChains ℚ (TopCat.of Y)).X n :=
  Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of Y))
    ((TopCat.toSSetObjEquivT (TopCat.of Y) (Opposite.op (SimplexCategory.mk n))).symm s)

/-- The `ℤ`-smul of a `ℚ`-linear map, evaluated at `1`. -/
theorem zsmul_apply_rat {N : Type*} [AddCommGroup N] [Module ℚ N] (f : ℚ →ₗ[ℚ] N) (c : ℤ) :
    ((c • f : ℚ →ₗ[ℚ] N)) 1 = (c : ℚ) • f 1 := by
  rw [LinearMap.smul_apply]
  exact (Int.cast_smul_eq_zsmul ℚ c (f 1)).symm

/-- **The boundary of a generator of the singular chains of a space, with `ℚ`-coefficients.**

(The `ℤ` analogue is `Work.EmbeddedSpheres.Hurewicz.d_genElt`.) -/
theorem d_genElt_rat {Y : Type} [TopologicalSpace Y] (n : ℕ)
    (x : (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op (SimplexCategory.mk (n+1)))) :
    (ModuleCat.Hom.hom (((TopCat.toSSet.obj (TopCat.of Y)).chainComplex
        (ModuleCat.of ℚ ℚ)).d (n+1) n))
        (Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of Y)) x)
      = ∑ i : Fin (n+2), ((-1 : ℚ) ^ (i : ℕ)) •
          Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of Y))
            ((SimplicialObject.δ (TopCat.toSSet.obj (TopCat.of Y)) i) x) := by
  have h := congrArg
    (fun (g : ModuleCat.of ℚ ℚ ⟶ ((TopCat.toSSet.obj (TopCat.of Y)).chainComplex
        (ModuleCat.of ℚ ℚ)).X n) => ModuleCat.Hom.hom g (1 : ℚ))
    (SSet.ιChainComplex_d (X := TopCat.toSSet.obj (TopCat.of Y)) (R := ModuleCat.of ℚ ℚ) x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.sum_apply,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul] at h
  simp only [Work.Cohomology.genElt] at h ⊢
  rw [h]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [zsmul_apply_rat]
  congr 1
  push_cast
  ring

/-- **The boundary of a generator, in the `Simp` presentation of the simplices of a space.** -/
theorem d_genQ {Y : Type} [TopologicalSpace Y] (n : ℕ)
    (s : Work.EmbeddedSpheres.Hurewicz.Simp (TopCat.of Y) (n+1)) :
    (Work.Cohomology.singularChains ℚ (TopCat.of Y)).d (n+1) n (genQ (Y := Y) (n+1) s)
      = ∑ i : Fin (n+2), ((-1 : ℚ) ^ (i : ℕ)) •
          genQ (Y := Y) n (Work.EmbeddedSpheres.Hurewicz.face i s) := by
  have hface : ∀ i : Fin (n+2),
      (TopCat.toSSetObjEquivT (TopCat.of Y) (Opposite.op (SimplexCategory.mk n))).symm
          (Work.EmbeddedSpheres.Hurewicz.face i s)
      = (SimplicialObject.δ (TopCat.toSSet.obj (TopCat.of Y)) i)
        ((TopCat.toSSetObjEquivT (TopCat.of Y) (Opposite.op (SimplexCategory.mk (n+1)))).symm s) := by
    intro i
    refine (Equiv.symm_apply_eq _).mpr ?_
    apply ContinuousMap.ext
    intro z
    rw [TopCat.toSSetObjEquivT_δ_apply]
    rfl
  have key := d_genElt_rat (Y := Y) n
    ((TopCat.toSSetObjEquivT (TopCat.of Y) (Opposite.op (SimplexCategory.mk (n+1)))).symm s)
  show (ModuleCat.Hom.hom (((TopCat.toSSet.obj (TopCat.of Y)).chainComplex
      (ModuleCat.of ℚ ℚ)).d (n+1) n))
      (Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of Y))
        ((TopCat.toSSetObjEquivT (TopCat.of Y) (Opposite.op (SimplexCategory.mk (n+1)))).symm s))
    = ∑ i : Fin (n+2), ((-1 : ℚ) ^ (i : ℕ)) •
        genQ (Y := Y) n (Work.EmbeddedSpheres.Hurewicz.face i s)
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hface i]
  congr 1

/-! ## The model attached to a cycle -/

/-- Path connectedness of a space from the triviality of its `π₀` at a base point. -/
theorem pathConnectedSpace_of_subsingleton_pi0 {X : Type} [TopologicalSpace X] {x₀ : X}
    (h : Subsingleton (HomotopyGroup (Fin 0) X x₀)) : PathConnectedSpace X := by
  have hz0 : Subsingleton (ZerothHomotopy X) :=
    ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).symm.injective
      (Subsingleton.elim _ _)⟩
  exact pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk x₀⟩, hz0⟩

/-- The support of a chain with `ℚ`-coefficients: the finitely many simplices with nonzero
coefficient. -/
noncomputable def cycleSupport (m : ℕ)
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X m) :
    Finset ((TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk m))) :=
  (Work.StemsB.coordsQ (TopCat.toSSet.obj (TopCat.of X)) m z).support

/-- The coefficient of a simplex in a chain with `ℚ`-coefficients. -/
noncomputable def cycleCoeff (m : ℕ) (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X m)
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk m))) : ℚ :=
  Work.StemsB.coordsQ (TopCat.toSSet.obj (TopCat.of X)) m z s

variable (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀))

/-- A chosen path from a point of `X` to the base point `x₀`. -/
noncomputable def pathToBase (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀)) (y : X) :
    Path y x₀ :=
  Classical.choice ((pathConnectedSpace_of_subsingleton_pi0 hconnX).joined y x₀)

/-- **The model attached to an `(n+1)`-cycle `z`**: one copy of `Δ^{n+1}` for each simplex of the
support of `z`, glued along the faces that agree in `X`, plus one arc from a vertex of each copy to
`x₀`. -/
noncomputable def cycleMData (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀)) (n : ℕ)
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X (n + 1)) : MData X n x₀ where
  Idx := {s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk (n + 1))) //
    s ∈ cycleSupport (n + 1) z}
  finIdx := inferInstance
  simplexMap i := (TopCat.toSSetObjEquivT (TopCat.of X)
    (Opposite.op (SimplexCategory.mk (n + 1)))) i.1
  arcPath i := (pathToBase hconnX
    ((TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op (SimplexCategory.mk (n + 1)))) i.1
      (stdSimplex.vertex (0 : Fin (n + 2)))))
  arc_zero i := (pathToBase hconnX _).source
  arc_one i := (pathToBase hconnX _).target

/-- The space of the model attached to `z`. -/
abbrev cycleModelSpace (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀)) (n : ℕ)
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X (n + 1)) : Type :=
  Model (cycleMData hconnX n z)

/-- The map from the model of `z` to `X`. -/
noncomputable def cycleModelToX (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀)) (n : ℕ)
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X (n + 1)) :
    C(cycleModelSpace hconnX n z, X) := toX (cycleMData hconnX n z)

/-- **The chain of the model of `z`** lifting `z`: the sum of the identity simplices of the copies of
the simplices of the support of `z`, with the coefficients of `z`. -/
noncomputable def cycleChain (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀)) (n : ℕ)
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X (n + 1)) :
    (Work.Cohomology.singularChains ℚ
      (TopCat.of (cycleModelSpace hconnX n z))).X (n + 1) :=
  ∑ i ∈ (cycleSupport (n + 1) z).attach,
    cycleCoeff (n + 1) z i.1 •
      genQ (Y := cycleModelSpace hconnX n z) (n + 1) (topMap (cycleMData hconnX n z) i)

/-- The `(n+1)`-simplex of `X` obtained by taking the `i`-th copy of a top cell along `toX`. -/
theorem toX_topMap {n : ℕ} (D : MData X n x₀) (i : D.Idx) :
    (TopCat.toSSet.map (TopCat.ofHom (toX D))).app (Opposite.op (SimplexCategory.mk (n + 1)))
      ((TopCat.toSSetObjEquivT (TopCat.of (Model D))
        (Opposite.op (SimplexCategory.mk (n + 1)))).symm (topMap D i))
    = (TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op (SimplexCategory.mk (n + 1)))).symm
        (D.simplexMap i) := by
  apply (TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op (SimplexCategory.mk (n + 1)))).injective
  rw [Work.StemsB.toSSetObjEquiv_map']
  simp only [Equiv.apply_symm_apply]
  ext x
  rfl

/-- The chain map of the model sends the generator of a copy of a top cell to the generator of the
corresponding simplex of `X`. -/
theorem chainMap_genQ_topMap {n : ℕ} (D : MData X n x₀) (i : D.Idx) :
    (Work.Cohomology.chainMap ℚ (TopCat.of (Model D)) (TopCat.of X)
      (TopCat.ofHom (toX D))).f (n + 1) (genQ (Y := Model D) (n + 1) (topMap D i))
    = genQ (Y := X) (n + 1) (D.simplexMap i) := by
  show (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (toX D)))
      (ModuleCat.of ℚ ℚ)).f (n + 1)
      (Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of (Model D)))
        ((TopCat.toSSetObjEquivT (TopCat.of (Model D))
          (Opposite.op (SimplexCategory.mk (n + 1)))).symm (topMap D i)))
    = Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of X))
        ((TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op (SimplexCategory.mk (n + 1)))).symm
          (D.simplexMap i))
  rw [Work.StemsB.genElt_chainComplexMapQ]
  rw [toX_topMap]

/-- **The chain of the model of `z` maps to `z`** under the chain map induced by the projection of
the model to `X`. -/
theorem cycleChain_map (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀)) (n : ℕ)
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X (n + 1)) :
    (Work.Cohomology.chainMap ℚ (TopCat.of (cycleModelSpace hconnX n z)) (TopCat.of X)
      (TopCat.ofHom (cycleModelToX hconnX n z))).f (n + 1) (cycleChain hconnX n z) = z := by
  have hz := Work.StemsB.chain_eq_sum_genQ (TopCat.toSSet.obj (TopCat.of X)) (n + 1) z
  have step1 : (Work.Cohomology.chainMap ℚ (TopCat.of (cycleModelSpace hconnX n z)) (TopCat.of X)
        (TopCat.ofHom (cycleModelToX hconnX n z))).f (n + 1) (cycleChain hconnX n z)
      = ∑ i ∈ (cycleSupport (n + 1) z).attach, (cycleCoeff (n + 1) z i.1) •
          genQ (Y := X) (n + 1) ((cycleMData hconnX n z).simplexMap i) := by
    rw [cycleChain, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (cycleModelToX hconnX n z) = toX (cycleMData hconnX n z) from rfl]
    simp only [cycleModelSpace]
    rw [map_smul]
    exact congrArg (fun v => (cycleCoeff (n + 1) z i.1) • v)
      (chainMap_genQ_topMap (cycleMData hconnX n z) i)
  have step2 : (∑ i ∈ (cycleSupport (n + 1) z).attach, (cycleCoeff (n + 1) z i.1) •
          genQ (Y := X) (n + 1) ((cycleMData hconnX n z).simplexMap i))
      = ∑ s ∈ (cycleSupport (n + 1) z), (cycleCoeff (n + 1) z s) •
          Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of X)) s := by
    rw [show (∑ i ∈ (cycleSupport (n + 1) z).attach, (cycleCoeff (n + 1) z i.1) •
          genQ (Y := X) (n + 1) ((cycleMData hconnX n z).simplexMap i))
        = ∑ i ∈ (cycleSupport (n + 1) z).attach, (cycleCoeff (n + 1) z i.1) •
          genQ (Y := X) (n + 1)
            ((TopCat.toSSetObjEquivT (TopCat.of X)
              (Opposite.op (SimplexCategory.mk (n + 1)))) i.1)
        from Finset.sum_congr rfl (fun i _ => rfl)]
    rw [Finset.sum_attach (cycleSupport (n + 1) z)
      (fun s => (cycleCoeff (n + 1) z s) • genQ (Y := X) (n + 1)
        ((TopCat.toSSetObjEquivT (TopCat.of X)
          (Opposite.op (SimplexCategory.mk (n + 1)))) s))]
    simp only [genQ, Equiv.symm_apply_apply]
  rw [step1, step2]
  exact hz.symm

/-- **The key face relation of the model**: two `p`-th faces of copies of top cells whose
corresponding simplices of `X` agree are the same map into the model. -/
theorem face_topMap_eq {n : ℕ} (D : MData X n x₀) {i j : D.Idx} {p q : Fin (n + 2)}
    (h : (D.simplexMap i).comp (facept (n + 1) p) = (D.simplexMap j).comp (facept (n + 1) q)) :
    (topMap D i).comp (facept (n + 1) p) = (topMap D j).comp (facept (n + 1) q) := by
  apply ContinuousMap.ext
  intro x
  exact Quotient.sound (Relation.EqvGen.rel _ _
    (Or.inl ⟨i, j, p, q, x, rfl, rfl, h⟩))

section ChainBoundary

/-- The expansion of the boundary of the model chain as a sum over the pairs consisting of a top cell
and a face index. -/
theorem cycleChain_d_expand (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀)) (n : ℕ)
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X (n + 1)) :
    (Work.Cohomology.singularChains ℚ
        (TopCat.of (cycleModelSpace hconnX n z))).d (n + 1) n (cycleChain hconnX n z)
      = ∑ ip ∈ (cycleSupport (n + 1) z).attach.product (Finset.univ : Finset (Fin (n + 2))),
          ((cycleCoeff (n + 1) z ip.1.1) * ((-1 : ℚ) ^ (ip.2 : ℕ))) •
            genQ (Y := cycleModelSpace hconnX n z) n
              (Work.EmbeddedSpheres.Hurewicz.face ip.2
                (topMap (cycleMData hconnX n z) ip.1)) := by
  have hA : (Work.Cohomology.singularChains ℚ
        (TopCat.of (cycleModelSpace hconnX n z))).d (n + 1) n (cycleChain hconnX n z)
      = ∑ i ∈ (cycleSupport (n + 1) z).attach,
          ∑ p ∈ (Finset.univ : Finset (Fin (n + 2))),
            ((cycleCoeff (n + 1) z i.1) * ((-1 : ℚ) ^ (p : ℕ))) •
              genQ (Y := cycleModelSpace hconnX n z) n
                (Work.EmbeddedSpheres.Hurewicz.face p (topMap (cycleMData hconnX n z) i)) := by
    rw [cycleChain, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
    rw [show (Work.Cohomology.singularChains ℚ
          (TopCat.of (cycleModelSpace hconnX n z))).d (n + 1) n
          (genQ (Y := cycleModelSpace hconnX n z) (n + 1) (topMap (cycleMData hconnX n z) i))
        = ∑ p : Fin (n + 2), ((-1 : ℚ) ^ (p : ℕ)) •
            genQ (Y := cycleModelSpace hconnX n z) n
              (Work.EmbeddedSpheres.Hurewicz.face p (topMap (cycleMData hconnX n z) i)) from
        d_genQ (Y := cycleModelSpace hconnX n z) n (topMap (cycleMData hconnX n z) i)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [smul_smul]
  have hB : (∑ i ∈ (cycleSupport (n + 1) z).attach,
          ∑ p ∈ (Finset.univ : Finset (Fin (n + 2))),
            ((cycleCoeff (n + 1) z i.1) * ((-1 : ℚ) ^ (p : ℕ))) •
              genQ (Y := cycleModelSpace hconnX n z) n
                (Work.EmbeddedSpheres.Hurewicz.face p (topMap (cycleMData hconnX n z) i)))
      = ∑ ip ∈ (cycleSupport (n + 1) z).attach.product (Finset.univ : Finset (Fin (n + 2))),
          ((cycleCoeff (n + 1) z ip.1.1) * ((-1 : ℚ) ^ (ip.2 : ℕ))) •
            genQ (Y := cycleModelSpace hconnX n z) n
              (Work.EmbeddedSpheres.Hurewicz.face ip.2
                (topMap (cycleMData hconnX n z) ip.1)) := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
  rw [hA, hB]

end ChainBoundary

/-! ## The `1`-skeleton of the model

The `1`-skeleton is the set of points of the model represented by a point of `Raw` that lies in a
cell of dimension `≤ 1`: for a point of a copy of `Δ^{n+2}` this means that at most two of its
barycentric coordinates are non-zero, and for a point of an arc it is automatic. -/

/-- A point of `Raw` lies in a cell of dimension `≤ 1`. -/
def isLowDim {n : ℕ} (D : MData X n x₀) (y : Raw D) : Prop :=
  match y with
  | Sum.inl p => (Finset.univ.filter (fun k : Fin (n + 2) => p.2 k ≠ 0)).card ≤ 2
  | Sum.inr _ => True

/-- **The `1`-skeleton of the model.** -/
def skeleton {n : ℕ} (D : MData X n x₀) : Set (Model D) :=
  {z | ∃ y : Raw D, Quotient.mk'' y = z ∧ isLowDim D y}

/-- **The base point of the model**: the common end point of the connecting arcs (the choice of
index is immaterial, the end points of all the arcs are identified). -/
noncomputable def modelBase {n : ℕ} (D : MData X n x₀) [Nonempty D.Idx] : Model D :=
  arcMap D (Classical.choice ‹Nonempty D.Idx›) 1

/-- The base point of the model lies in the `1`-skeleton. -/
theorem mem_skeleton_modelBase {n : ℕ} (D : MData X n x₀) [Nonempty D.Idx] :
    modelBase D ∈ skeleton D :=
  ⟨Sum.inr ⟨Classical.choice ‹Nonempty D.Idx›, 1⟩, rfl, trivial⟩

end

end Work.RatHurewicz
