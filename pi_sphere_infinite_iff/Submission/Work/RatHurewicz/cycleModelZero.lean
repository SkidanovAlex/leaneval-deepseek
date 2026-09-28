import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.RatHurewicz.cycleModelDefs
import Submission.Work.RatHurewicz.cycleModelPathConnected
import Submission.Work.RatHurewicz.finiteRangeOfFg
import Submission.Work.StemsB.PiMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option synthInstance.maxHeartbeats 400000


local instance instSubsingletonStdSimplexZeroCM : Subsingleton ↑(stdSimplex ℝ (Fin (0 + 1))) := by
  haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b => Fin.ext (by omega)⟩
  infer_instance

/-!
# The model of a `0`-cycle

A `0`-chain `z` on `X` is always a cycle.  To lift it with a cycle we replace every point of its
support by the constant `1`-simplex there: the resulting `1`-chain `constChain z` is a cycle, and we
take the model of that `1`-chain (whose top cells are constant `1`-simplices, so that everything
above dimension one is drawn from them).  The `0`-cycle lifting `z` is the sum of the generators at
the vertices `0` of the copies of `Δ¹`, one for each simplex in the support of `z`; its image under
the chain map of `cycleModelToX hconnX 0 (constChain z)` is `z`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology Simplicial unitInterval

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The constant `n`-simplex at a point of `X`. -/
def constSimp (n : ℕ) (p : X) : Work.EmbeddedSpheres.Hurewicz.Simp (TopCat.of X) n :=
  ⟨ContinuousMap.const _ p, continuous_const⟩

/-- The continuous map attached to a `0`-simplex of the singular simplicial set. -/
noncomputable def zeroSimplexMap
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0))) :
    Work.EmbeddedSpheres.Hurewicz.Simp (TopCat.of X) 0 :=
  (TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op (SimplexCategory.mk 0))) s

/-- The point of `X` underlying a `0`-simplex. -/
def zeroSimplexPoint
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0))) : X :=
  zeroSimplexMap s (stdSimplex.vertex (0 : Fin 1))

/-- A `0`-simplex is the constant simplex at its point. -/
theorem zeroSimplexMap_eq_const
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0))) :
    zeroSimplexMap s = constSimp 0 (zeroSimplexPoint s) := by
  apply ContinuousMap.ext
  intro y
  exact congrArg (zeroSimplexMap s) (Subsingleton.elim y (stdSimplex.vertex (0 : Fin 1)))

/-- The `1`-chain obtained by replacing each simplex of the support of `z` by the constant
`1`-simplex at its point. -/
noncomputable def constChain (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X 0) :
    (Work.Cohomology.singularChains ℚ (TopCat.of X)).X 1 :=
  ∑ s ∈ (cycleSupport 0 z).attach,
    (cycleCoeff 0 z s.1) • genQ (Y := X) 1 (constSimp 1 (zeroSimplexPoint s.1))

/-- **The constant `1`-chain of a `0`-chain is a cycle.** -/
theorem constChain_boundary (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X 0) :
    (Work.Cohomology.singularChains ℚ (TopCat.of X)).d 1 0 (constChain z) = 0 := by
  rw [constChain, map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [map_smul]
  rw [show (Work.Cohomology.singularChains ℚ (TopCat.of X)).d 1 0
        (genQ (Y := X) 1 (constSimp 1 (zeroSimplexPoint s.1)))
      = ∑ i : Fin 2, ((-1 : ℚ) ^ (i : ℕ)) •
          genQ (Y := X) 0 (Work.EmbeddedSpheres.Hurewicz.face i
            (constSimp 1 (zeroSimplexPoint s.1))) from
      d_genQ (Y := X) 0 (constSimp 1 (zeroSimplexPoint s.1))]
  have hface : ∀ i : Fin 2, Work.EmbeddedSpheres.Hurewicz.face i
      (constSimp 1 (zeroSimplexPoint s.1)) = constSimp 0 (zeroSimplexPoint s.1) := by
    intro i
    apply ContinuousMap.ext
    intro y
    rfl
  rw [Fin.sum_univ_two, hface 0, hface 1]
  simp

/-- The simplex data of the model of `constChain z`. -/
noncomputable def constMData (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X 0) : MData X 0 x₀ where
  Idx := {s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)) //
    s ∈ cycleSupport 0 z}
  finIdx := inferInstance
  simplexMap s := constSimp 1 (zeroSimplexPoint s.1)
  arcPath s := pathToBase hconnX (zeroSimplexPoint s.1)
  arc_zero s := (pathToBase hconnX _).source
  arc_one s := (pathToBase hconnX _).target

/-- The `0`-chain of the model of `constChain z`: the sum of the generators at the vertices `0` of
the copies. -/
noncomputable def vertexChain (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X 0) :
    (Work.Cohomology.singularChains ℚ (TopCat.of (Model (constMData hconnX z)))).X 0 :=
  ∑ s ∈ (cycleSupport 0 z).attach,
    (cycleCoeff 0 z s.1) • genQ (Y := Model (constMData hconnX z)) 0
      (constSimp 0 (Quotient.mk'' (Sum.inl ⟨⟨s.1, s.2⟩, stdSimplex.vertex (0 : Fin 2)⟩ :
        Raw (constMData hconnX z))))

/-- The generator at a vertex of the model of `constChain z` maps to the corresponding `0`-simplex
of `X`. -/
theorem chainMap_genQ_vertex (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X 0)
    (s : {s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)) //
      s ∈ cycleSupport 0 z}) :
    (Work.Cohomology.chainMap ℚ (TopCat.of (Model (constMData hconnX z))) (TopCat.of X)
      (TopCat.ofHom (toX (constMData hconnX z)))).f 0
        (genQ (Y := Model (constMData hconnX z)) 0
          (constSimp 0 (Quotient.mk'' (Sum.inl ⟨s, stdSimplex.vertex (0 : Fin 2)⟩ :
            Raw (constMData hconnX z)))))
      = genQ (Y := X) 0 (zeroSimplexMap s.1) := by
  show (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (toX (constMData hconnX z))))
      (ModuleCat.of ℚ ℚ)).f 0
      (Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of (Model (constMData hconnX z))))
        ((TopCat.toSSetObjEquivT (TopCat.of (Model (constMData hconnX z)))
          (Opposite.op (SimplexCategory.mk 0))).symm
            (constSimp 0 (Quotient.mk'' (Sum.inl ⟨s, stdSimplex.vertex (0 : Fin 2)⟩ :
              Raw (constMData hconnX z))))))
    = Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of X))
        ((TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op (SimplexCategory.mk 0))).symm
          (zeroSimplexMap s.1))
  rw [Work.StemsB.genElt_chainComplexMapQ]
  congr 1
  apply (TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op (SimplexCategory.mk 0))).injective
  rw [Work.StemsB.toSSetObjEquiv_map']
  simp only [Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro y
  show toX (constMData hconnX z)
      (Quotient.mk'' (Sum.inl ⟨s, stdSimplex.vertex (0 : Fin 2)⟩ : Raw (constMData hconnX z)))
    = (TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op (SimplexCategory.mk 0))) s.1 y
  show toXFun (constMData hconnX z)
      (Sum.inl ⟨s, stdSimplex.vertex (0 : Fin 2)⟩ : Raw (constMData hconnX z)) = _
  show (constMData hconnX z).simplexMap s (stdSimplex.vertex (0 : Fin 2)) = _
  show constSimp 1 (zeroSimplexPoint s.1) (stdSimplex.vertex (0 : Fin 2)) = _
  show zeroSimplexPoint s.1 = _
  exact congrArg ((TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op (SimplexCategory.mk 0))) s.1)
    (Subsingleton.elim (stdSimplex.vertex (0 : Fin 1)) y)

/-- The base point of the model of `constChain z` maps to the base point of `X`. -/
theorem toX_constMData_modelBase (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X 0)
    [Nonempty (constMData hconnX z).Idx] :
    toX (constMData hconnX z) (modelBase (constMData hconnX z)) = x₀ := by
  show toXFun (constMData hconnX z)
    (Sum.inr ⟨(Classical.choice (inferInstance : Nonempty (constMData hconnX z).Idx)),
      (1 : unitInterval)⟩) = x₀
  exact (constMData hconnX z).arc_one _

/-- **The model of a `0`-chain**: a path connected space with a `0`-cycle lifting `z`, whose
`π₁`-image in `π₁(X)` is finite as soon as `π₁` of the model is finitely generated. -/
theorem exists_model_zero (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X 0)
    [Nonempty (constMData hconnX z).Idx]
    (hfg : Group.FG (HomotopyGroup (Fin 1) (Model (constMData hconnX z))
      (modelBase (constMData hconnX z))))
    (hcomm : ∀ a b : HomotopyGroup (Fin 1) X x₀, a * b = b * a)
    (htors : ∀ α : HomotopyGroup (Fin 1) X x₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (y₀ : Y) (φ : C(Y, X))
      (w : (Work.Cohomology.singularChains ℚ (TopCat.of Y)).X 0),
      Subsingleton (HomotopyGroup (Fin 0) Y y₀) ∧
      (Work.Cohomology.singularChains ℚ (TopCat.of Y)).d 0 (0 - 1) w = 0 ∧
      (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of X) (TopCat.ofHom φ)).f 0 w = z ∧
      (Set.range (Work.StemsB.πmap φ 0 y₀)).Finite := by
  refine ⟨Model (constMData hconnX z), inferInstance, modelBase (constMData hconnX z),
    toX (constMData hconnX z), vertexChain hconnX z, ?_, ?_, ?_, ?_⟩
  · exact subsingleton_pi0_model (constMData hconnX z)
  · rw [HomologicalComplex.shape (Work.Cohomology.singularChains ℚ
      (TopCat.of (Model (constMData hconnX z)))) 0 0 (by decide)]
    simp
  · rw [vertexChain, map_sum]
    simp only [map_smul, chainMap_genQ_vertex hconnX z]
    refine Eq.trans ?_ (Work.StemsB.chain_eq_sum_genQ
      (TopCat.toSSet.obj (TopCat.of X)) 0 z).symm
    rw [Finset.sum_attach (cycleSupport 0 z)
      (fun s => (cycleCoeff 0 z s) • genQ (Y := X) 0 (zeroSimplexMap s))]
    exact Finset.sum_congr rfl (fun s _ => by
      first
        | rfl
        | (simp only [genQ, zeroSimplexMap, Equiv.symm_apply_apply]; rfl)
        | (simp only [genQ, zeroSimplexMap, Equiv.symm_apply_apply, cycleCoeff]; rfl))
  · have hbase := toX_constMData_modelBase hconnX z
    refine finiteRangeOfFg hfg ?_ ?_
      (Work.StemsB.πmap (toX (constMData hconnX z)) 0 (modelBase (constMData hconnX z)))
    · exact hbase.symm ▸ hcomm
    · exact hbase.symm ▸ htors


end

end Work.RatHurewicz
