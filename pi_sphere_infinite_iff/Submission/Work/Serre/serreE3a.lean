import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.E3aDefs
import Submission.Work.Serre.E3aStepDefs
import Submission.Work.Serre.E3aSkDefs
import Submission.Work.Serre.propagateAbsQ
import Submission.Work.Serre.exists_skeletonMap
import Submission.Work.Serre.pathConnectedSpace_attachOneCells
import Submission.Work.Serre.RatTower.fiveLemmaTau2
import Submission.Work.Serre.RatTower.pullbackFstRangeHomeo
import Submission.Work.Serre.RatTower.Attach
import Submission.Work.Serre.SPC.piOne_killStep
import Submission.Work.Serre.ratFibreTransport
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.oneCellStepRelHomologyIso
import Submission.Work.Serre.cellStepRelHomologyIso
import Submission.Work.Serre.Assembly.pullbackSnd_piMapN_bijective
import Submission.Work.Serre.Assembly.pullbackFst_serre
import Submission.Work.Serre.pullbackFst_piMapN_bijective
import Submission.Work.Serre.serreK2Proved
import Submission.Work.Serre.serreE3aStepA
import Submission.Work.Serre.E3aModel
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.CWModel.Kill
import Submission.Work.Serre.simplexBdry_eq_iUnion_coface

set_option synthInstance.maxHeartbeats 400000

/-!
# E3(a): the mapping theorem — `Work.Serre.SerreE3a`

Blueprint `Submission/Work/Drive/SERRE_BLUEPRINT.md` §1; the interface is fixed in
`Submission/Work/Serre/Engine.lean` (never edit):

```lean
def SerreE3a : Prop :=
  ∀ (E B) [TopologicalSpace E] [TopologicalSpace B] (p : C(E,B)) (e₀ : E) (N : ℕ),
    Work.StemsB.IsSerreFibration p → PathConnectedSpace B →
      RatAcyclicBelow (Work.RatHurewicz.homotopyFibre p e₀) N →
      ∀ i, i < N → IsIso (ratHomologyMap p i)
```

## The route (complete)

The proof is assembled in `Submission/Work/Serre/E3aModel.lean`, in two steps.

1. **The mapping path space** (`Work.Serre.serreE3aStepA`, proved in
   `Submission/Work/Serre/serreE3aStepA.lean`).  Replacing `p` by the fibration
   `q : E'' = {x : E × C(I,B) // x.2 0 = p x.1} → B`, `q (e,γ) = γ 1`, whose fibre over `b₀ = p e₀`
   is the homotopy fibre of `p`, reduces the theorem to the *honest-fibre* form
   `Work.Serre.SerreE3aFibreAcyclic`: a Serre fibration over a path-connected base whose fibre over
   `b₀` is rationally acyclic in degrees `≤ N` and rationally connected induces an isomorphism on
   rational homology in degrees `< N`.

2. **The cellular induction** (`Work.Serre.E3aModel.serreE3aFibreAcyclic`).  A model
   `g : Γ → B` with `π_i(g)` bijective for `i ≤ N` is built by attaching cells:

   * the `1`-skeleton (`Work.Serre.E3aSk.Skeleton`, one circle per based loop of `B`) with its
     structure map `Work.Serre.exists_skeletonMap`, then the `2`-cells killing the kernel of
     `π₁(g)` (`Work.Serre.SPC.piOne_killStep`) — this is the stage `Work.Serre.E3aModel.baseState`
     with `π₁` bijective;
   * the generator and killing steps `Work.Serre.CWModel.genStep`/`killStep`, iterated along the
     tower `Work.Serre.E3aModel.towerB` (the `π`-facts of the top stage are
     `Work.Serre.E3aModel.towerB_piMapN_bijective`).

   The comparison `H_i(Γ ×_B E;ℚ) ≅ H_i(Γ;ℚ)` for `i < N` is the invariant
   `Work.Serre.E3aStep.AbsGoodQ q N g`, propagated along the tower by
   `Work.Serre.propagateAbsQ` — the five lemma on the long exact sequences of the pair
   `(Γ' ×_B E, (Γ' ×_B E)|_Γ)`, whose relative term is the cell step
   `Work.Serre.cellStepRelHomologyIso` (cells of dimension `≥ 2`) or
   `Work.Serre.oneCellStepRelHomologyIso` (the `1`-cells of the skeleton), and whose fibre
   hypotheses are transported along paths in `B` by `Work.Serre.isZero_ratH_fibre_of_path`.
   The base case is `Work.Serre.E3aModel.absGoodQ_base`, from the one-point base
   `Work.Serre.E3aModel.absGoodQ_punit`, and the induction is `Work.Serre.E3aModel.towerB_absGoodQ`.

   Finally `H_i(Γ ×_B E;ℚ) ≅ H_i(E;ℚ)` (`Work.Serre.serreK2Proved` applied to the base change
   `Work.Serre.pullbackFst_piMapN_bijective`) and `H_i(Γ;ℚ) ≅ H_i(B;ℚ)` (`serreK2Proved` applied to
   `g`) combine with the pullback square to give `IsIso (ratHomologyMap q i)`.

The lemmas `Work.Serre.sChains`, `Work.Serre.filtrIncl`, `Work.Serre.serreChainMapSSet` and the
standard-simplex computations below belong to an earlier (unused) spelling of the proof and are kept
because `Submission/Work/RatHurewicz/e3aConclusion.lean` and `.../e3aFiltrationK0.lean` refer to
them.
-/



namespace Work.Serre

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

/-! ## The standard simplex and its boundary

`Δⁿ = stdSimplex ℝ (Fin (n+1))`; its boundary is the union of the codimension-one faces
`coface (n-1) i`.  The relative homology `H_*(Δ^{m+1}, ∂Δ^{m+1}) = ℤ[m+1]` (the disc pair
`(D^{m+1}, S^m)`) is piece (e) of the plan; the absolute half is proved below. -/

/-- The **boundary of the standard `(m+1)`-simplex** `Δ^{m+1}`: the union of its codimension-one
faces, each the image of `Work.RatHurewicz.Bridge.coface m i : Δ^m → Δ^{m+1}`. -/
def stdSimplexBdry (m : ℕ) : Set ↥(stdSimplex ℝ (Fin (m + 2))) :=
  ⋃ i : Fin (m + 2), Set.range (Work.RatHurewicz.Bridge.coface m i)

/-- **The absolute half of the simplex-pair computation.**  The standard simplex `Δⁿ` is
contractible (it is convex and nonempty), so its singular homology vanishes in every positive
degree.  Together with `H_0(Δⁿ;ℤ) ≅ ℤ` this is what the long exact sequence of the pair
`(Δⁿ, ∂Δⁿ)` needs on the absolute side. -/
theorem isZero_stdSimplex_homology (n k : ℕ) (hk : 0 < k) :
    IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(stdSimplex ℝ (Fin (n + 1))))).homology k) := by
  have := Convex.contractibleSpace (convex_stdSimplex ℝ (Fin (n + 1)))
    ⟨Pi.single (0 : Fin (n + 1)) (1 : ℝ), single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩
  exact Work.Cohomology.homologyContractible k hk

/-- The boundary `stdSimplexBdry m` of `Δ^{m+1}` defined above (the union of the codimension-one
faces) is the `Work.Serre.simplexBdry (m+1)` of the E0/Serre files; proved in
`Submission/Work/Serre/simplexBdry_eq_iUnion_coface.lean`. -/
theorem stdSimplexBdry_eq_simplexBdry (m : ℕ) :
    stdSimplexBdry m = Work.Serre.simplexBdry (m + 1) :=
  (Work.Serre.simplexBdry_eq_iUnion_coface m).symm

/-! ## The `K`-filtration induction (`E3A_PLAN.md` §11–§13): the chain-level setup

Phrased in the spelling of `SSet.chainComplexFunctor` (`sChains`), which avoids both coercions
flagged in §13: the inclusion of a filtration level into the ambient complex is the image of the
subcomplex inclusion `(serreSubcomplex f p).ι : G.toFunctor ⟶ F` under the chain functor, and the
map induced by `q` is `serreChainMapSSet`.  The translation to `Work.Cohomology.singularChains` /
`ratHomologyMap` is only needed at the very end. -/

/-- The singular chains of `X` in the `SSet.chainComplexFunctor` spelling. -/
noncomputable abbrev sChains (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℚ) ℕ :=
  ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj
    (TopCat.toSSet.obj (TopCat.of X))

/-- The inclusion of the `p`-th level of the Serre filtration of `C_*(X)` along `q` into the ambient
singular chain complex. -/
noncomputable def filtrIncl {X B : Type} [TopologicalSpace X] [TopologicalSpace B] (q : C(X, B))
    (p : ℕ) :
    (Work.StemsB.serreChainFiltration (TopCat.toSSet.map (TopCat.ofHom q)) ℚ).obj p ⟶ sChains X :=
  ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map
    (Work.StemsB.serreSubcomplex (TopCat.toSSet.map (TopCat.ofHom q)) p).ι

/-- The chain map induced by `q` on singular chains. -/
noncomputable def serreChainMapSSet {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) : sChains X ⟶ sChains B :=
  ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map
    (TopCat.toSSet.map (TopCat.ofHom q))

/-- **E3(a), the form stated by the blueprint** (the hypothesis is on the homotopy fibre). -/
theorem serreE3a : Work.Serre.SerreE3a :=
  Work.Serre.E3aModel.serreE3a_of_fibreAcyclic

end Work.Serre
