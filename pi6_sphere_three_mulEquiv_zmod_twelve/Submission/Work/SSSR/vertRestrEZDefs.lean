import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSSR.iotaTBdryHorn
import Submission.Work.SSSR.vertPathExists
import Submission.Work.SSSR.KunnethEZ.ezChain_isCycle
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option autoImplicit false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## The standard `1`-simplex and the interval -/

/-- `Δ[1]`, as a shorthand. -/
abbrev stdS1 : SSet.{0} := (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0})

/-- The fundamental `1`-simplex of `Δ[1]`. -/
abbrev idS1 : stdS1 _⦋1⦌ := stdIdSimplex 1

/-- The `1`-st face of the fundamental `1`-simplex: the vertex `0` of `Δ[1]`. -/
abbrev vtx0S1 : stdS1 _⦋0⦌ := (stdS1).δ 1 idS1

/-- The `0`-th face of the fundamental `1`-simplex: the vertex `1` of `Δ[1]`. -/
abbrev vtx1S1 : stdS1 _⦋0⦌ := (stdS1).δ 0 idS1

/-- The `1`-simplex `Δ[1] ⟶ Sing I` attached to the identity path of the interval. -/
def vertLiftI : stdS1 ⟶ sSing unitInterval :=
  SSet.yonedaEquiv.symm lambda1

lemma objEquiv_delta_idS1 (i : Fin 2) :
    SSet.stdSimplex.objEquiv ((stdS1).δ i idS1) = SimplexCategory.δ i := by
  have h : (stdS1).δ i idS1
      = (SSet.stdSimplex.obj (SimplexCategory.mk 1)).map (SimplexCategory.δ i).op idS1 := rfl
  rw [h, SSet.stdSimplex.map_apply]
  simp [idS1, stdIdSimplex]

lemma obj₀Equiv_delta_idS1 (i : Fin 2) :
    SSet.stdSimplex.obj₀Equiv ((stdS1).δ i idS1) = Fin.succAbove i 0 := by
  rw [SSet.stdSimplex.obj₀Equiv_apply]
  rw [show ((stdS1).δ i idS1) 0 = (SSet.stdSimplex.objEquiv ((stdS1).δ i idS1)).toOrderHom 0
    from rfl]
  rw [objEquiv_delta_idS1]
  rfl

/-- The `0`-simplex of `Sing I` attached to `i.succAbove 0` is the point `i.succAbove 0` of the
interval. -/
lemma toSSetObj₀Equiv_vertLiftI_apply (i : Fin 2) :
    TopCat.toSSetObj₀Equiv (vertLiftI.app (op ⦋0⦌) ((stdS1).δ i idS1))
      = stdSimplexHomeomorphUnitInterval (stdSimplex.vertex (Fin.succAbove i 0 : Fin 2)) := by
  have h1 : vertLiftI.app (op ⦋0⦌) ((stdS1).δ i idS1)
      = (sSing unitInterval).map (SSet.stdSimplex.objEquiv ((stdS1).δ i idS1)).op lambda1 :=
    (SSet.stdSimplex.map_objEquiv_op_apply (X := sSing unitInterval)
      (n := SimplexCategory.mk 1) lambda1 ((stdS1).δ i idS1)).symm
  rw [h1, objEquiv_delta_idS1]
  rw [show (sSing unitInterval).map (SimplexCategory.δ i).op lambda1
      = (sSing unitInterval).δ i lambda1 from rfl]
  rw [TopCat.toSSetObj₀Equiv_eq_T _ (stdSimplex.vertex (0 : Fin 1)), TopCat.toSSetObjEquivT_δ_apply]
  rw [stdSimplex.map_vertex, lambda1_apply]
  rfl

/-- The `0`-th vertex of the interval, as a `0`-simplex of `Sing I`. -/
lemma toSSetObj₀Equiv_vertLiftI_vtx0 :
    TopCat.toSSetObj₀Equiv (vertLiftI.app (op ⦋0⦌) vtx0S1) = 0 := by
  have h := toSSetObj₀Equiv_vertLiftI_apply 1
  rw [show ((stdS1).δ 1 idS1) = vtx0S1 from rfl] at h
  rw [h]
  rw [show (Fin.succAbove (1 : Fin 2) 0 : Fin 2) = 0 from rfl]
  exact stdSimplexHomeomorphUnitInterval_zero

/-- The `1`-st vertex of the interval, as a `0`-simplex of `Sing I`. -/
lemma toSSetObj₀Equiv_vertLiftI_vtx1 :
    TopCat.toSSetObj₀Equiv (vertLiftI.app (op ⦋0⦌) vtx1S1) = 1 := by
  have h := toSSetObj₀Equiv_vertLiftI_apply 0
  rw [show ((stdS1).δ 0 idS1) = vtx1S1 from rfl] at h
  rw [h]
  rw [show (Fin.succAbove (0 : Fin 2) 0 : Fin 2) = 1 from rfl]
  exact stdSimplexHomeomorphUnitInterval_one

/-! ## The prism map -/

/-- The `E`-component of the prism map `Δ[1] ⊗ Sing F_b ⟶ Sing E`. -/
def vertZE (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    (stdS1 ⊗ sSing (Work.SSSR.StemsB.fibre p b)) ⟶ sSing E :=
  (vertEdge s ⊗ₘ 𝟙 (sSing (Work.SSSR.StemsB.fibre p b))) ≫ liftFam p hfib (s+1) b σ h

/-- The `I`-component of the prism map `Δ[1] ⊗ Sing F_b ⟶ Sing I`. -/
def vertZI (p : C(E, B)) (b : B) :
    (stdS1 ⊗ sSing (Work.SSSR.StemsB.fibre p b)) ⟶ sSing unitInterval :=
  SemiCartesianMonoidalCategory.fst _ _ ≫ vertLiftI

/-- **The edge of `σ` in `Δ[s+1]` is `Sing γ` on the edge simplex**: the compatibility of the two
components of the prism map. -/
theorem vertZcompat (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ) :
    vertZE p hfib s b σ h ≫ sSingP p = vertZI p b ≫ sSingP γ.toContinuousMap := by
  have hlam : vertLiftI ≫ sSingP γ.toContinuousMap = vertEdge s ≫ σ := by
    have h1 : SSet.yonedaEquiv (vertLiftI ≫ sSingP γ.toContinuousMap)
        = SSet.yonedaEquiv (vertEdge s ≫ σ) := by
      rw [SSet.yonedaEquiv_comp]
      rw [show SSet.yonedaEquiv vertLiftI = lambda1 from
        Equiv.apply_symm_apply SSet.yonedaEquiv lambda1]
      rw [hγ]
      rfl
    exact Equiv.injective SSet.yonedaEquiv h1
  rw [vertZE, Category.assoc, liftFam_proj, ← Category.assoc,
    CartesianMonoidalCategory.tensorHom_fst, Category.assoc]
  rw [vertZI, Category.assoc, hlam]

/-- **The prism map** `Δ[1] ⊗ Sing F_b ⟶ Sing (Pullback p γ)`.

The comparison isomorphism `e : Sing (Pullback p γ) ≅ Sing E ×_{Sing B} Sing I` is an explicit
argument (its existence is `Work.SSSR.singPullbackIso_exists`), so that this file does not depend on
that lemma. -/
def vertZ (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap)) :
    (stdS1 ⊗ sSing (Work.SSSR.StemsB.fibre p b)) ⟶
      sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) :=
  pullback.lift (vertZE p hfib s b σ h) (vertZI p b)
    (vertZcompat p hfib s b σ h γ hγ) ≫ e.inv

/-! ## The vertex restrictions of the prism map -/

/-- The `(0,1)`-edge of `Δ[s+1]` sends the vertex `0` of `Δ[1]` to the vertex `0` of
`Δ[s+1]`. -/
lemma vertEdge_vtx0 (s : ℕ) : (vertEdge s).app (op ⦋0⦌) vtx0S1 = ssetVertex (s+1) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  have h1 : (vertEdge s).app (op ⦋0⦌) vtx0S1
      = (SSet.stdSimplex.map (vertEdgeHom s)).app (op ⦋0⦌) vtx0S1 := rfl
  rw [h1, obj₀Equiv_stdSimplex_map, obj₀Equiv_delta_idS1]
  rw [show (Fin.succAbove (1 : Fin 2) 0 : Fin 2) = 0 from rfl]
  rw [show ssetVertex (s+1) = (SSet.stdSimplex.obj₀Equiv (n := s+1)).symm 0 from rfl,
    Equiv.apply_symm_apply]
  apply Fin.ext
  rfl

/-- The `(0,1)`-edge of `Δ[s+1]` sends the vertex `1` of `Δ[1]` to the image of the vertex `0`
of `Δ[s]` under the `0`-th coface (i.e. to the vertex `1` of `Δ[s+1]`). -/
lemma vertEdge_vtx1 (s : ℕ) :
    (vertEdge s).app (op ⦋0⦌) vtx1S1
      = (SSet.stdSimplex.δ (n := s) 0).app (op ⦋0⦌) (ssetVertex s) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  have h1 : (vertEdge s).app (op ⦋0⦌) vtx1S1
      = (SSet.stdSimplex.map (vertEdgeHom s)).app (op ⦋0⦌) vtx1S1 := rfl
  have h2 : (SSet.stdSimplex.δ (n := s) 0).app (op ⦋0⦌) (ssetVertex s)
      = (SSet.stdSimplex.map (SimplexCategory.δ (n := s) 0)).app (op ⦋0⦌) (ssetVertex s) := rfl
  rw [h1, h2, obj₀Equiv_stdSimplex_map, obj₀Equiv_stdSimplex_map, obj₀Equiv_delta_idS1]
  rw [show (Fin.succAbove (0 : Fin 2) 0 : Fin 2) = 1 from rfl]
  rw [show ssetVertex s = (SSet.stdSimplex.obj₀Equiv (n := s)).symm 0 from rfl,
    Equiv.apply_symm_apply]
  apply Fin.ext
  rfl

/-- The source inclusion of the pullback along a path, followed by the first projection, is the
inclusion of the fibre. -/
lemma inclSource_comp_pullbackFst (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (TopCat.ofHom (inclSource p γ)
        ≫ TopCat.ofHom (Work.SSSR.StemsB.pullbackFst p γ.toContinuousMap)
      : TopCat.of (Work.SSSR.StemsB.fibre p b₀) ⟶ TopCat.of E)
      = TopCat.ofHom (Work.SSSR.StemsB.fibreIncl p b₀) := by
  ext e
  rfl

/-- The source inclusion of the pullback along a path, followed by the second projection, is the
constant map at `0`. -/
lemma inclSource_comp_pullbackSnd (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (TopCat.ofHom (inclSource p γ)
        ≫ TopCat.ofHom (Work.SSSR.StemsB.pullbackSnd p γ.toContinuousMap)
      : TopCat.of (Work.SSSR.StemsB.fibre p b₀) ⟶ TopCat.of unitInterval)
      = TopCat.const (0 : unitInterval) := by
  ext e
  rfl

/-- The target inclusion of the pullback along a path, followed by the first projection, is the
inclusion of the fibre. -/
lemma inclTarget_comp_pullbackFst (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (TopCat.ofHom (inclTarget p γ)
        ≫ TopCat.ofHom (Work.SSSR.StemsB.pullbackFst p γ.toContinuousMap)
      : TopCat.of (Work.SSSR.StemsB.fibre p b₁) ⟶ TopCat.of E)
      = TopCat.ofHom (Work.SSSR.StemsB.fibreIncl p b₁) := by
  ext e
  rfl

/-- The target inclusion of the pullback along a path, followed by the second projection, is the
constant map at `1`. -/
lemma inclTarget_comp_pullbackSnd (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (TopCat.ofHom (inclTarget p γ)
        ≫ TopCat.ofHom (Work.SSSR.StemsB.pullbackSnd p γ.toContinuousMap)
      : TopCat.of (Work.SSSR.StemsB.fibre p b₁) ⟶ TopCat.of unitInterval)
      = TopCat.const (1 : unitInterval) := by
  ext e
  rfl

/-- The vertex inclusion `σ ↦ (const_ν, σ)` of the fibre into `Δ[1] ⊗ Sing F_b`. -/
def vertInclS1 (p : C(E, B)) (b : B) (ν : stdS1 _⦋0⦌) :
    sSing (Work.SSSR.StemsB.fibre p b) ⟶ stdS1 ⊗ sSing (Work.SSSR.StemsB.fibre p b) :=
  CartesianMonoidalCategory.lift (SSet.const ν) (𝟙 _)

/-- **The prism map with the tensor factors interchanged.**  The Eilenberg–Zilber chain of a chain
of the fibre in the *first* factor is `ezChain R t 0` (degree `t + 0 = t`), so this is the order in
which the chain-level boundary computation is carried out. -/
def vertZ' (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap)) :
    (sSing (Work.SSSR.StemsB.fibre p b) ⊗ stdS1) ⟶
      sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) :=
  (β_ (sSing (Work.SSSR.StemsB.fibre p b)) stdS1).hom ≫ vertZ p hfib s b σ h γ hγ e

/-- **The vertex restriction of the prism map.**  Inserting the vertex `ν` of `Δ[1]` in the first
factor gives a map `Sing F_b ⟶ Sing (Pullback p γ)`. -/
def vertZvtx (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap))
    (ν : stdS1 _⦋0⦌) :
    sSing (Work.SSSR.StemsB.fibre p b) ⟶ sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) :=
  vertInclS1 p b ν ≫ vertZ p hfib s b σ h γ hγ e

/-- The vertex restriction of the prism map is the insertion of the vertex followed by the prism
map with interchanged factors. -/
lemma vertZvtx_eq_braiding (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap))
    (ν : stdS1 _⦋0⦌) :
    CartesianMonoidalCategory.lift (𝟙 (sSing (Work.SSSR.StemsB.fibre p b))) (SSet.const ν)
        ≫ vertZ' p hfib s b σ h γ hγ e
      = vertZvtx p hfib s b σ h γ hγ e ν := by
  rw [vertZ', vertZvtx, vertInclS1, ← Category.assoc,
    CategoryTheory.CartesianMonoidalCategory.lift_braiding_hom]

end

end Work.SSSR
