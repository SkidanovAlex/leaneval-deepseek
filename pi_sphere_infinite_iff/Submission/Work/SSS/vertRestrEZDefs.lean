import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSS.iotaTBdryHorn
import Submission.Work.SSS.vertPathExists
import Submission.Work.KunnethEZ.ezChain_isCycle

/-!
# The Eilenberg–Zilber prism of the `v₁`-vertex restriction of a coherent lift

For a Serre fibration `p : E → B`, a simplex `σ : Δ[s+1] ⟶ Sing B` with underlying point
`b = sigmaVert σ` and `Φ = liftFam p hfib (s+1) b σ h : Δ[s+1] ⊗ Sing F_b ⟶ Sing E` the chosen
coherent lift, this file builds the **prism map**

`vertZ : Δ[1] ⊗ Sing F_b ⟶ Sing (Pullback p γ)`

where `γ` is a path in `B` from `b` to `b' = sigmaVert (δ₀ σ)` whose associated edge simplex is
`vertEdgeSimplex s σ` (so that `γ` is the edge `σ|_{[v₀,v₁]}`); the map is defined as the pair

* `vertZE = (vertEdge s ⊗ₘ 𝟙) ≫ Φ : Δ[1] ⊗ Sing F_b ⟶ Sing E` (the edge of `Δ[s+1]` spread over
  the fibre) and
* `vertZI = fst ≫ vertLiftI : Δ[1] ⊗ Sing F_b ⟶ Sing I` (the projection to the base interval),

grouped through the canonical comparison isomorphism
`sSing (Pullback p γ) ≅ pullback (sSingP p) (sSingP γ)` (whose existence is
`Work.SSS.singPullbackIso_exists`; here the isomorphism is taken as an explicit hypothesis so that
this file is independent of that lemma).

The chain-level Eilenberg–Zilber chain associated with `vertZ`,
`vertW z = (sCCMap vertZ).f (t+1) (ezChain 1 t Δ[1] (Sing F_b) [id] z)`, is the "spread" of the
chain `z` along the edge; its boundary is computed in
`Submission/Work/SSS/vertRestrTransportChains.lean` (`∂ (vertW z) = target (v_* z) - source z`),
which is the input to the transport statement `Work.SSS.vertRestrTransportChains`.
-/

namespace Work.SSS

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

@[simp] lemma vertLiftI_stdId : vertLiftI.app (op ⦋1⦌) idS1 = lambda1 := by
  show (SSet.yonedaEquiv.symm lambda1).app (op ⦋1⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk 1))) = lambda1
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
  simp

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
def vertZE (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    (stdS1 ⊗ sSing (Work.StemsB.fibre p b)) ⟶ sSing E :=
  (vertEdge s ⊗ₘ 𝟙 (sSing (Work.StemsB.fibre p b))) ≫ liftFam p hfib (s+1) b σ h

/-- The `I`-component of the prism map `Δ[1] ⊗ Sing F_b ⟶ Sing I`. -/
def vertZI (p : C(E, B)) (b : B) :
    (stdS1 ⊗ sSing (Work.StemsB.fibre p b)) ⟶ sSing unitInterval :=
  SemiCartesianMonoidalCategory.fst _ _ ≫ vertLiftI

/-- **The edge of `σ` in `Δ[s+1]` is `Sing γ` on the edge simplex**: the compatibility of the two
components of the prism map. -/
theorem vertZcompat (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
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
argument (its existence is `Work.SSS.singPullbackIso_exists`), so that this file does not depend on
that lemma. -/
def vertZ (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap)) :
    (stdS1 ⊗ sSing (Work.StemsB.fibre p b)) ⟶
      sSing (Work.StemsB.Pullback p γ.toContinuousMap) :=
  pullback.lift (vertZE p hfib s b σ h) (vertZI p b)
    (vertZcompat p hfib s b σ h γ hγ) ≫ e.inv

/-- The `E`-projection of the prism map is its `E`-component. -/
lemma vertZ_fst (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap))
    (he : e.hom ≫ pullback.fst (sSingP p) (sSingP γ.toContinuousMap)
      = sSingP (Work.StemsB.pullbackFst p γ.toContinuousMap)) :
    vertZ p hfib s b σ h γ hγ e ≫ sSingP (Work.StemsB.pullbackFst p γ.toContinuousMap)
      = vertZE p hfib s b σ h := by
  show (pullback.lift (vertZE p hfib s b σ h) (vertZI p b)
      (vertZcompat p hfib s b σ h γ hγ) ≫ e.inv)
      ≫ sSingP (Work.StemsB.pullbackFst p γ.toContinuousMap) = vertZE p hfib s b σ h
  rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, pullback.lift_fst]

/-- The `I`-projection of the prism map is its `I`-component. -/
lemma vertZ_snd (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap))
    (he : e.hom ≫ pullback.snd (sSingP p) (sSingP γ.toContinuousMap)
      = sSingP (Work.StemsB.pullbackSnd p γ.toContinuousMap)) :
    vertZ p hfib s b σ h γ hγ e ≫ sSingP (Work.StemsB.pullbackSnd p γ.toContinuousMap)
      = vertZI p b := by
  show (pullback.lift (vertZE p hfib s b σ h) (vertZI p b)
      (vertZcompat p hfib s b σ h γ hγ) ≫ e.inv)
      ≫ sSingP (Work.StemsB.pullbackSnd p γ.toContinuousMap) = vertZI p b
  rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, pullback.lift_snd]

/-- The `E`-projection of the value of the prism map on a simplex. -/
lemma vertZ_proj_fst (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap))
    (he : e.hom ≫ pullback.fst (sSingP p) (sSingP γ.toContinuousMap)
      = sSingP (Work.StemsB.pullbackFst p γ.toContinuousMap))
    (n : SimplexCategoryᵒᵖ)
    (x : (stdS1 ⊗ sSing (Work.StemsB.fibre p b)).obj n) :
    (sSingP (Work.StemsB.pullbackFst p γ.toContinuousMap)).app n
        ((vertZ p hfib s b σ h γ hγ e).app n x)
      = (vertZE p hfib s b σ h).app n x := by
  have hh := congrArg (fun (φ : (stdS1 ⊗ sSing (Work.StemsB.fibre p b)) ⟶ sSing E) =>
    φ.app n x) (vertZ_fst p hfib s b σ h γ hγ e he)
  have hh' : (ConcreteCategory.hom
      ((sSingP (Work.StemsB.pullbackFst p γ.toContinuousMap)).app n))
        ((ConcreteCategory.hom ((vertZ p hfib s b σ h γ hγ e).app n)) x)
      = (ConcreteCategory.hom ((vertZE p hfib s b σ h).app n)) x := hh
  exact hh'

/-- The `I`-projection of the value of the prism map on a simplex. -/
lemma vertZ_proj_snd (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap))
    (he : e.hom ≫ pullback.snd (sSingP p) (sSingP γ.toContinuousMap)
      = sSingP (Work.StemsB.pullbackSnd p γ.toContinuousMap))
    (n : SimplexCategoryᵒᵖ)
    (x : (stdS1 ⊗ sSing (Work.StemsB.fibre p b)).obj n) :
    (sSingP (Work.StemsB.pullbackSnd p γ.toContinuousMap)).app n
        ((vertZ p hfib s b σ h γ hγ e).app n x)
      = (vertZI p b).app n x := by
  have hh := congrArg (fun (φ : (stdS1 ⊗ sSing (Work.StemsB.fibre p b)) ⟶
      sSing unitInterval) => φ.app n x) (vertZ_snd p hfib s b σ h γ hγ e he)
  have hh' : (ConcreteCategory.hom
      ((sSingP (Work.StemsB.pullbackSnd p γ.toContinuousMap)).app n))
        ((ConcreteCategory.hom ((vertZ p hfib s b σ h γ hγ e).app n)) x)
      = (ConcreteCategory.hom ((vertZI p b).app n)) x := hh
  exact hh'

/-- The comparison isomorphism is a section, hence its `n`-th component is injective. -/
lemma vertZ_hom_injective (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap))
    (n : SimplexCategoryᵒᵖ) :
    Function.Injective (e.hom.app n) := by
  intro a b hab
  have hcomp : ∀ y, e.inv.app n (e.hom.app n y) = y := by
    intro y
    have h1 : e.inv.app n (e.hom.app n y) = ((e.hom ≫ e.inv).app n) y := rfl
    rw [h1, Iso.hom_inv_id, NatTrans.id_app]
    rfl
  have hh := congrArg (e.inv.app n) hab
  rw [hcomp a, hcomp b] at hh
  exact hh

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
        ≫ TopCat.ofHom (Work.StemsB.pullbackFst p γ.toContinuousMap)
      : TopCat.of (Work.StemsB.fibre p b₀) ⟶ TopCat.of E)
      = TopCat.ofHom (Work.StemsB.fibreIncl p b₀) := by
  ext e
  rfl

/-- The source inclusion of the pullback along a path, followed by the second projection, is the
constant map at `0`. -/
lemma inclSource_comp_pullbackSnd (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (TopCat.ofHom (inclSource p γ)
        ≫ TopCat.ofHom (Work.StemsB.pullbackSnd p γ.toContinuousMap)
      : TopCat.of (Work.StemsB.fibre p b₀) ⟶ TopCat.of unitInterval)
      = TopCat.const (0 : unitInterval) := by
  ext e
  rfl

/-- The target inclusion of the pullback along a path, followed by the first projection, is the
inclusion of the fibre. -/
lemma inclTarget_comp_pullbackFst (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (TopCat.ofHom (inclTarget p γ)
        ≫ TopCat.ofHom (Work.StemsB.pullbackFst p γ.toContinuousMap)
      : TopCat.of (Work.StemsB.fibre p b₁) ⟶ TopCat.of E)
      = TopCat.ofHom (Work.StemsB.fibreIncl p b₁) := by
  ext e
  rfl

/-- The target inclusion of the pullback along a path, followed by the second projection, is the
constant map at `1`. -/
lemma inclTarget_comp_pullbackSnd (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (TopCat.ofHom (inclTarget p γ)
        ≫ TopCat.ofHom (Work.StemsB.pullbackSnd p γ.toContinuousMap)
      : TopCat.of (Work.StemsB.fibre p b₁) ⟶ TopCat.of unitInterval)
      = TopCat.const (1 : unitInterval) := by
  ext e
  rfl

/-- The vertex inclusion `σ ↦ (const_ν, σ)` of the fibre into `Δ[1] ⊗ Sing F_b`. -/
def vertInclS1 (p : C(E, B)) (b : B) (ν : stdS1 _⦋0⦌) :
    sSing (Work.StemsB.fibre p b) ⟶ stdS1 ⊗ sSing (Work.StemsB.fibre p b) :=
  CartesianMonoidalCategory.lift (SSet.const ν) (𝟙 _)

/-- **The prism map with the tensor factors interchanged.**  The Eilenberg–Zilber chain of a chain
of the fibre in the *first* factor is `ezChain t 0` (degree `t + 0 = t`), so this is the order in
which the chain-level boundary computation is carried out. -/
def vertZ' (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap)) :
    (sSing (Work.StemsB.fibre p b) ⊗ stdS1) ⟶
      sSing (Work.StemsB.Pullback p γ.toContinuousMap) :=
  (β_ (sSing (Work.StemsB.fibre p b)) stdS1).hom ≫ vertZ p hfib s b σ h γ hγ e

/-- **The vertex restriction of the prism map.**  Inserting the vertex `ν` of `Δ[1]` in the first
factor gives a map `Sing F_b ⟶ Sing (Pullback p γ)`. -/
def vertZvtx (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap))
    (ν : stdS1 _⦋0⦌) :
    sSing (Work.StemsB.fibre p b) ⟶ sSing (Work.StemsB.Pullback p γ.toContinuousMap) :=
  vertInclS1 p b ν ≫ vertZ p hfib s b σ h γ hγ e

/-- The vertex restriction of the prism map is the insertion of the vertex followed by the prism
map with interchanged factors. -/
lemma vertZvtx_eq_braiding (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap))
    (ν : stdS1 _⦋0⦌) :
    CartesianMonoidalCategory.lift (𝟙 (sSing (Work.StemsB.fibre p b))) (SSet.const ν)
        ≫ vertZ' p hfib s b σ h γ hγ e
      = vertZvtx p hfib s b σ h γ hγ e ν := by
  rw [vertZ', vertZvtx, vertInclS1, ← Category.assoc,
    CategoryTheory.CartesianMonoidalCategory.lift_braiding_hom]

/-- The prism chain of a `t`-chain `z` of the fibre `F_b`, in the pullback along `γ`. -/
def vertW (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (e : sSing (Work.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap))
    (z : (fibreCC p b).X t) :
    (Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).X (t+1) :=
  castElem (Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap))
    (by omega : 1 + t = t + 1)
    ((sCCMap (vertZ p hfib s b σ h γ hγ e)).f (1 + t)
      (Work.KunnethEZ.ezChain 1 t stdS1 (sSing (Work.StemsB.fibre p b))
        (Work.KunnethEZ.genC stdS1 idS1) z))

end

end Work.SSS
