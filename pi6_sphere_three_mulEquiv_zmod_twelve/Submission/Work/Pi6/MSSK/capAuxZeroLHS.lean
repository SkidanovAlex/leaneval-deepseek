import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.Pi6.MSSK.fibreIncZeroEq
import Submission.Work.Pi6.MSSK.TransportAux
import Submission.Work.Pi6.MSSK.capUnitCast
import Submission.Work.SSSR.iotaStatement_zero_c_one
import Submission.Work.SSSR.serreE1PieceIsoZero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

variable {R : Type} [CommRing R] [Nontrivial R]
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Auxiliary lemmas for the `s = 0` left-hand-side comparison -/

/-- The chain map induced by the vertex identification `vertexIso`. -/
abbrev ca0L_vIsoMap (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) ⟶
      Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))) :=
  Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p σ).hom

/-- The chain map induced by the vertex inclusion `fibreInc`. -/
abbrev ca0L_fibreIncChain (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ)) ⟶
      Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) :=
  Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)

/-- The chain-level transport of the fibre identification along an equality of vertices. -/
abbrev ca0L_sSingTransport (p : C(E, B))
    {τ σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B}
    (h : τ = σ) :
    Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert τ))) ⟶
      Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))) :=
  Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg (fun x => Work.SSSR.sSing
    (Work.SSSR.StemsB.fibre p x)) (congrArg Work.SSSR.sigmaVert h)))

/-- The chain-level transport of `T_σ` along an equality of vertices. -/
abbrev ca0L_pullAlongTransport (p : C(E, B))
    {τ σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B}
    (h : τ = σ) :
    Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) τ) ⟶
      Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) :=
  Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg (fun τ =>
    Work.SSSR.pullAlong (Work.SSSR.sSingP p) τ) h))

/-- Naturality of `vertexIso` in the vertex: transporting along an equality of vertices commutes
with the identification of the vertex piece with the singular simplicial set of the fibre. -/
theorem ca0L_vertexIsoCongr (p : C(E, B))
    {τ σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B}
    (h : τ = σ) :
    (Work.Pi6.MSSK.vertexIso p τ).hom
        ≫ CategoryTheory.eqToHom (congrArg (fun x => Work.SSSR.sSing
            (Work.SSSR.StemsB.fibre p x)) (congrArg Work.SSSR.sigmaVert h))
      = CategoryTheory.eqToHom (congrArg (fun τ =>
          Work.SSSR.pullAlong (Work.SSSR.sSingP p) τ) h)
        ≫ (Work.Pi6.MSSK.vertexIso p σ).hom := by
  subst h
  simp only [Work.Pi6.MSSK.vertexIso, Work.SSSR.pullAlongVertexIsoIso,
    CategoryTheory.Iso.symm_hom, CategoryTheory.eqToHom_refl, Category.id_comp,
    Category.comp_id]

/-- Naturality of `vertexIso` in the vertex, on chain complexes. -/
theorem ca0L_vertexIsoCongr_cmap (p : C(E, B))
    {τ σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B}
    (h : τ = σ) :
    ca0L_vIsoMap (R := R) p τ ≫ ca0L_sSingTransport (R := R) p h
      = ca0L_pullAlongTransport (R := R) p h ≫ ca0L_vIsoMap (R := R) p σ := by
  have hnat := ca0L_vertexIsoCongr p h
  have h2 := congrArg (Work.SSSR.sCCMap R) hnat
  rwa [Work.SSSR.izo_sCCMap_comp, Work.SSSR.izo_sCCMap_comp] at h2

/-- The `triv` trivialisation of the local system `b ↦ H_k(p⁻¹b)` is compatible with the transport
along an equality of base points. -/
lemma ca0L_triv_congr (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀)) (k : ℕ) {b b' : B} (h : b = b')
    (z : (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))).homology k) :
    (Work.SSSR.triv p e₀ hfib hsconn k b).hom.hom z
      = (Work.SSSR.triv p e₀ hfib hsconn k b').hom.hom
          (ModuleCat.Hom.hom ((CategoryTheory.eqToIso (congrArg (fun x => (Work.SSSR.sCC R
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p x))).homology k) h)).hom) z) := by
  subst h
  rfl

/-- The isomorphism of homology groups induced by an equality of base points is the homology of the
associated transport of singular simplicial sets. -/
lemma ca0L_homologyEqToIso_eq (p : C(E, B)) {b b' : B} (h : b = b') (k : ℕ) :
    (CategoryTheory.eqToIso (congrArg (fun x => (Work.SSSR.sCC R (Work.SSSR.sSing
        (Work.SSSR.StemsB.fibre p x))).homology k) h)).hom
      = HomologicalComplex.homologyMap (Work.SSSR.sCCMap R (CategoryTheory.eqToHom
          (congrArg (fun x => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p x)) h))) k := by
  subst h
  rw [show congrArg (fun x => (Work.SSSR.sCC R (Work.SSSR.sSing
        (Work.SSSR.StemsB.fibre p x))).homology k) (rfl : b = b) = rfl from rfl]
  rw [show congrArg (fun x => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p x)) (rfl : b = b)
      = rfl from rfl]
  simp only [CategoryTheory.eqToIso_refl, CategoryTheory.Iso.refl_hom,
    CategoryTheory.eqToHom_refl, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id]

/-- `homologyMap` on the homology class of a cycle. -/
lemma ca0L_homologyMap_homologyπ {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (k : ℕ)
    (x : K.X k) (hx : (ModuleCat.Hom.hom (K.d k ((ComplexShape.down ℕ).next k))) x = 0) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ k))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ K k))
          (K.cyclesMk x ((ComplexShape.down ℕ).next k) rfl hx))
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ L k))
          (HomologicalComplex.cyclesMap φ k (K.cyclesMk x ((ComplexShape.down ℕ).next k) rfl hx)) :=
  Work.SSSR.izo_homologyMap_homologyπ φ k _

/-- `cyclesMap` on the cycle of a `cyclesMk`. -/
lemma ca0L_cyclesMap_cyclesMk {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (k : ℕ)
    (x : K.X k) (hx : (ModuleCat.Hom.hom (K.d k ((ComplexShape.down ℕ).next k))) x = 0) :
    HomologicalComplex.cyclesMap φ k (K.cyclesMk x ((ComplexShape.down ℕ).next k) rfl hx)
      = L.cyclesMk ((ModuleCat.Hom.hom (φ.f k)) x) ((ComplexShape.down ℕ).next k) rfl
          (Work.SSSR.izo_d_map_eq_zero φ x hx) :=
  Work.SSSR.izo_cyclesMap_cyclesMk φ rfl x hx _

/-- `cyclesMk` depends only on the underlying element and not on the cycle proof. -/
lemma ca0L_cyclesMk_congr {K : ChainComplex (ModuleCat R) ℕ} {k : ℕ} {x x' : K.X k}
    (h : x = x') (hx : (ModuleCat.Hom.hom (K.d k ((ComplexShape.down ℕ).next k))) x = 0)
    (hx' : (ModuleCat.Hom.hom (K.d k ((ComplexShape.down ℕ).next k))) x' = 0) :
    K.cyclesMk x ((ComplexShape.down ℕ).next k) rfl hx
      = K.cyclesMk x' ((ComplexShape.down ℕ).next k) rfl hx' := by
  rcases h
  exact congrArg (fun (q : (ModuleCat.Hom.hom (K.d k ((ComplexShape.down ℕ).next k))) x = 0) =>
    (K.cyclesMk x ((ComplexShape.down ℕ).next k) rfl q : K.cycles k)) (Subsingleton.elim hx hx')

/-- `homologyπ` of two `cyclesMk`s with the same underlying element and different cycle proofs
agree. -/
lemma ca0L_homologyπ_cyclesMk_irrel {K : ChainComplex (ModuleCat R) ℕ} (k : ℕ) (x : K.X k)
    (hx hx' : (ModuleCat.Hom.hom (K.d k ((ComplexShape.down ℕ).next k))) x = 0) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K k))
        (K.cyclesMk x ((ComplexShape.down ℕ).next k) rfl hx)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K k))
        (K.cyclesMk x ((ComplexShape.down ℕ).next k) rfl hx') :=
  congrArg (fun p => (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K k))
    (K.cyclesMk x ((ComplexShape.down ℕ).next k) rfl p)) (Subsingleton.elim hx hx')

-- Chain/homology comparison for the `s = 0` base case of the cap/transport induction.
-- `T_σ = pullAlong (sSingP p) σ` is the vertex piece of `Sing E` over a vertex `σ : Δ[0] ⟶ Sing B`;
-- `vertexIso p σ : pullAlong (sSingP p) σ ≅ sSing (fibre p (sigmaVert σ))` is the canonical
-- identification (`Work.Pi6.MSSK.vertexIso`, defined in `Submission/Work/Pi6/MSSK/LastEdge.lean`),
-- and `fibreInc p σ : T_{lastV 0 ≫ σ} ⟶ T_σ` is the vertex inclusion (`Defs.lean`).
-- `hσ : lastV 0 ≫ σ = σ` holds because `lastV 0 = 𝟙`; `hy` says the chain `y` is carried by
-- `fibreInc` to the cap product `thetaTop ⌢ c`; `hZ` is the cycle condition of the chain
-- `vertexIso_*(thetaTop ⌢ c)` in the fibre over `sigmaVert σ`.
-- CLAIM: the class of `y` in the fibre over `sigmaVert (lastV 0 ≫ σ)`, read through `triv`, equals
-- the class of `vertexIso_*(thetaTop ⌢ c)` in the fibre over `sigmaVert σ`, read through `triv`.
-- Useful ingredients: `Work.Pi6.MSSK.triv_eqToIso` (`TransportAux.lean`), `Work.Pi6.MSSK.fibreIncZeroEq`,
-- the naturality square `vertexIso p τ ≫ eqToHom (congrArg _ (congrArg sigmaVert h))
--   = eqToHom (congrArg _ h) ≫ vertexIso p σ` (provable by `subst h; simp [vertexIso,
-- pullAlongVertexIsoIso]`), and `Work.SSSR.izo_homologyMap_homologyπ`, `Work.SSSR.izo_cyclesMap_cyclesMk`.
-- NB: `≫` is scoped notation; use `CategoryTheory.CategoryStruct.comp` in the statement text.
theorem capAuxZeroLHS {R : Type} [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀)) (k : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (hσ : CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ = σ)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0 + k))
    (y : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ))).X k)
    (hcyc : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ))).d k
        ((ComplexShape.down ℕ).next k) y = 0)
    (hy : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f k)) y
      = Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.thetaTop R p σ) k c)
    (hZ : (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
        (Work.SSSR.sigmaVert σ)))).d k ((ComplexShape.down ℕ).next k)
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R
          ((Work.Pi6.MSSK.vertexIso p σ).hom)).f k))
          (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.thetaTop R p σ) k c)) = 0) :
    (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hsconn k
        (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ))).hom)
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.sCCMap R
          ((Work.Pi6.MSSK.vertexIso p
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ)).hom)) k))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.sCC R
            (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
              (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ))) k))
            ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
              (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ))).cyclesMk y
                ((ComplexShape.down ℕ).next k) rfl hcyc)))
      = (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hsconn k
          (Work.SSSR.sigmaVert σ)).hom)
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.sCC R
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))) k))
            ((Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
              (Work.SSSR.sigmaVert σ)))).cyclesMk
                ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R
                  ((Work.Pi6.MSSK.vertexIso p σ).hom)).f k))
                  (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
                    (Work.Pi6.MSSK.thetaTop R p σ) k c))
                ((ComplexShape.down ℕ).next k) rfl hZ)) := by
  have hb : Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ)
      = Work.SSSR.sigmaVert σ := congrArg Work.SSSR.sigmaVert hσ
  have hfibInc : ca0L_fibreIncChain (R := R) p σ
      = ca0L_pullAlongTransport (R := R) p hσ :=
    congrArg (fun (φ : Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ) ⟶
          Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) => Work.SSSR.sCCMap R φ)
      (Work.Pi6.MSSK.fibreIncZeroEq p σ hσ)
  have hnat := ca0L_vertexIsoCongr_cmap (R := R) p hσ
  rw [← hfibInc] at hnat
  set W₀ : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ))).homology k :=
    (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.sCC R
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ))) k))
      ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ))).cyclesMk y
          ((ComplexShape.down ℕ).next k) rfl hcyc) with hW
  rw [ca0L_triv_congr p e₀ hfib hsconn k hb]
  refine congrArg (fun w => (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hsconn k
    (Work.SSSR.sigmaVert σ)).hom) w) ?_
  rw [ca0L_homologyEqToIso_eq p hb k]
  have step3 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (ca0L_sSingTransport (R := R) p hσ) k))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (ca0L_vIsoMap (R := R) p
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ)) k)) W₀)
    = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (ca0L_vIsoMap (R := R) p σ) k))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (ca0L_fibreIncChain (R := R) p σ) k)) W₀) := by
    have h1 := congrArg (fun (φ : Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ)) ⟶ Work.SSSR.sCC R
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))))
        => (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ k)) W₀) hnat
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h1
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h1
  rw [step3]
  rw [hW]
  rw [ca0L_homologyMap_homologyπ (R := R) (ca0L_fibreIncChain (R := R) p σ) k y hcyc]
  rw [ca0L_cyclesMap_cyclesMk (R := R) (ca0L_fibreIncChain (R := R) p σ) k y hcyc]
  have hcaps : (ModuleCat.Hom.hom ((ca0L_fibreIncChain (R := R) p σ).f k)) y
      = Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.thetaTop R p σ) k c := hy
  have hd_caps : (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong
      (Work.SSSR.sSingP p) σ)).d k ((ComplexShape.down ℕ).next k)))
      ((Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop R p σ) k c)) = 0 := by
    rw [← hcaps]
    exact Work.SSSR.izo_d_map_eq_zero (ca0L_fibreIncChain (R := R) p σ) y hcyc
  have hcyc_eq := ca0L_cyclesMk_congr (K := Work.SSSR.sCC R (Work.SSSR.pullAlong
      (Work.SSSR.sSingP p) σ)) hcaps
      (Work.SSSR.izo_d_map_eq_zero (ca0L_fibreIncChain (R := R) p σ) y hcyc) hd_caps
  rw [hcyc_eq]
  rw [ca0L_homologyMap_homologyπ (R := R) (ca0L_vIsoMap (R := R) p σ) k
      (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop R p σ) k c) hd_caps]
  rw [ca0L_cyclesMap_cyclesMk (R := R) (ca0L_vIsoMap (R := R) p σ) k
      (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop R p σ) k c) hd_caps]

end

end Work.Pi6.MSSK
