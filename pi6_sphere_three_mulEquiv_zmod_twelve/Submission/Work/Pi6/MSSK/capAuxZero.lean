import Mathlib
import Submission.Work.Pi6.MSSK.CapAux
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.Pi6.MSSK.CapThetaLift
import Submission.Work.Pi6.MSSK.TransportAux
import Submission.Work.Pi6.MSSK.fibreIncCapThetaLift
import Submission.Work.Pi6.MSSK.mono_fibreInc
import Submission.Work.Pi6.MSSK.capUnitCast
import Submission.Work.Pi6.MSSK.pieceAlongZeroIsoCast
import Submission.Work.Pi6.MSSK.fibreIncZeroEq
import Submission.Work.Pi6.MSSK.capThetaLiftZeroCyc
import Submission.Work.Pi6.MSSK.capAuxZeroLHS
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.ezSimplexZero_chain_class
import Submission.Work.SSSR.pieceAlongZero
import Submission.Work.SSSR.iotaStatement_zero_c_one
import Submission.Work.SSSR.serreE1PieceIsoZero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `capAuxZero`: the base case `s = 0` of the cap/transport induction

This file proves `Work.Pi6.MSSK.capAuxZero`, the `s = 0` instance of the induction statement
`Work.Pi6.MSSK.Aux` of the cap/transport lemma.

At `s = 0` the simplex `σ` is a vertex of the base, `T_σ = Δ[0] ×_{Sing B} Sing E` is the singular
simplicial set of the fibre `p⁻¹σ(v₀)`, the last vertex map `lastV 0` is the identity, and the `E¹`
isomorphism `serreE1PieceIso p hfib 0 k σ` is the identification of `H_k(piece_σ) = H_k(C(T_σ))`
with `H_k(F_{σ(v₀)})` given by `phiAlong`.

The statement says: for a relative cycle `c` of `T_σ`, the cap product `thetaTop ⌢ c` is a cycle
over the last vertex whose class, read in the fibre, is the `E¹`-image of the class of `c` (with
sign `capSign R 0 = 1`).  Its proof is an explicit chain/homology computation; the essential input
is the `s = 0` case "capping with the unit cochain is the identity up to the degree transport
`0 + k = k`" (`capUnitCast`), `thetaTop` being the unit cochain at a vertex
(`thetaTop_zero_eq_unit`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

namespace Work.Pi6.MSSK

noncomputable section

variable {R : Type} [CommRing R] [Nontrivial R]
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `lastV 0` is the identity: `Δ[0]` has a single vertex. -/
theorem lastV_zero : Work.Pi6.MSSK.lastV 0 = 𝟙 (Δ[0] : SSet.{0}) := by
  simp only [Work.Pi6.MSSK.lastV]
  rw [show (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) (Fin.last 0)) =
      𝟙 _ from SimplexCategory.const_eq_id]
  simp

/-- `Δ[0]` is the terminal object of `SSet`: every `0`-simplex of `Δ[0]` is `topS 0`. -/
lemma topS_zero_unique (w : (Δ[0] : SSet.{0}) _⦋0⦌) : w = Work.Pi6.MSSK.topS 0 := by
  simp only [Work.Pi6.MSSK.topS]
  apply SSet.stdSimplex.objEquiv.injective
  rw [SimplexCategory.eq_const_to_zero (SSet.stdSimplex.objEquiv w),
    SimplexCategory.const_eq_id]
  simp only [Equiv.apply_symm_apply]

/-- At a vertex `σ : Δ[0] ⟶ Sing B` the top cochain `thetaTop` is the unit cochain: every
`0`-simplex of `T_σ` lies over the unique `0`-simplex of `Δ[0]`. -/
theorem thetaTop_zero_eq_unit (p : C(E, B)) (σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Pi6.MSSK.thetaTop R p σ =
      Work.Cohomology.unitCochain R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) := by
  apply Work.Cohomology.genEval_ext
  intro w
  rw [Work.Pi6.MSSK.genEval_thetaTop, Work.Cohomology.genEval_unitCochain,
    Work.Pi6.MSSK.thetaVal_eq_one_iff]
  exact topS_zero_unique _

/-- Naturality of `vertexIso` in the vertex: transporting along an equality of vertices commutes
with the identification of the vertex piece with the singular simplicial set of the fibre. -/
theorem vertexIsoCongr (p : C(E, B)) {τ σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B}
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

/-- The chain map induced by the vertex identification `vertexIso p σ`. -/
abbrev vIsoMap (p : C(E, B)) (σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) ⟶
      Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
        (Work.SSSR.sigmaVert σ))) :=
  Work.SSSR.sCCMap R ((Work.Pi6.MSSK.vertexIso p σ).hom)

/-- The chain map induced by the vertex inclusion `fibreInc p σ`. -/
abbrev fibreIncChain (p : C(E, B)) (σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (Work.Pi6.MSSK.lastV 0 ≫ σ))
      ⟶ Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) :=
  Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)

/-- The chain-level transport of the fibre identification along an equality of vertices. -/
abbrev sSingTransport (p : C(E, B)) {τ σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B} (h : τ = σ) :
    Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
        (Work.SSSR.sigmaVert τ))) ⟶
      Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
        (Work.SSSR.sigmaVert σ))) :=
  Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg (fun x => Work.SSSR.sSing
    (Work.SSSR.StemsB.fibre p x)) (congrArg Work.SSSR.sigmaVert h)))

/-- The chain-level transport of `T_σ` along an equality of vertices. -/
abbrev pullAlongTransport (p : C(E, B)) {τ σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B}
    (h : τ = σ) :
    Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) τ) ⟶
      Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) :=
  Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg (fun τ =>
    Work.SSSR.pullAlong (Work.SSSR.sSingP p) τ) h))

/-- The projection `pieceπOf` followed by the canonical identification of the vertex piece with the
chains of `T_σ` is the identity. -/
lemma pieceπ_cokerIso (p : C(E, B)) (σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    (Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ) ≫
      (Work.SSSR.pieceAlongZeroCokerIso (R := R) p σ).hom = 𝟙 _ := by
  have hI : IsIso (CategoryTheory.Limits.cokernel.π
      (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)) :=
    CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ (CategoryTheory.Limits.cokernel.π _)
        (CategoryTheory.Limits.cokernel.condition _))
      (CategoryTheory.Limits.cokernelIsCokernel _)
      (Work.SSSR.sCCMap_ι_eq_zero_of_eq_bot
        (Work.SSSR.bdryAlong_eq_bot_of_zero (Work.SSSR.sSingP p) σ))
  rw [show Work.SSSR.pieceAlongZeroCokerIso p σ
      = (CategoryTheory.asIso (CategoryTheory.Limits.cokernel.π
          (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι))).symm from rfl]
  rw [show Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ
      = (CategoryTheory.asIso (CategoryTheory.Limits.cokernel.π
          (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι))).hom from rfl]
  rw [← Iso.trans_hom, Iso.self_symm_id, Iso.refl_hom]

/-- **The boundary of a relative cycle of `T_σ` at a vertex.**  For a chain `c` of `T_σ` whose
projection to `piece_σ = C(T_σ)/C(∂T_σ)` is a cycle, and with `∂Δ[0] = ∅`, the chain `c` is
itself a cycle. -/
theorem relCycle_d_eq_zero (p : C(E, B)) (σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B) (k : ℕ)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0 + k))
    (hcrel : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (0+k)
        ((ComplexShape.down ℕ).next (0+k))))
      ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
        (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (0+k))) c) = 0) :
    (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (0+k)
      ((ComplexShape.down ℕ).next (0+k)) c = 0 := by
  have hrel : (ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel
      (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).d (0+k)
        ((ComplexShape.down ℕ).next (0+k))))
      ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
        (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (0+k))) c) = 0 := by
    simpa only [Work.SSSR.pieceAlong] using hcrel
  have hcomm := congrArg (fun (g : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0+k) ⟶
      (CategoryTheory.Limits.cokernel (Work.SSSR.sCCMap R
        (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).X ((ComplexShape.down ℕ).next (0+k))) =>
      (ModuleCat.Hom.hom g) c)
    (HomologicalComplex.Hom.comm (CategoryTheory.Limits.cokernel.π
      (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)) (0+k)
      ((ComplexShape.down ℕ).next (0+k)))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  have h1 : (ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
      (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f
        ((ComplexShape.down ℕ).next (0+k))))
      ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (0+k)
        ((ComplexShape.down ℕ).next (0+k)) c) = 0 := by
    rw [← hcomm]
    exact hrel
  have hmor : ∀ x : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X
      ((ComplexShape.down ℕ).next (0+k)),
      (Work.SSSR.pieceAlongZeroCokerIso p σ).hom.f ((ComplexShape.down ℕ).next (0+k))
        ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
          (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f
            ((ComplexShape.down ℕ).next (0+k)))) x) = x := by
    intro x
    have hh := congrArg (fun (g : Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) ⟶
        Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) =>
        g.f ((ComplexShape.down ℕ).next (0+k))) (pieceπ_cokerIso (R := R) p σ)
    have hh2 := congrArg (fun (g : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X
        ((ComplexShape.down ℕ).next (0+k)) ⟶ (Work.SSSR.sCC R
          (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X ((ComplexShape.down ℕ).next (0+k))) =>
        (ModuleCat.Hom.hom g) x) hh
    exact hh2
  have hfinal := hmor ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (0+k)
    ((ComplexShape.down ℕ).next (0+k)) c)
  rw [h1, map_zero] at hfinal
  exact hfinal.symm

/-- The cap product with `thetaTop` at a vertex is the degree transport of `c`. -/
lemma cap_unit_eq_cast_aux (p : C(E, B)) (σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B) (k : ℕ)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0 + k)) :
    Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop R p σ) k c
      = Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ))
          (Nat.zero_add k) c := by
  rw [Work.Pi6.MSSK.thetaTop_zero_eq_unit]
  exact Work.Pi6.MSSK.capUnitCast R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) k c

/-- The cap product with `thetaTop` at a vertex is the degree transport of `c`; hence it is a
cycle when `c` is. -/
lemma cap_theta_cycle (p : C(E, B)) (σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B) (k : ℕ)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0 + k))
    (hc : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (0+k)
      ((ComplexShape.down ℕ).next (0+k)) c = 0) :
    (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d k
      ((ComplexShape.down ℕ).next k)
      (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop R p σ) k c) = 0 := by
  rw [Work.Pi6.MSSK.cap_unit_eq_cast_aux p σ k c]
  exact Work.SSSR.izo_d_castElem (R := R) (K := Work.SSSR.sCC R
      (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) (Nat.zero_add k) rfl c hc

/-- The inverse of the projection `cokernel.π` on elements. -/
lemma cokerIso_apply_cokerπ (p : C(E, B)) (σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B) (j : ℕ)
    (x : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X j) :
    (Work.SSSR.pieceAlongZeroCokerIso p σ).hom.f j
      ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
        (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f j)) x) = x := by
  have hh := congrArg (fun (g : Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) ⟶
      Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) => g.f j)
    (pieceπ_cokerIso (R := R) p σ)
  have hh2 := congrArg (fun (g : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X j ⟶
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X j) =>
      (ModuleCat.Hom.hom g) x) hh
  exact hh2

/-- `pieceAlongZeroIso` on the class of the projection of `c`, in the `cokernel.π` spelling of the
projection. -/
lemma pieceAlongZeroIsoCast_coker (p : C(E, B))
    (σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B) (k : ℕ)
    (x : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0 + k)) :
    (Work.SSSR.pieceAlongZeroIso p σ).hom.f k
        (Work.SSSR.castElem (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ) (Nat.zero_add k)
          ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
            (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (0 + k))) x))
      = (ModuleCat.Hom.hom ((vIsoMap (R := R) p σ).f k))
          (Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ))
            (Nat.zero_add k) x) := by
  rw [Work.Pi6.MSSK.pieceAlongZeroIso_fac (R := R) p σ k]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← Work.SSSR.izo_castElem_map (R := R)
        (φ := (Work.SSSR.pieceAlongZeroCokerIso (R := R) p σ).hom)
        (i := 0 + k) (j := k) (h := Nat.zero_add k)
        ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
          (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (0 + k))) x)]
  rw [cokerIso_apply_cokerπ (R := R) p σ (0 + k) x]
  simp only [vIsoMap, Work.Pi6.MSSK.vertexIso]
  rfl

/-- **Right-hand side computation.**  The `E¹` isomorphism `serreE1PieceIso p hfib 0 k σ` at a
vertex sends the class of the projection of `c` to the class of `vIsoMap (thetaTop ⌢ c)`. -/
theorem capAuxZero_RHS (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀)) (k : ℕ)
    (σ : (Δ[0] : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0 + k))
    (hcrel : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (0+k)
        ((ComplexShape.down ℕ).next (0+k))))
      ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
        (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (0+k))) c) = 0)
    (hZ : (Work.SSSR.Cohomology.singularChains R (TopCat.of (Work.SSSR.StemsB.fibre p
        (Work.SSSR.sigmaVert σ)))).d k ((ComplexShape.down ℕ).next k)
        ((ModuleCat.Hom.hom ((vIsoMap (R := R) p σ).f k))
          (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.thetaTop R p σ) k c)) = 0) :
    (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom)
        ((ModuleCat.Hom.hom ((Work.SSSR.serreE1PieceIso p hfib 0 k σ).hom))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.pieceAlong R
            (Work.SSSR.sSingP p) σ) (0 + k)))
            ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk
              ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
                (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (0+k))) c)
              ((ComplexShape.down ℕ).next (0+k)) rfl hcrel)))
      = (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hsconn k
          (Work.SSSR.sigmaVert σ)).hom)
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.Cohomology.singularChains R
            (TopCat.of (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))) k))
            ((Work.SSSR.Cohomology.singularChains R (TopCat.of (Work.SSSR.StemsB.fibre p
              (Work.SSSR.sigmaVert σ)))).cyclesMk
                ((ModuleCat.Hom.hom ((vIsoMap (R := R) p σ).f k))
                  (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
                    (Work.Pi6.MSSK.thetaTop R p σ) k c))
                ((ComplexShape.down ℕ).next k) rfl hZ)) := by
  refine congrArg (fun w => (ModuleCat.Hom.hom
    (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom) w) ?_
  rw [Work.SSSR.izo_serreE1PieceIso_zero_eq p hfib (Work.SSSR.sigmaVert σ) σ rfl k]
  simp only [CategoryTheory.Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact Work.SSSR.izo_homology_apply (Work.SSSR.pieceAlongZeroIso p σ).hom (Nat.zero_add k)
      ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
        (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (0 + k))) c)
      hcrel
      ((ModuleCat.Hom.hom ((vIsoMap (R := R) p σ).f k))
        (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.thetaTop R p σ) k c))
      hZ
      (by
        rw [pieceAlongZeroIsoCast_coker (R := R) p σ k c]
        rw [← Work.Pi6.MSSK.cap_unit_eq_cast_aux p σ k c])

/-- **The base case `s = 0` of the cap/transport induction.**  At a vertex `σ : Δ[0] ⟶ Sing B`, for
every relative cycle `c` of `T_σ` there is a cycle `z'` over the last vertex with
`fibreInc z' = thetaTop ⌢ c` whose class in the fibre is the `E¹`-image of the class of `c`. -/
theorem capAuxZero (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.SSSR.StemsB.IsSerreFibration p) (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀))
    (k : ℕ) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Pi6.MSSK.Aux R p e₀ hfib hsconn 0 k σ := by
  intro c hcrel
  have hσ : Work.Pi6.MSSK.lastV 0 ≫ σ = σ := by rw [lastV_zero, Category.id_comp]
  have hc : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (0 + k)
      ((ComplexShape.down ℕ).next (0 + k)) c = 0 := relCycle_d_eq_zero p σ k c hcrel
  have hcap : Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
      (Work.Pi6.MSSK.thetaTop R p σ) k c
      = Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ))
          (Nat.zero_add k) c := cap_unit_eq_cast_aux p σ k c
  have hZ : (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
      (Work.SSSR.sigmaVert σ)))).d k ((ComplexShape.down ℕ).next k)
      ((ModuleCat.Hom.hom ((vIsoMap (R := R) p σ).f k))
        (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.thetaTop R p σ) k c)) = 0 :=
    Work.SSSR.izo_d_map_eq_zero (vIsoMap (R := R) p σ)
      (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop R p σ) k c) (cap_theta_cycle p σ k c hc)
  have hcyc : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (Work.Pi6.MSSK.lastV 0 ≫ σ))).d k ((ComplexShape.down ℕ).next k)
      (Work.Pi6.MSSK.capThetaLift' R p σ k c) = 0 :=
    Work.Pi6.MSSK.capThetaLiftZeroCyc p σ k c hc hcap
  refine ⟨(Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
    (Work.Pi6.MSSK.lastV 0 ≫ σ))).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
    ((ComplexShape.down ℕ).next k) rfl hcyc, ?_, ?_⟩
  · rw [Work.SSSR.izo_iCycles_cyclesMk (R := R) rfl
      (Work.Pi6.MSSK.capThetaLift' R p σ k c) hcyc]
    exact Work.Pi6.MSSK.fibreIncCapThetaLift R p σ k c
  · rw [Work.Pi6.MSSK.capSign_zero, one_smul]
    exact (capAuxZeroLHS p e₀ hfib hsconn k σ hσ c
        (Work.Pi6.MSSK.capThetaLift' R p σ k c)
        hcyc (Work.Pi6.MSSK.fibreIncCapThetaLift R p σ k c) hZ).trans
      (capAuxZero_RHS p e₀ hfib hsconn k σ c hcrel hZ).symm

end

end Work.Pi6.MSSK
