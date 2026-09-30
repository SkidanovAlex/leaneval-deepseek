/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Mathlib
import Submission.Work.DescentGeom.Basic
import Submission.Work.Descent.isGaloisQuotient_of_iso
import Submission.Work.Descent.All
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.QuotientMap
import Submission.Work.SymQuot.QuotientHom
import Submission.Work.SymQuot.Chart.exists_quotientMap
import Submission.Work.SymQuot.Chart.quotient_lift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Effective Galois descent of a scheme with a Galois-stable affine cover: the setup

This file fixes the dictionary used by the proof of
`Work.DescentGeom.exists_descentData`: the hypotheses (`GalData`), the induced action of the
Galois group on `G'` as a `Work.SymQuot.GAction`, the quotient data `qd`, the descended `k`-scheme
`J`, the quotient map `q` and the comparison morphism `phi : G' ⟶ J_{k'}`.

The main external input is `localSpeiser`: for every chart `U` of the quotient data, the canonical
comparison map `sU D U : Ω_U ⟶ p⁻¹(chart U) ⊆ J_{k'}` is an isomorphism, which is the affine-local
Speiser statement for the ring of sections of the `Γ`-stable affine open `Ω_U`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory

universe u

namespace Work.DescentGeom

noncomputable section

/-- The data of the effective descent problem of `Work.DescentGeom.exists_descentData`:
`G'` a `k'`-scheme separated over `k'`, a semilinear action of `Γ = Gal k k'` on `G'`, and a
`Γ`-stable affine open cover of `G'`.  (The field-theoretic hypotheses `k'/k` finite Galois are
kept as separate typeclass arguments throughout.) -/
structure GalData (k k' : Type u) [Field k] [Field k'] [Algebra k k'] where
  /-- the `k'`-scheme to descend -/
  G' : Sch k'
  /-- `G'` is separated over `k'` -/
  isSep : IsSeparated G'.hom
  /-- the semilinear action of the Galois group -/
  galAct : Work.Descent.Gal k k' → (G'.left ≅ G'.left)
  /-- it is an action -/
  galAct_one : galAct 1 = Iso.refl G'.left
  /-- it is an action -/
  galAct_mul : ∀ σ τ, galAct (σ * τ) = (galAct σ).trans (galAct τ)
  /-- it is semilinear over `Spec k'` -/
  hhom : ∀ σ, (galAct σ).hom ≫ G'.hom = G'.hom ≫ specGal σ
  /-- `G'` has a `Γ`-stable affine open cover -/
  hcover : ∀ x : G'.left, ∃ Ω : G'.left.Opens, IsAffineOpen Ω ∧
      (∀ σ, (galAct σ).hom ⁻¹ᵁ Ω = Ω) ∧ x ∈ Ω

namespace GalData

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
  [IsGalois k k'] [FiniteDimensional k k']

/-- **Affine opens of `G'` have affine intersections**, since `G'` is separated over `k'`. -/
theorem isAffineHom_diagonal (D : GalData k k') :
    IsAffineHom (pullback.diagonal (terminal.from D.G'.left)) := by
  haveI := D.isSep
  have h1 : IsSeparated (D.G'.hom ≫ terminal.from (Spec (CommRingCat.of k'))) := inferInstance
  rw [terminal.comp_from D.G'.hom] at h1
  haveI := h1
  infer_instance

/-- `Spec σ` is a morphism of `k`-schemes. -/
lemma specGal_specMap (σ : Work.Descent.Gal k k') :
    specGal σ ≫ Work.Descent.specMap k k' = Work.Descent.specMap k k' := by
  simp only [Work.DescentGeom.specGal, Work.Descent.specMap, ← Spec.map_comp]
  congr 1
  ext c
  simp

/-- The Galois action on `G'` as a `Work.SymQuot.GAction` (with the contravariant composition
convention of `GAction`). -/
def act (D : GalData k k') : SymQuot.GAction (Work.Descent.Gal k k') D.G'.left where
  hom σ := (D.galAct σ⁻¹).hom
  inv σ := (D.galAct σ⁻¹).inv
  hom_inv σ := (D.galAct σ⁻¹).hom_inv_id
  inv_hom σ := (D.galAct σ⁻¹).inv_hom_id
  hom_one := by
    have h : (1 : Work.Descent.Gal k k')⁻¹ = 1 := inv_one
    rw [h, D.galAct_one]
    rfl
  hom_mul g h := by
    have h1 : (g * h)⁻¹ = h⁻¹ * g⁻¹ := mul_inv_rev g h
    rw [h1, D.galAct_mul]
    rfl

lemma act_hom (D : GalData k k') (σ : Work.Descent.Gal k k') :
    (D.act).hom σ = (D.galAct σ⁻¹).hom := rfl

lemma act_isInvariantOpen_iff (D : GalData k k') {Ω : D.G'.left.Opens} :
    (D.act).IsInvariantOpen Ω ↔ ∀ σ, (D.galAct σ).hom ⁻¹ᵁ Ω = Ω := by
  constructor
  · intro h σ
    simpa [act_hom] using h σ⁻¹
  · intro h σ
    simpa [act_hom, act] using h σ⁻¹

/-- The structure morphism of `G'` as a `k`-scheme. -/
def strK (D : GalData k k') : D.G'.left ⟶ Spec (CommRingCat.of k) :=
  D.G'.hom ≫ Work.Descent.specMap k k'

lemma strK_invariant (D : GalData k k') :
    ∀ g : Work.Descent.Gal k k', (D.act).hom g ≫ D.strK = D.strK := by
  intro g
  rw [strK, act_hom]
  rw [← Category.assoc, D.hhom, Category.assoc, specGal_specMap]

/-- The quotient data for the action of `Γ` on `G'`. -/
def qd (D : GalData k k') : SymQuot.QuotientData (Work.Descent.Gal k k') D.G'.left where
  action := D.act
  isAffineOpen_inf := by
    haveI := D.isAffineHom_diagonal
    intro U V hU hV
    exact hU.inf hV
  covers x := by
    obtain ⟨Ω, h1, h2, h3⟩ := D.hcover x
    exact ⟨Ω, h1, (D.act_isInvariantOpen_iff).mpr h2, h3⟩

lemma qd_action (D : GalData k k') : (D.qd).action = D.act := rfl

/-- The descent `J = G'/Γ` of `G'`, as a `k`-scheme. -/
def J (D : GalData k k') : Sch k :=
  Over.mk ((D.qd).quotientHom D.strK (D.strK_invariant))

lemma J_left (D : GalData k k') : (D.J).left = (D.qd).Quotient := rfl

lemma J_hom (D : GalData k k') :
    (D.J).hom = (D.qd).quotientHom D.strK (D.strK_invariant) := rfl

/-- The quotient map `G' ⟶ J`. -/
def q (D : GalData k k') : D.G'.left ⟶ (D.J).left := (D.qd).quotientMap

lemma q_hom (D : GalData k k') : D.q ≫ (D.J).hom = D.strK :=
  (D.qd).quotientMap_quotientHom D.strK (D.strK_invariant)

lemma q_isInvariant (D : GalData k k') (σ : Work.Descent.Gal k k') :
    (D.galAct σ).hom ≫ D.q = D.q := by
  have h := (D.qd).quotientMap_isInvariant σ⁻¹
  rw [qd_action] at h
  have h2 : (D.act).hom σ⁻¹ = (D.galAct σ).hom := by
    show (D.galAct (σ⁻¹)⁻¹).hom = (D.galAct σ).hom
    rw [inv_inv]
  rw [h2] at h
  exact h

/-- The comparison morphism `G' ⟶ J_{k'}` of `k'`-schemes, as a morphism of schemes. -/
def phi (D : GalData k k') : D.G'.left ⟶ (bc k' (D.J)).left :=
  pullback.lift D.q D.G'.hom (by rw [q_hom, strK])

lemma phi_bcπ (D : GalData k k') :
    D.phi ≫ pullback.fst (D.J).hom (Work.Descent.specMap k k') = D.q :=
  pullback.lift_fst _ _ _

lemma phi_hom (D : GalData k k') :
    D.phi ≫ pullback.snd (D.J).hom (Work.Descent.specMap k k') = D.G'.hom :=
  pullback.lift_snd _ _ _

lemma phi_bcπ' (D : GalData k k') : D.phi ≫ bcπ k' (D.J) = D.q := phi_bcπ D

lemma phi_hom' (D : GalData k k') : D.phi ≫ (bc k' (D.J)).hom = D.G'.hom := phi_hom D

attribute [simp] phi_bcπ phi_hom

/-- The comparison morphism `G' ⟶ J_{k'}` as a morphism of `k'`-schemes. -/
def phiOver (D : GalData k k') : D.G' ⟶ bc k' (D.J) := Over.homMk D.phi (phi_hom D)

@[simp] lemma phiOver_left (D : GalData k k') : (D.phiOver).left = D.phi := rfl

/-- **Equivariance of the comparison morphism.** -/
theorem galAct_phi (D : GalData k k') (σ : Work.Descent.Gal k k') :
    (D.galAct σ).hom ≫ D.phi = D.phi ≫ Work.Descent.galAct (D.J) σ := by
  apply pullback.hom_ext (f := (D.J).hom) (g := Work.Descent.specMap k k')
  · rw [Category.assoc, Category.assoc, phi_bcπ, Work.Descent.AffOpensDesc.galAct_fst,
      phi_bcπ, q_isInvariant]
  · rw [Category.assoc, Category.assoc, phi_hom, Work.Descent.AffOpensDesc.galAct_snd,
      ← Category.assoc, phi_hom, D.hhom]


/-! ### The charts of the quotient and the local comparison maps -/

/-- The open cover of `J` by its charts. -/
def coverV (D : GalData k k') : (D.J).left.OpenCover :=
  Scheme.IsLocallyDirected.openCover (D.qd).chartFunctor

lemma coverV_f (D : GalData k k') (U : (D.qd).Chart) :
    (D.coverV).f U = (D.qd).chartι U :=
  Scheme.IsLocallyDirected.openCover_f _ _

/-- The open cover of `J_{k'}` obtained by base change of the chart cover. -/
def coverU (D : GalData k k') : (bc k' (D.J)).left.OpenCover :=
  (D.coverV).pullback₁ (bcπ k' (D.J))

/-- The piece of `J_{k'}` above the chart `U`: the preimage of the chart under `bcπ`. -/
abbrev piece (D : GalData k k') (U : (D.qd).Chart) : Scheme :=
  pullback (bcπ k' (D.J)) ((D.qd).chartι U)

lemma coverU_f (D : GalData k k') (U : (D.qd).Chart) :
    (D.coverU).f U = pullback.fst (bcπ k' (D.J)) ((D.qd).chartι U) := rfl

/-- **The local comparison map.**  It exhibits the `Γ`-stable affine open `Ω_U = U.1 ⊆ G'` as
the preimage under `J_{k'} ⟶ J` of the chart `U` of the quotient.  It is an isomorphism by
Speiser's lemma, applied to the ring of sections `Γ(G', Ω_U)` (see `localSpeiser`).

Route for the proof of `IsIso (D.sU U)` (`localSpeiser`):

* `D.pieceIso U : (bc k' (D.chartSch U)).left ≅ D.piece U` is the pasting isomorphism, and
  `(bc k' (D.chartSch U)).left = pullback ((D.qd).chartι U ≫ (D.J).hom) (specMap k k')` by
  definition of `chartSch`;
* `s : U.1.toScheme ⟶ (bc k' (D.chartSch U)).left` is the morphism with components
  `D.qd.action.chartMap U.1 U.2.2` and `U.1.ι ≫ D.G'.hom`; then `s ≫ D.pieceIso U = D.sU U`;
* `IsIso s` is Speiser's statement for the affine `Γ`-stable open `U.1`: writing
  `R = Γ(G'.left, U.1)`, `A = (D.qd).action.chartRing U.1 U.2.2`, the pullback is
  `Spec (A ⊗_k k')` (`AlgebraicGeometry.pullbackSpecIso`), `U.1.toScheme = Spec R` and `s` is
  `Spec` of `A ⊗_k k' → R`, which is Speiser's map `b ⊗ c ↦ c • b` (`Work.Descent.speiser`),
  once `A` is identified with the `Γ`-invariants of the semilinear action of `Γ` on `R` (induced
  by `D.galAct`, cf. `Work.SymQuot.GAction.sectionMulSemiringAction` and
  `Work.Descent.SemilinearAction.invariants`). -/
def sU (D : GalData k k') (U : (D.qd).Chart) : U.1.toScheme ⟶ D.piece U :=
  pullback.lift (U.1.ι ≫ D.phi) ((D.qd).action.chartMap U.1 U.2.2) (by
    rw [Category.assoc, phi_bcπ']
    exact (D.qd).quotientMap_chartι U)

lemma sU_fst (D : GalData k k') (U : (D.qd).Chart) :
    D.sU U ≫ pullback.fst (bcπ k' (D.J)) ((D.qd).chartι U) = U.1.ι ≫ D.phi :=
  pullback.lift_fst _ _ _

lemma sU_coverU (D : GalData k k') (U : (D.qd).Chart) :
    D.sU U ≫ (D.coverU).f U = U.1.ι ≫ D.phi := by
  rw [coverU_f]
  exact sU_fst D U

lemma sU_chart (D : GalData k k') (U : (D.qd).Chart) :
    D.sU U ≫ pullback.snd (bcπ k' (D.J)) ((D.qd).chartι U) =
      (D.qd).action.chartMap U.1 U.2.2 :=
  pullback.lift_snd _ _ _


/-! ### The descent isomorphism -/

lemma inv_phi_hom (D : GalData k k') (h : IsIso D.phi) :
    inv D.phi ≫ D.G'.hom = (bc k' (D.J)).hom := by
  haveI := h
  rw [← D.phi_hom', IsIso.inv_hom_id_assoc]

lemma eInv_hl_hom (D : GalData k k') (h : IsIso D.phi) :
    (asIso D.phi).symm.hom ≫ D.G'.hom = (bc k' (D.J)).hom := by
  rw [Iso.symm_hom, asIso_inv]
  exact D.inv_phi_hom h

/-- **The descent isomorphism**, given that the comparison morphism `D.phi` is invertible: the
inverse of `D.phi`, as an isomorphism `J_{k'} ≅ G'` of `k'`-schemes. -/
noncomputable def eInv (D : GalData k k') (h : IsIso D.phi) : bc k' (D.J) ≅ D.G' :=
  Over.isoMk (asIso D.phi).symm (D.eInv_hl_hom h)

lemma eInv_hom_left (D : GalData k k') (h : IsIso D.phi) :
    (D.eInv h).hom.left = inv D.phi := by
  rw [eInv]
  rfl

/-- **Equivariance of the descent isomorphism.** -/
theorem eInv_galAct (D : GalData k k') (h : IsIso D.phi) (σ : Work.Descent.Gal k k') :
    Work.Descent.galAct (D.J) σ ≫ (D.eInv h).hom.left =
      (D.eInv h).hom.left ≫ (D.galAct σ).hom := by
  rw [eInv_hom_left]
  haveI := h
  have h2 : Work.Descent.galAct (D.J) σ = inv D.phi ≫ (D.galAct σ).hom ≫ D.phi := by
    rw [← IsIso.inv_hom_id_assoc D.phi (Work.Descent.galAct (D.J) σ), ← D.galAct_phi σ]
  rw [h2]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]


/-- The chart `U` of the quotient, viewed as a `k`-scheme via its structure map inside `J`. -/
def chartSch (D : GalData k k') (U : (D.qd).Chart) : Sch k :=
  Over.mk ((D.qd).chartι U ≫ (D.J).hom)

@[simp] lemma chartSch_hom (D : GalData k k') (U : (D.qd).Chart) :
    (D.chartSch U).hom = (D.qd).chartι U ≫ (D.J).hom := rfl

@[simp] lemma chartSch_left (D : GalData k k') (U : (D.qd).Chart) :
    (D.chartSch U).left = (D.qd).chart U := rfl

/-- **The pasting isomorphism.**  `D.piece U`, the preimage of the chart `U` in `J_{k'}`, is the
base change of the chart along its own structure morphism `chart U ⟶ J ⟶ Spec k`. -/
noncomputable def pieceIso (D : GalData k k') (U : (D.qd).Chart) :
    (bc k' (D.chartSch U)).left ≅ D.piece U :=
  (pullbackRightPullbackFstIso (f' := (D.qd).chartι U) (f := (D.J).hom)
      (g := Work.Descent.specMap k k')).symm ≪≫
    pullbackSymmetry ((D.qd).chartι U) (bcπ k' (D.J))

end GalData

end

end Work.DescentGeom
