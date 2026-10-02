import Mathlib
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.localThomMap_pdCohMap
import Submission.Work.Cohomology.pdCohSub_iUnion_of_wf

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type} (Z : RealBundle B F ι)

noncomputable section

/-- The relative part of a piece of the total space. -/
abbrev relPiece (W : Set B) : Set ↥(Z.proj ⁻¹' W) :=
  {y | (y : Z.TotalSpace) ∈ Work.Thom.zeroComplement Z}

/-- The relative cochain complex of the total piece over `W`; its homology is `PieceCoh Z W •`. -/
def TotComplex (W : Set B) : CochainComplex (ModuleCat ℤ) ℕ :=
  relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)

/-- The degrees of `TotComplex`. -/
abbrev TotC (W : Set B) (m : ℕ) : Type :=
  ↥(relKern ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) m)

/-- The absolute cochain complex of `W`; its homology is `Coh ℤ • W`. -/
def BaseComplex (W : Set B) : CochainComplex (ModuleCat ℤ) ℕ :=
  singularCochainComplex ℤ (TopCat.of ↥W)

/-- The degrees of `BaseComplex`. -/
abbrev BaseC (W : Set B) (m : ℕ) : Type :=
  ↥((singularCochainComplex ℤ (TopCat.of ↥W)).X m)

/-- The pullback of an absolute cochain on `W` to the total piece, as an absolute cochain. -/
def pullAbs (W : Set B) (m : ℕ) :
    BaseC W m →ₗ[ℤ] ↥((singularCochainComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W))).X m) :=
  ModuleCat.Hom.hom ((dualChainMap ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (TopCat.of ↥W)
    (TopCat.ofHom (Work.Thom.pieceProj Z W))).f m)

variable (n : ℕ) (U : Set B)

/-- The chosen relative cocycle representative of `τ ∈ H^n(X|_U, A)`. -/
def tauRep (τ : Work.Thom.PieceCoh Z U n) : TotC Z U n :=
  Classical.choose (exists_relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U) n τ)

theorem tauRep_cocycle (τ : Work.Thom.PieceCoh Z U n) :
    relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U) n (tauRep Z n U τ) = 0 :=
  (Classical.choose_spec (exists_relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' U))
    (relPiece Z U) n τ)).1

theorem tauRep_class (τ : Work.Thom.PieceCoh Z U n) :
    relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U) (tauRep Z n U τ)
      (tauRep_cocycle Z n U τ) = τ :=
  (Classical.choose_spec (exists_relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' U))
    (relPiece Z U) n τ)).2

/-- The restriction of the global representative to a piece `W ⊆ U`. -/
def tauRepAt (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) : TotC Z W n :=
  rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono hW) n (tauRep Z n U τ)

theorem tauRepAt_cocycle (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) :
    relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) n (tauRepAt Z n U τ W hW) = 0 := by
  rw [tauRepAt, ← rcResLM_comm]
  rw [tauRep_cocycle, map_zero]

/-- The cup of the pullback of a base cochain with the restricted representative, in degree `m+n`. -/
def psiAbs (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) (m : ℕ) (a : BaseC W m) :
    TotC Z W (m + n) :=
  ⟨cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
      (pullAbs Z W m a : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m)
      ((tauRepAt Z n U τ W hW).1 : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n),
    cup_mem_relKern_right ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)
      (pullAbs Z W m a : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m)
      (tauRepAt Z n U τ W hW).2⟩

/-- The cochain-level Thom map `ψ`, landing in degree `n + m`. -/
def psi (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) (m : ℕ) (a : BaseC W m) :
    TotC Z W (n + m) :=
  (Nat.add_comm m n) ▸ psiAbs Z n U τ W hW m a

/-- Cast-irrelevance for the transport of an element along equalities of types. -/
theorem cast_irrel {A B : Type} (h h' : A = B) (x : A) : h ▸ x = h' ▸ x := by
  rw [Subsingleton.elim h h']

/-- The degree cast commutes with the relative differential. -/
theorem relDiffLM_cast (W : Set B) {a b : ℕ} (h : a = b) (x : TotC Z W a) :
    relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) b (h ▸ x)
      = h ▸ (relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) a x) := by
  cases h
  rfl

end

end Work.ThomBordism
