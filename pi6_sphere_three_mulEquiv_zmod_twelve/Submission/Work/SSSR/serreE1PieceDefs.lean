import Mathlib
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.SSSR.Serre.E2bDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

/-- The **horn** of `Δ[s]`: the union of the faces `d_iΔ[s]` for `i < s` (all faces except the
last one).  Note that every point of `Λ` has at least one of its first `s` barycentric coordinates
equal to zero, so the last vertex `v_s` lies in the horn (for `s ≥ 1`). -/
def hornSimp (s : ℕ) : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}).Subcomplex :=
  ⨆ (i : Fin s), SSet.stdSimplex.face ({i.castSucc} : Finset (Fin (s + 1)))ᶜ

/-- The **last face** of `Δ[s]`, i.e. the face `d_sΔ[s]` opposite the last vertex. -/
def lastFaceSimp (s : ℕ) : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}).Subcomplex :=
  SSet.stdSimplex.face ({(Fin.last s)} : Finset (Fin (s + 1)))ᶜ

/-- The horn subcomplex `Λ ⊆ T_σ` of the pullback, i.e. the preimage of `hornSimp s`. -/
def pieceHorn {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    (pullAlong f σ).Subcomplex :=
  (hornSimp s).preimage (pullback.fst σ f)

/-- The last-face subcomplex `D ⊆ T_σ` of the pullback, i.e. the preimage of `lastFaceSimp s`. -/
def pieceLastFace {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    (pullAlong f σ).Subcomplex :=
  (lastFaceSimp s).preimage (pullback.fst σ f)

/-- The chain complex `C(T_σ)/C(Λ)` of the pullback modulo the horn. -/
def pieceHornC (R : Type) [CommRing R] [Nontrivial R] {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    ChainComplex (ModuleCat R) ℕ :=
  cokernel (sCCMap R (pieceHorn f σ).ι)

/-- The horn is contained in the boundary `∂Δ[s]`. -/
theorem hornSimp_le_boundary (s : ℕ) : hornSimp s ≤ SSet.boundary s := by
  rw [hornSimp, SSet.boundary_eq_iSup]
  refine iSup_le fun i => ?_
  exact le_iSup (fun j : Fin (s + 1) =>
    SSet.stdSimplex.face ({j} : Finset (Fin (s + 1)))ᶜ) i.castSucc

/-- The horn subcomplex is contained in the boundary subcomplex of the pullback. -/
theorem pieceHorn_le_bdryAlong {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    pieceHorn f σ ≤ bdryAlong f σ :=
  SSet.Subcomplex.preimage_monotone _ (hornSimp_le_boundary s)

/-- The chain complex `C(∂T_σ)/C(Λ)`. -/
def pieceBdryHornC (R : Type) [CommRing R] [Nontrivial R] {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    ChainComplex (ModuleCat R) ℕ :=
  cokernel (sCCMap R (SSet.Subcomplex.homOfLE (pieceHorn_le_bdryAlong f σ)))

end

end Work.SSSR
