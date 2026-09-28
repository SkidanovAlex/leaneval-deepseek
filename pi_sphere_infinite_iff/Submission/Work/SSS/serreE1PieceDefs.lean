import Mathlib
import Submission.Work.SSS.serreE1Defs
import Submission.Work.Serre.E2bDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Vocabulary for the σ-piece of the Serre filtration

For `f : X ⟶ Y` a morphism of simplicial sets and a simplex `σ : Δ[s] ⟶ Y`, the σ-piece
`pieceAlong f σ = C(T_σ)/C(∂T_σ)` of `Submission/Work/SSS/serreE1Defs.lean` is the relative chain
complex of the simplicial pullback `T_σ = Δ[s] ×_Y X` over the preimage `∂T_σ` of `∂Δ[s]`.

The proof of `serreE1Piece` proceeds by induction on `s`, splitting `∂Δ[s]` into
`∂Δ[s] = Λ ∪ D` where

* `Λ` is the **horn** `⋃_{i<s} d_iΔ[s]` (the union of the faces *other* than the last one), and
* `D` is the **last face** `d_sΔ[s]`.

The corresponding subcomplexes of `T_σ` are `pieceHorn f σ` and `pieceLastFace f σ`; the last face
`D ≅ Δ[s-1] ×_Y X` is the pullback along the composite `d_s ≫ σ`, whose first vertex is still the
first vertex of `σ` (so no fibre transport appears).

Main results of the induction step (all to be found downstream):

* `Work.SSS.pieceHornC` — the chain complex `C(T_σ)/C(Λ)`;
* its homology vanishes in all degrees when `1 ≤ s` (the prism contraction of the last vertex).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSS

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

/-- The inclusion of the **simplex hat** `sHat n = (Δⁿ×{0}) ∪ (∂Δⁿ×I)` into `Δⁿ × I`. -/
def sHatIncl (n : ℕ) :
    C(↥(Work.Serre.sHat n), ↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem sHatIncl_apply (n : ℕ) (x : ↥(Work.Serre.sHat n)) : sHatIncl n x = x.1 := rfl

/-- The chain complex `C(T_σ)/C(Λ)` of the pullback modulo the horn. -/
def pieceHornC {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (sCCMap (pieceHorn f σ).ι)

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
def pieceBdryHornC {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (sCCMap (SSet.Subcomplex.homOfLE (pieceHorn_le_bdryAlong f σ)))

end

end Work.SSS
