import Mathlib
import Submission.Work.SSSR.serreE1Psi
import Submission.Work.Cohomology.CapProduct
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option synthInstance.maxHeartbeats 800000

/-!
# MSSK — the lead's vocabulary for the E¹ cap/transport lemma (DO NOT EDIT: contract)

Design: `REFS/NOTES_LEAD_MSSK.md`.  For a simplex `σ : Δ[s] → Sing B` and `T_σ = Δ[s] ×_{Sing B} Sing E`
(`Work.SSSR.pullAlong`):
* `lastV s : Δ[0] ⟶ Δ[s]` — the last vertex;
* `fibreInc p σ : T_{σ(s)} ⟶ T_σ` — the inclusion of the part of `T_σ` over the last vertex;
* `thetaTop R p σ` — the `s`-cochain on `T_σ` which is `1` on the simplices lying over the top simplex
  `id : [s] → [s]` of `Δ[s]` and `0` elsewhere.  For a normalised `s`-cochain `β` on `Sing B`, the pull-back of
  `β` to `T_σ` equals `β(σ) • thetaTop` in degree `s`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

/-- The last vertex `Δ[0] ⟶ Δ[s]`. -/
def lastV (s : ℕ) : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶
    SSet.stdSimplex.obj (SimplexCategory.mk s) :=
  SSet.stdSimplex.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk s) (Fin.last s))

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The part of `T_σ` over the last vertex, included in `T_σ`. -/
def fibreInc (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastV s ≫ σ) ⟶
      Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ :=
  show pullback (lastV s ≫ σ) (Work.SSSR.sSingP p) ⟶ pullback σ (Work.SSSR.sSingP p) from
  pullback.lift (pullback.fst (lastV s ≫ σ) (Work.SSSR.sSingP p) ≫ lastV s)
    (pullback.snd (lastV s ≫ σ) (Work.SSSR.sSingP p))
    (by rw [Category.assoc]; exact pullback.condition)

/-- The top simplex of `Δ[s]`. -/
def topS (s : ℕ) : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) _⦋s⦌ :=
  SSet.stdSimplex.objEquiv.symm (𝟙 _)

/-- The value of `thetaTop` on an `s`-simplex of `T_σ`. -/
def thetaVal (R : Type) [CommRing R] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s⦌) : R := by
  classical
  exact if (pullback.fst σ (Work.SSSR.sSingP p)).app (op (SimplexCategory.mk s)) w = topS s then 1 else 0

/-- **`thetaTop`**: the indicator `s`-cochain of the simplices of `T_σ` over the top simplex of `Δ[s]`. -/
def thetaTop (R : Type) [CommRing R] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Cohomology.Cochain R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s :=
  ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).isColimitChainComplexXCofan (ModuleCat.of R R) s).desc
    (Cofan.mk (ModuleCat.of R R) (fun w =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton R R (thetaVal R p σ w)))) |>.hom

end

end Work.Pi6.MSSK
