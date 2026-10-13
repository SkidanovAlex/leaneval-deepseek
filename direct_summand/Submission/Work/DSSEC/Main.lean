import Submission.Work.DSSEC.Basic
import Submission.Work.DSSEC.exists_secData
import Submission.Work.DSSEC.exists_cechMap_of_secData

/-!
# DSSEC — the deliverable: `DSMap.Mix2.area_SEC_proved`

This module delivers `DSMap.Mix2.area_SEC_proved`, whose type is **identical** (up to universe
names) to the frozen node `DSMap.Mix2.area_SEC` of `Submission/Work/DSMap/Mix2.lean`: the SEC
node of the MIX2 route, i.e. the point-to-blowup chart comparison

`Γ(X ∩ D₊(x_S)) ⟶ W[J/t_S]`, `x_k/x_i ↦ t_k/t_i`  (`S` nonempty),

assembled into a chain map `Č(X, U) → Č(Bl_J W)` compatible with the coaugmentations.

The proof is the composition of the two halves built in this directory:

* `Work.DSSEC.exists_secData` (geometric half): the SEC hypotheses produce a
  `Work.DSSEC.SecData`, a comparison of `Γ(X, U_S)` with the blowup chart rings `W[J/t_S]`
  defined on nonempty index sets `S` only;
* `Work.DSSEC.exists_cechMap_of_secData` (combinatorial half): a `SecData` produces the chain
  map.

Everything else lives in the sibling modules of `Submission/Work/DSSEC/`; a caller needs only
import this module; `#print axioms DSMap.Mix2.area_SEC_proved` lists only
`propext, Classical.choice, Quot.sound` (see `Submission/Work/DSSEC/Axioms.lean`).
-/

open CategoryTheory AlgebraicGeometry Limits Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.unusedSectionVars false

namespace DSMap.Mix2
open DSMap DSMap.Mix

universe a

/-- **SEC** (DSSEC deliverable): a `W[1/p]`-point of the chart `X ∩ D₊(x_j)` with homogeneous
coordinates `t ∈ W` (`W` `p`-torsion-free) gives a chain map `Č(X, U) → Č(Bl_J W)` compatible
with the coaugmentations.  Same type as the frozen `DSMap.Mix2.area_SEC`. -/
theorem area_SEC_proved (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) (N : ℕ) (i : X ⟶ PSpace A N) (hi : IsClosedImmersion i)
    (hif : i ≫ PSpace.toSpec A N = f) (j : Fin (N + 1))
    (W : Type a) [CommRing W] (hW : IsSMulRegular W (p : W)) (ψ : A →+* W)
    (θ : Γ(X, chartCover i ⟨j⟩) →+* Localization.Away (p : W))
    (hθ : θ.comp (phiU A X f (chartCover i ⟨j⟩)) = (algebraMap W _).comp ψ)
    (t : ULift.{a} (Fin (N + 1)) → W)
    (ht : IsUnit (algebraMap W (Localization.Away (p : W)) (t ⟨j⟩)))
    (htθ : ∀ k, k ≠ j → algebraMap W (Localization.Away (p : W)) (t ⟨k⟩) =
      algebraMap W _ (t ⟨j⟩) * θ (xiSec i j k)) :
    ∃ χ : cechZ A X f (chartCover i) ⟶ chartCechA ψ t,
      coaug0 A X f (chartCover i) ≫
        ((cech A X f (chartCover i)).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv ≫
          χ.f 0 ≫ (ModuleCat.restrictScalars ψ).map
            ((chartCech t).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
        chartCoaugA ψ t := by
  obtain ⟨D⟩ := Work.DSSEC.exists_secData p A X f N i hi hif j W hW ψ θ hθ t ht htθ
  exact Work.DSSEC.exists_cechMap_of_secData p A X f N i W ψ t D

/-- The statement of `area_SEC_proved` is the statement of the frozen `area_SEC`: the frozen
proof is accepted at exactly this type (so the two types are definitionally equal, universe
levels included).  This is the type-identity check for the deliverable; it uses the frozen
(hence unproved) declaration `area_SEC` and therefore does **not** occur in the proof
of `area_SEC_proved`. -/
example (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) (N : ℕ) (i : X ⟶ PSpace A N) (hi : IsClosedImmersion i)
    (hif : i ≫ PSpace.toSpec A N = f) (j : Fin (N + 1))
    (W : Type a) [CommRing W] (hW : IsSMulRegular W (p : W)) (ψ : A →+* W)
    (θ : Γ(X, chartCover i ⟨j⟩) →+* Localization.Away (p : W))
    (hθ : θ.comp (phiU A X f (chartCover i ⟨j⟩)) = (algebraMap W _).comp ψ)
    (t : ULift.{a} (Fin (N + 1)) → W)
    (ht : IsUnit (algebraMap W (Localization.Away (p : W)) (t ⟨j⟩)))
    (htθ : ∀ k, k ≠ j → algebraMap W (Localization.Away (p : W)) (t ⟨k⟩) =
      algebraMap W _ (t ⟨j⟩) * θ (xiSec i j k)) :
    ∃ χ : cechZ A X f (chartCover i) ⟶ chartCechA ψ t,
      coaug0 A X f (chartCover i) ≫
        ((cech A X f (chartCover i)).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv ≫
          χ.f 0 ≫ (ModuleCat.restrictScalars ψ).map
            ((chartCech t).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
        chartCoaugA ψ t :=
  area_SEC p A X f N i hi hif j W hW ψ θ hθ t ht htθ

end DSMap.Mix2
