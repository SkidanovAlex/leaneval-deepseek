import Mathlib
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.Kunneth.ezEval
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.cup1Identity
import Submission.Work.Cohomology.cupNatural
import Submission.Work.Cohomology.KroneckerH

/-!
# Elementary tools for the Alexander–Whitney evaluation on `S³ × S³`

Generic (spelling-free) lemmas used by `Submission/Work/Cohomology/pxWitness.lean`:

* `pxCochainPullbackHom_eq_ssetPullback` — the identification of the cochain pullback along a
  continuous map with the pullback along the induced morphism of simplicial sets;
* `pxPullback_cocycle` — the pullback of a cocycle is a cocycle;
* `pxSsetPullback_comp` — contravariant functoriality of the pullback along simplicial maps;
* `pxCupSwapOnCycle` — the Alexander–Whitney product of two odd cocycles is graded-commutative on
  a cycle (they differ by the coboundary of the cup-`1` product).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial MonoidalCategory

namespace Work.Cohomology

noncomputable section

/-- The cochain pullback along a continuous map is the pullback along the induced simplicial map. -/
lemma pxCochainPullbackHom_eq_ssetPullback (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (β : Cochain ℤ (TopCat.toSSet.obj Y) n) :
    (cochainPullbackHom ℤ X Y f n).hom β
      = Kunneth.ssetPullback (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
          (TopCat.toSSet.map f) n β := rfl

/-- The coboundary of a pullback along a simplicial map is the pullback of the coboundary. -/
lemma pxSsetPullback_cochainDiff (X Y : SSet) (f : X ⟶ Y) (n : ℕ) (γ : Cochain ℤ Y n) :
    Kunneth.ssetPullback X Y f (n + 1) (cochainDiff ℤ Y γ)
      = cochainDiff ℤ X (Kunneth.ssetPullback X Y f n γ) := by
  apply LinearMap.ext
  intro w
  simp only [Kunneth.ssetPullback, LinearMap.dualMap_apply, cochainDiff, LinearMap.comp_apply]
  congr 1
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).comm (n + 1) n)) w

/-- The pullback of a cocycle along a simplicial map is a cocycle. -/
lemma pxSsetPullback_cocycle (X Y : SSet) (f : X ⟶ Y) (n : ℕ) (γ : Cochain ℤ Y n)
    (hγ : cochainDiff ℤ Y γ = 0) :
    cochainDiff ℤ X (Kunneth.ssetPullback X Y f n γ) = 0 := by
  rw [← pxSsetPullback_cochainDiff X Y f n γ, hγ]
  simp only [Kunneth.ssetPullback, map_zero]

/-- The pullback of a cocycle is a cocycle. -/
lemma pxPullback_cocycle (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (ψ : Cochain ℤ (TopCat.toSSet.obj Y) n)
    (hψ : cochainDiff ℤ (TopCat.toSSet.obj Y) ψ = 0) :
    cochainDiff ℤ (TopCat.toSSet.obj X) ((cochainPullbackHom ℤ X Y f n).hom ψ) = 0 := by
  rw [pxCochainPullbackHom_eq_ssetPullback]
  exact pxSsetPullback_cocycle _ _ _ n ψ hψ

/-- Contravariant functoriality of the pullback of cochains along simplicial maps. -/
theorem pxSsetPullback_comp (X Y Z : SSet) (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (γ : Cochain ℤ Z n) :
    Kunneth.ssetPullback X Z (f ≫ g) n γ
      = Kunneth.ssetPullback X Y f n (Kunneth.ssetPullback Y Z g n γ) := by
  apply cup_ext ℤ X
  intro σ
  rw [Kunneth.ssetPullback_genEval, Kunneth.ssetPullback_genEval,
    Kunneth.ssetPullback_genEval]
  rfl

/-- **The cup product of two degree `3` cocycles is graded-commutative on cycles.** -/
theorem pxCupSwapOnCycle (X : SSet) (α β : Cochain ℤ X 3)
    (hα : cochainDiff ℤ X α = 0) (hβ : cochainDiff ℤ X β = 0)
    (z : (chainC ℤ X).X 6) (hz : ((chainC ℤ X).d 6 5) z = 0) :
    (cup ℤ X α β) z = - (cup ℤ X β α) z := by
  have hid := cup1Identity ℤ X 3 3 (by norm_num) (by norm_num) α β hα hβ
  have hcast1 : (Nat.sub_add_cancel (by omega : 1 ≤ 3 + 3)) ▸
      (cochainDiff ℤ X (cup1 ℤ X 3 3 α β)) = cochainDiff ℤ X (cup1 ℤ X 3 3 α β) := by
    rw [Subsingleton.elim (Nat.sub_add_cancel (by omega : 1 ≤ 3 + 3)) rfl]
  have hcast2 : ((Nat.add_comm 3 3 : 3 + 3 = 3 + 3)) ▸ (cup ℤ X β α) = cup ℤ X β α := by
    rw [Subsingleton.elim (Nat.add_comm 3 3 : 3 + 3 = 3 + 3) rfl]
  rw [hcast1, hcast2, show ((-1 : ℤ) ^ (3 * 3)) = -1 from by norm_num] at hid
  have h2 := congrArg (fun (γ : Cochain ℤ X (3 + 3)) => γ z) hid
  have h3 : (cochainDiff ℤ X (cup1 ℤ X 3 3 α β)) z = 0 := by
    show (cup1 ℤ X 3 3 α β) (((chainC ℤ X).d 6 5) z) = 0
    rw [hz, map_zero]
  have h2' : (cup ℤ X α β - (-1 : ℤ) • cup ℤ X β α) z = 0 := by rw [← h2, h3]
  rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, neg_one_mul] at h2'
  exact sub_eq_zero.mp h2'

end

end Work.Cohomology
