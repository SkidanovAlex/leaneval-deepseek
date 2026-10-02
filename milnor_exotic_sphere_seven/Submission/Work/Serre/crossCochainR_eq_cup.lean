import Mathlib
import Submission.Work.Serre.ezShuffleRat
import Submission.Work.Serre.ezShuffleEval
import Submission.Work.Kunneth.CrossCup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `R`-coefficient cross product is the cup product of the pulled-back cochains

For cochains `α` of `X` and `β` of `Y` of degrees `p` and `q` over a commutative ring `R`, the
cross product `Work.Serre.crossCochainR R X Y p q α β` (the `R`-analogue of
`Work.Kunneth.crossCochain`) of `Submission/Work/Serre/ezShuffleRat.lean` is exactly the
Alexander–Whitney cup product of the pullbacks of `α` and `β` along the two projections of the
product `X ⊗ Y`:

  `α × β = π₁^* α ⌣ π₂^* β`.

Over `R = ℤ` this is `Work.Kunneth.crossCochain_eq_cup`; the proof here is the verbatim
coefficient-generic form of that argument.

## Main results

* `ssetPullbackR_genEval` — the value of the pullback of a cochain along a simplicial map on a
  generating simplex (the `R`-analogue of `Work.Cohomology.Kunneth.ssetPullback_genEval`);
* `crossCochainR_eq_cup` — the identity `α × β = π₁^*α ⌣ π₂^*β`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Serre

noncomputable section

open Work.Cohomology

variable (R : Type) [CommRing R]

/-- The value of the pullback of a cochain along a morphism of simplicial sets, on a generating
simplex, over an arbitrary commutative ring.  This is the `R`-analogue of
`Work.Cohomology.Kunneth.ssetPullback_genEval`. -/
lemma ssetPullbackR_genEval (X Y : SSet) (f : X ⟶ Y) (n : ℕ)
    (β : Cochain R Y n) (x : X _⦋n⦌) :
    genEval R X (((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap β) x
      = genEval R Y β ((ConcreteCategory.hom (f.app (Opposite.op ⦋n⦌))) x) := by
  have h := SSet.ι_chainComplexMap_f X Y f (ModuleCat.of R R) x
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ (Y.chainComplex (ModuleCat.of R R)).X n)
    => β (g.hom (1 : R))) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [genEval, genEval, LinearMap.dualMap_apply]
  exact h2

theorem crossCochainR_eq_cup (R : Type) [CommRing R] (X Y : SSet) (p q : ℕ)
    (α : Work.Cohomology.Cochain R X p) (β : Work.Cohomology.Cochain R Y q) :
    Work.Serre.crossCochainR R X Y p q α β
      = Work.Cohomology.cup R (Work.Kunneth.sProd X Y)
          (((SSet.chainComplexMap (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y)
              (ModuleCat.of R R)).f p).hom.dualMap α)
          (((SSet.chainComplexMap (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y)
              (ModuleCat.of R R)).f q).hom.dualMap β) := by
  apply Work.Cohomology.genEval_ext
  intro z
  obtain ⟨a, b⟩ := z
  rw [crossCochainR_apply, Work.Cohomology.cup_apply]
  have hα : Work.Cohomology.genEval R (X ⊗ Y)
        (((SSet.chainComplexMap (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y)
            (ModuleCat.of R R)).f p).hom.dualMap α)
        (Work.Cohomology.frontFace (X ⊗ Y) p (p + q) (Nat.le_add_right p q) (a, b))
      = Work.Cohomology.genEval R X α
        (Work.Cohomology.frontFace X p (p + q) (Nat.le_add_right p q) a) := by
    rw [ssetPullbackR_genEval R (X ⊗ Y) X
      (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p α
      (Work.Cohomology.frontFace (X ⊗ Y) p (p + q) (Nat.le_add_right p q) (a, b))]
    rw [Work.Cohomology.Kunneth.frontFace_prod_mk]
    rw [Work.Cohomology.Kunneth.fst_apply_prod]
  have hβ : Work.Cohomology.genEval R (X ⊗ Y)
        (((SSet.chainComplexMap (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y)
            (ModuleCat.of R R)).f q).hom.dualMap β)
        (Work.Cohomology.backFace (X ⊗ Y) p q (a, b))
      = Work.Cohomology.genEval R Y β (Work.Cohomology.backFace Y p q b) := by
    rw [ssetPullbackR_genEval R (X ⊗ Y) Y
      (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q β
      (Work.Cohomology.backFace (X ⊗ Y) p q (a, b))]
    rw [Work.Cohomology.Kunneth.backFace_prod_mk]
    rw [Work.Cohomology.Kunneth.snd_apply_prod]
  rw [hα, hβ]

end

end Work.Serre
