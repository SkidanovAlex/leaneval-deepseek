import Mathlib
import Submission.Work.Whitney.TCMQDefs
import Submission.Work.Whitney.TripleRel
import Submission.Work.Whitney.pd3InclRelR_quasiIso
import Submission.Work.Whitney.tcmRelCup_tripleImage_agreeA
import Submission.Work.Whitney.tcmRelCup_tripleImage_agree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-
# Auxiliaries for the associativity of the canonical relative–relative cup

This module collects everything the final assembly of `Work.Whitney.tcmRelCupAssoc` needs, apart
from the two delegated comparison lemmas:

* `tcmRelCup_gauge` — the gauge equation of the canonical cup;
* `pd3InclRelR_injective` — injectivity of `H^*(X,A∪B∪C) → H^*(X,A+B+C)` (from the quasi-isomorphism
  `Work.Whitney.pd3InclRelR_quasiIso`);
* `eqRec_homologyMap` — degree transport commutes with the map induced by a cochain map;
* `pd3InclRelR_factor_left` — the factorisation of `pd3InclRelR` through `pdABInclRelR (A∪B) C`;
* `eqRec_swap` — the degree and set transports of a class commute.
-/

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **The gauge equation of the canonical relative–relative cup**: the A+B-projection of the
canonical cup is the Alexander–Whitney product of the two classes. -/
theorem tcmRelCup_gauge (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh ℤ m X A) (b : Work.Thom.RelCoh ℤ n X B) :
    (HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) (TopCat.of X) A B) (m + n)).hom
        (tcmRelCup A B hA hB m n a b)
      = relRelCupHMap (TopCat.of X) A B m n a b := by
  rw [tcmRelCup, tcmRelCupG_apply]
  exact tcmRelCupInv_spec (R := ℤ) A B hA hB (m + n) _

/-- **Injectivity of the inclusion of the relative complex of the union into the three-fold
intersection complex** (the form in which the associativity of `tcmRelCup` uses the three-fold
small-chains theorem `pd3InclRelR_quasiIso`). -/
theorem pd3InclRelR_injective (A B C : Set X) (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C)
    (n : ℕ) :
    Function.Injective (fun x =>
      (HomologicalComplex.homologyMap (pd3InclRelR (TopCat.of X) A B C) n).hom x) := by
  haveI : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (pd3InclRelR (TopCat.of X) A B C) n) :=
    pd3InclRelR_quasiIso (TopCat.of X) A B C hA hB hC n
  exact (ConcreteCategory.bijective_of_isIso _).1

/-- Transporting a homology class along an equality of degrees commutes with the map induced by a
morphism of cochain complexes. -/
theorem eqRec_homologyMap {K L : CochainComplex (ModuleCat ℤ) ℕ} (ψ : K ⟶ L) {m m' : ℕ}
    (h : m = m') (x : K.homology m) :
    h ▸ ((HomologicalComplex.homologyMap ψ m).hom x)
      = (HomologicalComplex.homologyMap ψ m').hom (h ▸ x) := by
  cases h
  rfl

end

end Work.Whitney
