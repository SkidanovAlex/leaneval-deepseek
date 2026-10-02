import Mathlib
import Submission.Work.Whitney.ConjDefs
import Submission.Work.Whitney.ConjChern
import Submission.Work.Thom.complexification

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The complexification of a real bundle is self-conjugate

For a real bundle `Z`, the complexification `Z ⊗_ℝ ℂ` is isomorphic — indeed *equal* as gluing data
— to its own conjugate bundle: the transition functions of the complexification are the
complexifications `cxTrans (g)` of the real transition functions `g`, and conjugation of an
endomorphism commutes with `cxTrans` (because `cxTrans` is `g ⊗ id_ℂ` and conjugation is the identity
on the `ℝ`-factor).

Consequences (used by the 2-torsion bookkeeping of the Pontryagin classes, see
`Submission/Work/Whitney/README.md`, ADDENDUM W3):

* `Work.Whitney.conjCore_complexificationCore` — the two cores are equal;
* `Work.Whitney.chernClass_complexification_add_self` — for odd `j`,
  `c_j(Z ⊗_ℝ ℂ) + c_j(Z ⊗_ℝ ℂ) = 0`, i.e. all odd Chern classes of a complexified real bundle are
  2-torsion (the classical fact behind the 2-torsion correction of `p₁(E ⊕ F) = p₁E + p₁F`);
* `Work.Whitney.two_smul_chernClass_complexification` — the same as `2 • c_j = 0`.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-! ## Conjugation commutes with the complexification of a real endomorphism -/

/-- **Conjugation commutes with `cxTrans`**: the complexification `g ⊗ id_ℂ` of a real endomorphism
`g` is invariant under the conjugation of endomorphisms. -/
theorem conjC_cxTrans_conjC {k : ℕ}
    (T : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (v : EuclideanSpace ℂ (Fin k)) :
    conjC k (cxTrans T (conjC k v)) = cxTrans T v := by
  simp only [cxTrans_apply, cxRePart_conjC, cxImPart_conjC, map_neg, map_add,
    conjC_cxOfReal, conjC_cxMulI]
  abel

/-- **Conjugation of endomorphisms fixes `cxTrans T`.** -/
theorem conjCLM_cxTrans {k : ℕ}
    (T : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    conjCLM k (cxTrans T) = cxTrans T := by
  apply ContinuousLinearMap.ext
  intro v
  rw [conjCLM_apply]
  exact conjC_cxTrans_conjC T v

/-! ## The complexification is self-conjugate -/

/-- **The complexification of a real bundle is its own conjugate bundle** (an equality of gluing
data, not only an isomorphism). -/
theorem conjCore_complexificationCore {k : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    conjCore (complexificationCore Z) = complexificationCore Z := by
  refine bundleCore_ext rfl rfl (fun i j x => ?_)
  rw [conjCore_coordChange]
  apply ContinuousLinearMap.ext
  intro v
  rw [conjCLM_apply, congrFun (complexificationCore_coordChange Z i j x) (conjC k v)]
  rw [conjC_cxTrans_conjC]
  exact (congrFun (complexificationCore_coordChange Z i j x) v).symm

/-! ## The odd Chern classes of a complexification are 2-torsion -/

variable [Fintype ι]

/-- **The odd Chern classes of a complexified real bundle are the negatives of themselves**: for odd
`j`, `c_j(Z ⊗_ℝ ℂ) = - c_j(Z ⊗_ℝ ℂ)` (the conjugation sign rule along the self-conjugacy of the
complexification). -/
theorem chernClass_complexification_eq_neg_self {k j : ℕ} (hj : Odd j)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    chernClass k j (complexificationCore Z) = - chernClass k j (complexificationCore Z) := by
  have h := chernClass_conjCore k (complexificationCore Z) j
  rw [conjCore_complexificationCore] at h
  rw [hj.neg_one_pow] at h
  simpa using h

/-- **The odd Chern classes of a complexified real bundle are 2-torsion**, in the additivity
normalisation: `c_j(Z ⊗_ℝ ℂ) + c_j(Z ⊗_ℝ ℂ) = 0` for odd `j`. -/
theorem chernClass_complexification_add_self {k j : ℕ} (hj : Odd j)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    chernClass k j (complexificationCore Z) + chernClass k j (complexificationCore Z) = 0 := by
  have h := chernClass_complexification_eq_neg_self (B := B) hj Z
  nth_rewrite 1 [h]
  exact neg_add_cancel _

end

end Work.Whitney
