import Mathlib
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.Epic.BalancedTensor

/-!
# Silver's tensor relation for an epic ring homomorphism

If `f : R →+* S` is epic (`Work.ORHughesFree.IsEpic f`, i.e. `f` is right cancellable) and `S` is
regarded as an `(R,R)`-bimodule via `f`, then for every `d : S` the elementary tensors
`d ⊗ 1` and `1 ⊗ d` agree in the `R`-balanced tensor product `S ⊗[R] S`:

`Work.ORHughesFree.Epic.tmul_eq_of_isEpic`.

This is the Isbell–Silver–Mazet tensor criterion for epimorphisms, in the easy direction
(epimorphism `⟹` the tensor relation).  The proof uses the trivial square-zero extension
`S ⋉ (S ⊗[R] S)`: the map `s ↦ (s, s•(1⊗1) - (1⊗1)•s)` is a ring homomorphism which agrees with
the canonical inclusion `S → S ⋉ (S ⊗[R] S)` on `f '' R`, because for `r : R` the balance relation
`s·f r ⊗ t = s ⊗ f r·t` gives `f r ⊗ 1 = 1 ⊗ f r` in `S ⊗[R] S`.  Epicity of `f` then forces the
two homomorphisms to agree on all of `S`, and reading off the second coordinate of the value at
`d` gives `d•(1⊗1) = (1⊗1)•d`, i.e. `d ⊗ 1 = 1 ⊗ d`.
-/

namespace Work.ORHughesFree.Epic

namespace TmulEpicAux

open BalancedTensor TrivSqZeroExt

variable {R S : Type} [Ring R] [Ring S]

/-- The ring homomorphism `S → S ⋉ (S ⊗[R] S)`, `s ↦ (s, s•(1⊗1) - (1⊗1)•s)`, where the trivial
square-zero extension is formed with the `(S,S)`-bimodule structure on `S ⊗[R] S`.  It is a ring
homomorphism because the left and right `S`-actions on `S ⊗[R] S` commute. -/
noncomputable def twistHom (f : R →+* S) :
    S →+* TrivSqZeroExt S (BalancedTensor f) where
  toFun s := (s, s • (tmul f 1 1) - (MulOpposite.op s) • (tmul f 1 1))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' := by
    intro a b
    refine TrivSqZeroExt.ext rfl ?_
    show (a * b) • (tmul f 1 1) - (MulOpposite.op (a * b)) • (tmul f 1 1)
      = a • (b • (tmul f 1 1) - (MulOpposite.op b) • (tmul f 1 1))
        + (MulOpposite.op b) • (a • (tmul f 1 1) - (MulOpposite.op a) • (tmul f 1 1))
    simp only [smul_sub, mul_smul, MulOpposite.op_mul]
    rw [smul_comm a (MulOpposite.op b) (tmul f 1 1)]
    abel
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' := by
    intro a b
    refine TrivSqZeroExt.ext rfl ?_
    show (a + b) • (tmul f 1 1) - (MulOpposite.op (a + b)) • (tmul f 1 1)
      = (a • (tmul f 1 1) - (MulOpposite.op a) • (tmul f 1 1))
        + (b • (tmul f 1 1) - (MulOpposite.op b) • (tmul f 1 1))
    rw [add_smul, MulOpposite.op_add, add_smul]
    abel

@[simp]
theorem twistHom_apply (f : R →+* S) (s : S) :
    twistHom f s = (s, s • (tmul f 1 1) - (MulOpposite.op s) • (tmul f 1 1)) := rfl

end TmulEpicAux

open BalancedTensor TrivSqZeroExt

/-- **Silver's tensor relation.**  For an epic `f : R →+* S` and every `d : S` the two elementary
tensors `d ⊗ 1` and `1 ⊗ d` agree in the `R`-balanced tensor product `S ⊗[R] S`. -/
theorem tmul_eq_of_isEpic {R S : Type} [Ring R] [Ring S] (f : R →+* S)
    (hf : Work.ORHughesFree.IsEpic f) (d : S) :
    Work.ORHughesFree.Epic.BalancedTensor.tmul f d 1 = Work.ORHughesFree.Epic.BalancedTensor.tmul f 1 d := by
  have hbal : ∀ r : R, TmulEpicAux.twistHom f (f r) = TrivSqZeroExt.inl (f r) := by
    intro r
    refine TrivSqZeroExt.ext rfl ?_
    show f r • (tmul f 1 1) - (MulOpposite.op (f r)) • (tmul f 1 1) = 0
    rw [sub_eq_zero]
    change smulLeft f (f r) (tmul f 1 1) = smulRight f (f r) (tmul f 1 1)
    exact smulLeft_eq_smulRight_tmul_one_one f r
  have key : (TmulEpicAux.twistHom f).comp f
      = (TrivSqZeroExt.inlHom S (BalancedTensor f)).comp f := by
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply]
    rw [hbal r, TrivSqZeroExt.inlHom_apply]
  have h_eq : TmulEpicAux.twistHom f = TrivSqZeroExt.inlHom S (BalancedTensor f) :=
    hf (TmulEpicAux.twistHom f) (TrivSqZeroExt.inlHom S (BalancedTensor f)) key
  have h4 : (TmulEpicAux.twistHom f d).snd
      = (TrivSqZeroExt.inlHom S (BalancedTensor f) d).snd := by
    rw [h_eq]
  have h5 : d • (tmul f 1 1) - (MulOpposite.op d) • (tmul f 1 1) = 0 := by
    have h4' : (TrivSqZeroExt.inlHom S (BalancedTensor f) d).snd = 0 := by simp
    rw [h4'] at h4
    exact h4
  have h6 : d • (tmul f 1 1) = (MulOpposite.op d) • (tmul f 1 1) := sub_eq_zero.mp h5
  change smulLeft f d (tmul f 1 1) = smulRight f d (tmul f 1 1) at h6
  rw [smulLeft_tmul, smulRight_tmul] at h6
  simpa using h6

end Work.ORHughesFree.Epic
