import Mathlib
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.Epic.BalancedTensor

/-!
# Silver's tensor relation for an epic ring homomorphism

If `f : R →+* S` is epic and `S` is regarded as an `(R,R)`-bimodule via `f`, then for every
`d : S` the elementary tensors `d ⊗ 1` and `1 ⊗ d` coincide in `S ⊗[R] S`:
`Work.ORHughesFree.Epic.tmul_one_eq_tmul_one_of_isEpic`.

The proof uses the trivial square-zero extension `S ⋉ (S ⊗[R] S)`: the map
`s ↦ (s, s•(1⊗1) - (1⊗1)•s)` is a ring homomorphism agreeing with the canonical inclusion on
`f '' R` (by the balance relation `s·f r ⊗ t = s ⊗ f r·t`), so epicity forces it to agree on all
of `S`.
-/

namespace Work.ORHughesFree.Epic

open BalancedTensor TrivSqZeroExt

universe u

variable {R S : Type u} [Ring R] [Ring S]

/-- The ring homomorphism `S → S ⋉ (S ⊗[R] S)`, `s ↦ (s, s•(1⊗1) - (1⊗1)•s)`, where the
trivial square-zero extension is formed with the `(S,S)`-bimodule structure on `S ⊗[R] S`. -/
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

/-- **Silver's tensor relation.**  For an epic `f : R →+* S` and every `d : S` the two elementary
tensors `d ⊗ 1` and `1 ⊗ d` agree in the `R`-balanced tensor product `S ⊗[R] S`. -/
theorem tmul_one_eq_tmul_one_of_isEpic (f : R →+* S) (hf : IsEpic f) (d : S) :
    tmul f d 1 = tmul f 1 d := by
  have hbal : ∀ r : R, twistHom f (f r) = TrivSqZeroExt.inl (f r) := by
    intro r
    refine TrivSqZeroExt.ext rfl ?_
    show f r • (tmul f 1 1) - (MulOpposite.op (f r)) • (tmul f 1 1) = 0
    rw [sub_eq_zero]
    change smulLeft f (f r) (tmul f 1 1) = smulRight f (f r) (tmul f 1 1)
    exact smulLeft_eq_smulRight_tmul_one_one f r
  have key : (twistHom f).comp f = (TrivSqZeroExt.inlHom S (BalancedTensor f)).comp f := by
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply]
    rw [hbal r, TrivSqZeroExt.inlHom_apply]
  have h_eq : twistHom f = TrivSqZeroExt.inlHom S (BalancedTensor f) :=
    hf (twistHom f) (TrivSqZeroExt.inlHom S (BalancedTensor f)) key
  have h4 : (twistHom f d).snd = (TrivSqZeroExt.inlHom S (BalancedTensor f) d).snd := by
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
