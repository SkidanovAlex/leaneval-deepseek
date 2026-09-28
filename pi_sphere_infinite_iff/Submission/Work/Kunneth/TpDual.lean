import Mathlib
import Submission.Work.Kunneth.DualTens
import Submission.Work.Kunneth.tpD_comp_tpLof

/-!
# The degreewise duality `(tpC C (sumShift M))^* ≅ ctens C^* (M^*)`

`Work.Kunneth.tpDualEquiv C M n` is the degreewise-linear equivalence

`(⨁_{p+q=n} C_p ⊗ M_q →ₗ ℤ) ≃ₗ ⨁_{p+q=n} (C_p →ₗ ℤ) ⊗ (M_q →ₗ ℤ)`

which underlies the isomorphism of cochain complexes `Work.Kunneth.ctens_dual_tpC`.
It is the composite of

* `homDirectSumEquivPi` — `Hom` out of a finite direct sum is the product of the `Hom`s;
* the componentwise `Work.Kunneth.dualDistribEquivRight`;
* `DirectSum.linearEquivFunOnFintype` — a finite direct sum is its product.

The file also records the component formula `tpDualEquiv_apply_proj`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

set_option backward.isDefEq.respectTransparency false

/-- The component of the inverse of `DirectSum.linearEquivFunOnFintype`. -/
theorem linearEquivFunOnFintype_symm_apply {ι : Type*} [Fintype ι] (X : ι → Type*)
    [∀ i, AddCommMonoid (X i)] [∀ i, Module ℤ (X i)] (g : ∀ i, X i) (i : ι) :
    ((DirectSum.linearEquivFunOnFintype ℤ ι X).symm g) i = g i := rfl

variable (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
variable [∀ q, Module.Free ℤ ↥(M q)] [∀ q, Module.Finite ℤ ↥(M q)]

/-- **The degreewise duality** of the tensor product chain complex with the "no differential"
family `sumShift M`: the `ℤ`-dual of `⨁_{p+q=n} C_p ⊗ M_q` is `⨁_{p+q=n} C_p^* ⊗ M_q^*`. -/
def tpDualEquiv (n : ℕ) :
    (tpX C (sumShift M) n →ₗ[ℤ] ℤ) ≃ₗ[ℤ]
      ctensX (Work.Cohomology.dualComplex ℤ C) (homDual M) n :=
  (homDirectSumEquivPi ℤ (tpIdx n) (fun pq => tpSummand C (sumShift M) pq.1.1 pq.1.2) ℤ).trans
    ((LinearEquiv.piCongrRight
        (fun pq : tpIdx n => dualDistribEquivRight ↥(C.X pq.1.1) ↥(M pq.1.2))).trans
      (DirectSum.linearEquivFunOnFintype ℤ (tpIdx n)
        (fun pq : tpIdx n =>
          ↥((Work.Cohomology.dualComplex ℤ C).X pq.1.1 ⊗ homDual M pq.1.2))).symm)

/-- The `pq`-component of `tpDualEquiv`: the pairing of the `pq`-component of the functional with
the summand `C_p ⊗ M_q`. -/
theorem tpDualEquiv_apply_proj (n : ℕ) (f : tpX C (sumShift M) n →ₗ[ℤ] ℤ) (pq : tpIdx n) :
    tpDualEquiv C M n f pq
      = dualDistribEquivRight ↥(C.X pq.1.1) ↥(M pq.1.2)
          (f.comp (tpLof C (sumShift M) n pq)) := by
  simp only [tpDualEquiv, LinearEquiv.trans_apply, linearEquivFunOnFintype_symm_apply,
    LinearEquiv.piCongrRight_apply, homDirectSumEquivPi_apply]
  rfl

/-! ## The `sumShift` differentials of `tpDpq` -/

/-- At a bidegree whose first coordinate is positive, the Koszul differential against `sumShift M`
is `∂_C ⊗ 1`: the second (Koszul) term vanishes because `sumShift M` has zero differential. -/
theorem tpDpq_sumShift_tpStep (n : ℕ) (pq : tpIdx n) :
    tpDpq C (sumShift M) n (tpStep n pq)
      = (tpLof C (sumShift M) n pq).comp
          (TensorProduct.map ((C.d (pq.1.1 + 1) pq.1.1).hom) (LinearMap.id)) := by
  rw [tpDpq]
  rw [dif_pos (show 1 ≤ pq.1.1 + 1 by omega)]
  split_ifs with hq
  · have h1 := sumShift_d M (pq.1.2 - 1)
    rw [Nat.sub_add_cancel hq] at h1
    rw [h1, ModuleCat.hom_zero, TensorProduct.map_zero_right, LinearMap.comp_zero]
    exact add_zero _
  · exact add_zero _

/-- At the bidegree `(0, n+1)` the Koszul differential against `sumShift M` vanishes. -/
theorem tpDpq_sumShift_tpZero (n : ℕ) :
    tpDpq C (sumShift M) n (tpZero n) = 0 := by
  rw [tpDpq]
  rw [dif_neg (show ¬ (1 ≤ (0:ℕ)) by omega), zero_add]
  rw [dif_pos (show 1 ≤ n + 1 by omega)]
  have hz : (ModuleCat.Hom.hom ((sumShift M).d (n + 1) (n + 1 - 1))) = 0 := by
    rw [show (sumShift M).d (n + 1) (n + 1 - 1) = 0 from by
      rw [show n + 1 - 1 = n from Nat.add_sub_cancel n 1, sumShift_d]]
    rfl
  rw [hz, TensorProduct.map_zero_right, LinearMap.comp_zero]
  simp

/-! ## Small identifications -/

/-- The differential of the dual complex is the transpose of the differential of `C`. -/
theorem dualComplex_d_hom (p : ℕ) :
    ((Work.Cohomology.dualComplex ℤ C).d p (p + 1)).hom
      = LinearMap.dualMap ((C.d (p + 1) p).hom) := by
  simp only [Work.Cohomology.dualComplex, CochainComplex.of_d, Work.Cohomology.dualDiff,
    ModuleCat.hom_ofHom]
  rfl

/-- `TensorProduct.map f 1` is `LinearMap.rTensor` applied to `f`. -/
theorem tensorProduct_map_id_eq_rTensor {A A' N : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup A'] [Module ℤ A'] [AddCommGroup N] [Module ℤ N] (f : A →ₗ[ℤ] A') :
    TensorProduct.map f (LinearMap.id : N →ₗ[ℤ] N) = LinearMap.rTensor N f := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [TensorProduct.map_tmul, LinearMap.rTensor_tmul]
  | add x y hx hy => simp [hx, hy]

end

end Work.Kunneth
