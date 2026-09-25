import Mathlib
import Submission.Work.GolodShafarevich.Setup
import Submission.Work.GolodShafarevich.RelationModule.Defs

/-!
# Injectivity of `ψ` for the identity map of a free group

For a free group `F_d`, the map
`ψ : k[F_d]^d → k[F_d]`, `x ↦ ∑ᵢ xᵢ (gᵢ - 1)`
is injective: the augmentation ideal of a free group algebra is a free left
module with basis `{gᵢ - 1}`.

The proof uses the Fox derivative, extended `k`-linearly to the whole group
algebra.  Applying the `j`-th Fox derivative to `∑ᵢ xᵢ (gᵢ - 1)` recovers the
`j`-th coordinate `xⱼ`; hence an element of the kernel is zero.
-/

open scoped MonoidAlgebra

namespace Work.GolodShafarevich.RelationModule

open Work.GolodShafarevich

variable {k : Type*} [CommRing k] {d : ℕ}

/-- The Fox derivative in the generator `i`, extended `k`-linearly to the whole
group algebra `k[F_d]`. -/
noncomputable def foxDerivLin (i : Fin d) :
    MonoidAlgebra k (FreeGroup (Fin d)) →ₗ[k] MonoidAlgebra k (FreeGroup (Fin d)) :=
  Finsupp.linearCombination k (fun w => foxDeriv k i w) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

/-- On the basis element `of w` the linear Fox derivative is `foxDeriv`. -/
theorem foxDerivLin_of (i : Fin d) (w : FreeGroup (Fin d)) :
    foxDerivLin i (MonoidAlgebra.of k (FreeGroup (Fin d)) w) = foxDeriv k i w := by
  rw [foxDerivLin, LinearMap.comp_apply]
  simp [MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single,
    Finsupp.linearCombination_single]

/-- The Fox derivative is a derivation twisted by the augmentation: the product
rule `D(a * b) = ε(b) • D a + a * D b`. -/
theorem foxDerivLin_aux_of (i : Fin d) (u : FreeGroup (Fin d))
    (b : MonoidAlgebra k (FreeGroup (Fin d))) :
    foxDerivLin i (MonoidAlgebra.of k (FreeGroup (Fin d)) u * b) =
      augAlgHom k (FreeGroup (Fin d)) b • foxDerivLin i (MonoidAlgebra.of k (FreeGroup (Fin d)) u) +
        MonoidAlgebra.of k (FreeGroup (Fin d)) u * foxDerivLin i b := by
  induction b using MonoidAlgebra.induction_on with
  | of v =>
    rw [← map_mul, foxDerivLin_of, foxDerivLin_of, foxDerivLin_of, foxDeriv_mul, augAlgHom_of,
      one_smul]
  | add x y hx hy =>
    simp only [mul_add, map_add, hx, hy, add_smul]
    abel
  | smul r x hx =>
    rw [mul_smul_comm, map_smul, hx, map_smul, map_smul, smul_eq_mul, mul_smul, mul_smul_comm,
      ← smul_add]

/-- The Leibniz rule for the linear Fox derivative. -/
theorem foxDerivLin_mul (i : Fin d) (a b : MonoidAlgebra k (FreeGroup (Fin d))) :
    foxDerivLin i (a * b) = augAlgHom k (FreeGroup (Fin d)) b • foxDerivLin i a +
      a * foxDerivLin i b := by
  induction a using MonoidAlgebra.induction_on with
  | of u => exact foxDerivLin_aux_of i u b
  | add x y hx hy =>
    simp only [add_mul, map_add, hx, hy, smul_add]
    abel
  | smul r x hx =>
    rw [smul_mul_assoc, map_smul, hx, smul_add, map_smul, smul_mul_assoc, smul_comm]

/-- For the identity map, `gGenSubOne` is `of (gᵢ) - 1`. -/
theorem gGenSubOne_id (i : Fin d) :
    gGenSubOne k (MonoidHom.id (FreeGroup (Fin d))) i =
      MonoidAlgebra.of k (FreeGroup (Fin d)) (FreeGroup.of i) - 1 := by
  rw [gGenSubOne, groupAlgMap_id]
  rfl

/-- The linear Fox derivative of `1` is `0`. -/
theorem foxDerivLin_one (j : Fin d) :
    foxDerivLin j (1 : MonoidAlgebra k (FreeGroup (Fin d))) = 0 := by
  rw [show (1 : MonoidAlgebra k (FreeGroup (Fin d))) =
      MonoidAlgebra.of k (FreeGroup (Fin d)) 1 from
        (map_one (MonoidAlgebra.of k (FreeGroup (Fin d)))).symm, foxDerivLin_of, foxDeriv_one]

/-- The linear Fox derivative of `gᵢ - 1` is `δⱼᵢ`. -/
theorem foxDerivLin_gsub1 (j i : Fin d) :
    foxDerivLin j (MonoidAlgebra.of k (FreeGroup (Fin d)) (FreeGroup.of i) - 1) =
      if j = i then 1 else 0 := by
  rw [map_sub, foxDerivLin_of, foxDerivLin_one, foxDeriv_of, sub_zero]

/-- `of (gᵢ) - 1` lies in the augmentation ideal. -/
theorem augAlgHom_gsub1 (i : Fin d) :
    augAlgHom k (FreeGroup (Fin d))
      (MonoidAlgebra.of k (FreeGroup (Fin d)) (FreeGroup.of i) - 1) = 0 :=
  (mem_augIdeal_iff k (FreeGroup (Fin d))).mp
    (of_sub_one_mem_augIdeal k (FreeGroup (Fin d)) (FreeGroup.of i))

/-- Applying the `j`-th Fox derivative to `ψ x` recovers the `j`-th coordinate. -/
theorem foxDerivLin_psi_id (j : Fin d) (x : Fin d → MonoidAlgebra k (FreeGroup (Fin d))) :
    foxDerivLin j (psi k (MonoidHom.id (FreeGroup (Fin d))) x) = x j := by
  rw [psi_apply, map_sum]
  have hterm : ∀ i, foxDerivLin j (x i * gGenSubOne k (MonoidHom.id (FreeGroup (Fin d))) i) =
      x i * (if j = i then 1 else 0) := by
    intro i
    rw [gGenSubOne_id, foxDerivLin_mul, foxDerivLin_gsub1, augAlgHom_gsub1, zero_smul, zero_add]
  simp only [hterm]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hne
    simp [Ne.symm hne]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem psi_id_injective {k : Type*} [CommRing k] {d : ℕ} :
    Function.Injective (Work.GolodShafarevich.psi k (MonoidHom.id (FreeGroup (Fin d)))) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  funext j
  have h := foxDerivLin_psi_id (k := k) j x
  rw [LinearMap.mem_ker.mp hx, map_zero] at h
  exact h.symm

end Work.GolodShafarevich.RelationModule
