/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fox derivatives from `FreeGroupAugIdealBasis`

From the hypothesis `FreeGroupAugIdealBasis k` (the augmentation ideal of a free group algebra is
free on the elements `x - 1`) we obtain, for `F = FreeGroup (Fin n)`,

* the linear equivalence `foxEquiv : (Fin n →₀ k[F]) ≃ₗ[k[F]] augIdeal k F`;
* the Fox derivative `foxDelta m` of a free group element `m`, characterised by
  `∑ i, foxDelta m i * (xᵢ - 1) = m - 1`, together with the cocycle rule
  `foxDelta (a * b) = single a 1 • foxDelta b + foxDelta a`;
* the `k`-linear extension `foxD` of `foxDelta` to `k[F]`, with
  `∑ i, foxD a i * (xᵢ - 1) = a - aug(a) • 1`.
-/
import Mathlib
import Submission.Work.ORFP2.ExtSetup

set_option autoImplicit false

namespace Work.ORFP2.Ext

open MonoidAlgebra

variable (k : Type*) [CommRing k] {n : ℕ} {G : Type*} [Group G]

section Fox

variable (hbasis : FreeGroupAugIdealBasis k)

/-- The `k[F]`-linear equivalence `(Fin n →₀ k[F]) ≃ₗ augIdeal k F` provided by the basis
hypothesis. -/
noncomputable def foxEquiv (n : ℕ) :
    (Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) ≃ₗ[MonoidAlgebra k (FreeGroup (Fin n))]
      augIdeal k (FreeGroup (Fin n)) :=
  Classical.choose (hbasis (Fin n))

lemma foxEquiv_apply (n : ℕ) (c : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    ((foxEquiv k hbasis n c : augIdeal k (FreeGroup (Fin n))) :
        MonoidAlgebra k (FreeGroup (Fin n)))
      = c.sum (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)) :=
  Classical.choose_spec (hbasis (Fin n)) c

/-- The Fox derivative of a free group element. -/
noncomputable def foxDelta (n : ℕ) (m : FreeGroup (Fin n)) :
    Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n)) :=
  (foxEquiv k hbasis n).symm
    ⟨MonoidAlgebra.single m (1 : k) - 1,
      single_sub_one_mem_augIdeal k (FreeGroup (Fin n)) m⟩

lemma foxEquiv_foxDelta (n : ℕ) (m : FreeGroup (Fin n)) :
    foxEquiv k hbasis n (foxDelta k hbasis n m) =
      ⟨MonoidAlgebra.single m (1 : k) - 1,
        single_sub_one_mem_augIdeal k (FreeGroup (Fin n)) m⟩ :=
  (foxEquiv k hbasis n).apply_symm_apply _

lemma foxDelta_sum (n : ℕ) (m : FreeGroup (Fin n)) :
    (foxDelta k hbasis n m).sum
        (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1))
      = MonoidAlgebra.single m (1 : k) - 1 := by
  rw [← foxEquiv_apply k hbasis n]
  exact congrArg Subtype.val (foxEquiv_foxDelta k hbasis n m)

lemma foxDelta_mul (n : ℕ) (a b : FreeGroup (Fin n)) :
    foxDelta k hbasis n (a * b) =
      (MonoidAlgebra.single a (1 : k)) • foxDelta k hbasis n b
        + foxDelta k hbasis n a := by
  apply (foxEquiv k hbasis n).injective
  rw [map_add, map_smul]
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
  rw [foxEquiv_foxDelta k hbasis n (a * b)]
  have hb := congrArg Subtype.val (foxEquiv_foxDelta k hbasis n b)
  have ha := congrArg Subtype.val (foxEquiv_foxDelta k hbasis n a)
  simp only at hb ha
  rw [hb, ha, mul_sub, mul_one, single_mul_single, mul_one]
  abel

lemma foxDelta_one (n : ℕ) : foxDelta k hbasis n (1 : FreeGroup (Fin n)) = 0 := by
  have h := foxDelta_mul k hbasis n (1 : FreeGroup (Fin n)) 1
  simp only [mul_one] at h
  rw [show (MonoidAlgebra.single (1 : FreeGroup (Fin n)) (1 : k) :
      MonoidAlgebra k (FreeGroup (Fin n))) = 1 from MonoidAlgebra.one_def.symm, one_smul] at h
  have h2 : foxDelta k hbasis n 1 + foxDelta k hbasis n 1
      = foxDelta k hbasis n 1 + 0 := by rw [add_zero, ← h]
  exact add_left_cancel h2

/-- The `k[F]`-linear map `c ↦ ∑ i, c i * (xᵢ - 1)`; its range is the augmentation ideal. -/
noncomputable def foxLambda (n : ℕ) :
    (Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) →ₗ[MonoidAlgebra k (FreeGroup (Fin n))]
      MonoidAlgebra k (FreeGroup (Fin n)) :=
  Finsupp.linearCombination (MonoidAlgebra k (FreeGroup (Fin n)))
    (fun i => MonoidAlgebra.single (FreeGroup.of i) (1 : k) - 1)

lemma foxLambda_apply (n : ℕ) (c : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    foxLambda k n c = c.sum (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)) := by
  rw [foxLambda, Finsupp.linearCombination_apply]
  exact Finsupp.sum_congr fun a _ => by rw [smul_eq_mul]

lemma foxEquiv_eq_foxLambda (n : ℕ) (c : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    ((foxEquiv k hbasis n c : augIdeal k (FreeGroup (Fin n))) :
        MonoidAlgebra k (FreeGroup (Fin n))) = foxLambda k n c := by
  rw [foxEquiv_apply, foxLambda_apply]

lemma foxLambda_foxDelta (n : ℕ) (m : FreeGroup (Fin n)) :
    foxLambda k n (foxDelta k hbasis n m) = MonoidAlgebra.single m (1 : k) - 1 := by
  rw [foxLambda_apply]
  exact foxDelta_sum k hbasis n m

/-- The Fox derivative of an element of `k[F]`, extended `k`-linearly. -/
noncomputable def foxD (n : ℕ) :
    MonoidAlgebra k (FreeGroup (Fin n)) →ₗ[k] (Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :=
  (Finsupp.linearCombination k (fun w : FreeGroup (Fin n) => foxDelta k hbasis n w)).comp
    ((MonoidAlgebra.coeffLinearEquiv k).toLinearMap.restrictScalars k)

lemma foxD_single (n : ℕ) (w : FreeGroup (Fin n)) (c : k) :
    foxD k hbasis n (MonoidAlgebra.single w c) = c • foxDelta k hbasis n w := by
  have h : (MonoidAlgebra.coeffLinearEquiv k) (MonoidAlgebra.single w c)
      = Finsupp.single w c := MonoidAlgebra.coeff_single w c
  change (Finsupp.linearCombination k (fun w : FreeGroup (Fin n) => foxDelta k hbasis n w))
      ((MonoidAlgebra.coeffLinearEquiv k) (MonoidAlgebra.single w c)) = _
  rw [h, Finsupp.linearCombination_single]

lemma foxLambda_smul (n : ℕ) (c : k) (L : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    foxLambda k n (c • L) = c • foxLambda k n L := by
  rw [← IsScalarTower.algebraMap_smul
        (MonoidAlgebra k (FreeGroup (Fin n))) c L,
    LinearMap.map_smul (foxLambda k n)
      (algebraMap k (MonoidAlgebra k (FreeGroup (Fin n))) c) L,
    IsScalarTower.algebraMap_smul (MonoidAlgebra k (FreeGroup (Fin n))) c]

lemma foxD_eq_sum (n : ℕ) (a : MonoidAlgebra k (FreeGroup (Fin n))) :
    foxD k hbasis n a = ∑ w ∈ a.coeff.support, a.coeff w • foxDelta k hbasis n w := by
  change (Finsupp.linearCombination k (fun w : FreeGroup (Fin n) => foxDelta k hbasis n w))
      ((MonoidAlgebra.coeffLinearEquiv k) a) = _
  rw [MonoidAlgebra.coeffLinearEquiv_apply, Finsupp.linearCombination_apply, Finsupp.sum]

/-- The fundamental identity of Fox calculus: `∑ i, foxD a i * (xᵢ - 1) = a - aug(a) • 1`. -/
lemma foxLambda_foxD (n : ℕ) (a : MonoidAlgebra k (FreeGroup (Fin n))) :
    foxLambda k n (foxD k hbasis n a) = a - (Work.ORFP2.augmentation k (FreeGroup (Fin n)) a) • 1 := by
  rw [foxD_eq_sum, map_sum]
  have step1 : (∑ w ∈ a.coeff.support, foxLambda k n (a.coeff w • foxDelta k hbasis n w))
      = ∑ w ∈ a.coeff.support, a.coeff w • (MonoidAlgebra.single w (1 : k) - 1) :=
    Finset.sum_congr rfl fun w _ => by rw [foxLambda_smul, foxLambda_foxDelta]
  rw [step1]
  have step2 : (∑ w ∈ a.coeff.support, a.coeff w • (MonoidAlgebra.single w (1 : k) - 1))
      = (∑ w ∈ a.coeff.support, a.coeff w •
            (MonoidAlgebra.single w (1 : k) : MonoidAlgebra k (FreeGroup (Fin n))))
          - ∑ w ∈ a.coeff.support, a.coeff w • (1 : MonoidAlgebra k (FreeGroup (Fin n))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => smul_sub (a.coeff w) _ _
  rw [step2, ← Finset.sum_smul]
  congr 1
  · exact (Work.ORFP2.eq_sum_smul_single k (FreeGroup (Fin n)) a).symm
  · congr 1
    rw [Work.ORFP2.augmentation_eq_sum_coeff, Finsupp.sum]

lemma foxD_foxLambda (n : ℕ) (w : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    foxD k hbasis n (foxLambda k n w) = w := by
  have hmem : foxLambda k n w ∈ augIdeal k (FreeGroup (Fin n)) := by
    rw [← foxEquiv_eq_foxLambda k hbasis n]
    exact (foxEquiv k hbasis n w).2
  have hz : Work.ORFP2.augmentation k (FreeGroup (Fin n)) (foxLambda k n w) = 0 := by
    have h := Work.ORFP2.augIdeal_le_ker_augmentation k (FreeGroup (Fin n)) hmem
    rwa [RingHom.mem_ker] at h
  have key : foxLambda k n (foxD k hbasis n (foxLambda k n w)) = foxLambda k n w := by
    rw [foxLambda_foxD, hz, zero_smul, sub_zero]
  have h' : foxEquiv k hbasis n (foxD k hbasis n (foxLambda k n w)) = foxEquiv k hbasis n w := by
    apply Subtype.ext
    rw [foxEquiv_eq_foxLambda k hbasis n, foxEquiv_eq_foxLambda k hbasis n]
    exact key
  exact (foxEquiv k hbasis n).injective h'

lemma foxD_smul_augIdeal (n : ℕ) (a : MonoidAlgebra k (FreeGroup (Fin n)))
    (x : augIdeal k (FreeGroup (Fin n))) :
    foxD k hbasis n (a • (x : MonoidAlgebra k (FreeGroup (Fin n))))
      = a • foxD k hbasis n (x : MonoidAlgebra k (FreeGroup (Fin n))) := by
  have hx0 : Work.ORFP2.augmentation k (FreeGroup (Fin n))
      (x : MonoidAlgebra k (FreeGroup (Fin n))) = 0 := by
    have h := Work.ORFP2.augIdeal_le_ker_augmentation k (FreeGroup (Fin n)) x.2
    rwa [RingHom.mem_ker] at h
  have hax0 : Work.ORFP2.augmentation k (FreeGroup (Fin n))
      (a • (x : MonoidAlgebra k (FreeGroup (Fin n)))) = 0 := by
    rw [smul_eq_mul, map_mul, hx0, mul_zero]
  have key : foxLambda k n (foxD k hbasis n (a • (x : MonoidAlgebra k (FreeGroup (Fin n)))))
      = foxLambda k n (a • foxD k hbasis n (x : MonoidAlgebra k (FreeGroup (Fin n)))) := by
    rw [foxLambda_foxD,
      LinearMap.map_smul (foxLambda k n) a
        (foxD k hbasis n (x : MonoidAlgebra k (FreeGroup (Fin n)))),
      foxLambda_foxD, hx0, hax0]
    simp only [zero_smul, sub_zero]
  have h' : foxEquiv k hbasis n (foxD k hbasis n (a • (x : MonoidAlgebra k (FreeGroup (Fin n)))))
      = foxEquiv k hbasis n (a • foxD k hbasis n (x : MonoidAlgebra k (FreeGroup (Fin n)))) := by
    apply Subtype.ext
    rw [foxEquiv_eq_foxLambda k hbasis n, foxEquiv_eq_foxLambda k hbasis n]
    exact key
  exact (foxEquiv k hbasis n).injective h'

lemma foxD_sub_one (n : ℕ) (r : FreeGroup (Fin n)) :
    foxD k hbasis n (MonoidAlgebra.single r (1 : k) - 1) = foxDelta k hbasis n r := by
  rw [map_sub, foxD_single, one_smul,
    show (1 : MonoidAlgebra k (FreeGroup (Fin n))) = MonoidAlgebra.single 1 (1 : k) from
      MonoidAlgebra.one_def,
    foxD_single, one_smul, foxDelta_one, sub_zero]

end Fox

end Work.ORFP2.Ext
