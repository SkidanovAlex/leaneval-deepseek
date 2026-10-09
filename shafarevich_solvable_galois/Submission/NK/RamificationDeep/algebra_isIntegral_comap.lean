/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `A` is integral over `A ∩ K` when `A` is Galois stable

Let `K ⊆ L` be a finite Galois extension and `A` a valuation subring of `L` whose decomposition
subgroup is all of `Gal(L/K)` (i.e. `A` is stable under every `K`-automorphism of `L`).  Write
`𝔬 = A.comap (algebraMap K L) = A ∩ K`.  Then every element of `A` is integral over `𝔬`.

The proof is the classical one: for `y ∈ A` the conjugates `σ y` (`σ ∈ Gal(L/K)`) all lie in `A`,
so the product `Π_σ (X - σ y)` — equivalently, since `L/K` is separable, the image in `L[X]` of
the minimal polynomial `minpoly K y` — has all its coefficients in `A`.  Those coefficients lie in
`K`, hence in `𝔬`, and `minpoly K y` is monic of which `y` is a root; this transfers back through
`MonoDefs`'s `𝔬 → A` to integrality of `y` over `𝔬`.
-/
import Mathlib
import Submission.NK.RamificationDeep.MonoDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.RamificationDeep

open scoped Pointwise
open Polynomial

/-- If every element of a finite set `s ⊆ L` lies in a valuation subring `A` of `L`, then every
coefficient of `∏ z ∈ s, (X - C z)` lies in `A`. -/
lemma prod_X_sub_C_coeff_mem {L : Type*} [Field L] (A : ValuationSubring L) (s : Finset L)
    (hs : ∀ z ∈ s, z ∈ A) (k : ℕ) :
    (∏ z ∈ s, (Polynomial.X - Polynomial.C z)).coeff k ∈ A := by
  classical
  -- Lift the product to the subring `A` and push it forward along the inclusion.
  have key : ∃ uS : (A.toSubring)[X],
      uS.map (Subring.subtype A.toSubring) = ∏ z ∈ s, (Polynomial.X - Polynomial.C z) := by
    induction s using Finset.induction with
    | empty => exact ⟨1, by simp⟩
    | insert a s ha ih =>
      have hsS : ∀ z ∈ s, z ∈ A.toSubring := fun z hz => hs z (Finset.mem_insert_of_mem hz)
      obtain ⟨uS, huS⟩ := ih hsS
      refine ⟨(Polynomial.X - Polynomial.C ⟨a, hs a (Finset.mem_insert_self a s)⟩) * uS, ?_⟩
      rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, huS,
        Finset.prod_insert ha]
      rfl
  obtain ⟨uS, huS⟩ := key
  have hcoe : (∏ z ∈ s, (Polynomial.X - Polynomial.C z)).coeff k = (uS.coeff k : L) := by
    rw [← huS, Polynomial.coeff_map]
    rfl
  rw [hcoe]
  exact (uS.coeff k).2

theorem algebra_isIntegral_comap {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A] [FiniteDimensional K L] [IsGalois K L] (hA : A.decompositionSubgroup K = ⊤) : Algebra.IsIntegral ↥(A.comap (algebraMap K L)) ↥A := by
  classical
  have hfin : Fintype (L ≃ₐ[K] L) := AlgEquiv.fintype K L
  rw [Algebra.isIntegral_iff]
  intro y
  -- It suffices to prove integrality of the image in `L`.
  have hcore : IsIntegral ↥(A.comap (algebraMap K L)) (algebraMap ↥A L y) := by
    set yL : L := algebraMap ↥A L y with hyL
    have hyLmem : yL ∈ A := y.2
    -- every conjugate of `yL` lies in `A`, since `A` is stable under `Gal(L/K)`.
    have hcarrier : ∀ z ∈ (ConjRootClass.mk K yL).carrier, z ∈ A := by
      intro z hz
      rw [ConjRootClass.mem_carrier] at hz
      rw [ConjRootClass.mk_eq_mk] at hz
      obtain ⟨σ, hσ⟩ := isConjRoot_iff_exists_algEquiv.mp hz
      rw [← hσ]
      have hσA : σ • A = A := by
        rw [← MulAction.mem_stabilizer_iff, ← ValuationSubring.decompositionSubgroup, hA]
        exact Subgroup.mem_top σ
      rw [← hσA]
      exact Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr
        (by simpa [AlgEquiv.smul_def] using hyLmem)
    -- the minimal polynomial splits into linear factors over the conjugates.
    have hprod : (minpoly K yL).map (algebraMap K L)
        = ∏ z ∈ (ConjRootClass.mk K yL).carrier.toFinset, (Polynomial.X - Polynomial.C z) := by
      simpa using ConjRootClass.minpoly.map_eq_prod (ConjRootClass.mk K yL)
    -- hence its coefficients lie in `A ∩ K`.
    have hcoeff : ∀ k, (minpoly K yL).coeff k ∈ A.comap (algebraMap K L) := by
      intro k
      rw [ValuationSubring.mem_comap]
      have h1 : ((minpoly K yL).map (algebraMap K L)).coeff k ∈ A := by
        rw [hprod]
        exact prod_X_sub_C_coeff_mem A (ConjRootClass.mk K yL).carrier.toFinset
          (fun z hz => hcarrier z (Set.mem_toFinset.mp hz)) k
      rwa [Polynomial.coeff_map] at h1
    -- transport `minpoly K yL` back to a monic polynomial over `A ∩ K` with root `yL`.
    let q : Polynomial ↥(A.comap (algebraMap K L)) :=
      ∑ k ∈ (minpoly K yL).support,
        Polynomial.C ⟨(minpoly K yL).coeff k, hcoeff k⟩ * Polynomial.X ^ k
    have hqmap : q.map (algebraMap ↥(A.comap (algebraMap K L)) K) = minpoly K yL := by
      have h1 : q.map (algebraMap ↥(A.comap (algebraMap K L)) K)
          = ∑ x ∈ (minpoly K yL).support,
              Polynomial.C ((minpoly K yL).coeff x) * Polynomial.X ^ x := by
        simp only [q, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
          Polynomial.map_X, ValuationSubring.algebraMap_apply]
      rw [h1, show (∑ x ∈ (minpoly K yL).support,
              Polynomial.C ((minpoly K yL).coeff x) * Polynomial.X ^ x)
          = (minpoly K yL).sum (fun n a => Polynomial.C a * Polynomial.X ^ n) from by
            rw [Polynomial.sum_def],
        Polynomial.sum_C_mul_X_pow_eq]
    refine ⟨q, ?_, ?_⟩
    · refine Polynomial.monic_of_injective (f := algebraMap ↥(A.comap (algebraMap K L)) K)
        (fun a b h => Subtype.ext (by simpa using h)) ?_
      rw [hqmap]
      exact minpoly.monic ((Algebra.IsIntegral.of_finite K L).isIntegral yL)
    · rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K yL q, hqmap]
      exact minpoly.aeval K yL
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom _ _ _) (fun a b h => Subtype.ext h)).mp hcore

end NK.RamificationDeep
