import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.SplitPrimes
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
import Submission.Commons.FieldTheory.Galois.exists_finite_galois_containing
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The place realization of `σ` determines `ϕ`

If a base-field mapping isomorphism `σ : K₂' ≃+* K₁'` realizes the place correspondence `a` of a
group isomorphism `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` — i.e. `(a.placeMap A).comap σ.symm = A` for
every finite place `A` of `K₁'` — then `ϕ` is the conjugation by `σ`: `Conjugates σ ϕ`.

This is the converse of `NK.UchidaKummer.Identification.comap_placeMap_eq_of_conjugates`, and it
is *elementary*: no Čebotarev input and no homeomorphism hypothesis on `ϕ` is used.  The
Galois-equivariance of the place map (`a.map_smul`) together with the realization of the place map
by `σ` says that the group elements `ϕ g` and `σ⁻¹ g σ` act in the same way on *every* finite
place of `K₂'`; a Galois automorphism fixing every finite place is trivial (the completely split
primes see this: for a finite level in which the automorphism is non-trivial, a completely split
prime has trivial decomposition group).
-/

set_option linter.style.haveILetI false

namespace NK.UchidaKummer.Identification

open scoped Pointwise

/-- **A Galois automorphism fixing every finite place is trivial.**

Let `K` be a number field, `K'` a separable closure, and `k ∈ Gal(K'/K)`.  If `k` fixes every
place of `K'` over a finite prime of `K`, then `k = 1`.

Indeed, let `y ∈ K'` and let `N ⊆ K'` be a finite Galois intermediate field containing `y`.  A
prime `p` of `K` splitting completely in `N` has trivial decomposition group in `Gal(N/K)`; since
`k` fixes a place `B` of `K'` above `p`, its restriction to `N` lies in that trivial decomposition
group, so `k` fixes `y`. -/
theorem eq_one_of_smul_finitePlace_eq_self
    {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (k : Gal(K'/K))
    (h : ∀ B : {A : ValuationSubring K' // A.comap (algebraMap K K') ≠ ⊤}, k • B.1 = B.1) :
    k = 1 := by
  refine AlgEquiv.ext fun y => ?_
  obtain ⟨N, hNfin, hNgal, hyN⟩ :=
    Commons.FieldTheory.Galois.exists_finite_galois_containing (k := K) (K := K') y
  haveI : FiniteDimensional K N := hNfin
  haveI : Normal K N := hNgal.to_normal
  haveI : NumberField ↥N :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := K) (K' := K') N
  obtain ⟨p, -, hp⟩ :=
    NK.UchidaKummer.exists_splitsCompletely_notMem (K := K) (L := ↥N) (T := ∅)
  obtain ⟨B, hB⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime (K := K) (K' := K') p
  have hBne : B.comap (algebraMap K K') ≠ ⊤ := by
    rw [hB]
    exact Submission.NeukirchUchida.Local.valuationSubringAtPrime_ne_top p
  have hstab : k ∈ MulAction.stabilizer Gal(K'/K) B :=
    (MulAction.mem_stabilizer_iff).mpr (h ⟨B, hBne⟩)
  have hle : MulAction.stabilizer Gal(K'/K) B ≤ N.fixingSubgroup :=
    (NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely (K := K) (K' := K')
      (N := N) p B hB).mpr hp
  exact (IntermediateField.mem_fixingSubgroup_iff N k).mp (hle hstab) y hyN

/-- **The action of the conjugating automorphism on the place `A.comap σ`.**

For a base-field mapping isomorphism `σ : K₂' ≃+* K₁'`, a Galois automorphism `g` of `K₁'/K₁` and a
place `A` of `K₁'`, the transport of `A` along `σ` commutes with the action of `g`: the place
`(g • A).comap σ` is obtained from `A.comap σ` by the conjugation `σ⁻¹ g σ ∈ Gal(K₂'/K₂)`. -/
theorem smul_comap_sigma_eq_conj_smul
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [Algebra K₁ K₁'] [Algebra K₂ K₂']
    {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (g : Gal(K₁'/K₁)) (A : ValuationSubring K₁') :
    (g • A).comap (σ : K₂' →+* K₁') =
      (Submission.NeukirchUchida.conjHomEquiv hσ g) • (A.comap (σ : K₂' →+* K₁')) := by
  have hC : ∀ y : K₂', (Submission.NeukirchUchida.conjHomEquiv hσ g) y = σ.symm (g (σ y)) :=
    fun y => Submission.NeukirchUchida.conj_apply hσ g y
  have hsymm : ∀ x : K₂', (Submission.NeukirchUchida.conjHomEquiv hσ g)⁻¹ x
      = σ.symm (g.symm (σ x)) := by
    intro x
    have h1 : (Submission.NeukirchUchida.conjHomEquiv hσ g) (σ.symm (g.symm (σ x))) = x := by
      rw [hC]
      simp
    calc (Submission.NeukirchUchida.conjHomEquiv hσ g)⁻¹ x
        = (Submission.NeukirchUchida.conjHomEquiv hσ g)⁻¹
            ((Submission.NeukirchUchida.conjHomEquiv hσ g) (σ.symm (g.symm (σ x)))) := by
          rw [h1]
      _ = σ.symm (g.symm (σ x)) := AlgEquiv.symm_apply_apply _ _
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.smul_def,
      ValuationSubring.mem_comap, hsymm x]
  simp

theorem conjugates_of_comap_placeMap_eq
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (a : NK.Reconstruct.LocalCorrespondence ϕ)
    {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hreal : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    Submission.NeukirchUchida.Conjugates σ ϕ := by
  -- (1) the place map of `a` is the one realized by `σ`
  have hplace : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      (a.placeMap A).1 = A.1.comap (σ : K₂' →+* K₁') := by
    intro A
    have h1 := congrArg (fun B : ValuationSubring K₁' => B.comap (σ : K₂' →+* K₁')) (hreal A)
    rw [ValuationSubring.comap_comap, RingEquiv.symm_comp] at h1
    rw [show (a.placeMap A).1.comap (RingHom.id K₂') = (a.placeMap A).1 from by
      ext x
      rw [ValuationSubring.mem_comap]
      simp] at h1
    exact h1
  -- (2) `ϕ g` and `σ⁻¹ g σ` act alike on every finite place of `K₂'`
  have hact : ∀ (g : Gal(K₁'/K₁)) (B : NK.Reconstruct.FinitePlaceOf K₂ K₂'),
      (Submission.NeukirchUchida.conjHomEquiv hσ g) • B.1 = (ϕ g) • B.1 := by
    intro g B
    obtain ⟨A, hA⟩ : ∃ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        A.1.comap (σ : K₂' →+* K₁') = B.1 :=
      ⟨a.placeMap.symm B, by
        have h2 := hplace (a.placeMap.symm B)
        rw [Equiv.apply_symm_apply a.placeMap B] at h2
        exact h2.symm⟩
    have h2 : (g • A.1).comap (σ : K₂' →+* K₁') =
        (Submission.NeukirchUchida.conjHomEquiv hσ g) • B.1 := by
      rw [← hA]
      exact smul_comap_sigma_eq_conj_smul hσ g A.1
    have h3 : (g • A.1).comap (σ : K₂' →+* K₁') = (ϕ g) • B.1 := by
      have h1 := congrArg Subtype.val (a.map_smul g A)
      rw [NK.Reconstruct.placeSmul₂_val, hplace A,
        hplace (NK.Reconstruct.placeSmul g A), NK.Reconstruct.placeSmul_val,
        hA] at h1
      exact h1
    exact h2.symm.trans h3
  -- (3) conclude
  refine ⟨hσ, fun g => ?_⟩
  have hfix : (Submission.NeukirchUchida.conjHomEquiv hσ g)⁻¹ * ϕ g = 1 := by
    refine eq_one_of_smul_finitePlace_eq_self (K := K₂) (K' := K₂') _ (fun B => ?_)
    rw [mul_smul, ← hact g B, ← mul_smul, inv_mul_cancel, one_smul]
  have hEq : ϕ g = Submission.NeukirchUchida.conjHomEquiv hσ g :=
    (inv_mul_eq_one.mp hfix).symm
  exact (congrArg (fun e : Gal(K₂'/K₂) => (e : K₂' ≃+* K₂')) hEq).trans
    (Submission.NeukirchUchida.conj_toRingEquiv hσ g)

end NK.UchidaKummer.Identification
