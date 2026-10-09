import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Sylow descent setup for `φ¹` injectivity (E6)

Reusable pieces for the descent to `k' = K^P` (`P` a `p`-Sylow, `μ_p ⊆ K`):

* `finrank_adjoin_primitiveRoot_le` — `[k(ζ) : k] ≤ p - 1` for `ζ` a primitive `p`-th root;
* `not_dvd_finrank_adjoin` — hence `p ∤ [k(ζ) : k]`;
* `exists_pSylow_le_fixingSubgroup` — there is `P ≤ Gal(K/k)` with `IsPGroup p ↥P`,
  `¬ p ∣ P.index` and `σ ζ = ζ` for `σ ∈ P` (so `μ_p ⊆ K^P`);
* `classGroupRep_ρ_restrictScalars` — the change of base field for `C_K`: for `k ⊆ k' ⊆ K`,
  `classesK k' K` is the restriction of `classesK k K` along `AlgEquiv.restrictScalarsHom k`.

These are extracted so that the `Ω`-indexed node `phi1_mono_sylow_in` can import them without a cycle
(it cannot import `phi1_mono_sylow`, which imports it).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

section Setup

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- `[k(ζ) : k] ≤ p - 1` for a primitive `p`-th root of unity `ζ ∈ K` (`p` prime): `ζ` is a root of
`∑_{i<p} X^i`, whose degree is `≤ p-1`; hence `deg (minpoly k ζ) ≤ p-1`. -/
theorem finrank_adjoin_primitiveRoot_le (p : ℕ) [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set K)) ≤ p - 1 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpos : 0 < p := (Fact.out : p.Prime).pos
  have hint : IsIntegral k ζ := Algebra.IsIntegral.isIntegral ζ
  rw [IntermediateField.adjoin.finrank hint]
  have hne : (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial k) ^ i) ≠ 0 := by
    intro h
    have hc : (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial k) ^ i).coeff 0 = 1 := by
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
      · simp
      · intro b _ hb
        rw [Polynomial.coeff_X_pow, if_neg (Ne.symm hb)]
      · intro h0
        exact absurd (Finset.mem_range.mpr hpos) h0
    rw [h, Polynomial.coeff_zero] at hc
    exact zero_ne_one hc
  have hroot : (Polynomial.aeval ζ)
      (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial k) ^ i) = 0 := by
    rw [map_sum]
    simp only [map_pow, Polynomial.aeval_X]
    exact IsPrimitiveRoot.geom_sum_eq_zero hζ hp1
  have hdvd : (minpoly k ζ) ∣ (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial k) ^ i) :=
    minpoly.dvd k ζ hroot
  have hdeg : (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial k) ^ i).natDegree ≤ p - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.range p) (n := p - 1)
      (fun i => (Polynomial.X : Polynomial k) ^ i) ?_
    intro i hi
    rw [Polynomial.natDegree_X_pow]
    exact Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)
  exact le_trans (Polynomial.natDegree_le_of_dvd hdvd hne) hdeg

/-- `p ∤ [k(ζ) : k]` for `ζ` a primitive `p`-th root of unity (`p` prime), since the degree is
at least `1` and at most `p - 1`. -/
theorem not_dvd_finrank_adjoin (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    ¬ p ∣ Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set K)) := by
  have hle := finrank_adjoin_primitiveRoot_le k K p hζ
  have hpos : 0 < Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set K)) :=
    Module.finrank_pos
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · subst hc0; rw [mul_zero] at hc; omega
  · have : p ≤ Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set K)) := by
      rw [hc]
      calc p = p * 1 := (mul_one p).symm
        _ ≤ p * c := Nat.mul_le_mul_left p hcpos
    omega

/-- **The `p`-Sylow needed for the descent.** If `ζ ∈ K` is a primitive `p`-th root of unity there is
a subgroup `P ≤ Gal(K/k)` of `p`-power order whose index is prime to `p` and which fixes `ζ`
(so that `μ_p ⊆ K^P`).  Indeed a `p`-Sylow of `Gal(K/k(ζ))` has index `[G : P] = [G : H]·[H : P]`
whose second factor is prime to `p` by Sylow and whose first factor is `[k(ζ) : k]`, prime to `p` by
`not_dvd_finrank_adjoin`. -/
theorem exists_pSylow_le_fixingSubgroup (p : ℕ) [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    ∃ P : Subgroup (K ≃ₐ[k] K), IsPGroup p ↥P ∧ ¬ p ∣ P.index ∧ (∀ σ ∈ P, σ ζ = ζ) := by
  classical
  set H : Subgroup (K ≃ₐ[k] K) := (IntermediateField.adjoin k ({ζ} : Set K)).fixingSubgroup with hH
  obtain ⟨A⟩ := Sylow.nonempty (p := p) (G := ↥H)
  refine ⟨(A : Subgroup ↥H).map H.subtype, A.isPGroup'.map H.subtype, ?_, ?_⟩
  · have hcardA : Nat.card ↥((A : Subgroup ↥H).map H.subtype) = Nat.card ↥(A : Subgroup ↥H) :=
      Subgroup.card_map_of_injective (f := H.subtype) Subtype.coe_injective
    have hP : Nat.card ↥((A : Subgroup ↥H).map H.subtype) * ((A : Subgroup ↥H).map H.subtype).index
        = Nat.card (K ≃ₐ[k] K) := Subgroup.card_mul_index _
    have hAcard : Nat.card ↥(A : Subgroup ↥H) * (A : Subgroup ↥H).index = Nat.card ↥H :=
      Subgroup.card_mul_index _
    have hHcard : Nat.card ↥H * H.index = Nat.card (K ≃ₐ[k] K) := Subgroup.card_mul_index H
    have hAut : Nat.card (K ≃ₐ[k] K) = Module.finrank k K := IsGalois.card_aut_eq_finrank k K
    have hFix : Nat.card ↥H = Module.finrank ↥(IntermediateField.adjoin k ({ζ} : Set K)) K :=
      IsGalois.card_fixingSubgroup_eq_finrank (K := IntermediateField.adjoin k ({ζ} : Set K))
    have hTower : Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set K)) *
        Module.finrank ↥(IntermediateField.adjoin k ({ζ} : Set K)) K = Module.finrank k K :=
      Module.finrank_mul_finrank k ↥(IntermediateField.adjoin k ({ζ} : Set K)) K
    have hHidx : H.index = Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set K)) := by
      have h1 : Nat.card ↥H * H.index = Nat.card ↥H *
          Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set K)) := by
        rw [hHcard, hAut, ← hTower, ← hFix]
        ring
      exact Nat.mul_left_cancel (Nat.card_pos (α := ↥H)) h1
    have hPidx : ((A : Subgroup ↥H).map H.subtype).index = (A : Subgroup ↥H).index * H.index := by
      have h1 : Nat.card ↥((A : Subgroup ↥H).map H.subtype) *
            ((A : Subgroup ↥H).map H.subtype).index =
          Nat.card ↥((A : Subgroup ↥H).map H.subtype) *
            ((A : Subgroup ↥H).index * H.index) := by
        rw [hP, hcardA, ← mul_assoc, hAcard, hHcard]
      exact Nat.mul_left_cancel (Nat.card_pos (α := ↥((A : Subgroup ↥H).map H.subtype))) h1
    rw [hPidx]
    exact (Fact.out : p.Prime).not_dvd_mul (Sylow.not_dvd_index A)
      (by rw [hHidx]; exact not_dvd_finrank_adjoin k K p hζ)
  · intro σ hσ
    rw [Subgroup.mem_map] at hσ
    obtain ⟨τ, _, rfl⟩ := hσ
    exact (IntermediateField.mem_fixingSubgroup_iff
      (IntermediateField.adjoin k ({ζ} : Set K)) (τ : K ≃ₐ[k] K)).mp τ.2 ζ
      (IntermediateField.mem_adjoin_simple_self k ζ)


/-- **Change of base field for the idèle class group.** The action of `σ ∈ Gal(K/k')` on `C_K` (with
`k ⊆ k' ⊆ K`) agrees with the action of `σ`, viewed as an element of `Gal(K/k)`, on the
`Gal(K/k)`-module `C_K`: both are induced by the same ring automorphism of `K` (and the two `SMul`
instances are given by the same formula on idèle classes).  This is what identifies
`classesK k' K` with the restriction of `classesK k K` along `AlgEquiv.restrictScalarsHom k`. -/
theorem classGroupRep_ρ_restrictScalars (k k' K : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Algebra k K] [Algebra k' K] [Algebra k k']
    [IsScalarTower k k' K] (σ : K ≃ₐ[k'] K) (q : NK.GlobalCFT.IdeleClassGroup K) :
    (NK.HassePrinciple.classGroupRep k K).ρ (AlgEquiv.restrictScalarsHom k σ)
        (Additive.ofMul q)
      = (NK.HassePrinciple.classGroupRep k' K).ρ σ (Additive.ofMul q) := by
  rw [NK.HassePrinciple.classGroupRep_ρ_apply, NK.HassePrinciple.classGroupRep_ρ_apply]
  congr 1

end Setup

end Work.SSGRoute
