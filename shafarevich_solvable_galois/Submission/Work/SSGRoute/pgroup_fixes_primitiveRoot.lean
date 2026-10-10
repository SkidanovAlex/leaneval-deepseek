import Mathlib.NumberTheory.Cyclotomic.Basic
import Submission.Work.SSGRoute.phi1_sylow_setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt

/-- **A `p`-subgroup of `Gal(K/k)` fixes a primitive `p`-th root of unity in `K`.**

Let `k ⊆ K` be a finite Galois extension of number fields and `ζ ∈ K` a primitive `p`-th root of
unity.  Then every subgroup `P ≤ Gal(K/k)` of `p`-power order fixes `ζ` pointwise.

This is the `hfix` hypothesis of `Work.SSGRoute.exists_localZetaCoeff`: it is what lets Z8 pass to the
level `k' = K^S` (with `S` a Sylow `p`-subgroup of `D_w`) and still have `ζ ∈ k'`, hence supply the
`(z, hz)` datum of `Work.SSGRoute.detectAbove_pgroup`.  It is the companion of the *proved*
`Work.SSGRoute.exists_pSylow_le_fixingSubgroup` (which produces a Sylow `P` with `¬ p ∣ P.index`
and `∀ σ ∈ P, σ ζ = ζ`).

Proof routes (both checked by review).  With `H := (adjoin k {ζ}).fixingSubgroup` one has
`H.index = [k(ζ) : k]`, which **divides** `p - 1` and in particular is prime to `p`
(`Work.SSGRoute.not_dvd_finrank_adjoin`); the image of the `p`-group `P` in `Gal(K/k) ⧸ H` has
`p`-power order dividing both `Nat.card P` and `H.index`, hence is trivial, so `P ≤ H` and `P` fixes
`k(ζ)` pointwise.  Equivalently (reviewer 2): every `σ ∈ Gal(K/k)` sends `ζ` to `ζ ^ a` for some
`a ∈ (ℤ/p)^*`, so `σ ↦ a` is a homomorphism `P → (ℤ/p)^*` from a `p`-group to a group of order
`p - 1`, hence trivial.

Note (reviewer 1): `[k(ζ) : k]` **divides** `p - 1`; it is *not* equal to `Nat.totient p` in general
(it is `1` when `k ⊇ ℚ(ζ)`).  Only the coprimality to `p` is needed. -/
theorem pgroup_fixes_primitiveRoot (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (P : Subgroup (K ≃ₐ[k] K)) (hP : IsPGroup p P) :
    ∀ σ ∈ P, σ ζ = ζ := by
  classical
  -- `k(ζ) / k` is a cyclotomic (hence Galois) extension, so its fixing subgroup is normal.
  have hpne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hGalL : IsGalois k ↥(IntermediateField.adjoin k ({ζ} : Set K)) := by
    have hint : Algebra.IsIntegral k K := inferInstance
    have hcyc : IsCyclotomicExtension {p} k ↥(IntermediateField.adjoin k ({ζ} : Set K)) :=
      hζ.intermediateField_adjoin_isCyclotomicExtension k
    exact IsCyclotomicExtension.isGalois {p} k _
  set H : Subgroup (K ≃ₐ[k] K) := (IntermediateField.adjoin k ({ζ} : Set K)).fixingSubgroup with hH
  have hHnorm : H.Normal := by rw [hH]; infer_instance
  -- `H.index = [k(ζ) : k]` is prime to `p`.
  have hHidx : H.index = Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set K)) := by
    rw [hH]
    exact (IntermediateField.finrank_eq_fixingSubgroup_index K _).symm
  have hnotdvd : ¬ p ∣ H.index := by
    rw [hHidx]
    exact Work.SSGRoute.not_dvd_finrank_adjoin k K p hζ
  -- The image of `P` in `Gal(K/k) ⧸ H` is a `p`-group of order dividing `H.index`, hence trivial.
  have hcard : Nat.card ↥(P.map (QuotientGroup.mk' H)) = 1 := by
    rcases (hP.map (QuotientGroup.mk' H)).card_eq_or_dvd with h1 | hp
    · exact h1
    · exfalso
      have hdiv : Nat.card ↥(P.map (QuotientGroup.mk' H)) ∣ H.index := by
        rw [Subgroup.index_eq_card H]
        exact Subgroup.card_subgroup_dvd_card _
      exact hnotdvd (hp.trans hdiv)
  have hbot : P.map (QuotientGroup.mk' H) = ⊥ := Subgroup.card_eq_one.mp hcard
  have hle : P ≤ H := by
    have h := (Subgroup.map_eq_bot_iff P).mp hbot
    rwa [QuotientGroup.ker_mk' H] at h
  -- `P` fixes `k(ζ)` pointwise, in particular `ζ`.
  intro σ hσ
  have hσH : σ ∈ H := hle hσ
  rw [hH] at hσH
  exact (IntermediateField.mem_fixingSubgroup_iff (IntermediateField.adjoin k ({ζ} : Set K)) σ).mp
    hσH ζ (IntermediateField.mem_adjoin_simple_self k ζ)

end Work.SSGRoute
