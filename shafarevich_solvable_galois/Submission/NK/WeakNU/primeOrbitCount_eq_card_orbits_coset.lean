/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The number of `H`-orbits of primes above a place is an orbit count on a coset space

Let `N / ℚ` be a finite Galois extension of number fields, `H ≤ Gal(N/ℚ)` a subgroup, `𝔭` a
finite place of `ℚ` and `P₀` a place of `N` above `𝔭`.  The Galois group `Gal(N/ℚ)` acts
transitively on the primes of `𝓞 N` above `𝔭`, and the stabiliser of `P₀` is its decomposition
subgroup

`D_{P₀} = Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) P₀`.

Hence the primes of `𝓞 N` above `𝔭` are the coset space `Gal(N/ℚ) ⧸ D_{P₀}` *as `H`-sets*, and
the number of `H`-orbits of primes above `𝔭` — `NK.WeakNU.primeOrbitCount H 𝔭` — is the number
of `H`-orbits on that coset space.  This is the orbit-count form of the fundamental identity of
Galois ramification theory (orbit–stabiliser), the first half of the reduction of
`NK.WeakNU.PrimeCountOrbitInput` to the decomposition-theoretic description of the splitting
behaviour of `𝔭`; see `README.md`.
-/

import Mathlib
import Submission.NK.WeakNU.PrimeOrbit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

set_option linter.style.haveILetI false

namespace NK.WeakNU

noncomputable section

/-- **Transitivity of the Galois action on the primes above a fixed finite place.**  Every prime
`P` of `𝓞 N` above `𝔭` is the image of `P₀` under some `σ : Gal(N/ℚ)`.  This is the number field
case of `Algebra.IsInvariant.exists_smul_of_under_eq`, transported from ideals to height one
primes. -/
theorem exists_placeAct_eq_of_liesOver {N : Type} [Field N] [NumberField N] [Algebra ℚ N]
    [IsGalois ℚ N] (𝔭 : NK.Chebotarev.PrimeIdeal ℚ) (P₀ P : NK.Chebotarev.PrimeIdeal N)
    (hP₀ : P₀.asIdeal.LiesOver 𝔭.asIdeal) (hP : P.asIdeal.LiesOver 𝔭.asIdeal) :
    ∃ σ : Gal(N/ℚ), placeAct σ P₀ = P := by
  haveI : P₀.asIdeal.IsPrime := P₀.isPrime
  haveI : P.asIdeal.IsPrime := P.isPrime
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := NumberField.RingOfIntegers ℚ)
    (B := NumberField.RingOfIntegers N) (G := Gal(N/ℚ)) P₀.asIdeal P.asIdeal
    (hP₀.over.symm.trans hP.over)
  have hring : ∀ τ : Gal(N/ℚ),
      (MulSemiringAction.toRingHom Gal(N/ℚ) (NumberField.RingOfIntegers N) τ :
        NumberField.RingOfIntegers N →+* NumberField.RingOfIntegers N) =
      (galRestrict (NumberField.RingOfIntegers ℚ) ℚ N (NumberField.RingOfIntegers N) τ :
        NumberField.RingOfIntegers N →+* NumberField.RingOfIntegers N) := by
    intro τ
    refine RingHom.ext fun x => ?_
    apply Subtype.ext
    exact ((algebraMap_galRestrict_apply (NumberField.RingOfIntegers ℚ) τ x).trans rfl).symm
  refine ⟨σ, ?_⟩
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [placeAct_asIdeal, hσ, Ideal.pointwise_smul_def, hring σ]

theorem primeOrbitCount_eq_card_orbits_coset {N : Type} [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N] (H : Subgroup Gal(N/ℚ)) (𝔭 : NK.Chebotarev.PrimeIdeal ℚ) (P₀ : NK.Chebotarev.PrimeIdeal N) (hP₀ : P₀.asIdeal.LiesOver 𝔭.asIdeal) : NK.WeakNU.primeOrbitCount H 𝔭 = Nat.card (MulAction.orbitRel.Quotient H (Gal(N/ℚ) ⧸ Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) P₀)) := by
  classical
  -- the decomposition subgroup `D` of `P₀` is the stabiliser of `P₀` for `placeAct`
  set D : Subgroup Gal(N/ℚ) :=
    Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) P₀ with hD
  have memD : ∀ σ : Gal(N/ℚ), σ ∈ D ↔ placeAct σ P₀ = P₀ := by
    intro σ
    rw [hD]
    exact Submission.NeukirchUchida.Local.mem_decompositionSubgroup
  -- the primes of `𝓞 N` above `𝔭`
  let α := {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal}
  -- each prime above `𝔭` is a Galois translate of `P₀`; choose one
  have hex : ∀ P : α, ∃ σ : Gal(N/ℚ), placeAct σ P₀ = P.1 :=
    fun P => exists_placeAct_eq_of_liesOver 𝔭 P₀ P.1 hP₀ P.2
  let rep : α → Gal(N/ℚ) := fun P => Classical.choose (hex P)
  have hrep : ∀ P : α, placeAct (rep P) P₀ = P.1 := fun P => Classical.choose_spec (hex P)
  let φ : α → Gal(N/ℚ) ⧸ D := fun P => QuotientGroup.mk (rep P)
  -- two primes with the same translate of `P₀` lie in the same coset, and conversely
  have hcoset : ∀ σ τ : Gal(N/ℚ), placeAct σ P₀ = placeAct τ P₀ →
      (QuotientGroup.mk σ : Gal(N/ℚ) ⧸ D) = QuotientGroup.mk τ := by
    intro σ τ h
    refine QuotientGroup.eq.mpr ?_
    rw [memD]
    calc placeAct (σ⁻¹ * τ) P₀ = placeAct σ⁻¹ (placeAct τ P₀) := placeAct_mul σ⁻¹ τ P₀
      _ = placeAct σ⁻¹ (placeAct σ P₀) := by rw [h]
      _ = placeAct (σ⁻¹ * σ) P₀ := (placeAct_mul σ⁻¹ σ P₀).symm
      _ = placeAct 1 P₀ := by rw [inv_mul_cancel]
      _ = P₀ := placeAct_one P₀
  have hplace : ∀ σ τ : Gal(N/ℚ), (QuotientGroup.mk σ : Gal(N/ℚ) ⧸ D) = QuotientGroup.mk τ →
      placeAct σ P₀ = placeAct τ P₀ := by
    intro σ τ h
    have hmem : σ⁻¹ * τ ∈ D := QuotientGroup.eq.mp h
    rw [memD] at hmem
    have h2 : placeAct (σ * (σ⁻¹ * τ)) P₀ = placeAct σ P₀ := by
      rw [placeAct_mul, hmem]
    rw [mul_inv_cancel_left] at h2
    exact h2.symm
  have hplace_inv : ∀ (σ : Gal(N/ℚ)) (P Q : NK.Chebotarev.PrimeIdeal N),
      placeAct σ P = Q → placeAct σ⁻¹ Q = P := by
    intro σ P Q h
    rw [← h, ← placeAct_mul σ⁻¹ σ P, inv_mul_cancel, placeAct_one]
  -- the `H`-action on the coset space is left multiplication
  have smul_mk : ∀ (h : H) (g : Gal(N/ℚ)),
      h • (QuotientGroup.mk g : Gal(N/ℚ) ⧸ D) =
        QuotientGroup.mk ((h : Gal(N/ℚ)) * g) := fun h g => rfl
  have hinj : Function.Injective φ := by
    intro P Q hPQ
    have h := hplace (rep P) (rep Q) hPQ
    rw [hrep P, hrep Q] at h
    exact Subtype.ext h
  have hsurj : Function.Surjective φ := by
    intro q
    refine ⟨⟨placeAct q.out P₀, liesOver_placeAct hP₀ q.out⟩, ?_⟩
    have h := hcoset (rep ⟨placeAct q.out P₀, liesOver_placeAct hP₀ q.out⟩) q.out
      (by rw [hrep ⟨placeAct q.out P₀, liesOver_placeAct hP₀ q.out⟩])
    exact h.trans (QuotientGroup.out_eq' q)
  -- the (choice-free) bijection between the primes above `𝔭` and the coset space
  let e : α ≃ (Gal(N/ℚ) ⧸ D) := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ P : α, e P = φ P := fun P => rfl
  -- `e` is `H`-equivariant
  have hmap : ∀ (h : H) (P : α),
      e ⟨placeAct (h : Gal(N/ℚ)) P.1, liesOver_placeAct P.2 (h : Gal(N/ℚ))⟩ = h • e P := by
    intro h P
    have h' : (QuotientGroup.mk (rep ⟨placeAct (h : Gal(N/ℚ)) P.1,
        liesOver_placeAct P.2 (h : Gal(N/ℚ))⟩) :
        Gal(N/ℚ) ⧸ D) = QuotientGroup.mk ((h : Gal(N/ℚ)) * rep P) :=
      hcoset _ _ (by rw [hrep, placeAct_mul, hrep P])
    rw [he, he]
    change (QuotientGroup.mk (rep ⟨placeAct (h : Gal(N/ℚ)) P.1,
        liesOver_placeAct P.2 (h : Gal(N/ℚ))⟩) : Gal(N/ℚ) ⧸ D) =
      h • (QuotientGroup.mk (rep P) : Gal(N/ℚ) ⧸ D)
    rw [smul_mk]
    exact h'
  -- the orbit relation on the coset space, written with `h • x = y`
  have orbit_iff : ∀ x y : Gal(N/ℚ) ⧸ D,
      MulAction.orbitRel H (Gal(N/ℚ) ⧸ D) x y ↔ ∃ h : H, h • x = y := by
    intro x y
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k⁻¹, by rw [← hk, ← mul_smul, inv_mul_cancel, one_smul]⟩
    · rintro ⟨k, hk⟩
      exact ⟨k⁻¹, by rw [← hk, ← mul_smul, inv_mul_cancel, one_smul]⟩
  -- the orbit relation on the primes corresponds to that on the coset space
  have hrel : ∀ P Q : α, primeOrbitSetoid H 𝔭 P Q ↔
      MulAction.orbitRel H (Gal(N/ℚ) ⧸ D) (e P) (e Q) := by
    intro P Q
    rw [orbit_iff (e P) (e Q)]
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨h, ?_⟩
      have hsub : (⟨placeAct (h : Gal(N/ℚ)) P.1,
          liesOver_placeAct P.2 (h : Gal(N/ℚ))⟩ : α) = Q := Subtype.ext hh
      rw [← hmap h P, hsub]
    · rintro ⟨h, hh⟩
      rw [← hmap h P] at hh
      exact ⟨h, Subtype.ext_iff.mp (e.injective hh)⟩
  rw [primeOrbitCount]
  exact Nat.card_congr (Quotient.congr e hrel)

end

end NK.WeakNU
