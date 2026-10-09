/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The primes above a finite place as a Galois set

This file provides the vocabulary with which the input `NK.WeakNU.PrimeCountOrbitInput` is
attacked, namely

* `NK.WeakNU.placeAct`: the action of `Gal(N/ℚ)` on the finite places of `N`
  (`NK.NeukirchUchida.Local.placeSmul`), which preserves the primes above a fixed place `𝔭` of
  `ℚ` (`NK.WeakNU.liesOver_placeAct`);
* `NK.WeakNU.primeOrbitSetoid H 𝔭`: the orbit relation of a subgroup `H ≤ Gal(N/ℚ)` on the
  primes of `𝓞 N` above `𝔭`;
* `NK.WeakNU.primeOrbitCount H 𝔭`: the number of such orbits;
* `NK.WeakNU.primeCountAbove M 𝔭`: the number of primes of an intermediate field `M ⊆ N` above
  `𝔭`.

The classical statement whose formalisation would remove `NK.WeakNU.PrimeCountOrbitInput` from the
residual catalogue of this chapter is
`NK.WeakNU.primeCountAbove_eq_primeOrbitCount` (the two counts above), together with the
identification of `primeOrbitCount H 𝔭` with `orbitCount σ (Gal(N/ℚ) ⧸ H)` for a Frobenius `σ` at a
prime above `𝔭`; see `README.md` for the roadmap and the references.
-/

import Submission.NK.WeakNU.Defs
import Submission.NK.Chebotarev.Basic
import Submission.NeukirchUchida.Local.DecompositionGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.WeakNU

noncomputable section

variable {N : Type*} [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N]

/-- The Galois action on the finite places of `N`: `σ • 𝔓` is the image of `𝔓` under the ring
automorphism of `𝓞 N` induced by `σ` (`NK.NeukirchUchida.Local.placeSmul`). -/
def placeAct (σ : Gal(N/ℚ)) (P : NK.Chebotarev.PrimeIdeal N) : NK.Chebotarev.PrimeIdeal N :=
  Submission.NeukirchUchida.Local.placeSmul σ P

/-- Equation lemma for `placeAct`. -/
theorem placeAct_asIdeal (σ : Gal(N/ℚ)) (P : NK.Chebotarev.PrimeIdeal N) :
    (placeAct σ P).asIdeal =
      P.asIdeal.map (galRestrict (NumberField.RingOfIntegers ℚ) ℚ N
        (NumberField.RingOfIntegers N) σ : NumberField.RingOfIntegers N →+*
          NumberField.RingOfIntegers N) :=
  Submission.NeukirchUchida.Local.placeSmul_asIdeal σ P

/-- `placeAct` is a left action. -/
theorem placeAct_mul (σ τ : Gal(N/ℚ)) (P : NK.Chebotarev.PrimeIdeal N) :
    placeAct (σ * τ) P = placeAct σ (placeAct τ P) :=
  Submission.NeukirchUchida.Local.placeSmul_mul σ τ P

/-- `placeAct` of the identity is the identity. -/
theorem placeAct_one (P : NK.Chebotarev.PrimeIdeal N) :
    placeAct (1 : Gal(N/ℚ)) P = P :=
  Submission.NeukirchUchida.Local.placeSmul_one P

/-- **The Galois action preserves the primes above a fixed place.** -/
theorem liesOver_placeAct {𝔭 : NK.Chebotarev.PrimeIdeal ℚ} {P : NK.Chebotarev.PrimeIdeal N}
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) (σ : Gal(N/ℚ)) :
    (placeAct σ P).asIdeal.LiesOver 𝔭.asIdeal :=
  Submission.NeukirchUchida.Local.liesOver_placeSmul 𝔭 P σ

/-- **The orbit relation on the primes of `𝓞 N` above `𝔭` under a subgroup `H ≤ Gal(N/ℚ)`.** -/
def SamePrimeOrbit (H : Subgroup Gal(N/ℚ)) (𝔭 : NK.Chebotarev.PrimeIdeal ℚ)
    (P Q : {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal}) : Prop :=
  ∃ h : H, placeAct (h : Gal(N/ℚ)) P.1 = Q.1

theorem samePrimeOrbit_refl (H : Subgroup Gal(N/ℚ)) (𝔭 : NK.Chebotarev.PrimeIdeal ℚ)
    (P : {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal}) :
    SamePrimeOrbit H 𝔭 P P :=
  ⟨1, by
    rw [show ((1 : ↥H) : Gal(N/ℚ)) = 1 by simp]
    exact placeAct_one P.1⟩

theorem samePrimeOrbit_symm (H : Subgroup Gal(N/ℚ)) (𝔭 : NK.Chebotarev.PrimeIdeal ℚ)
    {P Q : {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal}}
    (h : SamePrimeOrbit H 𝔭 P Q) : SamePrimeOrbit H 𝔭 Q P := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k⁻¹, ?_⟩
  calc placeAct ((k⁻¹ : ↥H) : Gal(N/ℚ)) Q.1
      = placeAct ((k⁻¹ : ↥H) : Gal(N/ℚ))
          (placeAct ((k : ↥H) : Gal(N/ℚ)) P.1) := by rw [hk]
    _ = placeAct (((k⁻¹ : ↥H) : Gal(N/ℚ)) * ((k : ↥H) : Gal(N/ℚ))) P.1 := by
          rw [← placeAct_mul]
    _ = placeAct 1 P.1 := by
          rw [show (((k⁻¹ : ↥H) : Gal(N/ℚ)) * ((k : ↥H) : Gal(N/ℚ))) = 1 by simp]
    _ = P.1 := placeAct_one P.1

theorem samePrimeOrbit_trans (H : Subgroup Gal(N/ℚ)) (𝔭 : NK.Chebotarev.PrimeIdeal ℚ)
    {P Q R : {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal}}
    (h₁ : SamePrimeOrbit H 𝔭 P Q) (h₂ : SamePrimeOrbit H 𝔭 Q R) : SamePrimeOrbit H 𝔭 P R := by
  obtain ⟨k, hk⟩ := h₁
  obtain ⟨l, hl⟩ := h₂
  refine ⟨l * k, ?_⟩
  calc placeAct ((l * k : ↥H) : Gal(N/ℚ)) P.1
      = placeAct (((l : ↥H) : Gal(N/ℚ)) * ((k : ↥H) : Gal(N/ℚ))) P.1 := by
          rw [show ((l * k : ↥H) : Gal(N/ℚ)) = ((l : ↥H) : Gal(N/ℚ)) * ((k : ↥H) : Gal(N/ℚ)) by
            simp]
    _ = placeAct ((l : ↥H) : Gal(N/ℚ))
          (placeAct ((k : ↥H) : Gal(N/ℚ)) P.1) := placeAct_mul _ _ _
    _ = placeAct ((l : ↥H) : Gal(N/ℚ)) Q.1 := by rw [hk]
    _ = R.1 := hl

/-- The setoid of the `H`-orbits of primes of `𝓞 N` above `𝔭`. -/
def primeOrbitSetoid (H : Subgroup Gal(N/ℚ)) (𝔭 : NK.Chebotarev.PrimeIdeal ℚ) :
    Setoid {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal} where
  r := SamePrimeOrbit H 𝔭
  iseqv := ⟨samePrimeOrbit_refl H 𝔭, fun h => samePrimeOrbit_symm H 𝔭 h,
    fun h₁ h₂ => samePrimeOrbit_trans H 𝔭 h₁ h₂⟩

/-- **The number of `H`-orbits of primes of `𝓞 N` above the finite place `𝔭`.** -/
def primeOrbitCount (H : Subgroup Gal(N/ℚ)) (𝔭 : NK.Chebotarev.PrimeIdeal ℚ) : ℕ :=
  Nat.card (Quotient (primeOrbitSetoid H 𝔭))

/-- **The number of primes of an intermediate field above the finite place `𝔭`.** -/
def primeCountAbove (M : IntermediateField ℚ N) (𝔭 : NK.Chebotarev.PrimeIdeal ℚ) : ℕ :=
  Nat.card {𝔓 : NK.Chebotarev.PrimeIdeal ↥M // 𝔓.asIdeal.LiesOver 𝔭.asIdeal}

/-- **The place-indexed form of `NK.WeakNU.PrimeCountOrbitInput`.**

This is the counting statement in terms of a finite place `𝔭` of `ℚ` rather than a rational prime
`p ∈ ℕ`, i.e. in the vocabulary of `primeCountAbove` and `primeOrbitCount`.  It is the form in which
the counting statement is proved (`Submission/Work/WeakNU/PrimeCount.lean`); the bridge to the
natural-prime-indexed form of `NK.WeakNU.PrimeCountOrbitInput` is
`NK.WeakNU.primeCountAbove_under_eq_primesOverRat`. -/
def PrimeCountOrbitInputPlace : Prop :=
  ∀ (N : Type) [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N]
    (M : IntermediateField ℚ N) (𝔭 : NK.Chebotarev.PrimeIdeal ℚ),
    (∀ P : NK.Chebotarev.PrimeIdeal N, P.asIdeal.LiesOver 𝔭.asIdeal →
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1) →
    ∀ σ : Gal(N/ℚ),
      (∃ P : NK.Chebotarev.PrimeIdeal N,
        P.asIdeal.LiesOver 𝔭.asIdeal ∧ NK.Chebotarev.IsFrobAt P σ) →
      primeCountAbove M 𝔭 = orbitCount σ (Gal(N/ℚ) ⧸ M.fixingSubgroup)

end

end NK.WeakNU
