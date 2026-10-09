import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Chebotarev.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Splitting primes and the base change of Frobenius elements

This file supplies the two ingredients of Shimizu's Proposition 4f.3
(arXiv:2009.10431, §4) that the naive statement misses: the escaping prime of `Γ_L` has to be
chosen among the primes of `L` which are **completely split over `ℚ`**, so that the residue
degrees in every intermediate extension are `1` and the base-change maps `π_{L/K_i}` send the
Frobenius element at the chosen prime to the *Frobenius element* at its contraction (rather than
to a power of it — the trap recorded in README §19.8).

## Contents

* `SplitsCompletelyOverRat 𝔭` — `𝔭` is unramified over `ℚ` with residue degree one;
* `natCard_quot_eq_of_inertiaDeg_eq_one` — the residue fields of `𝔭` over two base fields agree
  when the intermediate inertia degree is one (this is what makes `IsFrobAt` independent of the
  base field);
* `isFrobAt_of_isFrobAt_restrictScalars` — **the base change of Frobenius elements**: over a tower
  `K ⊆ L ⊆ M` with `f(P∩L | P∩K) = 1`, an element `τ ∈ Gal(M/L)` which is a Frobenius at `P` in
  the sense of the base field `K` is also one in the sense of the base field `L`;
* `inertiaDeg_eq_one_of_splitsCompletelyOverRat`,
  `ramificationIdx_eq_one_of_splitsCompletelyOverRat` — the transfer of the splitting condition
  down to every intermediate field;
* `isFrobElementAt_restrictScalars` — the pointwise step of Proposition 4f.3 that failed in the
  un-split setting: at a prime completely split over `ℚ`, a Frobenius element over `L` restricts to
  a Frobenius element over `K ⊆ L`;
* `isFrobElementAt_iff_forall_frobLevel` — `IsFrobElementAt` indexed by `FrobLevel`'s;
* `exists_split_frobAt` — **Čebotarev with a completely split prime**: from the Čebotarev input
  over `ℚ` one gets, for every finite Galois level `N/L` and every `τ ∈ Gal(N/L)`, a prime `𝔭` of
  `L` completely split over `ℚ` with `τ` a Frobenius at a prime above `𝔭`.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4;
J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. XII §12.2.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

open NK.Chebotarev
open scoped NumberField

/-! ## The splitting condition -/

section Splits

variable {L : Type*} [Field L] [NumberField L]

/-- **`𝔭` is completely split over `ℚ`**: `𝔭` is unramified over the rational prime below it and
has residue degree one. -/
def SplitsCompletelyOverRat (𝔭 : PrimeIdeal L) : Prop :=
  𝔭.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) = 1 ∧
    𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1

end Splits

/-! ## The residue-field cardinality is a base-independent notion of inertia degree -/

/-- **The residue-field cardinalities agree when the inertia degree is one.**  For a tower of
number rings `A ⊆ B ⊆ C` and a prime `q` of `B` over `A`, if the inertia degree of `q` over `A` is
one then `A ⧸ q ∩ A` and `B ⧸ q` are equinumerous. -/
theorem natCard_quot_eq_of_inertiaDeg_eq_one {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (q : Ideal B) [q.IsMaximal]
    (h : q.inertiaDeg A = 1) :
    Nat.card (A ⧸ q.under A) = Nat.card (B ⧸ q) := by
  have h1 : Submodule.cardQuot (q.under A) ^ q.inertiaDeg A = Submodule.cardQuot q :=
    Ideal.cardQuot_pow_inertiaDeg (q.under A) q
  rw [h, pow_one] at h1
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h1
  exact h1

/-! ## The base change of `IsFrobAt` -/

section BaseChange

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]

/-- The prime of `𝓞 K` under `P` does not depend on which intermediate base we contract through. -/
theorem under_under_spectrum (P : PrimeIdeal M) :
    (P.under (𝓞 L)).under (𝓞 K) = P.under (𝓞 K) :=
  IsDedekindDomain.HeightOneSpectrum.ext (Ideal.under_under P.asIdeal)

/-- **The underlying element of `𝓞 M` obtained by applying `galRestrict` to `x` does not depend on
the base ring** (only on the value of the algebra automorphism on `𝓞 M`). -/
theorem galRestrict_eq_of_restrictScalars (τ : Gal(M/L)) (x : 𝓞 M) :
    galRestrict (𝓞 L) L M (𝓞 M) τ x
      = galRestrict (𝓞 K) K M (𝓞 M) (τ.restrictScalars K) x :=
  NumberField.RingOfIntegers.ext (by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap,
      NumberField.RingOfIntegers.coe_eq_algebraMap,
      algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
    rfl)

/-- The `toAlgHom`-form of `galRestrict_eq_of_restrictScalars`. -/
theorem galRestrict_toAlgHom_apply (τ : Gal(M/L)) (x : 𝓞 M) :
    (galRestrict (𝓞 L) L M (𝓞 M) τ).toAlgHom x
      = (galRestrict (𝓞 K) K M (𝓞 M) (τ.restrictScalars K)).toAlgHom x := by
  simpa using galRestrict_eq_of_restrictScalars (K := K) (L := L) (M := M) τ x

/-- **The base change of a Frobenius element, in the reverse direction**: if `τ ∈ Gal(M/L)` is a
Frobenius element at `P` with respect to the base field `L`, and the residue degree of `P ∩ 𝓞 L`
over `P ∩ 𝓞 K` is one, then `τ`, viewed over `K`, is a Frobenius element at `P` with respect to the
base field `K`. -/
theorem isFrobAt_of_isFrobAt_of_inertiaDeg_eq_one (P : PrimeIdeal M) (τ : Gal(M/L))
    (hf : (Ideal.under (𝓞 L) P.asIdeal).inertiaDeg (𝓞 K) = 1)
    (h : IsFrobAt (K := L) (L := M) P τ) :
    IsFrobAt (K := K) (L := M) P (τ.restrictScalars K) := by
  have h1 : Ideal.under (𝓞 K) (Ideal.under (𝓞 L) P.asIdeal) = Ideal.under (𝓞 K) P.asIdeal :=
    Ideal.under_under P.asIdeal
  have hcard : Nat.card (𝓞 L ⧸ Ideal.under (𝓞 L) P.asIdeal)
      = Nat.card (𝓞 K ⧸ Ideal.under (𝓞 K) P.asIdeal) := by
    have h0 := natCard_quot_eq_of_inertiaDeg_eq_one (A := 𝓞 K) (B := 𝓞 L)
      (q := Ideal.under (𝓞 L) P.asIdeal) hf
    rw [← h0]
    exact congrArg (fun I : Ideal (𝓞 K) => Nat.card (𝓞 K ⧸ I)) h1
  intro x
  have hx := h x
  rw [← galRestrict_toAlgHom_apply (K := K) (L := L) (M := M) τ x, ← hcard]
  exact hx

/-- **The base change of a Frobenius element.**  Let `K ⊆ L ⊆ M` be a tower of number fields with
`P` a prime of `𝓞 M` and `τ ∈ Gal(M/L)`.  If the residue degree of `P ∩ 𝓞 L` over `P ∩ 𝓞 K`
is one, then `τ` is a Frobenius element at `P` with respect to the base field `L` whenever
`τ`, viewed over `K`, is one with respect to the base field `K`. -/
theorem isFrobAt_of_isFrobAt_restrictScalars (P : PrimeIdeal M) (τ : Gal(M/L))
    (hf : (Ideal.under (𝓞 L) P.asIdeal).inertiaDeg (𝓞 K) = 1)
    (h : IsFrobAt (K := K) (L := M) P (τ.restrictScalars K)) :
    IsFrobAt (K := L) (L := M) P τ := by
  have h1 : Ideal.under (𝓞 K) (Ideal.under (𝓞 L) P.asIdeal) = Ideal.under (𝓞 K) P.asIdeal :=
    Ideal.under_under P.asIdeal
  have hcard : Nat.card (𝓞 L ⧸ Ideal.under (𝓞 L) P.asIdeal)
      = Nat.card (𝓞 K ⧸ Ideal.under (𝓞 K) P.asIdeal) := by
    have h0 := natCard_quot_eq_of_inertiaDeg_eq_one (A := 𝓞 K) (B := 𝓞 L)
      (q := Ideal.under (𝓞 L) P.asIdeal) hf
    rw [← h0]
    exact congrArg (fun I : Ideal (𝓞 K) => Nat.card (𝓞 K ⧸ I)) h1
  intro x
  have hx := h x
  rw [galRestrict_toAlgHom_apply (K := K) (L := L) (M := M) τ x, hcard]
  exact hx

end BaseChange
/-! ## Transferring the splitting condition to intermediate fields -/

section Transfer

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- A prime completely split over `ℚ` has residue degree one over every intermediate field. -/
theorem inertiaDeg_eq_one_of_splitsCompletelyOverRat (𝔭 : PrimeIdeal L)
    (h : SplitsCompletelyOverRat 𝔭) :
    𝔭.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have h1 : 𝔭.asIdeal.inertiaDeg (𝓞 ℚ)
      = (Ideal.under (𝓞 K) 𝔭.asIdeal).inertiaDeg (𝓞 ℚ) * 𝔭.asIdeal.inertiaDeg (𝓞 K) :=
    Ideal.inertiaDeg_tower (q := Ideal.under (𝓞 K) 𝔭.asIdeal) (r := 𝔭.asIdeal)
  rw [h.1] at h1
  exact (mul_eq_one.mp h1.symm).2

/-- A prime completely split over `ℚ` is unramified over every intermediate field. -/
theorem ramificationIdx_eq_one_of_splitsCompletelyOverRat (𝔭 : PrimeIdeal L)
    (h : SplitsCompletelyOverRat 𝔭) :
    𝔭.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have h1 : 𝔭.asIdeal.ramificationIdx (𝓞 ℚ)
      = (Ideal.under (𝓞 K) 𝔭.asIdeal).ramificationIdx (𝓞 ℚ) * 𝔭.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_tower (q := Ideal.under (𝓞 K) 𝔭.asIdeal) (r := 𝔭.asIdeal)
  rw [h.2] at h1
  exact (mul_eq_one.mp h1.symm).2

end Transfer
