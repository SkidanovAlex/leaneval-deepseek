import Mathlib
import Submission.NK.WeakNU.PrimeOrbit

/-!
# The primes above a place as the orbits of the fixing subgroup

This file proves

`NK.WeakNU.primeCountAbove_eq_primeOrbitCount`,

the classical count of the primes of an intermediate field `M ⊆ N` above a finite place `𝔭` of `ℚ`
as the number of orbits of `M.fixingSubgroup = Gal(N/M)` on the primes of `𝓞 N` above `𝔭`.

The mathematical content is the fibre–torsor argument: the contraction map
`𝔓 ↦ 𝔓 ∩ 𝓞 M` from the primes of `𝓞 N` above `𝔭` onto the primes of `𝓞 M` above `𝔭` has, as its
fibres, exactly the orbits of `Gal(N/M) = M.fixingSubgroup`.  Surjectivity is the lying over
theorem, and the fibre statement is the transitivity of the Galois action on the primes above a
fixed prime (`Algebra.IsInvariant.exists_smul_of_under_eq` in the AKLB setup `𝓞 M ⊆ 𝓞 N`),
together with the invariance of the contraction under the action of `Gal(N/M)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.WeakNU

noncomputable section

open scoped Pointwise

variable {N : Type} [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N]
variable (M : IntermediateField ℚ N)

/-! ## Two generalities on `Ideal.map` -/

/-- Two ring homomorphisms with the same underlying function induce the same map on ideals. -/
lemma ideal_map_congr_apply {R S : Type*} [Semiring R] [Semiring S] {f g : R →+* S}
    (h : ∀ x, f x = g x) (I : Ideal R) : I.map f = I.map g := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, h x]
    exact Ideal.mem_map_of_mem g hx
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← h x]
    exact Ideal.mem_map_of_mem f hx

/-- A surjective ring endomorphism of `B` which fixes the image of `A` preserves the contraction
of ideals along `A`. -/
lemma ideal_under_map_eq_of_fixes {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (f : B →+* B) (hinj : Function.Injective f)
    (hf : ∀ x : A, f (algebraMap A B x) = algebraMap A B x)
    (hsurj : Function.Surjective f) (I : Ideal B) :
    (Ideal.map f I).under A = I.under A := by
  rw [Ideal.under_def, Ideal.under_def]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_map_iff_of_surjective f hsurj]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy' : y = algebraMap A B x := hinj (by rw [hyx, hf x])
    rwa [hy'] at hy
  · intro hx
    exact ⟨algebraMap A B x, hx, hf x⟩

/-! ## The contraction of a prime over `𝔭` -/

section ResPrime

variable (𝔭 : NK.Chebotarev.PrimeIdeal ℚ)

/-- The contraction `𝔓 ∩ 𝓞 M` of a prime of `𝓞 N` is a prime of `𝓞 M`. -/
lemma under_isPrime (P : NK.Chebotarev.PrimeIdeal N) :
    (P.asIdeal.under (NumberField.RingOfIntegers ↥M)).IsPrime := by
  haveI : P.asIdeal.IsPrime := P.isPrime
  infer_instance

/-- If `𝔓` lies over `𝔭` then so does its contraction to `𝓞 M`. -/
lemma under_liesOver {P : NK.Chebotarev.PrimeIdeal N} (hP : P.asIdeal.LiesOver 𝔭.asIdeal) :
    (P.asIdeal.under (NumberField.RingOfIntegers ↥M)).LiesOver 𝔭.asIdeal := by
  haveI : P.asIdeal.LiesOver (P.asIdeal.under (NumberField.RingOfIntegers ↥M)) :=
    Ideal.over_under P.asIdeal
  exact Ideal.LiesOver.tower_bot P.asIdeal (P.asIdeal.under (NumberField.RingOfIntegers ↥M))
    𝔭.asIdeal

/-- The contraction of a prime of `𝓞 N` lying over `𝔭` is nonzero. -/
lemma under_ne_bot {P : NK.Chebotarev.PrimeIdeal N} (hP : P.asIdeal.LiesOver 𝔭.asIdeal) :
    P.asIdeal.under (NumberField.RingOfIntegers ↥M) ≠ ⊥ := by
  haveI : P.asIdeal.LiesOver (P.asIdeal.under (NumberField.RingOfIntegers ↥M)) :=
    Ideal.over_under P.asIdeal
  haveI : (P.asIdeal.under (NumberField.RingOfIntegers ↥M)).LiesOver 𝔭.asIdeal :=
    under_liesOver M 𝔭 hP
  exact Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _

/-- **The contraction map** from the primes of `𝓞 N` above `𝔭` to the primes of `𝓞 M`
above `𝔭`. -/
def resPrime (P : {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal}) :
    {𝔮 : NK.Chebotarev.PrimeIdeal ↥M // 𝔮.asIdeal.LiesOver 𝔭.asIdeal} :=
  ⟨⟨P.1.asIdeal.under (NumberField.RingOfIntegers ↥M), under_isPrime M P.1,
      under_ne_bot M 𝔭 P.2⟩, under_liesOver M 𝔭 P.2⟩

@[simp]
lemma resPrime_asIdeal (P : {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal}) :
    (resPrime M 𝔭 P).1.asIdeal = P.1.asIdeal.under (NumberField.RingOfIntegers ↥M) := rfl

end ResPrime

/-! ## The action of the fixing subgroup preserves the contraction -/

/-- **Invariance of the contraction under the fixing subgroup.**  An element `h` of
`M.fixingSubgroup` acts on the primes of `𝓞 N` by an automorphism of the `𝓞 M`-algebra `𝓞 N`,
hence preserves the contraction to `𝓞 M`. -/
lemma under_placeAct_eq_of_mem_fixingSubgroup (h : M.fixingSubgroup)
    (P : NK.Chebotarev.PrimeIdeal N) :
    (placeAct (h : Gal(N/ℚ)) P).asIdeal.under (NumberField.RingOfIntegers ↥M) =
      P.asIdeal.under (NumberField.RingOfIntegers ↥M) := by
  have hfx : ∀ x : NumberField.RingOfIntegers ↥M,
      (galRestrict (NumberField.RingOfIntegers ℚ) ℚ N (NumberField.RingOfIntegers N)
        (h : Gal(N/ℚ)) : NumberField.RingOfIntegers N →+* NumberField.RingOfIntegers N)
        (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) x)
      = algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) x := by
    intro x
    show galRestrict (NumberField.RingOfIntegers ℚ) ℚ N (NumberField.RingOfIntegers N)
        (h : Gal(N/ℚ)) (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) x)
      = algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) x
    apply NumberField.RingOfIntegers.coe_injective
    rw [algebraMap_galRestrict_apply]
    rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M)
      (NumberField.RingOfIntegers N) N x]
    rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M) (↥M) N x]
    exact (IntermediateField.mem_fixingSubgroup_iff M (h : Gal(N/ℚ))).mp h.2 _
      (algebraMap (NumberField.RingOfIntegers ↥M) ↥M x).2
  rw [placeAct_asIdeal]
  exact ideal_under_map_eq_of_fixes _ (fun a b hab =>
      (galRestrict (NumberField.RingOfIntegers ℚ) ℚ N (NumberField.RingOfIntegers N)
        (h : Gal(N/ℚ))).injective hab) hfx
    (galRestrict (NumberField.RingOfIntegers ℚ) ℚ N
      (NumberField.RingOfIntegers N) (h : Gal(N/ℚ))).surjective P.asIdeal

/-! ## The fibres of the contraction map are the orbits of the fixing subgroup -/

/-- **The transversal (fibre) statement.**  Two primes of `𝓞 N` with the same contraction to
`𝓞 M` are conjugate under `Gal(N/M) = M.fixingSubgroup`.

This is `Algebra.IsInvariant.exists_smul_of_under_eq` for the AKLB setup
`𝓞 M ⊆ M ⊆ N`, transported to the `ℚ`-base Galois action `placeAct`. -/
lemma exists_mem_fixingSubgroup_placeAct_eq_of_under_eq (P Q : NK.Chebotarev.PrimeIdeal N)
    (h : P.asIdeal.under (NumberField.RingOfIntegers ↥M) =
      Q.asIdeal.under (NumberField.RingOfIntegers ↥M)) :
    ∃ h' : M.fixingSubgroup, placeAct (h' : Gal(N/ℚ)) P = Q := by
  letI act : MulSemiringAction Gal(N/↥M) (NumberField.RingOfIntegers N) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers ↥M) ↥M N
      (NumberField.RingOfIntegers N)
  haveI inv : Algebra.IsInvariant (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N)
      Gal(N/↥M) :=
    Algebra.isInvariant_of_isGalois (NumberField.RingOfIntegers ↥M) ↥M N (NumberField.RingOfIntegers N)
  haveI scc : SMulCommClass Gal(N/↥M) (NumberField.RingOfIntegers ↥M)
      (NumberField.RingOfIntegers N) :=
    ⟨fun g a b => by
      show galRestrict (NumberField.RingOfIntegers ↥M) ↥M N (NumberField.RingOfIntegers N) g
          (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) a * b)
        = algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) a *
          galRestrict (NumberField.RingOfIntegers ↥M) ↥M N (NumberField.RingOfIntegers N) g b
      rw [map_mul, AlgEquiv.commutes]⟩
  haveI hP : P.asIdeal.IsPrime := P.isPrime
  haveI hQ : Q.asIdeal.IsPrime := Q.isPrime
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (NumberField.RingOfIntegers ↥M)
    (NumberField.RingOfIntegers N) Gal(N/↥M) P.asIdeal Q.asIdeal h
  let hfix : M.fixingSubgroup := ⟨g.restrictScalars ℚ, by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    show g x = x
    exact g.commutes ⟨x, hx⟩⟩
  have hgh : ∀ x : N, (hfix : Gal(N/ℚ)) x = g x := fun x => rfl
  refine ⟨hfix, ?_⟩
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [placeAct_asIdeal, hg, Ideal.pointwise_smul_def]
  have key : ∀ x : NumberField.RingOfIntegers N,
      (↑(galRestrict (NumberField.RingOfIntegers ℚ) ℚ N (NumberField.RingOfIntegers N)
          (hfix : Gal(N/ℚ)) :
        NumberField.RingOfIntegers N →+* NumberField.RingOfIntegers N) :
          NumberField.RingOfIntegers N → NumberField.RingOfIntegers N) x
      = (MulSemiringAction.toRingHom Gal(N/↥M) (NumberField.RingOfIntegers N) g :
          NumberField.RingOfIntegers N → NumberField.RingOfIntegers N) x := by
    intro x
    apply NumberField.RingOfIntegers.coe_injective
    show algebraMap (NumberField.RingOfIntegers N) N
        (galRestrict (NumberField.RingOfIntegers ℚ) ℚ N (NumberField.RingOfIntegers N)
          (hfix : Gal(N/ℚ)) x)
      = algebraMap (NumberField.RingOfIntegers N) N
        (galRestrict (NumberField.RingOfIntegers ↥M) ↥M N (NumberField.RingOfIntegers N) g x)
    rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
    exact hgh x
  exact ideal_map_congr_apply key P.asIdeal

/-! ## The bijection -/

section Quotient

variable (𝔭 : NK.Chebotarev.PrimeIdeal ℚ)

/-- **The contraction map is well defined on the orbits of the fixing subgroup.** -/
def resQuot :
    Quotient (primeOrbitSetoid M.fixingSubgroup 𝔭) →
      {𝔮 : NK.Chebotarev.PrimeIdeal ↥M // 𝔮.asIdeal.LiesOver 𝔭.asIdeal} :=
  Quotient.lift (resPrime M 𝔭) (fun P Q h => by
    apply Subtype.ext
    apply IsDedekindDomain.HeightOneSpectrum.ext
    obtain ⟨h', hh'⟩ := h
    rw [resPrime_asIdeal, resPrime_asIdeal, ← hh']
    exact (under_placeAct_eq_of_mem_fixingSubgroup M h' P.1).symm)

lemma resQuot_mk (P : {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal}) :
    resQuot M 𝔭 (Quotient.mk (primeOrbitSetoid M.fixingSubgroup 𝔭) P) = resPrime M 𝔭 P :=
  rfl

/-- **The fibres of the contraction map are exactly the orbits**: two primes of `𝓞 N` above `𝔭`
have the same contraction to `𝓞 M` if and only if they are conjugate under `M.fixingSubgroup`. -/
lemma resPrime_eq_iff (P Q : {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal}) :
    resPrime M 𝔭 P = resPrime M 𝔭 Q ↔ SamePrimeOrbit M.fixingSubgroup 𝔭 P Q := by
  constructor
  · intro h
    have h' : P.1.asIdeal.under (NumberField.RingOfIntegers ↥M) =
        Q.1.asIdeal.under (NumberField.RingOfIntegers ↥M) := by
      rw [← resPrime_asIdeal M 𝔭 P, ← resPrime_asIdeal M 𝔭 Q, h]
    exact exists_mem_fixingSubgroup_placeAct_eq_of_under_eq M P.1 Q.1 h'
  · rintro ⟨h', hh'⟩
    apply Subtype.ext
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [resPrime_asIdeal, resPrime_asIdeal, ← hh']
    exact (under_placeAct_eq_of_mem_fixingSubgroup M h' P.1).symm

lemma resQuot_injective : Function.Injective (resQuot M 𝔭) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h P =>
    induction y using Quotient.inductionOn with
    | h Q =>
      refine Quotient.sound ?_
      refine (resPrime_eq_iff M 𝔭 P Q).mp ?_
      rw [← resQuot_mk M 𝔭 P, ← resQuot_mk M 𝔭 Q]
      exact hxy

lemma resQuot_surjective : Function.Surjective (resQuot M 𝔭) := by
  intro 𝔮
  obtain ⟨P, hP⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := ↥M) (L := N) 𝔮.1
  have hlies : P.asIdeal.LiesOver 𝔭.asIdeal := by
    haveI : P.asIdeal.LiesOver 𝔮.1.asIdeal := hP
    haveI : 𝔮.1.asIdeal.LiesOver 𝔭.asIdeal := 𝔮.2
    exact Ideal.LiesOver.trans P.asIdeal 𝔮.1.asIdeal 𝔭.asIdeal
  let P' : {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal} := ⟨P, hlies⟩
  refine ⟨Quotient.mk (primeOrbitSetoid M.fixingSubgroup 𝔭) P', ?_⟩
  rw [resQuot_mk]
  apply Subtype.ext
  apply IsDedekindDomain.HeightOneSpectrum.ext
  exact (Ideal.LiesOver.over : 𝔮.1.asIdeal = P.asIdeal.under (NumberField.RingOfIntegers ↥M)).symm

/-- **The primes of `𝓞 ↥M` above `𝔭` are the orbits of `M.fixingSubgroup` on the primes of
`𝓞 N` above `𝔭`.** -/
def primeOrbitEquivPrimesAbove :
    Quotient (primeOrbitSetoid M.fixingSubgroup 𝔭) ≃
      {𝔮 : NK.Chebotarev.PrimeIdeal ↥M // 𝔮.asIdeal.LiesOver 𝔭.asIdeal} :=
  Equiv.ofBijective (resQuot M 𝔭) ⟨resQuot_injective M 𝔭, resQuot_surjective M 𝔭⟩

end Quotient

end

/-- **The number of primes of `𝓞 ↥M` above `𝔭` is the number of orbits of
`M.fixingSubgroup = Gal(N/M)` on the primes of `𝓞 N` above `𝔭`.**

This is the fibre–torsor argument: the contraction `𝔓 ↦ 𝔓 ∩ 𝓞 M` is a surjection (lying over)
whose fibres are exactly the `Gal(N/M)`-orbits (transitivity of the Galois action on the primes
above a fixed prime). -/
theorem primeCountAbove_eq_primeOrbitCount {N : Type} [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N] (M : IntermediateField ℚ N) (𝔭 : NK.Chebotarev.PrimeIdeal ℚ) : NK.WeakNU.primeCountAbove M 𝔭 = NK.WeakNU.primeOrbitCount M.fixingSubgroup 𝔭 := by
  exact (Nat.card_congr (primeOrbitEquivPrimesAbove M 𝔭)).symm

end NK.WeakNU
