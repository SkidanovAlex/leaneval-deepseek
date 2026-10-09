/-
Work of the Neukirch–Uchida team: the general Čebotarev density theorem.

# The number of primes above an unramified prime at which `σ` is a Frobenius

Let `N/K` be a finite Galois extension of number fields, `𝔭` a prime of `K` unramified in `N` and
`σ ∈ Gal(N/K)` an element which is a Frobenius element at some prime of `𝓞 N` above `𝔭`.  The
primes of `𝓞 N` above `𝔭` at which `σ` is a Frobenius element are then the `⟨σ⟩`-orbit of a single
one of them, so their number is `|C_G(σ)| / ord(σ)`:

`card_isFrobAt_liesOver_mul_orderOf`.

The proof is orbit–stabiliser for the action of the centraliser `C_G(σ)` on the primes above `𝔭`,
together with the two classical facts that the action of `Gal(N/K)` on the primes above `𝔭` is
transitive and that the Frobenius element at an unramified prime is unique.
-/
import Mathlib
import Submission.NK.ChebotarevGeneral.Defs
import Submission.NK.ChebotarevGeneral.decompositionSubgroup_eq_zpowers_of_isFrobAt
import Submission.NK.Chebotarev.IsFrobAtConj
import Submission.Commons.NumberTheory.NumberField.finite_primesOver
import Submission.Commons.NumberTheory.RamificationInertia.exists_map_galRestrict_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.ChebotarevGeneral

noncomputable section

open NK.Chebotarev

variable {K N : Type*} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]

/-! ## The Galois action on the primes above a fixed place -/

/-- The action of `Gal(N/K)` on the finite places of `N` agrees with the `placeSmul` action of
`Submission.NeukirchUchida.Local`. -/
theorem smul_primeIdeal_eq_placeSmul (τ : Gal(N/K)) (P : PrimeIdeal N) :
    τ • P = Submission.NeukirchUchida.Local.placeSmul τ P := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [smul_primeIdeal_asIdeal, Submission.NeukirchUchida.Local.placeSmul_asIdeal]

theorem smul_primeIdeal_mul (τ₁ τ₂ : Gal(N/K)) (P : PrimeIdeal N) :
    (τ₁ * τ₂) • P = τ₁ • (τ₂ • P) := by
  rw [smul_primeIdeal_eq_placeSmul (τ₁ * τ₂) P, smul_primeIdeal_eq_placeSmul τ₂ P,
    smul_primeIdeal_eq_placeSmul τ₁ (Submission.NeukirchUchida.Local.placeSmul τ₂ P),
    Submission.NeukirchUchida.Local.placeSmul_mul]

theorem smul_primeIdeal_one (P : PrimeIdeal N) : (1 : Gal(N/K)) • P = P := by
  rw [smul_primeIdeal_eq_placeSmul, Submission.NeukirchUchida.Local.placeSmul_one]

/-- **The action preserves the primes above the base prime.** -/
theorem liesOver_smul {𝔭 : PrimeIdeal K} {P : PrimeIdeal N} (hP : P.asIdeal.LiesOver 𝔭.asIdeal)
    (τ : Gal(N/K)) : (τ • P).asIdeal.LiesOver 𝔭.asIdeal := by
  haveI := hP
  rw [smul_primeIdeal_asIdeal]
  exact Commons.NumberTheory.NumberField.liesOver_map_galRestrict 𝔭 P τ

/-- **Transitivity of the Galois action on the primes above a fixed prime.** -/
theorem exists_smul_eq_of_liesOver {𝔭 : PrimeIdeal K} {P₀ P : PrimeIdeal N}
    (hP₀ : P₀.asIdeal.LiesOver 𝔭.asIdeal) (hP : P.asIdeal.LiesOver 𝔭.asIdeal) :
    ∃ τ : Gal(N/K), τ • P₀ = P := by
  haveI := hP₀
  haveI := hP
  obtain ⟨σ, hσ⟩ :=
    Commons.NumberTheory.RamificationInertia.exists_map_galRestrict_eq (K := K) (L := N) 𝔭 P₀ P
  exact ⟨σ, IsDedekindDomain.HeightOneSpectrum.ext (by rw [smul_primeIdeal_asIdeal, hσ])⟩

/-- **The action of `Gal(N/K)` on the primes of `𝓞 N` above a fixed prime `𝔭` of `K`.** -/
instance instMulActionPrimesOver {𝔭 : PrimeIdeal K} :
    MulAction Gal(N/K) {P : PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal} where
  smul τ P := ⟨τ • P.1, liesOver_smul P.2 τ⟩
  one_smul P := Subtype.ext (smul_primeIdeal_one P.1)
  mul_smul τ₁ τ₂ P := Subtype.ext (smul_primeIdeal_mul τ₁ τ₂ P.1)

@[simp]
theorem smul_primesOver_val {𝔭 : PrimeIdeal K} (τ : Gal(N/K))
    (P : {P : PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal}) : (τ • P).1 = τ • P.1 := rfl

/-- Only finitely many primes of `𝓞 N` lie above a given prime of `𝓞 K`. -/
instance finite_primesOver_subtype {𝔭 : PrimeIdeal K} :
    Finite {P : PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal} := by
  have hfin : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers N)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot
  haveI := hfin.to_subtype
  refine Finite.of_injective
    (fun P : {P : PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal} =>
      (⟨P.1.asIdeal, P.1.isPrime, P.2⟩ :
        𝔭.asIdeal.primesOver (NumberField.RingOfIntegers N))) ?_
  intro P Q h
  exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext (Subtype.ext_iff.mp h))

/-! ## Frobenius elements and the centraliser -/

/-- **`σ` is a Frobenius element at the conjugate `τ • P₀` if and only if `τ` commutes with `σ`**,
the prime `P₀` being unramified over `𝔭` and `σ` being a Frobenius element at `P₀`. -/
theorem isFrobAt_smul_iff_mem_centralizer {𝔭 : PrimeIdeal K}
    (hunr : ∀ P : PrimeIdeal N, P.asIdeal.LiesOver 𝔭.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    {P₀ : PrimeIdeal N} (hP₀ : P₀.asIdeal.LiesOver 𝔭.asIdeal)
    {σ : Gal(N/K)} (hfrob : IsFrobAt P₀ σ) (τ : Gal(N/K)) :
    IsFrobAt (τ • P₀) σ ↔ τ ∈ Subgroup.centralizer ({σ} : Set (Gal(N/K))) := by
  have hlies : (τ • P₀).asIdeal.LiesOver 𝔭.asIdeal := liesOver_smul hP₀ τ
  have he : (τ • P₀).asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := hunr _ hlies
  constructor
  · intro h
    have hconj : IsFrobAt (τ • P₀) (τ * σ * τ⁻¹) := IsFrobAtConj hfrob
    have heq : τ * σ * τ⁻¹ = σ := IsFrobAt.eq_of_isFrobAt hlies he hconj h
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp heq
  · intro h
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    have hconj : IsFrobAt (τ • P₀) (τ * σ * τ⁻¹) := IsFrobAtConj hfrob
    have heq : τ * σ * τ⁻¹ = σ := by
      rw [h]
      group
    rwa [heq] at hconj

/-! ## The main count -/

/-- **The number of primes of `N` above an unramified prime of `K` at which `σ` is a Frobenius
element.**  If such a prime exists, this number is `|C_G(σ)| / ord(σ)`. -/
theorem card_isFrobAt_liesOver_mul_orderOf {K N : Type*} [Field K] [NumberField K]
    [Field N] [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    {𝔭 : NK.Chebotarev.PrimeIdeal K}
    (hunr : ∀ P : NK.Chebotarev.PrimeIdeal N, P.asIdeal.LiesOver 𝔭.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    {σ : Gal(N/K)}
    (hσ : ∃ P : NK.Chebotarev.PrimeIdeal N, P.asIdeal.LiesOver 𝔭.asIdeal ∧
      NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ) :
    Nat.card {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal ∧
        NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ} * orderOf σ =
      Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) := by
  classical
  obtain ⟨P₀, hP₀, hfrob₀⟩ := hσ
  -- `P₀` is unramified over `𝔭`, and the decomposition group of `P₀` is generated by `σ`
  have hram₀ : P₀.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := hunr P₀ hP₀
  have hD : Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) P₀ =
      Subgroup.zpowers σ :=
    decompositionSubgroup_eq_zpowers_of_isFrobAt (K := K) (N := N) P₀ σ hram₀ hfrob₀
  -- the centraliser of `σ`, as a subgroup of `Gal(N/K)`
  let C : Subgroup Gal(N/K) := Subgroup.centralizer ({σ} : Set (Gal(N/K)))
  have hCdef : C = Subgroup.centralizer ({σ} : Set (Gal(N/K))) := rfl
  have hσC : σ ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
  have hzpC : Subgroup.zpowers σ ≤ C := Subgroup.zpowers_le.mpr hσC
  -- `P₀` as an element of the type of primes of `𝓞 N` above `𝔭`
  let P₀' : {P : PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal} := ⟨P₀, hP₀⟩
  -- the stabiliser of `P₀` in `Gal(N/K)` is `⟨σ⟩`
  have hstabG : ∀ g : Gal(N/K), g • P₀' = P₀' ↔ g ∈ Subgroup.zpowers σ := by
    intro g
    constructor
    · intro h
      have h1 : g • P₀ = P₀ := congrArg Subtype.val h
      rw [smul_primeIdeal_eq_placeSmul] at h1
      exact hD ▸ (Submission.NeukirchUchida.Local.mem_decompositionSubgroup (K := K)
        (w := P₀)).mpr h1
    · intro h
      have h1 : Submission.NeukirchUchida.Local.placeSmul g P₀ = P₀ :=
        (Submission.NeukirchUchida.Local.mem_decompositionSubgroup (K := K)
          (w := P₀)).mp (hD ▸ h)
      apply Subtype.ext
      show g • P₀ = P₀
      rw [smul_primeIdeal_eq_placeSmul, h1]
  -- the stabiliser of `P₀` in the centraliser is still `⟨σ⟩`
  have hstabC : ∀ c : C, c ∈ MulAction.stabilizer C P₀' ↔
      (c : Gal(N/K)) ∈ Subgroup.zpowers σ := by
    intro c
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    exact hstabG c.1
  have hstab_card : Nat.card ↥(MulAction.stabilizer C P₀') = orderOf σ := by
    have est : ↥(MulAction.stabilizer C P₀') ≃ ↥(Subgroup.zpowers σ) :=
      { toFun := fun c => ⟨(c.1 : Gal(N/K)), (hstabC c.1).mp c.2⟩
        invFun := fun d => ⟨⟨(d : Gal(N/K)), hzpC d.2⟩, (hstabC ⟨(d : Gal(N/K)), hzpC d.2⟩).mpr d.2⟩
        left_inv := fun c => Subtype.ext (Subtype.ext rfl)
        right_inv := fun d => Subtype.ext rfl }
    rw [Nat.card_congr est, Nat.card_zpowers]
  -- the primes at which `σ` is a Frobenius element are the orbit of `P₀` under the centraliser
  have horbit_iff : ∀ P : {P : PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal},
      IsFrobAt P.1 σ ↔ P ∈ MulAction.orbit C P₀' := by
    intro P
    rw [MulAction.mem_orbit_iff]
    constructor
    · intro hP
      obtain ⟨τ, hτ⟩ := exists_smul_eq_of_liesOver (K := K) (N := N) hP₀ P.2
      have hτC : τ ∈ C := by
        rw [hCdef]
        exact (isFrobAt_smul_iff_mem_centralizer (K := K) (N := N) hunr hP₀ hfrob₀ τ).mp
          (hτ ▸ hP)
      exact ⟨⟨τ, hτC⟩, Subtype.ext (by show τ • P₀ = P.1; exact hτ)⟩
    · rintro ⟨c, hc⟩
      have hval : P.1 = (c : Gal(N/K)) • P₀ := by
        have h1 : (c • P₀').1 = P.1 := congrArg Subtype.val hc
        rw [Subgroup.smul_def] at h1
        exact h1.symm
      have hc2 : (c : Gal(N/K)) ∈ Subgroup.centralizer ({σ} : Set (Gal(N/K))) := c.2
      rw [hval]
      exact (isFrobAt_smul_iff_mem_centralizer (K := K) (N := N) hunr hP₀ hfrob₀
        (c : Gal(N/K))).mpr hc2
  -- orbit–stabiliser for the action of the centraliser
  letI : Fintype ↥C := Fintype.ofFinite ↥C
  letI : Fintype ↥(MulAction.orbit C P₀') := Fintype.ofFinite ↥(MulAction.orbit C P₀')
  letI : Fintype ↥(MulAction.stabilizer C P₀') := Fintype.ofFinite ↥(MulAction.stabilizer C P₀')
  have hOS : Nat.card ↥(MulAction.orbit C P₀') * orderOf σ = Nat.card ↥C := by
    rw [← hstab_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group C P₀'
  -- the set of interest is the `C`-orbit of `P₀`
  have hS : Nat.card {P : PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal ∧ IsFrobAt P σ}
      = Nat.card ↥(MulAction.orbit C P₀') := by
    have e₁ : {P : PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal ∧ IsFrobAt P σ} ≃
        {P : {Q : PrimeIdeal N // Q.asIdeal.LiesOver 𝔭.asIdeal} // IsFrobAt P.1 σ} :=
      { toFun := fun P => ⟨⟨P.1, P.2.1⟩, P.2.2⟩
        invFun := fun Q => ⟨Q.1.1, Q.1.2, Q.2⟩
        left_inv := fun P => rfl
        right_inv := fun Q => rfl }
    have e₂ : {P : {Q : PrimeIdeal N // Q.asIdeal.LiesOver 𝔭.asIdeal} // IsFrobAt P.1 σ} ≃
        {P : {Q : PrimeIdeal N // Q.asIdeal.LiesOver 𝔭.asIdeal} // P ∈ MulAction.orbit C P₀'} :=
      Equiv.subtypeEquivRight (fun P => horbit_iff P)
    rw [Nat.card_congr e₁, Nat.card_congr e₂]
  calc Nat.card {P : PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal ∧ IsFrobAt P σ} * orderOf σ
      = Nat.card ↥(MulAction.orbit C P₀') * orderOf σ := by rw [hS]
    _ = Nat.card ↥C := hOS
    _ = Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) := by rw [hCdef]

end

end NK.ChebotarevGeneral
