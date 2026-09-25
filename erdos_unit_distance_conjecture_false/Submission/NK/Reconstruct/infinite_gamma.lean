import Mathlib
import Submission.NK.Reconstruct.proj_surjective
import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.ellRestrict_surjective

/-!
# `Γ_K` is infinite

`NK.Reconstruct.Gamma K K' ℓ` is Shimizu's `Γ_K = G_K^{ab,(ℓ)}`, the ℓ-part of the
abelianisation of the absolute Galois group `G_K = Gal(K'/K)` of a number field `K`, presented as
the projective limit of the finite ℓ-parts `Γ_{L,ℓ} = ℓ-part(Gal(L/K)^{ab})` over the finite normal
number-field levels `L` of `K'` over `K` (`NK.Reconstruct.FrobLevel`), with projections
`NK.Reconstruct.Gamma.proj L`.

This file proves that this projective limit is **infinite**:

  `NK.Reconstruct.infinite_gamma : Infinite (Gamma K K' ℓ)`.

## The argument

`Γ_K` is the projective limit of the finite groups `Γ_{L,ℓ}`, and the projections
`Γ_K → Γ_{L,ℓ}` are surjective (`NK.Reconstruct.proj_surjective`).  Hence `Γ_K` is infinite as
soon as the finite groups `Γ_{L,ℓ}` have unbounded cardinality, i.e. as soon as there are levels
`L` of arbitrarily large ℓ-part.  Such levels are supplied by the **cyclotomic levels**
`L = K(ζ_{ℓ^s})`, where `ζ_{ℓ^s}` is a primitive `ℓ^s`-th root of unity in the separable closure
`K'` (which, in characteristic `0`, contains all roots of unity):

* `Gal(K(ζ_{ℓ^s})/K)` is *abelian* (a cyclotomic extension), so its ℓ-part is the ℓ-part of
  `Gal(L/K)^{ab}` and hence a quotient of `Γ_K`;
* the ℓ-adic cyclotomic character embeds `Gal(K(ζ_{ℓ^s})/K)` into `(ℤ/ℓ^s)^×`, so its order
  divides `φ(ℓ^s) = ℓ^{s-1}(ℓ-1)`  (`card_gal_adjoin_dvd_of_isPrimitiveRoot`);
* the tower law together with `[ℚ(ζ_{ℓ^s}) : ℚ] = φ(ℓ^s)` gives
  `[K(ζ_{ℓ^s}) : ℚ] ≥ ℓ^{s-1}(ℓ-1)`, hence `[K(ζ_{ℓ^s}) : K] · [K : ℚ] ≥ ℓ^{s-1}(ℓ-1)`
  (`totient_le_finrank_adjoin_of_isPrimitiveRoot`).

Combining the two divisibility statements (`pow_dvd_of_dvd_mul_le`) shows that the ℓ-part of
`Gal(K(ζ_{ℓ^s})/K)` has order at least `ℓ^{s-1-[K:ℚ]}`, which is unbounded in `s`; the elementary
group-theoretic step `ellPart_card_ge_of_pow_dvd` then converts the ℓ-adic divisibility of the
order of `Γ_{L,ℓ}` into a lower bound for its cardinality.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace NK.Reconstruct

open Polynomial

/-! ## 1. Unbounded finite quotients force infinitude

The limit of a projective system of finite groups with surjective transition maps is infinite as
soon as the groups in the system have unbounded cardinality.  For `Γ_K` the transition maps are
surjective (`NK.Reconstruct.proj_surjective`), so a bound on the cardinality of `Γ_K` would bound
the cardinality of every `Γ_{L,ℓ}`. -/

section Infinitude

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']

/-- **Unbounded level ℓ-parts make `Γ_K` infinite.**  If for every `n` some finite level `L` has
`ℓ^n ≤ #Γ_{L,ℓ}`, then `Γ_K` is infinite. -/
theorem infinite_of_unbounded_ellPart (ℓ : ℕ) [Fact ℓ.Prime] [IsGalois K K']
    (h : ∀ n : ℕ, ∃ L : FrobLevel K K', ℓ ^ n ≤ Nat.card ↥(LevelEllPart L.L ℓ)) :
    Infinite (Gamma K K' ℓ) := by
  rw [← not_finite_iff_infinite]
  intro hfin
  haveI := hfin
  obtain ⟨L, hL⟩ := h (Nat.card (Gamma K K' ℓ) + 1)
  have hsurj : Function.Surjective (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L) :=
    proj_surjective (K := K) (K' := K') ℓ L
  have hle : Nat.card ↥(LevelEllPart L.L ℓ) ≤ Nat.card (Gamma K K' ℓ) :=
    Nat.card_le_card_of_surjective (fun f : Gamma K K' ℓ => Gamma.proj L f) hsurj
  have hlt : Nat.card (Gamma K K' ℓ) < ℓ ^ (Nat.card (Gamma K K' ℓ) + 1) := by
    have h2 : 2 ≤ ℓ := (Fact.out (p := ℓ.Prime)).two_le
    calc Nat.card (Gamma K K' ℓ) < 2 ^ Nat.card (Gamma K K' ℓ) := Nat.lt_two_pow_self
      _ ≤ 2 ^ (Nat.card (Gamma K K' ℓ) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ ℓ ^ (Nat.card (Gamma K K' ℓ) + 1) := Nat.pow_le_pow_left h2 _
  omega

end Infinitude

/-! ## 2. Primitive roots of unity in an algebraically closed field of characteristic `0`

In characteristic `0` a separable closure is an algebraic closure (Mathlib:
`IsSepClosure.isAlgClosure_of_perfectField`), so it contains roots of the cyclotomic polynomials
and hence primitive `ℓ^s`-th roots of unity. -/

section PrimitiveRoot

/-- **An algebraically closed field of characteristic zero contains primitive `ℓ^s`-th roots of
unity**: a root of the `ℓ^s`-th cyclotomic polynomial is a primitive `ℓ^s`-th root of unity
(`Polynomial.isRoot_cyclotomic_iff`), and such a root exists because the field is algebraically
closed and `cyclotomic (ℓ^s) K'` has positive degree (`Polynomial.degree_cyclotomic`,
`Nat.totient_prime_pow`). -/
theorem exists_isPrimitiveRoot_prime_pow (K' : Type*) [Field K'] [IsAlgClosed K'] [CharZero K']
    (ℓ s : ℕ) [Fact ℓ.Prime] (hs : 0 < s) :
    ∃ ζ : K', IsPrimitiveRoot ζ (ℓ ^ s) := by
  have h2 : ℓ ^ s ≠ 0 := pow_ne_zero s (Fact.out (p := ℓ.Prime)).ne_zero
  haveI : NeZero ((ℓ ^ s : ℕ) : K') := ⟨Nat.cast_ne_zero.mpr h2⟩
  have hne : (cyclotomic (ℓ ^ s) K').degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    have hpos : 0 < (ℓ ^ s).totient :=
      Nat.totient_pos.mpr (pow_pos (Fact.out (p := ℓ.Prime)).pos s)
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  exact ⟨_, isRoot_cyclotomic_iff.mp (Classical.choose_spec (IsAlgClosed.exists_root _ hne))⟩

end PrimitiveRoot

/-! ## 3. The cyclotomic level, and the two arithmetic bounds on it

For `ζ` a primitive `ℓ^s`-th root of unity in `K'`, `K⟮ζ⟯` is a cyclotomic (hence finite Galois
abelian) extension of `K`, and therefore a finite normal number-field level, i.e. an element of
`FrobLevel K K'`. -/

section CycLevel

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsSepClosure K K']

/-- **The cyclotomic level is cyclotomic.** -/
theorem isCyclotomicExtension_adjoin_of_isPrimitiveRoot (ℓ s : ℕ) [Fact ℓ.Prime] {ζ : K'}
    (hζ : IsPrimitiveRoot ζ (ℓ ^ s)) :
    IsCyclotomicExtension ({ℓ ^ s} : Set ℕ) K
      ↥(IntermediateField.adjoin K ({ζ} : Set K')) := by
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : Algebra.IsIntegral K K' := (IsSepClosure.separable.isAlgebraic).isIntegral
  haveI : NeZero (ℓ ^ s) := ⟨pow_ne_zero s (Fact.out (p := ℓ.Prime)).ne_zero⟩
  exact hζ.intermediateField_adjoin_isCyclotomicExtension K

/-- **The cyclotomic level `K(ζ_{ℓ^s})` as a finite normal number-field level of `K'` over `K`.** -/
noncomputable def cycLevel (ℓ s : ℕ) [Fact ℓ.Prime] (ζ : K')
    (hζ : IsPrimitiveRoot ζ (ℓ ^ s)) : FrobLevel K K' := by
  haveI := isCyclotomicExtension_adjoin_of_isPrimitiveRoot (K := K) (K' := K') ℓ s hζ
  refine ⟨IntermediateField.adjoin K ({ζ} : Set K'), ?_, ?_, ?_⟩
  · exact IsCyclotomicExtension.finiteDimensional ({ℓ ^ s} : Set ℕ) K _
  · exact (IsCyclotomicExtension.isGalois ({ℓ ^ s} : Set ℕ) K _).to_normal
  · exact IsCyclotomicExtension.numberField ({ℓ ^ s} : Set ℕ) K _

/-- **The ℓ-adic cyclotomic character bounds the Galois group of a cyclotomic level.**

`Gal(K⟮ζ⟯/K)` acts faithfully on the (cyclic) group of `ℓ^s`-th roots of unity, generated by `ζ`;
this is Mathlib's `IsPrimitiveRoot.autToPow`, whose injectivity on a cyclotomic extension is
`IsPrimitiveRoot.autToPow_injective`.  Hence the order of `Gal(K⟮ζ⟯/K)` divides `#(ℤ/ℓ^s)^× =
ℓ^{s-1}(ℓ-1)`. -/
theorem card_gal_adjoin_dvd_of_isPrimitiveRoot (ℓ s : ℕ) [Fact ℓ.Prime] (hs : 0 < s) {ζ : K'}
    (hζ : IsPrimitiveRoot ζ (ℓ ^ s)) :
    Nat.card Gal(↥(IntermediateField.adjoin K ({ζ} : Set K'))/K) ∣ ℓ ^ (s - 1) * (ℓ - 1) := by
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : Algebra.IsIntegral K K' := (IsSepClosure.separable.isAlgebraic).isIntegral
  haveI : NeZero (ℓ ^ s) := ⟨pow_ne_zero s (Fact.out (p := ℓ.Prime)).ne_zero⟩
  let L := IntermediateField.adjoin K ({ζ} : Set K')
  haveI hcyc : IsCyclotomicExtension ({ℓ ^ s} : Set ℕ) K ↥L := hζ.intermediateField_adjoin_isCyclotomicExtension K
  have hμ : IsPrimitiveRoot (IsCyclotomicExtension.zeta (ℓ ^ s) K ↥L) (ℓ ^ s) :=
    IsCyclotomicExtension.zeta_spec (ℓ ^ s) K ↥L
  have hinj : Function.Injective (IsPrimitiveRoot.autToPow K hμ) :=
    IsPrimitiveRoot.autToPow_injective K hμ
  have h1 : Nat.card Gal(↥L/K) ∣ Nat.card (ZMod (ℓ ^ s))ˣ :=
    Subgroup.card_dvd_of_injective _ hinj
  have hZ : Nat.card (ZMod (ℓ ^ s))ˣ = ℓ ^ (s - 1) * (ℓ - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow (Fact.out (p := ℓ.Prime)) hs]
  rwa [hZ] at h1

/-- **The degree of a cyclotomic level.**  `ℚ⟮ζ⟯ ⊆ K⟮ζ⟯`, so the tower law gives
`[K⟮ζ⟯ : ℚ] ≥ [ℚ⟮ζ⟯ : ℚ] = φ(ℓ^s) = ℓ^{s-1}(ℓ-1)`; Mathlib's
`IsPrimitiveRoot.lcm_totient_le_finrank` is precisely the second inequality. -/
theorem totient_le_finrank_adjoin_of_isPrimitiveRoot (ℓ s : ℕ) [Fact ℓ.Prime] (hs : 0 < s) {ζ : K'}
    (hζ : IsPrimitiveRoot ζ (ℓ ^ s)) :
    ℓ ^ (s - 1) * (ℓ - 1) ≤ Module.finrank ℚ ↥(IntermediateField.adjoin K ({ζ} : Set K')) := by
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : Algebra.IsIntegral K K' := (IsSepClosure.separable.isAlgebraic).isIntegral
  haveI : NeZero (ℓ ^ s) := ⟨pow_ne_zero s (Fact.out (p := ℓ.Prime)).ne_zero⟩
  let L := IntermediateField.adjoin K ({ζ} : Set K')
  haveI hcyc : IsCyclotomicExtension ({ℓ ^ s} : Set ℕ) K ↥L := hζ.intermediateField_adjoin_isCyclotomicExtension K
  haveI hfinK : FiniteDimensional K ↥L :=
    IsCyclotomicExtension.finiteDimensional ({ℓ ^ s} : Set ℕ) K ↥L
  haveI hfinQ : FiniteDimensional ℚ ↥L := Module.Finite.trans (R := ℚ) (A := K) (M := ↥L)
  have hμ : IsPrimitiveRoot (IsCyclotomicExtension.zeta (ℓ ^ s) K ↥L) (ℓ ^ s) :=
    IsCyclotomicExtension.zeta_spec (ℓ ^ s) K ↥L
  have h1 : IsPrimitiveRoot (1 : ↥L) 1 := IsPrimitiveRoot.one
  have hirr : Irreducible (cyclotomic (Nat.lcm (ℓ ^ s) 1) ℚ) := by
    rw [Nat.lcm_one_right]
    exact cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ s))
  have hkey := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) (L := ↥L) hμ h1 hirr
  rw [Nat.lcm_one_right, Nat.totient_prime_pow (Fact.out (p := ℓ.Prime)) hs] at hkey
  exact hkey

end CycLevel

/-! ## 4. The elementary arithmetic and group theory

Two elementary lemmas:

* `pow_dvd_of_dvd_mul_le`: if `ℓ` is prime, `m ∣ ℓ^{s-1}(ℓ-1)` and `m·d ≥ ℓ^{s-1}(ℓ-1)` with
  `d ≤ ℓ^d`, then `ℓ^{s-1-d} ∣ m` (the ℓ'-part of `m` is bounded by `ℓ-1`);
* `ellPart_card_ge_of_pow_dvd`: if `ℓ^n ∣ #A` for a finite abelian group `A`, then
  `ℓ^n ≤ #A_ℓ`. -/

/-- **The ℓ-power in `m` is large.**  If `ℓ` is prime, `m ∣ ℓ^{s-1}(ℓ-1)` and
`m·d ≥ ℓ^{s-1}(ℓ-1)` for some `d ≤ ℓ^d`, then `ℓ^{s-1-d}` divides `m`. -/
theorem pow_dvd_of_dvd_mul_le {ℓ m d s : ℕ} (hℓ : ℓ.Prime)
    (hdiv : m ∣ ℓ ^ (s - 1) * (ℓ - 1)) (hle : ℓ ^ (s - 1) * (ℓ - 1) ≤ m * d)
    (hd : d ≤ ℓ ^ d) : ℓ ^ (s - 1 - d) ∣ m := by
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [zero_dvd_iff] at hdiv
    have : 0 < ℓ ^ (s - 1) * (ℓ - 1) := Nat.mul_pos (pow_pos (by omega) _) (by omega)
    omega
  obtain ⟨v, hv1, hv2⟩ : ∃ v, ℓ ^ v ∣ m ∧ ¬ (ℓ ^ (v + 1) ∣ m) := by
    refine ⟨m.factorization ℓ, (hℓ.pow_dvd_iff_le_factorization hm0).mpr le_rfl, ?_⟩
    rw [hℓ.pow_dvd_iff_le_factorization hm0]
    omega
  set c := m / ℓ ^ v with hc
  have hmul : ℓ ^ v * c = m := Nat.mul_div_cancel' hv1
  have hcdvd_phi : c ∣ ℓ ^ (s - 1) * (ℓ - 1) :=
    (show c ∣ m from ⟨ℓ ^ v, by rw [mul_comm c (ℓ ^ v), hmul]⟩).trans hdiv
  have hcop_ell : Nat.Coprime c ℓ := by
    rw [Nat.coprime_comm]
    refine (hℓ.coprime_iff_not_dvd).mpr (fun hdvd => hv2 ?_)
    obtain ⟨x, hx⟩ := hdvd
    exact ⟨x, by calc m = ℓ ^ v * c := hmul.symm
                      _ = ℓ ^ v * (ℓ * x) := by rw [hx]
                      _ = ℓ ^ (v + 1) * x := by rw [pow_succ']; ring⟩
  have hc_dvd : c ∣ ℓ - 1 := (hcop_ell.pow_right (s - 1)).dvd_of_dvd_mul_left hcdvd_phi
  have hc_le : c ≤ ℓ - 1 := Nat.le_of_dvd (by omega) hc_dvd
  have h3 : ℓ ^ v * ((ℓ - 1) * ℓ ^ d) = ℓ ^ (v + d) * (ℓ - 1) := by
    rw [pow_add]; ring
  have h4 : ℓ ^ (s - 1) * (ℓ - 1) ≤ ℓ ^ (v + d) * (ℓ - 1) :=
    calc ℓ ^ (s - 1) * (ℓ - 1) ≤ m * d := hle
      _ = (ℓ ^ v * c) * d := by rw [hmul]
      _ = ℓ ^ v * (c * d) := by ring
      _ ≤ ℓ ^ v * ((ℓ - 1) * ℓ ^ d) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hc_le hd)
      _ = ℓ ^ (v + d) * (ℓ - 1) := h3
  have h5 : ℓ ^ (s - 1) ≤ ℓ ^ (v + d) := Nat.le_of_mul_le_mul_right h4 (by omega)
  have h6 : s - 1 ≤ v + d := (Nat.pow_le_pow_iff_right (by omega)).mp h5
  have h7 : s - 1 - d ≤ v := by omega
  exact (Nat.pow_dvd_pow ℓ h7).trans hv1

/-- **The ℓ-part of a finite abelian group is as large as its ℓ-power part.**  If `ℓ^n ∣ #A` then
`ℓ^n ≤ #A_ℓ`: the quotient `A ⧸ A_ℓ` has order coprime to `ℓ`
(`NK.Reconstruct.coprime_card_ellPart_quotient`), so all the ℓ-power in `#A` sits in `A_ℓ`. -/
theorem ellPart_card_ge_of_pow_dvd {A : Type*} [CommGroup A] [Finite A] (ℓ n : ℕ)
    (h : ℓ ^ n ∣ Nat.card A) : ℓ ^ n ≤ Nat.card ↥(ellPart A ℓ) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (ellPart A ℓ)] at h
  have hcop : Nat.Coprime (ℓ ^ n) (Nat.card (A ⧸ ellPart A ℓ)) :=
    (coprime_card_ellPart_quotient (A := A) ℓ).pow_left n
  exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_left h)

/-! ## 5. The arithmetic input: cyclotomic levels have arbitrarily large ℓ-parts -/

section Levels

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsSepClosure K K']

/-- **Levels of arbitrarily large ℓ-part exist.**  For every `n` the cyclotomic level
`K(ζ_{ℓ^s})`, `s = n + 1 + [K : ℚ]`, has `Γ_{L,ℓ}` of order at least `ℓ^n`.

Indeed `m = #Gal(K(ζ_{ℓ^s})/K) = [K(ζ_{ℓ^s}) : K]` satisfies `m ∣ ℓ^{s-1}(ℓ-1)` and
`m·[K:ℚ] ≥ ℓ^{s-1}(ℓ-1)`, so `ℓ^n ∣ m` (`pow_dvd_of_dvd_mul_le`); as `K(ζ_{ℓ^s})/K` is abelian,
`m = #Gal(K(ζ_{ℓ^s})/K)^{ab}` and the ℓ-part of the abelianisation has order at least `ℓ^n`
(`ellPart_card_ge_of_pow_dvd`). -/
theorem exists_level_card_ellPart_ge (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    ∃ L : FrobLevel K K', ℓ ^ n ≤ Nat.card ↥(LevelEllPart L.L ℓ) := by
  classical
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI hInt : Algebra.IsIntegral K K' := (IsSepClosure.separable.isAlgebraic).isIntegral
  set d := Module.finrank ℚ K with hd
  set s := n + 1 + d with hs
  have hs_pos : 0 < s := by omega
  haveI : IsAlgClosed K' := IsAlgClosure.isAlgClosed K
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_prime_pow K' ℓ s hs_pos
  haveI : NeZero (ℓ ^ s) := ⟨pow_ne_zero s (Fact.out (p := ℓ.Prime)).ne_zero⟩
  let L : IntermediateField K K' := IntermediateField.adjoin K ({ζ} : Set K')
  haveI hcyc : IsCyclotomicExtension ({ℓ ^ s} : Set ℕ) K ↥L :=
    hζ.intermediateField_adjoin_isCyclotomicExtension K
  haveI hgal : IsGalois K ↥L := IsCyclotomicExtension.isGalois ({ℓ ^ s} : Set ℕ) K ↥L
  haveI habel : IsAbelianGalois K ↥L :=
    IsCyclotomicExtension.isAbelianGalois ({ℓ ^ s} : Set ℕ) K ↥L
  haveI hfin : FiniteDimensional K ↥L :=
    IsCyclotomicExtension.finiteDimensional ({ℓ ^ s} : Set ℕ) K ↥L
  haveI hfinQ : FiniteDimensional ℚ ↥L := Module.Finite.trans (R := ℚ) (A := K) (M := ↥L)
  -- the order of the Galois group is the degree
  have hcard : Nat.card Gal(↥L/K) = Module.finrank K ↥L := IsGalois.card_aut_eq_finrank K ↥L
  -- it divides `φ(ℓ^s)`
  have hdiv : Nat.card Gal(↥L/K) ∣ ℓ ^ (s - 1) * (ℓ - 1) :=
    card_gal_adjoin_dvd_of_isPrimitiveRoot ℓ s hs_pos hζ
  -- and `[K(ζ) : ℚ]` is at least `φ(ℓ^s)`
  have hdeg : ℓ ^ (s - 1) * (ℓ - 1) ≤ Module.finrank ℚ ↥L :=
    totient_le_finrank_adjoin_of_isPrimitiveRoot ℓ s hs_pos hζ
  have htower : Module.finrank ℚ K * Module.finrank K ↥L = Module.finrank ℚ ↥L :=
    Module.finrank_mul_finrank ℚ K ↥L
  have hdle : d ≤ ℓ ^ d := by
    refine le_trans (le_of_lt (Nat.lt_two_pow_self (n := d)))
      (Nat.pow_le_pow_left (Fact.out (p := ℓ.Prime)).two_le d)
  have hdvdpow : ℓ ^ (s - 1 - d) ∣ Nat.card Gal(↥L/K) := by
    refine pow_dvd_of_dvd_mul_le (Fact.out (p := ℓ.Prime)) hdiv ?_ hdle
    have hmd : Nat.card Gal(↥L/K) * d = Module.finrank ℚ ↥L := by
      rw [hcard, hd, mul_comm (Module.finrank K ↥L) (Module.finrank ℚ K), htower]
    rw [hmd]
    exact hdeg
  have hsnd : s - 1 - d = n := by omega
  rw [hsnd] at hdvdpow
  -- the Galois group is abelian, so the abelianisation has the same cardinality
  have hab : Nat.card (Abelianization Gal(↥L/K)) = Nat.card Gal(↥L/K) := by
    letI : CommGroup Gal(↥L/K) :=
      { (inferInstance : Group Gal(↥L/K)) with
        mul_comm := IsMulCommutative.is_comm.comm }
    exact Nat.card_congr (Abelianization.equivOfComm (H := Gal(↥L/K))).symm.toEquiv
  have hdvdA : ℓ ^ n ∣ Nat.card (LevelAbelianization L) := by
    change ℓ ^ n ∣ Nat.card (Abelianization Gal(↥L/K))
    rw [hab]
    exact hdvdpow
  have hfinal : ℓ ^ n ≤ Nat.card ↥(LevelEllPart L ℓ) :=
    ellPart_card_ge_of_pow_dvd (A := LevelAbelianization L) ℓ n hdvdA
  exact ⟨⟨L, hfin, hgal.to_normal, IsCyclotomicExtension.numberField ({ℓ ^ s} : Set ℕ) K ↥L⟩,
    hfinal⟩

end Levels

/-! ## 6. The target -/

theorem infinite_gamma {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] :
    Infinite (Gamma K K' ℓ) :=
  infinite_of_unbounded_ellPart (K := K) (K' := K') ℓ
    (fun n => exists_level_card_ellPart_ge (K := K) (K' := K') ℓ n)

end NK.Reconstruct
