/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.

For a cyclotomic extension `F/ℚ` of conductor `n` and an intermediate field `E`, the primes whose
Frobenius in `E` is a prescribed element `σ ∈ Gal(E/ℚ)` have Dirichlet density `1/[E:ℚ]`.  This is
Čebotarev for the abelian number field `E`.

The proof reduces to `NK.Chebotarev.CyclotomicFrobDensity` for `F` itself.  The restriction
`Gal(F/ℚ) → Gal(E/ℚ)`, `τ ↦ τ|_E`, is surjective with fibres in bijection with its kernel
`Gal(F/E)`, of order `[F:E]` (`fiberCard_restrictNormalHom`).  For all but finitely many primes
(the ramified ones) Frobenius elements are unique, so the preimage of `σ` is an `[F:E]`-element
coset of `Gal(F/ℚ)`, and the Frobenius set of `σ` in `E` is the union of the `[F:E]` disjoint
Frobenius sets of that coset in `F`.  Hence its density is
`[F:E] · (1/φ(n)) = [F:E]/[F:ℚ] = 1/[E:ℚ]`.
-/
import Mathlib
import Submission.NK.Chebotarev.CyclotomicFrobDensity
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.Chebotarev.HasDirichletDensityIUnionFinset
import Submission.NK.Chebotarev.HasDirichletDensitySensitivity
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Chebotarev

open IsDedekindDomain
open scoped NumberField

/-! ## Auxiliary lemmas

The three lemmas below are general field-theoretic / number-theoretic facts about a tower
`K ⊆ E ⊆ M`, collected here (in their own namespace, to avoid clashes with the rest of the
shared library) because that is where the main theorem needs them. -/

namespace CyclotomicIntermediateFieldDensityAux

/-- **The fibres of the restriction map `Gal(M/K) → Gal(E/K)` have cardinality `[M : E]`.**

Let `K ⊆ E ⊆ M` be a tower of fields with `M/K` finite Galois and `E/K` normal.  Then for every
`σ ∈ Gal(E/K)` the set of `τ ∈ Gal(M/K)` restricting to `σ` is a coset of the kernel
`Gal(M/E)` of the restriction, whence it has `[M:E]` elements. -/
theorem fiberCard_restrictNormalHom {K M : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] (E : IntermediateField K M) [Normal K E]
    (σ : Gal(↥E/K)) :
    Nat.card {τ : Gal(M/K) // AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E τ = σ} =
      Module.finrank ↥E M := by
  have hker : (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E).ker = E.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker E
  obtain ⟨τ₀, hτ₀⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) (E := M) σ
  have e : {τ : Gal(M/K) // AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E τ = σ} ≃
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E).ker :=
    { toFun := fun τ => ⟨τ₀⁻¹ * τ.1, by
        simp only [MonoidHom.mem_ker, map_mul, map_inv, τ.2, hτ₀, inv_mul_cancel]⟩
      invFun := fun k => ⟨τ₀ * k.1, by
        rw [map_mul, MonoidHom.mem_ker.mp k.2, mul_one, hτ₀]⟩
      left_inv := fun τ => by ext; simp
      right_inv := fun k => by ext; simp }
  rw [Nat.card_congr e, hker]
  exact IsGalois.card_fixingSubgroup_eq_finrank (F := K) (E := M) E

/-- **Restriction of a Frobenius at a prime of the base field.**  Let `K ⊆ E ⊆ M` be a tower of
number fields with `M/K` finite Galois and `E/K` normal.  If `τ ∈ Gal(M/K)` is an arithmetic
Frobenius at the prime `p` of `K` (i.e. at some prime of `𝓞 M` above `p`), then its restriction
`τ|_E ∈ Gal(E/K)` is an arithmetic Frobenius at `p`. -/
theorem isFrobAtPrime_restrictNormalHom {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (E : IntermediateField K M) [Normal K E] {p : PrimeIdeal K} {τ : Gal(M/K)}
    (h : IsFrobAtPrime (K := K) (L := M) p τ) :
    IsFrobAtPrime (K := K) (L := ↥E) p
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E τ) := by
  obtain ⟨P, hP, hPfrob⟩ := h
  refine ⟨P.under (NumberField.RingOfIntegers ↥E), ?_, ?_⟩
  · refine ⟨?_⟩
    rw [under_asIdeal, Ideal.under_under, ← hP.over]
  · exact IsFrobAtRestrictNormalHom E hP hPfrob

/-- **Only finitely many primes of the base field are ramified in an extension.**  For a finite
extension `L/K` of number fields, only finitely many primes `p` of `K` have a prime of `L` above
them at which the extension ramifies. -/
theorem finite_badPrimes {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    {p : PrimeIdeal K | ∃ P : PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal ∧
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}.Finite := by
  have h := Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := K) (L := L)
  refine Set.Finite.subset
    (h.image (fun q : PrimeIdeal L => q.under (NumberField.RingOfIntegers K))) ?_
  rintro p ⟨P, hP, hram⟩
  refine ⟨P, hram, ?_⟩
  ext : 1
  show Ideal.under (NumberField.RingOfIntegers K) P.asIdeal = p.asIdeal
  rw [← hP.over]

end CyclotomicIntermediateFieldDensityAux

/-! ## The main theorem -/

theorem CyclotomicIntermediateFieldDensity {n : ℕ} [NeZero n] {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (E : IntermediateField ℚ F) [Normal ℚ E] [FiniteDimensional ℚ E]
    (hcomm : ∀ a b : Gal(↥E/ℚ), a * b = b * a) (σ : Gal(↥E/ℚ)) :
    NumberField.Set.HasDirichletDensity
      {p : NK.Chebotarev.PrimeIdeal ℚ |
        NK.Chebotarev.IsFrobAtPrime (K := ℚ) (L := ↥E) p σ}
      (1 / (Module.finrank ℚ ↥E : ℝ)) := by
  classical
  haveI : IsGalois ℚ F := IsCyclotomicExtension.isGalois {n} ℚ F
  haveI : IsGalois ℚ ↥E := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- The intermediate-field API (`restrictNormalHom`, `IsFrobAtRestrictNormalHom`, …) is stated
  -- with the tower algebra structure `IntermediateField.algebra'` on `↥E`, while the statement's
  -- `[Normal ℚ E]` was elaborated with the canonical `ℚ`-algebra structure of a division ring.
  -- The two are definitionally equal; the instance below makes the tower structure available to
  -- typeclass search.
  haveI hNalg : @Normal ℚ ↥E _ _ (IntermediateField.algebra' (R' := ℚ) E) :=
    (inferInstance : Normal ℚ ↥E)
  -- The restriction `Gal(F/ℚ) →* Gal(E/ℚ)`.
  let φ : Gal(F/ℚ) →* Gal(↥E/ℚ) := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := F) E
  -- `Gal(F/ℚ)` is commutative, being isomorphic to `(ℤ/nℤ)ˣ`.
  have hcommF : ∀ a b : Gal(F/ℚ), a * b = b * a := by
    intro a b
    exact (IsCyclotomicExtension.Rat.galEquivZMod n F).injective (by
      rw [map_mul, map_mul, mul_comm])
  -- The exceptional set: the primes at which some prime above them ramifies, in `E` or in `F`.
  let Bad : Set (PrimeIdeal ℚ) :=
    {p | (∃ P : PrimeIdeal ↥E, P.asIdeal.LiesOver p.asIdeal ∧
            P.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 1) ∨
         (∃ P : PrimeIdeal F, P.asIdeal.LiesOver p.asIdeal ∧
            P.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 1)}
  have hBadfin : Bad.Finite := by
    have h1 : {p : PrimeIdeal ℚ | ∃ P : PrimeIdeal ↥E, P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 1}.Finite :=
      CyclotomicIntermediateFieldDensityAux.finite_badPrimes (K := ℚ) (L := ↥E)
    have h2 : {p : PrimeIdeal ℚ | ∃ P : PrimeIdeal F, P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 1}.Finite :=
      CyclotomicIntermediateFieldDensityAux.finite_badPrimes (K := ℚ) (L := F)
    exact h1.union h2
  let T : Gal(F/ℚ) → Set (PrimeIdeal ℚ) := fun τ => {p | IsFrobAtPrime (K := ℚ) (L := F) p τ}
  let S : Set (PrimeIdeal ℚ) := {p | IsFrobAtPrime (K := ℚ) (L := ↥E) p σ}
  -- **Descent.**  The Frobenius of `F` at `p` restricts to the Frobenius of `E` at `p`.
  have hC1 : ∀ p : PrimeIdeal ℚ, (∃ τ : Gal(F/ℚ), φ τ = σ ∧ p ∈ T τ) → p ∈ S := by
    rintro p ⟨τ, hτ, hp⟩
    have h : IsFrobAtPrime (K := ℚ) (L := ↥E) p (φ τ) :=
      CyclotomicIntermediateFieldDensityAux.isFrobAtPrime_restrictNormalHom (K := ℚ) (M := F) E hp
    rw [hτ] at h
    exact h
  -- **Lift.**  Away from `Bad`, the Frobenius of `E` at `p` lifts to a Frobenius of `F`.
  have hC2 : ∀ p : PrimeIdeal ℚ, p ∉ Bad → p ∈ S →
      ∃ τ : Gal(F/ℚ), φ τ = σ ∧ p ∈ T τ := by
    intro p hpBad hpS
    have hunrE : ∀ P : PrimeIdeal ↥E, P.asIdeal.LiesOver p.asIdeal →
        P.asIdeal.ramificationIdx (𝓞 ℚ) = 1 := by
      intro P hP
      by_contra h
      exact hpBad (Or.inl ⟨P, hP, h⟩)
    obtain ⟨ρ, -, huniq⟩ := ExistsUniqueIsFrobAtPrime (K := ℚ) (L := ↥E) hcomm p hunrE
    obtain ⟨τ, hτ⟩ := exists_isFrobAtPrime (K := ℚ) (L := F) p
    refine ⟨τ, ?_, hτ⟩
    have hφτ : IsFrobAtPrime (K := ℚ) (L := ↥E) p (φ τ) :=
      CyclotomicIntermediateFieldDensityAux.isFrobAtPrime_restrictNormalHom (K := ℚ) (M := F) E hτ
    exact (huniq (φ τ) hφτ).trans (huniq σ hpS).symm
  -- The Frobenius sets of `F` avoid the exceptional primes.
  have hTdens : ∀ τ : Gal(F/ℚ),
      NumberField.Set.HasDirichletDensity (T τ \ Bad) (1 / (n.totient : ℝ)) := by
    intro τ
    refine HasDirichletDensitySensitivity ?_ (CyclotomicFrobDensity (n := n) (F := F) τ)
    refine hBadfin.subset ?_
    rintro p (hp | hp)
    · by_contra hb
      exact hp.2 ⟨hp.1, hb⟩
    · exact (hp.2 hp.1.1).elim
  -- Away from `Bad` the Frobenius of `F` at `p` is unique, so the sets `T τ \ Bad` are disjoint.
  have hdisj : (((Finset.univ : Finset {τ : Gal(F/ℚ) // φ τ = σ}) :
        Set {τ : Gal(F/ℚ) // φ τ = σ})).Pairwise
      fun i j => Disjoint (T ↑i \ Bad) (T ↑j \ Bad) := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr fun p hpi hpj => ?_
    have hunrF : ∀ P : PrimeIdeal F, P.asIdeal.LiesOver p.asIdeal →
        P.asIdeal.ramificationIdx (𝓞 ℚ) = 1 := by
      intro P hP
      by_contra h
      exact hpi.2 (Or.inr ⟨P, hP, h⟩)
    obtain ⟨ρ, -, huniq⟩ := ExistsUniqueIsFrobAtPrime (K := ℚ) (L := F) hcommF p hunrF
    exact hij (Subtype.ext ((huniq ↑i hpi.1).trans (huniq ↑j hpj.1).symm))
  -- The union of the finitely many disjoint Frobenius sets of the preimage of `σ`.
  have hunion : NumberField.Set.HasDirichletDensity
      (⋃ i : {τ : Gal(F/ℚ) // φ τ = σ}, (T ↑i \ Bad))
      ((Nat.card {τ : Gal(F/ℚ) // φ τ = σ} : ℝ) * (1 / (n.totient : ℝ))) := by
    have hd := HasDirichletDensityIUnionFinset (K := ℚ)
      (s := (Finset.univ : Finset {τ : Gal(F/ℚ) // φ τ = σ}))
      (f := fun i => T ↑i \ Bad) (δ := fun _ => 1 / (n.totient : ℝ))
      (fun i _ => hTdens ↑i) hdisj
    have hset : (⋃ i ∈ (Finset.univ : Finset {τ : Gal(F/ℚ) // φ τ = σ}), (T ↑i \ Bad))
        = ⋃ i : {τ : Gal(F/ℚ) // φ τ = σ}, (T ↑i \ Bad) := by
      ext p; simp
    have hsum : (∑ i ∈ (Finset.univ : Finset {τ : Gal(F/ℚ) // φ τ = σ}),
          (1 / (n.totient : ℝ)))
        = (Nat.card {τ : Gal(F/ℚ) // φ τ = σ} : ℝ) * (1 / (n.totient : ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card, nsmul_eq_mul]
    rw [hset, hsum] at hd
    exact hd
  -- The Frobenius set of `σ` in `E` agrees with that union away from the exceptional primes.
  have hSeq : S \ Bad = ⋃ i : {τ : Gal(F/ℚ) // φ τ = σ}, (T ↑i \ Bad) := by
    ext p
    constructor
    · intro hp
      obtain ⟨τ, hτ, hpT⟩ := hC2 p hp.2 hp.1
      exact Set.mem_iUnion.mpr ⟨⟨τ, hτ⟩, hpT, hp.2⟩
    · intro hp
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
      exact ⟨hC1 p ⟨↑i, i.2, hi.1⟩, hi.2⟩
  have hdens : NumberField.Set.HasDirichletDensity S
      ((Nat.card {τ : Gal(F/ℚ) // φ τ = σ} : ℝ) * (1 / (n.totient : ℝ))) := by
    have h1 : NumberField.Set.HasDirichletDensity (S \ Bad)
        ((Nat.card {τ : Gal(F/ℚ) // φ τ = σ} : ℝ) * (1 / (n.totient : ℝ))) := by
      rw [hSeq]; exact hunion
    refine HasDirichletDensitySensitivity ?_ h1
    refine hBadfin.subset ?_
    intro p hp
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
    · exact absurd hp1.1 hp2
    · by_contra hb
      exact hp2 ⟨hp1, hb⟩
  -- The numerical identity `[F:E] · (1/φ(n)) = 1/[E:ℚ]`.
  have hval : (Nat.card {τ : Gal(F/ℚ) // φ τ = σ} : ℝ) * (1 / (n.totient : ℝ)) =
      1 / (Module.finrank ℚ ↥E : ℝ) := by
    have hcard : Nat.card {τ : Gal(F/ℚ) // φ τ = σ} = Module.finrank ↥E F :=
      CyclotomicIntermediateFieldDensityAux.fiberCard_restrictNormalHom (K := ℚ) (M := F) E σ
    rw [hcard]
    have htot : (n.totient : ℝ) = (Module.finrank ℚ F : ℝ) := by
      rw [IsCyclotomicExtension.Rat.finrank n F]
    have htower : (Module.finrank ℚ F : ℕ) = Module.finrank ↥E F * Module.finrank ℚ ↥E := by
      rw [← Module.finrank_mul_finrank ℚ ↥E F, mul_comm]
    have ha : (Module.finrank ↥E F : ℝ) ≠ 0 := by
      have h : 0 < Module.finrank ↥E F := Module.finrank_pos
      exact_mod_cast h.ne'
    have hb : (Module.finrank ℚ ↥E : ℝ) ≠ 0 := by
      have h : 0 < Module.finrank ℚ ↥E := Module.finrank_pos
      exact_mod_cast h.ne'
    rw [htot, htower, Nat.cast_mul]
    field_simp
  rw [hval] at hdens
  exact hdens

end NK.Chebotarev
