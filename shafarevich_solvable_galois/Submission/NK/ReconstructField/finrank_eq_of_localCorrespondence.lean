import Mathlib
import Submission.NK.ReconstructField.Basic
import Submission.NK.LocalInputs.Degree.finrank_eq_of_localDegree_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree of the fields of a local correspondence

Given a local correspondence `a` of `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)`
(`NK.Reconstruct.LocalCorrespondence`, CoNF (12.1.9)), the two number fields `K₁` and `K₂` have
the same degree over `ℚ`.

The proof is the bookkeeping step which turns the *local* input — preservation of the local degree
`[K_𝔭 : ℚ_p]` (`a.localDegree`) and of the residue characteristic (`a.residueChar`) — into the
equality of the global degrees, by summing the local degrees over the primes above a fixed rational
prime.

## The route

* `charP_quotient_iff_mem`, `charP_of_liesOver`, `liesOver_of_charP` — the residue characteristic
  of a finite prime `q` of `K` is the rational prime `p` with `q ∩ ℤ = (p)`: the characteristic of
  `𝓞 K ⧸ q` is `p` exactly when `q` lies over `(p)`.
* `charP_primeMap` — `a.residueChar` (transported from places to primes along `primeMap_spec`)
  says that `a.primeMap` preserves the residue characteristic.
* `primeMap_mem_primesOver` / `primeMap_symm_mem_primesOver` — consequently `a.primeMap` restricts
  to a bijection of the primes above a fixed rational prime `P`: the forward direction is the
  preservation of the characteristic just proved, the reverse direction is the same argument for
  the rational prime `q ∩ ℤ` of `a.primeMap⁻¹ q'`, which by the forward direction must agree with
  `P`.
* `localDegree_primeMap` — for corresponding primes the local degrees agree, which is
  `a.localDegree` rewritten by `localDegree_eq_ramificationIdx_mul_inertiaDeg`.
* `primeEquivOver` assembles the bijection of primes over `P`, and
  `NK.LocalInputs.finrank_eq_of_localDegree_eq` turns the pointwise equality of local degrees
  into `[K₁ : ℚ] = [K₂ : ℚ]` by reindexing the sum of
  `NK.LocalInputs.Degree.sum_localDegree_eq_finrank`.
-/

open IsDedekindDomain

namespace NK.ReconstructField

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

section ResidueCharacteristic

/-- **The residue characteristic of a finite prime is membership of the prime in the ideal.**  For
a number field `K`, a finite prime `q` of `K` and a prime number `p`, the residue field
`𝓞 K ⧸ q` has characteristic `p` exactly when `(p : 𝓞 K) ∈ q`. -/
theorem charP_quotient_iff_mem {K : Type*} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime) :
    CharP (NumberField.RingOfIntegers K ⧸ q.asIdeal) p ↔
      (p : NumberField.RingOfIntegers K) ∈ q.asIdeal := by
  have hprime : q.asIdeal.IsPrime := q.isPrime
  rw [CharP.charP_iff_prime_eq_zero hp]
  constructor
  · intro h
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h)
  · intro h
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr h :
      Ideal.Quotient.mk q.asIdeal (p : NumberField.RingOfIntegers K) = 0)

/-- **A prime lying over `P` has residue characteristic the rational prime of `P`.** -/
theorem charP_of_liesOver {K : Type*} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : q.asIdeal.LiesOver P.asIdeal) :
    CharP (NumberField.RingOfIntegers K ⧸ q.asIdeal) (Rat.HeightOneSpectrum.primesEquiv P).1 := by
  have hprime : q.asIdeal.IsPrime := q.isPrime
  rw [CharP.charP_iff_prime_eq_zero (Rat.HeightOneSpectrum.primesEquiv P).2]
  have hmem : ((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers ℚ) ∈ P.asIdeal :=
    Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq P _ _ (Subtype.ext rfl)
  have hmem' : ((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers K) ∈
      q.asIdeal := by
    rw [← map_natCast (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)) _]
    show algebraMap _ _
      ((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers ℚ) ∈ q.asIdeal
    rw [← Ideal.mem_under, ← h.over]
    exact hmem
  simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem' :
    Ideal.Quotient.mk q.asIdeal
      ((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers K) = 0)

/-- **A prime whose residue field has characteristic the rational prime of `P` lies over `P`**:
the converse of `charP_of_liesOver`. -/
theorem liesOver_of_charP {K : Type*} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : CharP (NumberField.RingOfIntegers K ⧸ q.asIdeal)
      (Rat.HeightOneSpectrum.primesEquiv P).1) :
    q.asIdeal.LiesOver P.asIdeal := by
  have hp : (Rat.HeightOneSpectrum.primesEquiv P).1.Prime :=
    (Rat.HeightOneSpectrum.primesEquiv P).2
  have hmem : ((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers K) ∈
      q.asIdeal :=
    (charP_quotient_iff_mem (K := K) q hp).mp h
  have hmemQ : ((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers ℚ) ∈
      q.asIdeal.under (NumberField.RingOfIntegers ℚ) := by
    rw [Ideal.mem_under]
    simpa using hmem
  have hPmem : ((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers ℚ) ∈
      P.asIdeal :=
    Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq P _ hp (Subtype.ext rfl)
  have hPspan : P.asIdeal =
      Ideal.span {((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers ℚ)} :=
    Commons.NumberTheory.NumberField.Completion.asIdeal_eq_span_prime P _ hp hPmem
  have hle : Ideal.span {((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers ℚ)} ≤
      q.asIdeal.under (NumberField.RingOfIntegers ℚ) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmemQ)
  have hprimeUnder : (q.asIdeal.under (NumberField.RingOfIntegers ℚ)).IsPrime :=
    Ideal.IsPrime.under (A := NumberField.RingOfIntegers ℚ) q.asIdeal
  have hmax : (Ideal.span
      {((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers ℚ)}).IsMaximal := by
    rw [← hPspan]; exact P.isPrime.isMaximal P.ne_bot
  refine Ideal.LiesOver.mk ?_
  rw [hPspan, Ideal.IsMaximal.eq_of_le hmax ?_ hle]
  exact fun hh => hprimeUnder.ne_top hh

end ResidueCharacteristic

section LocalCorrespondence

variable {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}

/-- The prime below the place `placeOver p` is `p`. -/
theorem primeOf_placeOver
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)) :
    Submission.NeukirchUchida.primeOf
      (Submission.NeukirchUchida.placeOver (K₁ := K₁) (K₁' := K₁') p).1
      (Submission.NeukirchUchida.placeOver (K₁ := K₁) (K₁' := K₁') p).2 = p := by
  apply (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K₁))
  rw [← Submission.NeukirchUchida.primeOf_spec, Submission.NeukirchUchida.placeOver_spec]

/-- **The local correspondence preserves the residue characteristic of finite primes.**  This is
`a.residueChar`, which is stated for places, transported to primes along `primeMap_spec`. -/
theorem charP_primeMap (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)) (ℓ : ℕ)
    (h : CharP (NumberField.RingOfIntegers K₁ ⧸ q.asIdeal) ℓ) :
    CharP (NumberField.RingOfIntegers K₂ ⧸ (a.primeMap q).asIdeal) ℓ := by
  let A := Submission.NeukirchUchida.placeOver (K₁ := K₁) (K₁' := K₁') q
  have hqA : Submission.NeukirchUchida.primeOf A.1 A.2 = q := primeOf_placeOver q
  have h1 : CharP (NumberField.RingOfIntegers K₁ ⧸
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ := by rw [hqA]; exact h
  have h2 := a.residueChar A ℓ h1
  have h3 : a.primeMap (Submission.NeukirchUchida.primeOf A.1 A.2) =
      Submission.NeukirchUchida.primeOf (a.placeMap A).1 (a.placeMap A).2 := a.primeMap_spec A
  rw [hqA] at h3
  rw [← h3] at h2
  exact h2

/-- **The local correspondence preserves the primes above a rational prime.** -/
theorem primeMap_mem_primesOver (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (hq : q.asIdeal ∈ P.asIdeal.primesOver (NumberField.RingOfIntegers K₁)) :
    (a.primeMap q).asIdeal ∈ P.asIdeal.primesOver (NumberField.RingOfIntegers K₂) := by
  refine ⟨(a.primeMap q).isPrime, ?_⟩
  exact liesOver_of_charP _ P (charP_primeMap a q _ (charP_of_liesOver q P hq.2))

/-- **The inverse of the local correspondence preserves the primes above a rational prime.**  If
`q'` lies over `P`, so does its preimage: writing `q` for that preimage and `P₁ = q ∩ ℤ` for the
rational prime below it, the forward direction shows that `q' = a.primeMap q` lies over `P₁`; but
`q'` also lies over `P`, so `P₁ = P` since a prime has a unique prime below it. -/
theorem primeMap_symm_mem_primesOver (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (hq' : q'.asIdeal ∈ P.asIdeal.primesOver (NumberField.RingOfIntegers K₂)) :
    (a.primeMap.symm q').asIdeal ∈ P.asIdeal.primesOver (NumberField.RingOfIntegers K₁) := by
  set q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁) :=
    a.primeMap.symm q' with hq
  have hb : (a.primeMap q).asIdeal ∈
      (NK.LocalInputs.primeBelow K₁ q).asIdeal.primesOver (NumberField.RingOfIntegers K₂) :=
    primeMap_mem_primesOver a (NK.LocalInputs.primeBelow K₁ q) q
      ⟨q.isPrime, NK.LocalInputs.primeBelow_liesOver K₁ q⟩
  have hq'eq : a.primeMap q = q' := by rw [hq]; exact a.primeMap.apply_symm_apply q'
  rw [hq'eq] at hb
  have h1 : q'.asIdeal.LiesOver (NK.LocalInputs.primeBelow K₁ q).asIdeal := hb.2
  have h2 : q'.asIdeal.LiesOver P.asIdeal := hq'.2
  have heq : (NK.LocalInputs.primeBelow K₁ q).asIdeal = P.asIdeal := by
    rw [h1.over, h2.over]
  have hPq : P = NK.LocalInputs.primeBelow K₁ q :=
    IsDedekindDomain.HeightOneSpectrum.ext heq.symm
  rw [hPq]
  exact ⟨q.isPrime, NK.LocalInputs.primeBelow_liesOver K₁ q⟩

/-- **The local correspondence restricts to a bijection of the primes above a rational prime.** -/
noncomputable def primeEquivOver (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    P.asIdeal.primesOver (NumberField.RingOfIntegers K₁) ≃
      P.asIdeal.primesOver (NumberField.RingOfIntegers K₂) where
  toFun qq := ⟨(a.primeMap (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ P qq)).asIdeal,
    primeMap_mem_primesOver a P _ qq.2⟩
  invFun qq :=
    ⟨(a.primeMap.symm (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ P qq)).asIdeal,
      primeMap_symm_mem_primesOver a P _ qq.2⟩
  left_inv qq := by
    apply Subtype.ext
    simp only [Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ]
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal (Equiv.symm_apply_apply a.primeMap _)
  right_inv qq := by
    apply Subtype.ext
    simp only [Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ]
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal (Equiv.apply_symm_apply a.primeMap _)

/-- **Corresponding primes have the same local degree.**  This is `a.localDegree` rewritten by
`localDegree = ramificationIdx * inertiaDeg` over `ℤ`. -/
theorem localDegree_primeMap (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)) :
    NK.LocalInputs.localDegree K₁ q = NK.LocalInputs.localDegree K₂ (a.primeMap q) := by
  rw [NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg (K := K₁) q,
    NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg (K := K₂) (a.primeMap q)]
  have hA := a.localDegree (Submission.NeukirchUchida.placeOver (K₁ := K₁) (K₁' := K₁') q)
  have hqA : Submission.NeukirchUchida.primeOf
      (Submission.NeukirchUchida.placeOver (K₁ := K₁) (K₁' := K₁') q).1
      (Submission.NeukirchUchida.placeOver (K₁ := K₁) (K₁' := K₁') q).2 = q := primeOf_placeOver q
  rw [hqA] at hA
  have h2 : Submission.NeukirchUchida.primeOf
      (a.placeMap (Submission.NeukirchUchida.placeOver (K₁ := K₁) (K₁' := K₁') q)).1
      (a.placeMap (Submission.NeukirchUchida.placeOver (K₁ := K₁) (K₁' := K₁') q)).2 =
      a.primeMap q := by
    rw [← a.primeMap_spec (Submission.NeukirchUchida.placeOver (K₁ := K₁) (K₁' := K₁') q), hqA]
  rw [h2] at hA
  calc q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ
      = q.asIdeal.inertiaDeg ℤ * q.asIdeal.ramificationIdx ℤ := mul_comm _ _
    _ = (a.primeMap q).asIdeal.inertiaDeg ℤ * (a.primeMap q).asIdeal.ramificationIdx ℤ := hA
    _ = (a.primeMap q).asIdeal.ramificationIdx ℤ * (a.primeMap q).asIdeal.inertiaDeg ℤ :=
        mul_comm _ _

/-- **Corresponding number fields have the same degree.**  For a local correspondence `a` of
`ϕ` (CoNF (12.1.9), as packaged in `NK.Reconstruct.LocalCorrespondence`), the number fields `K₁`
and `K₂` have the same degree over `ℚ`.

Proof route: `a.residueChar` shows that `a.primeMap` preserves the rational prime below a prime
(the characteristic of the residue field `𝓞 K ⧸ 𝔭` is the prime `p` with `(p) ⊆ 𝔭`, so
`CharP`-preservation forces `p | a.primeMap 𝔭` when `p | 𝔭`; here `primeOf` is surjective, so
`primeMap` is pinned down by `primeMap_spec` on every prime); hence `a.primeMap` restricts to a
bijection of the primes above each rational prime `P`, and by `a.localDegree` this bijection
matches `inertiaDeg ℤ * ramificationIdx ℤ = localDegree K 𝔭`
(`NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg`).  The sum of the local
degrees over the primes above `P` is `[K : ℚ]`
(`NK.LocalInputs.Degree.sum_localDegree_eq_finrank`), so the two degrees agree — the final
reindexing step is `NK.LocalInputs.Degree.finrank_eq_of_localDegree_eq`. -/
theorem finrank_eq_of_localCorrespondence
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) :
    Module.finrank ℚ K₁ = Module.finrank ℚ K₂ := by
  -- any rational prime will do
  let P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  refine NK.LocalInputs.finrank_eq_of_localDegree_eq P (primeEquivOver a P) ?_
  intro qq
  have h1 : NK.LocalInputs.localDegree K₁
      (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ P qq) =
      NK.LocalInputs.localDegree K₂
        (a.primeMap (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ P qq)) :=
    localDegree_primeMap a _
  have h2 : Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ P (primeEquivOver a P qq) =
      a.primeMap (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ P qq) := rfl
  rw [h2]
  exact h1

end LocalCorrespondence

end NK.ReconstructField
