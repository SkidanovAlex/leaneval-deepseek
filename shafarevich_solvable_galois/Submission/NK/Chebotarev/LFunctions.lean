/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Frobenius elements as a function of the prime, and the Hecke `L`-function input

For an abelian extension `L/K`, the Frobenius element at a prime `p` of `K` is well defined as
soon as `p` is unramified.  This file introduces

* `NK.Chebotarev.frobAtPrime` — an arbitrary but fixed choice of a Frobenius element at `p`
  (the chosen one is correct whenever `p` is unramified and `L/K` is abelian);
* `NK.Chebotarev.charPrimeSum` — the prime sum `∑_𝔭 χ(Frob_𝔭) N𝔭^{-s}` twisted by a character
  `χ` of the Galois group, i.e. the Euler product expansion of the Hecke `L`-function of `χ`;
* `NK.Chebotarev.AbelianLFunctions` — the analytic input of Čebotarev in the abelian case: for
  every non-trivial character the twisted prime sum is bounded as `s → 1⁺`.  This is exactly what
  the holomorphy and non-vanishing at `s = 1` of the Hecke `L`-function of a non-trivial character
  of a ray class group gives, after taking logarithms.
-/

set_option linter.unusedSectionVars false

namespace NK.Chebotarev

open Filter IsDedekindDomain Asymptotics
open scoped BigOperators Classical

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **A chosen Frobenius element at a prime `p` of `K`**, namely the unique `σ` with
`IsFrobAtPrime p σ` if such exists, and `1` otherwise. -/
noncomputable def frobAtPrime (p : PrimeIdeal K) : Gal(L/K) :=
  if h : ∃ σ : Gal(L/K), IsFrobAtPrime p σ then h.choose else 1

/-- For an unramified prime of an abelian extension, the chosen element `frobAtPrime p` really is
a Frobenius at `p`. -/
theorem isFrobAtPrime_frobAtPrime (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (p : PrimeIdeal K)
    (hunr : ∀ P : PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    IsFrobAtPrime p (frobAtPrime (K := K) (L := L) p) := by
  classical
  by_cases h : ∃ σ : Gal(L/K), IsFrobAtPrime p σ
  · rw [frobAtPrime, dif_pos h]
    obtain ⟨σ, hσ, huniq⟩ := ExistsUniqueIsFrobAtPrime hcomm p hunr
    rw [huniq h.choose h.choose_spec]
    exact hσ
  · rw [frobAtPrime, dif_neg h]
    exact absurd (exists_isFrobAtPrime (K := K) (L := L) p) h

/-- At an unramified prime of an abelian extension, `IsFrobAtPrime p σ` is equivalent to
`frobAtPrime p = σ`. -/
theorem isFrobAtPrime_iff_frobAtPrime_eq (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (p : PrimeIdeal K)
    (hunr : ∀ P : PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (σ : Gal(L/K)) :
    IsFrobAtPrime p σ ↔ frobAtPrime (K := K) (L := L) p = σ := by
  constructor
  · intro hσ
    exact ((ExistsUniqueIsFrobAtPrime hcomm p hunr).unique hσ
      (isFrobAtPrime_frobAtPrime hcomm p hunr)).symm
  · intro hσ
    rw [← hσ]
    exact isFrobAtPrime_frobAtPrime hcomm p hunr

/-- **The character-twisted prime sum** `∑_𝔭 χ(Frob_𝔭) N𝔭^{-s}`: the Euler product expansion of
the Hecke `L`-function of the character `χ`. -/
noncomputable def charPrimeSum (χ : Gal(L/K) →* ℂ) (s : ℝ) : ℂ :=
  ∑' p : PrimeIdeal K, χ (frobAtPrime (K := K) (L := L) p) *
    (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)

/-- **The Hecke `L`-function input of Čebotarev's density theorem in the abelian case.**  For every
non-trivial character `χ` of `Gal(L/K)` the twisted prime sum stays bounded as `s → 1⁺`.

This is the Euler-product form of "the Hecke `L`-function of a non-trivial character of a ray
class group is holomorphic and non-zero at `s = 1`": taking logarithms of the Euler product,
`log L(χ,s) = ∑_𝔭 ∑_{k ≥ 1} χ(𝔭^k)N𝔭^{-ks}/k`, and `log L(χ,1) ≠ ±∞` confines the `k = 1` term,
which is the sum below (the terms with `k ≥ 2` are bounded). -/
def AbelianLFunctions (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Prop :=
  ∀ χ : Gal(L/K) →* ℂ, χ ≠ 1 →
    (fun s : ℝ => charPrimeSum (K := K) (L := L) χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ))

end NK.Chebotarev
