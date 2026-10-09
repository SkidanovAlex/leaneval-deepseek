import Mathlib
import Submission.NK.Chebotarev.LFunctions
import Submission.NK.HeckeL.Basic
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèlic Artin map from the ideal-theoretic reciprocity law

Definitions for the proof of `NK.CFTLib.fcElement_of_arl`.

* `artinSym`: the Artin symbol of a fractional ideal, `A ↦ ∏_𝔭 Frob_𝔭 ^ (count 𝔭 A)`.
* `CongrOneAt`, `PosAtInfinite`: the congruence and positivity conditions defining the
  congruence subgroup of a modulus.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- A commutative-monoid structure on `Gal(L/K)` from the commutativity hypothesis. -/
noncomputable def galCommMonoid (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    CommMonoid Gal(L/K) :=
  { (inferInstance : Monoid Gal(L/K)) with mul_comm := hcomm }

/-- The exponent vector of a fractional ideal of `K`: the multiplicities of the primes. -/
noncomputable def exps (A : FractionalIdeal (𝓞 K)⁰ K) : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.ofSupportFinite (fun 𝔭 => FractionalIdeal.count K 𝔭 A)
    (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors A))

@[simp] lemma exps_apply (A : FractionalIdeal (𝓞 K)⁰ K) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    exps A 𝔭 = FractionalIdeal.count K 𝔭 A :=
  congrFun (Finsupp.ofSupportFinite_coe) 𝔭

/-- **The Artin symbol of a fractional ideal**: the product of the Frobenius elements at the
primes occurring in the factorisation of `A`, with the multiplicities as exponents. -/
noncomputable def artinSym (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (A : FractionalIdeal (𝓞 K)⁰ K) : Gal(L/K) :=
  letI := galCommMonoid hcomm
  (exps A).prod (fun 𝔭 e => (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ e)

lemma exps_one : exps (1 : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  ext 𝔭
  rw [exps_apply, FractionalIdeal.count_one]
  rfl

lemma exps_mul {A B : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≠ 0) (hB : B ≠ 0) :
    exps (A * B) = exps A + exps B := by
  ext 𝔭
  rw [exps_apply, Finsupp.add_apply, exps_apply, exps_apply, FractionalIdeal.count_mul K 𝔭 hA hB]

lemma exps_pow (A : FractionalIdeal (𝓞 K)⁰ K) (n : ℕ) (hA : A ≠ 0) :
    exps (A ^ n) = n • exps A := by
  ext 𝔭
  rw [exps_apply, Finsupp.nsmul_apply, exps_apply, FractionalIdeal.count_pow]
  push_cast
  ring

lemma artinSym_one (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    artinSym hcomm (1 : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  letI := galCommMonoid hcomm
  unfold artinSym
  rw [exps_one]
  exact Finsupp.prod_zero_index

lemma artinSym_mul (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    {A B : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≠ 0) (hB : B ≠ 0) :
    artinSym hcomm (A * B) = artinSym hcomm A * artinSym hcomm B := by
  letI := galCommMonoid hcomm
  unfold artinSym
  rw [exps_mul hA hB]
  have hz : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ (0 : ℤ) = 1 :=
    fun 𝔭 => zpow_zero _
  have ha : ∀ (𝔭 : HeightOneSpectrum (𝓞 K)) (x y : ℤ),
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ (x + y)
        = (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ x
          * (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ y :=
    fun 𝔭 x y => zpow_add ..
  exact Finsupp.prod_add_index' hz ha

lemma artinSym_prime (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    artinSym hcomm (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 := by
  letI := galCommMonoid hcomm
  have h : exps (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) = Finsupp.single 𝔭 1 := by
    ext q
    rw [exps_apply]
    classical
    by_cases hq : q = 𝔭
    · subst hq; simp [FractionalIdeal.count_self]
    · rw [FractionalIdeal.count_maximal (K := K) (v := q) 𝔭, if_neg (Ne.symm hq)]
      simp [Finsupp.single_eq_of_ne hq]
  unfold artinSym
  have hz : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ (0 : ℤ) = 1 :=
    fun 𝔭 => zpow_zero _
  rw [h, Finsupp.prod_single_index (h := fun (𝔭 : HeightOneSpectrum (𝓞 K)) (e : ℤ) =>
    (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ e)
    (show (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ (0 : ℤ) = 1 from zpow_zero _),
    zpow_one]


/-! ## The congruence subgroup of a modulus -/

/-- `x` is positive at the real place `w`: its image under the identification `K_w ≅ ℝ` is a
positive real number. -/
def PosAtReal (w : InfinitePlace K) (x : (w.Completion)ˣ) : Prop :=
  ∀ (hw : w.IsReal), 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw) ((x : w.Completion))

/-- **The congruence subgroup of the modulus `m`**, as a `Prop`-valued predicate on subgroups of
`𝕀 K`: `U` is the group of idèles congruent to `1` modulo `m` at the finite places dividing `m`
and positive at every real place. -/
def IsCongruenceSubgroup (m : ℕ) (U : Subgroup (Idele K)) : Prop :=
  (∀ x : Idele K, x ∈ U ↔
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      Valued.v (((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1)
        ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)))
    ∧ (∀ w : InfinitePlace K, PosAtReal w (x (Place.ofInfinite w))))
  ∧ (∀ b : Kˣ, Idele.principalIdele K b ∈ U ↔
      ((∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
          Valued.v (algebraMap K (𝔭.adicCompletion K) (b : K) - 1)
            ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)))
        ∧ (∀ (w : InfinitePlace K) (hw : w.IsReal),
            0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              (algebraMap K w.Completion (b : K)))))

/-! ## The idèlic Artin map -/

/-- A chosen adjustment: for the idèle `x`, an element `b : Kˣ` with `x * (b) ∈ U`. -/
noncomputable def adjust (U : Subgroup (Idele K))
    (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U) (x : Idele K) : Kˣ :=
  Classical.choose (hadj x)

lemma adjust_spec (U : Subgroup (Idele K))
    (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U) (x : Idele K) :
    x * Idele.principalIdele K (adjust U hadj x) ∈ U :=
  Classical.choose_spec (hadj x)

/-- **The idèlic Artin map** attached to the reciprocity law `h` (through the modulus `m` and its
congruence subgroup `U`): the Artin symbol of the ideal of `x` after adjustment. -/
noncomputable def ideleArtin (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (U : Subgroup (Idele K))
    (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U) (x : Idele K) :
    Gal(L/K) :=
  artinSym hcomm (Idele.idealOf (x * Idele.principalIdele K (adjust U hadj x)))

end NK.CFTLib.Arl