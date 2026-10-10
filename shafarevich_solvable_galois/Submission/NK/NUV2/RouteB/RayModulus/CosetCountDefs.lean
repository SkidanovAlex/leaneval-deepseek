import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Submission.NK.NUV2.RouteB.CongClassSetup
import Submission.NK.NUV2.RouteB.RayModulus.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The counting vocabulary for the ray class count of a congruence subgroup

This file fixes the vocabulary used by the counting step of
`NK.NUV2.RouteB.rayClassCountRateUniform`:

* `cosetConeCountF K I x₀ X` — the number of points of the coset `x₀ + L(I)` of the lattice of a
  fractional ideal `I` in the mixed space which lie in the fundamental cone and have norm `≤ X`
  (the object controlled by `NK.NUV2.RouteB.latticeCosetCount_cone_isBigO`);
* `rayClassCnt K 𝔪 𝔡 X` — the number of ideals of `𝓞 K` which are nonzero, coprime to the support
  of the modulus `𝔪` and in the ray class of `𝔡` modulo the congruence subgroup `CongSubgroup K 𝔪`,
  of norm `≤ X`;
* `SharpSub K U S θ` — the assertion that the ray class counts of `U` for ideals coprime to `S`
  differ by `O(X ^ θ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

namespace NK.NUV2.RouteB

variable (K : Type) [Field K] [NumberField K]

/-- The number of points of the coset `x₀ + L` of the lattice `L` of the fractional ideal `I` in
the mixed space which lie in the fundamental cone and have norm `≤ X`. -/
noncomputable def cosetConeCountF
    (I : (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K)ˣ)
    (x₀ : mixedSpace K) (X : ℝ) : ℕ :=
  Nat.card {a : mixedSpace K // a - x₀ ∈ (idealLattice K I : Set (mixedSpace K)) ∧
    a ∈ fundamentalCone K ∧ mixedEmbedding.norm a ≤ X}

/-- The number of ideals of `𝓞 K` which are nonzero, coprime to the support of the modulus `𝔪`,
in the ray class of `𝔡` modulo the congruence subgroup `CongSubgroup K 𝔪`, of norm `≤ X`. -/
noncomputable def rayClassCnt (𝔪 : Modulus K) (𝔡 : Ideal (RingOfIntegers K)) (X : ℝ) : ℕ :=
  Nat.card {𝔞 : Ideal (RingOfIntegers K) //
    𝔞 ≠ 0 ∧ (∀ q : HeightOneSpectrum (RingOfIntegers K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ 𝔞) ∧
    NK.HeckeL.classOfIdeal K (CongSubgroup K 𝔪) 𝔞 =
      NK.HeckeL.classOfIdeal K (CongSubgroup K 𝔪) 𝔡 ∧
    (Ideal.absNorm 𝔞 : ℝ) ≤ X}

/-- **The power-saving ray class count for a subgroup `U` of the idèles and a finite set `S` of
primes**: the numbers of ideals of `𝓞 K` which are nonzero, coprime to `S` and of given class
modulo `𝕀 K ⧸ (Kˣ · U)`, of norm `≤ X`, differ by `O(X ^ θ)`. -/
def SharpSub (U : Subgroup (NK.GlobalCFT.Idele K))
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    ∀ c₁ c₂ : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
      |((Nat.card {𝔞 : Ideal (RingOfIntegers K) //
            𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
            NK.HeckeL.classOfIdeal K U 𝔞 = c₁ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ X} : ℝ)
        - (Nat.card {𝔞 : Ideal (RingOfIntegers K) //
            𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
            NK.HeckeL.classOfIdeal K U 𝔞 = c₂ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ X} : ℝ))|
      ≤ C * X ^ θ

variable {K}

/-- The integral ideal of a modulus is again nonzero, in the `NeZero` form. -/
instance instNeZeroModulusIdeal (𝔪 : Modulus K) : NeZero 𝔪.ideal := ⟨𝔪.ideal_ne_zero⟩

/-- The quotient of the units by the units congruent to `1` modulo the integral ideal of a modulus
is finite. -/
instance instFiniteQuotUnitCongOneIdeal (𝔪 : Modulus K) :
    Finite ((RingOfIntegers K)ˣ ⧸ unitCongOne 𝔪.ideal) :=
  haveI : (unitCongOne 𝔪.ideal).FiniteIndex := finiteIndex_unitCongOne 𝔪.ideal
  Subgroup.finite_quotient_of_finiteIndex (H := unitCongOne 𝔪.ideal)

/-- The quotient of the units by the units congruent to `1` modulo the integral ideal of a modulus
is finite. -/
noncomputable instance instFintypeQuotUnitCongOneIdeal (𝔪 : Modulus K) :
    Fintype ((RingOfIntegers K)ˣ ⧸ unitCongOne 𝔪.ideal) :=
  Fintype.ofFinite _

end NK.NUV2.RouteB
