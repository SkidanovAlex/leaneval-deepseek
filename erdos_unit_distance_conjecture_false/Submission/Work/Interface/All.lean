import Submission.Work.Defs.Basic
import Submission.Work.Arithmetic.Splitting
import Submission.Work.Lattice.Separation
import Submission.Work.Numeric.Inequalities
import Submission.Work.Prime.Combine
import Submission.Work.Arithmetic.Pigeonhole
import Submission.Work.Geometry.Core
import Submission.Work.ClassNumber.Bound
import Submission.Work.CFT.Target
import Submission.Work.Tower.MinkowskiGS.All

/-!
# The interface lemmas of the unit-distance construction

Statements of the main inputs for the proof that Erdős's unit-distance conjecture is false.
Each of these is proved in its own file under `Submission/Work/`; the wiring happens here.
-/

open MeasureTheory
open NumberField
open scoped Classical nonZeroDivisors
open Work.Defs

namespace Work
namespace Interface

/-- **Geometric core of the construction** (paper §2, Lemmas 2.4, 2.5, 2.6).

Let `K` be a CM number field, `I` a fractional ideal of `K` (the lattice `Q⁻²𝒪_K` of the
construction), and `U` a finite set of elements of `I` with `u · c(u) = 1`, where `c` is complex
conjugation. Assume the lattice `I` is separated at scale `1/D`, i.e. every nonzero element has
some infinite-place norm `≥ 1/D`. Then there is a nonempty finite planar point set `P` with
`|P| ≤ (4RD)^[K:ℚ]` and `ν(P) ≥ 2⁻¹ |U| (1 - 1/(2R))^[K:ℚ] |P|`. -/
theorem geometric_core (K : Type) [Field K] [NumberField K] [IsCMField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R D : ℝ) (hR : 1/2 < R) (hD : 0 < D) (hRD : 1 ≤ R * D)
    (U : Finset K) (hU : ∀ u ∈ U, u ∈ (I : Set K))
    (hU1 : ∀ u ∈ U, u * IsCMField.complexConj K u = 1)
    (hsep : ∀ β ∈ (I : Set K), β ≠ 0 →
      ∃ w : InfinitePlace K, 1/D ≤ mixedEmbedding.normAtPlace w (mixedEmbedding K β))
    (w₀ : InfinitePlace K) :
    ∃ P : Finset ℂ, 0 < P.card ∧ (P.card : ℝ) ≤ (4 * R * D) ^ (Module.finrank ℚ K) ∧
      2⁻¹ * (U.card : ℝ) * (1 - 1/(2*R)) ^ (Module.finrank ℚ K) * (P.card : ℝ)
        ≤ (cDist P : ℝ) :=
  Work.Geometry.geometric_core_card_pos K I R D hR hD hRD U hU hU1 hsep w₀

/-- **Class-group pigeonhole** (paper Proposition 2.2).

Let `K` be a CM field, `𝔓₀, …, 𝔓_{m-1}` distinct prime ideals of `𝒪_K` which are pairwise
non-conjugate under complex conjugation, each lying above a rational prime dividing `Q`.
Then there are at least `2^m / h(K)` elements `u ∈ K` with `u · c(u) = 1` whose denominators
are bounded by `Q²`, and which are distinct. -/
theorem exists_unitary_elements (K : Type) [Field K] [NumberField K] [IsCMField K]
    (m : ℕ) (P : Fin m → Ideal (𝓞 K)) (hP : ∀ i, (P i).IsPrime)
    (hPne : ∀ i j, i ≠ j → P i ≠ P j)
    (hconj : ∀ i j, Ideal.map (IsCMField.ringOfIntegersComplexConj K).toRingHom (P i) ≠ P j)
    (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : ∀ i, ∃ p : ℕ, p ∣ Q ∧ Nat.Prime p ∧ Ideal.span {(p : 𝓞 K)} ≤ P i) :
    ∃ U : Finset K, (∀ u ∈ U, u * IsCMField.complexConj K u = 1) ∧
      (∀ u ∈ U, ∃ w : 𝓞 K, (w : K) = (Q : K) ^ 2 * u) ∧
      U.card * NumberField.classNumber K ≥ 2 ^ m :=
  Work.Arithmetic.Pigeonhole K m P hP hPne hconj Q hQ0 hQ

/-- **Splitting produces conjugate prime pairs**: a rational prime `q ≡ 1 (mod 4)` which splits
completely in a CM field `K` has `[K⁺ : ℚ]` pairwise distinct primes above it in `𝒪_K`, none of
which is conjugate to any of them. -/
theorem exists_conj_prime_pairs (K : Type) [Field K] [NumberField K] [IsCMField K]
    (q : ℕ) (hq : Nat.Prime q) (hq4 : q % 4 = 1)
    (hsplit : SplitsCompletely q K) :
    ∃ P : Fin (Module.finrank ℚ (maximalRealSubfield K)) → Ideal (𝓞 K),
      (∀ i, (P i).IsPrime) ∧ (∀ i, (q : 𝓞 K) ∈ P i) ∧
      (∀ i j, i ≠ j → P i ≠ P j) ∧
      (∀ i j, Ideal.map (IsCMField.ringOfIntegersComplexConj K).toRingHom (P i) ≠ P j) :=
  Work.Arithmetic.Splitting K q hq hq4 hsplit

/-- **Prime families**: a finite injective family of primes `q ≡ 1 mod 4` which all split
completely in a CM field `K` produces `t · [K⁺:ℚ]` prime ideals of `𝒪_K` which are pairwise
distinct and pairwise non-conjugate. -/
theorem exists_prime_family (K : Type) [Field K] [NumberField K] [IsCMField K]
    (t : ℕ) (q : Fin t → ℕ) (hq : ∀ b, Nat.Prime (q b)) (hqi : Function.Injective q)
    (hq4 : ∀ b, q b % 4 = 1) (hsplit : ∀ b, SplitsCompletely (q b) K) :
    ∃ P : Fin (t * Module.finrank ℚ (maximalRealSubfield K)) → Ideal (𝓞 K),
      (∀ i, (P i).IsPrime) ∧ (∀ i j, i ≠ j → P i ≠ P j) ∧
      (∀ i j, Ideal.map (IsCMField.ringOfIntegersComplexConj K).toRingHom (P i) ≠ P j) ∧
      (∀ i, ∃ p : ℕ, p ∣ (∏ b, q b) ∧ Nat.Prime p ∧ Ideal.span {(p : 𝓞 K)} ≤ P i) :=
  Work.Prime.Combine K t q hq hqi hq4 hsplit

/-- **The lattice of the construction**: the elements `u` with `Q² u` integral form the fractional
ideal `Q⁻²𝒪_K`, and this lattice is separated at scale `1/Q²`. -/
theorem exists_lattice (K : Type) [Field K] [NumberField K] [IsCMField K]
    (Q : ℕ) (hQ : 0 < Q) (U : Finset K)
    (hU : ∀ u ∈ U, ∃ w : 𝓞 K, (w : K) = (Q : K) ^ 2 * u) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      (∀ u ∈ U, u ∈ (I : Set K)) ∧
      (∀ β ∈ (I : Set K), β ≠ 0 → ∃ w : InfinitePlace K,
        1 / (Q : ℝ) ^ 2 ≤ mixedEmbedding.normAtPlace w (mixedEmbedding K β)) :=
  Work.Lattice.Separation K Q hQ U hU

/-- **Minkowski's bound** (paper Proposition 3.7): the class number of a number field is at most
exponential in the degree, with a base depending only on the root discriminant. -/
theorem classNumber_le_rootDiscr :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K] (A : ℝ), 1 ≤ A →
      NumberField.rootDiscr K ≤ A →
      (NumberField.classNumber K : ℝ) ≤ (C * A * (1 + Real.log A)) ^ (Module.finrank ℚ K) :=
  Work.ClassNumber.Bound

/-- **Numerical core** (paper end of §2.2 and (11)), with the window radius as input. -/
theorem numeric_inequalities (t : ℕ) (Hc : ℝ) (hHc : 0 < Hc) (ht : 1 ≤ t)
    (hnum : Hc ^ 2 < (2:ℝ)^t) (D R : ℝ) (hD : 1 ≤ D) (hR : 1/2 < R) (hRD : 1 ≤ R * D)
    (hρ : -((t:ℝ) * Real.log 2 - 2 * Real.log Hc)/4 ≤ Real.log (1 - 1/(2*R))) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (f : ℕ) (U n : ℝ), 1 ≤ f → 0 < U → (2:ℝ) ^ (t * f) ≤ Hc ^ (2 * f) * U →
        n ≤ (4 * R * D) ^ (2 * f) → (2:ℝ) ^ (1 / δ) ≤ n →
        n ^ (1 + δ) ≤ 2⁻¹ * U * (1 - 1 / (2*R)) ^ (2*f) * n :=
  Work.Numeric.Inequalities t Hc hHc ht hnum D R hD hR hRD hρ

end Interface
end Work
