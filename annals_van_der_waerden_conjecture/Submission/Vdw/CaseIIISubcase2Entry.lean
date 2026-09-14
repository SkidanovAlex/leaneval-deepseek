import Mathlib
import Submission.Vdw.CaseIIIThreshold
import Submission.Vdw.CaseIIIRegion

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case III, subcase (ii): the eventual *entry* of paper-side data into the
region `CaseIIISubcase2` at the canonical threshold

The paper's subcase (ii) is `A = ∏_{p | C, p > H^(δ/2)} p > H`, where `C` is
the product of the ramified primes of `K_f` (`ramifiedProduct f`, = the
radical of `D_f`), and `δ/2 = 1/(4n)`.  Since `p` ranges over integers,
`p > H^(δ/2)` (real) ⟺ `⌈H^(δ/2)⌉ ≤ p` (integer), and the counting region
`CaseIIISubcase2 n H B` is expressed at an integer threshold `B` as
`largePart D_f B = ∏_{p | D_f, B ≤ p} p`.  This module closes the last
"translation" gaps between the paper's `C`-side data and the region:

* `radical_primeFactors` — the prime factors of the radical of `N` are
  exactly those of `N` (`Nat.primeFactors_prod_primeFactors`);
* `ramifiedProduct_primeFactors_eq` — `C_f` and `D_f` have the same prime
  factors (`C_f = radical D_f`);
* `mem_caseIIISubcase2_of_ramified_data` — an irreducible box polynomial
  `f` (degree `n ≥ 3`) whose `D_f` is squarefull, with `DD(u_f) ≠ 0` and
  `H < largePart C_f (lowerThr (4n) H)` (the paper's subcase-(ii) condition
  on the ramified-product side, at the integer canonical threshold
  `⌈H^(1/(4n))⌉`) lies in `CaseIIISubcase2 n H (lowerThr (4n) H)`.

Together with `caseIII_subcase2_region_isBigO` /
`caseIII_subcase2_region_bound_pointwise` (`CaseIIIThreshold`,
`CaseIIIBound`) this is exactly the counting input the eventual assembly
needs for subcase (ii) of Case III.
-/

namespace Submission.Vdw

/-- The radical of `N` has the same prime factors as `N`
(`radical N = ∏_{p | N} p`, so `Nat.primeFactors_prod_primeFactors`). -/
lemma radical_primeFactors (N : ℕ) : (radical N).primeFactors = N.primeFactors := by
  unfold radical
  exact Nat.primeFactors_prod_primeFactors N

/-- `C_f` (the product of the ramified primes of `K_f`, i.e. the radical of
`D_f`) and `D_f = fieldDisc f` have the same prime factors. -/
lemma ramifiedProduct_primeFactors_eq (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] :
    (ramifiedProduct f).primeFactors = (fieldDisc f).primeFactors := by
  unfold ramifiedProduct
  exact radical_primeFactors (fieldDisc f)

/-- **Entry into the subcase-(ii) region.**  Irreducible box polynomial `f`
(degree `n ≥ 3`) with squarefull `D_f`, `DD(u_f) ≠ 0`, and
`H < largePart C_f (lowerThr (4n) H)` (subcase (ii): the large-prime part of
the ramified product `C_f` above the canonical threshold `⌈H^(1/(4n))⌉`
exceeds `H`) lies in the region `CaseIIISubcase2 n H (lowerThr (4n) H)`. -/
theorem mem_caseIIISubcase2_of_ramified_data (n H : ℕ) (_hn : 3 ≤ n) (f : ℤ[X])
    (h : Irreducible (f.map φℚ)) (hfbox : f ∈ Box n H)
    (hsq : Squarefull (fieldDiscExp f h))
    (hdd : concDDZ n (upperCoeffs n f) ≠ 0)
    (hA : H < largePart (@ramifiedProduct f (Fact.mk h)) (lowerThr (4 * n) H)) :
    f ∈ CaseIIISubcase2 n H (lowerThr (4 * n) H) := by
  classical
  refine ⟨h, hfbox, hsq, hdd, ?_⟩
  -- the region's largePart is computed from D_f; the hypothesis from C_f:
  -- ramifiedProduct f = radical (fieldDisc f), same prime factors
  have hlg : largePart (@ramifiedProduct f (Fact.mk h)) (lowerThr (4 * n) H) =
      largePart (fieldDiscExp f h) (lowerThr (4 * n) H) := by
    haveI : Fact (Irreducible (f.map φℚ)) := ⟨h⟩
    dsimp [fieldDiscExp]
    exact ramifiedProduct_largePart_eq f (lowerThr (4 * n) H)
  exact (by simpa [hlg] using hA)

/-- **Entry, region membership from the arithmetic large-part of `D_f`**
(direct instance of the `CaseIIISubcase2` definition; included for
completeness of the interface). -/
theorem mem_caseIIISubcase2_of_field_disc_data (n H : ℕ) (f : ℤ[X])
    (h : Irreducible (f.map φℚ)) (hfbox : f ∈ Box n H)
    (hsq : Squarefull (fieldDiscExp f h))
    (hdd : concDDZ n (upperCoeffs n f) ≠ 0)
    (hA : H < largePart (fieldDiscExp f h) (lowerThr (4 * n) H)) :
    f ∈ CaseIIISubcase2 n H (lowerThr (4 * n) H) := by
  exact ⟨h, hfbox, hsq, hdd, hA⟩

end Submission.Vdw
