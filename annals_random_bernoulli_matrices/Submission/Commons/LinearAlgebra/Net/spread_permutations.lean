import Mathlib
import Submission.Commons.LinearAlgebra.Net.perm_family_top_coords
import Submission.Commons.LinearAlgebra.Net.perm_spreads

set_option autoImplicit false
open scoped BigOperators

namespace Commons.LinearAlgebra.Net

/--
`spread_permutations` : the "special permutations" lemma of K. Tikhomirov,
`Singularity of random Bernoulli matrices`, Ann. of Math. 191 (2020).

For every `n ≥ 2` there is a set `PiSet` of permutations of `Fin n` of
cardinality at most `CPermⁿ` (universal `CPerm`) such that for every
unit, incompressible vector `x` and every integer vector `spv` within
sup-distance 1 of `(√n/th)·x` there is a permutation `σ ∈ PiSet` after
which the reordered integer vector has: (lower bound) its first `⌊δn⌋`
entries of absolute value `> ν/th − 1`, and (upper bound) at every dyadic
level `j` (`2^j ≤ δ·n`) the entries at positions `δn/2^j < i+1` are at
most `2^((j+1)/2)/(√δ·th) + 1` in absolute value.

The proof combines two commons results:
`Commons.LinearAlgebra.Net.perm_family_top_coords` supplies the universal
family `PiSet` with the dyadic top-coordinate domination property, and
`Commons.LinearAlgebra.Net.perm_spreads` turns that domination property
(using incompressibility and the rounding hypothesis `hspv`) into the two
clauses above. -/
theorem spread_permutations :
    ∃ CPerm : ℝ, 1 ≤ CPerm ∧
    ∀ (n : ℕ) (hn : 2 ≤ n), ∃ PiSet : Finset (Equiv.Perm (Fin n)),
      (PiSet.card : ℝ) ≤ CPerm ^ n ∧
      ∀ {δ ν : ℝ} (hδ₀ : 0 < δ) (hδ₁₂ : δ ≤ 1 / 2) (hν₀ : 0 < ν) (hν₁ : ν ≤ 1)
        (x : Fin n → ℝ) (hx : sqNorm x = 1) (hinc : ¬ compressible δ ν x)
        {th : ℝ} (hth₀ : 0 < th) (spv : Fin n → ℤ)
        (hspv : ∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * x i - (spv i : ℝ)| ≤ 1),
        ∃ σ : Equiv.Perm (Fin n), σ ∈ PiSet ∧
          (∀ i : Fin n, ((i : ℝ) + 1) ≤ δ * (n : ℝ) →
              ν / th - 1 < |(spv (σ i) : ℝ)|) ∧
          (∀ j : ℕ, (2 : ℝ) ^ j ≤ δ * (n : ℝ) → ∀ i : Fin n,
              δ * (n : ℝ) / (2 : ℝ) ^ j < ((i : ℝ) + 1) →
              |(spv (σ i) : ℝ)| ≤
                (2 : ℝ) ^ (((j : ℝ) + 1) / 2) / (Real.sqrt δ * th) + 1) := by
  classical
  rcases perm_family_top_coords with ⟨CPerm, hC1, hfam⟩
  refine ⟨CPerm, hC1, ?_⟩
  intro n hn
  rcases hfam n hn with ⟨PiSet, hPiCard, hPiProp⟩
  refine ⟨PiSet, hPiCard, ?_⟩
  intro δ ν hδ₀ hδ₁₂ hν₀ hν₁ x hx hinc th hth₀ spv hspv
  rcases hPiProp x δ hδ₀ hδ₁₂ with ⟨σ, hσmem, hdom⟩
  refine ⟨σ, hσmem, ?_⟩
  exact perm_spreads hδ₀ hδ₁₂ hν₀ x hx hinc hth₀ spv hspv σ hdom

end Commons.LinearAlgebra.Net
