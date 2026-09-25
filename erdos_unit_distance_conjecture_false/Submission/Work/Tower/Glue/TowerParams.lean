import Submission.Work.Tower.Params.exists_tower_parameters
import Submission.Work.Tower.APDensity.Main
import Submission.Work.Tower.Defs

/-!
# End-to-end parameter selection for the tower

Combines the prime-counting input (`Work.Tower.exists_primes_mod_three_log_sum`, area
`Tower/APDensity`) with the numeric window of `Work.Tower.Params.exists_tower_parameters`, to
produce, for every target class-number base `H` and every S̆afarevič constant `C₀`, the
parameters `ℓ`, `rᵢ`, `t`, `C` of the tower construction:

* the `rᵢ` are `ℓ` distinct primes `≡ 1 (mod 3)`;
* `C = max 1 (2 · exp ((2/3) ∑ log rᵢ))` is (twice) the root discriminant of the base field;
* `(H · C · (1 + log C))² < 2^t` (the split primes beat the class-number loss);
* `(ℓ-1)² > 4((ℓ-1) + C₀ + 3t)` (the Golod–S̆afarevič deficiency condition with `m = ℓ-1`
  generators and `3t` killed Frobenius elements).
-/

open scoped Classical BigOperators

namespace Work
namespace Tower
namespace Glue

/-- End-to-end parameter selection: from the prime-counting theorem of the `APDensity` area and
the numeric window lemma, for every `H > 0` and every `C₀` there are tower parameters. -/
theorem exists_tower_params (H : ℝ) (hH : 0 < H) (C₀ : ℕ) :
    ∃ (ℓ : ℕ) (r : Fin ℓ → ℕ) (t : ℕ) (C : ℝ),
      (∀ i, Nat.Prime (r i)) ∧ Function.Injective r ∧ (∀ i, r i % 3 = 1) ∧
      0 < ℓ ∧ 0 < t ∧ 1 ≤ C ∧
      C = max 1 (2 * Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ))) ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      4 * (((ℓ - 1 : ℕ) : ℝ) + C₀ + 3 * t) < (((ℓ - 1 : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨C_A, hCA, hap⟩ := Work.Tower.exists_primes_mod_three_log_sum
  exact Work.Tower.Params.exists_tower_parameters C_A hCA hap H hH C₀

end Glue
end Tower
end Work
