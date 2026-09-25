import Mathlib

/-!
# Shared definitions for the unit-distance construction

Vocabulary used by both the arithmetic and the geometric parts of the proof that
Erdős's unit-distance conjecture is false.
-/

open MeasureTheory
open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Defs

/-- Unit-distance count for a finite planar point set modelled inside `ℂ`:
the number of unordered pairs `{x,y}` of distinct points at distance exactly `1`. -/
noncomputable def cDist (P : Finset ℂ) : ℕ :=
  (P.offDiag.filter (fun pq => ‖pq.1 - pq.2‖ = 1)).card / 2

/-- The sup-norm polydisc of radius `R` in `ι → ℂ`. -/
def Window {ι : Type*} (R : ℝ) : Set (ι → ℂ) := {z | ∀ i, ‖z i‖ < R}

/-- A rational prime `q` splits completely in the number field `L`: the ideal `q𝒪_L` is a
product of `[L : ℚ]` pairwise distinct primes, each with residue field `𝔽_q`. -/
def SplitsCompletely (q : ℕ) (L : Type*) [Field L] [NumberField L] : Prop :=
  ∃ 𝔮 : Fin (Module.finrank ℚ L) → Ideal (𝓞 L),
    (∀ i, (𝔮 i).IsPrime) ∧ (∀ i, (q : 𝓞 L) ∈ 𝔮 i) ∧
    (∀ i, Nonempty (𝓞 L ⧸ 𝔮 i ≃+* ZMod q)) ∧
    (∀ i j, i ≠ j → ¬ 𝔮 i ≤ 𝔮 j) ∧
    (Ideal.span {(q : 𝓞 L)} = ∏ i, 𝔮 i)

end Defs
end Work
