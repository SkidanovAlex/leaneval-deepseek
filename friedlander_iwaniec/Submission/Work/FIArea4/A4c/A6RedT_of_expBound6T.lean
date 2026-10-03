import Mathlib
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FIArea4.A6R2.sepBound6
import Submission.Work.FIArea4.A6R2.expLogBound6
import Submission.Work.FIArea4.A6R2.psiSumEqTcut6

namespace Work.FIArea4.A4c

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The §15 reduction with the divisor factor `T` carried through**
(`Work.FIArea4.A4c.A6RedTProp` is defined in `Submission/Work/FIArea4/A4c/Defs.lean`).

Copy the proof of `Work.FIArea4.A6Red` (`Submission/Work/FIArea4/A6Red.lean`), replacing the crux
`ExpBound6`/`ExpBound6_proof` by the hypothesis `h : ExpBound6T` and carrying the factor `T`:
* `Work.FIArea4.A6R2.sepBound6 ψ hψ hψsup` gives `C₁, x₁` with `‖psiSum6‖ ≤ C₁ (log N+1)² M`;
* `Work.FIArea4.A6R2.expLogBound6` gives `C₂` with `‖expLog6‖ ≤ C₂ (log N+1)² M'`;
* `h` gives `C₃, x₀` with `‖expSum6‖ ≤ C₃ (log N+1)⁴ S15Br6 (T · A6Ener3)`;
* `Work.FIArea4.A6R2.psiSumEqTcut6 Pa X j ψ hψsup hX φ β (A6Cl.toPrimBoxCoeff hβ)` rewrites
  `Tcut (A6cut ψ X j) β` to `psiSum6 Pa X j ψ β`;
then the exponents compose as `2 + 2 + 4 = 8` and the `T` sits in the final factor.  Only
`IsPrimBoxCoeff Pa φ β` (and `1 ≤ X`, `X ≤ N^{1/9}`) are used by the two middle steps;
`DivBound Pa β T` is used only to invoke `h`. -/
theorem A6RedT_of_expBound6T (h : Work.FIArea4.A4c.ExpBound6T) : Work.FIArea4.A4c.A6RedTProp := by
  intro ψ hψ hψ0 hψ1 hψsup
  obtain ⟨C₁, hC₁, hSep⟩ := A6R2.sepBound6 ψ hψ hψsup
  obtain ⟨C₂, hC₂, hLog⟩ := A6R2.expLogBound6
  obtain ⟨C₃, x₀, hC₃, hCrux⟩ := h
  refine ⟨C₁ * C₂ * C₃, x₀, by positivity, ?_⟩
  intro Pa hx X φ j β T hβ hDiv hX hX9
  have hM : ∀ (ℓ : ℤ) (u t : ℝ), ‖A6R2.expSum6 Pa X j β ℓ u t‖
      ≤ C₃ * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * (T * A6Ener3 Pa β) :=
    fun ℓ u t => hCrux Pa hx X j φ β ℓ u t T hβ hX hX9 hDiv
  have hM2 : ∀ u t : ℝ, ‖A6R2.expLog6 Pa X j β u t‖
      ≤ C₂ * (Real.log Pa.N + 1) ^ 2
          * (C₃ * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * (T * A6Ener3 Pa β)) :=
    fun u t => hLog Pa X j φ β u t _ hβ hX (fun ℓ => hM ℓ u t)
  have hfin := hSep Pa X j φ β _ hβ hX hM2
  rw [A6R2.psiSumEqTcut6 Pa X j ψ hψsup hX φ β hβ]
  calc ‖A6R2.psiSum6 Pa X j ψ β‖
      ≤ C₁ * (Real.log Pa.N + 1) ^ 2
          * (C₂ * (Real.log Pa.N + 1) ^ 2
              * (C₃ * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * (T * A6Ener3 Pa β))) := hfin
    _ = C₁ * C₂ * C₃ * (Real.log Pa.N + 1) ^ 8 * S15Br6 Pa X * (T * A6Ener3 Pa β) := by ring

end

end Work.FIArea4.A4c
