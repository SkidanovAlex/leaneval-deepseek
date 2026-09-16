import Submission.ZagierHoffmanProof.GenLSeries
import Submission.ZagierHoffmanProof.LSeries

/-!
# Regression tests for the generic depth-one `L`-series

Over a `ℤᵐ⁰`-valued field the generic definitions of `GenLSeries.lean` are *the same* as the
`ℤᵐ⁰`-specific ones of `LSeries.lean` (`GIsSmall (exp (-1)) = IsSmall`, `atL1Gen = atL1`), which
makes the generic chapter a faithful generalisation of the existing one; and the concrete small
series `θ⁻¹ Ω̃` of `LSeries.lean` is a `GIsSmall` series.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- The generic smallness condition at `γ = exp (-1)` is the `ℤᵐ⁰`-specific one. -/
lemma gIsSmall_iff_isSmall (f : PowerSeries K) :
    GIsSmall (WithZero.exp (-1)) f ↔ IsSmall f := Iff.rfl

/-- The generic depth-one `L`-series is the `ℤᵐ⁰`-specific one. -/
lemma atL1Gen_eq_atL1 (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (s : ℕ) (Q : PowerSeries K) :
    atL1Gen (K := K) q ω s Q = atL1 (K := K) q ω s Q := rfl

/-- The concrete small series `θ⁻¹ Ω̃` of `LSeries.lean` is small in the generic sense. -/
lemma gIsSmall_omegaSmall (q : ℕ) (θ : K) [FrobPow K q] [CompleteSpace K]
    [NonarchimedeanAddGroup K] (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    GIsSmall (WithZero.exp (-1)) (omegaSmall (K := K) q θ) :=
  (gIsSmall_iff_isSmall _).mpr (isSmall_omegaSmall (K := K) q θ hθ hq)

end ZagierHoffmanPositiveChar
