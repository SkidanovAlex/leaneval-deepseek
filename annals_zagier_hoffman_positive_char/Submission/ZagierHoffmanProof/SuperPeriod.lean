import Submission.ZagierHoffmanProof.PeriodL
import Submission.ZagierHoffmanProof.SuperOmega
import Submission.ZagierHoffmanProof.SuperLSeries

/-!
# The period function and the depth-one `L`-series over `F((y))` lie in `ε`

`SuperOmega.lean` proves that the Anderson–Thakur period function `Ω` and the depth-one `L`-series
`∑_{i≥0}(ω^sQ)^{(i)}` are *super-entire* (lie in ABP's ring `ε`, i.e. converge everywhere), and
`PeriodL.lean` realises `Ω = C μ · ∏_{i≥1}(1 - t/θ^{q^i})` concretely over the Kummer field
`F((y))` (with `θ = -y^{-(q-1)}`, `μ = y^q`).

This file combines the two: over `F((y))` the period function is super-entire, and so is the
depth-one `L`-series with `ω := Ω` and any small constant `Q` — Chang's Lemma 5.3.1 (depth one)
in the concrete normalisation.

## Main results

* ★★ `superEntire_periodOmega` — `Ω ∈ ε` over `F((y))`.
* ★★★ `superEntire_atL1_periodOmega` — the `L`-series `∑_i (Ω^s Q)^{(i)}` of a small constant
  `Q` lies in `ε`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology
open LaurentSeries HahnSeries

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

noncomputable section

/-- **The Anderson–Thakur period function over `F((y))` is super-entire.** -/
theorem superEntire_periodOmega : SuperEntire (periodOmega F) := by
  haveI : FrobPow (LaurentSeries F) (periodCard F) := frobPow_laurentSeries F
  exact (SuperEntire.C (periodMu F)).mul
    (superEntire_atOmega (periodCard F) (periodTheta F) (periodD F) (one_le_periodD F)
      (v_periodTheta F) (two_le_periodCard F))

/-- **Chang's Lemma 5.3.1 (depth one) over `F((y))`**: for a small constant `c`, the `L`-series
`∑_{i≥0} (Ω^s · C c)^{(q^i)}` is super-entire. -/
theorem superEntire_atL1_periodOmega {c : LaurentSeries F}
    (hc : Valued.v c ≤ WithZero.exp (-1)) (s : ℕ) :
    SuperEntire (atL1 (periodCard F) (periodOmega F) s (PowerSeries.C c)) :=
  superEntire_atL1Fold (periodCard F) (two_le_periodCard F) (isSmall_periodDatum_L F)
    (superEntire_periodOmega F) (isSmall_C hc) (SuperEntire.C c) s

/-- The concrete instance with the period constant `c = μ`. -/
theorem superEntire_atL1_periodOmega_mu (s : ℕ) :
    SuperEntire (atL1 (periodCard F) (periodOmega F) s (PowerSeries.C (periodMu F))) :=
  superEntire_atL1_periodOmega F (v_periodMu_le_one F) s

/-- **Chang's Lemma 5.3.1 over `F((y))`, all depths**: the (cutoff) `L`-series of any list of
small super-entire factors is super-entire. -/
theorem superEntire_atLrcut_periodOmega {L : List (ℕ × PowerSeries (LaurentSeries F))}
    (hL : ∀ x ∈ L, IsSmall x.2) (hLse : ∀ x ∈ L, SuperEntire x.2) (N : ℕ) :
    SuperEntire (atLrcut (periodCard F) (periodOmega F) L N) :=
  superEntire_atLrcut (periodCard F) (two_le_periodCard F) (isSmall_periodDatum_L F)
    (superEntire_periodOmega F) hL hLse N

/-- The same without the cutoff. -/
theorem superEntire_atLr_periodOmega {L : List (ℕ × PowerSeries (LaurentSeries F))}
    (hL : ∀ x ∈ L, IsSmall x.2) (hLse : ∀ x ∈ L, SuperEntire x.2) :
    SuperEntire (atLr (periodCard F) (periodOmega F) L) :=
  superEntire_atLr (periodCard F) (two_le_periodCard F) (isSmall_periodDatum_L F)
    (superEntire_periodOmega F) hL hLse

/-- A concrete depth-two instance: the `L`-series of `(1, μ), (2, μ)`. -/
theorem superEntire_atLr_periodOmega_example :
    SuperEntire (atLr (periodCard F) (periodOmega F)
      [(1, PowerSeries.C (periodMu F)), (2, PowerSeries.C (periodMu F))]) :=
  superEntire_atLr_periodOmega F
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx <;> rw [hx] <;> exact isSmall_C (v_periodMu_le_one F))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx <;> rw [hx] <;> exact SuperEntire.C (periodMu F))

/-- **The entries of the trivialisation matrix `Ψ` over `F((y))` lie in `ε`.** -/
theorem superEntire_Psi_entry {L : List (ℕ × PowerSeries (LaurentSeries F))}
    (hL : ∀ x ∈ L, IsSmall x.2) (hLse : ∀ x ∈ L, SuperEntire x.2) (s : ℕ) :
    SuperEntire (atLr (periodCard F) (periodOmega F) L * periodOmega F ^ s) :=
  superEntire_atLr_mul_pow (periodCard F) (two_le_periodCard F) (isSmall_periodDatum_L F)
    (superEntire_periodOmega F) hL hLse s

end

end ZagierHoffmanPositiveChar
