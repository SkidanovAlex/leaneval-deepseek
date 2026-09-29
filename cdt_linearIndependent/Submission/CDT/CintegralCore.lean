import Mathlib
import Submission.Commons.Analysis.Integral.cintegral_recurrence_parametric
import Submission.CDT.CintegralOne
import Submission.CDT.L2chi3Cintegral
import Submission.CDT.ZagierH
import Submission.CDT.ZagierHBC
import Submission.CDT.EichlerInput

/-!
# `(Cintegral)` for all `n` via the Zagier recurrence (core, split out of `CintegralAssembled`)

The per-degree instances `n ≤ 35` in `CintegralAssembled` are not needed: the identity follows for every `n`
from the two base cases and the parametric recurrence `cintegral_recurrence_parametric`.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Interval

namespace Submission.CDT

/-!
## The parametric reduction of `CintegralIdentity` to the Zagier recurrence

The `(Cintegral)` coefficient identity relates two sequences that both
satisfy the **Zagier three-term P-recurrence**

`(n+1)²y_{n+1} = (10n² + 10n + 3)·yₙ − 9n²·y_{n−1}`   (`n ≥ 1`):

* the sequence `cₙ := L(2,χ₋₃)·aₙ − 2·bₙ` — because `(aₙ)` and `(bₙ)` do
  (`HA_coeff_recurrence`, `HB_coeff_recurrence`, both PROVED);
* the double integrals `Jₙ = cintegralJ n` — this is the one *analytic*
  input that is still open (the Beukers/Zagier evaluation of the period
  integrals, i.e. the (Cintegral)/Beukers-integral evaluation for general
  `n`).

Since a sequence satisfying that recurrence is determined by its first two
values, and the two base cases `n = 0, 1` are PROVED
(`CintegralIdentity_zero`, `cintegral_identity_one`), the *whole* of
`CintegralIdentity` — and hence the analytic conjunct of `EichlerInputB` —
follows from the single parametric recurrence for `J`.  The reductions below
record this precisely (`CintegralIdentity_of_recurrence`,
`overconvergesB_of_recurrence`). -/

/-- **the Zagier recurrence determines a sequence from its first two
values**: if `u`, `v` both satisfy
`(n+1)²y_{n+1} = (10n²+10n+3)yₙ − 9n²y_{n−1}` (`n ≥ 1`) and `u 0 = v 0`,
`u 1 = v 1`, then `u = v`. -/
theorem eq_of_zagier_recurrence {u v : ℕ → ℝ}
    (hu : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ 2 * u (n + 1)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * u n - 9 * (n : ℝ) ^ 2 * u (n - 1))
    (hv : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ 2 * v (n + 1)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * v n - 9 * (n : ℝ) ^ 2 * v (n - 1))
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) : ∀ n, u n = v n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more k ihk ihk1 =>
      have huk := hu (k + 1) (by omega)
      have hvk := hv (k + 1) (by omega)
      rw [show k + 1 + 1 = k + 2 by omega, show k + 1 - 1 = k by omega] at huk hvk
      have hne : (((k + 2 : ℕ)) : ℝ) ^ 2 ≠ 0 := by positivity
      apply mul_left_cancel₀ hne
      rw [huk, hvk, ihk, ihk1]

/-- the combination `L(2,χ₋₃)·aₙ − 2·bₙ` satisfies the Zagier recurrence
(from `HA_coeff_recurrence` and `HB_coeff_recurrence`) -/
theorem zagier_diff_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℝ) ^ 2
        * (L2chi3Real * (HA_coeff (n + 1) : ℝ) - 2 * (HB_coeff (n + 1) : ℝ))
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3)
          * (L2chi3Real * (HA_coeff n : ℝ) - 2 * (HB_coeff n : ℝ))
        - 9 * (n : ℝ) ^ 2
          * (L2chi3Real * (HA_coeff (n - 1) : ℝ) - 2 * (HB_coeff (n - 1) : ℝ)) := by
  have hA : ((n + 1 : ℕ) : ℝ) ^ 2 * (HA_coeff (n + 1) : ℝ)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * (HA_coeff n : ℝ)
        - 9 * (n : ℝ) ^ 2 * (HA_coeff (n - 1) : ℝ) := by
    have h := HA_coeff_recurrence n hn
    exact_mod_cast h
  have hB : ((n + 1 : ℕ) : ℝ) ^ 2 * (HB_coeff (n + 1) : ℝ)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * (HB_coeff n : ℝ)
        - 9 * (n : ℝ) ^ 2 * (HB_coeff (n - 1) : ℝ) := by
    have h := HB_coeff_recurrence n hn
    have h' : ((n + 1 : ℕ) : ℚ) ^ 2 * HB_coeff (n + 1)
        = ((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * HB_coeff n
          - (9 : ℚ) * (n : ℚ) ^ 2 * HB_coeff (n - 1) := by
      linear_combination h
    exact_mod_cast h'
  linear_combination (L2chi3Real) * hA - 2 * hB

/-- **`CintegralIdentity` from the single parametric recurrence** for the
double integrals `Jₙ = cintegralJ n`. -/
theorem CintegralIdentity_of_recurrence
    (hrec : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ 2 * cintegralJ (n + 1)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * cintegralJ n
        - 9 * (n : ℝ) ^ 2 * cintegralJ (n - 1)) : CintegralIdentity := by
  have h01 := eq_of_zagier_recurrence
    (u := fun n => L2chi3Real * (HA_coeff n : ℝ) - 2 * (HB_coeff n : ℝ))
    (v := cintegralJ) zagier_diff_recurrence hrec
    (by simpa [CintegralIdentityAt] using cintegral_identity_le_one 0 (by norm_num))
    (by simpa [CintegralIdentityAt] using cintegral_identity_le_one 1 (by norm_num))
  intro n
  exact h01 n

/-- **the analytic conjunct of `EichlerInputB` from the single parametric
recurrence**: `OverconvergesUnit eichlerDiffB` follows from the Zagier
recurrence for `cintegralJ`. -/
theorem overconvergesB_of_recurrence
    (hrec : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ 2 * cintegralJ (n + 1)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * cintegralJ n
        - 9 * (n : ℝ) ^ 2 * cintegralJ (n - 1)) : OverconvergesUnit eichlerDiffB :=
  overconvergesB_of_cintegral (CintegralIdentity_of_recurrence hrec) cintegralJ_bound'

/-! ## The parametric recurrence is PROVED (commons lemma) — `(Cintegral)` closes

The commons lemma `Commons.Analysis.Integral.cintegral_recurrence_parametric`
(explicit divergence certificate `P(n,s,t) = P₀(s,t) + n·P₁(s,t)` for the
`(0,1)²`-integral of the `n`-family `9ⁿ(st)ⁿ(1−s³)ⁿ(1−t³)ⁿ/(1+st+s²t²)^{2n+1}`)
proves the Zagier recurrence for the double integrals for *all* `n ≥ 1`.
Through `CintegralIdentity_of_recurrence` this closes the whole
`(Cintegral)` identity, and hence the `H_B`-side overconvergence of node (2).
-/

/-- **the parametric Zagier recurrence** `(n+1)²J_{n+1} = (10n²+10n+3)Jₙ − 9n²J_{n−1}`
for the `(Cintegral)` double integrals, from the commons lemma
`Commons.Analysis.Integral.cintegral_recurrence_parametric` -/
theorem cintegralJ_recurrence : ∀ n : ℕ, 1 ≤ n →
    (((n + 1 : ℕ) : ℝ)) ^ 2 * cintegralJ (n + 1)
      = (10 * ((n : ℕ) : ℝ) ^ 2 + 10 * ((n : ℕ) : ℝ) + 3) * cintegralJ n
        - 9 * ((n : ℕ) : ℝ) ^ 2 * cintegralJ (n - 1) := by
  intro n hn
  have h := Commons.Analysis.Integral.cintegral_recurrence_parametric n hn
  simpa [cintegralJ, cintegralKernel] using h

/-- **`(Cintegral)` is PROVED**: `L(2,χ₋₃)·aₙ − 2·bₙ = Jₙ` for every `n` -/
theorem CintegralIdentity_proved : CintegralIdentity :=
  CintegralIdentity_of_recurrence cintegralJ_recurrence

/-- **the `H_B`-overconvergence of node (2), unconditional**:
`OverconvergesUnit eichlerDiffB` (radius-≥1 overconvergence of
`H_B − (L(2,χ₋₃)/2)·H_A`) -/
theorem overconvergesB_proved : OverconvergesUnit eichlerDiffB :=
  overconvergesB_of_cintegral CintegralIdentity_proved cintegralJ_bound'

/-- `EichlerInputB` from the modular conjunct and the parametric recurrence -/
theorem eichlerInputB_of_modular_and_recurrence (hMod : ModularIntegralityB)
    (hrec : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ 2 * cintegralJ (n + 1)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * cintegralJ n
        - 9 * (n : ℝ) ^ 2 * cintegralJ (n - 1)) : EichlerInputB :=
  eichlerInputB_of_modular_and_cintegral hMod (CintegralIdentity_of_recurrence hrec)
    cintegralJ_bound'

/-- **`EichlerInputB` from the modular conjunct alone**: the analytic
(overconvergence) half is now proved; only the modular `[1..n]²`-integrality
remains. -/
theorem eichlerInputB_of_modular (hMod : ModularIntegralityB) : EichlerInputB :=
  eichlerInputB_of_modular_and_recurrence hMod cintegralJ_recurrence


end Submission.CDT
