/-
Copyright (c) 2025 Katerina Hristova. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, Kevin Buzzard
-/

import Mathlib.Topology.MetricSpace.HausdorffDimension
import Submission.Helpers
import Submission.DS.CircRed
import Submission.Main.Transport
import Submission.DS.Thm2a
import Submission.DS.Case1
import Submission.DS.Truncate
import Submission.DS.Catlin2b
import Submission.DS.Coro3Main
import Submission.Main.BVMain
import Submission.Work.MassTransferenceAlt.Main
import ChallengeDeps
/-!
# Main Statements from On the Duffin-Schaeffer conjecture

We formalise the statements of the main results from D. Koukoulopoulos and J. Maynard,
`On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020.

## Implementation Details

In the paper, `ℕ` denotes the positive integers, which are denoted `ℕ+` in Lean.
Hence, no changes to the domains of the functions `ψ` and `ψ⋆` have been made in the formalisation.
-/


namespace Submission

open _root_.DuffinSchaefferConjecture
set_option autoImplicit false

namespace DuffinSchaefferConjecture

open NNReal ENNReal MeasureTheory

open scoped Nat





/--
Statement of Theorem 1:

If for `ψ : ℕ → ℝ≥0`, the infinite series `∑ (ψ q * φ q) / q`, where `φ` is the
Euler totient function, diverges, then the set `𝒜` defined above has Lebesgue measure `1`.
-/
theorem theorem_1 (ψ : ℕ+ → ℝ≥0) (hdivergence : ¬ Summable fun q ↦ (ψ q * φ q) / q) :
    MeasurableSet (𝒜 ψ) ∧ volume (𝒜 ψ) = 1 :=
  ⟨Submission.DS.measurableSet_A ψ,
    Submission.Main.volume_A_eq_one_of_divergence ψ hdivergence⟩





/--
Statement of Theorem 2(a):

Let `ψ : ℕ → ℝ≥0`, `𝒦` and `ψ⋆` be as above. Then, if `∑ ψ⋆ (q)` converges, `𝒦` has Lebesgue
measure `0`.
-/
theorem theorem_2_a (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q, ψ_star ψ q < ∞) :
    MeasurableSet (𝒦 ψ) ∧ volume (𝒦 ψ) = 0 :=
  Submission.DS.theorem_2_a_core ψ hψ

/--
Statement of Theorem 2(b):

Let `ψ : ℕ → ℝ≥0`, `𝒦` and `ψ⋆` be as above. Then, if `∑ ψ⋆ (q)` diverges, `𝒦` has Lebesgue
measure `1`.
-/
theorem theorem_2_b (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q, ψ_star ψ q = ∞) :
    MeasurableSet (𝒦 ψ) ∧ volume (𝒦 ψ) = 1 :=
  Submission.DS.theorem_2_b_of_theorem_1
    (fun χ hdiv => ⟨Submission.DS.measurableSet_A χ,
      Submission.Main.volume_A_eq_one_of_divergence χ hdiv⟩) ψ hψ



/--
Statement of Corollary 3:

For a function `ψ : ℕ → [0, 1/2]`, the set `𝒜` and the element `s` defined as above,
the Hausdorff dimension of `𝒜` is the minimum of `s` and `1`.
-/
theorem corollary_3 (ψ : ℕ+ → ℝ≥0) (hψ : ∀ n, ψ n ∈ Set.Icc 0 (1 / 2)) :
    dimH (𝒜 ψ) = min (s_inf ψ) 1 :=
  Submission.Main.corollary_3_of_MTP
    Work.MassTransferenceAlt.massTransferencePrincipleOne ψ hψ

/--
The elementary (Jarník-type covering) UPPER bound of Corollary 3, proved
independently of the Duffin–Schaeffer theorem:

    dimH (𝒜 ψ) ≤ min (s_inf ψ) 1

(see `Submission.DS.dimH_A_le_min`; the reverse inequality is the deep
Beresnevich–Velani mass-transference lower bound).
-/
lemma coro3_upper_bound (ψ : ℕ+ → ℝ≥0) (hψ : ∀ n : ℕ+, ψ n ∈ Set.Icc 0 (1 / 2 : ℝ≥0)) :
    dimH (𝒜 ψ) ≤ ((min (s_inf ψ) 1 : ℝ≥0) : ℝ≥0∞) :=
  Submission.DS.dimH_A_le_min ψ hψ

end DuffinSchaefferConjecture

end Submission
