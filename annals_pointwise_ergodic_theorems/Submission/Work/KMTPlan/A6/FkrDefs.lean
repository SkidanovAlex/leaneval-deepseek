/-
# Definitions for the `fkr` interchange lemma (area A6)

This module fixes the vocabulary used by `Work.KMTPlan.A6.FkrInterchange`
(=`Work.KMTPlan.A6.FkrInterchange`, the paper's Lemma `fkr`: *interchanging variational and
Lebesgue norms*, Krause--Mirek--Tao, Annals 195 (2022), Lemma `fkr`).

The target is: for `1 ≤ R < r`, there is `C > 0` with

  `eLpNorm (fun x ↦ varPart r (fun k ↦ f k x)) r μ
     ≤ C * (⨆ J k, Monotone k, (∑ i, (eLpNorm (f (k i.succ) - f (k i.castSucc)) r μ) ^ R) ^ (1/R))`

for every sequence `f` of complex-valued functions on a measure space `(X, μ)`.  The right-hand
side is `fkrW` below; the left-hand side is the `eLpNorm` of the *variation part* of the
variational norm of the sequence `x ↦ (f k x)_k`.

## Contents

* `fkrW` -- the right-hand side (`V^R(ℕ; L^r)` norm of the sequence), in `ℝ≥0∞`;
* `Chain K` -- a monotone chain of indices in `{0, …, K}`;
* `varKc r K a` -- the clamped variation `⨆` over chains in `{0, …, K}` (an `ℝ≥0∞`-valued twin of
  the challenge's `varPart`, used to truncate the free chains of `varPart`);
* `fkrPhi β k t` -- the length of the intersection of `(0, t]` with the `k`-th block
  `(β (k-1), β k]`;
* `fkrH K β w x t` -- the piecewise linear interpolation of the points `(β k, g k x)` with density
  `w k x = (g k x - g (k-1) x) / (β k - β (k-1))`.

The mathematical content (the cell bound for `fkrH`, its telescoping along the chain `β ∘ u`, and
the assembly) is developed elsewhere; this file holds only the definitions and their elementary
algebra.
-/
import Mathlib

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- The right-hand side of the target `FkrInterchange`: the `V^R(ℕ; L^r)` norm of the sequence
`g`, i.e. the supremum over finite chains `k 0 ≤ … ≤ k J` of the `ℓ^R` norm of the `L^r` norms of
the successive differences. -/
noncomputable def fkrW (μ : Measure X) (R : ℝ) (r : NNReal) (g : ℕ → X → ℂ) : ENNReal :=
  ⨆ (J : ℕ) (k : Fin (J + 1) → ℕ), ⨆ (_ : Monotone k),
    (∑ i : Fin J, (eLpNorm (fun x => g (k i.succ) x - g (k i.castSucc) x) (r : ENNReal) μ) ^ R)
      ^ (1 / R)

/-- A monotone chain `u 0 ≤ … ≤ u J` of indices in `{0, …, K}`. -/
def Chain (K : ℕ) : Type :=
  Σ J : Fin (K + 1), {w : Fin (J.1 + 1) → Fin (K + 1) // Monotone w}

instance (K : ℕ) : Fintype (Chain K) := by
  classical
  unfold Chain
  infer_instance

/-- The clamped variation of a sequence: the supremum, over chains `u` of indices in `{0, …, K}`,
of the `ℓ^r` norm of the successive differences. -/
noncomputable def varKc (r : ℝ) (K : ℕ) (a : ℕ → ℂ) : ENNReal :=
  ⨆ p : Chain K,
    (∑ i : Fin p.1.1,
      ‖a ((p.2.1 i.succ : Fin (K + 1)) : ℕ) - a ((p.2.1 i.castSucc : Fin (K + 1)) : ℕ)‖ₑ ^ r)
      ^ (1 / r)

/-- The length of the intersection of `(0, t]` with the block `(β (k-1), β k]`. -/
noncomputable def fkrPhi (β : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  min (max 0 (min t 1)) (β k) - min (max 0 (min t 1)) (β (k - 1))

/-- The piecewise linear interpolation of the points `(β k, g k x)`, written with the density
`w k x = (g k x - g (k-1) x) / (β k - β (k-1))`: `fkrH K β w x t = ∑_{k=1}^{K} w k x • φ_k(t)`
where `φ_k(t) = |(0,t] ∩ (β(k-1), β k]|`. -/
noncomputable def fkrH (K : ℕ) (β : ℕ → ℝ) (w : ℕ → X → ℂ) (x : X) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 K, w k x * ((fkrPhi β k t : ℝ) : ℂ)

end Work.KMTPlan.A6
