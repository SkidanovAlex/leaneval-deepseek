/-
# `Work.FIChain.PerLayerDefs` — the vocabulary of the FI per-layer bound

The definitions used by `Work.FIChain.TnB_FIgtil_perLayer` and by the lemmas it is assembled
from.  The per-layer bound is

    `TnB 19 ν_Δ (2k+1) Δ (yFI Δ) ≤ φ(2k+1) · VfB ν_Δ (yFI Δ)`

with `ν_Δ = nuFI Δ = g̃ · hSieveC g̃ (1/log Δ)`, `yFI Δ = ⌈Δ^{1/20}⌉₊ + 1` and a `φ` whose odd
values are summable.  The route is:

* `chainMassTnB` — the purely combinatorial core: for odd `n = 2k+1` every chain counted by
  `TnB B ν n D y` has all its primes above the threshold `levC B D k = max ⌈D^{levB B k}⌉₊ 2`
  (`levB B k = ρ^k/(B+1)`, `ρ = (B-1)/(B+1)`), whence the weighted chain sum is dominated by
  `VfB ν (levC B D k) · (windowMass ν (levC B D k) y)^{2k+1}/(2k+1)!`;
* `nuFI_LinNormKup` and the two consequences of the windowed norm `LinNormKup`
  (`VfB_ratio_le_LinNormKup`, `sum_nu_le_LinNormKup`) convert this into
  `VfB ν y · K · U^2 · (log K + 2 log U)^{2k+1}/(2k+1)!` with `U = log ⌈y⌉₊ / log (levC B D k)`;
* `U ≤ 2·ρ^{-k}` turns the latter into the explicit term `phiTerm K k`, and `phiSeries_bound`
  shows that `∑_k phiTerm K k` converges.

Everything here is definitions and elementary facts (no `sorry`, no `axiom`).
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.LamPlusBLayerDefs
import Submission.Work.FIChain.OddLayersMajorantDefs
import Submission.Work.FIChain.sharpNorm_two_FIgtil

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `Ω₂`-norm constant of the FI sieve density, from `sharpNorm_two_FIgtil` (made `≥ 2`). -/
def KFI : ℝ := max (Classical.choose sharpNorm_two_FIgtil) 2

/-- The §6 sieve density of the FI sequence at level `Δ`: `ν_Δ = g̃ · hSieveC g̃ (1/log Δ)`. -/
def nuFI (Δ : ℕ) : ℕ → ℝ :=
  fun n => Submission.ASP.FIgtil n * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) n

/-- The layer range `y = ⌈Δ^{1/20}⌉₊ + 1`. -/
def yFI (Δ : ℕ) : ℝ := ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ : ℕ) : ℝ) + 1

/-- The `B`-delay window threshold at odd layer `2k+1`: every prime of a chain counted by
`TnB B ν (2k+1) D y` is at least `levC B D k`. -/
def levC (B : ℝ) (D : ℝ) (k : ℕ) : ℕ := max ⌈D ^ levB B k⌉₊ 2

/-- The `ν`-mass of the window `[c, y)` of primes. -/
def windowMass (ν : ℕ → ℝ) (c : ℕ) (y : ℝ) : ℝ :=
  ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => c ≤ p), ν p

/-- The explicit per-layer majorant term `K·(2ρ^{-k})²·(log K + 2 log(2ρ^{-k}))^{2k+1}/(2k+1)!`
at `ρ = 9/10`. -/
def phiTerm (K : ℝ) (k : ℕ) : ℝ :=
  K * (2 * (10 / 9 : ℝ) ^ k) ^ 2
    * (Real.log K + 2 * Real.log (2 * (10 / 9 : ℝ) ^ k)) ^ (2 * k + 1)
    / ((2 * k + 1).factorial : ℝ)

/-- The majorant sequence `φ` of the per-layer bound: `φ n = phiTerm K (n/2)` for odd `n`, `0` for
even `n`. -/
def phiFI (K : ℝ) : ℕ → ℝ := fun n => if Odd n then phiTerm K (n / 2) else 0

lemma KFI_pos : 0 < KFI := lt_of_lt_of_le (by norm_num) (le_max_right _ _)

lemma KFI_one_le : 1 ≤ KFI := le_trans (by norm_num) (le_max_right _ _)

/-! ## Unfolding the layer condition -/

/-- At an odd level `m ≠ 1` the layer condition is just `p^{B+1} ≤ D`. -/
lemma TcondB_odd {B D : ℝ} {m : ℕ} (hm1 : m ≠ 1) (hm2 : 2 ≤ m) (hmo : Odd m) (p : ℕ) :
    TcondB B m D p ↔ (p : ℝ) ^ (B + 1) ≤ D := by
  constructor
  · intro h; exact h.2 hm2 hmo
  · intro h; exact ⟨fun h1 => absurd h1 hm1, fun _ _ => h⟩

/-- At an even level `m ≠ 1` the layer condition is vacuous. -/
lemma TcondB_even {B D : ℝ} {m : ℕ} (hm1 : m ≠ 1) (hme : Even m) (p : ℕ) :
    TcondB B m D p :=
  ⟨fun h1 => absurd h1 hm1, fun _ hmo => by
    rcases hme with ⟨r, hr⟩
    rcases hmo with ⟨k, hk⟩
    omega⟩

end

end Work.FIChain
