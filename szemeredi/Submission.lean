import ChallengeDeps
import Submission.Szemeredi.Basic
import Submission.Szemeredi.Roth
import Submission.Szemeredi.Waerden
import Submission.Szemeredi.CornersToAP
import Submission.Szemeredi.CornersInstances
import Submission.Szemeredi.CornersRemovalD
import Submission.Szemeredi.Removal.Part2

open LeanEval.Combinatorics
open scoped BigOperators
open Filter Finset

namespace Submission

open Szemeredi

/-- The upper density used in the challenge equals the `limsup` of the initial-segment
densities `|A ∩ {0,…,n}| / (n+1)` (counted by cardinality rather than by a real indicator). -/
lemma upperDensity_eq_limsup_density (A : Set ℕ) :
    upperDensity A = Filter.limsup (Szemeredi.density A) Filter.atTop := by
  have hpoint :
      (fun n : ℕ => (∑ k ∈ Finset.range (n + 1),
          A.indicator (fun _ => (1 : ℝ)) k) / (n + 1)) = Szemeredi.density A := by
    funext n
    unfold Szemeredi.density
    congr 1
    rw [← Szemeredi.countInd_eq_countUpTo A n]
    rfl
  unfold upperDensity
  rw [hpoint]

/-- The challenge's positive-upper-density hypothesis is exactly `PositiveUpperDensity`. -/
lemma positiveUpperDensity_iff (A : Set ℕ) :
    Szemeredi.PositiveUpperDensity A ↔ 0 < upperDensity A := by
  unfold Szemeredi.PositiveUpperDensity
  rw [upperDensity_eq_limsup_density]

/-- The challenge's `ContainsArbitraryAPs` is pointwise `HasAP`. -/
lemma containsArbitraryAPs_iff (A : Set ℕ) :
    ContainsArbitraryAPs A ↔ ∀ k : ℕ, Szemeredi.HasAP A k := by
  unfold ContainsArbitraryAPs Szemeredi.HasAP
  rfl

/-- **Szemerédi's theorem**, derived from the finite version for every length and density. -/
theorem szemeredi_of_finite
    (hfin : ∀ (k : ℕ) (δ : ℝ), 0 < δ → Szemeredi.FiniteSzemeredi k δ)
    (A : Set ℕ) (h : 0 < upperDensity A) : ContainsArbitraryAPs A := by
  have hd : Szemeredi.PositiveUpperDensity A := (positiveUpperDensity_iff A).mpr h
  have hAP : ∀ k : ℕ, Szemeredi.HasAP A k := Szemeredi.infinite_ap_of_finite hfin hd
  exact (containsArbitraryAPs_iff A).mpr hAP

/-- The finite form of Szemerédi's theorem for every length `k` and density `δ > 0`.

This is the content of Szemerédi's paper: for every `k` and `δ > 0` there is an `N₀`
such that every `δ`-dense subset of `{0, …, N-1}` (`N ≥ N₀`) contains a nontrivial
`k`-term arithmetic progression.

The cases `k ≤ 3` are fully proved in this development (`k = 3` is Roth's theorem,
proved here from mathlib's `roth_3ap_theorem_nat` as `Szemeredi.finiteSzemeredi_three`,
and `k = 0, 1, 2` are elementary).

The remaining open case `k ≥ 4` is the deep combinatorial core of Szemerédi's
theorem.  It is reduced, in `Szemeredi.CornersToAP`, to the **multidimensional
corners theorem** `Szemeredi.CornersFiniteD d ε` for cyclic groups in dimension
`d = k-1`: see `Szemeredi.finite_szemeredi_of_corners_allD` and
`szemeredi_of_corners_allD` below.  That reduction — which generalises the way
mathlib's `corners_theorem` (dimension two) implies Roth's theorem — is fully
proved here; `CornersFiniteD d` is the single open statement that remains. -/
theorem szemeredi_finite (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Szemeredi.FiniteSzemeredi k δ := by
  by_cases hk : k ≤ 3
  · interval_cases k
    · exact finiteSzemeredi_zero δ hδ
    · exact finiteSzemeredi_one δ hδ
    · exact finiteSzemeredi_two δ hδ
    · exact finiteSzemeredi_three δ hδ
  · push_neg at hk
    have hk2 : 2 ≤ k := by omega
    have hk1 : 1 ≤ k - 1 := by omega
    have hcor : Szemeredi.CornersFiniteD (k - 2 + 1) (δ / 4) := by
      have heq : k - 2 + 1 = k - 1 := by omega
      rw [heq]
      exact Szemeredi.cornersFiniteD_d
        (Szemeredi.simplexRemovalProgrammeD_of_main2 (k - 1) hk1) (δ / 4) (by positivity)
    have hfin := Szemeredi.finiteSzemeredi_of_cornersD (n := k - 2) hδ hcor
    simpa [Nat.sub_add_cancel hk2] using hfin

/-- **Szemerédi's theorem**: every subset of `ℕ` of positive upper density contains
arbitrarily long arithmetic progressions. -/
theorem szemeredi (A : Set ℕ) (h : 0 < upperDensity A) : ContainsArbitraryAPs A :=
  szemeredi_of_finite szemeredi_finite A h


/-- **Szemerédi's theorem from the multidimensional corners theorem.**

If the `d`-dimensional corners theorem over cyclic groups holds at every dimension
`d ≥ 1` and every density (the statement `Szemeredi.CornersFiniteD d ε`), then the
full Szemerédi theorem follows: every subset of `ℕ` of positive upper density
contains arbitrarily long arithmetic progressions.

This theorem is fully proved here; together with
`Szemeredi.finite_szemeredi_of_corners_allD` and
`Szemeredi.finiteSzemeredi_of_cornersD` (in `Submission/Szemeredi/CornersToAP.lean`)
it reduces the entire challenge to the single open statement
`∀ d ε, 0 < ε → Szemeredi.CornersFiniteD d ε`.  (For `d = 1` and `d = 2` that
statement is elementary (see `Szemeredi.cornersFiniteD_one`) or is mathlib's
`corners_theorem` (see `Szemeredi.cornersFiniteD_two`); for `d ≥ 3` it is the
deep multidimensional generalisation — equivalent in difficulty to Szemerédi's
theorem itself, and the natural target of the hypergraph regularity programme.) -/
theorem szemeredi_of_corners_allD
    (hcorn : ∀ (d : ℕ) (ε : ℝ), 0 < ε → Szemeredi.CornersFiniteD d ε)
    (A : Set ℕ) (h : 0 < upperDensity A) : ContainsArbitraryAPs A := by
  exact szemeredi_of_finite (Szemeredi.finite_szemeredi_of_corners_allD hcorn) A h


/-- **Szemerédi's theorem from the multidimensional simplex removal lemma.**

If the `d`-dimensional simplex removal lemma holds at every uniformity `d ≥ 1`
(the statement `Szemeredi.SimplexRemovalProgrammeD d`), then the full Szemerédi
theorem follows.  This is proved here by chaining the fully verified reductions
`Szemeredi.cornersFiniteD_d` (simplex removal in dimension `d` implies the
`d`-dimensional corners theorem, `Submission/Szemeredi/CornersRemovalD.lean`) with
`szemeredi_of_corners_allD` above.  Together these reduce the entire challenge to
the statement `∀ d ≥ 1, Szemeredi.SimplexRemovalProgrammeD d`, which is in turn
established (this development) from Tao's σ-algebra form of the hypergraph removal
lemma: see `Szemeredi.simplexRemovalProgrammeD_of_main2` in
`Submission/Szemeredi/Removal/Part2.lean`, which rests on
`Szemeredi.Removal.hypergraph_removal_complete`
(`Submission/Szemeredi/Removal/Main2.lean`).

(We only state the hypothesis for `d ≥ 1`: for `d = 0` the conclusion of
`SimplexRemovalProgrammeD` is false — a single `0`-uniform simplex would force
`c · |G| ≤ 1` for arbitrarily large `|G|` — while `CornersFiniteD 0` is elementary.) -/
theorem szemeredi_of_simplexRemovalD
    (hrem : ∀ d : ℕ, 1 ≤ d → Szemeredi.SimplexRemovalProgrammeD d)
    (A : Set ℕ) (h : 0 < upperDensity A) : ContainsArbitraryAPs A := by
  refine szemeredi_of_finite (fun k δ hδ => ?_) A h
  by_cases hk : k ≤ 3
  · interval_cases k
    · exact finiteSzemeredi_zero δ hδ
    · exact finiteSzemeredi_one δ hδ
    · exact finiteSzemeredi_two δ hδ
    · exact finiteSzemeredi_three δ hδ
  · push_neg at hk
    have hk2 : 2 ≤ k := by omega
    have hk1 : 1 ≤ k - 1 := by omega
    have hcor : Szemeredi.CornersFiniteD (k - 2 + 1) (δ / 4) := by
      have heq : k - 2 + 1 = k - 1 := by omega
      rw [heq]
      exact Szemeredi.cornersFiniteD_d (hrem (k - 1) hk1) (δ / 4) (by positivity)
    have hfin := Szemeredi.finiteSzemeredi_of_cornersD (n := k - 2) hδ hcor
    simpa [Nat.sub_add_cancel hk2] using hfin

end Submission
