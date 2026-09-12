import Submission.Work.OuterSqueeze

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The Unc diagonal at degenerate heights (GREEN: core theorem)

An UNCOVERED-degenerate sequence `uₙ → y₀` (with `y₀` any degenerate flat
height) has leaf slopes `leafSlope(uₙ) → leafSlope(y₀)`.

Method (the diagonal): at each Unc point `uₙ` brick (B) supplies the
below-sequence `bₙ : ℕ → ℝ` of U-heights (`uHeightBelowSeq`),
`bₙ k → uₙ`, whose slopes converge to `degenerateSlope(uₙ) =
leafSlope(uₙ)`.  For each `n` pick an index `kₙ` (the max of the two
`ε = 1/(n+1)` witnesses) so that the diagonal `zₙ := bₙ kₙ` satisfies
`|zₙ − uₙ| < 1/(n+1)` AND `|leafSlope zₙ − leafSlope uₙ| < 1/(n+1)`.
Then `zₙ → y₀` (U-heights), so the U-limit machinery at `y₀` gives
`leafSlope zₙ → leafSlope y₀`; combined with
`|leafSlope uₙ − leafSlope zₙ| → 0` this is `leafSlope uₙ → leafSlope y₀`.

* `leafSlope_tendsto_uncovered` — the core (takes the U-limit property at
  `y₀` as a hypothesis);
* `leafSlope_tendsto_uncovered_of_covered` — target `y₀` COVERED
  (`leafSlope_tendsto_uHeight_of_covered`);
* `leafSlope_tendsto_uncovered_of_uncovered` — target `y₀` UNCOVERED
  (`leafSlope_tendsto_uHeight_of_uncovered`).

Build: `lake build Submission.Work.UncDiagonal` rc=0, zero sorry.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- **The Unc diagonal**: an uncovered-degenerate sequence converging to a
height `y₀` at which every U-height sequence has the leaf-slope limit
`leafSlope y₀` has leaf slopes converging to `leafSlope y₀`. -/
theorem leafSlope_tendsto_uncovered {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} {u : ℕ → ℝ}
    (huF : ∀ n : ℕ, u n ∈ FlatHeight a f)
    (huni : ∀ n : ℕ, ¬ IsFlatInterior f (centrePoint (u n)))
    (huunc : ∀ n : ℕ, ¬ CoveredHeight (f := f) (u n))
    (hu : Tendsto u atTop (𝓝 y₀))
    (hy0lim : ∀ {w : ℕ → ℝ}, (∀ n : ℕ, w n ∈ UHeight a f) →
      Tendsto w atTop (𝓝 y₀) →
        Tendsto (fun n : ℕ => leafSlope hf ha (w n)) atTop (𝓝 (leafSlope hf ha y₀))) :
    Tendsto (fun n : ℕ => leafSlope hf ha (u n)) atTop (𝓝 (leafSlope hf ha y₀)) := by
  let b : ℕ → ℕ → ℝ := fun n k => uHeightBelowSeq hf ha (huF n) (huni n) (huunc n) k
  let kw : ℕ → ℕ := fun n => Classical.choose ((Metric.tendsto_atTop.mp
    (uHeightBelowSeq_tendsto hf ha (huF n) (huni n) (huunc n))) (1 / (n + 1)) (by positivity))
  let ks : ℕ → ℕ := fun n => Classical.choose ((Metric.tendsto_atTop.mp
    (degenerateSlope_tendsto hf ha (huF n) (huni n) (huunc n))) (1 / (n + 1)) (by positivity))
  let k : ℕ → ℕ := fun n => max (kw n) (ks n)
  let z : ℕ → ℝ := fun n => b n (k n)
  have hzU : ∀ n : ℕ, z n ∈ UHeight a f := by
    intro n
    change uHeightBelowSeq hf ha (huF n) (huni n) (huunc n) (k n) ∈ UHeight a f
    exact uHeightBelowSeq_mem hf ha (huF n) (huni n) (huunc n) (k n)
  have hzw : ∀ n : ℕ, |z n - u n| < 1 / (n + 1) := by
    intro n
    have hkw : kw n ≤ k n := by dsimp [k]; exact le_max_left _ _
    have hw := (Classical.choose_spec ((Metric.tendsto_atTop.mp
        (uHeightBelowSeq_tendsto hf ha (huF n) (huni n) (huunc n))) (1 / (n + 1)) (by positivity)))
      (k n) hkw
    change |uHeightBelowSeq hf ha (huF n) (huni n) (huunc n) (k n) - u n| < 1 / (n + 1)
    simpa [Real.dist_eq] using hw
  have hzs : ∀ n : ℕ,
      |slopeAtHeight hf ha (hzU n) - degenerateSlope hf ha (huF n) (huni n) (huunc n)| < 1 / (n + 1) := by
    intro n
    have hks : ks n ≤ k n := by dsimp [k]; exact le_max_right _ _
    have hs := (Classical.choose_spec ((Metric.tendsto_atTop.mp
        (degenerateSlope_tendsto hf ha (huF n) (huni n) (huunc n))) (1 / (n + 1)) (by positivity)))
      (k n) hks
    change |slopeAtHeight hf ha (uHeightBelowSeq_mem hf ha (huF n) (huni n) (huunc n) (k n)) -
        degenerateSlope hf ha (huF n) (huni n) (huunc n)| < 1 / (n + 1)
    simpa [Real.dist_eq] using hs
  have hzminus : Tendsto (fun n : ℕ => z n - u n) atTop (𝓝 (0 : ℝ)) := by
    have hle : ∀ n : ℕ, |z n - u n| ≤ 1 / (n + 1) := fun n => le_of_lt (hzw n)
    have habs : Tendsto (fun n : ℕ => |z n - u n|) atTop (𝓝 0) :=
      squeeze_zero (fun n => abs_nonneg (z n - u n)) hle tendsto_one_div_add_atTop_nhds_zero_nat
    exact (tendsto_iff_dist_tendsto_zero.mpr (by simpa [Real.dist_eq] using habs))
  have hz₀ : Tendsto z atTop (𝓝 y₀) := by
    have hsum : Tendsto (fun n : ℕ => u n + (z n - u n)) atTop (𝓝 y₀) := by
      have h' := hu.add hzminus
      simpa using h'
    have hfun : (fun n : ℕ => u n + (z n - u n)) = z := by
      funext n
      abel
    rwa [hfun] at hsum
  have hsl : Tendsto (fun n : ℕ => leafSlope hf ha (z n)) atTop
      (𝓝 (leafSlope hf ha y₀)) := hy0lim hzU hz₀
  have hconst : Tendsto (fun _ : ℕ => leafSlope hf ha y₀) atTop (𝓝 (leafSlope hf ha y₀)) := tendsto_const_nhds
  have hslsub : Tendsto (fun n : ℕ => leafSlope hf ha (z n) - leafSlope hf ha y₀) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hsl.sub hconst)
  -- |leafSlope uₙ − leafSlope zₙ| ≤ 1/(n+1)
  have hclose : ∀ n : ℕ, |leafSlope hf ha (u n) - leafSlope hf ha (z n)| ≤ 1 / (n + 1) := by
    intro n
    have hl₁ : leafSlope hf ha (u n) = degenerateSlope hf ha (huF n) (huni n) (huunc n) :=
      leafSlope_eq_degenerateSlope hf ha (huF n) (huni n) (huunc n)
    have hl₂ : leafSlope hf ha (z n) = slopeAtHeight hf ha (hzU n) :=
      leafSlope_eq_slopeAtHeight hf ha (hzU n)
    calc
      |leafSlope hf ha (u n) - leafSlope hf ha (z n)| =
          |slopeAtHeight hf ha (hzU n) - degenerateSlope hf ha (huF n) (huni n) (huunc n)| := by
            rw [hl₁, hl₂]
            rw [abs_sub_comm]
      _ ≤ 1 / (n + 1) := le_of_lt (hzs n)
  have hclose₀ : Tendsto (fun n : ℕ => leafSlope hf ha (u n) - leafSlope hf ha (z n)) atTop (𝓝 (0 : ℝ)) := by
    have habs : Tendsto (fun n : ℕ => |leafSlope hf ha (u n) - leafSlope hf ha (z n)|) atTop (𝓝 0) :=
      squeeze_zero (fun n => abs_nonneg (leafSlope hf ha (u n) - leafSlope hf ha (z n))) hclose
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact (tendsto_iff_dist_tendsto_zero.mpr (by simpa [Real.dist_eq] using habs))
  have hdiag : Tendsto (fun n : ℕ =>
      (leafSlope hf ha (u n) - leafSlope hf ha (z n)) + (leafSlope hf ha (z n) - leafSlope hf ha y₀))
      atTop (𝓝 (0 : ℝ)) := by simpa using (hclose₀.add hslsub)
  have hfun2 : (fun n : ℕ =>
      (leafSlope hf ha (u n) - leafSlope hf ha (z n)) + (leafSlope hf ha (z n) - leafSlope hf ha y₀)) =
      fun n : ℕ => leafSlope hf ha (u n) - leafSlope hf ha y₀ := by
    funext n
    ring
  have htarget : Tendsto (fun n : ℕ => leafSlope hf ha (u n) - leafSlope hf ha y₀) atTop (𝓝 (0 : ℝ)) := by
    rwa [hfun2] at hdiag
  exact (tendsto_sub_nhds_zero_iff.mp htarget)

/-- The Unc diagonal toward a COVERED height. -/
theorem leafSlope_tendsto_uncovered_of_covered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ} (hc : CoveredHeight (f := f) y₀)
    {u : ℕ → ℝ} (huF : ∀ n : ℕ, u n ∈ FlatHeight a f)
    (huni : ∀ n : ℕ, ¬ IsFlatInterior f (centrePoint (u n)))
    (huunc : ∀ n : ℕ, ¬ CoveredHeight (f := f) (u n))
    (hu : Tendsto u atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => leafSlope hf ha (u n)) atTop (𝓝 (leafSlope hf ha y₀)) := by
  refine leafSlope_tendsto_uncovered hf ha huF huni huunc hu ?_
  intro w hwU hw
  exact leafSlope_tendsto_uHeight_of_covered hf ha hc hwU hw

/-- The Unc diagonal toward an UNCOVERED height. -/
theorem leafSlope_tendsto_uncovered_of_uncovered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ}
    (hy₀F : y₀ ∈ FlatHeight a f) (hni₀ : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc₀ : ¬ CoveredHeight (f := f) y₀)
    {u : ℕ → ℝ} (huF : ∀ n : ℕ, u n ∈ FlatHeight a f)
    (huni : ∀ n : ℕ, ¬ IsFlatInterior f (centrePoint (u n)))
    (huunc : ∀ n : ℕ, ¬ CoveredHeight (f := f) (u n))
    (hu : Tendsto u atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => leafSlope hf ha (u n)) atTop (𝓝 (leafSlope hf ha y₀)) := by
  refine leafSlope_tendsto_uncovered hf ha huF huni huunc hu ?_
  intro w hwU hw
  exact leafSlope_tendsto_uHeight_of_uncovered hf ha hy₀F hni₀ hunc₀ hwU hw

end Submission
