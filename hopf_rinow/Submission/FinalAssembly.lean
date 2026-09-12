import ChallengeDeps
import Submission.Metric
import Submission.MetricLimit
import Submission.MetricCompleteCompact

/-!
# Verified reduction of Hopf–Rinow to three clean geometric interfaces

This module proves the *entire* metric assembly: both directions of the challenge
equivalence are derived, using only the metric facts already established, from three
statements about the manifold that encode the local Riemannian geodesic theory:

* `GeoRightExt M` — every locally linear path with a limit at its right endpoint extends
  to a locally linear path on the whole half line `(a, ∞)` (same speed);
* `GeoLeftExt  M` — the mirror statement on `(−∞, b)`;
* `ballsCompact_of_geodesicComplete` — `IsGeodesicallyComplete M` implies all closed
  metric balls are compact (the Hopf–Rinow compactness lemma).

None of the three requires Riemannian structure in its statement: each is a theorem of
Riemannian geometry that is proved elsewhere from the smooth hypotheses of the challenge.
-/

open scoped ENNReal Topology
open EMetric
open Set Filter

namespace Submission

open LeanEval.Geometry

namespace FinalAssembly

variable {M : Type*} [EMetricSpace M]

/-- One-sided "right locally linear" curve: locally linear at every `t₀ > a` with windows
unclipped on the right (pairs are only required to stay above `a`). -/
def IsLocLinRight (a : ℝ) (c : NNReal) (γ : ℝ → M) : Prop :=
  ∀ t₀, a < t₀ → ∃ δ > (0 : ℝ), ∀ s t : ℝ,
    a < s → a < t → |s - t₀| < δ → |t - t₀| < δ →
    edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s|

/-- One-sided "left locally linear" curve: locally linear at every `t₀ < b` with windows
unclipped on the left (pairs are only required to stay below `b`). -/
def IsLocLinLeft (b : ℝ) (c : NNReal) (γ : ℝ → M) : Prop :=
  ∀ t₀, t₀ < b → ∃ δ > (0 : ℝ), ∀ s t : ℝ,
    s < b → t < b → |s - t₀| < δ → |t - t₀| < δ →
    edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s|

/-- Geometric interface (direction A, right side): a locally linear path on `(a,b)` that has a
limit at `b⁻` extends to a right-locally-linear path on the half-line `(a,∞)`, agreeing with the
original path on `(a,b)`. -/
def GeoRightExt (M : Type*) [EMetricSpace M] : Prop :=
  ∀ (a b : ℝ) (c : NNReal) (γ : ℝ → M), a < b →
    Metric.IsLocLinear a b c γ →
    (∃ p : M, Tendsto γ (𝓝[Iio b] b) (𝓝 p)) →
    ∃ γR : ℝ → M, (∀ t ∈ Ioo a b, γR t = γ t) ∧ IsLocLinRight a c γR

/-- Geometric interface (direction A, left side): mirror statement at `a⁺`. -/
def GeoLeftExt (M : Type*) [EMetricSpace M] : Prop :=
  ∀ (a b : ℝ) (c : NNReal) (γ : ℝ → M), a < b →
    Metric.IsLocLinear a b c γ →
    (∃ p : M, Tendsto γ (𝓝[Ioi a] a) (𝓝 p)) →
    ∃ γL : ℝ → M, (∀ t ∈ Ioo a b, γL t = γ t) ∧ IsLocLinLeft b c γL

section DirectionA

/-- Direction A of Hopf–Rinow, modulo the two geometric interfaces: metric completeness implies
geodesic completeness. -/
theorem directionA (hc : CompleteSpace M) (hGR : GeoRightExt M) (hGL : GeoLeftExt M) :
    IsGeodesicallyComplete M := by
  letI : CompleteSpace M := hc
  intro a b γ hab ⟨c, hγ⟩
  -- limit of γ at b⁻ (complete space)
  rcases Metric.IsLocLinear.exists_tendsto_nhdsWithin_Iio hγ hab with ⟨pR, hpR⟩
  rcases hGR a b c γ hab hγ ⟨pR, hpR⟩ with ⟨γR, hEqR, hLinR⟩
  -- pick B := b + 1, get local linearity of γR on (a,B) and its limit at a⁺
  let B : ℝ := b + 1
  have hB : a < B := by dsimp [B]; linarith
  have hγR_LL : Metric.IsLocLinear a B c γR := by
    intro t₀ ht₀
    rcases hLinR t₀ ht₀.1 with ⟨δ, hδ, hwin⟩
    refine ⟨δ, hδ, ?_⟩
    intro s t hs ht
    have hs1 : a < s := lt_of_le_of_lt (le_max_left a (t₀ - δ)) hs.1
    have ht1 : a < t := lt_of_le_of_lt (le_max_left a (t₀ - δ)) ht.1
    have hsδ : |s - t₀| < δ := by
      have h1 : t₀ - δ < s := lt_of_le_of_lt (le_max_right a (t₀ - δ)) hs.1
      have h2 : s < t₀ + δ := lt_of_lt_of_le hs.2 (min_le_right B (t₀ + δ))
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have htδ : |t - t₀| < δ := by
      have h1 : t₀ - δ < t := lt_of_le_of_lt (le_max_right a (t₀ - δ)) ht.1
      have h2 : t < t₀ + δ := lt_of_lt_of_le ht.2 (min_le_right B (t₀ + δ))
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    exact hwin s t hs1 ht1 hsδ htδ
  rcases Metric.IsLocLinear.exists_tendsto_nhdsWithin_Ioi hγR_LL hB with ⟨pL, hpL⟩
  rcases hGL a B c γR hB hγR_LL ⟨pL, hpL⟩ with ⟨γL, hEqL, hLinL⟩
  -- splice: γL on (−∞,B), γR on [B,∞)
  let γext : ℝ → M := fun t => if t < B then γL t else γR t
  have hγext_eqR {t : ℝ} (ht : a < t) : γext t = γR t := by
    dsimp [γext]
    by_cases htB : t < B
    · have htI : t ∈ Ioo a B := ⟨ht, htB⟩
      rw [if_pos htB, hEqL t htI]
    · rw [if_neg htB]
  refine ⟨γext, ?_, ?_⟩
  · -- γext is a global geodesic
    refine ⟨c, ?_⟩
    intro t₀
    by_cases ht₀a : a < t₀
    · -- use right-locality of γR; window staying above a
      rcases hLinR t₀ ht₀a with ⟨δ, hδ, hwinR⟩
      let δ0 : ℝ := min δ (t₀ - a)
      have hδ0 : 0 < δ0 := lt_min hδ (sub_pos.mpr ht₀a)
      refine ⟨δ0, hδ0, ?_⟩
      intro s t hs ht
      have hsa_le : a ≤ t₀ - δ0 := by
        have : δ0 ≤ t₀ - a := min_le_right δ (t₀ - a)
        linarith
      have hs_a : a < s := by
        have h1 : |t₀ - s| < δ0 := by simpa [abs_sub_comm] using hs
        have h2 : t₀ - s < δ0 := lt_of_le_of_lt (le_abs_self (t₀ - s)) h1
        have h3 : t₀ - δ0 < s := by linarith
        linarith
      have ht_a : a < t := by
        have h1 : |t₀ - t| < δ0 := by simpa [abs_sub_comm] using ht
        have h2 : t₀ - t < δ0 := lt_of_le_of_lt (le_abs_self (t₀ - t)) h1
        have h3 : t₀ - δ0 < t := by linarith
        linarith
      have hsδR : |s - t₀| < δ := lt_of_lt_of_le hs (min_le_left δ (t₀ - a))
      have htδR : |t - t₀| < δ := lt_of_lt_of_le ht (min_le_left δ (t₀ - a))
      rw [hγext_eqR hs_a, hγext_eqR ht_a]
      exact hwinR s t hs_a ht_a hsδR htδR
    · -- use left-locality of γL; window staying below B
      have ht₀B : t₀ < B := by dsimp [B]; linarith
      rcases hLinL t₀ ht₀B with ⟨δ, hδ, hwinL⟩
      let δ0 : ℝ := min δ (B - t₀)
      have hδ0 : 0 < δ0 := lt_min hδ (sub_pos.mpr ht₀B)
      refine ⟨δ0, hδ0, ?_⟩
      intro s t hs ht
      have hB_le : t₀ + δ0 ≤ B := by
        have : δ0 ≤ B - t₀ := min_le_right δ (B - t₀)
        linarith
      have hs_B : s < B := by
        have h1 : s - t₀ ≤ |s - t₀| := le_abs_self (s - t₀)
        have h2 : |s - t₀| < δ0 := hs
        linarith [hB_le]
      have ht_B : t < B := by
        have h1 : t - t₀ ≤ |t - t₀| := le_abs_self (t - t₀)
        have h2 : |t - t₀| < δ0 := ht
        linarith [hB_le]
      have hsδL : |s - t₀| < δ := lt_of_lt_of_le hs (min_le_left δ (B - t₀))
      have htδL : |t - t₀| < δ := lt_of_lt_of_le ht (min_le_left δ (B - t₀))
      have h1 : γext s = γL s := by
        dsimp [γext]; rw [if_pos hs_B]
      have h2 : γext t = γL t := by
        dsimp [γext]; rw [if_pos ht_B]
      rw [h1, h2]
      exact hwinL s t hs_B ht_B hsδL htδL
  · -- agreement with γ on (a,b)
    intro t ht
    have htB : t < B := by dsimp [B]; linarith [ht.2]
    have h1 : γext t = γL t := by dsimp [γext]; rw [if_pos htB]
    have h2 : γL t = γR t := hEqL t ⟨ht.1, htB⟩
    have h3 : γR t = γ t := hEqR t ht
    rw [h1, h2, h3]

end DirectionA

section

/-- Closed (finite-radius) metric balls around every point are compact. -/
def BallsCompactFinite (M : Type*) [EMetricSpace M] : Prop :=
  ∀ p : M, ∀ R : ℝ≥0∞, R < ⊤ → IsCompact (closedBall p R)

/-- Direction B of Hopf–Rinow, modulo the compactness lemma: geodesic completeness implies that
closed (finite-radius) metric balls are compact, and compact balls give completeness.
(The metric completeness lemma `Metric.complete_of_closedBalls_compact` needs only the ball of
radius 1, so finite radii suffice.) -/
theorem directionB (hB : IsGeodesicallyComplete M → BallsCompactFinite M) :
    IsGeodesicallyComplete M → CompleteSpace M := by
  intro hgc
  -- Cauchy sequences are eventually in a compact closed ball of radius 1.
  refine EMetric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  rcases EMetric.cauchySeq_iff.mp hu (1 : ℝ≥0∞) (by norm_num) with ⟨N, hN⟩
  have hmem : ∀ᶠ n in atTop, u n ∈ closedBall (u N) (1 : ℝ≥0∞) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (Metric.mem_closedEBall).2 (le_of_lt (hN n hn N (le_rfl)))
  have hmap : Filter.map u atTop ≤ 𝓟 (closedBall (u N) (1 : ℝ≥0∞)) := by
    rwa [le_principal_iff, mem_map]
  have hone : (1 : ℝ≥0∞) < ⊤ := by norm_num
  rcases (hB hgc (u N) (1 : ℝ≥0∞) hone).exists_mapClusterPt (f := atTop) (u := u) hmap with
    ⟨x, -, hxc⟩
  exact ⟨x, le_nhds_of_cauchy_adhp hu hxc⟩

end

/-- The full Hopf–Rinow equivalence, modulo the three geometric interfaces.

The direction-A interfaces `GeoRightExt`/`GeoLeftExt` are only true under metric completeness
(they assert that geodesics extend indefinitely, which fails e.g. on the bounded open interval
(0,1)), so they are supplied as functions of the completeness hypothesis. -/
theorem hopf_rinow_core (hGR : CompleteSpace M → GeoRightExt M)
    (hGL : CompleteSpace M → GeoLeftExt M)
    (hB : IsGeodesicallyComplete M → BallsCompactFinite M) :
    IsGeodesicallyComplete M ↔ CompleteSpace M := by
  constructor
  · exact directionB hB
  · intro hc
    exact directionA hc (hGR hc) (hGL hc)

end FinalAssembly

end Submission
