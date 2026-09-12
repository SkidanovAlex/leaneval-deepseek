import ChallengeDeps
import Submission.Metric
import Submission.MetricCont
import Mathlib

open scoped ENNReal Topology
open Set EMetric

namespace Submission

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

/-! Shared metric core for Direction B (geodesic completeness ⇒ compact balls).

Definitions of `mnorm` (chart metric norm), `UnitGeo` (global unit-speed locally linear
curves), `Realises` (distance-realising unit geodesic segments) and their basic lemmas.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- metric norm w.r.t. the chart bilinear form `ge0`. -/
noncomputable def mnorm (ge0 : E →L[ℝ] E →L[ℝ] ℝ) (v : E) : ℝ := Real.sqrt (ge0 v v)

lemma mnorm_nonneg (ge0 : E →L[ℝ] E →L[ℝ] ℝ) (v : E) : 0 ≤ mnorm ge0 v := Real.sqrt_nonneg _

/-- A global unit-speed locally linear curve on all of `ℝ`. -/
def UnitGeo {M : Type*} [EMetricSpace M] (γ : ℝ → M) : Prop :=
  ∀ B : ℝ, 0 < B → Metric.IsLocLinear (-B) B (1 : NNReal) γ

namespace UnitGeo

variable {M : Type*} [EMetricSpace M]
variable {γ : ℝ → M}

private lemma neg_abs_le_self (s : ℝ) : -|s| ≤ s := by
  by_cases hsgn : 0 ≤ s
  · rw [abs_of_nonneg hsgn]; linarith
  · have hsneg : s < 0 := lt_of_not_ge hsgn
    rw [abs_of_neg hsneg]; linarith

private lemma mem_Ioo_abs {B s : ℝ} (hB : 0 < B) (hs : |s| < B) : s ∈ Ioo (-B) B := by
  constructor
  · have h1 : -B < -|s| := by linarith
    exact lt_of_lt_of_le h1 (neg_abs_le_self s)
  · have h1 : |s| < B := hs
    exact lt_of_le_of_lt (le_abs_self s) h1

/-- A unit geodesic is locally linear on every bounded interval. -/
lemma isLocLinear (hγ : UnitGeo γ) : ∀ (a b : ℝ), a < b → Metric.IsLocLinear a b (1 : NNReal) γ := by
  intro a b hab
  have hB : 0 < max (-a) b := by
    by_cases ha : 0 < -a
    · exact lt_of_lt_of_le ha (le_max_left (-a) b)
    · have hnot : -a ≤ 0 := le_of_not_gt ha
      have hapos : 0 ≤ a := by linarith
      have hbpos : 0 < b := lt_of_le_of_lt hapos hab
      exact lt_of_lt_of_le hbpos (le_max_right (-a) b)
  have h1 : -max (-a) b ≤ a := by
    have hx : -a ≤ max (-a) b := le_max_left (-a) b
    linarith
  have h2 : b ≤ max (-a) b := le_max_right (-a) b
  exact Metric.IsLocLinear.restrict (hγ (max (-a) b) hB) h1 h2

/-- A unit geodesic is continuous. -/
lemma continuous (hγ : UnitGeo γ) : Continuous γ := by
  refine continuous_iff_continuousAt.mpr ?_
  intro t₀
  have hll := isLocLinear hγ (t₀ - 1) (t₀ + 1) (by linarith)
  exact Metric.IsLocLinear.continuousAt hll (by constructor <;> linarith)

/-- Upper Lipschitz bound: `edist (γ s) (γ t) ≤ |t-s|`. -/
lemma lipschitz_le (hγ : UnitGeo γ) {s t : ℝ} (hst : s ≤ t) :
    edist (γ s) (γ t) ≤ ENNReal.ofReal (t - s) := by
  let B : ℝ := |s| + |t| + 1
  have hB : 0 < B := by
    dsimp [B]
    have h1 : (0 : ℝ) ≤ |s| := abs_nonneg s
    have h2 : (0 : ℝ) ≤ |t| := abs_nonneg t
    linarith
  have hs_lt : |s| < B := by dsimp [B]; linarith [abs_nonneg s, abs_nonneg t]
  have ht_lt : |t| < B := by dsimp [B]; linarith [abs_nonneg s, abs_nonneg t]
  have hs : s ∈ Ioo (-B) B := mem_Ioo_abs hB hs_lt
  have ht : t ∈ Ioo (-B) B := mem_Ioo_abs hB ht_lt
  have hll : Metric.IsLocLinear (-B) B (1 : NNReal) γ := isLocLinear hγ (-B) B (by linarith [hB])
  have hb := Metric.IsLocLinear.edist_le_of_le hll hs ht hst
  simpa using hb

lemma edist_zero_le (hγ : UnitGeo γ) {t : ℝ} (ht : 0 ≤ t) :
    edist (γ 0) (γ t) ≤ ENNReal.ofReal t := by
  simpa using lipschitz_le hγ ht

end UnitGeo

/-- A **realising** unit geodesic from `p` up to time `L`: `γ 0 = p` and
`edist p (γ t) = t` for all `0 ≤ t ≤ L`. -/
def Realises {M : Type*} [EMetricSpace M] (γ : ℝ → M) (p : M) (L : ℝ) : Prop :=
  UnitGeo γ ∧ γ 0 = p ∧ ∀ t : ℝ, 0 ≤ t → t ≤ L → edist p (γ t) = ENNReal.ofReal t

namespace Realises

variable {M : Type*} [EMetricSpace M]
variable {γ : ℝ → M} {p : M} {L : ℝ}

lemma isUnitGeo (h : Realises γ p L) : UnitGeo γ := h.1
lemma start (h : Realises γ p L) : γ 0 = p := h.2.1
lemma dist (h : Realises γ p L) {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) :
    edist p (γ t) = ENNReal.ofReal t := h.2.2 t ht0 htL

/-- truncation. -/
lemma truncate (h : Realises γ p L) {L' : ℝ} (hL' : L' ≤ L) : Realises γ p L' := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro t ht0 ht
  exact h.2.2 t ht0 (le_trans ht hL')

end Realises

end Submission
