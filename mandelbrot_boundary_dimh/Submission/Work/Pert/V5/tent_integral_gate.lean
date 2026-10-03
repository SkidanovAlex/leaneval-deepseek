import Mathlib
import Submission.Work.Pert.V5.Basics

/-!
# The tent integral gate

`Work.Pert.V5.mgA` and `Work.Pert.V5.mgB` are the two *marginals* of the gate `Qm Ξ α`
(`mgA z = Re z - Ξ + Re (1/α) + |Im z + Im (1/α)|` is the `b₁`-condition,
`mgB z = |Im z| - Ξ - Re z` the `b₂`-condition).  Along a horizontal line `x ↦ x + i s`
they are *affine*:

`mgA Ξ α (x + i s) = x + c`,   `mgB Ξ (x + i s) = -x + d`,

one of slope `1` and one of slope `-1`.  So the function whose reciprocal we integrate,

  `x ↦ min (mgA Ξ α (x + i s)) (mgB Ξ (x + i s))`,

is the *tent* `min (x + c, d - x)`: concave, peaking where the two affine functions cross.

The main theorem `tent_integral_gate` is the resulting integral bound.  On `[a,b]` the tent is
`≥ 2^10` by hypothesis, hence (writing `K = 2^10`, `L = b - a`)

`∫_a^b dx / tent x ≤ ∫_a^b (1/(K + (x - a)) + 1/(K + (b - x))) dx`
`                = log (1 + L/K) + log (1 + L/K) = 2 log (1 + L/K)`,

because on `[a,b]` the tent dominates `min (K + (x - a), K + (b - x))` (the increasing branch is
`≥` its value at `a`, the decreasing one `≥` its value at `b`) and
`1 / min(u,v) ≤ 1/u + 1/v`.  This is exactly the estimate used by the assembly of
`Phi_dev_gate_lin_v5`, where `1 / min (mgA, mgB)` is the reciprocal of the gate margin.

## Main results

* `mgA_line`, `mgB_line` : the two marginals along a horizontal line;
* `integral_inv_min_tent` : the tent integral bound for the explicit tent `min (K + x - a, K + b - x)`;
* `tent_integral_gate` : the gate statement, obtained by comparing the gate tent with
  `min (K + (x - a)) (K + (b - x))`.
-/

open Set Metric Filter MeasureTheory
open scoped Topology

namespace Work.Pert.V5

noncomputable section

/-- The `b₁`-marginal along a horizontal line is affine of slope `1`. -/
lemma mgA_line (Ξ : ℝ) (α : ℂ) (x s : ℝ) :
    mgA Ξ α (x + s * Complex.I) = x + (-Ξ + (1 / α).re + |s + (1 / α).im|) := by
  simp [mgA]
  ring

/-- The `b₂`-marginal along a horizontal line is affine of slope `-1`. -/
lemma mgB_line (Ξ : ℝ) (x s : ℝ) :
    mgB Ξ (x + s * Complex.I) = -x + (|s| - Ξ) := by
  simp [mgB]
  ring

/-- `∫_a^b dx / (K + x - a) = log (1 + (b-a)/K)` for `K > 0`, `a ≤ b`. -/
lemma integral_one_div_add_sub {K a b : ℝ} (hK : 0 < K) (hab : a ≤ b) :
    ∫ x in a..b, 1 / (K + (x - a)) = Real.log (1 + (b - a) / K) := by
  rw [show (fun x : ℝ => 1 / (K + (x - a)))
        = (fun x : ℝ => (fun y : ℝ => 1 / y) (x + (K - a))) by
      funext x; congr 1; ring]
  rw [intervalIntegral.integral_comp_add_right (fun y : ℝ => 1 / y) (K - a)]
  rw [show a + (K - a) = K by ring, show b + (K - a) = b - a + K by ring]
  rw [integral_one_div_of_pos (a := K) (b := b - a + K) hK (by linarith)]
  congr 1
  rw [add_div, div_self (ne_of_gt hK)]
  ring

/-- `∫_a^b dx / (K + b - x) = log (1 + (b-a)/K)` for `K > 0`, `a ≤ b`. -/
lemma integral_one_div_K_sub {K a b : ℝ} (hK : 0 < K) (hab : a ≤ b) :
    ∫ x in a..b, 1 / (K + (b - x)) = Real.log (1 + (b - a) / K) := by
  rw [show (fun x : ℝ => 1 / (K + (b - x)))
        = (fun x : ℝ => (fun y : ℝ => 1 / y) (b + K - x)) by
      funext x; congr 1; ring]
  rw [intervalIntegral.integral_comp_sub_left (fun y : ℝ => 1 / y) (b + K)]
  rw [show b + K - b = K by ring, show b + K - a = b - a + K by ring]
  rw [integral_one_div_of_pos (a := K) (b := b - a + K) hK (by linarith)]
  congr 1
  rw [add_div, div_self (ne_of_gt hK)]
  ring

/-- The tent `x ↦ min (K + x - a) (K + b - x)` is continuous. -/
lemma continuous_min_tent (K a b : ℝ) :
    Continuous (fun x : ℝ => min (K + (x - a)) (K + (b - x))) :=
  (continuous_const.add (continuous_id.sub continuous_const)).min
    (continuous_const.add (continuous_const.sub continuous_id))

/-- `1 / min (K + x - a) (K + b - x)` is interval integrable for `K > 0`, `a ≤ b`. -/
lemma intervalIntegrable_inv_min_tent {K a b : ℝ} (hK : 0 < K) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => 1 / min (K + (x - a)) (K + (b - x))) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div continuousOn_const (continuous_min_tent K a b).continuousOn ?_
  rw [uIcc_of_le hab]
  intro x hx
  exact ne_of_gt (lt_min (by linarith [hx.1]) (by linarith [hx.2]))

/-- **The tent integral bound for the explicit tent** `min (K + x - a) (K + b - x)`. -/
lemma integral_inv_min_tent {K a b : ℝ} (hK : 0 < K) (hab : a ≤ b) :
    ∫ x in a..b, 1 / min (K + (x - a)) (K + (b - x))
      ≤ 2 * Real.log (1 + (b - a) / K) := by
  have hpos : ∀ x ∈ Set.Icc a b, 0 < min (K + (x - a)) (K + (b - x)) :=
    fun x hx => lt_min (by linarith [hx.1]) (by linarith [hx.2])
  -- `1 / min u v ≤ 1 / u + 1 / v`
  have hpt : ∀ x ∈ Set.Icc a b, 1 / min (K + (x - a)) (K + (b - x))
      ≤ 1 / (K + (x - a)) + 1 / (K + (b - x)) := by
    intro x hx
    have hu : 0 < K + (x - a) := by linarith [hx.1]
    have hv : 0 < K + (b - x) := by linarith [hx.2]
    have h1 : 0 ≤ 1 / (K + (x - a)) := le_of_lt (one_div_pos.mpr hu)
    have h2 : 0 ≤ 1 / (K + (b - x)) := le_of_lt (one_div_pos.mpr hv)
    rcases le_total (K + (x - a)) (K + (b - x)) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hgi1 : IntervalIntegrable (fun x : ℝ => 1 / (K + (x - a))) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (continuous_const.add (continuous_id.sub continuous_const)).continuousOn
    · rw [uIcc_of_le hab]; intro x hx; exact ne_of_gt (by linarith [hx.1])
  have hgi2 : IntervalIntegrable (fun x : ℝ => 1 / (K + (b - x))) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (continuous_const.add (continuous_const.sub continuous_id)).continuousOn
    · rw [uIcc_of_le hab]; intro x hx; exact ne_of_gt (by linarith [hx.2])
  calc ∫ x in a..b, 1 / min (K + (x - a)) (K + (b - x))
      ≤ ∫ x in a..b, (1 / (K + (x - a)) + 1 / (K + (b - x))) :=
        intervalIntegral.integral_mono_on hab (intervalIntegrable_inv_min_tent hK hab)
          (hgi1.add hgi2) hpt
    _ = (∫ x in a..b, 1 / (K + (x - a))) + ∫ x in a..b, 1 / (K + (b - x)) :=
        intervalIntegral.integral_add hgi1 hgi2
    _ = Real.log (1 + (b - a) / K) + Real.log (1 + (b - a) / K) := by
        rw [integral_one_div_add_sub hK hab, integral_one_div_K_sub hK hab]
    _ = 2 * Real.log (1 + (b - a) / K) := by ring

/-- **The tent comparison.**  If `A` is affine of slope `1` and `B` affine of slope `-1` on
`[a,b]`, with `A a ≥ K` and `B b ≥ K`, then the reciprocal of the tent `min (A,B)` is bounded by
`2 log (1 + (b-a)/K)` in integral. -/
lemma integral_inv_min_le {K : ℝ} (hK : 0 < K) {a b : ℝ} (hab : a ≤ b) {A B : ℝ → ℝ}
    (hAc : Continuous A) (hBc : Continuous B) (hAa : K ≤ A a) (hBb : K ≤ B b)
    (hAsh : ∀ x ∈ Set.Icc a b, A x = A a + (x - a))
    (hBsh : ∀ x ∈ Set.Icc a b, B x = B b + (b - x)) :
    ∫ x in a..b, 1 / min (A x) (B x) ≤ 2 * Real.log (1 + (b - a) / K) := by
  have hpos : ∀ x ∈ Set.Icc a b, 0 < min (K + (x - a)) (K + (b - x)) :=
    fun x hx => lt_min (by linarith [hx.1]) (by linarith [hx.2])
  have hAx : ∀ x ∈ Set.Icc a b, K + (x - a) ≤ A x := by
    intro x hx
    rw [hAsh x hx]
    linarith [hx.1]
  have hBx : ∀ x ∈ Set.Icc a b, K + (b - x) ≤ B x := by
    intro x hx
    rw [hBsh x hx]
    linarith [hx.2]
  have hminpos : ∀ x ∈ Set.Icc a b, 0 < min (A x) (B x) := fun x hx =>
    lt_of_lt_of_le (hpos x hx) (min_le_min (hAx x hx) (hBx x hx))
  have hpoint : ∀ x ∈ Set.Icc a b,
      1 / min (A x) (B x) ≤ 1 / min (K + (x - a)) (K + (b - x)) := fun x hx =>
    one_div_le_one_div_of_le (hpos x hx) (min_le_min (hAx x hx) (hBx x hx))
  have hminpos' : ∀ x ∈ uIcc a b, 0 < min (A x) (B x) := by
    rw [uIcc_of_le hab]
    exact hminpos
  have hfi : IntervalIntegrable (fun x : ℝ => 1 / min (A x) (B x)) volume a b :=
    (ContinuousOn.div continuousOn_const (hAc.min hBc).continuousOn
      (fun x hx => ne_of_gt (hminpos' x hx))).intervalIntegrable
  exact (intervalIntegral.integral_mono_on hab hfi (intervalIntegrable_inv_min_tent hK hab)
    hpoint).trans (integral_inv_min_tent hK hab)

theorem tent_integral_gate {Ξ : ℝ} {α : ℂ} {s a b : ℝ} (hab : a ≤ b)
    (hlo : ∀ x ∈ Set.Icc a b, (2:ℝ)^10 ≤ min (Work.Pert.V5.mgA Ξ α (x + s * Complex.I)) (Work.Pert.V5.mgB Ξ (x + s * Complex.I))) :
    ∫ x in a..b, 1 / min (Work.Pert.V5.mgA Ξ α (x + s * Complex.I)) (Work.Pert.V5.mgB Ξ (x + s * Complex.I))
      ≤ 2 * Real.log (1 + (b-a)/(2:ℝ)^10) := by
  have hK : (0 : ℝ) < 2 ^ 10 := by norm_num
  have hA : Continuous (fun x : ℝ => mgA Ξ α (x + s * Complex.I)) := by
    simp only [mgA]; fun_prop
  have hB : Continuous (fun x : ℝ => mgB Ξ (x + s * Complex.I)) := by
    simp only [mgB]; fun_prop
  refine integral_inv_min_le hK hab hA hB ?_ ?_ ?_ ?_
  · exact le_trans (hlo a ⟨le_rfl, hab⟩) (min_le_left _ _)
  · exact le_trans (hlo b ⟨hab, le_rfl⟩) (min_le_right _ _)
  · intro x hx
    rw [mgA_line, mgA_line]
    ring
  · intro x hx
    rw [mgB_line, mgB_line]
    ring

end

end Work.Pert.V5
