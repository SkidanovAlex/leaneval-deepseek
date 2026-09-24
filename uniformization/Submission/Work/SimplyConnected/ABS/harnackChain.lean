import Mathlib
import Submission.Work.SimplyConnected.ABS.harnackChartBall

/-!
# The Harnack chain estimate

A "Harnack chain" is a finite sequence of chart balls in which each ball contains the centre of the
next one at chart distance at most half of its radius.  Iterating the chart-ball Harnack inequality
(`Work.SimplyConnected.ABS.harnack_inequality_chartBall`) along such a chain, a non-negative
harmonic function is comparable at the two ends of the chain with the explicit factor `5 ^ n`.

This is the second brick of the Harnack layer needed by the barrier globalisation
(`Work.SimplyConnected.ABS.posHarmonicDominatedOfLocalBarrier`): applied to a chain joining a base
point to the compact chart-sphere piece of a collar, it produces a *uniform* lower bound for a
positive harmonic function, independent of the function, as soon as a chain exists.
-/

open Filter Set Metric
open scoped Topology Manifold ContDiff

noncomputable section

namespace Work.SimplyConnected.ABS

/-- **One step of a Harnack chain.**  If `q'` lies in the chart ball of centre `q` and radius `r`
at chart distance at most `r / 2` from the centre, and that ball sits inside the open set `U` on
which `h ≥ 0` is harmonic, then `h q ≤ 5 * h q'` and `h q' ≤ 5 * h q`. -/
theorem harnack_chain_step {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} {h : X → ℝ} (hh : Submission.HarmonicOnX h U)
    (hpos : ∀ x ∈ U, 0 ≤ h x) {q q' : X} {r : ℝ} (hr : 0 < r)
    (htgt : Metric.closedBall ((chartAt ℂ q) q) r ⊆ (chartAt ℂ q).target)
    (hsub : Submission.chartBall (chartAt ℂ q) ((chartAt ℂ q) q) r ⊆ U)
    (hstep : q' ∈ Submission.chartBall (chartAt ℂ q) ((chartAt ℂ q) q) r)
    (hhalf : ‖(chartAt ℂ q) q' - (chartAt ℂ q) q‖ ≤ r / 2) :
    h q' ≤ 5 * h q ∧ h q ≤ 5 * h q' := by
  have hpos' : ∀ y ∈ Submission.chartBall (chartAt ℂ q) ((chartAt ℂ q) q) r, 0 ≤ h y :=
    fun y hy => hpos y (hsub hy)
  have hcq : q ∈ Submission.chartBall (chartAt ℂ q) ((chartAt ℂ q) q) r := by
    rw [Submission.mem_chartBall]
    exact ⟨mem_chart_source ℂ q, by rw [Metric.mem_ball, dist_self]; exact hr⟩
  have h := harnack_inequality_chartBall (p := q) (x := q') hr htgt (hh.mono hsub) hpos' hstep hhalf
  exact ⟨h.1, h.2⟩

/-- **Harnack chain estimate.**  Let `h ≥ 0` be harmonic on an open set `U`, and let
`p 0, …, p n` be joined by a chain of chart balls `Bᵢ` centred at `p i` with radius `r i`, each
contained in `U` and with `p (i+1)` at chart distance `≤ r i / 2` from the centre `p i`.  Then

  `h (p n) ≤ 5 ^ n * h (p 0)`  and  `h (p 0) ≤ 5 ^ n * h (p n)`. -/
theorem harnack_chain_le {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} {h : X → ℝ} (hh : Submission.HarmonicOnX h U)
    (hpos : ∀ x ∈ U, 0 ≤ h x) {n : ℕ} {p : ℕ → X} {r : ℕ → ℝ}
    (hr : ∀ i < n, 0 < r i)
    (htgt : ∀ i < n, Metric.closedBall ((chartAt ℂ (p i)) (p i)) (r i) ⊆ (chartAt ℂ (p i)).target)
    (hsub : ∀ i < n, Submission.chartBall (chartAt ℂ (p i)) ((chartAt ℂ (p i)) (p i)) (r i) ⊆ U)
    (hstep : ∀ i < n, p (i + 1) ∈
      Submission.chartBall (chartAt ℂ (p i)) ((chartAt ℂ (p i)) (p i)) (r i))
    (hhalf : ∀ i < n,
      ‖(chartAt ℂ (p i)) (p (i + 1)) - (chartAt ℂ (p i)) (p i)‖ ≤ r i / 2) :
    h (p n) ≤ 5 ^ n * h (p 0) ∧ h (p 0) ≤ 5 ^ n * h (p n) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have ih' := ih (fun i hi => hr i (Nat.lt_succ_of_lt hi))
        (fun i hi => htgt i (Nat.lt_succ_of_lt hi))
        (fun i hi => hsub i (Nat.lt_succ_of_lt hi))
        (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
        (fun i hi => hhalf i (Nat.lt_succ_of_lt hi))
      obtain ⟨ihlo, ihhi⟩ := ih'
      obtain ⟨hklo, hkhi⟩ :=
        harnack_chain_step hh hpos (hr k (Nat.lt_succ_self k)) (htgt k (Nat.lt_succ_self k))
          (hsub k (Nat.lt_succ_self k)) (hstep k (Nat.lt_succ_self k)) (hhalf k (Nat.lt_succ_self k))
      constructor
      · calc h (p (k + 1)) ≤ 5 * h (p k) := hklo
          _ ≤ 5 * (5 ^ k * h (p 0)) := mul_le_mul_of_nonneg_left ihlo (by norm_num)
          _ = 5 ^ (k + 1) * h (p 0) := by ring
      · calc h (p 0) ≤ 5 ^ k * h (p k) := ihhi
          _ ≤ 5 ^ k * (5 * h (p (k + 1))) :=
              mul_le_mul_of_nonneg_left hkhi (by positivity)
          _ = 5 ^ (k + 1) * h (p (k + 1)) := by ring

end Work.SimplyConnected.ABS
