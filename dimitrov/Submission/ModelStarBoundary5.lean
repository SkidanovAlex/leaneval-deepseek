import Mathlib
import Submission.ModelStarMap
import Submission.ModelStarBoundary2
import Submission.ModelStarBoundary3
import Submission.ModelStarBoundary4
import Submission.Commons.Analysis.Interval.surjOn_Ioo_zero_sSup

noncomputable section
open scoped Real BigOperators Topology
open Filter Set Complex
open Submission.ModelStarMap
open Submission.ModelStarBoundary2
open Submission.ModelStarBoundary3
open Submission.ModelStarBoundary4

/-!
# ModelStarBoundary5 -- consecutive-arc sweep: the boundary image of an arc
# between consecutive junctions is the full segment (stage 3b part 2)

STATUS: verified research-isolate milestone; 0 sorries; axiom-clean
[propext, Classical.choice, Quot.sound]; unimported module (does NOT import
`Submission.lean`).  Builds on ModelStarBoundary2 (ray identity),
ModelStarBoundary3 (rho: continuity + junction-zero limits),
ModelStarBoundary4 (fixed ray on junction-free arcs) and the shared-commons
IVT sweep `Commons.Analysis.Interval.surjOn_Ioo_zero_sSup`.

THEOREM (`arc_sweeps_segment`, stage 3b core): let junctions
`z₀ k = eAngle (φ k)`, `0 ≤ φ k < 2π`, strictly monotone `φ`, weights
`0 ≤ r k` with `Σ r k = 1`.  On the open arc between two CONSECUTIVE
junctions `φ j < φ (j+1)` with `0 < r j`, `0 < r (j+1)` the boundary map
sweeps a full segment: there is a unit direction `u` such that every
`x ∈ (0, m_j)`, `m_j := sSup (rho φ r '' Ioo (φ j) (φ (j+1)))`, is a
boundary value of the arc: `∃ t ∈ Ioo (φ j) (φ (j+1))` with
`modelF z₀ r (eAngle t) = (x : ℂ) * u`.  (Closed-endpoint statement,
image `⊇ [0, m_j]·u` up to the endpoint limits at the junctions, is
deferred to the next stage; the interior sweep is the IVT content.)

Proof route: (1) on the junction-free interval `Ioo (φ j) (φ (j+1))`
(no `φ k` lies strictly between two consecutive values, by monotonicity +
a `k ≤ j`/`j+1 ≤ k` case split) the fixed-ray theorem gives `u` with
`F = (rho : ℂ) * u`; (2) `rho` is continuous (`rho_continuousAt`), bounded
above (each factor `‖1 − eAngle θ‖ ≤ 2`, so `rho ≤ ∏_k 2^(2 r k)`), and
tends to `0` at both endpoints (`rho_tendsto_junction_zero` restricted to
the one-sided filters via `Tendsto.mono_left nhdsWithin_le_nhds`);
(3) `Commons.Analysis.Interval.surjOn_Ioo_zero_sSup` attains each
`x ∈ (0, m_j)`, and the fixed ray turns `rho t = x` into `F = x·u`.
-/

namespace Submission.ModelStarBoundary5

/-- `‖1 − eAngle θ‖ ≤ 2` (unit circle geometry). -/
lemma norm_one_sub_eAngle_le_two (θ : ℝ) : ‖1 - eAngle θ‖ ≤ 2 := by
  calc
    ‖1 - eAngle θ‖ ≤ ‖(1 : ℂ)‖ + ‖eAngle θ‖ := norm_sub_le _ _
    _ = 2 := by
      have h1 : ‖(1 : ℂ)‖ = 1 := by simp
      have h2 : ‖eAngle θ‖ = 1 := eAngle_norm θ
      rw [h1, h2]
      norm_num

/-- Per-factor bound: `‖1 − eAngle θ‖^(2 r k) ≤ 2^(2 r k)` for `0 ≤ r k`. -/
lemma factor_pow_le {r : ℝ} (hr : 0 ≤ r) {θ : ℝ} :
    ‖1 - eAngle θ‖ ^ (2 * r) ≤ (2 : ℝ) ^ (2 * r) := by
  have hq : 0 ≤ 2 * r := by nlinarith
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_one_sub_eAngle_le_two θ) hq

/-- Global uniform upper bound of the sweep factor:
`rho φ r t ≤ ∏_k 2^(2 r k)` for nonnegative weights. -/
lemma rho_le_uniform_bound {s : ℕ} (φ : Fin s → ℝ) (r : Fin s → ℝ)
    (hr : ∀ k : Fin s, 0 ≤ r k) (t : ℝ) :
    rho φ r t ≤ ∏ k : Fin s, (2 : ℝ) ^ (2 * r k) := by
  have h0 : ∀ k : Fin s, 0 ≤ ‖1 - eAngle (φ k - t)‖ ^ (2 * r k) := by
    intro k
    exact Real.rpow_nonneg (norm_nonneg _) _
  have h1 : ∀ k : Fin s, ‖1 - eAngle (φ k - t)‖ ^ (2 * r k) ≤ (2 : ℝ) ^ (2 * r k) := by
    intro k
    exact factor_pow_le (hr k) (θ := φ k - t)
  have h0m : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      0 ≤ ‖1 - eAngle (φ i - t)‖ ^ (2 * r i) := fun i hi => h0 i
  have h1m : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      ‖1 - eAngle (φ i - t)‖ ^ (2 * r i) ≤ (2 : ℝ) ^ (2 * r i) := fun i hi => h1 i
  have hprod : (∏ k ∈ (Finset.univ : Finset (Fin s)),
      ‖1 - eAngle (φ k - t)‖ ^ (2 * r k)) ≤
      (∏ k ∈ (Finset.univ : Finset (Fin s)), (2 : ℝ) ^ (2 * r k)) := by
    exact Finset.prod_le_prod h0m h1m
  unfold rho
  simpa using hprod

/-- Consecutive junctions bound a junction-free open interval: for strictly
monotone `φ` and `j1 := ⟨j.val+1, hj⟩`, no `φ k` lies strictly between
`φ j` and `φ j1`. -/
lemma no_junction_between_consecutive {s : ℕ} (φ : Fin s → ℝ) (hmono : Monotone φ)
    {j : Fin s} (hj : j.val + 1 < s) :
    ∀ k : Fin s, φ k ∉ Ioo (φ j) (φ ⟨j.val + 1, hj⟩) := by
  intro k hk
  by_cases hkj : k.val ≤ j.val
  · have hkle : k ≤ j := (Fin.le_def).2 hkj
    have hφk : φ k ≤ φ j := hmono hkle
    exact (not_lt_of_ge hφk) hk.1
  · have hj1k : j.val + 1 ≤ k.val := Nat.succ_le_of_lt (Nat.lt_of_not_ge hkj)
    have hj1le : (⟨j.val + 1, hj⟩ : Fin s) ≤ k := (Fin.le_def).2 hj1k
    have hφk2 : φ ⟨j.val + 1, hj⟩ ≤ φ k := hmono hj1le
    exact (not_lt_of_ge hφk2) hk.2

/-- Strict increase of consecutive values (from monotone + injective). -/
lemma consecutive_lt {s : ℕ} (φ : Fin s → ℝ) (hmono : Monotone φ)
    (hφinj : Function.Injective φ) {j : Fin s} (hj : j.val + 1 < s) :
    φ j < φ ⟨j.val + 1, hj⟩ := by
  have hle : φ j ≤ φ ⟨j.val + 1, hj⟩ := hmono ((Fin.le_def).2 (by dsimp; omega))
  have hne : φ j ≠ φ ⟨j.val + 1, hj⟩ := by
    intro h
    have heq : (⟨j.val + 1, hj⟩ : Fin s) = j := hφinj h.symm
    have hval : (⟨j.val + 1, hj⟩ : Fin s).val ≠ j.val := by
      dsimp
      omega
    exact hval (congrArg Fin.val heq)
  exact lt_of_le_of_ne hle hne

/-- **Arc sweep between consecutive junctions (stage-3b core).** -/
theorem arc_sweeps_segment {s : ℕ} (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (φ : Fin s → ℝ)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hr : ∀ k : Fin s, 0 ≤ r k)
    {j : Fin s} (hj : j.val + 1 < s) (hrj : 0 < r j) (hrj1 : 0 < r ⟨j.val + 1, hj⟩) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      ∀ x : ℝ, 0 < x → x < sSup (rho φ r '' Ioo (φ j) (φ ⟨j.val + 1, hj⟩)) →
        ∃ t : ℝ, t ∈ Ioo (φ j) (φ ⟨j.val + 1, hj⟩) ∧
          Submission.ModelStarMap.modelF z₀ r (eAngle t) = (x : ℂ) * u := by
  let j1 : Fin s := ⟨j.val + 1, hj⟩
  have hj1f : ∀ k : Fin s, φ k ∉ Ioo (φ j) (φ j1) := by
    simpa [j1] using (no_junction_between_consecutive φ hmono hj)
  have hab : φ j < φ j1 := by
    simpa [j1] using (consecutive_lt φ hmono hφinj hj)
  have hI : Ioo (φ j) (φ j1) ⊆ Ioo 0 (2 * Real.pi) := by
    intro t ht
    have ht1 : φ j < t := ht.1
    have ht2 : t < φ j1 := ht.2
    constructor
    · have h0 : 0 ≤ φ j := hφlo j
      exact lt_of_le_of_lt h0 ht1
    · have h2 : φ j1 < 2 * Real.pi := hφhi j1
      exact lt_trans ht2 h2
  rcases (boundaryMap_on_junctionFree_interval z₀ r φ hz₀e hφlo hφhi hsum hab hI hj1f) with
    ⟨u, hu1, hu2⟩
  refine ⟨u, hu1, ?_⟩
  intro x hx0 hxm
  -- apply the commons IVT sweep to p := rho φ r on Ioo (φ j) (φ j1)
  have hpglob : Continuous (fun t : ℝ => rho φ r t) :=
    continuous_iff_continuousAt.2 (fun t => rho_continuousAt φ r hr t)
  have hp : ContinuousOn (fun t : ℝ => rho φ r t) (Ioo (φ j) (φ j1)) := hpglob.continuousOn
  have hBdd : BddAbove ((fun t : ℝ => rho φ r t) '' Ioo (φ j) (φ j1)) := by
    refine ⟨∏ k : Fin s, (2 : ℝ) ^ (2 * r k), ?_⟩
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact rho_le_uniform_bound φ r hr t
  have hpa : Tendsto (fun t : ℝ => rho φ r t) (𝓝[>] (φ j)) (𝓝 0) := by
    exact (rho_tendsto_junction_zero φ r hr (j := j) hrj).mono_left nhdsWithin_le_nhds
  have hpb : Tendsto (fun t : ℝ => rho φ r t) (𝓝[<] (φ j1)) (𝓝 0) := by
    exact (rho_tendsto_junction_zero φ r hr (j := j1) hrj1).mono_left nhdsWithin_le_nhds
  have hsweep := Commons.Analysis.Interval.surjOn_Ioo_zero_sSup (p := fun t : ℝ => rho φ r t)
    (a := φ j) (b := φ j1) hab hp hBdd hpa hpb x hx0 hxm
  rcases hsweep with ⟨t, ht, hpt⟩
  refine ⟨t, ht, ?_⟩
  have hF := hu2 t ht
  -- hF : modelF z₀ r (eAngle t) = (rho φ r t : ℂ) * u
  rw [hF, hpt]

end Submission.ModelStarBoundary5

end
