import Mathlib
import Submission.ModelStarMap
import Submission.ModelStarBoundary
import Submission.ModelStarBoundary2
import Submission.ModelStarBoundary3
import Submission.ModelStarBoundary4
import Submission.ModelStarBoundary5
import Submission.Commons.Analysis.Complex.one_sub_exp_ne_zero_of_mem_Ioo

noncomputable section
open scoped Real BigOperators Topology
open Filter Set Metric
open Submission.ModelStarMap
open Submission.ModelStarBoundary2
open Submission.ModelStarBoundary3
open Submission.ModelStarBoundary4
open Submission.ModelStarBoundary5

/-!
# ModelStarBoundary6 -- stage 4: closed-arc sweep of the model boundary map
# (milestone (a) part 3, stage 4: the arc sweeps the full closed segment)

STATUS: verified research-isolate milestone; 0 sorries; axiom-clean
[propext, Classical.choice, Quot.sound]; unimported module.  Builds on
ModelStarBoundary3 (rho/boundaryMap continuity + junction-zero limits),
ModelStarBoundary4 (fixed-ray identity on junction-free intervals) and
ModelStarBoundary5 (interior sweep machinery, `rho_le_uniform_bound`).

CONTENT (stage 4, closed-arc packaging -- the last boundary-level piece of
the EASY half of Eremenko's equivalence):
  * `one_sub_eAngle_ne_zero_of_mem`: `1 − eAngle x ≠ 0` for
    `x ∈ (−2π, 2π)`, `x ≠ 0` (commons `one_sub_exp_ne_zero_of_mem_Ioo`
    in `eAngle` form);
  * `eAngle_ne_of_mem_diff`: `eAngle x ≠ eAngle y` for `y − x ∈ (−2π,2π)`,
    `x ≠ y` (injectivity away from the period lattice);
  * `modelF_junction_value_zero`: the model boundary map takes the value `0`
    AT the junction `eAngle (φ j)` (the `j`-factor is `0^(2 r j) = 0` when
    `0 < r j`);
  * `boundaryMap_continuousOn_closedArc`: `t ↦ modelF z₀ r (eAngle t)` is
    continuous on the closed arc `[φ j, φ j1]` between consecutive junctions
    (in fact continuous at every point of the arc: at interior points via
    the analytic shell, at the junctions by the limit `→ 0` and the value
    `0`);
  * `rho_pos_of_mem_Ioo`: `ρ(t) > 0` for `t` in the open arc (every factor
    base is nonzero there);
  * `rho_max_on_closedArc`: on the closed arc `ρ` attains its maximum at an
    INTERIOR point `t₀`, and that maximum equals `sSup (ρ '' Ioo …)`;
  * `closed_arc_sweeps_segment` (stage-4 core): for the standard model data
    (unit junctions, sorted `φ`, `Σ r = 1`), on the arc between consecutive
    junctions `φ j < φ j1` with `0 < r j`, `0 < r j1`:
      ∃ u, ‖u‖ = 1 ∧ ∀ x ∈ Icc 0 m, ∃ t ∈ Icc (φ j) (φ j1),
        modelF z₀ r (eAngle t) = (x : ℂ) * u,
    `m := sSup (rho φ r '' Ioo (φ j) (φ j1))` -- the arc sweeps the CLOSED
    segment `[0, m]·u`, attaining the tip `m·u` at an interior point and the
    junction value `0` at both arc endpoints.

NOTE (framework value only): this does NOT close the gate
`Step3.sym_maximality` (which needs the converse E1-E5).
-/

namespace Submission.ModelStarBoundary6

/-- `1 − eAngle x ≠ 0` for `x ∈ (−2π, 2π)`, `x ≠ 0`. -/
private lemma one_sub_eAngle_ne_zero_of_mem {x : ℝ} (hxlo : -2 * Real.pi < x)
    (hxhi : x < 2 * Real.pi) (hx0 : x ≠ 0) : 1 - eAngle x ≠ 0 := by
  simpa [eAngle] using
    (Commons.Analysis.Complex.one_sub_exp_ne_zero_of_mem_Ioo (x := x) hxlo hxhi hx0)

/-- `eAngle` is injective away from the period lattice: if `y − x ∈ (−2π,2π)`
and `x ≠ y`, then `eAngle x ≠ eAngle y`. -/
lemma eAngle_ne_of_mem_diff {x y : ℝ} (hxy : y - x ∈ Ioo (-2 * Real.pi) (2 * Real.pi))
    (hxney : x ≠ y) : eAngle x ≠ eAngle y := by
  intro h
  have hnorm : ‖1 - eAngle (y - x)‖ = 0 := by
    rw [← norm_eAngle_sub (t := x) (θ := y)]
    have hsub : eAngle x - eAngle y = 0 := by
      rw [h, sub_self]
    simp [hsub]
  have hne0 : 1 - eAngle (y - x) ≠ 0 :=
    one_sub_eAngle_ne_zero_of_mem (mem_Ioo.mp hxy).1 (mem_Ioo.mp hxy).2
      (sub_ne_zero.mpr hxney.symm)
  exact hne0 (norm_eq_zero.mp hnorm)

/-- The model boundary map takes the value `0` at the junction point
`eAngle (φ j)` when the weight `r j` is positive. -/
lemma modelF_junction_value_zero {s : ℕ} (z₀ : Fin s → ℂ) (r φ : Fin s → ℝ)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k)) {j : Fin s} (hrj : 0 < r j) :
    modelF z₀ r (eAngle (φ j)) = 0 := by
  have hzane : eAngle (φ j) ≠ 0 := by
    intro hz
    have h : ‖eAngle (φ j)‖ = 0 := by simp [hz]
    have hn : ‖eAngle (φ j)‖ = 1 := eAngle_norm (φ j)
    rw [hn] at h
    norm_num at h
  have hbase : 1 - z₀ j * (eAngle (φ j))⁻¹ = 0 := by
    rw [hz₀e j]
    rw [mul_inv_cancel₀ hzane]
    norm_num
  have hpow : (1 - z₀ j * (eAngle (φ j))⁻¹) ^ ((2 * r j : ℝ) : ℂ) = 0 := by
    rw [hbase]
    have hne : ((2 * r j : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) hrj))
    exact Complex.zero_cpow hne
  have hfac : modelFactor (z₀ j) (2 * r j) (eAngle (φ j)) = 0 := by
    dsimp [modelFactor]
    simpa using hpow
  have hprod : modelProduct z₀ r (eAngle (φ j)) = 0 := by
    unfold modelProduct
    simpa using (Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin s)))
      (f := fun k : Fin s => modelFactor (z₀ k) (2 * r k) (eAngle (φ j)))
      (i := j) (Finset.mem_univ j) hfac)
  unfold modelF
  rw [hprod]
  exact mul_zero (eAngle (φ j))

/-- Continuity of the model boundary map on the closed arc between two
consecutive junctions (full-topology continuity at every point of the arc). -/
theorem boundaryMap_continuousOn_closedArc {s : ℕ} (z₀ : Fin s → ℂ) (r φ : Fin s → ℝ)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hr : ∀ k : Fin s, 0 ≤ r k) (hmono : Monotone φ)
    {j : Fin s} (hj : j.val + 1 < s) (hrj : 0 < r j)
    (hrj1 : 0 < r ⟨j.val + 1, hj⟩) :
    ContinuousOn (fun t : ℝ => modelF z₀ r (eAngle t)) (Icc (φ j) (φ ⟨j.val + 1, hj⟩)) := by
  classical
  let j1 : Fin s := ⟨j.val + 1, hj⟩
  have hz₀u : ∀ k : Fin s, ‖z₀ k‖ = 1 := by
    intro k
    rw [hz₀e k]
    exact eAngle_norm (φ k)
  have hcont : ∀ t₀ : ℝ, t₀ ∈ Icc (φ j) (φ j1) →
      ContinuousAt (fun t : ℝ => modelF z₀ r (eAngle t)) t₀ := by
    intro t₀ ht₀
    have hφjS : φ j ≤ t₀ ∧ t₀ ≤ φ j1 := by
      simpa [j1] using (mem_Icc.mp ht₀)
    by_cases ht₀j : t₀ = φ j
    · subst t₀
      have hz : modelF z₀ r (eAngle (φ j)) = 0 :=
        modelF_junction_value_zero z₀ r φ hz₀e (j := j) hrj
      simpa [ContinuousAt, hz] using
        (boundaryMap_tendsto_junction_zero z₀ φ r hz₀e (j := j) hr hrj)
    · by_cases ht₀j1 : t₀ = φ j1
      · subst t₀
        have hz : modelF z₀ r (eAngle (φ j1)) = 0 :=
          modelF_junction_value_zero z₀ r φ hz₀e (j := j1) hrj1
        simpa [ContinuousAt, hz] using
          (boundaryMap_tendsto_junction_zero z₀ φ r hz₀e (j := j1) hr hrj1)
      · have ht₀oo : t₀ ∈ Ioo (φ j) (φ j1) :=
          mem_Ioo.mpr ⟨lt_of_le_of_ne hφjS.1 (Ne.symm ht₀j),
            lt_of_le_of_ne hφjS.2 ht₀j1⟩
        have ht₀I : t₀ ∈ Ioo 0 (2 * Real.pi) := by
          constructor
          · have h0 : 0 ≤ φ j := hφlo j
            exact lt_of_le_of_lt h0 ht₀oo.1
          · have h2 : φ j1 < 2 * Real.pi := hφhi j1
            exact lt_trans ht₀oo.2 h2
        have hzj : ∀ k : Fin s, z₀ k ≠ eAngle t₀ := by
          intro k
          rw [hz₀e k]
          have hknot : φ k ∉ Ioo (φ j) (φ j1) := by
            simpa [j1] using (no_junction_between_consecutive φ hmono hj k)
          have hφkne : φ k ≠ t₀ := by
            have hle : φ k ≤ φ j ∨ φ j1 ≤ φ k := by
              have hnot : ¬(φ j < φ k ∧ φ k < φ j1) := by
                simpa [mem_Ioo] using hknot
              rcases (not_and_or.mp hnot) with h | h
              · left
                exact le_of_not_gt h
              · right
                exact le_of_not_gt h
            rcases hle with h | h
            · exact ne_of_lt (lt_of_le_of_lt h ht₀oo.1)
            · exact (ne_of_lt (lt_of_lt_of_le ht₀oo.2 h)).symm
          have hdiff : t₀ - φ k ∈ Ioo (-2 * Real.pi) (2 * Real.pi) := by
            constructor
            · nlinarith [hφhi k, ht₀I.1]
            · nlinarith [hφlo k, ht₀I.2]
          exact eAngle_ne_of_mem_diff (x := φ k) (y := t₀) hdiff hφkne
        exact boundaryMap_continuousAt z₀ r hz₀u (t₀ := t₀) hzj
  intro t₀ ht₀
  exact (hcont t₀ (by simpa [j1] using ht₀)).continuousWithinAt

/-- `ρ(t) > 0` for `t` in the open arc between consecutive junctions. -/
lemma rho_pos_of_mem_Ioo {s : ℕ} (φ r : Fin s → ℝ)
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hmono : Monotone φ) {j : Fin s} (hj : j.val + 1 < s)
    {t : ℝ} (ht : t ∈ Ioo (φ j) (φ ⟨j.val + 1, hj⟩)) :
    0 < rho φ r t := by
  let j1 : Fin s := ⟨j.val + 1, hj⟩
  have htI : t ∈ Ioo 0 (2 * Real.pi) := by
    constructor
    · have h0 : 0 ≤ φ j := hφlo j
      exact lt_of_le_of_lt h0 ht.1
    · have h2 : φ j1 < 2 * Real.pi := hφhi j1
      exact lt_trans ht.2 h2
  have hbase : ∀ k : Fin s, ‖1 - eAngle (φ k - t)‖ ≠ 0 := by
    intro k
    have hknot : φ k ∉ Ioo (φ j) (φ j1) := by
      simpa [j1] using (no_junction_between_consecutive φ hmono hj k)
    have hφkne : φ k ≠ t := by
      have hle : φ k ≤ φ j ∨ φ j1 ≤ φ k := by
        have hnot : ¬(φ j < φ k ∧ φ k < φ j1) := by
          simpa [mem_Ioo] using hknot
        rcases (not_and_or.mp hnot) with h | h
        · left
          exact le_of_not_gt h
        · right
          exact le_of_not_gt h
      rcases hle with h | h
      · exact ne_of_lt (lt_of_le_of_lt h ht.1)
      · exact (ne_of_lt (lt_of_lt_of_le ht.2 h)).symm
    have hxlo : -2 * Real.pi < φ k - t := by
      nlinarith [hφlo k, htI.2]
    have hxhi : φ k - t < 2 * Real.pi := by
      nlinarith [hφhi k, htI.1]
    have hx0 : φ k - t ≠ 0 := sub_ne_zero.mpr hφkne
    have hne1 : 1 - eAngle (φ k - t) ≠ 0 :=
      one_sub_eAngle_ne_zero_of_mem hxlo hxhi hx0
    exact norm_ne_zero_iff.mpr hne1
  have hfac : ∀ k : Fin s, 0 < ‖1 - eAngle (φ k - t)‖ ^ (2 * r k) := by
    intro k
    exact Real.rpow_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hbase k))) (2 * r k)
  unfold rho
  simpa using (Finset.prod_pos (s := (Finset.univ : Finset (Fin s)))
    (f := fun k : Fin s => ‖1 - eAngle (φ k - t)‖ ^ (2 * r k))
    (by intro k hk; exact hfac k))

/-- On the closed arc between consecutive junctions `ρ` attains its maximum
at an interior point, equal to the supremum over the open arc. -/
theorem rho_max_on_closedArc {s : ℕ} (φ r : Fin s → ℝ)
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hr : ∀ k : Fin s, 0 ≤ r k) (hmono : Monotone φ) (hφinj : Function.Injective φ)
    {j : Fin s} (hj : j.val + 1 < s) (hrj : 0 < r j)
    (hrj1 : 0 < r ⟨j.val + 1, hj⟩) :
    ∃ t₀ : ℝ, t₀ ∈ Ioo (φ j) (φ ⟨j.val + 1, hj⟩) ∧
      (∀ t : ℝ, t ∈ Icc (φ j) (φ ⟨j.val + 1, hj⟩) → rho φ r t ≤ rho φ r t₀) ∧
      rho φ r t₀ = sSup (rho φ r '' Ioo (φ j) (φ ⟨j.val + 1, hj⟩)) := by
  classical
  let j1 : Fin s := ⟨j.val + 1, hj⟩
  let f : ℝ → ℝ := fun t : ℝ => rho φ r t
  let m : ℝ := sSup (f '' Ioo (φ j) (φ j1))
  have hab : φ j < φ j1 := by
    simpa [j1] using (consecutive_lt φ hmono hφinj hj)
  have hφjS : φ j ∈ Icc (φ j) (φ j1) := mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩
  have hSne : (Icc (φ j) (φ j1)).Nonempty := ⟨φ j, hφjS⟩
  have hfcontS : ContinuousOn f (Icc (φ j) (φ j1)) := by
    dsimp [f]
    exact (continuous_iff_continuousAt.2 (fun t => rho_continuousAt φ r hr t)).continuousOn
  rcases (isCompact_Icc.exists_isMaxOn hSne hfcontS) with ⟨x₀, hx₀S, hx₀max⟩
  have hmid : (φ j + φ j1) / 2 ∈ Ioo (φ j) (φ j1) := by
    constructor <;> nlinarith [hab]
  have hmidS : (φ j + φ j1) / 2 ∈ Icc (φ j) (φ j1) :=
    mem_Icc.mpr ⟨le_of_lt hmid.1, le_of_lt hmid.2⟩
  have hmidpos : 0 < f ((φ j + φ j1) / 2) := by
    dsimp [f]
    exact rho_pos_of_mem_Ioo φ r hφlo hφhi hmono (j := j) hj (t := (φ j + φ j1) / 2) hmid
  have hx₀max' : ∀ y : ℝ, y ∈ Icc (φ j) (φ j1) → f y ≤ f x₀ := by
    have hev : ∀ᶠ y in Filter.principal (Icc (φ j) (φ j1)), f y ≤ f x₀ := hx₀max
    exact Filter.eventually_principal.mp hev
  have hfx0pos : 0 < f x₀ := lt_of_lt_of_le hmidpos (hx₀max' _ hmidS)
  have hx0ne1 : x₀ ≠ φ j := by
    intro hx
    have hval : f x₀ = 0 := by
      dsimp [f]
      rw [hx]
      exact rho_junction_value_zero φ r (j := j) hrj
    rw [hval] at hfx0pos
    norm_num at hfx0pos
  have hx0ne2 : x₀ ≠ φ j1 := by
    intro hx
    have hval : f x₀ = 0 := by
      dsimp [f]
      rw [hx]
      exact rho_junction_value_zero φ r (j := j1) hrj1
    rw [hval] at hfx0pos
    norm_num at hfx0pos
  have hx0S' : φ j ≤ x₀ ∧ x₀ ≤ φ j1 := mem_Icc.mp hx₀S
  have hx0oo : x₀ ∈ Ioo (φ j) (φ j1) :=
    mem_Ioo.mpr ⟨lt_of_le_of_ne hx0S'.1 (Ne.symm hx0ne1), lt_of_le_of_ne hx0S'.2 hx0ne2⟩
  have hBdd : BddAbove (f '' Ioo (φ j) (φ j1)) := by
    refine ⟨∏ k : Fin s, (2 : ℝ) ^ (2 * r k), ?_⟩
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    dsimp [f]
    exact rho_le_uniform_bound φ r hr t
  have hm1 : f x₀ ≤ m := by
    dsimp [m]
    exact le_csSup hBdd ⟨x₀, hx0oo, rfl⟩
  have hm2 : m ≤ f x₀ := by
    dsimp [m]
    refine csSup_le ⟨f x₀, x₀, hx0oo, rfl⟩ ?_
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    have htS : t ∈ Icc (φ j) (φ j1) := mem_Icc.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact hx₀max' t htS
  have hm : f x₀ = m := le_antisymm hm1 hm2
  refine ⟨x₀, hx0oo, ?_, ?_⟩
  · intro t ht
    exact hx₀max' t ht
  · dsimp [f] at hm ⊢
    dsimp [m] at hm ⊢
    simpa [j1] using hm

/-- **Closed-arc sweep (stage-4 core).**  On the arc between consecutive
junctions the model boundary map sweeps the whole closed segment
`[0, m]·u`, `m := sSup (ρ '' Ioo …)`: every point `x·u` with `x ∈ [0, m]`
is attained at some `t` of the closed arc (the tip `m·u` at an interior
point, the junction value `0` at the arc endpoints). -/
theorem closed_arc_sweeps_segment {s : ℕ} (z₀ : Fin s → ℂ) (r φ : Fin s → ℝ)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hr : ∀ k : Fin s, 0 ≤ r k)
    {j : Fin s} (hj : j.val + 1 < s) (hrj : 0 < r j)
    (hrj1 : 0 < r ⟨j.val + 1, hj⟩) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      ∀ x : ℝ, x ∈ Icc 0 (sSup (rho φ r '' Ioo (φ j) (φ ⟨j.val + 1, hj⟩))) →
        ∃ t : ℝ, t ∈ Icc (φ j) (φ ⟨j.val + 1, hj⟩) ∧
          modelF z₀ r (eAngle t) = (x : ℂ) * u := by
  classical
  let j1 : Fin s := ⟨j.val + 1, hj⟩
  let m : ℝ := sSup (rho φ r '' Ioo (φ j) (φ j1))
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
  have hjf : ∀ k : Fin s, φ k ∉ Ioo (φ j) (φ j1) := by
    simpa [j1] using (no_junction_between_consecutive φ hmono hj)
  rcases (boundaryMap_on_junctionFree_interval z₀ r φ hz₀e hφlo hφhi hsum hab hI hjf)
    with ⟨u, hu1, hu2⟩
  have hrhoGlob : Continuous (fun t : ℝ => rho φ r t) :=
    continuous_iff_continuousAt.2 (fun t => rho_continuousAt φ r hr t)
  have hp : ContinuousOn (fun t : ℝ => rho φ r t) (Ioo (φ j) (φ j1)) := hrhoGlob.continuousOn
  have hBdd : BddAbove (rho φ r '' Ioo (φ j) (φ j1)) := by
    refine ⟨∏ k : Fin s, (2 : ℝ) ^ (2 * r k), ?_⟩
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact rho_le_uniform_bound φ r hr t
  have hpa : Tendsto (fun t : ℝ => rho φ r t) (𝓝[>] (φ j)) (𝓝 0) := by
    exact (rho_tendsto_junction_zero φ r hr (j := j) hrj).mono_left nhdsWithin_le_nhds
  have hpb : Tendsto (fun t : ℝ => rho φ r t) (𝓝[<] (φ j1)) (𝓝 0) := by
    exact (rho_tendsto_junction_zero φ r hr (j := j1) hrj1).mono_left nhdsWithin_le_nhds
  have hint : ∀ x : ℝ, 0 < x → x < m →
      ∃ t ∈ Ioo (φ j) (φ j1), modelF z₀ r (eAngle t) = (x : ℂ) * u := by
    intro x hx0 hxm
    have hsweep := Commons.Analysis.Interval.surjOn_Ioo_zero_sSup (p := fun t : ℝ => rho φ r t)
      (a := φ j) (b := φ j1) hab hp hBdd hpa hpb x hx0 hxm
    rcases hsweep with ⟨t, ht, hpt⟩
    refine ⟨t, ht, ?_⟩
    have hF := hu2 t ht
    rw [hF, hpt]
  rcases (rho_max_on_closedArc φ r hφlo hφhi hr hmono hφinj (j := j) hj hrj hrj1)
    with ⟨t₀, ht₀oo, ht₀max, ht₀m⟩
  refine ⟨u, hu1, ?_⟩
  intro x hx
  have hx0le : 0 ≤ x := (mem_Icc.mp hx).1
  have hxle : x ≤ m := by
    simpa [m] using (mem_Icc.mp hx).2
  by_cases hx0 : x = 0
  · refine ⟨φ j, ?_, ?_⟩
    · exact mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩
    · rw [hx0]
      simp
      exact modelF_junction_value_zero z₀ r φ hz₀e (j := j) hrj
  · have hxpos : 0 < x := lt_of_le_of_ne hx0le (Ne.symm hx0)
    by_cases hxm : x = m
    · refine ⟨t₀, ?_, ?_⟩
      · exact mem_Icc.mpr ⟨le_of_lt ht₀oo.1, le_of_lt ht₀oo.2⟩
      · have hF := hu2 t₀ ht₀oo
        rw [hF, hxm]
        have hm' : rho φ r t₀ = m := by
          simpa [m] using ht₀m
        rw [← hm']
    · have hxltm : x < m := lt_of_le_of_ne hxle hxm
      rcases hint x hxpos hxltm with ⟨t, ht, hval⟩
      refine ⟨t, ?_, hval⟩
      exact mem_Icc.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩

end Submission.ModelStarBoundary6

end
