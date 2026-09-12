import Mathlib
import Submission.ModelStarMap
import Submission.ModelStarBoundary2
import Submission.ModelStarBoundary3

noncomputable section
open scoped Real BigOperators Topology
open Filter Set Complex
open Submission.ModelStarMap
open Submission.ModelStarBoundary2
open Submission.ModelStarBoundary3

/-!
# ModelStarBoundary4 -- fixed ray on junction-free arcs (stage 3b part 1)

STATUS: verified research-isolate milestone; 0 sorries; axiom-clean
[propext, Classical.choice, Quot.sound]; unimported module (does NOT import
`Submission.lean`).  Builds on Submission.ModelStarMap (modelF),
Submission.ModelStarBoundary2 (`eAngle`, `dirSign`, per-`t` ray identity
`modelF_boundary_ray`) and Submission.ModelStarBoundary3 (`rho`, the
boundary sweep factor).

CONTENT (stage 3b part 1: the DIRECTION is constant on any open interval
that contains no junction value):
  * `dirSign_eq_of_no_junction_between`: on an interval `Ioo a b` free of
    junction values (`∀ k, φ k ∉ Ioo a b`), the pass/fail pattern
    `dirSign φ t k` is independent of the interior point `t` (a pure
    order/logic lemma over the finite index type).
  * `theta_dirSign_const`: consequently the model direction
    `Θ(t) := Σ_k r k·(φ k + π·dirSign φ t k)` is constant in `t` over any
    junction-free interval.
  * `boundaryMap_on_junctionFree_interval` (stage-3b core): if the interval
    `Ioo a b ⊆ Ioo 0 (2π)` contains no junction value, then there is a
    unit complex number `u` (the arc direction) such that every boundary
    value on the interval lies on the fixed ray `ℝ≥0·u`:
        modelF z₀ r (eAngle t) = (rho φ r t : ℂ) * u   for all t ∈ Ioo a b,
    with the real nonnegative factor `rho φ r t = ‖modelF z₀ r (eAngle t)‖`
    (rho_eq_norm_boundary).  Together with the junction-zero limits of
    ModelStarBoundary3 this yields (stage 3b part 2, next milestone) that
    on the maximal arc between two consecutive junctions the boundary map
    sweeps the whole segment `[0, m·u]`, `m := sup over the arc of rho`
    (via the generic IVT sweep `Submission.RaySweep.surjOn_Ioo_zero_sSup`).
-/

namespace Submission.ModelStarBoundary4

/-- On an interval free of junction values the pass/fail sign pattern is
independent of the interior point. -/
lemma dirSign_eq_of_no_junction_between {s : ℕ} (φ : Fin s → ℝ) {a b t t' : ℝ}
    (hjf : ∀ k : Fin s, φ k ∉ Ioo a b) (ht : t ∈ Ioo a b) (ht' : t' ∈ Ioo a b)
    (k : Fin s) :
    dirSign φ t k = dirSign φ t' k := by
  have hk_not : ¬(a < φ k ∧ φ k < b) := by simpa using hjf k
  have hk' : φ k ≤ a ∨ b ≤ φ k := by
    rcases not_and_or.mp hk_not with h1 | h2
    · left
      exact le_of_not_gt h1
    · right
      exact le_of_not_gt h2
  have hiff : (φ k < t) ↔ φ k < t' := by
    constructor
    · intro hkt
      rcases hk' with hka | hbk
      · have hat' : a < t' := ht'.1
        exact lt_of_le_of_lt hka hat'
      · exfalso
        have htb : t < b := ht.2
        exact not_lt_of_ge hbk (lt_trans hkt htb)
    · intro hkt'
      rcases hk' with hka | hbk
      · have hat : a < t := ht.1
        exact lt_of_le_of_lt hka hat
      · exfalso
        have ht'b : t' < b := ht'.2
        exact not_lt_of_ge hbk (lt_trans hkt' ht'b)
  unfold dirSign
  by_cases h : φ k < t
  · have h' : φ k < t' := (hiff.1) h
    rw [if_pos h, if_pos h']
  · have h' : ¬ φ k < t' := fun hx => h ((hiff.2) hx)
    rw [if_neg h, if_neg h']

/-- The model direction `Θ(t)` is constant over a junction-free interval. -/
lemma theta_dirSign_const {s : ℕ} (r : Fin s → ℝ) (φ : Fin s → ℝ) {a b t t' : ℝ}
    (hjf : ∀ k : Fin s, φ k ∉ Ioo a b) (ht : t ∈ Ioo a b) (ht' : t' ∈ Ioo a b) :
    (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k))) =
      (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t' k))) := by
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [dirSign_eq_of_no_junction_between φ hjf ht ht' k]

/-- The circle parametrisation has unit norm. -/
lemma eAngle_norm (x : ℝ) : ‖eAngle x‖ = 1 := by
  unfold eAngle
  simp

/-- **Fixed ray on a junction-free arc.**  On any open interval
`Ioo a b ⊆ Ioo 0 (2π)` that contains no junction value `φ k`, every
boundary value `modelF z₀ r (eAngle t)` lies on one fixed ray
`ℝ≥0 · u` (u unit), at distance `rho φ r t`. -/
theorem boundaryMap_on_junctionFree_interval {s : ℕ} (z₀ : Fin s → ℂ) (r : Fin s → ℝ)
    (φ : Fin s → ℝ) (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1)
    {a b : ℝ} (hab : a < b)
    (hI : Ioo a b ⊆ Ioo 0 (2 * Real.pi))
    (hjf : ∀ k : Fin s, φ k ∉ Ioo a b) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ t : ℝ, t ∈ Ioo a b →
      Submission.ModelStarMap.modelF z₀ r (eAngle t) = (rho φ r t : ℂ) * u := by
  let t₀ : ℝ := (a + b) / 2
  have ht₀ : t₀ ∈ Ioo a b := by
    have h₁ : a < t₀ := by dsimp [t₀]; linarith
    have h₂ : t₀ < b := by dsimp [t₀]; linarith
    exact ⟨h₁, h₂⟩
  let u : ℂ := eAngle (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t₀ k)))
  refine ⟨u, ?_, ?_⟩
  · have hu : ‖u‖ = 1 := by
      dsimp [u]
      exact eAngle_norm (x := ∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t₀ k)))
    exact hu
  · intro t ht
    have htI : t ∈ Ioo 0 (2 * Real.pi) := hI ht
    have ht0' : 0 < t := htI.1
    have ht2 : t < 2 * Real.pi := htI.2
    have hne : ∀ k : Fin s, φ k ≠ t := by
      intro k hk
      have hkt : φ k ∈ Ioo a b := by
        rw [hk]
        exact ht
      exact (hjf k) hkt
    have ray := ModelStarBoundary2.modelF_boundary_ray z₀ r φ hz₀e hφlo hφhi hsum (t := t) ht0' ht2 hne
    have hth : (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k))) =
        (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t₀ k))) :=
      theta_dirSign_const r φ hjf ht ht₀
    -- ray : modelF z₀ r (eAngle t) = ((∏_k ‖1-eAngle(φk-t)‖^(2rk)):ℂ) * eAngle (Θ t)
    rw [ModelStarBoundary2.modelF_boundary_ray z₀ r φ hz₀e hφlo hφhi hsum (t := t) ht0' ht2 hne]
    rw [hth]
    have hpr : ((∏ k : Fin s, ‖1 - eAngle (φ k - t)‖ ^ (2 * r k) : ℝ) : ℂ) = (rho φ r t : ℂ) := by
      unfold rho
      rfl
    rw [hpr]

end Submission.ModelStarBoundary4

end
