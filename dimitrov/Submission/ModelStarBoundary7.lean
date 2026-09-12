import Mathlib
import Submission.ModelStarMap
import Submission.ModelStarBoundary2
import Submission.ModelStarBoundary3
import Submission.ModelStarBoundary4
import Submission.ModelStarBoundary5
import Submission.ModelStarBoundary6
import Submission.Commons.Analysis.Interval.surjOn_Ioo_zero_sSup

noncomputable section
open scoped Real BigOperators Topology
open Filter Set Complex
open Submission.ModelStarMap
open Submission.ModelStarBoundary2
open Submission.ModelStarBoundary3
open Submission.ModelStarBoundary4

/-!
# ModelStarBoundary7 -- stage 5: the wrap-around arc (2π-periodicity and the
# sweep of the last arc between φ(s−1) and φ(0)+2π)

STATUS: verified research-isolate milestone; 0 sorries; axiom-clean
[propext, Classical.choice, Quot.sound]; unimported module (does NOT import
`Submission.lean`).  Builds on ModelStarBoundary2 (per-`t` ray identity
`modelF_boundary_ray`), ModelStarBoundary3 (`rho`: continuity, junction-zero
limits, `rho_eq_norm_boundary`), ModelStarBoundary5/6 (consecutive-arc
sweeps) and the shared-commons IVT sweep
`Commons.Analysis.Interval.surjOn_Ioo_zero_sSup`.

CONTENT (the missing "last arc" of the model boundary programme).  Stages
3b/4 covered the arcs between CONSECUTIVE junctions `(φ j, φ (j+1))` with
`j.val + 1 < s`.  The circle minus the `s` junctions has `s` arcs; the
final (wrap-around) arc runs from `φ (s−1)` through the angle `2π` (= 0)
back to `φ 0 + 2π` (lifted coordinates).  This module proves that this
arc sweeps a full segment as well:

  * `eAngle_add_two_pi` / `eAngle_sub_two_pi`: the canonical circle
    exponential is 2π-periodic;
  * `rho_two_pi_periodic`: the sweep factor satisfies
    `rho φ r (t + 2π) = rho φ r t`;
  * `boundaryMap_two_pi_periodic`: the boundary map
    `t ↦ modelF z₀ r (eAngle t)` is 2π-periodic in `t`;
  * `modelF_at_one`: at the point `1 = eAngle 0` (equivalently `eAngle 2π`)
    the model value lies on the wrap ray (all factor arguments positive);
  * `wrap_ray` (core): on the WHOLE open wrap interval
    `(φ (s−1), φ 0 + 2π)` — including the point `t = 2π` — every boundary
    value lies on the fixed ray `u := eAngle (Σ_k r_k φ_k + π)` with
    `modelF z₀ r (eAngle t) = (rho φ r t : ℂ) * u`;
  * `rho_tendsto_wrapA` / `rho_tendsto_wrapB`: one-sided zero limits of the
    sweep factor at the two wrap endpoints (positive-weight endpoint
    junctions);
  * `wrap_sweep_open`: the open-arc interior sweep: every
    `0 < x < sSup (rho φ r '' Ioo a b)` (with the endpoint junctions of
    positive weight) is attained on the wrap arc;
  * `rho_pos_on_wrap` / `rho_max_on_wrap`: `rho` is positive on the wrap
    interior and attains its closed-interval maximum at an interior point,
    equal to the open-interval supremum;
  * `wrap_sweep_closed`: the wrap arc sweeps the WHOLE closed segment
    `[0, m]·u` (value `0` at both junction endpoints, the tip `m·u` at an
    interior point, every interior value attained).

The wrap arc completes the claim "the image of the unit circle under the
model boundary map contains every segment `[0, m_k]·u_k` of the `s`-spike
model star" (the assembly of the full `s`-spike star from the `s` arc
sweeps is the next milestone; together with the KL bridge it gives the
sharpness value `4^{1/s}` of the cap-1 model star).
-/

namespace Submission.ModelStarBoundary7

/-- The canonical circle exponential is `2π`-periodic. -/
lemma eAngle_add_two_pi (x : ℝ) : eAngle (x + 2 * Real.pi) = eAngle x := by
  unfold eAngle
  simpa [Complex.ofReal_add, add_assoc, add_comm, add_left_comm, mul_add]
    using Complex.exp_mul_I_periodic x

/-- ... and also for a `−2π` shift. -/
lemma eAngle_sub_two_pi (x : ℝ) : eAngle (x - 2 * Real.pi) = eAngle x := by
  have h1 := eAngle_add_two_pi (x - 2 * Real.pi)
  have h2 : eAngle (x - 2 * Real.pi + 2 * Real.pi) = eAngle x := by
    congr 1
    ring
  exact h1.symm.trans h2

/-- The sweep factor is `2π`-periodic in `t`. -/
lemma rho_two_pi_periodic {s : ℕ} (φ : Fin s → ℝ) (r : Fin s → ℝ) (t : ℝ) :
    rho φ r (t + 2 * Real.pi) = rho φ r t := by
  unfold rho
  apply Finset.prod_congr rfl
  intro k hk
  have harg : φ k - (t + 2 * Real.pi) = (φ k - t) - 2 * Real.pi := by ring
  rw [harg, eAngle_sub_two_pi]

/-- The boundary map `t ↦ modelF z₀ r (eAngle t)` is `2π`-periodic. -/
lemma boundaryMap_two_pi_periodic {s : ℕ} (z₀ : Fin s → ℂ) (r : Fin s → ℝ)
    (t : ℝ) : modelF z₀ r (eAngle (t + 2 * Real.pi)) = modelF z₀ r (eAngle t) := by
  rw [eAngle_add_two_pi]

/-- First junction index `⟨0, hs⟩` (angle minimum under `Monotone φ`). -/
abbrev wrapFirst (s : ℕ) (hs : 0 < s) : Fin s := ⟨0, hs⟩

/-- Last junction index `⟨s−1, ·⟩` (angle maximum under `Monotone φ`). -/
abbrev wrapLast (s : ℕ) (hs : 0 < s) : Fin s :=
  ⟨s - 1, Nat.sub_lt hs (by norm_num : (0 : ℕ) < 1)⟩

/-- The left endpoint of the wrap arc. -/
abbrev wrapA {s : ℕ} (φ : Fin s → ℝ) (hs : 0 < s) : ℝ := φ (wrapLast s hs)

/-- The right endpoint of the wrap arc (lifted by `2π`). -/
abbrev wrapB {s : ℕ} (φ : Fin s → ℝ) (hs : 0 < s) : ℝ :=
  φ (wrapFirst s hs) + 2 * Real.pi

/-- `φ (wrapLast s hs)` is at least every `φ k` (monotone data). -/
lemma wrapLast_ge {s : ℕ} (hs : 0 < s) {φ : Fin s → ℝ} (hmono : Monotone φ)
    (k : Fin s) : φ k ≤ φ (wrapLast s hs) := by
  have hkle : k ≤ wrapLast s hs := by
    rw [Fin.le_def]
    dsimp [wrapLast]
    omega
  exact hmono hkle

/-- `φ (wrapFirst s hs)` is at most every `φ k` (monotone data). -/
lemma wrapFirst_le {s : ℕ} (hs : 0 < s) {φ : Fin s → ℝ} (hmono : Monotone φ)
    (k : Fin s) : φ (wrapFirst s hs) ≤ φ k := by
  have h0le : wrapFirst s hs ≤ k := by
    rw [Fin.le_def]
    dsimp [wrapFirst]
    exact Nat.zero_le k.val
  exact hmono h0le

/-- The wrap interval is nonempty: `wrapA < wrapB`. -/
lemma wrapA_lt_wrapB {s : ℕ} (hs : 0 < s) {φ : Fin s → ℝ}
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi) :
    wrapA φ hs < wrapB φ hs := by
  have h1 : φ (wrapLast s hs) < 2 * Real.pi := hφhi (wrapLast s hs)
  have h2 : 0 ≤ φ (wrapFirst s hs) := hφlo (wrapFirst s hs)
  dsimp [wrapA, wrapB]
  linarith

/-- On the interior of the wrap interval all junctions lie to the LEFT of
`t` (every `φ k < t`), so `dirSign = +1` everywhere there. -/
lemma dirSign_wrap {s : ℕ} (hs : 0 < s) {φ : Fin s → ℝ} (hmono : Monotone φ)
    {t : ℝ} (ht : t ∈ Ioo (wrapA φ hs) (wrapB φ hs)) (k : Fin s) :
    φ k < t := by
  have h1 : φ k ≤ φ (wrapLast s hs) := wrapLast_ge hs hmono k
  have h2 : φ (wrapLast s hs) < t := ht.1
  exact lt_of_le_of_lt h1 h2

/-- The direction of the wrap ray: `u := eAngle (Σ_k r_k φ_k + π)` (all
junctions passed; `Σ r k = 1`). -/
abbrev wrapRayDir {s : ℕ} (r φ : Fin s → ℝ) : ℂ :=
  eAngle ((∑ k : Fin s, r k * φ k) + Real.pi)

/-- `‖u‖ = 1` for the wrap ray direction. -/
lemma wrapRayDir_unit {s : ℕ} (r φ : Fin s → ℝ) : ‖wrapRayDir r φ‖ = 1 := by
  dsimp [wrapRayDir]
  exact eAngle_norm _

/-- The direction sum collapses to `Σ r_k φ_k + π` when every junction is
passed (`dirSign = +1` for all `k`). -/
lemma dirSum_wrap {s : ℕ} (r φ : Fin s → ℝ) {t : ℝ}
    (hsig : ∀ k : Fin s, dirSign φ t k = 1)
    (hsum : (∑ k : Fin s, r k) = 1) :
    (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k))) =
      (∑ k : Fin s, r k * φ k) + Real.pi := by
  calc
    (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k)))
        = (∑ k : Fin s, (r k * φ k + r k * (Real.pi * 1))) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hsig k]
            ring
    _ = (∑ k : Fin s, r k * φ k) + Real.pi * (∑ k : Fin s, r k) := by
            rw [Finset.sum_add_distrib]
            congr 1
            calc
              (∑ k : Fin s, r k * (Real.pi * 1))
                  = (∑ k : Fin s, Real.pi * r k) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      ring
              _ = Real.pi * (∑ k : Fin s, r k) := by
                      rw [← Finset.mul_sum]
    _ = (∑ k : Fin s, r k * φ k) + Real.pi := by
            rw [hsum]
            ring
/-- Direction sum when every junction is UNPASSED (`dirSign = −1` for all
`k`): the ray angle is `Σ r_k φ_k − π`. -/
lemma dirSum_wrap_neg {s : ℕ} (r φ : Fin s → ℝ) {t : ℝ}
    (hsig : ∀ k : Fin s, dirSign φ t k = -1)
    (hsum : (∑ k : Fin s, r k) = 1) :
    (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k))) =
      (∑ k : Fin s, r k * φ k) - Real.pi := by
  calc
    (∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t k)))
        = (∑ k : Fin s, (r k * φ k + r k * (Real.pi * -1))) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hsig k]
            ring
    _ = (∑ k : Fin s, r k * φ k) + (∑ k : Fin s, r k * (Real.pi * -1)) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ k : Fin s, r k * φ k) + (∑ k : Fin s, r k) * (Real.pi * -1) := by
            rw [← Finset.sum_mul]
    _ = (∑ k : Fin s, r k * φ k) + (1 : ℝ) * (Real.pi * -1) := by
            rw [hsum]
    _ = (∑ k : Fin s, r k * φ k) - Real.pi := by
            ring

/-- Ray identity on the FIRST half of the wrap arc, `t ∈ (φ (s−1), 2π)`
(all junctions passed): `b(t) = ρ(t)·u` with the wrap direction
`u := eAngle (Σ r_k φ_k + π)`. -/
lemma wrap_first_half_ray {s : ℕ} (hs : 0 < s) (z₀ : Fin s → ℂ) (r φ : Fin s → ℝ)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    {t : ℝ} (hta : wrapA φ hs < t) (ht2 : t < 2 * Real.pi) :
    modelF z₀ r (eAngle t) = (rho φ r t : ℂ) * wrapRayDir r φ := by
  have ht0 : 0 < t := lt_of_le_of_lt (hφlo (wrapLast s hs)) hta
  have htne : ∀ k : Fin s, φ k ≠ t := by
    intro k
    exact ne_of_lt (lt_of_le_of_lt (wrapLast_ge hs hmono k) hta)
  have hpass : ∀ k : Fin s, φ k < t := by
    intro k
    exact lt_of_le_of_lt (wrapLast_ge hs hmono k) hta
  have hsig : ∀ k : Fin s, dirSign φ t k = 1 := by
    intro k
    unfold dirSign
    rw [if_pos (hpass k)]
  have hdir := dirSum_wrap r φ (t := t) hsig hsum
  have ray := ModelStarBoundary2.modelF_boundary_ray z₀ r φ hz₀e hφlo hφhi hsum
    (t := t) ht0 ht2 htne
  -- ray : modelF ... = (rho t : ℂ) * eAngle (Σ rk(φk + π·dirSign))
  rw [ray]
  rw [hdir]
  rfl

/-- Ray identity on the SECOND half of the wrap arc, canonical lift
`t ∈ (0, φ 0)` (no junction passed): `b(t) = ρ(t)·u` (modulo the 2π-phase
of the direction, which the canonical wrap direction `u` absorbs). -/
lemma wrap_second_half_ray {s : ℕ} (hs : 0 < s) (z₀ : Fin s → ℂ) (r φ : Fin s → ℝ)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    {t : ℝ} (ht0 : 0 < t) (htφ : t < φ (wrapFirst s hs)) :
    modelF z₀ r (eAngle t) = (rho φ r t : ℂ) * wrapRayDir r φ := by
  have ht2 : t < 2 * Real.pi := by
    exact lt_trans htφ (hφhi (wrapFirst s hs))
  have htne : ∀ k : Fin s, φ k ≠ t := by
    intro k
    have hge : φ (wrapFirst s hs) ≤ φ k := wrapFirst_le hs hmono k
    exact ne_of_gt (lt_of_lt_of_le htφ hge)
  have hnot : ∀ k : Fin s, ¬ φ k < t := by
    intro k
    have hge : φ (wrapFirst s hs) ≤ φ k := wrapFirst_le hs hmono k
    exact not_lt_of_ge (le_trans (le_of_lt htφ) hge)
  have hsig : ∀ k : Fin s, dirSign φ t k = -1 := by
    intro k
    unfold dirSign
    rw [if_neg (hnot k)]
  have hdir := dirSum_wrap_neg r φ (t := t) hsig hsum
  have ray := ModelStarBoundary2.modelF_boundary_ray z₀ r φ hz₀e hφlo hφhi hsum
    (t := t) ht0 ht2 htne
  rw [ray]
  rw [hdir]
  -- eAngle (Σ rk φk − π) = eAngle (Σ rk φk + π)  (2π-periodicity)
  have hphase : eAngle ((∑ k : Fin s, r k * φ k) - Real.pi) = wrapRayDir r φ := by
    dsimp [wrapRayDir]
    have hper := eAngle_add_two_pi ((∑ k : Fin s, r k * φ k) - Real.pi)
    have harg : ((∑ k : Fin s, r k * φ k) - Real.pi) + 2 * Real.pi =
        (∑ k : Fin s, r k * φ k) + Real.pi := by ring
    rw [harg] at hper
    exact hper.symm
  rw [hphase]
  rfl

/-- **Wrap-arc ray identity (stage-5 core).**  On the WHOLE open wrap
interval `(φ (s−1), φ 0 + 2π)` — including the point `t = 2π` where the
parameterisation crosses the branch cut — every boundary value
`modelF z₀ r (eAngle t)` lies on the single fixed unit ray
`u := eAngle (Σ_k r_k φ_k + π)` at distance `rho φ r t`. -/
theorem wrap_ray {s : ℕ} (hs : 0 < s) (z₀ : Fin s → ℂ) (r φ : Fin s → ℝ)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    (hr : ∀ k : Fin s, 0 ≤ r k) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      ∀ t : ℝ, t ∈ Ioo (wrapA φ hs) (wrapB φ hs) →
        modelF z₀ r (eAngle t) = (rho φ r t : ℂ) * u := by
  refine ⟨wrapRayDir r φ, wrapRayDir_unit r φ, ?_⟩
  intro t ht
  by_cases ht2 : t = 2 * Real.pi
  · -- t = 2π: the branch-cut point.  Needs φ 0 > 0; take the limit of the
    -- second-half ray identity as s0 → 0⁺.
    have hφ0pos : 0 < φ (wrapFirst s hs) := by
      have hlt : 2 * Real.pi < φ (wrapFirst s hs) + 2 * Real.pi := by
        simpa [ht2, wrapB] using ht.2
      linarith
    have hz₀u : ∀ k : Fin s, ‖z₀ k‖ = 1 := by
      intro k
      rw [hz₀e k]
      exact eAngle_norm _
    have hzjn : ∀ k : Fin s, z₀ k ≠ eAngle 0 := by
      intro k
      have hposk : 0 < φ k := lt_of_lt_of_le hφ0pos (wrapFirst_le hs hmono k)
      have hargn : 0 - φ k ∈ Ioo (-2 * Real.pi) (2 * Real.pi) := by
        constructor <;> linarith [hposk, hφhi k]
      rw [hz₀e k]
      exact Submission.ModelStarBoundary6.eAngle_ne_of_mem_diff (x := φ k) (y := 0)
        hargn (ne_of_gt hposk)
    have hb0c : ContinuousAt (fun s0 : ℝ => modelF z₀ r (eAngle s0)) 0 :=
      boundaryMap_continuousAt z₀ r hz₀u (t₀ := 0) hzjn
    have hb0t : Tendsto (fun s0 : ℝ => modelF z₀ r (eAngle s0)) (𝓝[>] 0)
        (𝓝 (modelF z₀ r (eAngle 0))) :=
      hb0c.tendsto.mono_left nhdsWithin_le_nhds
    have hb2ray : ∀ s0 : ℝ, s0 ∈ Ioo 0 (φ (wrapFirst s hs)) →
        modelF z₀ r (eAngle s0) = (rho φ r s0 : ℂ) * wrapRayDir r φ := by
      intro s0 hs0
      exact wrap_second_half_ray hs z₀ r φ hz₀e hφlo hφhi hsum hmono (t := s0) hs0.1 hs0.2
    have hIoo : Ioo 0 (φ (wrapFirst s hs)) ∈ 𝓝[>] 0 := by
      rw [nhdsWithin, mem_inf_iff]
      refine ⟨Iio (φ (wrapFirst s hs)), isOpen_Iio.mem_nhds hφ0pos, Ioi 0, ?_, ?_⟩
      · exact Filter.mem_principal.mpr Subset.rfl
      · ext y
        simp [Ioo, Iio, Ioi, and_comm]
    have hev2 : (fun s0 : ℝ => modelF z₀ r (eAngle s0)) =ᶠ[𝓝[>] 0]
        (fun s0 : ℝ => (rho φ r s0 : ℂ) * wrapRayDir r φ) := by
      exact Filter.mem_of_superset hIoo (by
        intro s0 hs0
        exact hb2ray s0 hs0)
    have hcontOfReal : ContinuousAt (fun x : ℝ => (x : ℂ)) (rho φ r 0) :=
      Complex.continuous_ofReal.continuousAt
    have hrhoc : ContinuousAt (fun s0 : ℝ => rho φ r s0) 0 := rho_continuousAt φ r hr 0
    have hlimrho : Tendsto (fun s0 : ℝ => ((rho φ r s0 : ℝ) : ℂ) * wrapRayDir r φ)
        (𝓝[>] 0) (𝓝 (((rho φ r 0 : ℝ) : ℂ) * wrapRayDir r φ)) :=
      ((hcontOfReal.comp hrhoc).mul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds
    have hbEq : Tendsto (fun s0 : ℝ => modelF z₀ r (eAngle s0)) (𝓝[>] 0)
        (𝓝 (((rho φ r 0 : ℝ) : ℂ) * wrapRayDir r φ)) := by
      exact Filter.Tendsto.congr' hev2.symm hlimrho
    have huniq : modelF z₀ r (eAngle 0) = ((rho φ r 0 : ℝ) : ℂ) * wrapRayDir r φ :=
      tendsto_nhds_unique hb0t hbEq
    have hbper : modelF z₀ r (eAngle (2 * Real.pi)) = modelF z₀ r (eAngle 0) := by
      have hp := boundaryMap_two_pi_periodic z₀ r (t := 0)
      have hz : 0 + 2 * Real.pi = 2 * Real.pi := by ring
      simpa [hz] using hp
    have hrhoper : rho φ r (2 * Real.pi) = rho φ r 0 := by
      have hp := rho_two_pi_periodic φ r (t := 0)
      have hz : 0 + 2 * Real.pi = 2 * Real.pi := by ring
      simpa [hz] using hp
    rw [ht2, hbper, hrhoper]
    exact huniq
  · -- t ≠ 2π: split into the two halves of the wrap arc
    have hltgt : t < 2 * Real.pi ∨ 2 * Real.pi < t := lt_or_gt_of_ne ht2
    rcases hltgt with htlt | htgt
    · -- first half: t ∈ (φ (s−1), 2π)
      exact wrap_first_half_ray hs z₀ r φ hz₀e hφlo hφhi hsum hmono (t := t) ht.1 htlt
    · -- second half: t = (t − 2π) + 2π with t − 2π ∈ (0, φ 0)
      let t' : ℝ := t - 2 * Real.pi
      have ht'0 : 0 < t' := by
        dsimp [t']
        linarith
      have ht'φ : t' < φ (wrapFirst s hs) := by
        dsimp [t']
        linarith [ht.2]
      have hray' : modelF z₀ r (eAngle t') = (rho φ r t' : ℂ) * wrapRayDir r φ :=
        wrap_second_half_ray hs z₀ r φ hz₀e hφlo hφhi hsum hmono (t := t') ht'0 ht'φ
      have htdef : t = t' + 2 * Real.pi := by
        dsimp [t']
        ring
      have hbper' : modelF z₀ r (eAngle t) = modelF z₀ r (eAngle t') := by
        rw [htdef]
        exact boundaryMap_two_pi_periodic z₀ r (t := t')
      have hrhoper' : rho φ r t = rho φ r t' := by
        rw [htdef]
        exact rho_two_pi_periodic φ r (t := t')
      rw [hbper', hrhoper']
      exact hray'

/-- The sweep factor tends to `0` at the LEFT endpoint of the wrap interval
(`t → φ (s−1)⁺`), for a positive-weight last junction. -/
lemma rho_tendsto_wrapA {s : ℕ} (hs : 0 < s) {φ : Fin s → ℝ} (r : Fin s → ℝ)
    (hr : ∀ k : Fin s, 0 ≤ r k) (hrlast : 0 < r (wrapLast s hs)) :
    Tendsto (fun t : ℝ => rho φ r t) (𝓝[>] (wrapA φ hs)) (𝓝 0) := by
  dsimp [wrapA]
  exact (rho_tendsto_junction_zero φ r hr (j := wrapLast s hs) hrlast).mono_left
    nhdsWithin_le_nhds

/-- The sweep factor tends to `0` at the RIGHT endpoint of the wrap interval
(`t → (φ 0 + 2π)⁻`), for a positive-weight first junction. -/
lemma rho_tendsto_wrapB {s : ℕ} (hs : 0 < s) {φ : Fin s → ℝ} (r : Fin s → ℝ)
    (hr : ∀ k : Fin s, 0 ≤ r k) (hrfirst : 0 < r (wrapFirst s hs)) :
    Tendsto (fun t : ℝ => rho φ r t) (𝓝[<] (wrapB φ hs)) (𝓝 0) := by
  -- reduce by 2π-periodicity to the junction limit at φ 0
  have hzero := rho_tendsto_junction_zero φ r hr (j := wrapFirst s hs) hrfirst
  have hshift : Tendsto (fun t : ℝ => t - 2 * Real.pi) (𝓝[<] (wrapB φ hs))
      (𝓝 (φ (wrapFirst s hs))) := by
    have hc : Continuous (fun t : ℝ => t - 2 * Real.pi) := continuous_id.sub continuous_const
    dsimp [wrapB]
    simpa using (hc.tendsto (φ (wrapFirst s hs) + 2 * Real.pi)).mono_left
      nhdsWithin_le_nhds
  have hcomp : Tendsto (fun t : ℝ => rho φ r (t - 2 * Real.pi))
      (𝓝[<] (wrapB φ hs)) (𝓝 0) := hzero.comp hshift
  have hpoint : (fun t : ℝ => rho φ r (t - 2 * Real.pi)) =ᶠ[𝓝[<] (wrapB φ hs)]
      (fun t : ℝ => rho φ r t) := by
    refine Filter.Eventually.of_forall ?_
    intro t
    have hp := rho_two_pi_periodic φ r (t - 2 * Real.pi)
    have hz : (t - 2 * Real.pi) + 2 * Real.pi = t := by ring
    simpa [hz] using hp.symm
  exact Filter.Tendsto.congr' hpoint hcomp

/-- **Wrap-arc interior sweep (stage-5 core).**  Every interior value of the
wrap-arc sweep factor below its supremum is attained: for
`m := sSup (rho φ r '' Ioo (wrapA) (wrapB))`, each `0 < x < m` is realised as
`rho φ r t = x` at some `t` of the wrap interval, and the boundary map
there takes the value `x·u` on the fixed wrap ray. -/
theorem wrap_sweep_open {s : ℕ} (hs : 0 < s) (z₀ : Fin s → ℂ) (r φ : Fin s → ℝ)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    (hr : ∀ k : Fin s, 0 ≤ r k)
    (hrlast : 0 < r (wrapLast s hs)) (hrfirst : 0 < r (wrapFirst s hs)) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      ∀ x : ℝ, 0 < x →
        x < sSup (rho φ r '' Ioo (wrapA φ hs) (wrapB φ hs)) →
        ∃ t : ℝ, t ∈ Ioo (wrapA φ hs) (wrapB φ hs) ∧
          modelF z₀ r (eAngle t) = (x : ℂ) * u := by
  classical
  let a : ℝ := wrapA φ hs
  let b : ℝ := wrapB φ hs
  have hab : a < b := by
    dsimp [a, b]
    exact wrapA_lt_wrapB hs hφlo hφhi
  rcases (wrap_ray hs z₀ r φ hz₀e hφlo hφhi hsum hmono hr) with ⟨u, hu1, hu2⟩
  have hrhoGlob : Continuous (fun t : ℝ => rho φ r t) :=
    continuous_iff_continuousAt.2 (fun t => rho_continuousAt φ r hr t)
  have hp : ContinuousOn (fun t : ℝ => rho φ r t) (Ioo a b) := hrhoGlob.continuousOn
  have hBdd : BddAbove (rho φ r '' Ioo a b) := by
    refine ⟨∏ k : Fin s, (2 : ℝ) ^ (2 * r k), ?_⟩
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact Submission.ModelStarBoundary5.rho_le_uniform_bound φ r hr t
  have hpa : Tendsto (fun t : ℝ => rho φ r t) (𝓝[>] a) (𝓝 0) := by
    simpa [a] using rho_tendsto_wrapA hs r hr hrlast
  have hpb : Tendsto (fun t : ℝ => rho φ r t) (𝓝[<] b) (𝓝 0) := by
    simpa [b] using rho_tendsto_wrapB hs r hr hrfirst
  refine ⟨u, hu1, ?_⟩
  intro x hx0 hxm
  have hsweep := Commons.Analysis.Interval.surjOn_Ioo_zero_sSup (p := fun t : ℝ => rho φ r t)
    (a := a) (b := b) hab hp hBdd hpa hpb x hx0 hxm
  rcases hsweep with ⟨t, ht, hpt⟩
  refine ⟨t, ht, ?_⟩
  have hF := hu2 t ht
  rw [hF, hpt]

/-- On the interior of the wrap interval every factor base is nonzero, so
`rho` is strictly positive there (positive weights). -/
lemma rho_pos_on_wrap {s : ℕ} (hs : 0 < s) (φ : Fin s → ℝ) (r : Fin s → ℝ)
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hmono : Monotone φ) (hr : ∀ k : Fin s, 0 ≤ r k)
    {t : ℝ} (ht : t ∈ Ioo (wrapA φ hs) (wrapB φ hs)) : 0 < rho φ r t := by
  have hfac : ∀ k : Fin s, 0 < ‖1 - eAngle (φ k - t)‖ ^ (2 * r k) := by
    intro k
    have hlt : φ k - t < 0 := by
      have h1 : φ k ≤ φ (wrapLast s hs) := wrapLast_ge hs hmono k
      have h2 : φ (wrapLast s hs) < t := ht.1
      linarith
    have hgt : -2 * Real.pi < φ k - t := by
      have h1 : t < φ (wrapFirst s hs) + 2 * Real.pi := ht.2
      have h2 : φ (wrapFirst s hs) ≤ φ k := wrapFirst_le hs hmono k
      linarith
    have hne0 : φ k - t ≠ 0 := ne_of_lt hlt
    have hbase : ‖1 - eAngle (φ k - t)‖ ≠ 0 := by
      have hxhi2 : φ k - t < 2 * Real.pi := by linarith
      have hn : 1 - eAngle (φ k - t) ≠ 0 := by
        simpa [eAngle] using
          (ModelStarBoundary2.one_sub_exp_mul_I_ne_zero_of_Ioo (x := φ k - t) hgt hxhi2 hne0)
      exact norm_ne_zero_iff.mpr hn
    exact Real.rpow_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hbase)) (2 * r k)
  unfold rho
  exact Finset.prod_pos (s := (Finset.univ : Finset (Fin s)))
    (f := fun k : Fin s => ‖1 - eAngle (φ k - t)‖ ^ (2 * r k))
    (by intro k hk; exact hfac k)

/-- On the closed wrap interval `rho` attains its maximum at an interior
point, equal to the supremum over the open wrap interval (positive-weight
endpoint junctions). -/
theorem rho_max_on_wrap {s : ℕ} (hs : 0 < s) (φ r : Fin s → ℝ)
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hmono : Monotone φ) (hr : ∀ k : Fin s, 0 ≤ r k)
    (hrlast : 0 < r (wrapLast s hs)) (hrfirst : 0 < r (wrapFirst s hs)) :
    ∃ t₀ : ℝ, t₀ ∈ Ioo (wrapA φ hs) (wrapB φ hs) ∧
      (∀ t : ℝ, t ∈ Icc (wrapA φ hs) (wrapB φ hs) → rho φ r t ≤ rho φ r t₀) ∧
      rho φ r t₀ = sSup (rho φ r '' Ioo (wrapA φ hs) (wrapB φ hs)) := by
  classical
  let a : ℝ := wrapA φ hs
  let b : ℝ := wrapB φ hs
  let f : ℝ → ℝ := fun t : ℝ => rho φ r t
  let m : ℝ := sSup (f '' Ioo a b)
  have hab : a < b := by
    dsimp [a, b]
    exact wrapA_lt_wrapB hs hφlo hφhi
  have hSne : (Icc a b).Nonempty := ⟨a, mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩⟩
  have hfcontS : ContinuousOn f (Icc a b) := by
    dsimp [f]
    exact (continuous_iff_continuousAt.2 (fun t => rho_continuousAt φ r hr t)).continuousOn
  rcases (isCompact_Icc.exists_isMaxOn hSne hfcontS) with ⟨x₀, hx₀S, hx₀max⟩
  have hmid : (a + b) / 2 ∈ Ioo a b := by
    constructor <;> nlinarith [hab]
  have hmidS : (a + b) / 2 ∈ Icc a b := mem_Icc.mpr ⟨le_of_lt hmid.1, le_of_lt hmid.2⟩
  have hmidpos : 0 < f ((a + b) / 2) := by
    dsimp [f]
    exact rho_pos_on_wrap hs φ r hφlo hφhi hmono hr (t := (a + b) / 2)
      (by simpa [a, b] using hmid)
  have hx₀max' : ∀ y : ℝ, y ∈ Icc a b → f y ≤ f x₀ := by
    have hev : ∀ᶠ y in Filter.principal (Icc a b), f y ≤ f x₀ := hx₀max
    exact Filter.eventually_principal.mp hev
  have hfx0pos : 0 < f x₀ := lt_of_lt_of_le hmidpos (hx₀max' _ hmidS)
  have hx0ne1 : x₀ ≠ a := by
    intro hx
    have hval : f x₀ = 0 := by
      dsimp [f]
      rw [hx]
      dsimp [a]
      exact rho_junction_value_zero φ r (j := wrapLast s hs) hrlast
    rw [hval] at hfx0pos
    norm_num at hfx0pos
  have hx0ne2 : x₀ ≠ b := by
    intro hx
    have hval : f x₀ = 0 := by
      dsimp [f]
      rw [hx]
      dsimp [b]
      have hp := rho_two_pi_periodic φ r (t := φ (wrapFirst s hs))
      have hz : φ (wrapFirst s hs) + 2 * Real.pi = φ (wrapFirst s hs) + 2 * Real.pi := rfl
      have hb0 : rho φ r (φ (wrapFirst s hs) + 2 * Real.pi) = 0 := by
        simpa [hp, rho_junction_value_zero φ r (j := wrapFirst s hs) hrfirst]
      exact hb0
    rw [hval] at hfx0pos
    norm_num at hfx0pos
  have hx0S' : a ≤ x₀ ∧ x₀ ≤ b := mem_Icc.mp hx₀S
  have hx0oo : x₀ ∈ Ioo a b :=
    mem_Ioo.mpr ⟨lt_of_le_of_ne hx0S'.1 (Ne.symm hx0ne1), lt_of_le_of_ne hx0S'.2 hx0ne2⟩
  have hBdd : BddAbove (f '' Ioo a b) := by
    refine ⟨∏ k : Fin s, (2 : ℝ) ^ (2 * r k), ?_⟩
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    dsimp [f]
    exact Submission.ModelStarBoundary5.rho_le_uniform_bound φ r hr t
  have hm1 : f x₀ ≤ m := by
    dsimp [m]
    exact le_csSup hBdd ⟨x₀, hx0oo, rfl⟩
  have hm2 : m ≤ f x₀ := by
    dsimp [m]
    refine csSup_le ⟨f x₀, x₀, hx0oo, rfl⟩ ?_
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    have htS : t ∈ Icc a b := mem_Icc.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact hx₀max' t htS
  have hm : f x₀ = m := le_antisymm hm1 hm2
  refine ⟨x₀, ?_, ?_, ?_⟩
  · simpa [a, b] using hx0oo
  · intro t ht
    exact hx₀max' t (by simpa [a, b] using ht)
  · dsimp [f] at hm ⊢
    dsimp [m] at hm ⊢
    simpa [a, b] using hm

/-- **Wrap-arc closed sweep (stage-5 conclusion).**  The wrap arc (from the
last junction through the angle `2π` back to the first junction) sweeps the
whole closed segment `[0, m]·u`: every `x·u` with `0 ≤ x ≤ m` is attained
at some `t` of the closed wrap interval (tip at an interior point, value
`0` at the two endpoint junctions). -/
theorem wrap_sweep_closed {s : ℕ} (hs : 0 < s) (z₀ : Fin s → ℂ) (r φ : Fin s → ℝ)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    (hr : ∀ k : Fin s, 0 ≤ r k)
    (hrlast : 0 < r (wrapLast s hs)) (hrfirst : 0 < r (wrapFirst s hs)) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      ∀ x : ℝ, x ∈ Icc 0 (sSup (rho φ r '' Ioo (wrapA φ hs) (wrapB φ hs))) →
        ∃ t : ℝ, t ∈ Icc (wrapA φ hs) (wrapB φ hs) ∧
          modelF z₀ r (eAngle t) = (x : ℂ) * u := by
  classical
  let a : ℝ := wrapA φ hs
  let b : ℝ := wrapB φ hs
  let m : ℝ := sSup (rho φ r '' Ioo a b)
  have hab : a < b := by
    dsimp [a, b]
    exact wrapA_lt_wrapB hs hφlo hφhi
  rcases (wrap_ray hs z₀ r φ hz₀e hφlo hφhi hsum hmono hr) with ⟨u, hu1, hu2⟩
  rcases (rho_max_on_wrap hs φ r hφlo hφhi hmono hr hrlast hrfirst)
    with ⟨t₀, ht₀oo, ht₀max, ht₀m⟩
  have hrhoGlob : Continuous (fun t : ℝ => rho φ r t) :=
    continuous_iff_continuousAt.2 (fun t => rho_continuousAt φ r hr t)
  have hp : ContinuousOn (fun t : ℝ => rho φ r t) (Ioo a b) := hrhoGlob.continuousOn
  have hBdd : BddAbove (rho φ r '' Ioo a b) := by
    refine ⟨∏ k : Fin s, (2 : ℝ) ^ (2 * r k), ?_⟩
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact Submission.ModelStarBoundary5.rho_le_uniform_bound φ r hr t
  have hpa : Tendsto (fun t : ℝ => rho φ r t) (𝓝[>] a) (𝓝 0) := by
    simpa [a] using rho_tendsto_wrapA hs r hr hrlast
  have hpb : Tendsto (fun t : ℝ => rho φ r t) (𝓝[<] b) (𝓝 0) := by
    simpa [b] using rho_tendsto_wrapB hs r hr hrfirst
  refine ⟨u, hu1, ?_⟩
  intro x hx
  have hx0le : 0 ≤ x := (mem_Icc.mp hx).1
  have hxle : x ≤ m := by
    simpa [m] using (mem_Icc.mp hx).2
  by_cases hx0 : x = 0
  · refine ⟨a, ?_, ?_⟩
    · exact mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩
    · rw [hx0]
      simp
      dsimp [a]
      exact Submission.ModelStarBoundary6.modelF_junction_value_zero z₀ r φ hz₀e
        (j := wrapLast s hs) hrlast
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
      have hsweep := Commons.Analysis.Interval.surjOn_Ioo_zero_sSup
        (p := fun t : ℝ => rho φ r t) (a := a) (b := b) hab hp hBdd hpa hpb x hxpos hxltm
      rcases hsweep with ⟨t, ht, hpt⟩
      refine ⟨t, ?_, ?_⟩
      · exact mem_Icc.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      · have hF := hu2 t ht
        rw [hF, hpt]
