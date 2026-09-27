import Mathlib
import Submission.Work.Mostow.BdExt.bdMap
import Submission.Work.Mostow.BdExt.rayDist

/-!
# `bdMapDetect`: the boundary map is detected by *any* escaping sequence

`bdMap n Φ ξ` is defined (see `bdMap.lean`) as the limit of the directions `dirv (Φ (ray ξ t))`
along the geodesic ray to `ξ`.  This module shows that the same limit is obtained from *any*
sequence `z : ℕ → E n` that converges to `ξ` in the visual compactification of `ℍⁿ`, i.e.
`dirv (z k) → ξ` and `lvl (z k) → ∞`:

  `dirv (Φ (z k)) → bdMap n Φ ξ`.

The proof is short because of the *uniform* rate of convergence `bdMap_rate`: there is a constant
`C₄ ≥ 0` with

  `‖dirv (Φ (ray ξ' t)) - bdMap n Φ ξ'‖ ≤ C₄ · exp (-(t / (2 K)))`

*uniformly in* `ξ' ∈ Sph n`.  Every escaping sequence is of the form
`z k = ray (dirv (z k)) (lvl (z k))` (because `sinh (lvl u) • dirv u = u`), so the uniform rate
applied at `ξ' = dirv (z k)` and `t = lvl (z k)` together with the continuity of `ξ' ↦ bdMap n Φ ξ'`
on `Sph n` (`hcont`) finishes the argument, since `exp (-(lvl (z k) / (2 K))) → 0` and
`dirv (z k) → ξ`.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow Filter

theorem bdMapDetect (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (Φ : Submission.Mostow.E n → Submission.Mostow.E n) (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, Submission.Mostow.hdist (Φ u) (Φ v) ≤ K * Submission.Mostow.hdist u v + C)
    (hlow : ∀ u v, Submission.Mostow.hdist u v ≤ K * Submission.Mostow.hdist (Φ u) (Φ v) + C)
    (hcont : ContinuousOn (fun ξ : Submission.Mostow.E n => Work.Mostow.BdExt.bdMap n Φ ξ)
      (Submission.Mostow.Sph n))
    (z : ℕ → Submission.Mostow.E n) (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hz : Filter.Tendsto (fun k => Work.Mostow.BdExt.dirv (z k)) Filter.atTop (nhds ξ))
    (hzl : Filter.Tendsto (fun k => Work.Mostow.BdExt.lvl (z k)) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun k => Work.Mostow.BdExt.dirv (Φ (z k))) Filter.atTop
      (nhds (Work.Mostow.BdExt.bdMap n Φ ξ)) := by
  -- the uniform rate of convergence of `bdMap` along rays
  obtain ⟨C₄, _hC₄, hrate⟩ := bdMap_rate n hI Φ K C hK hC hup hlow
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  -- eventually the sequence is nonzero, so `dirv (z k)` is a point of `Sph n`
  have hz0 : ∀ᶠ k in atTop, z k ≠ 0 := by
    filter_upwards [hzl.eventually (eventually_ge_atTop (1 : ℝ))] with k hk h0
    rw [h0, lvl_zero] at hk
    linarith
  have hmem : ∀ᶠ k in atTop, dirv (z k) ∈ Sph n := by
    filter_upwards [hz0] with k hk
    rw [Sph, Metric.mem_sphere, dist_zero_right]
    exact norm_dirv (z k) hk
  -- the boundary map is continuous at `ξ`, so `bdMap (dirv (z k)) → bdMap ξ`
  have hbdc : Tendsto (fun k => bdMap n Φ (dirv (z k))) atTop (nhds (bdMap n Φ ξ)) :=
    Filter.Tendsto.comp (hcont.continuousWithinAt hξ) (tendsto_nhdsWithin_iff.mpr ⟨hz, hmem⟩)
  -- the exponential error tends to `0`
  have hexp : Tendsto (fun k => C₄ * Real.exp (-(lvl (z k) / (2 * K)))) atTop (nhds 0) := by
    have hlin : Tendsto (fun k => lvl (z k) / (2 * K)) atTop atTop := by
      have h := Tendsto.const_mul_atTop (r := (2 * K)⁻¹)
        (inv_pos.mpr (by positivity : (0:ℝ) < 2 * K)) hzl
      simpa only [div_eq_inv_mul] using h
    have hneg : Tendsto (fun k => -(lvl (z k) / (2 * K))) atTop atBot :=
      tendsto_neg_atBot_iff.mpr hlin
    have hexp' : Tendsto (fun k => Real.exp (-(lvl (z k) / (2 * K)))) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hneg
    simpa only [mul_zero] using hexp'.const_mul C₄
  -- the uniform estimate at `ξ' = dirv (z k)`, `t = lvl (z k)`
  have hupper : ∀ᶠ k in atTop,
      ‖dirv (Φ (ray (dirv (z k)) (lvl (z k)))) - bdMap n Φ (dirv (z k))‖ ≤
        C₄ * Real.exp (-(lvl (z k) / (2 * K))) := by
    filter_upwards [hz0, hmem] with k hk0 hkmem
    exact hrate (dirv (z k)) hkmem (lvl (z k)) (le_of_lt (lvl_pos (z k) hk0))
  have hdiff : Tendsto (fun k => dirv (Φ (ray (dirv (z k)) (lvl (z k)))) - bdMap n Φ (dirv (z k)))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
      (Eventually.of_forall (fun k => norm_nonneg _)) hupper
  -- `dirv (Φ (ray ξ_k (lvl z_k))) = (· - bdMap ξ_k) + bdMap ξ_k → 0 + bdMap ξ`
  have hmain : Tendsto (fun k => dirv (Φ (ray (dirv (z k)) (lvl (z k))))) atTop
      (nhds (bdMap n Φ ξ)) := by
    have hsum := hdiff.add hbdc
    simpa only [sub_add_cancel, zero_add] using hsum
  -- finally replace the ray by the sequence itself: `ray (dirv (z k)) (lvl (z k)) = z k`
  exact hmain.congr' (Eventually.of_forall (fun k => by
    rw [show ray (dirv (z k)) (lvl (z k)) = z k from sinh_lvl_smul_dirv (z k)]))

end Work.Mostow.BdExt
