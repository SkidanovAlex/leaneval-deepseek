import Mathlib
import Submission.Work.ParamRaysCrit.CritDomain
import Submission.Work.ParamRaysCrit.GreenLevel
import Submission.Work.ParamRaysCrit.GreenBound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRaysCrit.CritUnique

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays

/-! ## The ratio `φ / ψ` on the critical domain

The whole argument of `Work.ParamRays.isDynBottcher_unique` is transported from the escaping set
to the critical domain: `critDomain c` is `T_c`-invariant (`orbit_mem_critDomain`), preconnected
(`isPreconnected_critDomain`) and contained in the escaping set
(`critDomain_subset_escapingSet`), which is all that the orbit arguments need.
-/

/-- A critical Böttcher coordinate does not vanish on the critical domain: if `ψ z = 0` then all
even iterates of `z` (which live in `critDomain c`) are zeros of `ψ`, contradicting the
asymptotic `ψ w ~ w` at infinity. -/
theorem IsCritBottcher.ne_zero {c : ℂ} {ψ : ℂ → ℂ} (hψ : IsCritBottcher c ψ)
    {z : ℂ} (hz : z ∈ critDomain c) : ψ z ≠ 0 := by
  intro hz0
  have hzero : ∀ n : ℕ, ψ (orbit c z n) = 0 := by
    intro n
    induction n with
    | zero => simpa using hz0
    | succ n ih =>
      rw [orbit_succ, hψ.2.1 (orbit c z n) (orbit_mem_critDomain hz n), ih]
      simp
  have hcoc : Tendsto (fun n : ℕ => orbit c z n) atTop (cocompact ℂ) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by
      show Tendsto (fun n : ℕ => dist (orbit c z n) 0) atTop atTop
      rw [show (fun n : ℕ => dist (orbit c z n) 0) = fun n : ℕ => ‖orbit c z n‖ from by
        funext n; rw [dist_zero_right]]
      exact critDomain_subset_escapingSet c hz)
  have h2 : ∀ᶠ w : ℂ in cocompact ℂ, ‖ψ w - w‖ ≤ (1 / 2) * ‖w‖ := hψ.2.2 (1 / 2) (by norm_num)
  have h3 : ∀ᶠ n : ℕ in atTop, ‖ψ (orbit c z n) - orbit c z n‖ ≤ (1 / 2) * ‖orbit c z n‖ :=
    hcoc.eventually h2
  have h4 : ∀ᶠ n : ℕ in atTop, 0 < ‖orbit c z n‖ :=
    Escaping.eventually_gt (critDomain_subset_escapingSet c hz) 0
  obtain ⟨n, hn1, hn2⟩ := (h3.and h4).exists
  have hineq : ‖orbit c z n‖ ≤ ‖ψ (orbit c z n)‖ + (1 / 2) * ‖orbit c z n‖ := by
    have hsum : ψ (orbit c z n) + (orbit c z n - ψ (orbit c z n)) = orbit c z n := by ring
    calc ‖orbit c z n‖ = ‖ψ (orbit c z n) + (orbit c z n - ψ (orbit c z n))‖ := by rw [hsum]
      _ ≤ ‖ψ (orbit c z n)‖ + ‖orbit c z n - ψ (orbit c z n)‖ := norm_add_le _ _
      _ = ‖ψ (orbit c z n)‖ + ‖ψ (orbit c z n) - orbit c z n‖ := by rw [norm_sub_rev]
      _ ≤ ‖ψ (orbit c z n)‖ + (1 / 2) * ‖orbit c z n‖ := by linarith
  have hpos : 0 < ‖ψ (orbit c z n)‖ := by linarith
  rw [hzero n] at hpos
  simp at hpos

/-- The Böttcher equation for the ratio `φ / ψ` at a point of the critical domain. -/
theorem uq_T {c : ℂ} {φ ψ : ℂ → ℂ} (hφ : IsCritBottcher c φ) (hψ : IsCritBottcher c ψ)
    {z : ℂ} (hz : z ∈ critDomain c) :
    φ (Tantibar c z) / ψ (Tantibar c z) = conj (φ z / ψ z) ^ 2 := by
  rw [hφ.2.1 z hz, hψ.2.1 z hz, map_div₀, div_pow]

/-- The conjugated ratio along an orbit satisfies the squaring recurrence. -/
theorem conj_uq_orbit_succ {c : ℂ} {φ ψ : ℂ → ℂ} (hφ : IsCritBottcher c φ)
    (hψ : IsCritBottcher c ψ) {z : ℂ} (hz : z ∈ critDomain c) (k : ℕ) :
    conj (φ (orbit c z (k + 1)) / ψ (orbit c z (k + 1))) =
      (φ (orbit c z k) / ψ (orbit c z k)) ^ 2 := by
  have h1 : φ (orbit c z (k + 1)) / ψ (orbit c z (k + 1)) =
      conj (φ (orbit c z k) / ψ (orbit c z k)) ^ 2 := by
    rw [orbit_succ]
    exact uq_T hφ hψ (orbit_mem_critDomain hz k)
  rw [h1, map_pow, Complex.conj_conj]

/-- `(φ z / ψ z) ^ (2 ^ k)` equals the ratio at the `k`-th iterate, possibly conjugated. -/
theorem uq_pow_two_or {c : ℂ} {φ ψ : ℂ → ℂ} (hφ : IsCritBottcher c φ) (hψ : IsCritBottcher c ψ)
    {z : ℂ} (hz : z ∈ critDomain c) :
    ∀ k : ℕ, (φ z / ψ z) ^ (2 ^ k) = φ (orbit c z k) / ψ (orbit c z k) ∨
      (φ z / ψ z) ^ (2 ^ k) = conj (φ (orbit c z k) / ψ (orbit c z k)) := by
  intro k
  induction k with
  | zero => exact Or.inl (by simp)
  | succ k ih =>
    have hp : (φ z / ψ z) ^ (2 ^ (k + 1)) = ((φ z / ψ z) ^ (2 ^ k)) ^ 2 := by
      rw [pow_succ (2 : ℕ) k, pow_mul]
    rw [hp]
    rcases ih with h | h
    · rw [h]
      right
      rw [conj_uq_orbit_succ hφ hψ hz k]
    · rw [h]
      left
      have h2 : φ (orbit c z (k + 1)) / ψ (orbit c z (k + 1)) =
          conj (φ (orbit c z k) / ψ (orbit c z k)) ^ 2 := by
        rw [orbit_succ]
        exact uq_T hφ hψ (orbit_mem_critDomain hz k)
      rw [h2]

/-- `φ / ψ → 1` at infinity: both coordinates are asymptotic to the identity, and the asymptotic
bounds hold on a neighbourhood of infinity (so no invariance of a domain is needed). -/
theorem tendsto_uq_cocompact {c : ℂ} {φ ψ : ℂ → ℂ} (hφ : IsCritBottcher c φ)
    (hψ : IsCritBottcher c ψ) :
    Tendsto (fun w : ℂ => φ w / ψ w) (cocompact ℂ) (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := min (ε / 8) (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδle : δ ≤ 1 / 2 := min_le_right _ _
  have hδle' : δ ≤ ε / 8 := min_le_left _ _
  have hφe : ∀ᶠ w : ℂ in cocompact ℂ, ‖φ w - w‖ ≤ δ * ‖w‖ := hφ.2.2 δ hδpos
  have hψe : ∀ᶠ w : ℂ in cocompact ℂ, ‖ψ w - w‖ ≤ δ * ‖w‖ := hψ.2.2 δ hδpos
  have h1e : ∀ᶠ w : ℂ in cocompact ℂ, 1 ≤ ‖w‖ := by
    have hmem : {w : ℂ | 1 ≤ ‖w‖} ∈ cocompact ℂ := by
      rw [Filter.mem_cocompact]
      refine ⟨Metric.closedBall 0 1, isCompact_closedBall _ _, ?_⟩
      intro w hw
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hw
      exact le_of_lt hw
    exact hmem
  filter_upwards [hφe, hψe, h1e] with w hφw hψw h1w
  have hw1 : (0 : ℝ) < ‖w‖ := lt_of_lt_of_le zero_lt_one h1w
  have hψlb : (1 - δ) * ‖w‖ ≤ ‖ψ w‖ := by
    have h5 : ‖w‖ ≤ ‖ψ w‖ + ‖w - ψ w‖ := by
      calc ‖w‖ = ‖ψ w + (w - ψ w)‖ := by rw [show ψ w + (w - ψ w) = w by ring]
        _ ≤ ‖ψ w‖ + ‖w - ψ w‖ := norm_add_le _ _
    rw [norm_sub_rev w (ψ w)] at h5
    nlinarith
  have hψpos : 0 < ‖ψ w‖ := by
    have h3 : (1 / 2) * ‖w‖ ≤ (1 - δ) * ‖w‖ := by nlinarith
    have h4 : (0 : ℝ) < (1 / 2) * ‖w‖ := by positivity
    linarith
  have hψwne : ψ w ≠ 0 := norm_pos_iff.mp hψpos
  rw [dist_eq_norm, div_sub_one hψwne, norm_div, div_lt_iff₀ hψpos]
  have hnum : ‖φ w - ψ w‖ ≤ 2 * δ * ‖w‖ := by
    have h5 : ‖φ w - ψ w‖ ≤ ‖φ w - w‖ + ‖w - ψ w‖ := by
      calc ‖φ w - ψ w‖ = ‖(φ w - w) + (w - ψ w)‖ := by
            rw [show (φ w - w) + (w - ψ w) = φ w - ψ w by ring]
        _ ≤ ‖φ w - w‖ + ‖w - ψ w‖ := norm_add_le _ _
    rw [norm_sub_rev w (ψ w)] at h5
    linarith
  calc ‖φ w - ψ w‖ ≤ 2 * δ * ‖w‖ := hnum
    _ < ε * ((1 - δ) * ‖w‖) := by
          have h6 : 2 * δ < ε * (1 - δ) := by nlinarith
          nlinarith
    _ ≤ ε * ‖ψ w‖ := mul_le_mul_of_nonneg_left hψlb hε.le

/-- Along the orbit of a point of the critical domain, the ratio powers converge to `1`. -/
theorem tendsto_uq_pow_two {c : ℂ} {φ ψ : ℂ → ℂ} (hφ : IsCritBottcher c φ)
    (hψ : IsCritBottcher c ψ) {z : ℂ} (hz : z ∈ critDomain c) :
    Tendsto (fun k : ℕ => (φ z / ψ z) ^ (2 ^ k)) atTop (nhds 1) := by
  have hesc : Escaping c z := critDomain_subset_escapingSet c hz
  have hcoc : Tendsto (fun k : ℕ => orbit c z k) atTop (cocompact ℂ) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by
      show Tendsto (fun n : ℕ => dist (orbit c z n) 0) atTop atTop
      rw [show (fun n : ℕ => dist (orbit c z n) 0) = fun n : ℕ => ‖orbit c z n‖ from by
        funext n; rw [dist_zero_right]]
      exact hesc)
  have h1 : Tendsto (fun k : ℕ => φ (orbit c z k) / ψ (orbit c z k)) atTop (nhds 1) :=
    (tendsto_uq_cocompact hφ hψ).comp hcoc
  have h2 : Tendsto (fun k : ℕ => conj (φ (orbit c z k) / ψ (orbit c z k))) atTop (nhds 1) := by
    have hcc : Tendsto (fun x : ℂ => conj x) (nhds 1) (nhds 1) := by
      simpa using (Complex.continuous_conj.tendsto (1 : ℂ))
    exact hcc.comp h1
  rw [Metric.tendsto_nhds] at h1 h2 ⊢
  intro ε hε
  filter_upwards [h1 ε hε, h2 ε hε] with k hk1 hk2
  rcases uq_pow_two_or hφ hψ hz k with h | h <;> rw [h]
  · exact hk1
  · exact hk2

/-! ## Uniqueness -/

/-- **Uniqueness of the critical Böttcher coordinate.**

Two critical Böttcher coordinates of `T_c` agree on `critDomain c`.  This is what makes
`Work.ParamRays.Phi c = φ c` well defined (off the mandelbar `c ∈ critDomain c` by
`Work.ParamRays.self_mem_critDomain`).

Suggested route: copy `Work.ParamRays.isDynBottcher_unique`
(`Submission/Work/ParamRays/isDynBottcher_unique.lean`, including its auxiliary lemmas
`uq_T`, `conj_uq_orbit_succ`, `uq_pow_two_or`, `tendsto_uq_cocompact`, `tendsto_uq_pow_two`,
restated for `IsCritBottcher`), replacing everywhere
* `Work.ParamRays.escapingSet c` by `Work.ParamRays.critDomain c`,
* the hypothesis `Work.ParamRays.Escaping c z` by `z ∈ Work.ParamRays.critDomain c`,
* `Work.ParamRays.isPreconnected_escapingSet c` by `Work.ParamRays.isPreconnected_critDomain c`
  (available in `Submission.Work.ParamRaysCrit.GreenLevel`),
* the base point `Work.ParamRays.e0 c` (an escaping point) by a point of `critDomain c` of large
  norm, which exists by `Work.ParamRays.exists_mem_critDomain_gt_norm`
  (`Submission.Work.ParamRaysCrit.GreenBound`); the final step uses the cocompact limit
  `tendsto_uq_cocompact` and such a far point.
The non-vanishing of `ψ` on `critDomain c` (used to divide) is available either from
`IsCritBottcher.ne_zero` (being proved in parallel in
`Submission.Work.ParamRaysCrit.CritBottcher.IsCritBottcher_modulus`) or from a private copy of
that argument (`Submissions/Work/ParamRays/isDynBottcher_unique.lean`, proof of
`IsDynBottcher.ne_zero`). -/
theorem isCritBottcher_unique {c : ℂ} {φ ψ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsCritBottcher c φ) (hψ : Work.ParamRays.IsCritBottcher c ψ)
    {z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) : φ z = ψ z := by
  have hψne : ∀ w : ℂ, w ∈ critDomain c → ψ w ≠ 0 := fun w hw => IsCritBottcher.ne_zero hψ hw
  have hcont : ContinuousOn (fun w : ℂ => φ w / ψ w) (critDomain c) :=
    hφ.1.div hψ.1 (fun w hw => hψne w hw)
  have hpre : IsPreconnected ((fun w : ℂ => φ w / ψ w) '' critDomain c) :=
    (isPreconnected_critDomain c).image _ hcont
  have hsub : (fun w : ℂ => φ w / ψ w) '' critDomain c ⊆ {ζ : ℂ | ∃ n, ζ ^ (2 ^ n) = 1} := by
    rintro ζ ⟨w, hw, rfl⟩
    exact exists_pow_two_pow_eq_one (tendsto_uq_pow_two hφ hψ hw)
  have hsingle : (((fun w : ℂ => φ w / ψ w) '' critDomain c)).Subsingleton :=
    isPreconnected_subsingleton_of_pow_two_pow_eq_one hpre hsub
  obtain ⟨z₀, -, hz₀⟩ := exists_mem_critDomain_gt_norm c 0
  set c₀ : ℂ := φ z₀ / ψ z₀ with hc₀def
  have hval : ∀ w : ℂ, w ∈ critDomain c → φ w / ψ w = c₀ := by
    intro w hw
    exact (hsingle ⟨w, hw, rfl⟩ ⟨z₀, hz₀, rfl⟩).trans hc₀def.symm
  have hc₀ : c₀ = 1 := by
    by_contra hne
    have hpos : 0 < ‖c₀ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hev : {w : ℂ | ‖φ w / ψ w - 1‖ < ‖c₀ - 1‖} ∈ cocompact ℂ := by
      have ht : {w : ℂ | dist (φ w / ψ w) 1 < ‖c₀ - 1‖} ∈ cocompact ℂ :=
        (Metric.tendsto_nhds.mp (tendsto_uq_cocompact hφ hψ)) _ hpos
      rwa [show {w : ℂ | dist (φ w / ψ w) 1 < ‖c₀ - 1‖} =
          {w : ℂ | ‖φ w / ψ w - 1‖ < ‖c₀ - 1‖} from by
        ext w; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, dist_eq_norm]] at ht
    rw [Filter.mem_cocompact] at hev
    obtain ⟨K, hK, hKs⟩ := hev
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨w₀, hw₀norm, hw₀crit⟩ := exists_mem_critDomain_gt_norm c R
    have hw₀K : w₀ ∉ K := by
      intro hmem
      have h1 := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      linarith
    have hdist := hKs hw₀K
    simp only [Set.mem_setOf_eq] at hdist
    rw [hval w₀ hw₀crit] at hdist
    exact lt_irrefl _ hdist
  have hz1 : φ z / ψ z = 1 := by rw [hval z hz, hc₀]
  exact (div_eq_one_iff_eq (hψne z hz)).mp hz1

end Work.ParamRaysCrit.CritUnique
