import Mathlib
import Submission.Work.LandLeaves.V2Anchor.Helpers
import Submission.Work.ELTop.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-! Clash-free copy of `cluster_rayAccum_eq_singleton` (see `V2Anchor/Helpers.lean`). -/

namespace Work.LandLeaves.V2Anchor

open Classical Filter Set
open scoped Topology

/-! ## Auxiliary lemmas on the level sequence

These are the (private) monotonicity lemmas of
`Submission/Work/LandLeaves/exists_rayAccum_singleton_of_isRepelling.lean`, reproduced here so that
the window decomposition of `(1, r₀]` into the level windows `[λ(m), λ(m)^D]` is available. -/

private theorem cluster_lvlSeq_lt_self {r₀ : ℝ} (hr₀ : 1 < r₀) {D : ℕ} (hD : 2 ≤ D) (n : ℕ) :
    lvlSeq r₀ D (n + 1) < lvlSeq r₀ D n := by
  have h := lvlSeq_pow (le_of_lt (lt_trans zero_lt_one hr₀)) (by omega : D ≠ 0) n
  have h1 : 1 < lvlSeq r₀ D (n + 1) := lvlSeq_one_lt hr₀ hD (n + 1)
  have h2 : lvlSeq r₀ D (n + 1) < (lvlSeq r₀ D (n + 1)) ^ D := by
    calc lvlSeq r₀ D (n + 1) = (lvlSeq r₀ D (n + 1)) ^ 1 := (pow_one _).symm
      _ < (lvlSeq r₀ D (n + 1)) ^ D := pow_lt_pow_right₀ h1 (by omega)
  rwa [h] at h2

private theorem cluster_lvlSeq_lt_of_lt {r₀ : ℝ} (hr₀ : 1 < r₀) {D : ℕ} (hD : 2 ≤ D)
    {m n : ℕ} (h : m < n) : lvlSeq r₀ D n < lvlSeq r₀ D m := by
  obtain ⟨k, hk, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt h)
  calc lvlSeq r₀ D (m + k) ≤ lvlSeq r₀ D (m + 1) := lvlSeq_mono hr₀ hD (by omega)
    _ < lvlSeq r₀ D m := cluster_lvlSeq_lt_self hr₀ hD m

/-- Every level `t ∈ (1, λ(M)]` lies in one of the level windows `[λ(m), λ(m)^D]` with `m ≥ M`. -/
private theorem cluster_exists_window {r₀ : ℝ} (hr₀ : 1 < r₀) {D : ℕ} (hD : 2 ≤ D)
    {t : ℝ} (ht1 : 1 < t) {M : ℕ} (htM : t ≤ lvlSeq r₀ D M) :
    ∃ m : ℕ, M ≤ m ∧ t ∈ Set.Icc (lvlSeq r₀ D m) (lvlSeq r₀ D m ^ D) := by
  have hr₀pos : 0 < r₀ := lt_trans zero_lt_one hr₀
  have hex : ∃ n, lvlSeq r₀ D n ≤ t := by
    have htend := tendsto_lvlSeq hr₀pos hD
    have hev : ∀ᶠ n in atTop, lvlSeq r₀ D n < t :=
      htend.eventually (isOpen_Iio.mem_nhds ht1)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    exact ⟨N, le_of_lt (hN N le_rfl)⟩
  set m := Nat.find hex with hmdef
  have hm_le : lvlSeq r₀ D m ≤ t := Nat.find_spec hex
  have hm_ge : M ≤ m := by
    by_contra hlt
    push Not at hlt
    have h1 : lvlSeq r₀ D M < lvlSeq r₀ D m := cluster_lvlSeq_lt_of_lt hr₀ hD hlt
    linarith
  have hm_upper : t ≤ lvlSeq r₀ D m ^ D := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have hm0' : m = 0 := hm0
      have hM0 : M = 0 := by omega
      rw [hm0']
      rw [hM0] at htM
      calc t ≤ lvlSeq r₀ D 0 := htM
        _ ≤ (lvlSeq r₀ D 0) ^ D := by
            calc lvlSeq r₀ D 0 = (lvlSeq r₀ D 0) ^ 1 := (pow_one _).symm
              _ ≤ (lvlSeq r₀ D 0) ^ D :=
                  pow_le_pow_right₀ (le_of_lt (lvlSeq_one_lt hr₀ hD 0)) (by omega)
    · have hprev : ¬ (lvlSeq r₀ D (m - 1) ≤ t) :=
        Nat.find_min hex (by omega : m - 1 < m)
      push Not at hprev
      have hpow : lvlSeq r₀ D m ^ D = lvlSeq r₀ D (m - 1) := by
        conv_lhs => rw [show m = (m - 1) + 1 from by omega]
        exact lvlSeq_pow (le_of_lt (lt_trans zero_lt_one hr₀)) (by omega : D ≠ 0) (m - 1)
      rw [hpow]; exact le_of_lt hprev
  exact ⟨m, hm_ge, hm_le, hm_upper⟩

/-- If the ray of angle `θ` converges to `y` as the level tends to `1` (`LandsN`), then the
accumulation set `rayAccum` of that ray is the singleton `{y}`. -/
private theorem cluster_rayAccum_eq_singleton_of_landsN {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    {θ : ℝ} {y : ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) (h : Work.EL.LandsN hN θ y) :
    Work.Landing.rayAccum c φ θ = {y} := by
  obtain ⟨ψ, hψ, hψacc⟩ := (Work.ELTop.landsN_iff_landsAt hN hφ θ y).mp h
  rw [show Work.Landing.rayAccum c φ θ = Work.Landing.rayAccum c ψ θ from
    Work.ELTop.rayAccum_congr (fun w hw => Work.ParamRays.isDynBottcher_unique hφ hψ hw) θ, hψacc]

/-- **A tail-cluster point of an `htail`-controlled backward orbit of angles lands at `y`.**

`htail` is verbatim the second field of the conclusion of `Work.LandLeaves.exists_backward_orbit_tail`:
for every level window `Icc (lvlSeq r₀ D m) ((lvlSeq r₀ D m)^D)` with `D = 4^k` of the ray at angle
`θ n` (`n ≥ m`) the ray points are within `κ^m r` of `y`, with `0 ≤ κ < 1`.

`hx` says `x` is a limit point of the sequence `n ↦ Int.fract (θ n)`: it lies in the closure of every
tail `{Int.fract (θ n) | n ≥ N}`.

The proof is the same as the final part of
`Submission/Work/LandLeaves/exists_rayAccum_singleton_of_isRepelling.lean`: the bound `htail` is
transported to the cluster point `x` by continuity of the level-`s` ray point in the angle (valid
since `s > 1`), giving `‖rayPt hN x s - y‖ ≤ κ^m r` on the level window of index `m`; since the
windows cover `(1, r₀]` and `κ^m r → 0`, the ray of angle `x` converges to `y`, i.e.
`Work.EL.LandsN hN x y`, and `LandsN` is the same as `rayAccum = {y}`. -/
theorem cluster_rayAccum_eq_singleton {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hN : Work.EL.DynB c φ)
    {r κ r₀ : ℝ} {θ : ℕ → ℝ}
    (hk : 0 < k)
    (hr : 0 < r) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hr₀ : 1 < r₀)
    (htail : ∀ m n : ℕ, m ≤ n → ∀ s : ℝ,
        s ∈ Set.Icc (Work.LandLeaves.V2Anchor.lvlSeq r₀ (4 ^ k) m)
            ((Work.LandLeaves.V2Anchor.lvlSeq r₀ (4 ^ k) m) ^ (4 ^ k)) →
        ‖Work.EL.rayPt hN (θ n) s - y‖ ≤ κ ^ m * r)
    {x : ℝ} (hx : ∀ N : ℕ, x ∈ closure ((fun n : ℕ => Int.fract (θ n)) '' Set.Ici N)) :
    Work.Landing.rayAccum c φ x = {y} := by
  classical
  have hD2 : 2 ≤ 4 ^ k := by
    calc (2 : ℕ) ≤ 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 4) hk
  -- The bound `htail`, transported to the cluster point `x`, on each level window.
  have hwin : ∀ m : ℕ, ∀ s : ℝ,
      s ∈ Set.Icc (lvlSeq r₀ (4 ^ k) m) ((lvlSeq r₀ (4 ^ k) m) ^ (4 ^ k)) →
      ‖Work.EL.rayPt hN x s - y‖ ≤ κ ^ m * r := by
    intro m s hs
    have hs1 : 1 < s := lt_of_lt_of_le (lvlSeq_one_lt hr₀ hD2 m) hs.1
    have hcont : Continuous fun a : ℝ => Work.EL.rayPt hN a s :=
      Work.ELTop.continuous_rayPt_angle hN hs1
    have hxmem : x ∈ closure ((fun n : ℕ => Int.fract (θ n)) '' Set.Ici m) := hx m
    have hsub : (fun a : ℝ => Work.EL.rayPt hN a s) ''
          ((fun n : ℕ => Int.fract (θ n)) '' Set.Ici m)
        ⊆ Metric.closedBall y (κ ^ m * r) := by
      rintro _ ⟨a, ⟨n, hn, rfl⟩, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      show ‖Work.EL.rayPt hN (Int.fract (θ n)) s - y‖ ≤ κ ^ m * r
      rw [Work.LandLeaves.V2Anchor.rayPt_fract]
      exact htail m n hn s hs
    have hcl : Work.EL.rayPt hN x s ∈ closure ((fun a : ℝ => Work.EL.rayPt hN a s) ''
        ((fun n : ℕ => Int.fract (θ n)) '' Set.Ici m)) :=
      image_closure_subset_closure_image hcont ⟨x, hxmem, rfl⟩
    have := closure_minimal hsub Metric.isClosed_closedBall hcl
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hlandsN : Work.EL.LandsN hN x y := by
    show Tendsto (fun t : ℝ => Work.EL.rayPt hN x t) (nhdsWithin 1 (Set.Ioi 1)) (nhds y)
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have htend : Tendsto (fun m : ℕ => κ ^ m) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1
    have hev : ∀ᶠ m : ℕ in atTop, κ ^ m * r < ε := by
      have h2 : ∀ᶠ m : ℕ in atTop, κ ^ m < ε / r :=
        htend.eventually (isOpen_Iio.mem_nhds (div_pos hε hr))
      filter_upwards [h2] with m hm
      rw [lt_div_iff₀ hr] at hm
      linarith
    obtain ⟨M, hM⟩ := eventually_atTop.mp hev
    refine ⟨lvlSeq r₀ (4 ^ k) M - 1, by linarith [lvlSeq_one_lt hr₀ hD2 M],
      fun t ht1 htδ => ?_⟩
    have ht1' : (1 : ℝ) < t := by simpa using ht1
    have htM : t ≤ lvlSeq r₀ (4 ^ k) M := by
      rw [Real.dist_eq, abs_of_pos (by linarith : (0 : ℝ) < t - 1)] at htδ
      linarith
    obtain ⟨m', hm'ge, hm'mem⟩ := cluster_exists_window hr₀ hD2 ht1' htM
    have hb := hwin m' t hm'mem
    have hpow : κ ^ m' ≤ κ ^ M := pow_le_pow_of_le_one hκ0 (le_of_lt hκ1) hm'ge
    rw [dist_eq_norm]
    calc ‖Work.EL.rayPt hN x t - y‖ ≤ κ ^ m' * r := hb
      _ ≤ κ ^ M * r := mul_le_mul_of_nonneg_right hpow (le_of_lt hr)
      _ < ε := hM M le_rfl
  exact cluster_rayAccum_eq_singleton_of_landsN hφ hlandsN

end Work.LandLeaves.V2Anchor

