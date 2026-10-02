/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.exitTrackedWindow_of_lockstep` — the lock-step transit delivers the
bounded-window exit tracking

The uniform lock-step transit `Work.PARIMPL2.LockstepAll` states, for *every* bounded box
`X₁ ≤ Re φa ≤ X₁ + W`, `|Im φa| ≤ H` of the attracting coordinate and every bounded exit
window `−Xo ≤ Re u < −1`, that the `n`-th iterate of any point `y'` within `ρ` of a box point
`y ∈ Pa` sits within `η` of `Ψ (trans c − nIn − v + n + φa y)`.

Here we draw from it the **bounded-window exit tracking** `Work.PARIMPL2.ExitTrackedWindow`:
for every window `−Xo ≤ · < −1` with `1 < Xo` and every integer level `trans c + k` of the
repelling coordinate lying in it, some iterate of the critical orbit of `c` sits within `η` of
`Ψ (trans c + k)`, uniformly for `c` in a neighbourhood of `c₀` inside `Nm`.

The phase bookkeeping is the one of `NOTES_LEAD_mandelbar_gate2transport.md` §5:

* the box point is the **entry point of the `c₀`-orbit**, `y := (Ft c₀)^[nIn] c₀` — it lies in
  `Pa` by `hentry` and its attracting coordinate is `φa y = v + nIn` by the definition of `v`
  and the vanishing of the critical height `hcrit` (`|Im φa y| = 0`);
* hence the tracked level is `u = trans c − nIn − v + n + φa y = trans c + n`, i.e. the orbit
  point at time `nIn + k` sits at `≈ Ψ (trans c + k)` — exactly PARIMPL's exit convention;
* the starting point of the transit is `y' := (Ft c)^[nIn] c`, the `nIn`-th iterate of the
  *critical point of `c` itself*, a `ρu`-perturbation of `y` for `c` near `c₀` by the continuity
  `hcontN nIn` of the `nIn`-th iterate;
* the blow-up `hblow` (with `R := Xo + 1`) makes the condition `−Xo ≤ (trans c + k).re < −1`
  force `k ≥ 1`, so that `n := k.toNat` is available and `(k.toNat : ℂ) = (k : ℂ)`.

The relation `hmapsTo`/`hshift` are not needed for this statement (they are used upstream, to
iterate the box point through the chain `Pa`).
-/
import Mathlib
import Submission.Work.PARIMPL2.ExitTracking

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PARIMPL2

theorem exitTrackedWindow_of_lockstep {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {nIn : ℕ}
    {Ft : ℂ → ℂ → ℂ} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {v : ℝ}
    (hUT : Work.PARIMPL2.LockstepAll c₀ Nm trans nIn Ft Pa φa Ψ v)
    (hmapsTo : Set.MapsTo (Ft c₀) Pa Pa)
    (hshift : ∀ z ∈ Pa, φa (Ft c₀ z) = φa z + 1)
    (hentry : (Ft c₀)^[nIn] c₀ ∈ Pa)
    (hcrit : (φa ((Ft c₀)^[nIn] c₀)).im = 0)
    (hv : v = (φa ((Ft c₀)^[nIn] c₀)).re - (nIn : ℝ))
    (hblow : ∀ R : ℝ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, (trans c).re ≤ -R)
    (hcontN : ∀ N : ℕ, ContinuousAt (fun c : ℂ => (Ft c)^[N] c) c₀) :
    Work.PARIMPL2.ExitTrackedWindow c₀ Nm trans Ft Ψ := by
  intro Xo hXo η hη
  -- the blow-up radius, at depth `Xo + 1`, forces every window level `k` to satisfy `k ≥ 1`
  obtain ⟨ρb, hρb, hblow'⟩ := hblow (Xo + 1)
  -- the lock-step transit in the box `[v + nIn, v + nIn + 1]`, `Im φa = 0`
  obtain ⟨ρu, hρu, hUT'⟩ := hUT 0 1 Xo η (v + nIn) hη
  -- the `nIn`-th iterate is continuous at `c₀`: its `δ`-ball is a `ρu`-neighbourhood of the box point
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp (hcontN nIn) ρu hρu
  refine ⟨min ρb (min ρu δ), lt_min hρb (lt_min hρu hδpos), ?_⟩
  intro c hc k hk1 hk2
  have hcNm : c ∈ Nm := hc.1
  have hcball : c ∈ Metric.ball c₀ (min ρb (min ρu δ)) := hc.2
  have hcbρb : c ∈ Nm ∩ Metric.ball c₀ ρb :=
    ⟨hcNm, Metric.ball_subset_ball (min_le_left _ _) hcball⟩
  have hcbρu : c ∈ Nm ∩ Metric.ball c₀ ρu :=
    ⟨hcNm, Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) hcball⟩
  have hcbδ : c ∈ Metric.ball c₀ δ :=
    Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _)) hcball
  -- `k ≥ 1`: the level sits in the bounded window, the transit coordinate is at depth `Xo + 1`
  have hkre : (trans c + (k : ℂ)).re = (trans c).re + (k : ℝ) := by simp
  have hkr : (1 : ℝ) ≤ (k : ℝ) := by
    have := hblow' c hcbρb
    linarith
  have hk0 : (0 : ℤ) ≤ k := by exact_mod_cast (le_trans zero_le_one hkr)
  -- the entry point of the `c₀`-orbit is the box point `y`, at the level `v + nIn`
  have hφre : (φa ((Ft c₀)^[nIn] c₀)).re = v + (nIn : ℝ) := by rw [hv]; ring
  have hφy : φa ((Ft c₀)^[nIn] c₀) = ((v + (nIn : ℝ) : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa using hφre
    · simpa using hcrit
  have hkn : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0]
  -- the tracked level is exactly `trans c + k`
  have hu : trans c - ↑nIn - ↑v + ↑k.toNat + φa ((Ft c₀)^[nIn] c₀) = trans c + (k : ℂ) := by
    rw [hφy, hkn]; push_cast; ring
  have h1 : -Xo ≤ (trans c - ↑nIn - ↑v + ↑k.toNat + φa ((Ft c₀)^[nIn] c₀)).re := by
    rw [hu]; exact hk1
  have h2 : (trans c - ↑nIn - ↑v + ↑k.toNat + φa ((Ft c₀)^[nIn] c₀)).re < -1 := by
    rw [hu]; exact hk2
  -- the `nIn`-th iterate of the critical point is within `ρu` of the box point
  have hcl : ‖(Ft c)^[nIn] c - (Ft c₀)^[nIn] c₀‖ ≤ ρu := by
    have h := hδ hcbδ
    simpa [dist_eq_norm] using h.le
  have key := hUT' c hcbρu ((Ft c₀)^[nIn] c₀) ((Ft c)^[nIn] c) k.toNat hentry
      (by rw [hφre]) (by rw [hφre]; linarith)
      (by rw [hcrit]; norm_num) hcl h1 h2
  rw [hu] at key
  -- the orbit point at time `nIn + k` is the `k`-th iterate of the `nIn`-th iterate
  exact ⟨k.toNat + nIn, by rw [Function.iterate_add_apply]; exact key⟩

end Work.PARIMPL2
