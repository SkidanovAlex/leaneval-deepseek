/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# Goldberg-Milnor B.1 (dynamical form): the descent along the level bands

This file is the assembly file of ledger item 6 (`Work.LANDCL.GoldbergMilnorB1`, the primitive
input of the `gm` row).  It contains the *quantitative descent* argument, which is the analytic
heart of the classical statement "the landing of a dynamic ray at a repelling periodic point is
stable under perturbation of the parameter" (Goldberg-Milnor, *Fixed points of polynomial maps
II*, Lemma B.1).

## The route (and what is proved here)

Write `T_c z = z̄² + c`, let `y` be a repelling periodic point of `T_c` (odd period `k`) which is
the landing point of the ray `R_c(θ)`, put `F = (T_c)^[2kq]` where `q` is the period of `θ` under
the angle map `angDouble^[2k]` (so that `F` fixes `y` and preserves the ray at angle `θ`), and let
`g` be the inverse branch of `F` at `y`, contracting distances to `y` by a factor `κ < 1` on a
ball `B(y,ρ)`.  Finally let `v : ℝ → ℂ` parametrise the ray by its Böttcher level
(`φ (v t) = t·rayDir θ`), so that `F (v t) = v (t^Λ)` with `Λ = 4^(kq)`.

* `descent_near` (**proved**): the *fundamental-segment identity* `g (v t) = v (t^(1/Λ))` holds
  at `t₀` as soon as `‖v t₀ - y‖ < ρ` — because both `v (t₀^(1/Λ))` and `g (v t₀)` are the unique
  preimage of `v t₀` in the ball.  This is the local ("perturbation") step: it uses only the
  local inverse branch, *not* any Koenigs linearisation.
* `propagate_interval` (**stated**): if `{P} ∩ [a,b]` is closed, `P` persists in a neighbourhood of
  each of its points, then `P` holds between any two of its points.  This turns the local
  persistence of `descent_near` into the identity on a whole level band, starting from the anchor
  at the shallow endpoint of the band (where the identity follows from the base hypothesis).
  The remaining proof is elementary: `X := {u | P on [t₁,u]}` is closed (if `u_n → u` with
  `[t₁,u_n] ⊆ P` then `u_n ∈ P`, so `u ∈ P` by closedness, and every `v < u` is eventually `≤ u_n`),
  and `sSup X` cannot be strictly below the right endpoint, since the local persistence produces a
  larger element.
* `descent_band` (**proved**): given the fundamental-segment identity and the base-band membership
  `v '' [η₀^(1/Λ), η₀] ⊆ B(y,ρ)`, the band `v '' [η₀^(Λ^-(m+1)), η₀^(Λ^-m)]` lies within `κ^m ρ` of
  `y`.  Since `η₀^(Λ^-m) → 1` and `κ^m ρ → 0`, this is exactly the stability of the landing.

The base-band membership is supplied by `Work.LandLeaves.rayAccum_entry` at the limit parameter
together with the joint continuity of the critical Böttcher coordinate
(`Work.NAKANE.continuousOn_jointVarphi_of_isCritBottcher`, applied to the family
`varphiCrit`), which gives the level-`τ` points of the perturbed rays at *fixed* levels; the
periodicity of `θ` is `Work.LandLeaves.periodicAngle_of_landsAt_isRepelling`, and the local
branch is `Work.LandLeaves.exists_local_repelling_branch`.

## Contents

* `isCritBottcher_iterate` — the Böttcher equation for the holomorphic iterate
  `φ ((T_c)^[2m] z) = (φ z)^(4^m)` on the critical domain (used for the level bookkeeping).
* `descent_near`, `propagate_interval`, `descent_band` — the descent, as described above.
* `goldbergMilnorB1StatementCheck` — the target, still `sorry` (assembly in progress).
-/
import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.dynBottcherOnlyOnMandelbar
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.NAKANE.All
import Submission.Work.Bottcher.CritBottcherExists
import Submission.Work.Landing.Land.Landing
import Submission.Work.Landing.Angle.angDouble_iterate_succ
import Submission.Work.LandLeaves.periodicAngle_landsAt_repelling
import Submission.Work.LandLeaves.landingDecay
import Submission.Work.LandLeaves.gmLocalOrder

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Set
open scoped _root_.Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The Böttcher equation for the holomorphic iterates -/

/-- **The Böttcher equation for `(T_c)^[2m]`.**  If `φ` is a critical Böttcher coordinate of
`T_c` and `z` lies in the critical domain, then `φ ((T_c)^[2m] z) = (φ z)^(4^m)`: the holomorphic
`2m`-th iterate acts on the Böttcher coordinate by the `4^m`-th power, i.e. on the *level* by
`τ ↦ τ^(4^m)` and on the *angle* by `angDouble^[2m]`. -/
theorem isCritBottcher_iterate {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsCritBottcher c φ)
    (m : ℕ) {z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    φ ((Tantibar c)^[2 * m] z) = (φ z) ^ (4 ^ m) := by
  have hmem : ∀ j : ℕ, (Tantibar c)^[j] z ∈ Work.ParamRays.critDomain c := by
    intro j
    induction j with
    | zero => simpa using hz
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact Work.ParamRays.Tantibar_mem_critDomain ih
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep : (Tantibar c)^[2 * (m + 1)] z
        = Tantibar c ((Tantibar c)^[2 * m + 1] z) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 from by ring, Function.iterate_succ_apply']
    have hodd : (Tantibar c)^[2 * m + 1] z = Tantibar c ((Tantibar c)^[2 * m] z) :=
      Function.iterate_succ_apply' _ _ _
    rw [hstep, hφ.2.1 _ (hmem (2 * m + 1)), hodd, hφ.2.1 _ (hmem (2 * m)), ih]
    simp only [map_pow, starRingEnd_apply, star_star]
    rw [← pow_mul, ← pow_mul, ← pow_succ]

/-! ## The descent along the level bands of an invariant ray

This is the analytic heart of the stability statement (Goldberg–Milnor B.1).  Let `F` be the
`2kq`-th iterate of `T_c` (holomorphic, fixing `z`), so that `F` preserves the ray at angle `θ`
and acts on the Böttcher *level* by `τ ↦ τ^Λ` (`Λ = 4^(kq)`), and let `g` be the local inverse
branch of `F` at the repelling fixed point `z`, contracting distances to `z` by a factor `κ < 1`
on the closed ball `B̄(z,ρ)`.

If the piece of the ray at levels in `[η₀^(1/Λ), η₀]` lies strictly inside `B(z,ρ)`, then the
piece at levels in `[η₀^(Λ^-(m+1)), η₀^(Λ^-m)]` lies within `κ^m ρ` of `z`.  Since
`η₀^(Λ^-m) → 1` and `κ^m ρ → 0`, every accumulation point of the ray is `z`: the landing at `z`
is *stable*.

The proof is the "fundamental segment" argument made quantitative.  With `σ t = t^(1/Λ)` the
level map of the inverse branch, the identity `g (v t) = v (σ t)` holds at the anchor `t = η₀`
(where `v (σ η₀) ∈ B̄(z,ρ)` and both sides are the unique preimage of `v η₀` in the ball), and the
set of levels at which it holds is closed (continuity) and has a neighbourhood at each of its
points (the contraction supplies a margin), hence is the whole level band. -/

/-- **Local persistence of the descent identity.**  If `g (v t) = v (t^(1/Λ))` holds at a level
`t₀ > 1` with `‖v t₀ - z‖ < ρ`, then it holds for all levels near `t₀`. -/
theorem descent_near {F : ℂ → ℂ} {z : ℂ} {Λ κ ρ : ℝ} {g : ℂ → ℂ} {v : ℝ → ℂ}
    (hΛ : 1 < Λ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hρ : 0 < ρ)
    (hv : Continuous v) (hg : Continuous g)
    (hleft : ∀ u : ℂ, ‖u - z‖ ≤ ρ → g (F u) = u)
    (hright : ∀ w : ℂ, ‖w - z‖ ≤ ρ → F (g w) = w)
    (hcontr : ∀ w : ℂ, ‖w - z‖ ≤ ρ → ‖g w - z‖ ≤ κ * ‖w - z‖)
    (hinv : ∀ t : ℝ, 1 < t → F (v t) = v (t ^ Λ))
    {t₀ : ℝ} (ht₀ : 1 < t₀) (hball : ‖v t₀ - z‖ < ρ)
    (hid : g (v t₀) = v (t₀ ^ (1 / Λ))) :
    ∀ᶠ t in 𝓝 t₀, (1 < t ∧ ‖v t - z‖ < ρ) → g (v t) = v (t ^ (1 / Λ)) := by
  have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ
  have hσpos : 0 < 1 / Λ := by positivity
  have hcont_le : Continuous fun t : ℝ => v (t ^ (1 / Λ)) :=
    hv.comp (Real.continuous_rpow_const (le_of_lt hσpos))
  have hval : ‖v (t₀ ^ (1 / Λ)) - z‖ ≤ κ * ‖v t₀ - z‖ := by
    rw [← hid]
    exact hcontr _ (le_of_lt hball)
  have hmargin : κ * ‖v t₀ - z‖ < ρ := by
    calc κ * ‖v t₀ - z‖ ≤ κ * ρ := mul_le_mul_of_nonneg_left (le_of_lt hball) hκ0
      _ = ρ * κ := by ring
      _ < ρ * 1 := mul_lt_mul_of_pos_left hκ1 hρ
      _ = ρ := mul_one ρ
  have h1 : ∀ᶠ t in 𝓝 t₀, ‖v (t ^ (1 / Λ)) - z‖ < ρ := by
    have hlt : ‖v (t₀ ^ (1 / Λ)) - z‖ < ρ := lt_of_le_of_lt hval hmargin
    have hcont2 : Continuous fun t : ℝ => ‖v (t ^ (1 / Λ)) - z‖ :=
      (hcont_le.sub continuous_const).norm
    exact hcont2.continuousAt.eventually (Iio_mem_nhds hlt)
  have h2 : ∀ᶠ t in 𝓝 t₀, ‖v t - z‖ < ρ :=
    ((hv.sub continuous_const).continuousAt.norm).eventually (Iio_mem_nhds hball)
  have h3 : ∀ᶠ t in 𝓝 t₀, 1 < t := isOpen_Ioi.mem_nhds ht₀
  filter_upwards [h1, h2, h3] with t htle htball ht1 hcond
  have ht1' : 1 < t ^ (1 / Λ) := by
    calc (1 : ℝ) = 1 ^ (1 / Λ) := (Real.one_rpow _).symm
      _ < t ^ (1 / Λ) := Real.rpow_lt_rpow (le_of_lt zero_lt_one) hcond.1 hσpos
  have hmemA : ‖v (t ^ (1 / Λ)) - z‖ ≤ ρ := le_of_lt htle
  have hmemB : ‖g (v t) - z‖ ≤ ρ := by
    calc ‖g (v t) - z‖ ≤ κ * ‖v t - z‖ := hcontr _ (le_of_lt hcond.2)
      _ ≤ κ * ρ := mul_le_mul_of_nonneg_left (le_of_lt htball) hκ0
      _ ≤ ρ := by
          calc κ * ρ ≤ 1 * ρ := mul_le_mul_of_nonneg_right (le_of_lt hκ1) (le_of_lt hρ)
            _ = ρ := one_mul ρ
  have hFA : F (v (t ^ (1 / Λ))) = v t := by
    rw [hinv (t ^ (1 / Λ)) ht1']
    congr 1
    rw [← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one hcond.1))]
    rw [div_mul_cancel₀ (1 : ℝ) (ne_of_gt hΛpos), Real.rpow_one]
  have hFB : F (g (v t)) = v t := hright _ (le_of_lt hcond.2)
  calc g (v t) = g (F (v (t ^ (1 / Λ)))) := by rw [hFA]
    _ = v (t ^ (1 / Λ)) := hleft _ hmemA

/-- **Descent along the level bands, given the fundamental-segment identity.**

Let `g` be a continuous local inverse branch of `F` at `z` on the closed ball `B̄(z,ρ)`
contracting by `κ < 1`, `F (v t) = v (t^Λ)` the invariance of the ray and
`g (v t) = v (t^(1/Λ))` the *fundamental-segment identity* (the tail of the ray is the iterated
inverse-branch image of the base piece; this is the content of `descent_near` plus
`propagate_interval`).

If the base band `v '' [η₀^(1/Λ), η₀]` lies strictly inside `B(z,ρ)`, then the band
`v '' [η₀^(Λ^-(m+1)), η₀^(Λ^-m)]` lies within `κ^m ρ` of `z`. -/
theorem descent_band {z : ℂ} {Λ κ ρ η₀ : ℝ} {g : ℂ → ℂ} {v : ℝ → ℂ}
    (hΛ : 1 < Λ) (hη : 1 < η₀) (hρ : 0 < ρ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hcontr : ∀ w : ℂ, ‖w - z‖ ≤ ρ → ‖g w - z‖ ≤ κ * ‖w - z‖)
    (hdesc : ∀ t : ℝ, 1 < t → g (v t) = v (t ^ (1 / Λ)))
    (hbase : ∀ t : ℝ, η₀ ^ (1 / Λ) ≤ t → t ≤ η₀ → ‖v t - z‖ < ρ) :
    ∀ (m : ℕ) (t : ℝ), η₀ ^ ((1 / Λ) ^ (m + 1)) ≤ t → t ≤ η₀ ^ ((1 / Λ) ^ m) →
      ‖v t - z‖ ≤ κ ^ m * ρ := by
  have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ
  have hσpos : 0 < 1 / Λ := by positivity
  have hσ1 : ∀ t : ℝ, 1 < t → 1 < t ^ (1 / Λ) := by
    intro t ht
    calc (1 : ℝ) = 1 ^ (1 / Λ) := (Real.one_rpow _).symm
      _ < t ^ (1 / Λ) := Real.rpow_lt_rpow (le_of_lt zero_lt_one) ht hσpos
  set c : ℕ → ℝ := fun m => η₀ ^ ((1 / Λ) ^ m) with hc
  have hc0 : c 0 = η₀ := by simp [hc]
  have hc1e : c 1 = η₀ ^ (1 / Λ) := by simp [hc]
  have hc1 : ∀ m : ℕ, 1 < c m := by
    intro m
    have hlt : (0 : ℝ) < (1 / Λ) ^ m := by positivity
    calc (1 : ℝ) = 1 ^ ((1 / Λ) ^ m) := (Real.one_rpow _).symm
      _ < η₀ ^ ((1 / Λ) ^ m) := Real.rpow_lt_rpow (le_of_lt zero_lt_one) hη hlt
  have hσc : ∀ m : ℕ, c (m + 1) = (c m) ^ (1 / Λ) := by
    intro m
    simp only [hc, pow_succ]
    exact Real.rpow_mul (le_of_lt (lt_trans zero_lt_one hη)) ((1 / Λ) ^ m) (1 / Λ)
  have hcc : ∀ m : ℕ, (c (m + 1)) ^ Λ = c m := by
    intro m
    rw [hσc m]
    rw [← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one (hc1 m))), one_div_mul_cancel (ne_of_gt hΛpos),
      Real.rpow_one]
  have hmono : ∀ m : ℕ, c (m + 1) < c m := by
    intro m
    rw [hσc m]
    calc c m ^ (1 / Λ) < c m ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (hc1 m) (by rw [one_div]; exact inv_lt_one_of_one_lt₀ hΛ)
      _ = c m := Real.rpow_one _
  -- the induction
  have main : ∀ m : ℕ, ∀ t ∈ Set.Icc (c (m + 1)) (c m), ‖v t - z‖ ≤ κ ^ m * ρ := by
    intro m
    induction m with
    | zero =>
      intro t ht
      have h1 : η₀ ^ (1 / Λ) ≤ t := by rw [hc1e, hc0] at ht; exact ht.1
      have h2 : t ≤ η₀ := by rw [hc1e, hc0] at ht; exact ht.2
      simpa using le_of_lt (hbase t h1 h2)
    | succ m ih =>
      intro t ht
      have ht1 : 1 < t := lt_of_lt_of_le (hc1 (m + 2)) ht.1
      have hmem : t ^ Λ ∈ Set.Icc (c (m + 1)) (c m) := by
        constructor
        · calc c (m + 1) ≤ (c (m + 2)) ^ Λ := le_of_eq (hcc (m + 1)).symm
            _ ≤ t ^ Λ := Real.rpow_le_rpow (x := c (m + 2)) (y := t) (z := Λ) (le_of_lt (lt_trans zero_lt_one (hc1 (m + 2)))) ht.1 (le_of_lt hΛpos)
        · calc t ^ Λ ≤ (c (m + 1)) ^ Λ := Real.rpow_le_rpow (x := t) (y := c (m + 1)) (z := Λ) (le_of_lt (lt_trans zero_lt_one ht1)) ht.2 (le_of_lt hΛpos)
            _ = c m := hcc m
      have hst : ‖v (t ^ Λ) - z‖ ≤ ρ := by
        have := ih _ hmem
        calc ‖v (t ^ Λ) - z‖ ≤ κ ^ m * ρ := this
          _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right (pow_le_one₀ hκ0 (le_of_lt hκ1)) (le_of_lt hρ)
          _ = ρ := one_mul ρ
      have hfac : (t ^ Λ) ^ (1 / Λ) = t := by
        rw [← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one ht1)), mul_one_div,
          div_self (ne_of_gt hΛpos), Real.rpow_one]
      have htL1 : 1 < t ^ Λ := by
        calc (1 : ℝ) = 1 ^ Λ := (Real.one_rpow Λ).symm
          _ < t ^ Λ := Real.rpow_lt_rpow (x := 1) (y := t) (z := Λ) (by norm_num) ht1 hΛpos
      have hd := hdesc (t ^ Λ) htL1
      rw [hfac] at hd
      calc ‖v t - z‖ = ‖g (v (t ^ Λ)) - z‖ := by rw [hd]
        _ ≤ κ * ‖v (t ^ Λ) - z‖ := hcontr _ hst
        _ ≤ κ * (κ ^ m * ρ) := mul_le_mul_of_nonneg_left (ih _ hmem) hκ0
        _ = κ ^ (m + 1) * ρ := by ring
  intro m t ht1 ht2
  have ht1' : c (m + 1) ≤ t := by simpa only [hc] using ht1
  have ht2' : t ≤ c m := by simpa only [hc] using ht2
  exact main m t ⟨ht1', ht2'⟩

/-- **Goldberg-Milnor B.1 in dynamical form**, the statement required by the `gm` row of the
`LANDCL` delivery table.  See the file header for the route. -/
theorem goldbergMilnorB1StatementCheck : Work.LANDCL.GoldbergMilnorB1 := by
  intro c θ k y hrep hland cn wn zn hcrit hray hc hlev z hz
  -- the landing angle of a repelling periodic point is periodic under the angle map
  obtain ⟨q, hq, hper⟩ := Work.LandLeaves.periodicAngle_landsAt_repelling hrep hland
  -- the quantitative stability of the landing (Goldberg-Milnor B.1)
  obtain ⟨δ, η, C, κ, yf, hδ, hη, hC, hκ0, hκ1, hyfcont, hyfc, hdecay⟩ :=
    Work.LandLeaves.landingDecay hrep hland hq hper
  -- `zₙ` converges to the (continuous) continuation of the repelling point
  have hzy : Filter.Tendsto zn Filter.atTop (𝓝 y) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- fix a depth `M` at which the geometric factor is already small
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one
      (show (0 : ℝ) < (ε / 2) / C by positivity) hκ1
    have hMC : κ ^ M * C < ε / 2 := by
      have h := mul_lt_mul_of_pos_right hM hC
      rwa [div_mul_cancel₀ (ε / 2) (ne_of_gt hC)] at h
    have hηM : (1 : ℝ) < η ^ (((1 : ℝ) / (4 : ℝ) ^ (k * q)) ^ M) :=
      Real.one_lt_rpow hη (by positivity)
    -- the three eventual conditions
    have h1 : ∀ᶠ n : ℕ in Filter.atTop, ‖cn n - c‖ < δ :=
      (hc.eventually (Metric.ball_mem_nhds c hδ)).mono fun n hn => by
        rwa [dist_eq_norm] at hn
    have h2 : ∀ᶠ n : ℕ in Filter.atTop,
        ‖wn n‖ ≤ η ^ (((1 : ℝ) / (4 : ℝ) ^ (k * q)) ^ M) :=
      (hlev.eventually (isOpen_Iio.mem_nhds hηM)).mono fun n hn => le_of_lt hn
    have h3 : ∀ᶠ n : ℕ in Filter.atTop, dist (yf (cn n)) y < ε / 2 := by
      have ht : Filter.Tendsto (fun n : ℕ => yf (cn n)) Filter.atTop (𝓝 y) := by
        have hcomp := hyfcont.tendsto.comp hc
        rw [hyfc] at hcomp
        exact hcomp
      exact ht.eventually (Metric.ball_mem_nhds y (by positivity))
    rw [Filter.eventually_atTop] at h1 h2 h3
    obtain ⟨N1, hN1⟩ := h1
    obtain ⟨N2, hN2⟩ := h2
    obtain ⟨N3, hN3⟩ := h3
    refine ⟨max (max N1 N2) N3, fun n hn => ?_⟩
    have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn3 : N3 ≤ n := le_trans (le_max_right _ _) hn
    have hcn : ‖cn n - c‖ < δ := hN1 n hn1
    have hwn : ‖wn n‖ ≤ η ^ (((1 : ℝ) / (4 : ℝ) ^ (k * q)) ^ M) := hN2 n hn2
    have hyfr : dist (yf (cn n)) y < ε / 2 := hN3 n hn3
    -- the hypothesis gives the critical-domain level point explicitly
    obtain ⟨φ, hφ, hzn, hφz⟩ := hcrit n
    obtain ⟨r, hr, hwr⟩ := hray n
    have hnormr : ‖wn n‖ = r := by
      have h1 : ‖((r : ℝ) : ℂ)‖ = r := by
        simp [abs_of_pos (by linarith : (0 : ℝ) < r)]
      rw [hwr, norm_mul, Work.ParamRays.norm_rayDir, mul_one, h1]
    have hval : Work.Bottcher.varphiCrit (cn n) (zn n)
        = (r : ℂ) * Work.ParamRays.rayDir θ := by
      rw [Work.Bottcher.varphiCrit_unique hφ hzn, hφz, hwr]
    have hbnd : r ≤ η ^ (((1 : ℝ) / (4 : ℝ) ^ (k * q)) ^ M) := by
      rw [← hnormr]; exact hwn
    have hdec := hdecay (cn n) hcn M (zn n) hzn ⟨r, hr, hbnd, hval⟩
    have hlt : ‖zn n - yf (cn n)‖ < ε / 2 := lt_of_le_of_lt hdec hMC
    have hsum : dist (zn n) y < ε / 2 + ε / 2 := by
      calc dist (zn n) y
          ≤ dist (zn n) (yf (cn n)) + dist (yf (cn n)) y := dist_triangle _ _ _
        _ = ‖zn n - yf (cn n)‖ + dist (yf (cn n)) y := by rw [dist_eq_norm]
        _ < ε / 2 + ε / 2 := add_lt_add hlt hyfr
    linarith
  exact tendsto_nhds_unique hz hzy

end Work.LandLeaves
