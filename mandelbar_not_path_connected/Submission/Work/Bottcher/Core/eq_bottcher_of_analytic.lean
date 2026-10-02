/-
# The product formula is the analytic Böttcher coordinate on the far region

`Work.Bottcher.bottcher c` is *defined* by the product formula

`φ_c(z) = z · exp (Σ_n 4^{-(n+1)} log (p_c^n z / (p_c^n z)^4))`,  `p_c = T_c ∘ T_c`.

This file proves that on the far region `{z : escapeRadius c ≤ ‖z‖}` this explicit
object coincides with *every* analytic solution of the Böttcher problem for the
holomorphic quartic `p_c`: if

* `ψ` is analytic on `{escapeRadius c ≤ ‖z‖}`,
* `ψ ∘ p_c = ψ^4` there,
* `‖ψ z‖ = exp (G_c z)` there (the Green function of `T_c`), and
* `ψ z / z → 1` as `z → ∞`,

then `ψ z = bottcher c z` for every `z` in the far region.

The proof is the classical uniqueness argument for Böttcher coordinates, run on the
*open* far region `S = {escapeRadius c < ‖z‖}` (preconnected, by
`Work.ParamRays.isPreconnected_lt_norm`):

* the two coordinate functions have the same modulus `exp ∘ G_c` on `S`
  (`norm_bottcher_eq_exp_green_of_escapeRadius_le` here, `hmod` for `ψ`), so the ratio
  `u = ψ / φ_c` has modulus `1` on `S`;
* `u ∘ p_c = u^4` and `p_c^n z → ∞`, while `u → 1` at `∞` (from `ψ z / z → 1` and
  `bottcher_tendsto_atTop`), so `u z` is a `2`-power root of unity
  (`exists_pow_two_pow_eq_one_of_tendsto_pow_four`); the image `u '' S` is preconnected
  and contained in the (totally disconnected) set of `2`-power roots of unity, hence a
  singleton (`Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one`);
* the constant value is `1` because `u` has limit `1` at infinity along `S`;
* the equality extends to the boundary `‖z‖ = escapeRadius c` by continuity.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.bottcher_comm_pMap
import Submission.Work.Bottcher.Core.norm_bottcher_domain
import Submission.Work.Bottcher.Core.bottcher_tendsto_atTop
import Submission.Work.Bottcher.Core.norm_iterate_pMap_ge
import Submission.Work.Bottcher.Core.norm_bottcher_eq_exp_green
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.ParamRays.exists_pow_two_pow_eq_one
import Submission.Work.ParamRays.isPreconnected_lt_norm_of_differentiable
import Submission.Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

namespace Work.Bottcher.Core

noncomputable section

/-! ## Elementary facts about the escape radius -/

theorem escapeRadius_pos (c : ℂ) : 0 < Work.Bottcher.escapeRadius c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [Work.Bottcher.escapeRadius]
  linarith

theorem two_add_norm_le_escapeRadius (c : ℂ) : 2 + ‖c‖ ≤ Work.Bottcher.escapeRadius c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [Work.Bottcher.escapeRadius]
  linarith

theorem two_le_escapeRadius (c : ℂ) : (2 : ℝ) ≤ Work.Bottcher.escapeRadius c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [Work.Bottcher.escapeRadius]
  linarith

/-- The open far region `{z : escapeRadius c < ‖z‖}`, on which the ratio argument runs.
It is preconnected (`Work.ParamRays.isPreconnected_lt_norm`) and invariant under `p_c`. -/
def farRegion (c : ℂ) : Set ℂ := {z : ℂ | Work.Bottcher.escapeRadius c < ‖z‖}

theorem mem_farRegion {c z : ℂ} :
    z ∈ farRegion c ↔ Work.Bottcher.escapeRadius c < ‖z‖ := Iff.rfl

/-! ## Growth of the `T_c`-orbit in the far region

Above the escape radius the antiholomorphic quadratic `T_c` at least doubles the norm,
`2 ‖w‖ ≤ ‖T_c w‖`, so the orbit of every point of the far region escapes to infinity
with norms growing like `2 ^ n`.  (This is proved directly, since the general escape
criterion `Work.Escape.tendsto_norm_Tantibar_iterate_atTop` needs the *strict*
inequality `max 2 ‖c‖ < ‖z‖`, which fails at `‖z‖ = escapeRadius c` when `c = 0`.) -/

theorem two_mul_norm_le_norm_Tantibar (c : ℂ) {w : ℂ}
    (hw : Work.Bottcher.escapeRadius c ≤ ‖w‖) :
    2 * ‖w‖ ≤ ‖Tantibar c w‖ := by
  have ht : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have h1 : ‖w‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c w‖ := norm_Tantibar_ge c w
  have hR : 2 + 2 * ‖c‖ ≤ ‖w‖ := by
    rw [Work.Bottcher.escapeRadius] at hw
    linarith
  have hR2 : 2 * ‖c‖ ≤ ‖w‖ - 2 := by linarith
  have hprod : (2 + 2 * ‖c‖) * (2 * ‖c‖) ≤ ‖w‖ * (‖w‖ - 2) :=
    mul_le_mul hR hR2 (by positivity) (by linarith)
  have hle : ‖c‖ ≤ ‖w‖ * (‖w‖ - 2) := by nlinarith [hprod, ht, sq_nonneg ‖c‖]
  linarith [h1]

theorem escapeRadius_le_norm_Tantibar (c : ℂ) {w : ℂ}
    (hw : Work.Bottcher.escapeRadius c ≤ ‖w‖) :
    Work.Bottcher.escapeRadius c ≤ ‖Tantibar c w‖ := by
  have h1 := two_mul_norm_le_norm_Tantibar c hw
  have h2 : ‖w‖ ≤ 2 * ‖w‖ := by linarith [norm_nonneg w]
  linarith

/-- Along the `T_c`-orbit of a point of the far region the norms grow at least like
`2 ^ n`, and every iterate stays in the far region. -/
theorem escapeRadius_le_norm_Tantibar_iterate (c : ℂ) {z : ℂ}
    (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) (n : ℕ) :
    Work.Bottcher.escapeRadius c ≤ ‖(Tantibar c)^[n] z‖ ∧
      2 ^ n * ‖z‖ ≤ ‖(Tantibar c)^[n] z‖ := by
  induction n with
  | zero => exact ⟨hz, by simp⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨escapeRadius_le_norm_Tantibar c ih.1, ?_⟩
      rw [pow_succ]
      have h2 : 2 * ‖(Tantibar c)^[n] z‖ ≤ ‖Tantibar c ((Tantibar c)^[n] z)‖ :=
        two_mul_norm_le_norm_Tantibar c ih.1
      nlinarith [ih.2, h2]

/-- The norms of the `T_c`-orbit of a point of the far region tend to infinity. -/
theorem tendsto_norm_Tantibar_iterate_of_escapeRadius_le (c : ℂ) {z : ℂ}
    (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) :
    Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] z‖) atTop atTop := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (escapeRadius_pos c) hz
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine tendsto_atTop_mono (fun n => (escapeRadius_le_norm_Tantibar_iterate c hz n).2) ?_
  simpa using hpow.atTop_mul_const hzpos

/-! ## The far region is invariant under `p_c` -/

/-- On the far region the holomorphic quartic `p_c` does not decrease the norm and keeps
one inside the far region. -/
theorem escapeRadius_le_norm_pMap (c : ℂ) {w : ℂ}
    (hw : Work.Bottcher.escapeRadius c ≤ ‖w‖) :
    Work.Bottcher.escapeRadius c ≤ ‖Work.Bottcher.pMap c w‖ ∧
      ‖w‖ ≤ ‖Work.Bottcher.pMap c w‖ := by
  have h2 : 2 + ‖c‖ ≤ ‖w‖ := le_trans (two_add_norm_le_escapeRadius c) hw
  have h2' : (2 : ℝ) ≤ ‖w‖ := le_trans (two_le_escapeRadius c) hw
  obtain ⟨h5, h6, -⟩ := pMap_norm_step c w h2
  refine ⟨?_, h5⟩
  have h3 : (8 : ℝ) ≤ ‖w‖ ^ 3 := by nlinarith [h2', sq_nonneg ‖w‖]
  have h4 : 8 * ‖w‖ ≤ ‖w‖ ^ 4 := by
    calc 8 * ‖w‖ ≤ ‖w‖ ^ 3 * ‖w‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg w)
      _ = ‖w‖ ^ 4 := by ring
  calc Work.Bottcher.escapeRadius c ≤ ‖w‖ := hw
    _ ≤ 4 * ‖w‖ := by linarith [norm_nonneg w]
    _ ≤ ‖w‖ ^ 4 / 2 := by linarith
    _ ≤ ‖Work.Bottcher.pMap c w‖ := h6

theorem escapeRadius_le_norm_pMap_iterate (c : ℂ) {w : ℂ}
    (hw : Work.Bottcher.escapeRadius c ≤ ‖w‖) (n : ℕ) :
    Work.Bottcher.escapeRadius c ≤ ‖(Work.Bottcher.pMap c)^[n] w‖ :=
  (norm_iterate_pMap_ge c (Work.Bottcher.escapeRadius c)
    (fun _ hu => escapeRadius_le_norm_pMap c hu) w hw n).1

/-- No `p_c`-iterate of a point of the far region vanishes. -/
theorem pMap_iterate_ne_zero (c : ℂ) {w : ℂ}
    (hw : Work.Bottcher.escapeRadius c ≤ ‖w‖) (n : ℕ) :
    (Work.Bottcher.pMap c)^[n] w ≠ 0 :=
  norm_pos_iff.mp
    (lt_of_lt_of_le (escapeRadius_pos c) (escapeRadius_le_norm_pMap_iterate c hw n))

/-! ## `‖φ_c‖ = exp ∘ G_c` and the Böttcher equation on the far region -/

/-- The modulus of the product formula on the far region.  This is
`norm_bottcher_eq_exp_green` with its three hypotheses verified there: the orbit escapes
(`tendsto_norm_Tantibar_iterate_of_escapeRadius_le`), the Green function is the defining
limit, and no `p_c`-iterate vanishes (`pMap_iterate_ne_zero`). -/
theorem norm_bottcher_eq_exp_green_of_escapeRadius_le (c : ℂ) {z : ℂ}
    (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) :
    ‖Work.Bottcher.bottcher c z‖ = Real.exp (Work.Bottcher.green c z) := by
  refine norm_bottcher_eq_exp_green c z ?_ ?_ ?_
  · exact tendsto_norm_Tantibar_iterate_of_escapeRadius_le c hz
  · have hgr := Work.Escape.tendsto_greenIter (Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) (by norm_num) z
    have hfun : Work.Escape.greenIter (Tantibar c) 2 z
        = fun n : ℕ => ((1 : ℝ) / 2) ^ n * Work.Escape.logPos ‖(Tantibar c)^[n] z‖ := by
      funext n
      rw [Work.Escape.greenIter_def, one_div, inv_pow]
      norm_num
    exact hfun ▸ hgr
  · intro n
    exact pMap_iterate_ne_zero c hz n

/-- The Böttcher equation for the product formula on the far region. -/
theorem bottcher_comm_pMap_of_escapeRadius_le (c : ℂ) {z : ℂ}
    (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) :
    Work.Bottcher.bottcher c (Work.Bottcher.pMap c z) = (Work.Bottcher.bottcher c z) ^ 4 :=
  bottcher_comm_pMap c z (tendsto_norm_Tantibar_iterate_of_escapeRadius_le c hz)
    (fun n => pMap_iterate_ne_zero c hz n)

/-! ## Roots of unity of `2`-power order -/

/-- A sequence converging to `1` along both parities converges to `1`. -/
theorem tendsto_one_of_tendsto_even_odd {b : ℕ → ℂ}
    (he : Tendsto (fun n : ℕ => b (2 * n)) atTop (nhds 1))
    (ho : Tendsto (fun n : ℕ => b (2 * n + 1)) atTop (nhds 1)) :
    Tendsto b atTop (nhds 1) := by
  rw [Metric.tendsto_atTop] at he ho ⊢
  intro ε hε
  obtain ⟨N₁, h₁⟩ := he ε hε
  obtain ⟨N₂, h₂⟩ := ho ε hε
  refine ⟨2 * N₁ + 2 * N₂ + 2, fun k hk => ?_⟩
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hmN : N₁ ≤ m := by omega
    have h := h₁ m hmN
    simpa [hm, two_mul] using h
  · have hmN : N₂ ≤ m := by omega
    have h := h₂ m hmN
    simpa [hm] using h

/-- If `ζ ^ (4 ^ n) → 1` then `ζ` is a root of unity of `2`-power order: the two
subsequences `ζ ^ (2 ^ (2n)) = ζ ^ (4 ^ n)` and `ζ ^ (2 ^ (2n+1)) = (ζ ^ (4 ^ n))^2`
both converge to `1`, so the whole sequence `ζ ^ (2 ^ k)` does. -/
theorem exists_pow_two_pow_eq_one_of_tendsto_pow_four {ζ : ℂ}
    (h : Tendsto (fun n : ℕ => ζ ^ (4 ^ n)) atTop (nhds 1)) :
    ∃ N : ℕ, ζ ^ (2 ^ N) = 1 := by
  have he : Tendsto (fun n : ℕ => ζ ^ (2 ^ (2 * n))) atTop (nhds 1) := by
    refine h.congr' (Eventually.of_forall (fun n => ?_))
    congr 1
    rw [pow_mul]
    norm_num
  have ho : Tendsto (fun n : ℕ => ζ ^ (2 ^ (2 * n + 1))) atTop (nhds 1) := by
    have h2 : Tendsto (fun n : ℕ => (ζ ^ (4 ^ n)) ^ 2) atTop (nhds ((1 : ℂ) ^ 2)) := h.pow 2
    have h2' : Tendsto (fun n : ℕ => (ζ ^ (4 ^ n)) ^ 2) atTop (nhds (1 : ℂ)) := by
      simpa using h2
    refine h2'.congr' (Eventually.of_forall (fun n => ?_))
    show (ζ ^ 4 ^ n) ^ 2 = ζ ^ (2 ^ (2 * n + 1))
    rw [← pow_mul]
    congr 1
    rw [pow_succ, pow_mul]
    norm_num
  exact Work.ParamRays.exists_pow_two_pow_eq_one (tendsto_one_of_tendsto_even_odd he ho)

/-! ## The main theorem -/

theorem eq_bottcher_of_analytic (c : ℂ) (ψ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ ψ {z : ℂ | Work.Bottcher.escapeRadius c ≤ ‖z‖})
    (hfe : ∀ z : ℂ, Work.Bottcher.escapeRadius c ≤ ‖z‖ →
      ψ (Work.Bottcher.pMap c z) = (ψ z) ^ 4)
    (hmod : ∀ z : ℂ, Work.Bottcher.escapeRadius c ≤ ‖z‖ →
      ‖ψ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => ψ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ)))
    {z : ℂ} (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) :
    ψ z = Work.Bottcher.bottcher c z := by
  classical
  -- ## Identical modulus and non-vanishing on the far region
  have hmodφ : ∀ w : ℂ, Work.Bottcher.escapeRadius c ≤ ‖w‖ →
      ‖Work.Bottcher.bottcher c w‖ = Real.exp (Work.Bottcher.green c w) :=
    fun w hw => norm_bottcher_eq_exp_green_of_escapeRadius_le c hw
  have hφne : ∀ w : ℂ, Work.Bottcher.escapeRadius c ≤ ‖w‖ →
      Work.Bottcher.bottcher c w ≠ 0 := by
    intro w hw h
    have h1 := hmodφ w hw
    rw [h, norm_zero] at h1
    exact absurd h1.symm (Real.exp_ne_zero _)
  have hfeφ : ∀ w : ℂ, Work.Bottcher.escapeRadius c ≤ ‖w‖ →
      Work.Bottcher.bottcher c (Work.Bottcher.pMap c w) = (Work.Bottcher.bottcher c w) ^ 4 :=
    fun w hw => bottcher_comm_pMap_of_escapeRadius_le c hw
  have hnormU : ∀ w : ℂ, Work.Bottcher.escapeRadius c ≤ ‖w‖ →
      ‖ψ w / Work.Bottcher.bottcher c w‖ = 1 := by
    intro w hw
    rw [norm_div, hmod w hw, hmodφ w hw, div_self (Real.exp_ne_zero _)]
  have hfeU : ∀ w : ℂ, Work.Bottcher.escapeRadius c ≤ ‖w‖ →
      ψ (Work.Bottcher.pMap c w) / Work.Bottcher.bottcher c (Work.Bottcher.pMap c w)
        = (ψ w / Work.Bottcher.bottcher c w) ^ 4 := by
    intro w hw
    rw [hfe w hw, hfeφ w hw, div_pow]
  -- ## The ratio `u = ψ / φ_c` has limit `1` at infinity
  have hUtendsto : Tendsto (fun u : ℂ => ψ u / Work.Bottcher.bottcher c u)
      (cocompact ℂ) (nhds (1 : ℂ)) := by
    have hratio : Tendsto (fun u : ℂ => (ψ u / u) / (Work.Bottcher.bottcher c u / u))
        (cocompact ℂ) (nhds ((1 : ℂ) / 1)) :=
      has.div (bottcher_tendsto_atTop c) one_ne_zero
    have hratio' : Tendsto (fun u : ℂ => (ψ u / u) / (Work.Bottcher.bottcher c u / u))
        (cocompact ℂ) (nhds (1 : ℂ)) := by
      simpa using hratio
    refine hratio'.congr' ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with u hu
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu
      norm_num at hu
    have hφu0 : Work.Bottcher.bottcher c u ≠ 0 := by
      rw [Work.Bottcher.bottcher]
      exact mul_ne_zero hu0 (Complex.exp_ne_zero _)
    field_simp
  -- ## The open far region
  have hSpre : IsPreconnected (farRegion c) :=
    Work.ParamRays.isPreconnected_lt_norm (escapeRadius_pos c).le
  have hcontU : ContinuousOn (fun u : ℂ => ψ u / Work.Bottcher.bottcher c u) (farRegion c) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (han.mono (fun w hw => (mem_farRegion.mp hw).le)).continuousOn
    · intro w hw
      exact (analyticAt_bottcher c w (mem_farRegion.mp hw).le).continuousAt.continuousWithinAt
    · intro w hw
      exact hφne w (mem_farRegion.mp hw).le
  have hpre : IsPreconnected
      ((fun u : ℂ => ψ u / Work.Bottcher.bottcher c u) '' farRegion c) :=
    hSpre.image _ hcontU
  -- every value of the ratio on the far region is a `2`-power root of unity
  have hcert : ∀ w : ℂ, w ∈ farRegion c → ∃ N : ℕ,
      (ψ w / Work.Bottcher.bottcher c w) ^ (2 ^ N) = 1 := by
    intro w hw
    have hwD : Work.Bottcher.escapeRadius c ≤ ‖w‖ := (mem_farRegion.mp hw).le
    have hDiter : ∀ n : ℕ, Work.Bottcher.escapeRadius c ≤ ‖(Work.Bottcher.pMap c)^[n] w‖ :=
      fun n => escapeRadius_le_norm_pMap_iterate c hwD n
    have hiterU : ∀ n : ℕ,
        ψ ((Work.Bottcher.pMap c)^[n] w) / Work.Bottcher.bottcher c ((Work.Bottcher.pMap c)^[n] w)
          = (ψ w / Work.Bottcher.bottcher c w) ^ (4 ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', hfeU _ (hDiter n), ih, ← pow_mul, pow_succ]
    have hcoc : Tendsto (fun n : ℕ => (Work.Bottcher.pMap c)^[n] w) atTop (cocompact ℂ) := by
      refine tendsto_cocompact_of_tendsto_dist_comp_atTop 0 ?_
      have hT := tendsto_norm_Tantibar_iterate_of_escapeRadius_le c hwD
      have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
        tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
      have h1 : Tendsto (fun n : ℕ => ‖(Tantibar c)^[2 * n] w‖) atTop atTop := hT.comp h2n
      refine h1.congr' (Eventually.of_forall (fun n => ?_))
      simp only [dist_zero_right]
      rw [Work.Bottcher.pMap_iterate]
    have hlim : Tendsto (fun n : ℕ =>
        ψ ((Work.Bottcher.pMap c)^[n] w) / Work.Bottcher.bottcher c ((Work.Bottcher.pMap c)^[n] w))
        atTop (nhds 1) := hUtendsto.comp hcoc
    have hpow : Tendsto (fun n : ℕ => (ψ w / Work.Bottcher.bottcher c w) ^ (4 ^ n))
        atTop (nhds 1) :=
      hlim.congr' (Eventually.of_forall (fun n => hiterU n))
    exact exists_pow_two_pow_eq_one_of_tendsto_pow_four hpow
  have hsingle : ((fun u : ℂ => ψ u / Work.Bottcher.bottcher c u) '' farRegion c).Subsingleton :=
    Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one hpre
      (by rintro ζ ⟨w, hw, rfl⟩; exact hcert w hw)
  -- ## The constant value is `1`
  set w₀ : ℂ := ((Work.Bottcher.escapeRadius c + 1 : ℝ) : ℂ) with hw₀def
  have hw₀norm : ‖w₀‖ = Work.Bottcher.escapeRadius c + 1 := by
    rw [hw₀def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [(escapeRadius_pos c).le])]
  have hw₀S : w₀ ∈ farRegion c := by
    rw [mem_farRegion, hw₀norm]
    linarith
  have hconst : ∀ w : ℂ, w ∈ farRegion c →
      ψ w / Work.Bottcher.bottcher c w = ψ w₀ / Work.Bottcher.bottcher c w₀ :=
    fun w hw => hsingle ⟨w, hw, rfl⟩ ⟨w₀, hw₀S, rfl⟩
  have hval : ψ w₀ / Work.Bottcher.bottcher c w₀ = 1 := by
    have hclose : ∀ ε : ℝ, 0 < ε → ‖ψ w₀ / Work.Bottcher.bottcher c w₀ - 1‖ < ε := by
      intro ε hε
      have hmem : {u : ℂ | dist (ψ u / Work.Bottcher.bottcher c u) 1 < ε} ∈ cocompact ℂ :=
        (Metric.tendsto_nhds.mp hUtendsto) ε hε
      rw [Filter.mem_cocompact] at hmem
      obtain ⟨K, hKc, hKsub⟩ := hmem
      obtain ⟨M, hM⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
      set t : ℝ := max (Work.Bottcher.escapeRadius c) M + 1 with htdef
      have ht0 : 0 ≤ t := by
        rw [htdef]
        have h := le_max_left (Work.Bottcher.escapeRadius c) M
        linarith [(escapeRadius_pos c).le]
      have htnorm : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      have htmem : (t : ℂ) ∈ farRegion c := by
        rw [mem_farRegion, htnorm, htdef]
        linarith [le_max_left (Work.Bottcher.escapeRadius c) M]
      have htK : (t : ℂ) ∉ K := by
        intro ht
        have h1 := hM ht
        rw [Metric.mem_closedBall, dist_zero_right, htnorm, htdef] at h1
        linarith [le_max_right (Work.Bottcher.escapeRadius c) M]
      have hd := hKsub htK
      rw [Set.mem_ofPred_eq, dist_eq_norm] at hd
      rw [hconst t htmem] at hd
      exact hd
    have hzero : ‖ψ w₀ / Work.Bottcher.bottcher c w₀ - 1‖ ≤ 0 :=
      le_of_forall_pos_le_add (fun ε hε => by simpa using (hclose ε hε).le)
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))
  -- ## Equality on the open far region
  have heqS : ∀ w : ℂ, w ∈ farRegion c → ψ w = Work.Bottcher.bottcher c w := by
    intro w hw
    have h1 : ψ w / Work.Bottcher.bottcher c w = 1 := (hconst w hw).trans hval
    exact (div_eq_one_iff_eq (hφne w (mem_farRegion.mp hw).le)).mp h1
  -- ## Extension to the closed far region by continuity
  rcases lt_or_eq_of_le hz with hlt | heq
  · exact heqS z hlt
  · have hcontψ : ContinuousAt ψ z := (han z hz).continuousAt
    have hcontφ : ContinuousAt (Work.Bottcher.bottcher c) z :=
      (analyticAt_bottcher c z hz).continuousAt
    have hseq : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z) atTop (nhds z) := by
      have h1 : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (nhds (1 : ℂ)) := by
        have h3 : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
            (nhds ((1 + 0 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto _).comp h1
        simpa using h3
      simpa using h2.mul_const z
    have hmemS : ∀ n : ℕ, ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z ∈ farRegion c := by
      intro n
      have hq : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hcnorm : ‖(((1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ)‖ = 1 + 1 / ((n : ℝ) + 1) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      rw [mem_farRegion, norm_mul, hcnorm, ← heq]
      nlinarith [escapeRadius_pos c]
    have hagree : ∀ n : ℕ, ψ (((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z)
        = Work.Bottcher.bottcher c (((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z) :=
      fun n => heqS _ (hmemS n)
    have h1 : Tendsto (fun n : ℕ => ψ (((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z))
        atTop (nhds (ψ z)) := hcontψ.tendsto.comp hseq
    have h2 : Tendsto (fun n : ℕ =>
        Work.Bottcher.bottcher c (((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z))
        atTop (nhds (Work.Bottcher.bottcher c z)) := hcontφ.tendsto.comp hseq
    exact tendsto_nhds_unique h1 (h2.congr' (Eventually.of_forall (fun n => (hagree n).symm)))

end

end Work.Bottcher.Core
