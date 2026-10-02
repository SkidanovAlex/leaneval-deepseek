/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The accumulation set of a periodic dynamic ray consists of periodic points

Let `c` lie in the mandelbar `M*` (the connectedness locus of `T_c(z) = z̄² + c`), so that the
dynamical Böttcher coordinate `φ = dynPhiOf c` is a homeomorphism of the escaping set onto the
exterior of the unit disc, and let `θ` be a periodic angle for the angle-doubling map
`angDouble θ = -2θ mod 1`, of period `k > 0`.  This file proves

`Work.LandLeaves.rayAccum_subset_fixp`:
every point of the accumulation set `rayAccum c φ θ` of the dynamic ray `R_c(θ)` is fixed by
`(T_c)^[k]`.

## The argument

Write `M = 2^k` and let `rayPt hN θ t` (`t > 1`) be the point of the ray of angle `θ` at
Böttcher level `t`; it is the inverse Böttcher image of `rayPoint θ t = t e^{2πiθ}`.

* **Transfer.**  `T_c` maps the ray at angle `θ` onto the ray at angle `angDouble θ = T θ`, and
  the level is squared; iterating, `(T_c)^[k] (rayPt θ s) = rayPt θ (s^M)` whenever
  `angDouble^[k] θ = θ` (`rayPt_iterate_T`, built on `Work.ELTop.rayPt_T`).

* **Beads shrink** (`rayPt_bead`).  If `1 < r₁ ≤ r₂` are close to `1` with
  `log r₂ ≤ M log r₁`, then `‖rayPt θ r₂ - rayPt θ r₁‖` is small.  Proof: Koebe's quarter
  theorem for the univalent inverse Böttcher coordinate (`Work.LandLeaves.koebeDerivBound`)
  gives `‖Ψ' w‖ (‖w‖-1) ≤ 4 · dist(Ψ w, filledJulia c)`, and the distance from `Ψ w` to the
  filled Julia set tends to `0` as `‖w‖ → 1` (`Work.LandLeaves.invBottcherCloseFilledJulia`).
  Hence along the bead `‖d/dt rayPt θ t‖ ≤ 4ε/(r₁-1)`, and the mean value inequality together
  with the elementary bound `(r₂-1)/(r₁-1) ≤ (r₁^M - 1)/(r₁-1) ≤ 2^M` gives the claim.

* **Assembly.**  A point `z` of `rayAccum c φ θ` is a limit of ray points `rayPt θ (t n)` with
  levels `t n ↓ 1` (`Work.ELTop.rayAccum_eq_closure`).  Since the beads shrink,
  `rayPt θ ((t n)^(1/M)) → z` as well, so by continuity of `(T_c)^[k]` and the transfer,
  `(T_c)^[k] z = lim (T_c)^[k] (rayPt θ ((t n)^(1/M))) = lim rayPt θ (t n) = z`.

## Analytic inputs (proved by the sibling ledger, imported here)

* `Work.LandLeaves.koebeDerivBound` — Koebe's quarter theorem for the univalent inverse Böttcher
  coordinate `Ψ`, in the form `‖Ψ' w‖ (‖w‖ - 1)/4 ≤ ‖y - Ψ w‖` for `1 < ‖w‖` and `y` outside the
  escaping set.  It rests, through `Work.LandLeaves.bieberbachA2`, on Grönwall's area theorem.
* `Work.LandLeaves.invBottcherCloseFilledJulia` — `dist (Ψ w) (filledJulia c) → 0` uniformly as
  `‖w‖ → 1⁺`, i.e. the inverse Böttcher coordinate approaches the filled Julia set.
* `Work.ELTop.rayPt_T`, `Work.ELTop.rayAccum_eq_closure`, `Work.ELRig.invBottcher_rayPoint` —
  the ray transfer, the description of `rayAccum` by ray pieces, and `rayPt = Ψ ∘ rayPoint`.
-/
import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.bottcherInverse
import Submission.Work.LandLeaves.koebeDerivBound
import Submission.Work.LandLeaves.invBottcherCloseFilledJulia
import Submission.Work.ELTop.landsN_map
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.ELRig.analyticOn_rayPt_of_analytic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical Set Metric Filter
open scoped Topology ComplexConjugate

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays (IsDynBottcher Escaping escapingSet filledJulia)

theorem rayPt_iterate_T {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hφ : IsDynBottcher c φ)
    (θ : ℝ) (n : ℕ) :
    ∀ {s : ℝ}, 1 < s →
      Work.EL.rayPt hN ((Work.EL.T)^[n] θ) (s ^ 2 ^ n)
        = (Tantibar c)^[n] (Work.EL.rayPt hN θ s) := by
  induction n generalizing θ with
  | zero =>
      intro s hs
      simp
  | succ n ih =>
      intro s hs
      have hs2 : 1 < s ^ 2 := by nlinarith
      have hlev : s ^ 2 ^ (n + 1) = (s ^ 2) ^ 2 ^ n := by
        rw [pow_succ' 2 n, pow_mul]
      rw [hlev, Function.iterate_succ_apply, ih (Work.EL.T θ) (s := s ^ 2) hs2,
        Work.ELTop.rayPt_T hN hφ hs, Function.iterate_succ_apply]

/-! ## The beads shrink -/

/-- **The beads of the dynamic ray shrink.**  If `1 < r₁ ≤ r₂` with `r₂` close to `1` and
`log r₂ ≤ M log r₁` (`M ≥ 2`), then the corresponding points of the ray are close. -/
theorem rayPt_bead (c : ℂ) (hc : c ∈ Mandelbar) (θ : ℝ) (M : ℕ) (hM : 2 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧
      ∀ r₁ r₂ : ℝ, 1 < r₁ → r₁ ≤ r₂ → r₂ < ρ → Real.log r₂ ≤ (M : ℝ) * Real.log r₁ →
        ‖Work.EL.rayPt (Work.SeedDyn.dynB hc) θ r₂ - Work.EL.rayPt (Work.SeedDyn.dynB hc) θ r₁‖
          ≤ ε := by
  intro ε hε
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  set C : ℝ := 4 * (2 : ℝ) ^ M with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  set ε₀ : ℝ := ε / (C + 1) with hε₀def
  have hε₀pos : 0 < ε₀ := by rw [hε₀def]; positivity
  have hkey : 4 * (2 : ℝ) ^ M * ε₀ ≤ ε := by
    rw [hε₀def, ← hCdef, mul_div_assoc', div_le_iff₀ (by linarith : 0 < C + 1)]
    nlinarith [hCnn, hε]
  obtain ⟨ρ, hρ1, hρ2, hρ⟩ := invBottcherCloseFilledJulia c hc ε₀ hε₀pos
  refine ⟨ρ, hρ1, hρ2, ?_⟩
  intro r₁ r₂ hr₁ hr₁₂ hr₂ρ hlog
  set u : ℂ := Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) with hudef
  have hunorm : ‖u‖ = 1 := by
    rw [hudef, Complex.norm_exp]
    simp
  have hray : ∀ t : ℝ, Work.Top.NakaneData.rayPoint θ t = (t : ℂ) * u := by
    intro t
    rw [Work.Top.NakaneData.rayPoint, hudef]
  have hrayPt : ∀ t : ℝ, 1 < t →
      Work.ELRig.invBottcher (Work.SeedDyn.dynB hc) (Work.Top.NakaneData.rayPoint θ t)
        = Work.EL.rayPt (Work.SeedDyn.dynB hc) θ t := by
    intro t ht
    rw [Work.ELRig.invBottcher_rayPoint (Work.SeedDyn.dynB hc) ht]
  have hr₂pos : 0 < r₂ := by linarith
  have hr₁pos : 0 < r₁ := by linarith
  have hr₁ne : r₁ ≠ 1 := by linarith
  have hr₁2 : r₁ ≤ 2 := le_trans hr₁₂ (le_trans hr₂ρ.le hρ2)
  -- (1) the levels lie in a bounded geometric window
  have hr₂pow : r₂ ≤ r₁ ^ M := by
    have h1 : Real.log r₂ ≤ Real.log (r₁ ^ M) := by
      rw [Real.log_pow]
      exact hlog
    calc r₂ = Real.exp (Real.log r₂) := (Real.exp_log hr₂pos).symm
      _ ≤ Real.exp (Real.log (r₁ ^ M)) := Real.exp_le_exp.mpr h1
      _ = r₁ ^ M := Real.exp_log (by positivity)
  have hratio : (r₂ - 1) / (r₁ - 1) ≤ (2 : ℝ) ^ M := by
    have hr₁1 : 0 < r₁ - 1 := by linarith
    have h2 : (r₂ - 1) / (r₁ - 1) ≤ (r₁ ^ M - 1) / (r₁ - 1) :=
      div_le_div_of_nonneg_right (by linarith : r₂ - 1 ≤ r₁ ^ M - 1)
        (by linarith : (0:ℝ) ≤ r₁ - 1)
    have h3 : (r₁ ^ M - 1) / (r₁ - 1) = ∑ i ∈ Finset.range M, r₁ ^ i :=
      (geom_sum_eq hr₁ne M).symm
    have h4 : ∑ i ∈ Finset.range M, r₁ ^ i ≤ ∑ i ∈ Finset.range M, (2 : ℝ) ^ i :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ r₁) hr₁2 i)
    have h5 : ∑ i ∈ Finset.range M, (2 : ℝ) ^ i = (2 : ℝ) ^ M - 1 := by
      rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) M]
      norm_num
    have h6 : (2 : ℝ) ^ M - 1 ≤ (2 : ℝ) ^ M := by
      have : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
      linarith
    linarith [h2, h3, h4, h5, h6]
  -- (2) the pointwise bound on the derivative along the bead
  have hpoint : ∀ t ∈ Set.Ico r₁ r₂,
      ‖deriv (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc)) (Work.Top.NakaneData.rayPoint θ t)‖
        ≤ 4 * ε₀ / (r₁ - 1) := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hr₁ ht.1
    have htpos : 0 < t := by linarith
    have htr₁ : r₁ ≤ t := ht.1
    have htρ : t < ρ := lt_trans ht.2 hr₂ρ
    have hwt : ‖Work.Top.NakaneData.rayPoint θ t‖ = t := by
      rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos htpos]
    obtain ⟨y, hyK, hyε⟩ := hρ _ (by rw [hwt]; exact ht1) (by rw [hwt]; exact htρ)
    have hyesc : y ∉ escapingSet c := by
      rw [← Work.ParamRays.compl_filledJulia c, Set.mem_compl_iff, not_not]
      exact hyK
    have hkoebe := koebeDerivBound (Work.SeedDyn.dynB hc)
      ((Work.SeedDyn.isDynBottcherHomeo hc).1) (Work.Top.NakaneData.rayPoint θ t)
      (by rw [hwt]; exact ht1) y hyesc
    rw [hwt] at hkoebe
    have h4 : ‖deriv (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc))
        (Work.Top.NakaneData.rayPoint θ t)‖ * (t - 1) ≤ 4 * ε₀ := by
      have := le_trans hkoebe hyε
      linarith
    have h5 : ‖deriv (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc))
        (Work.Top.NakaneData.rayPoint θ t)‖ * (t - 1) / (t - 1) ≤ 4 * ε₀ / (t - 1) :=
      div_le_div_of_nonneg_right h4 (by linarith)
    have h6 : ‖deriv (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc))
        (Work.Top.NakaneData.rayPoint θ t)‖ * (t - 1) / (t - 1)
          = ‖deriv (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc))
        (Work.Top.NakaneData.rayPoint θ t)‖ := by
      rw [mul_div_assoc, div_self (by linarith : (t - 1) ≠ 0), mul_one]
    rw [h6] at h5
    refine le_trans h5 (div_le_div_of_nonneg_left (by positivity)
      (by linarith : 0 < r₁ - 1) (by linarith : r₁ - 1 ≤ t - 1))
  -- (3) the mean value inequality
  have hMVT : ‖Work.EL.rayPt (Work.SeedDyn.dynB hc) θ r₂ - Work.EL.rayPt (Work.SeedDyn.dynB hc) θ r₁‖
      ≤ (4 * ε₀ / (r₁ - 1)) * (r₂ - r₁) := by
    have hderiv : ∀ x ∈ Set.Icc r₁ r₂,
        HasDerivWithinAt (fun t : ℝ => Work.ELRig.invBottcher (Work.SeedDyn.dynB hc)
            (Work.Top.NakaneData.rayPoint θ t))
          (deriv (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc))
            (Work.Top.NakaneData.rayPoint θ x) * u) (Set.Icc r₁ r₂) x := by
      intro x hx
      have hx1 : 1 < x := lt_of_lt_of_le hr₁ hx.1
      have hwt : 1 < ‖Work.Top.NakaneData.rayPoint θ x‖ := by
        rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
        exact hx1
      have han : AnalyticAt ℂ (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc))
          (Work.Top.NakaneData.rayPoint θ x) :=
        Work.ELRig.analyticAt_invBottcher (Work.SeedDyn.dynB hc)
          (Work.ELRig.analyticOnNhd_dynBottcher ((Work.SeedDyn.isDynBottcherHomeo hc).1)) hwt
      have h2 : HasDerivAt (fun s : ℝ => Work.Top.NakaneData.rayPoint θ s) u x := by
        have hc' : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := (hasDerivAt_id x).ofReal_comp
        have := hc'.mul_const u
        simpa [hray] using this
      exact ((han.differentiableAt.hasDerivAt).comp x h2).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico r₁ r₂,
        ‖deriv (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc))
          (Work.Top.NakaneData.rayPoint θ x) * u‖ ≤ 4 * ε₀ / (r₁ - 1) := by
      intro x hx
      rw [norm_mul, hunorm, mul_one]
      exact hpoint x hx
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => Work.ELRig.invBottcher (Work.SeedDyn.dynB hc)
        (Work.Top.NakaneData.rayPoint θ t))
      (a := r₁) (b := r₂) hderiv hbound r₂ ⟨hr₁₂, le_rfl⟩
    rw [hrayPt r₂ (by linarith), hrayPt r₁ hr₁] at hmain
    exact hmain
  -- (4) assemble
  calc ‖Work.EL.rayPt (Work.SeedDyn.dynB hc) θ r₂ - Work.EL.rayPt (Work.SeedDyn.dynB hc) θ r₁‖
      ≤ (4 * ε₀ / (r₁ - 1)) * (r₂ - r₁) := hMVT
    _ = 4 * ε₀ * ((r₂ - r₁) / (r₁ - 1)) := by ring
    _ ≤ 4 * ε₀ * ((r₂ - 1) / (r₁ - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ ≤ 4 * ε₀ * (2 : ℝ) ^ M := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ ε := by linarith [hkey]

/-! ## The accumulation set of a periodic ray consists of periodic points -/

theorem rayAccum_subset_fixp (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) {θ : ℝ} {k : ℕ} (hk : 0 < k) (hper : Work.Landing.PeriodicAngle θ k) : ∀ z ∈ Work.Landing.rayAccum c (Work.ParamRays.dynPhiOf c) θ, (LeanEval.ComplexAnalysis.Tantibar c)^[k] z = z := by
  intro z hz
  have hφ : IsDynBottcher c (Work.ParamRays.dynPhiOf c) := (Work.SeedDyn.isDynBottcherHomeo hc).1
  set M : ℕ := 2 ^ k with hMdef
  have hM2 : 2 ≤ M := by
    rw [hMdef]
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  -- the sequence of ray points approaching `z`
  have hseq : ∀ n : ℕ, ∃ t : ℝ, 1 < t ∧ t ≤ 1 + 1 / ((n : ℝ) + 1) ∧
      ‖Work.EL.rayPt (Work.SeedDyn.dynB hc) θ t - z‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have hR : (1 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hzall : ∀ ρ : ℝ, 1 < ρ →
        z ∈ closure (Work.EL.rayPiece (Work.SeedDyn.dynB hc) θ 0 ρ) :=
      (Work.ELTop.rayAccum_eq_closure (Work.SeedDyn.dynB hc) θ).le hz
    have hzR : z ∈ closure (Work.EL.rayPt (Work.SeedDyn.dynB hc) θ
        '' Set.Ioc (1 : ℝ) (1 + 1 / ((n : ℝ) + 1))) := by
      rw [← Work.ELTop.rayPiece_eq_image (Work.SeedDyn.dynB hc) hR]
      exact hzall _ hR
    obtain ⟨w, hw, hwz⟩ := (Metric.mem_closure_iff.mp hzR) (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨t, ht, rfl⟩ := hw
    refine ⟨t, ht.1, ht.2, ?_⟩
    rw [dist_eq_norm] at hwz
    rw [norm_sub_rev]
    exact hwz.le
  choose t ht using hseq
  have ht1 : ∀ n : ℕ, 1 < t n := fun n => (ht n).1
  have htle : ∀ n : ℕ, t n ≤ 1 + 1 / ((n : ℝ) + 1) := fun n => (ht n).2.1
  have hdist : ∀ n : ℕ, ‖Work.EL.rayPt (Work.SeedDyn.dynB hc) θ (t n) - z‖
      ≤ 1 / ((n : ℝ) + 1) := fun n => (ht n).2.2
  -- the level sequence tends to one
  have htend : Tendsto t atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ht1 n])]
    have := htle n
    linarith
  -- the ray points tend to `z`
  have hlim1 : Tendsto (fun n : ℕ => Work.EL.rayPt (Work.SeedDyn.dynB hc) θ (t n)) atTop (𝓝 z) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact hdist n
  have hnorm1 : Tendsto (fun n : ℕ => ‖Work.EL.rayPt (Work.SeedDyn.dynB hc) θ (t n) - z‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hlim1
  -- the level-`1/M` points of the ray also tend to `z`
  have hdiff : Tendsto (fun n : ℕ => ‖Work.EL.rayPt (Work.SeedDyn.dynB hc) θ ((t n) ^ (1 / (M : ℝ)))
        - Work.EL.rayPt (Work.SeedDyn.dynB hc) θ (t n)‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨ρ, hρ1, hρ2, hρ⟩ := rayPt_bead c hc θ M hM2 (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htend.eventually (Iio_mem_nhds hρ1))
    refine ⟨N, fun n hn => ?_⟩
    have hnρ : t n < ρ := hN n hn
    have hr1 : 1 < (t n) ^ (1 / (M : ℝ)) := Real.one_lt_rpow (ht1 n) (by positivity)
    have hle : (t n) ^ (1 / (M : ℝ)) ≤ t n := by
      refine Real.rpow_le_self_of_one_le (le_of_lt (ht1 n)) ?_
      rw [div_le_one hMpos]
      exact_mod_cast (by omega : 1 ≤ M)
    have hlog : Real.log (t n) ≤ (M : ℝ) * Real.log ((t n) ^ (1 / (M : ℝ))) := by
      rw [Real.log_rpow (by linarith [ht1 n]), ← mul_assoc, mul_one_div, div_self hMpos.ne',
        one_mul]
    have hb := hρ ((t n) ^ (1 / (M : ℝ))) (t n) hr1 hle hnρ hlog
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), norm_sub_rev]
    linarith [hb]
  have hlim2 : Tendsto (fun n : ℕ => Work.EL.rayPt (Work.SeedDyn.dynB hc) θ
      ((t n) ^ (1 / (M : ℝ)))) atTop (𝓝 z) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hdiff) (ε / 2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hnorm1) (ε / 2) (by linarith)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
    have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1 h2
    rw [dist_eq_norm]
    calc ‖Work.EL.rayPt (Work.SeedDyn.dynB hc) θ ((t n) ^ (1 / (M : ℝ))) - z‖
        = ‖(Work.EL.rayPt (Work.SeedDyn.dynB hc) θ ((t n) ^ (1 / (M : ℝ)))
            - Work.EL.rayPt (Work.SeedDyn.dynB hc) θ (t n))
            + (Work.EL.rayPt (Work.SeedDyn.dynB hc) θ (t n) - z)‖ := by ring_nf
      _ ≤ ‖Work.EL.rayPt (Work.SeedDyn.dynB hc) θ ((t n) ^ (1 / (M : ℝ)))
            - Work.EL.rayPt (Work.SeedDyn.dynB hc) θ (t n)‖
          + ‖Work.EL.rayPt (Work.SeedDyn.dynB hc) θ (t n) - z‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  -- the transfer
  have htrans : ∀ n : ℕ, (Tantibar c)^[k] (Work.EL.rayPt (Work.SeedDyn.dynB hc) θ
        ((t n) ^ (1 / (M : ℝ)))) = Work.EL.rayPt (Work.SeedDyn.dynB hc) θ (t n) := by
    intro n
    have hs : 1 < (t n) ^ (1 / (M : ℝ)) := Real.one_lt_rpow (ht1 n) (by positivity)
    have hmain := rayPt_iterate_T (Work.SeedDyn.dynB hc) hφ θ k hs
    have hTk : (Work.EL.T)^[k] θ = θ := by
      have hT : Work.EL.T = Work.Landing.angDouble := by funext x; rfl
      rw [hT]
      exact hper
    have hlev : ((t n) ^ (1 / (M : ℝ))) ^ 2 ^ k = t n := by
      have hpow : (((2 : ℕ) ^ k : ℕ) : ℝ) = (M : ℝ) := by rw [hMdef]
      have hmul : (1 / (M : ℝ)) * (((2 : ℕ) ^ k : ℕ) : ℝ) = 1 := by
        rw [hpow]
        exact div_mul_cancel₀ 1 hMpos.ne'
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (by linarith [ht1 n])), hmul,
        Real.rpow_one]
    rw [hTk, hlev] at hmain
    exact hmain.symm
  -- conclude
  have hcontF : Continuous ((Tantibar c)^[k]) := (Work.Landing.Family.tantibar_continuous c).iterate k
  have h2 : Tendsto (fun n : ℕ => (Tantibar c)^[k] (Work.EL.rayPt (Work.SeedDyn.dynB hc) θ
      ((t n) ^ (1 / (M : ℝ))))) atTop (𝓝 ((Tantibar c)^[k] z)) :=
    hcontF.continuousAt.tendsto.comp hlim2
  have h1 : Tendsto (fun n : ℕ => (Tantibar c)^[k] (Work.EL.rayPt (Work.SeedDyn.dynB hc) θ
      ((t n) ^ (1 / (M : ℝ))))) atTop (𝓝 z) :=
    hlim1.congr' (Filter.Eventually.of_forall fun n => (htrans n).symm)
  exact tendsto_nhds_unique h2 h1

end Work.LandLeaves
