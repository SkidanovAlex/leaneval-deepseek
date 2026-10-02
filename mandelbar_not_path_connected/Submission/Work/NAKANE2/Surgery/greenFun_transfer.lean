import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

open Filter
open scoped Real Topology

/-! ## Auxiliary estimates for the Green-function transfer -/

/-- The weights `2^{-n} log 2` tend to `0`. -/
private theorem tendsto_inv_pow_two_mul_log_two :
    Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * Real.log 2) Filter.atTop (𝓝 0) := by
  have h := Work.ParamRays.tendsto_inv_pow_two_mul 2
  have h2 : Real.posLog (2 : ℝ) = Real.log 2 := Real.posLog_eq_log (by norm_num)
  simpa [h2] using h

/-- If a homeomorphism `θ` of `ℂ` differs from the identity by at most `C / ‖z‖` in norm
for `‖z‖ ≥ R`, then at a point `u` with `1 ≤ ‖u‖` and `2 * C < ‖u‖` it distorts the norm by
at most a factor `2`. -/
private theorem norm_theta_bounds {θ : ℂ ≃ₜ ℂ} {C R : ℝ}
    (hdec : ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖)
    {u : ℂ} (hR : R ≤ ‖u‖) (h1 : 2 ≤ ‖u‖) (h2C : 2 * C < ‖u‖) :
    ‖u‖ / 2 ≤ ‖θ u‖ ∧ ‖θ u‖ ≤ 2 * ‖u‖ := by
  have hu0 : (0 : ℝ) < ‖u‖ := lt_of_lt_of_le (by norm_num) h1
  have hdiff : ‖θ u - u‖ ≤ C / ‖u‖ := hdec u hR
  have hCu : C / ‖u‖ ≤ 1 / 2 := by
    rw [div_le_iff₀ hu0]
    linarith
  constructor
  · have hsub : ‖u‖ ≤ ‖θ u‖ + ‖θ u - u‖ := by
      have := norm_sub_le (θ u) (θ u - u)
      rwa [sub_sub_cancel] at this
    linarith
  · have hadd : ‖θ u‖ ≤ ‖θ u - u‖ + ‖u‖ := by
      have := norm_add_le (θ u - u) u
      rwa [sub_add_cancel] at this
    linarith

/-- Route: for `z ∈ W c₀` the orbit `n ↦ (g^[n]) z` stays in `W c₀` (`hWg`) and equals the
`T_{c₀}`-orbit (`hWT`), and `T_{c'}^n (θ z) = θ ((g^[n]) z)` (`hconj`).  Both orbits tend to
infinity (`Work.ParamRays.greenFun_orbit` gives `G (T_{c₀}^n z) = 2^n G z → ∞`), and `hdecay`
gives `log ‖θ u‖ - log ‖u‖ → 0` for `‖u‖ → ∞`; `greenFun = limsup greenSeq` with
`greenSeq c w n = 2^{-n} log⁺ ‖T_c^[n] w‖` (`Work.ParamRays.greenFun_eq_of_tendsto`). -/
theorem greenFun_transfer {c₀ c' : ℂ} {g : ℂ → ℂ} {θ : ℂ ≃ₜ ℂ}
    (hconj : ∀ z : ℂ, θ (g z) = LeanEval.ComplexAnalysis.Tantibar c' (θ z))
    (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖)
    (hWT : ∀ z ∈ Work.NAKANE2.W c₀, g z = LeanEval.ComplexAnalysis.Tantibar c₀ z)
    (hWg : ∀ z ∈ Work.NAKANE2.W c₀, g z ∈ Work.NAKANE2.W c₀) :
    ∀ z ∈ Work.NAKANE2.W c₀, Work.ParamRays.greenFun c' (θ z) = Work.ParamRays.greenFun c₀ z := by
  intro z hz
  -- The orbit of `z` stays in `W c₀`, so along it `g` agrees with `T_{c₀}`.
  have horbW : ∀ n : ℕ, Work.ParamRays.orbit c₀ z n ∈ Work.NAKANE2.W c₀ := by
    intro n
    induction n with
    | zero => simpa [Work.ParamRays.orbit] using hz
    | succ n ih =>
      rw [Work.ParamRays.orbit_succ, ← hWT _ ih]
      exact hWg _ ih
  have hgiter : ∀ n : ℕ, (g^[n]) z = Work.ParamRays.orbit c₀ z n := by
    intro n
    induction n with
    | zero => simp [Work.ParamRays.orbit]
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hWT _ (horbW n)]
      exact (Work.ParamRays.orbit_succ c₀ z n).symm
  -- `θ` carries that orbit to the `T_{c'}`-orbit of `θ z`.
  have htheta : ∀ n : ℕ, Work.ParamRays.orbit c' (θ z) n = θ (Work.ParamRays.orbit c₀ z n) := by
    intro n
    induction n with
    | zero => simp [Work.ParamRays.orbit]
    | succ n ih =>
      rw [Work.ParamRays.orbit_succ, ih, ← hconj (Work.ParamRays.orbit c₀ z n),
        hWT _ (horbW n), ← Work.ParamRays.orbit_succ]
  -- `z` escapes under `T_{c₀}`.
  have hGpos : 0 < Work.ParamRays.greenFun c₀ z :=
    lt_of_le_of_lt (mul_nonneg (by norm_num) (Work.ParamRays.greenFun_nonneg c₀ c₀)) hz
  have hesce : Work.ParamRays.Escaping c₀ z :=
    (Work.ParamRays.greenFun_pos_iff_escaping c₀ z).mp hGpos
  -- `θ z` escapes under `T_{c'}`.
  obtain ⟨C, R, hCR⟩ := hdecay
  set R' : ℝ := max R (max 2 (2 * C)) with hR'def
  have hRle : R ≤ R' := by rw [hR'def]; exact le_max_left _ _
  have h2le : 2 ≤ R' := by
    rw [hR'def]
    exact le_trans (le_max_left 2 (2 * C)) (le_max_right R (max 2 (2 * C)))
  have h2Cle : 2 * C ≤ R' := by
    rw [hR'def]
    exact le_trans (le_max_right 2 (2 * C)) (le_max_right R (max 2 (2 * C)))
  have hnorm_ev : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Work.ParamRays.orbit c₀ z n‖ / 2 ≤ ‖Work.ParamRays.orbit c' (θ z) n‖ := by
    filter_upwards [Work.ParamRays.Escaping.eventually_gt hesce R'] with n hn
    have h1 : 2 ≤ ‖Work.ParamRays.orbit c₀ z n‖ := le_of_lt (lt_of_le_of_lt h2le hn)
    have h2 : 2 * C < ‖Work.ParamRays.orbit c₀ z n‖ := lt_of_le_of_lt h2Cle hn
    have h3 : R ≤ ‖Work.ParamRays.orbit c₀ z n‖ := le_of_lt (lt_of_le_of_lt hRle hn)
    rw [htheta n]
    exact (norm_theta_bounds hCR h3 h1 h2).1
  have hEsc' : Work.ParamRays.Escaping c' (θ z) := by
    refine (Filter.tendsto_atTop_atTop).mpr fun b => ?_
    obtain ⟨i, hi⟩ :=
      Filter.eventually_atTop.mp (Work.ParamRays.Escaping.eventually_gt hesce (2 * b))
    obtain ⟨j, hj⟩ := Filter.eventually_atTop.mp hnorm_ev
    exact ⟨max i j, fun a ha => by
      have h1 := hi a (le_trans (le_max_left i j) ha)
      have h2 := hj a (le_trans (le_max_right i j) ha)
      linarith⟩
  -- Both normalized-logarithm sequences converge to the corresponding Green functions.
  have hA : Filter.Tendsto (Work.ParamRays.greenSeq c₀ z) Filter.atTop
      (𝓝 (Work.ParamRays.greenFun c₀ z)) :=
    Work.ParamRays.greenSeq_tendsto_greenFun c₀ z hesce
  have hB : Filter.Tendsto (Work.ParamRays.greenSeq c' (θ z)) Filter.atTop
      (𝓝 (Work.ParamRays.greenFun c' (θ z))) :=
    Work.ParamRays.greenSeq_tendsto_greenFun c' (θ z) hEsc'
  -- ... and they differ by `O(2^{-n})`.
  have hdiff_ev : ∀ᶠ n : ℕ in Filter.atTop,
      |Work.ParamRays.greenSeq c' (θ z) n - Work.ParamRays.greenSeq c₀ z n| ≤
        ((2 : ℝ) ^ n)⁻¹ * Real.log 2 := by
    filter_upwards [Work.ParamRays.Escaping.eventually_gt hesce R'] with n hn
    have h1 : 2 ≤ ‖Work.ParamRays.orbit c₀ z n‖ := le_of_lt (lt_of_le_of_lt h2le hn)
    have h2 : 2 * C < ‖Work.ParamRays.orbit c₀ z n‖ := lt_of_le_of_lt h2Cle hn
    have h3 : R ≤ ‖Work.ParamRays.orbit c₀ z n‖ := le_of_lt (lt_of_le_of_lt hRle hn)
    obtain ⟨hlo, hup⟩ := norm_theta_bounds hCR h3 h1 h2
    have hu0 : (0 : ℝ) < ‖Work.ParamRays.orbit c₀ z n‖ := by linarith
    have hpl1 : Real.posLog ‖Work.ParamRays.orbit c₀ z n‖
        = Real.log ‖Work.ParamRays.orbit c₀ z n‖ :=
      Real.posLog_eq_log (by rw [abs_of_nonneg (norm_nonneg _)]; linarith)
    have hpl2 : Real.posLog ‖θ (Work.ParamRays.orbit c₀ z n)‖
        = Real.log ‖θ (Work.ParamRays.orbit c₀ z n)‖ :=
      Real.posLog_eq_log (by rw [abs_of_nonneg (norm_nonneg _)]; linarith)
    have hlog : |Real.log ‖θ (Work.ParamRays.orbit c₀ z n)‖
        - Real.log ‖Work.ParamRays.orbit c₀ z n‖| ≤ Real.log 2 := by
      rw [abs_sub_le_iff]
      refine ⟨?_, ?_⟩
      · have hle : Real.log ‖θ (Work.ParamRays.orbit c₀ z n)‖
            ≤ Real.log (2 * ‖Work.ParamRays.orbit c₀ z n‖) :=
          Real.log_le_log (by linarith) hup
        rw [Real.log_mul (by norm_num) (ne_of_gt hu0)] at hle
        linarith
      · have hle : Real.log (‖Work.ParamRays.orbit c₀ z n‖ / 2)
            ≤ Real.log ‖θ (Work.ParamRays.orbit c₀ z n)‖ :=
          Real.log_le_log (by linarith) hlo
        rw [Real.log_div (ne_of_gt hu0) (by norm_num : (2 : ℝ) ≠ 0)] at hle
        linarith
    rw [Work.ParamRays.greenSeq, Work.ParamRays.greenSeq, htheta n, hpl1, hpl2, ← mul_sub,
      abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹)]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hdiff : Filter.Tendsto
      (fun n => Work.ParamRays.greenSeq c' (θ z) n - Work.ParamRays.greenSeq c₀ z n)
      Filter.atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_
      tendsto_inv_pow_two_mul_log_two
    filter_upwards [hdiff_ev] with n hn
    simpa only [sub_zero, Real.norm_eq_abs] using hn
  have hsum : Filter.Tendsto (fun n => Work.ParamRays.greenSeq c₀ z n +
      (Work.ParamRays.greenSeq c' (θ z) n - Work.ParamRays.greenSeq c₀ z n))
      Filter.atTop (𝓝 (Work.ParamRays.greenFun c₀ z)) := by
    simpa using hA.add hdiff
  exact tendsto_nhds_unique hB (Filter.Tendsto.congr (fun n => by ring) hsum)

end Work.NAKANE2.Surgery
