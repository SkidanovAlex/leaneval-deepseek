import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Existence of surgery data at every parameter outside the mandelbar

The structure `Work.NAKANE2.SurgeryData c₀` collects the quantitative data of a
Shishikura surgery at the parameter `c₀`: a bump radius `ρ`, a smooth bump `χ` with
`rIn = ρ/2`, `rOut = ρ`, a bound `Λ ≥ 1` for the Fréchet derivative of the
`ℂ`-valued version `chiC c₀ χ` of `χ`, a radius `R₀` containing the complement of
the conformal region `W c₀`, and two conditions:

* the **band condition**: `closedBall c₀ (3ρ) ⊆ {7 g₀/8 < G < 9 g₀/8}` where
  `g₀ = Gcrit c₀ > 0`;
* the **boundedness of the complement of `W`**: `(W c₀)ᶜ ⊆ closedBall 0 R₀`.

Here we show that such data always exist for `c₀ ∉ Mb`.  The three inputs are:

* `Gcrit_pos`: `Gcrit c₀ = G_{c₀}(c₀) > 0` off the mandelbar;
* joint continuity of the Green function (`Work.NAKANE.continuous_greenFun`), which
  makes `G c₀ ·` continuous and produces the band condition around the point `c₀`;
* the doubly-exponential growth of escaping orbits
  (`Work.ParamRays.GreenGrowth.orbit_growth`), which gives the quantitative lower
  bound `log(‖z‖/2) ≤ G c₀ z` for `‖z‖ ≥ max 4 (2‖c₀‖)`, hence the boundedness of
  the complement of `W`.

## Main results

* `Work.NAKANE2.Surgery.greenFun_ge_log_half` : the growth bound at infinity.
* `Work.NAKANE2.Surgery.chiC_fderiv_bound` : the derivative of a bump is bounded.
* `Work.NAKANE2.Surgery.surgeryData_exists` : the existence of surgery data.
-/

open scoped ContDiff

namespace Work.NAKANE2.Surgery

/-- **Growth of the Green function at infinity.**  If `w` has already exceeded the
escape threshold `max 4 (2‖c‖)` then the Green function dominates `log(‖w‖/2)`.

This is the `N = 0` case of the argument in `Work.ParamRays.greenFun_pos_of_lt`:
the orbit of `w` grows at least like `2 (‖w‖/2)^{2^k}`, so every normalized
logarithm `greenSeq c w k` is at least `(2^k)⁻¹ log 2 + log(‖w‖/2) ≥ log(‖w‖/2)`,
and a `limsup` dominates any eventual lower bound. -/
theorem greenFun_ge_log_half (c w : ℂ) (h : max 4 (2 * ‖c‖) ≤ ‖w‖) :
    Real.log (‖w‖ / 2) ≤ Work.ParamRays.greenFun c w := by
  have hw2 : (0 : ℝ) < ‖w‖ / 2 := by
    have : (4 : ℝ) ≤ ‖w‖ := le_trans (le_max_left _ _) h
    linarith
  have hkey : ∀ k : ℕ, Real.log (‖w‖ / 2) ≤ Work.ParamRays.greenSeq c w k := by
    intro k
    obtain ⟨hg2, -⟩ := Work.ParamRays.GreenGrowth.orbit_growth c w h k
    have hgr : 2 * (‖w‖ / 2) ^ (2 ^ k) ≤ ‖Work.ParamRays.orbit c w k‖ := hg2
    have hA1 : (1 : ℝ) ≤ 2 * (‖w‖ / 2) ^ (2 ^ k) := by
      have h1 : (1 : ℝ) ≤ ‖w‖ / 2 := by
        have : (4 : ℝ) ≤ ‖w‖ := le_trans (le_max_left _ _) h
        linarith
      have h2 := one_le_pow₀ h1 (n := 2 ^ k)
      linarith
    have hple : Real.posLog (2 * (‖w‖ / 2) ^ (2 ^ k)) ≤
        Real.posLog ‖Work.ParamRays.orbit c w k‖ :=
      Real.posLog_le_posLog (by linarith) hgr
    have hplog : Real.posLog (2 * (‖w‖ / 2) ^ (2 ^ k))
        = Real.log 2 + (2 : ℝ) ^ k * Real.log (‖w‖ / 2) := by
      rw [Real.posLog_eq_log (by rwa [abs_of_nonneg (by positivity)])]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Nat.cast_pow]
      norm_num
    rw [Work.ParamRays.greenSeq]
    have h1 : Real.log 2 + (2 : ℝ) ^ k * Real.log (‖w‖ / 2)
        ≤ Real.posLog ‖Work.ParamRays.orbit c w k‖ := by
      rw [← hplog]; exact hple
    have h2 : ((2 : ℝ) ^ k)⁻¹ * (Real.log 2 + (2 : ℝ) ^ k * Real.log (‖w‖ / 2))
        ≤ ((2 : ℝ) ^ k)⁻¹ * Real.posLog ‖Work.ParamRays.orbit c w k‖ :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : ((2 : ℝ) ^ k)⁻¹ * (Real.log 2 + (2 : ℝ) ^ k * Real.log (‖w‖ / 2))
        = ((2 : ℝ) ^ k)⁻¹ * Real.log 2 + Real.log (‖w‖ / 2) := by
      have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
      field_simp
    have h4 : (0 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ * Real.log 2 := by
      have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity
    linarith
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      Real.log (‖w‖ / 2) ≤ Work.ParamRays.greenSeq c w k :=
    Filter.Eventually.of_forall hkey
  have hB : ∀ k : ℕ,
      Work.ParamRays.greenSeq c w k ≤ Real.log (2 * (‖w‖ + (‖c‖ + 1))) :=
    Work.ParamRays.GreenGrowth.greenSeq_le_log c w
  rw [Work.ParamRays.greenFun, Filter.limsup_eq]
  refine le_csInf ⟨Real.log (2 * (‖w‖ + (‖c‖ + 1))), Filter.Eventually.of_forall hB⟩ ?_
  intro b hb
  obtain ⟨n, hn1, hn2⟩ := (hev.and hb).exists
  exact le_trans hn1 hn2

/-- **The Fréchet derivative of a bump is bounded.**  For every bump `χ` at `c₀`, the
`ℂ`-valued function `chiC c₀ χ = fun z => (χ z : ℂ)` is `C^∞` with compact support,
so its Fréchet derivative is continuous with compact support, hence bounded. -/
theorem chiC_fderiv_bound (c₀ : ℂ) (χ : ContDiffBump c₀) :
    ∃ M : ℝ, ∀ z : ℂ, ‖fderiv ℝ (chiC c₀ χ) z‖ ≤ M := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (chiC c₀ χ) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => ((χ z : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.contDiff).comp (ContDiffBump.contDiff χ)
    exact h1
  have hcs : HasCompactSupport (chiC c₀ χ) := by
    have h1 : HasCompactSupport (fun z : ℂ => ((χ z : ℝ) : ℂ)) :=
      (ContDiffBump.hasCompactSupport χ).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    exact h1
  have hcs' : HasCompactSupport (fderiv ℝ (chiC c₀ χ)) := hcs.fderiv ℝ
  have hcont : Continuous (fderiv ℝ (chiC c₀ χ)) := hcd.continuous_fderiv (by simp)
  have hbdd : Bornology.IsBounded (Set.range (fderiv ℝ (chiC c₀ χ))) := by
    have himg : IsCompact
        ((fderiv ℝ (chiC c₀ χ)) '' tsupport (fderiv ℝ (chiC c₀ χ))) := hcs'.image hcont
    have hsub : Set.range (fderiv ℝ (chiC c₀ χ)) ⊆
        (fderiv ℝ (chiC c₀ χ)) '' tsupport (fderiv ℝ (chiC c₀ χ)) ∪ {0} := by
      intro L hL
      obtain ⟨w, rfl⟩ := hL
      by_cases hw : fderiv ℝ (chiC c₀ χ) w = 0
      · exact Or.inr hw
      · exact Or.inl ⟨w, subset_tsupport _ (by simpa [Function.mem_support] using hw), rfl⟩
    exact (himg.isBounded.union Bornology.isBounded_singleton).subset hsub
  rw [isBounded_iff_forall_norm_le] at hbdd
  obtain ⟨M, hM⟩ := hbdd
  exact ⟨M, fun w => hM _ (Set.mem_range_self w)⟩

/-- **Surgery data exist off the mandelbar.**  Given `c₀ ∉ Mb` we choose `ρ` small
enough that the ball `closedBall c₀ (3ρ)` lies in the band `{7g₀/8 < G < 9g₀/8}`
(possible because `G c₀ ·` is continuous at `c₀`, where it equals `g₀ = Gcrit c₀ > 0`),
the bump `χ` of radii `ρ/2 < ρ`, a derivative bound `Λ = max 1 M` from
`chiC_fderiv_bound`, and a radius `R₀` beyond which `G c₀ · > 3g₀/4` (possible by the
growth bound `greenFun_ge_log_half`). -/
theorem surgeryData_exists {c₀ : ℂ} (hc₀ : c₀ ∉ Work.NAKANE2.Mb) :
    Nonempty (Work.NAKANE2.SurgeryData c₀) := by
  have hg : 0 < Gcrit c₀ := Gcrit_pos hc₀
  -- joint continuity of the Green function, restricted to the parameter `c₀`
  have hcont : Continuous (fun z : ℂ => G c₀ z) := by
    have h := Work.NAKANE.continuous_greenFun
    have h2 : Continuous (fun z : ℂ => Work.ParamRays.greenFun (c₀, z).1 (c₀, z).2) :=
      h.comp (continuous_const.prodMk continuous_id)
    simpa [G] using h2
  -- the band radius
  have hca : ContinuousAt (fun z : ℂ => G c₀ z) c₀ := hcont.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.continuousAt_iff.mp hca) (Gcrit c₀ / 8) (by linarith)
  set ρ : ℝ := δ / 6 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hband : Metric.closedBall c₀ (3 * ρ) ⊆
      {z : ℂ | 7 / 8 * Gcrit c₀ < G c₀ z ∧ G c₀ z < 9 / 8 * Gcrit c₀} := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    have h3 : 3 * ρ = δ / 2 := by rw [hρdef]; ring
    have hlt : dist z c₀ < δ := by rw [h3] at hz; linarith
    have hd := hδ hlt
    rw [Real.dist_eq] at hd
    have hcc : G c₀ c₀ = Gcrit c₀ := rfl
    rw [hcc] at hd
    obtain ⟨ha, hb⟩ := abs_lt.mp hd
    exact ⟨by linarith, by linarith⟩
  -- the bump and its derivative bound
  let χ : ContDiffBump c₀ := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  obtain ⟨M, hM⟩ := chiC_fderiv_bound c₀ χ
  -- the radius carrying the complement of `W`
  set R₀ : ℝ := max (max 4 (2 * ‖c₀‖)) (2 * Real.exp (3 / 4 * Gcrit c₀) + 1) with hR₀def
  have hR₀pos : 0 < R₀ := by
    rw [hR₀def]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4)
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hWc : (W c₀)ᶜ ⊆ Metric.closedBall 0 R₀ := by
    intro z hz
    rw [Set.mem_compl_iff, mem_W, not_lt] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    push Not at hcon
    have hle1 : max 4 (2 * ‖c₀‖) ≤ R₀ := by rw [hR₀def]; exact le_max_left _ _
    have hR0le : max 4 (2 * ‖c₀‖) ≤ ‖z‖ := le_trans hle1 (le_of_lt hcon)
    have hge : Real.log (‖z‖ / 2) ≤ G c₀ z := greenFun_ge_log_half c₀ z hR0le
    have hlog : 3 / 4 * Gcrit c₀ < Real.log (‖z‖ / 2) := by
      rw [← Real.log_exp (3 / 4 * Gcrit c₀)]
      apply Real.log_lt_log (Real.exp_pos _)
      have hle2 : 2 * Real.exp (3 / 4 * Gcrit c₀) + 1 ≤ R₀ := by
        rw [hR₀def]; exact le_max_right _ _
      linarith
    linarith
  exact ⟨(show SurgeryData c₀ from
    { ρ := ρ, hρ := hρpos, χ := χ, hrIn := rfl, hrOut := rfl,
      Λ := max 1 M, hΛ1 := le_max_left _ _,
      hΛ := fun z => le_trans (hM z) (le_max_right _ _),
      R₀ := R₀, hR₀ := hR₀pos, hband := hband, hWc := hWc })⟩

end Work.NAKANE2.Surgery
