import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.coordError_bound
import Submission.Work.FatouCoord.Estimate.coordError_deriv_bound
import Submission.Work.FatouCoord.Estimate.wMap_re_growth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Holomorphy of the Fatou coordinate in the chart

The Fatou coordinate of a parabolic germ, written in the chart `w = -1/z`, is the series

`fatouCoordW f c w = approxCoord c w + ∑' k, coordError f c ((wMap f)^[k] w)`

where `approxCoord c w = w - c log w` is the approximate Abel coordinate and `coordError` is
its defect.  In this file we show that for `c = 1 - a` the series converges locally uniformly
on a right half-plane `{Re w > N}` and hence that `fatouCoordW f (1 - a)` is holomorphic there.

The two quantitative inputs are

* `Estimate.wMap_re_growth`: the orbit moves to the right, `Re ((wMap f)^[k] w) ≥ Re w + k/2`,
* `Estimate.coordError_bound`: `‖coordError f (1 - a) w‖ ≤ B / ‖w‖ ^ 2` for `Re w > N₁`.

Choosing `N` past both levels, every orbit starting in `{Re w > N}` stays there and grows, so
`‖coordError f (1 - a) ((wMap f)^[k] w)‖ ≤ B / (((γ/2) (k+1)) ^ 2)` with `γ = min N 1`; this is a
summable majorant of the terms, and each term is holomorphic on the half-plane (the defect is
holomorphic where `Re (> 1/r + 9)`, by `hasDerivAt_coordError`, and the iterates map into that
region).  Local uniform convergence of a series of holomorphic functions is Mathlib's
`Complex.differentiableOn_tsum_of_summable_norm`.  The remaining term `approxCoord` is
holomorphic on the half-plane because it stays away from the slit `(-∞, 0]` of the principal
logarithm.
-/

namespace Work.FatouCoord.Exist

open Work.FatouCoord
open scoped Topology
open Set Filter Metric

noncomputable section

theorem fatouCoordW_differentiable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') : ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧ DifferentiableOn ℂ (fatouCoordW f (1 - a)) {w : ℂ | N < w.re} := by
  obtain ⟨M, hMpos, hrM, hgrowthM₀⟩ := Estimate.wMap_re_growth hb
  obtain ⟨N₁, B, hN₁pos, hBnn, hrN₁, hcErr⟩ := Estimate.coordError_bound hb
  -- the final level
  set N : ℝ := max (max M N₁) (1 / r + 9) + 1 with hNdef
  have hMN : M < N := by
    rw [hNdef]
    have h1 : M ≤ max M N₁ := le_max_left _ _
    have h2 : max M N₁ ≤ max (max M N₁) (1 / r + 9) := le_max_left _ _
    linarith
  have hN₁N : N₁ < N := by
    rw [hNdef]
    have h1 : N₁ ≤ max M N₁ := le_max_right _ _
    have h2 : max M N₁ ≤ max (max M N₁) (1 / r + 9) := le_max_left _ _
    linarith
  have hN9 : 1 / r + 9 < N := by
    rw [hNdef]
    have h1 : 1 / r + 9 ≤ max (max M N₁) (1 / r + 9) := le_max_right _ _
    linarith
  have hNr : 1 / r < N := lt_trans hrM hMN
  have hNpos : 0 < N := lt_trans hMpos hMN
  set U : Set ℂ := {w : ℂ | N < w.re} with hUdef
  set V : Set ℂ := {w : ℂ | 1 / r + 9 < w.re} with hVdef
  have hUopen : IsOpen U := by
    rw [hUdef]; exact isOpen_lt continuous_const Complex.continuous_re
  -- the sharp orbit growth, at the final level
  have hgrowthM : ∀ w : ℂ, N < w.re → ∀ k : ℕ,
      w.re + (k : ℝ) / 2 ≤ ((wMap f)^[k] w).re :=
    fun w hw k => hgrowthM₀ w (lt_trans hMN hw) k
  -- differentiability of the defect on `V`
  have hVdiff : DifferentiableOn ℂ (coordError f (1 - a)) V := by
    intro z hz
    have hz' : 1 / r + 9 < z.re := hz
    have hWslit : wMap f z ∈ Complex.slitPlane := Or.inl (Estimate.wMap_sub_aux hb hz').2
    exact ((Estimate.hasDerivAt_coordError hb hz' hWslit).differentiableAt).differentiableWithinAt
  -- `wMap f` is holomorphic on `U`
  have hwMapDiff : DifferentiableOn ℂ (wMap f) U := by
    intro z hz
    have hz' : N < z.re := hz
    have h9 : 1 / r + 9 < z.re := lt_trans hN9 hz'
    exact ((Estimate.wMap_hasDerivAt hb h9).differentiableAt).differentiableWithinAt
  have hmapU : MapsTo (wMap f) U U := by
    intro z hz
    have hz' : N < z.re := hz
    have h := hgrowthM z hz' 1
    have h1 : ((wMap f)^[1] z).re = (wMap f z).re := by simp
    rw [h1] at h
    show N < (wMap f z).re
    linarith
  have hiterDiff : ∀ k : ℕ, DifferentiableOn ℂ (fun w : ℂ => (wMap f)^[k] w) U := by
    intro k
    induction k with
    | zero =>
      have h0 : (fun w : ℂ => (wMap f)^[0] w) = id := by funext w; simp
      rw [h0]; exact differentiableOn_id
    | succ k ih =>
      rw [Function.iterate_succ']
      exact hwMapDiff.comp ih (mapsTo_iterate_of_mapsTo hmapU k)
  have hFdiff : ∀ k : ℕ,
      DifferentiableOn ℂ (fun w : ℂ => coordError f (1 - a) ((wMap f)^[k] w)) U := by
    intro k
    refine hVdiff.comp (hiterDiff k) ?_
    intro w hw
    have hw' : N < w.re := hw
    show 1 / r + 9 < ((wMap f)^[k] w).re
    have h := hgrowthM w hw' k
    have hk : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
    linarith
  -- the summable majorant
  set γ : ℝ := min N 1 with hγdef
  have hγpos : 0 < γ := lt_min hNpos one_pos
  have hγle1 : γ ≤ 1 := by rw [hγdef]; exact min_le_right _ _
  have hγleN : γ ≤ N := by rw [hγdef]; exact min_le_left _ _
  have hbound : ∀ (k : ℕ) (w : ℂ), w ∈ U →
      ‖coordError f (1 - a) ((wMap f)^[k] w)‖ ≤ B / ((γ / 2) * ((k : ℝ) + 1)) ^ 2 := by
    intro k w hw
    have hw' : N < w.re := hw
    have hgr := hgrowthM w hw' k
    have hN₁lt : N₁ < ((wMap f)^[k] w).re := by
      have hk : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      have h1 : N₁ < w.re := lt_trans hN₁N hw'
      linarith
    have hb1 : ‖coordError f (1 - a) ((wMap f)^[k] w)‖ ≤ B / ‖((wMap f)^[k] w)‖ ^ 2 :=
      hcErr _ hN₁lt
    have hge : (γ / 2) * ((k : ℝ) + 1) ≤ ‖((wMap f)^[k] w)‖ := by
      have h1 : ((wMap f)^[k] w).re ≤ ‖((wMap f)^[k] w)‖ := Complex.re_le_norm _
      have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have h2 : (γ / 2) * ((k : ℝ) + 1) ≤ N + (k : ℝ) / 2 := by nlinarith
      linarith
    have hpos : 0 < (γ / 2) * ((k : ℝ) + 1) := by
      have : 0 < γ / 2 := by linarith
      positivity
    have hsq : ((γ / 2) * ((k : ℝ) + 1)) ^ 2 ≤ ‖((wMap f)^[k] w)‖ ^ 2 :=
      pow_le_pow_left₀ hpos.le hge 2
    exact le_trans hb1 (div_le_div_of_nonneg_left hBnn (pow_pos hpos 2) hsq)
  have hsummable : Summable (fun k : ℕ => B / ((γ / 2) * ((k : ℝ) + 1)) ^ 2) := by
    have h0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h1 : Summable (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ)) ^ 2) :=
      (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr h0
    have h2 : Summable (fun n : ℕ => (B / (γ / 2) ^ 2) * ((1 : ℝ) / ((((n + 1 : ℕ)) : ℝ)) ^ 2)) :=
      h1.mul_left _
    refine h2.congr (fun n => ?_)
    push_cast
    rw [mul_one_div, mul_pow, div_div]
  -- holomorphy of the approximate coordinate on `U`
  have hAdiff : DifferentiableOn ℂ (approxCoord (1 - a)) U := by
    have hlog : DifferentiableOn ℂ Complex.log U := by
      intro z hz
      have hz' : N < z.re := hz
      exact (Complex.differentiableAt_log (Or.inl (lt_trans hNpos hz'))).differentiableWithinAt
    show DifferentiableOn ℂ (fun w : ℂ => w - (1 - a) * Complex.log w) U
    exact differentiableOn_id.sub (hlog.const_mul (1 - a))
  have htsum : DifferentiableOn ℂ
      (fun w : ℂ => ∑' k : ℕ, coordError f (1 - a) ((wMap f)^[k] w)) U :=
    Complex.differentiableOn_tsum_of_summable_norm hsummable hFdiff hUopen hbound
  have hsum : DifferentiableOn ℂ
      (fun w : ℂ => approxCoord (1 - a) w
        + ∑' k : ℕ, coordError f (1 - a) ((wMap f)^[k] w)) U :=
    hAdiff.add htsum
  refine ⟨N, hNpos, hNr, ?_⟩
  show DifferentiableOn ℂ
    (fun w : ℂ => approxCoord (1 - a) w
      + ∑' k : ℕ, coordError f (1 - a) ((wMap f)^[k] w)) U
  exact hsum

end

end Work.FatouCoord.Exist
