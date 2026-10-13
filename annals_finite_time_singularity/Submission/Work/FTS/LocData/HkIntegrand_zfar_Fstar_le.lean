/-
# `HkIntegrand_zfar_Fstar_le` — the pointwise `𝓗⁴`-majorant of the far part `zfar L F_*`

The localised datum of the route is `F_* ·χ(·/L) + βh`; the *far part* of the reference profile
is `zfar L F_* = (1 - χ(·/L))·F_*`.  This module proves the pointwise majorant

  `HkIntegrand α 4 (zfar L F_*) z θ ≤ C·α²·angMaj α θ/(1+z)²`

for a **single** constant `C`, all `0 < α ≤ 1`, all `L ≥ 1` and all `(z,θ) ∈ Iz × Iθ`.

## Structure of the proof

Write `f = zfar L F_* = G·F_*` with `G = 1 - χ(·/L)` a function of `z` alone, and split on `z`:

* **`z ≥ 1`.**  `HkIntegrand` is the sum of the squares of the weighted derivatives
  `D_z^i f·w/sin(2θ)^{η/2}` (`i ≤ 4`) and `D_z^j D_θ^i f·W` (`1 ≤ i`, `i+j ≤ 4`).
  `ZfarDzIterBound` and `ZfarMixedBound` bound the underlying
  weighted derivatives by `64·Kc·αΓ/z` and `6400000·Kc·αΓ/z`, where `Kc` is the uniform bound
  on `|D_z^c(1 - χ(·/L))|` coming from `ZFBase.DzIter_oneSubChi_bound_uniform`
  (`Kc ≥ 1`).  Squaring and using `1/z² ≤ 4/(1+z)²` (`z ≥ 1`) and
  `Γ²sin(2θ)^{-η}, Γ²sin(2θ)^{-γ} ≤ angMaj α θ` turns the two sums into
  `20·(64Kc)²·α²angMaj/(1+z)² + 100·(6.4·10⁶Kc)²·α²angMaj/(1+z)²`.
* **`z < 1`.**  Then `z < L`, so `χ(z'/L) = 1` for `z'` near `z` and `f` vanishes identically on
  a neighbourhood of `z`; all of its `D`-derivatives vanish at `z` and
  `HkIntegrand α 4 f z θ = 0` (`ZFBase.HkIntegrand_eq_zero_of_eventually_zero`), which is
  `≤` the (nonnegative) right-hand side.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.ZfarFstar.ZfarPointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary `rpow` algebra for the two weight factors -/

/-- `(s^{-e/2})² = s^{-e}` for `s ≥ 0`. -/
private lemma rpow_neg_half_sq (s e : ℝ) (hs : 0 ≤ s) : (s ^ (-(e / 2))) ^ 2 = s ^ (-e) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
  congr 1
  ring

/-- Squaring a weighted derivative: if `|x·w| ≤ A` and `s ≥ 0` then
`(x·(w·s^{-e/2}))² ≤ A²·s^{-e}`.  This is the step `w/sin(2θ)^{γ/2} = w·sin(2θ)^{-γ/2}`. -/
private lemma sq_mul_rpow_neg_le {x w s A e : ℝ} (hs : 0 ≤ s) (hx : |x * w| ≤ A) :
    (x * (w * s ^ (-(e / 2)))) ^ 2 ≤ A ^ 2 * s ^ (-e) := by
  have h1 : (x * (w * s ^ (-(e / 2)))) ^ 2 = (x * w) ^ 2 * (s ^ (-(e / 2))) ^ 2 := by ring
  rw [h1, rpow_neg_half_sq s e hs]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x * w)) hx 2)
    (Real.rpow_nonneg hs _)

theorem HkIntegrand_zfar_Fstar_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (L : ℝ), 1 ≤ L →
      ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ C * α ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨Kc, hKc1, hKc⟩ := ZFBase.DzIter_oneSubChi_bound_uniform
  refine ⟨20 * (64 * Kc) ^ 2 + 100 * (6400000 * Kc) ^ 2, by positivity, ?_⟩
  intro α hα hα1 L hL z hzI θ hθ
  have hz0 : 0 ≤ z := hzI
  have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hs0 : 0 ≤ Real.sin (2 * θ) := ZFBase.sin_two_nonneg_Iθ hθ
  have hang0 : 0 ≤ angMaj α θ := angMaj_nonneg hθ
  by_cases hz1 : 1 ≤ z
  · -- #### the main case `z ≥ 1`
    have hzpos : 0 < z := by linarith
    have hden : 0 < (1 + z) ^ 2 := by positivity
    have hsη : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs0 _
    have hsgam : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
    -- the two pointwise weighted bounds
    have hDzb : ∀ i' : ℕ, i' ≤ 4 →
        |Work.Spaces.DzIter i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
          * Work.Spaces.w z| ≤ 64 * Kc * α * Work.Spaces.Gam α θ / z :=
      fun i' hi' => ZfarDzIterBound hKc hKc1 α hα hα1 L hL z hz1 θ hθ i' hi'
    have hMxb : ∀ i' j' : ℕ, 1 ≤ i' → i' + j' ≤ 4 →
        |Work.Spaces.mixed j' i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
          * Work.Spaces.w z| ≤ 6400000 * Kc * α * Work.Spaces.Gam α θ / z :=
      fun i' j' hi' hij' =>
        ZfarMixedBound hKc hKc1 α hα hα1 L hL z hz1 θ hθ i' hi' j' hij'
    -- the `D_z`-terms
    have hterm1 : ∀ i' ∈ Finset.range 5,
        (Work.Spaces.DzIter i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2 := by
      intro i' hi'
      have hi'4 : i' ≤ 4 := by rw [Finset.mem_range] at hi'; omega
      have hb := hDzb i' hi'4
      have hw : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hs0]
      rw [hw]
      refine le_trans (sq_mul_rpow_neg_le hs0 hb) (le_of_eq ?_)
      ring
    -- the mixed terms
    have hterm2 : ∀ i' ∈ Finset.range 5, ∀ j' ∈ Finset.range 5,
        (if 1 ≤ i' ∧ i' + j' ≤ 4 then
          (Work.Spaces.mixed j' i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2 := by
      intro i' hi' j' hj'
      by_cases hc : 1 ≤ i' ∧ i' + j' ≤ 4
      · rw [if_pos hc]
        have hb := hMxb i' j' hc.1 hc.2
        have hWt : Work.Spaces.Wt α z θ
            = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
          rw [Work.Spaces.Wt, Work.Spaces.wTheta]
        rw [hWt]
        refine le_trans (sq_mul_rpow_neg_le hs0 hb) (le_of_eq ?_)
        ring
      · rw [if_neg hc]
        exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg (6400000 * Kc))
          (sq_nonneg α)) (sq_nonneg (Work.Spaces.Gam α θ))) hsgam) (le_of_lt (by positivity))
    -- the two sums
    have hsum1 : (∑ i' ∈ Finset.range 5,
        (Work.Spaces.DzIter i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * ((64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2) := by
      calc (∑ i' ∈ Finset.range 5,
          (Work.Spaces.DzIter i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i' ∈ Finset.range 5, ((64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2) := Finset.sum_le_sum hterm1
        _ = 5 * ((64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2) := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsum2 : (∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5,
        (if 1 ≤ i' ∧ i' + j' ≤ 4 then
          (Work.Spaces.mixed j' i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ 25 * ((6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2) := by
      calc (∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5,
          (if 1 ≤ i' ∧ i' + j' ≤ 4 then
            (Work.Spaces.mixed j' i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5,
              ((6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2) :=
            Finset.sum_le_sum (fun i' hi' => Finset.sum_le_sum (fun j' hj' => hterm2 i' hi' j' hj'))
        _ = 25 * ((6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    -- `1/z² ≤ 4/(1+z)²` for `z ≥ 1`
    have hz2 : 1 / z ^ 2 ≤ 4 / (1 + z) ^ 2 := by
      have h1 : (0 : ℝ) < z ^ 2 := by positivity
      have h2 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
      rw [div_le_div_iff₀ h1 h2]
      nlinarith [hz1]
    -- `Γ²sin^{-η}, Γ²sin^{-γ} ≤ angMaj`
    have hη : Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ angMaj α θ := by
      rw [angMaj_apply]
      have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_nonneg (sq_nonneg _) hsgam
      linarith
    have hgam : Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ angMaj α θ := by
      rw [angMaj_apply]
      have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_nonneg (sq_nonneg _) hsη
      linarith
    -- the final comparison
    have hkey : 5 * ((64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2)
          + 25 * ((6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2)
        ≤ (20 * (64 * Kc) ^ 2 + 100 * (6400000 * Kc) ^ 2) * α ^ 2 * angMaj α θ
            / (1 + z) ^ 2 := by
      set X1 : ℝ := (64 * Kc) ^ 2 * α ^ 2
        * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) with hX1
      set X2 : ℝ := (6400000 * Kc) ^ 2 * α ^ 2
        * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) with hX2
      have hX10 : 0 ≤ X1 := by
        rw [hX1]; exact mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) hsη)
      have hX20 : 0 ≤ X2 := by
        rw [hX2]; exact mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) hsgam)
      have hX1le : X1 ≤ (64 * Kc) ^ 2 * α ^ 2 * angMaj α θ := by
        rw [hX1]
        exact mul_le_mul_of_nonneg_left hη (by positivity)
      have hX2le : X2 ≤ (6400000 * Kc) ^ 2 * α ^ 2 * angMaj α θ := by
        rw [hX2]
        exact mul_le_mul_of_nonneg_left hgam (by positivity)
      calc 5 * ((64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2)
          + 25 * ((6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2)
          = (5 * X1 + 25 * X2) * (1 / z ^ 2) := by rw [hX1, hX2]; ring
        _ ≤ (5 * X1 + 25 * X2) * (4 / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_left hz2 (by linarith)
        _ = (20 * X1 + 100 * X2) / (1 + z) ^ 2 := by ring
        _ ≤ (20 * ((64 * Kc) ^ 2 * α ^ 2 * angMaj α θ)
              + 100 * ((6400000 * Kc) ^ 2 * α ^ 2 * angMaj α θ))
              / (1 + z) ^ 2 :=
            div_le_div_of_nonneg_right (by linarith [hX1le, hX2le]) (le_of_lt hden)
        _ = (20 * (64 * Kc) ^ 2 + 100 * (6400000 * Kc) ^ 2) * α ^ 2 * angMaj α θ
              / (1 + z) ^ 2 := by ring
    rw [Work.Spaces.HkIntegrand]
    exact le_trans (add_le_add hsum1 hsum2) hkey
  · -- #### the vanishing case `z < 1`
    have hzlt : z < 1 := lt_of_not_ge hz1
    have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have hLz : z < L := lt_of_lt_of_le hzlt hL
    have hzero := ZFBase.HkIntegrand_eq_zero_of_eventually_zero (α := α) (k := 4) (z := z) (θ := θ)
      (f := Work.Stability.zfar L (Work.Construction.Fstar α))
      (ZFBase.zfar_eventually_zero hL0 hz0 hLz)
    rw [hzero]
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg α)) hang0)
      (le_of_lt (by positivity : (0 : ℝ) < (1 + z) ^ 2))

end Work.FTS.LocData
