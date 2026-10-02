import Mathlib
import Submission.Work.FlowerGlue2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

/-
## The transfer form of a repelling coordinate

Given a conjugacy `F (z₁ + s·ζ) = z₁ + s·f ζ` for `‖ζ‖ < r`, and a repelling conjugacy `V` for
`f` in the chart (`V (w+1) = wMap f (V w)` on `{Re w < -R}`, injective there, and
`‖V w - w‖ ≤ ‖w‖/2`), the transfer form `w ↦ z₁ + s·(-1/V w)` is a repelling coordinate for
`F` at `z₁` on the far-left half-plane `{Re w < -R₁}`, provided `R₁ ≥ R+1`, `R₁ ≥ 1` and
`2/r < R₁`.

Proof sketch:
* diff: `V` is differentiable and nonzero on `{Re w < -R₁}` (nonzero since `‖V w‖ ≥ ‖w‖/2 > 0`);
  a constant plus `s` times `-1/V`.
* shift: for `w.re < -R₁` we have `(w+1).re < -R₁+1 ≤ -R`, so `V (w+1) = wMap f (V w)`; then
  `-1/(wMap f (V w)) = f (-1/(V w))` by `Work.FatouCoord.wMap_apply` (`wMap f x = -1/f(-1/x)`),
  and `‖-1/(V w)‖ ≤ 2/‖w‖ < 2/R₁ < r` puts the argument in the ball where the conjugacy holds.
* inj: `s ≠ 0` and `V` injective.
* ne_zero: `V w ≠ 0`.
* small: `‖Ψ w - z₁‖ = ‖s‖/‖V w‖ ≤ 2‖s‖/‖w‖ → 0`.
-/
theorem isRepellingCoord_transfer {F : ℂ → ℂ} {f V : ℂ → ℂ} {z₁ s : ℂ} {r R R₁ : ℝ}
    (hs : s ≠ 0) (hr : 0 < r) (hR₁ : 1 ≤ R₁) (hRR₁ : R + 1 ≤ R₁) (h2r : 2 / r < R₁)
    (hconj : ∀ ζ : ℂ, ‖ζ‖ < r → F (z₁ + s * ζ) = z₁ + s * f ζ)
    (hVdiff : DifferentiableOn ℂ V {w : ℂ | w.re < -R})
    (hVshift : ∀ w : ℂ, w.re < -R → V (w + 1) = Work.FatouCoord.wMap f (V w))
    (hVinj : Set.InjOn V {w : ℂ | w.re < -R})
    (hVclose : ∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ ‖w‖ / 2) :
    Work.FatouCoord.IsRepellingCoord F z₁ R₁ (fun w => z₁ + s * (-1 / V w)) := by
  have hnn : ∀ x : ℂ, (-1 : ℂ) / (-1 / x) = x := fun x => by field_simp
  have hR₁pos : 0 < R₁ := lt_of_lt_of_le one_pos hR₁
  -- the inclusion of the two half-planes
  have hsub : ∀ w : ℂ, w.re < -R₁ → w.re < -R := by
    intro w hw
    linarith
  -- `V` does not shrink the norm by more than half on the far left half-plane
  have hnorm_ge : ∀ w : ℂ, w.re < -R → ‖w‖ / 2 ≤ ‖V w‖ := by
    intro w hw
    have h3 : |‖V w‖ - ‖w‖| ≤ ‖V w - w‖ := abs_norm_sub_norm_le (V w) w
    have h4 : -‖V w - w‖ ≤ ‖V w‖ - ‖w‖ := (abs_le.mp h3).1
    have h5 := hVclose w hw
    linarith
  -- on `{Re w < -R₁}` the point `w` is far away from the origin
  have hnorm_w : ∀ w : ℂ, w.re < -R₁ → R₁ < ‖w‖ := by
    intro w hw
    have h1 : -w.re ≤ ‖w‖ := le_trans (neg_le_abs w.re) (Complex.abs_re_le_norm w)
    linarith
  have hVne : ∀ w : ℂ, w.re < -R₁ → V w ≠ 0 := by
    intro w hw
    have h1 : ‖w‖ / 2 ≤ ‖V w‖ := hnorm_ge w (hsub w hw)
    have h2 : 0 < ‖w‖ := by have := hnorm_w w hw; linarith
    exact norm_pos_iff.mp (by linarith)
  have hle_aux : ∀ w : ℂ, w.re < -R₁ → ‖(-1 : ℂ) / V w‖ ≤ 2 / ‖w‖ := by
    intro w hw
    have h1 : ‖w‖ / 2 ≤ ‖V w‖ := hnorm_ge w (hsub w hw)
    have h2 : 0 < ‖w‖ := by have := hnorm_w w hw; linarith
    have h3 : 0 < ‖V w‖ := by linarith
    rw [norm_div, norm_neg, norm_one]
    rw [div_le_div_iff₀ h3 h2]
    linarith
  have h2r' : 2 / R₁ < r := by
    have hrne : r ≠ 0 := ne_of_gt hr
    have h : 2 / r * r < R₁ * r := mul_lt_mul_of_pos_right h2r hr
    rw [div_mul_cancel₀ 2 hrne] at h
    rw [div_lt_iff₀ hR₁pos]
    linarith
  -- the coordinate `-1/(V w)` is inside the ball of the germ conjugacy
  have hlt_aux : ∀ w : ℂ, w.re < -R₁ → ‖(-1 : ℂ) / V w‖ < r := by
    intro w hw
    have h2 : 0 < ‖w‖ := by have := hnorm_w w hw; linarith
    have h5 : 2 / ‖w‖ < 2 / R₁ := by
      rw [div_lt_div_iff₀ h2 hR₁pos]
      have := hnorm_w w hw
      linarith
    linarith [hle_aux w hw]
  refine ⟨hR₁pos, ?_, ?_, ?_, ?_, ?_⟩
  · -- holomorphy: `V` is holomorphic and nonzero, `Ψ = z₁ + s·(-1/V)`
    have hd1 : DifferentiableOn ℂ V {w : ℂ | w.re < -R₁} :=
      hVdiff.mono (fun w hw => hsub w hw)
    have hd2 : DifferentiableOn ℂ (fun w : ℂ => (-1 : ℂ) / V w) {w : ℂ | w.re < -R₁} :=
      (differentiableOn_const (c := (-1 : ℂ))).div hd1 (fun w hw => hVne w hw)
    exact (differentiableOn_const (c := z₁)).add ((differentiableOn_const (c := s)).mul hd2)
  · -- equivariance: use the conjugacy `F (z₁ + s·ζ) = z₁ + s·f ζ` and `wMap`
    intro w hw
    have hwR : w.re < -R := hsub w hw
    have hkey : (-1 : ℂ) / V (w + 1) = f ((-1) / V w) := by
      rw [hVshift w hwR, Work.FatouCoord.wMap_apply]
      exact hnn _
    show z₁ + s * ((-1) / V (w + 1)) = F (z₁ + s * ((-1) / V w))
    rw [hkey]
    exact (hconj _ (hlt_aux w hw)).symm
  · -- injectivity
    intro x hx y hy hxy
    have h1 : s * ((-1) / V x) = s * ((-1) / V y) := add_left_cancel hxy
    have h2 : (-1) / V x = (-1) / V y := mul_left_cancel₀ hs h1
    have h3 : V x = V y := by
      have h4 := congrArg (fun z : ℂ => (-1) / z) h2
      simpa only [hnn] using h4
    exact hVinj (hsub x hx) (hsub y hy) h3
  · -- `Ψ` avoids `z₁`
    intro w hw hcon
    have h1 : s * ((-1) / V w) = 0 := by
      exact add_left_cancel (show z₁ + s * ((-1) / V w) = z₁ + 0 by simpa using hcon)
    have h2 : (-1) / V w = 0 := (mul_eq_zero.mp h1).resolve_left hs
    exact (div_ne_zero (by norm_num) (hVne w hw)) h2
  · -- `Ψ w → z₁` at the far end
    intro ε hε
    refine ⟨max R₁ (2 * ‖s‖ / ε + 1), fun w hw => ?_⟩
    have hw₁ : w.re < -R₁ := lt_of_lt_of_le hw (neg_le_neg (le_max_left _ _))
    have hwn : 2 * ‖s‖ / ε + 1 ≤ ‖w‖ := by
      have hmax1 : R₁ ≤ max R₁ (2 * ‖s‖ / ε + 1) := le_max_left _ _
      have hmax2 : 2 * ‖s‖ / ε + 1 ≤ max R₁ (2 * ‖s‖ / ε + 1) := le_max_right _ _
      have h1 : -w.re ≤ ‖w‖ := le_trans (neg_le_abs w.re) (Complex.abs_re_le_norm w)
      linarith
    have hpos_w : 0 < ‖w‖ := by
      have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
      have h2 : 0 ≤ 2 * ‖s‖ / ε := div_nonneg (by linarith) hε.le
      linarith
    have hlt2 : 2 * ‖s‖ < ε * ‖w‖ := by
      have hlt : 2 * ‖s‖ / ε < ‖w‖ := by linarith
      have := (div_lt_iff₀ hε).mp hlt
      linarith
    have hgoal : z₁ + s * ((-1) / V w) - z₁ = s * ((-1) / V w) := by ring
    rw [hgoal, norm_mul]
    have hfin : ‖s‖ * (2 / ‖w‖) < ε := by
      have hkey : ‖s‖ * (2 / ‖w‖) = 2 * ‖s‖ / ‖w‖ := by ring
      rw [hkey, div_lt_iff₀ hpos_w]
      exact hlt2
    have hb : ‖(-1 : ℂ) / V w‖ ≤ 2 / ‖w‖ := hle_aux w hw₁
    have hmul := mul_le_mul_of_nonneg_left hb (norm_nonneg s)
    linarith


end Work.FlowerGlue2
