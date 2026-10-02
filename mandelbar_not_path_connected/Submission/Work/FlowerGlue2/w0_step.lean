import Mathlib
import Submission.Work.FlowerGlue2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

open Filter Set Metric
open scoped Topology

open Work.PARIMPL (ParNormal Ft)

/-- **The first-order step of the `w0`-chart at the parabolic parameter.**

In the chart `z = m c₀ + s c₀·ζ` of the parameter normal form the coordinate is
`w0 P z = -P.s c₀ / (z - d.z₁) = -1/ζ`, and at the parabolic parameter `c₀` the second return map
is `ζ ↦ ζ + ζ² h_{c₀}(ζ)` on the chart ball (the two fixed points `±a` have collided,
`a_{c₀} = 0`).  Hence `w0 (Ft c₀ z) - w0 z - 1 = (h_{c₀} ζ - 1 - ζ h_{c₀} ζ)/(1 + ζ h_{c₀} ζ)`,
and with `h_{c₀}(0) = 1` the numerator is `O(ζ)`: the chart coordinate is an *approximate*
Fatou coordinate with unit step and error of first order in the distance to the parabolic
point. -/
theorem w0_step {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (hτ : P.h c₀ 0 = 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ≠ d.z₁ → ‖z - d.z₁‖ < r →
      (Work.PARIMPL.Ft c₀ z ≠ d.z₁ ∧
        ‖Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z) - Work.FlowerGlue2.w0 P z - 1‖
          ≤ C * ‖z - d.z₁‖) := by
  have hc₀ : c₀ ∈ ball c₀ P.ρ₀ := mem_ball_self P.hρ₀
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ hc₀
  have hsn : 0 < ‖P.s c₀‖ := norm_pos_iff.mpr hs
  have hm : P.m c₀ = d.z₁ := P.m₀
  have ha : P.a c₀ = 0 := by
    have h := P.a_sq c₀ hc₀
    rw [P.a2₀] at h
    have h' : P.a c₀ * P.a c₀ = 0 := by simpa [pow_two] using h
    exact mul_self_eq_zero.mp h'
  have hb := P.bounds c₀ hc₀
  have hbA : 0 ≤ P.A := P.hA
  have hbr : 0 < P.r := P.hr
  refine ⟨min P.r (1 / 4) * ‖P.s c₀‖, mul_pos (lt_min hbr (by norm_num)) hsn,
    (P.A / 2 + 2 * ‖P.h1 c₀‖ + 4) / ‖P.s c₀‖,
    div_nonneg (by nlinarith [hbA, norm_nonneg (P.h1 c₀)]) (le_of_lt hsn), ?_⟩
  intro z hz hzd
  set ζ : ℂ := (z - d.z₁) / P.s c₀ with hζdef
  have hζlt : ‖ζ‖ < min P.r (1 / 4) := by
    rw [hζdef, norm_div, div_lt_iff₀ hsn]
    exact hzd
  have hrζ : ‖ζ‖ < P.r := lt_of_lt_of_le hζlt (min_le_left _ _)
  have hq : ‖ζ‖ < 1 / 4 := lt_of_lt_of_le hζlt (min_le_right _ _)
  have hzsub : z - d.z₁ = P.s c₀ * ζ := by
    rw [hζdef]; field_simp
  have hζne : ζ ≠ 0 := by
    intro h
    apply hz
    have : z - d.z₁ = 0 := by rw [hzsub, h, mul_zero]
    exact sub_eq_zero.mp this
  have hz_eq : z = P.m c₀ + P.s c₀ * ζ := by
    rw [hm, ← sub_eq_iff_eq_add']
    exact hzsub
  have hnorm : ∀ w : ℂ, ‖w‖ < P.r → ‖P.h c₀ w‖ ≤ 2 := fun w hw => hb.2.2.2.1 w hw
  have hclose : ∀ w : ℂ, ‖w‖ < P.r → ‖P.h c₀ w - 1 - P.h1 c₀ * w‖ ≤ P.A * ‖w‖ ^ 2 := by
    intro w hw
    have h := hb.2.2.1 w hw
    rwa [hτ] at h
  have hsmall : ‖ζ * P.h c₀ ζ‖ ≤ 1 / 2 := by
    rw [norm_mul]
    calc ‖ζ‖ * ‖P.h c₀ ζ‖ ≤ (1 / 4) * 2 :=
          mul_le_mul (le_of_lt hq) (hnorm ζ hrζ) (norm_nonneg _) (by norm_num)
      _ = 1 / 2 := by norm_num
  have h1ζh : 1 + ζ * P.h c₀ ζ ≠ 0 := by
    intro h
    have hx : ‖ζ * P.h c₀ ζ‖ = 1 := by
      have hh : ζ * P.h c₀ ζ = -1 := by linear_combination h
      rw [hh, norm_neg, norm_one]
    linarith
  have hX : ζ * (1 + ζ * P.h c₀ ζ) ≠ 0 := mul_ne_zero hζne h1ζh
  have hNF : Work.Implosion.normalForm (P.a c₀) (P.h c₀) ζ = ζ + ζ ^ 2 * P.h c₀ ζ := by
    rw [ha]; simp [Work.Implosion.normalForm]
  have hconj := P.conj c₀ hc₀ ζ (by rw [mem_ball, dist_eq_norm]; simpa using hrζ)
  have hFt_sub : Ft c₀ z - d.z₁ = P.s c₀ * (ζ + ζ ^ 2 * P.h c₀ ζ) := by
    have hFt : Ft c₀ z = P.m c₀ + P.s c₀ * (ζ + ζ ^ 2 * P.h c₀ ζ) := by
      rw [hz_eq, hconj, hNF]
    rw [hFt, hm]; ring
  have hfac : ζ + ζ ^ 2 * P.h c₀ ζ = ζ * (1 + ζ * P.h c₀ ζ) := by ring
  have hFtne : Ft c₀ z ≠ d.z₁ := by
    intro hcon
    have h0 : Ft c₀ z - d.z₁ = 0 := sub_eq_zero.mpr hcon
    rw [hFt_sub, hfac] at h0
    exact mul_ne_zero hs hX h0
  have hw0z : w0 P z = -1 / ζ := by
    rw [w0_apply, hzsub]
    field_simp
  have hw0ft : w0 P (Ft c₀ z) = -1 / (ζ * (1 + ζ * P.h c₀ ζ)) := by
    rw [w0_apply, show Ft c₀ z - d.z₁ = P.s c₀ * (ζ * (1 + ζ * P.h c₀ ζ)) from by
      rw [hFt_sub, hfac]]
    field_simp
  have hident : w0 P (Ft c₀ z) - w0 P z - 1
      = (P.h c₀ ζ - 1 - ζ * P.h c₀ ζ) / (1 + ζ * P.h c₀ ζ) := by
    rw [hw0ft, hw0z]
    field_simp
    ring
  have hN_bound :
      ‖P.h c₀ ζ - 1 - ζ * P.h c₀ ζ‖ ≤ (P.A / 4 + ‖P.h1 c₀‖ + 2) * ‖ζ‖ := by
    have hdec : P.h c₀ ζ - 1 - ζ * P.h c₀ ζ
        = (P.h c₀ ζ - 1 - P.h1 c₀ * ζ) + (P.h1 c₀ * ζ - ζ * P.h c₀ ζ) := by ring
    rw [hdec]
    calc ‖(P.h c₀ ζ - 1 - P.h1 c₀ * ζ) + (P.h1 c₀ * ζ - ζ * P.h c₀ ζ)‖
        ≤ ‖P.h c₀ ζ - 1 - P.h1 c₀ * ζ‖ + ‖P.h1 c₀ * ζ - ζ * P.h c₀ ζ‖ := norm_add_le _ _
      _ ≤ P.A * ‖ζ‖ ^ 2 + ‖ζ‖ * (‖P.h1 c₀‖ + 2) := by
          have h2 : ‖P.h1 c₀ * ζ - ζ * P.h c₀ ζ‖ ≤ ‖ζ‖ * (‖P.h1 c₀‖ + 2) := by
            have he : P.h1 c₀ * ζ - ζ * P.h c₀ ζ = ζ * (P.h1 c₀ - P.h c₀ ζ) := by ring
            rw [he, norm_mul]
            calc ‖ζ‖ * ‖P.h1 c₀ - P.h c₀ ζ‖
                ≤ ‖ζ‖ * (‖P.h1 c₀‖ + ‖P.h c₀ ζ‖) :=
                  mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg ζ)
              _ ≤ ‖ζ‖ * (‖P.h1 c₀‖ + 2) :=
                  mul_le_mul_of_nonneg_left (by linarith [hnorm ζ hrζ]) (norm_nonneg ζ)
          linarith [hclose ζ hrζ]
      _ ≤ (P.A / 4 + ‖P.h1 c₀‖ + 2) * ‖ζ‖ := by
          have hsq : ‖ζ‖ ^ 2 ≤ (1 / 4) * ‖ζ‖ := by
            have := mul_le_mul_of_nonneg_right (le_of_lt hq) (norm_nonneg ζ)
            simpa [pow_two] using this
          have hA : P.A * ‖ζ‖ ^ 2 ≤ (P.A / 4) * ‖ζ‖ := by
            calc P.A * ‖ζ‖ ^ 2 ≤ P.A * ((1 / 4) * ‖ζ‖) := mul_le_mul_of_nonneg_left hsq hbA
              _ = (P.A / 4) * ‖ζ‖ := by ring
          linarith
  have hD_bound : 1 / 2 ≤ ‖1 + ζ * P.h c₀ ζ‖ := by
    have h3 : 1 - ‖ζ * P.h c₀ ζ‖ ≤ ‖1 + ζ * P.h c₀ ζ‖ := by
      have := norm_sub_le ((1 : ℂ) + ζ * P.h c₀ ζ) (ζ * P.h c₀ ζ)
      simp only [add_sub_cancel_right, norm_one] at this
      linarith
    linarith
  have hζ_eq : ‖ζ‖ = ‖z - d.z₁‖ / ‖P.s c₀‖ := by rw [hζdef, norm_div]
  refine ⟨hFtne, ?_⟩
  calc ‖w0 P (Ft c₀ z) - w0 P z - 1‖
      = ‖(P.h c₀ ζ - 1 - ζ * P.h c₀ ζ) / (1 + ζ * P.h c₀ ζ)‖ := by rw [hident]
    _ = ‖P.h c₀ ζ - 1 - ζ * P.h c₀ ζ‖ / ‖1 + ζ * P.h c₀ ζ‖ := norm_div _ _
    _ ≤ ‖P.h c₀ ζ - 1 - ζ * P.h c₀ ζ‖ / (1 / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hD_bound
    _ ≤ ((P.A / 4 + ‖P.h1 c₀‖ + 2) * ‖ζ‖) / (1 / 2) :=
        div_le_div_of_nonneg_right hN_bound (by norm_num)
    _ = ((P.A / 2 + 2 * ‖P.h1 c₀‖ + 4) / ‖P.s c₀‖) * ‖z - d.z₁‖ := by
        rw [hζ_eq]; ring

end Work.FlowerGlue2
