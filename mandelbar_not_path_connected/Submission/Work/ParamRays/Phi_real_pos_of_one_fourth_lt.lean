import Mathlib
import Submission.Work.ParamRays.RealSlice

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

/-- A continuous real function on the interval `(a, ∞)` which is positive for all sufficiently
large arguments and never vanishes is positive everywhere on the interval.

Reason: `(a, ∞)` is preconnected, hence order-convex (`IsPreconnected.ordConnected`), so a point
of the interval between a non-positive and a positive value of `g` would have to be a zero of
`g`. -/
theorem pos_of_continuousOn_Ioi_of_eventually_pos {a : ℝ} {g : ℝ → ℝ}
    (hc : ContinuousOn g (Set.Ioi a)) (hev : ∀ᶠ x : ℝ in atTop, 0 < g x)
    (hne : ∀ x ∈ Set.Ioi a, g x ≠ 0) {x : ℝ} (hx : x ∈ Set.Ioi a) : 0 < g x := by
  by_contra h
  have hle : g x ≤ 0 := le_of_not_gt h
  have h3 : ∀ᶠ y : ℝ in atTop, 0 < g y ∧ x < y ∧ a < y := by
    filter_upwards [hev, eventually_gt_atTop x, eventually_gt_atTop a] with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp h3
  obtain ⟨hpos, hyx, hya⟩ := hN (max N (max x a + 1)) (le_max_left _ _)
  have hmem : g (max N (max x a + 1)) ∈ g '' Set.Ioi a := Set.mem_image_of_mem g hya
  have hmemx : g x ∈ g '' Set.Ioi a := Set.mem_image_of_mem g hx
  have himg : IsPreconnected (g '' Set.Ioi a) := isPreconnected_Ioi.image g hc
  have h0 : (0 : ℝ) ∈ g '' Set.Ioi a :=
    himg.ordConnected.out hmemx hmem ⟨hle, le_of_lt hpos⟩
  obtain ⟨z, hz, hgz⟩ := h0
  exact hne z hz hgz

/-- For real `x > 1/4` the parameter Böttcher map takes a **positive real** value `> 1`:
this is the forward half of `paramRay 0 = (1/4, ∞)`. -/
theorem Phi_real_pos_of_one_fourth_lt (hN : Work.ParamRays.NakaneInput)
    (hconj : ∀ c : ℂ, Work.ParamRays.Phi ((starRingEnd ℂ) c) =
      (starRingEnd ℂ) (Work.ParamRays.Phi c)) {x : ℝ} (hx : 1 / 4 < x) :
    ∃ r : ℝ, 1 < r ∧ Work.ParamRays.Phi (x : ℂ) = (r : ℂ) := by
  -- `x > 1/4` lies outside the mandelbar, so `Φ (x : ℂ)` is defined and has modulus `> 1`.
  have hxMb : (x : ℂ) ∉ Mb := real_not_mem_Mb_of_one_fourth_lt hx
  have hlt : 1 < ‖Phi (x : ℂ)‖ := one_lt_norm_Phi hN.bottcher hxMb
  -- `Φ` is conjugation-equivariant, so `Φ (x : ℂ)` is real on the real axis.
  have hreal : Phi (x : ℂ) = ((Phi (x : ℂ)).re : ℂ) := Phi_ofReal_eq_re hconj x
  -- `x ↦ (Φ (x : ℂ)).re` is continuous on `(1/4, ∞)`, where `Φ` agrees with Nakane's
  -- homeomorphism.
  have hcont : ContinuousOn (fun y : ℝ => (Phi (y : ℂ)).re) (Set.Ioi (1 / 4 : ℝ)) :=
    Complex.continuous_re.comp_continuousOn
      ((continuousOn_Phi_compl hN).comp Complex.continuous_ofReal.continuousOn
        (fun y hy => real_not_mem_Mb_of_one_fourth_lt hy))
  -- ... and never vanishes there, because its absolute value is `‖Φ‖ > 1`.
  have hne : ∀ y ∈ Set.Ioi (1 / 4 : ℝ), (Phi (y : ℂ)).re ≠ 0 := by
    intro y hy h0
    have h1 : 1 < ‖Phi (y : ℂ)‖ :=
      one_lt_norm_Phi hN.bottcher (real_not_mem_Mb_of_one_fourth_lt hy)
    rw [Phi_ofReal_eq_re hconj y, h0] at h1
    exact absurd h1 (by norm_num)
  -- The sign is therefore constant, and the asymptotic `Φ y / y → 1` makes it positive.
  have hpos : 0 < (Phi (x : ℂ)).re :=
    pos_of_continuousOn_Ioi_of_eventually_pos hcont (eventually_re_Phi_ofReal_pos hN) hne hx
  refine ⟨(Phi (x : ℂ)).re, ?_, hreal⟩
  -- `‖Φ (x : ℂ)‖ = |(Φ (x : ℂ)).re| > 1` together with positivity gives `(Φ (x : ℂ)).re > 1`.
  have h1 : 1 < |(Phi (x : ℂ)).re| := by
    have h2 : ‖Phi (x : ℂ)‖ = |(Phi (x : ℂ)).re| := by rw [hreal]; simp
    rwa [h2] at hlt
  rcases lt_abs.mp h1 with h | h
  · exact h
  · linarith

end Work.ParamRays
