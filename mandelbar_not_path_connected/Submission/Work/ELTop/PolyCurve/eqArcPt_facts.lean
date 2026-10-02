import Mathlib
import Submission.Work.ELTop.PolyCurve.Defs
import Submission.Work.ELTop.rayPt_inj
import Submission.Work.ELTop.continuous_rayPt_angle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop.PolyCurve

/-! ## Elementary facts about reals differing by an integer -/

/-- A real number which differs from `x` by an integer and by less than `1` in absolute value
equals `x`. -/
theorem eq_of_eq_add_int_of_abs_sub_lt_one {x y : ℝ}
    (h : ∃ k : ℤ, y = x + (k : ℝ)) (hlt : |y - x| < 1) : y = x := by
  obtain ⟨k, hk⟩ := h
  have h1 : (k : ℝ) = y - x := by linarith
  obtain ⟨h2, h3⟩ := abs_lt.mp hlt
  have h4 : (k : ℝ) < 1 := by linarith
  have h5 : (-1 : ℝ) < (k : ℝ) := by linarith
  have h6 : k < 1 := by exact_mod_cast h4
  have h7 : (-1 : ℤ) < k := by exact_mod_cast h5
  have h8 : k = 0 := by omega
  rw [h8] at h1
  simp at h1
  linarith

/-! ## The continuity of `eqArcPt` in the parameter -/

theorem continuous_eqArcPt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {R : ℝ} (hR : 1 < R)
    (β₁ β₂ : ℝ) : Continuous (Work.ELTop.eqArcPt hN β₁ β₂ R) := by
  have h : Continuous fun u : ℝ => Work.EL.rayPt hN (β₁ + u * (β₂ - β₁)) R :=
    (Work.ELTop.continuous_rayPt_angle hN hR).comp (by fun_prop)
  exact h

/-! ## Injectivity of `eqArcPt` on the unit interval -/

theorem injOn_eqArcPt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {R : ℝ} (hR : 1 < R)
    {β₁ β₂ : ℝ} (h21 : β₂ < β₁) (hsub : β₁ - β₂ < 1) :
    Set.InjOn (Work.ELTop.eqArcPt hN β₁ β₂ R) (Set.Icc 0 1) := by
  intro u hu v hv huv
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  have hdiff : ∃ k : ℤ, β₁ + v * (β₂ - β₁) = β₁ + u * (β₂ - β₁) + (k : ℝ) :=
    Work.ELTop.rayPt_inj hN hR huv
  have huv_abs : |v - u| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hlt : |(β₁ + v * (β₂ - β₁)) - (β₁ + u * (β₂ - β₁))| < 1 := by
    have hd : β₂ - β₁ < 0 := by linarith
    have h1 : (β₁ + v * (β₂ - β₁)) - (β₁ + u * (β₂ - β₁)) = (v - u) * (β₂ - β₁) := by ring
    rw [h1, abs_mul, abs_of_neg hd]
    nlinarith [abs_nonneg (v - u)]
  have heq := eq_of_eq_add_int_of_abs_sub_lt_one hdiff hlt
  have hzero : (v - u) * (β₂ - β₁) = 0 := by
    have h0 : (β₁ + v * (β₂ - β₁)) - (β₁ + u * (β₂ - β₁)) = 0 := by linarith
    linarith
  have hne : β₂ - β₁ ≠ 0 := by linarith
  have hvu : v - u = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hne
  linarith

/-! ## The image of `eqArcPt` on the unit interval -/

theorem image_eqArcPt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {R β₁ β₂ : ℝ}
    (h : β₂ ≤ β₁) :
    Work.ELTop.eqArcPt hN β₁ β₂ R '' Set.Icc 0 1 = Work.EL.eqArc hN β₂ β₁ R := by
  ext z
  simp only [Set.mem_image, Set.mem_Icc, Work.EL.eqArc, Work.Top.NakaneData.eqArc,
    Set.mem_range, Work.ELTop.eqArcPt]
  constructor
  · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
    exact ⟨⟨β₁ + u * (β₂ - β₁), ⟨by nlinarith, by nlinarith⟩⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    rcases eq_or_lt_of_le h with heq | hlt
    · refine ⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩
      have hs : s.1 = β₁ := le_antisymm s.2.2 (heq ▸ s.2.1)
      have harg : β₁ + 0 * (β₂ - β₁) = β₁ := by ring
      rw [harg, hs]
    · have hd : 0 < β₁ - β₂ := by linarith
      refine ⟨(β₁ - s.1) / (β₁ - β₂), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg (by linarith [s.2.2]) (le_of_lt hd)
      · rw [div_le_one hd]
        linarith [s.2.1]
      · have harg : β₁ + (β₁ - s.1) / (β₁ - β₂) * (β₂ - β₁) = s.1 := by
          field_simp
          ring
        rw [harg]

/-! ## The target theorem -/

theorem eqArcPt_facts {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {R : ℝ} (hR : 1 < R) (β₁ β₂ : ℝ) :
    Continuous (Work.ELTop.eqArcPt hN β₁ β₂ R) ∧
    (β₂ < β₁ → β₁ - β₂ < 1 → Set.InjOn (Work.ELTop.eqArcPt hN β₁ β₂ R) (Set.Icc 0 1)) ∧
    (β₂ ≤ β₁ → Work.ELTop.eqArcPt hN β₁ β₂ R '' Set.Icc 0 1 =
      Work.EL.eqArc hN β₂ β₁ R) :=
  ⟨continuous_eqArcPt hN hR β₁ β₂,
   fun h21 hsub => injOn_eqArcPt hN hR h21 hsub,
   fun h => image_eqArcPt hN h⟩

end Work.ELTop.PolyCurve
