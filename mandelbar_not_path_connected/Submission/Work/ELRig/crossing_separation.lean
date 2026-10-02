import Mathlib
import Submission.Work.ELRig.crosscut_separation_ball

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

open Set

namespace Work.ELRig

/-- **A crosscut of a disc through its centre separates the two ends of the perpendicular
diameter.**  This is `Work.ELRig.crosscut_separation_ball`, applied to the reparametrised arc
`u ↦ γ (s₁ + u (s₂ - s₁))` (whose image on `[0,1]` is the image of the arc on `[s₁,s₂]`). -/
theorem crossing_separation {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {γ : ℝ → ℂ} {s₁ s₀ s₂ : ℝ}
    (h₁ : s₁ < s₀) (h₂ : s₀ < s₂)
    (hcont : Continuous γ) (hinj : Set.InjOn γ (Set.Icc s₁ s₂))
    (hγ₀ : γ s₀ = p)
    (hint : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₁ → s ≠ s₂ → dist (γ s) p < ρ)
    (hsph₁ : dist (γ s₁) p = ρ) (hsph₂ : dist (γ s₂) p = ρ)
    (hre₁ : (γ s₁).re < p.re) (hre₂ : p.re < (γ s₂).re)
    (hcross : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₀ → 0 < ((γ s).re - p.re) * (s - s₀)) :
    ∀ δ : ℝ, 0 < δ → δ < ρ →
      ¬ JoinedIn (Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂)) (p + δ * Complex.I) (p - δ * Complex.I) := by
  intro δ hδ0 hδρ
  have hΔ : 0 < s₂ - s₁ := by linarith
  have hΔne : (s₂ - s₁) ≠ 0 := ne_of_gt hΔ
  set β : ℝ → ℂ := fun u => γ (s₁ + u * (s₂ - s₁)) with hβ
  set v : ℝ := (s₀ - s₁) / (s₂ - s₁) with hv
  have hβv : β v = p := by
    change γ (s₁ + (s₀ - s₁) / (s₂ - s₁) * (s₂ - s₁)) = p
    have : s₁ + (s₀ - s₁) / (s₂ - s₁) * (s₂ - s₁) = s₀ := by field_simp; ring
    rw [this, hγ₀]
  have hmem : ∀ u ∈ Set.Icc (0:ℝ) 1, s₁ + u * (s₂ - s₁) ∈ Set.Icc s₁ s₂ := by
    intro u hu
    exact ⟨by nlinarith [hu.1, hu.2, hΔ], by nlinarith [hu.1, hu.2, hΔ]⟩
  have hcontβ : ContinuousOn β (Set.Icc (0:ℝ) 1) := by
    rw [hβ]
    exact (hcont.comp (by fun_prop : Continuous fun u : ℝ => s₁ + u * (s₂ - s₁))).continuousOn
  have hinjβ : Set.InjOn β (Set.Icc (0:ℝ) 1) := by
    intro u₁ hu₁ u₂ hu₂ h
    rw [hβ] at h
    have h' : s₁ + u₁ * (s₂ - s₁) = s₁ + u₂ * (s₂ - s₁) :=
      hinj (hmem u₁ hu₁) (hmem u₂ hu₂) h
    have : u₁ * (s₂ - s₁) = u₂ * (s₂ - s₁) := by linarith
    exact mul_right_cancel₀ hΔne this
  have h0β : β 0 ∈ Metric.sphere p ρ := by
    rw [Metric.mem_sphere, hβ]; simpa using hsph₁
  have h1β : β 1 ∈ Metric.sphere p ρ := by
    rw [Metric.mem_sphere, hβ]; simpa using hsph₂
  have hintβ : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ 0 → u ≠ 1 → β u ∈ Metric.ball p ρ := by
    intro u hu hu0 hu1
    rw [Metric.mem_ball, hβ]
    have hne1 : s₁ + u * (s₂ - s₁) ≠ s₁ := by
      intro hc; apply hu0
      have : u * (s₂ - s₁) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hΔne
    have hne2 : s₁ + u * (s₂ - s₁) ≠ s₂ := by
      intro hc; apply hu1
      have : u * (s₂ - s₁) = s₂ - s₁ := by linarith
      nlinarith [hΔ]
    exact hint _ (hmem u hu) hne1 hne2
  have hv0 : 0 < v := by rw [hv]; exact div_pos (by linarith) hΔ
  have hv1 : v < 1 := by rw [hv]; rw [div_lt_one hΔ]; linarith
  have haxβ : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ v → (β u).re ≠ p.re := by
    intro u hu huv
    rw [hβ]
    have hne : s₁ + u * (s₂ - s₁) ≠ s₀ := by
      intro hc
      apply huv
      rw [hv, eq_div_iff hΔne]
      linarith
    have hx := hcross _ (hmem u hu) hne
    intro hcon
    rw [hcon, sub_self, zero_mul] at hx
    exact lt_irrefl 0 hx
  have hsignβ : (∀ u ∈ Set.Ioo (0:ℝ) v, (β u).re < p.re) ∧
      (∀ u ∈ Set.Ioo v 1, p.re < (β u).re) := by
    constructor
    · intro u hu
      rw [hβ]
      have huicc : u ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hu.1, le_of_lt (lt_trans hu.2 hv1)⟩
      have hlt : s₁ + u * (s₂ - s₁) < s₀ := by
        have h2' := hu.2
        rw [hv, lt_div_iff₀ hΔ] at h2'
        linarith
      have hne : s₁ + u * (s₂ - s₁) ≠ s₀ := ne_of_lt hlt
      have hx := hcross _ (hmem u huicc) hne
      have hs : s₁ + u * (s₂ - s₁) - s₀ < 0 := by linarith
      nlinarith [hx, hs]
    · intro u hu
      rw [hβ]
      have huicc : u ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt (lt_trans hv0 hu.1), le_of_lt hu.2⟩
      have hgt : s₀ < s₁ + u * (s₂ - s₁) := by
        have h2' := hu.1
        rw [hv, div_lt_iff₀ hΔ] at h2'
        linarith
      have hne : s₁ + u * (s₂ - s₁) ≠ s₀ := ne_of_gt hgt
      have hx := hcross _ (hmem u huicc) hne
      have hs : 0 < s₁ + u * (s₂ - s₁) - s₀ := by linarith
      nlinarith [hx, hs]
  have hset : β '' Set.Icc (0:ℝ) 1 = γ '' Set.Icc s₁ s₂ := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hmem u hu, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨(s - s₁) / (s₂ - s₁), ?_, ?_⟩
      · constructor
        · exact div_nonneg (by linarith [hs.1]) (le_of_lt hΔ)
        · rw [div_le_one hΔ]; linarith [hs.2]
      · change γ (s₁ + (s - s₁) / (s₂ - s₁) * (s₂ - s₁)) = γ s
        have : s₁ + (s - s₁) / (s₂ - s₁) * (s₂ - s₁) = s := by field_simp; ring
        rw [this]
  have ht0 : 0 < δ / ρ := div_pos hδ0 hρ
  have ht1 : δ / ρ < 1 := (div_lt_one hρ).mpr hδρ
  have key := crosscut_separation_ball hρ hcontβ hinjβ h0β h1β hintβ hv0 hv1 hβv haxβ hsignβ
    (δ / ρ) ht0 ht1
  rw [hset] at key
  have hmulC : ((δ / ρ : ℝ) : ℂ) * (ρ : ℂ) = (δ : ℂ) := by
    rw [← Complex.ofReal_mul]; congr 1; field_simp
  rw [hmulC] at key
  exact key

end Work.ELRig
