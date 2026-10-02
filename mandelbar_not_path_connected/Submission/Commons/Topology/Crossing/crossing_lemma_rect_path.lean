import Mathlib
import Submission.Commons.Topology.Jordan.crossing_lemma_rect

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Topology.Crossing

open Set Complex

theorem crossing_lemma_rect_path {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (h : Path (a : ℂ) (b : ℂ)) (v : Path ((c : ℂ) * Complex.I) ((d : ℂ) * Complex.I))
    (hh : ∀ t, (h t).re ∈ Set.Icc a b ∧ (h t).im ∈ Set.Icc c d)
    (hv : ∀ t, (v t).re ∈ Set.Icc a b ∧ (v t).im ∈ Set.Icc c d) :
    ∃ s t, h s = v t := by
  -- Clamp `ℝ` onto the unit interval `[0,1]`.
  let ρ : C(ℝ, unitInterval) :=
    ⟨Set.projIcc (0 : ℝ) 1 (by norm_num), continuous_projIcc⟩
  -- Reparametrize both paths to continuous maps on all of `ℝ`.
  let H : C(ℝ, ℂ) := ⟨fun t => h (ρ t), h.continuous.comp ρ.continuous⟩
  let V : C(ℝ, ℂ) := ⟨fun t => v (ρ t), v.continuous.comp ρ.continuous⟩
  have hH : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 →
      (H t).re ∈ Set.Icc a b ∧ (H t).im ∈ Set.Icc c d := by
    intro t _
    exact hh (ρ t)
  have hV : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 →
      (V t).re ∈ Set.Icc a b ∧ (V t).im ∈ Set.Icc c d := by
    intro t _
    exact hv (ρ t)
  have hρm1 : ρ (-1) = (0 : unitInterval) := by
    apply Subtype.ext
    simp [ρ]
  have hρ1 : ρ (1) = (1 : unitInterval) := by
    apply Subtype.ext
    simp [ρ]
  have Hm1 : (H (-1)).re = a := by
    have : H (-1) = (a : ℂ) := by
      show h (ρ (-1)) = (a : ℂ)
      rw [hρm1, h.source]
    rw [this, Complex.ofReal_re]
  have H1 : (H 1).re = b := by
    have : H 1 = (b : ℂ) := by
      show h (ρ 1) = (b : ℂ)
      rw [hρ1, h.target]
    rw [this, Complex.ofReal_re]
  have Vm1 : (V (-1)).im = c := by
    have : V (-1) = (c : ℂ) * Complex.I := by
      show v (ρ (-1)) = (c : ℂ) * Complex.I
      rw [hρm1, v.source]
    rw [this]
    simp
  have V1 : (V 1).im = d := by
    have : V 1 = (d : ℂ) * Complex.I := by
      show v (ρ 1) = (d : ℂ) * Complex.I
      rw [hρ1, v.target]
    rw [this]
    simp
  obtain ⟨s, _hs, t, _ht, hst⟩ :=
    Commons.Topology.Jordan.crossing_lemma_rect H V hH hV Hm1 H1 Vm1 V1
  exact ⟨ρ s, ρ t, hst⟩

end Commons.Topology.Crossing
