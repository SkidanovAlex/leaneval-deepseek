import Mathlib
import Submission.Work.ELRig.crossing_separation
import Submission.Work.ELRig.cover_of_crosscut

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

open Set Metric

namespace Work.ELRig

/-- **Elementary intermediate value.**  A continuous real function that is negative at the left
end of an interval and positive at the right end vanishes somewhere in its interior. -/
private lemma exists_zero_of_neg_pos {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b)) (ha : f a < 0) (hb : 0 < f b) :
    ∃ c ∈ Set.Ioo a b, f c = 0 := by
  have hpc : IsPreconnected (f '' Set.Icc a b) := IsPreconnected.image isPreconnected_Icc f hcont
  have h0mem : (0 : ℝ) ∈ f '' Set.Icc a b :=
    hpc.Icc_subset ⟨a, ⟨le_refl a, hab.le⟩, rfl⟩ ⟨b, ⟨hab.le, le_refl b⟩, rfl⟩
      (Set.mem_Icc.mpr ⟨le_of_lt ha, le_of_lt hb⟩)
  obtain ⟨c, hc, hc0⟩ := h0mem
  refine ⟨c, ⟨?_, ?_⟩, hc0⟩
  · rcases eq_or_lt_of_le hc.1 with h | h
    · rw [← h] at hc0; linarith
    · exact h
  · rcases eq_or_lt_of_le hc.2 with h | h
    · rw [h] at hc0; linarith
    · exact h

/-- **Sign structure of a continuous function which vanishes at exactly one point.**  If `g` is
continuous on `[s₁,s₂]`, vanishes at `s₀` (with `s₁ < s₀ < s₂`) and nowhere else in the interval,
and is negative at `s₁` and positive at `s₂`, then `g (s) * (s - s₀) > 0` for every `s ≠ s₀` in the
interval (i.e. `g` crosses the axis at `s₀` in the "positive" direction). -/
private lemma sign_crossing {g : ℝ → ℝ} {s₁ s₀ s₂ : ℝ} (h₁ : s₁ < s₀) (h₂ : s₀ < s₂)
    (hcont : ContinuousOn g (Set.Icc s₁ s₂)) (hzero₀ : g s₀ = 0)
    (hne : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₀ → g s ≠ 0)
    (hg₁ : g s₁ < 0) (hg₂ : 0 < g s₂) :
    ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₀ → 0 < g s * (s - s₀) := by
  have hleft : ∀ s ∈ Set.Icc s₁ s₂, s < s₀ → g s < 0 := by
    intro s hs hslt
    have hsne : g s ≠ 0 := hne s hs (ne_of_lt hslt)
    rcases lt_trichotomy (g s) 0 with h | h | h
    · exact h
    · exact absurd h hsne
    · exfalso
      rcases eq_or_lt_of_le hs.1 with hseq | hslt'
      · rw [← hseq] at h; linarith
      · have hcont' : ContinuousOn g (Set.Icc s₁ s) :=
          hcont.mono (fun x hx => ⟨hx.1, hx.2.trans hs.2⟩)
        obtain ⟨c, hc, hc0⟩ := exists_zero_of_neg_pos hslt' hcont' hg₁ h
        exact hne c ⟨hc.1.le, hc.2.le.trans hs.2⟩ (ne_of_lt (hc.2.trans hslt)) hc0
  have hright : ∀ s ∈ Set.Icc s₁ s₂, s₀ < s → 0 < g s := by
    intro s hs hsgt
    have hsne : g s ≠ 0 := hne s hs (ne_of_gt hsgt)
    rcases lt_trichotomy (g s) 0 with h | h | h
    · exfalso
      rcases eq_or_lt_of_le hs.2 with hseq | hslt'
      · rw [hseq] at h; linarith
      · have hcont' : ContinuousOn g (Set.Icc s s₂) :=
          hcont.mono (fun x hx => ⟨h₁.le.trans (hsgt.le.trans hx.1), hx.2⟩)
        obtain ⟨c, hc, hc0⟩ := exists_zero_of_neg_pos hslt' hcont' h hg₂
        exact hne c ⟨h₁.le.trans (le_of_lt (hsgt.trans hc.1)), hc.2.le⟩
          (ne_of_gt (hsgt.trans hc.1)) hc0
    · exact absurd h hsne
    · exact h
  intro s hs hsne
  rcases lt_or_gt_of_ne hsne with hlt | hgt
  · exact mul_pos_of_neg_of_neg (hleft s hs hlt) (by linarith)
  · exact mul_pos (hright s hs hgt) (by linarith)

/-- **Case `hside = (γ s₁).re < p.re < (γ s₂).re` of `crosscut_pair_separation`.**

Combining the sign structure with the two crosscut results, we get both the non-joining of the two
ends of the perpendicular diameter and the covering of the punctured disc minus the arc. -/
private lemma pair_separation_of_hre {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {γ : ℝ → ℂ} {s₁ s₀ s₂ : ℝ}
    (h₁ : s₁ < s₀) (h₂ : s₀ < s₂)
    (hcont : Continuous γ) (hinj : Set.InjOn γ (Set.Icc s₁ s₂))
    (hγ₀ : γ s₀ = p)
    (hint : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₁ → s ≠ s₂ → dist (γ s) p < ρ)
    (hsph₁ : dist (γ s₁) p = ρ) (hsph₂ : dist (γ s₂) p = ρ)
    (hax : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₀ → (γ s).re ≠ p.re)
    (hre₁ : (γ s₁).re < p.re) (hre₂ : p.re < (γ s₂).re) :
    (¬ JoinedIn (Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂)) (p + (ρ / 2) * Complex.I)
      (p - (ρ / 2) * Complex.I)) ∧
    (∀ w ∈ Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂),
      JoinedIn (Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂)) w (p + (ρ / 2) * Complex.I) ∨
      JoinedIn (Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂)) w (p - (ρ / 2) * Complex.I)) := by
  have hcontg : ContinuousOn (fun s : ℝ => (γ s).re - p.re) (Set.Icc s₁ s₂) :=
    ((Complex.continuous_re.comp hcont).sub continuous_const).continuousOn
  have hzero₀ : (fun s : ℝ => (γ s).re - p.re) s₀ = 0 := by
    simp [hγ₀]
  have hne' : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₀ → (fun s : ℝ => (γ s).re - p.re) s ≠ 0 := by
    intro s hs hsne
    simpa [sub_eq_zero] using hax s hs hsne
  have hg₁ : (fun s : ℝ => (γ s).re - p.re) s₁ < 0 := by
    simp only; linarith
  have hg₂ : 0 < (fun s : ℝ => (γ s).re - p.re) s₂ := by
    simp only; linarith
  have hcross := sign_crossing h₁ h₂ hcontg hzero₀ hne' hg₁ hg₂
  refine ⟨?_, ?_⟩
  · have h := crossing_separation hρ h₁ h₂ hcont hinj hγ₀ hint hsph₁ hsph₂ hre₁ hre₂ hcross
        (ρ / 2) (by linarith) (by linarith)
    have hbridge : ((ρ / 2 : ℝ) : ℂ) = (ρ : ℂ) / 2 := by push_cast; ring
    simpa only [hbridge] using h
  · exact cover_of_crosscut hρ h₁ h₂ hcont hinj hγ₀ hint hsph₁ hsph₂ hre₁ hre₂ hcross

theorem crosscut_pair_separation {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {γ : ℝ → ℂ} {s₁ s₀ s₂ : ℝ}
    (h₁ : s₁ < s₀) (h₂ : s₀ < s₂)
    (hcont : Continuous γ) (hinj : Set.InjOn γ (Set.Icc s₁ s₂))
    (hγ₀ : γ s₀ = p)
    (hint : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₁ → s ≠ s₂ → dist (γ s) p < ρ)
    (hsph₁ : dist (γ s₁) p = ρ) (hsph₂ : dist (γ s₂) p = ρ)
    (hax : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₀ → (γ s).re ≠ p.re)
    (hside : ((γ s₁).re < p.re ∧ p.re < (γ s₂).re) ∨ (p.re < (γ s₁).re ∧ (γ s₂).re < p.re)) :
    (¬ JoinedIn (Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂)) (p + (ρ / 2) * Complex.I)
      (p - (ρ / 2) * Complex.I)) ∧
    (∀ w ∈ Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂),
      JoinedIn (Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂)) w (p + (ρ / 2) * Complex.I) ∨
      JoinedIn (Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂)) w (p - (ρ / 2) * Complex.I)) := by
  rcases hside with ⟨hre₁, hre₂⟩ | ⟨hre₁, hre₂⟩
  · exact pair_separation_of_hre hρ h₁ h₂ hcont hinj hγ₀ hint hsph₁ hsph₂ hax hre₁ hre₂
  · -- the arc runs from the right half to the left half; reverse the parametrisation
    have ht₁ : -s₂ < -s₀ := by linarith
    have ht₂ : -s₀ < -s₁ := by linarith
    have hcontδ : Continuous (fun u : ℝ => γ (-u)) := hcont.comp (by fun_prop)
    have hinjδ : Set.InjOn (fun u : ℝ => γ (-u)) (Set.Icc (-s₂) (-s₁)) := by
      intro u hu v hv huv
      have hu' : -u ∈ Set.Icc s₁ s₂ := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      have hv' : -v ∈ Set.Icc s₁ s₂ := ⟨by linarith [hv.2], by linarith [hv.1]⟩
      have h := hinj hu' hv' huv
      linarith
    have hγ₀δ : (fun u : ℝ => γ (-u)) (-s₀) = p := by simpa using hγ₀
    have hintδ : ∀ u ∈ Set.Icc (-s₂) (-s₁), u ≠ -s₂ → u ≠ -s₁ →
        dist ((fun u : ℝ => γ (-u)) u) p < ρ := by
      intro u hu hu₁ hu₂
      have hu' : -u ∈ Set.Icc s₁ s₂ := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      have hne₁ : -u ≠ s₁ := fun h => hu₂ (by linarith)
      have hne₂ : -u ≠ s₂ := fun h => hu₁ (by linarith)
      exact hint (-u) hu' hne₁ hne₂
    have hsphδ₁ : dist ((fun u : ℝ => γ (-u)) (-s₂)) p = ρ := by simpa using hsph₂
    have hsphδ₂ : dist ((fun u : ℝ => γ (-u)) (-s₁)) p = ρ := by simpa using hsph₁
    have haxδ : ∀ u ∈ Set.Icc (-s₂) (-s₁), u ≠ -s₀ →
        ((fun u : ℝ => γ (-u)) u).re ≠ p.re := by
      intro u hu hu₀
      have hu' : -u ∈ Set.Icc s₁ s₂ := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      have hne : -u ≠ s₀ := fun h => hu₀ (by linarith)
      exact hax (-u) hu' hne
    have hreδ₁ : ((fun u : ℝ => γ (-u)) (-s₂)).re < p.re := by simpa using hre₂
    have hreδ₂ : p.re < ((fun u : ℝ => γ (-u)) (-s₁)).re := by simpa using hre₁
    have hkey := pair_separation_of_hre hρ ht₁ ht₂ hcontδ hinjδ hγ₀δ hintδ hsphδ₁ hsphδ₂
      haxδ hreδ₁ hreδ₂
    have hδarc : (fun u : ℝ => γ (-u)) '' Set.Icc (-s₂) (-s₁) = γ '' Set.Icc s₁ s₂ := by
      ext z; constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨-u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by simp⟩
    rw [hδarc] at hkey
    exact hkey

end Work.ELRig
