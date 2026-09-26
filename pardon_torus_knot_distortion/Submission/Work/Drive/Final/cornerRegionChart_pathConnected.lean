import Mathlib

namespace Work.Drive.Final

open Set

/-- For a chart `W` that is monotone in the second variable, the `y`-fibre
`{y | y ∈ (-δ, δ) ∧ (0 < y ∨ 0 < W (x, y))}` is convex in `ℝ`:
it is the intersection of `(-δ, δ)` with an upward-closed subset of `ℝ`, hence
an interval. -/
private lemma convex_fibre (W : ℝ × ℝ → ℝ) {ε δ : ℝ}
    (hmono : ∀ x y y' : ℝ, x ∈ Set.Ioo (-ε) ε → y ∈ Set.Ioo (-δ) δ → y' ∈ Set.Ioo y δ →
      0 < W (x, y) → 0 < W (x, y'))
    {x : ℝ} (hx : x ∈ Set.Ioo (-ε) ε) :
    Convex ℝ {y : ℝ | y ∈ Set.Ioo (-δ) δ ∧ (0 < y ∨ 0 < W (x, y))} := by
  refine convex_iff_ordConnected.2 (Set.OrdConnected.mk ?_)
  intro y₁ hy₁ y₂ hy₂ c hc
  obtain ⟨hy₁δ, hy₁c⟩ := hy₁
  obtain ⟨hy₂δ, _⟩ := hy₂
  obtain ⟨hc₁, hc₂⟩ := hc
  refine ⟨⟨lt_of_lt_of_le hy₁δ.1 hc₁, lt_of_le_of_lt hc₂ hy₂δ.2⟩, ?_⟩
  rcases hy₁c with h | h
  · exact Or.inl (lt_of_lt_of_le h hc₁)
  · rcases eq_or_lt_of_le hc₁ with heq | hlt
    · exact Or.inr (heq ▸ h)
    · exact Or.inr (hmono x y₁ c hx hy₁δ ⟨hlt, lt_of_le_of_lt hc₂ hy₂δ.2⟩ h)

/-- The segment between two points of a convex subset of `ℝ`, in the
`(1 - t) a + t b` parametrisation. -/
private lemma segment_mem {A : Set ℝ} (hA : Convex ℝ A) {a b t : ℝ}
    (ha : a ∈ A) (hb : b ∈ A) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * a + t * b ∈ A := by
  have h : (1 - t) • a + t • b ∈ A :=
    (hA ha) hb (show (0:ℝ) ≤ 1 - t by linarith) ht0 (show (1 - t) + t = 1 by ring)
  simpa [smul_eq_mul] using h

theorem cornerRegionChart_pathConnected (W : ℝ × ℝ → ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hmono : ∀ x y y' : ℝ, x ∈ Set.Ioo (-ε) ε → y ∈ Set.Ioo (-δ) δ → y' ∈ Set.Ioo y δ →
      0 < W (x, y) → 0 < W (x, y')) :
    IsPathConnected {ξ : ℝ × ℝ | ξ ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ ∧ ξ.1 < 0 ∧
      (0 < ξ.2 ∨ 0 < W ξ)} := by
  -- The region is star-shaped over the horizontal segment at height `δ / 2`:
  -- every point is joined to the base point `(-ε/2, δ/2)` by a vertical segment
  -- followed by a horizontal one.  Vertically the fibre is convex by monotonicity
  -- of `W` in the second variable, horizontally the condition `0 < ξ.2` holds.
  set s : Set (ℝ × ℝ) := {ξ : ℝ × ℝ | ξ ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ ∧ ξ.1 < 0 ∧
      (0 < ξ.2 ∨ 0 < W ξ)} with hs
  have hε2 : (-ε / 2 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, by linarith⟩
  have hε2neg : (-ε / 2 : ℝ) ∈ Set.Iio (0:ℝ) := by simp only [Set.mem_Iio]; linarith
  have hbmem : ((-ε / 2 : ℝ), δ / 2) ∈ s := by
    rw [hs]
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, by linarith,
      Or.inl (by linarith)⟩
  have key : ∀ ξ ∈ s, JoinedIn s ξ ((-ε / 2 : ℝ), δ / 2) := by
    intro ξ hξ
    rw [hs] at hξ
    obtain ⟨hξbox, hξneg, hξcond⟩ := hξ
    have hξx : ξ.1 ∈ Set.Ioo (-ε) ε := hξbox.1
    have hξy : ξ.2 ∈ Set.Ioo (-δ) δ := hξbox.2
    have hconv : Convex ℝ {y : ℝ | y ∈ Set.Ioo (-δ) δ ∧ (0 < y ∨ 0 < W (ξ.1, y))} :=
      convex_fibre W hmono hξx
    have hyδ : δ / 2 ∈ {y : ℝ | y ∈ Set.Ioo (-δ) δ ∧ (0 < y ∨ 0 < W (ξ.1, y))} :=
      ⟨⟨by linarith, by linarith⟩, Or.inl (by linarith)⟩
    have hξA : ξ.2 ∈ {y : ℝ | y ∈ Set.Ioo (-δ) δ ∧ (0 < y ∨ 0 < W (ξ.1, y))} :=
      ⟨hξy, hξcond⟩
    -- vertical segment, keeping `ξ.1` fixed, from `ξ.2` up to `δ / 2`
    have hvert : JoinedIn s ξ (ξ.1, δ / 2) := by
      have hcont : ContinuousOn (fun t : ℝ => (ξ.1, (1 - t) * ξ.2 + t * (δ / 2))) unitInterval := by
        fun_prop
      have hf0 : (fun t : ℝ => (ξ.1, (1 - t) * ξ.2 + t * (δ / 2))) 0 = ξ := by simp
      have hf1 : (fun t : ℝ => (ξ.1, (1 - t) * ξ.2 + t * (δ / 2))) 1 = (ξ.1, δ / 2) := by simp
      refine ⟨Path.ofLine hcont hf0 hf1, ?_⟩
      have himg : (fun t : ℝ => (ξ.1, (1 - t) * ξ.2 + t * (δ / 2))) '' unitInterval ⊆ s := by
        rintro _ ⟨t, ht, rfl⟩
        simp only [hs, Set.mem_ofPred_eq, Set.mem_prod]
        exact ⟨⟨hξx, (segment_mem hconv hξA hyδ ht.1 ht.2).1⟩, hξneg,
          (segment_mem hconv hξA hyδ ht.1 ht.2).2⟩
      intro t
      exact himg (Path.ofLine_mem hcont hf0 hf1 t)
    -- horizontal segment at height `δ / 2`, from `ξ.1` to `-ε / 2`
    have hhoriz : JoinedIn s (ξ.1, δ / 2) ((-ε / 2 : ℝ), δ / 2) := by
      have hcont : ContinuousOn (fun t : ℝ => ((1 - t) * ξ.1 + t * (-ε / 2), δ / 2)) unitInterval := by
        fun_prop
      have hg0 : (fun t : ℝ => ((1 - t) * ξ.1 + t * (-ε / 2), δ / 2)) 0 = (ξ.1, δ / 2) := by simp
      have hg1 : (fun t : ℝ => ((1 - t) * ξ.1 + t * (-ε / 2), δ / 2)) 1 = ((-ε / 2 : ℝ), δ / 2) := by
        ext <;> ring
      refine ⟨Path.ofLine hcont hg0 hg1, ?_⟩
      have himg : (fun t : ℝ => ((1 - t) * ξ.1 + t * (-ε / 2), δ / 2)) '' unitInterval ⊆ s := by
        rintro _ ⟨t, ht, rfl⟩
        simp only [hs, Set.mem_ofPred_eq, Set.mem_prod]
        have hx1 : (1 - t) * ξ.1 + t * (-ε / 2) ∈ Set.Ioo (-ε) ε :=
          segment_mem (convex_Ioo (-ε) ε) hξx hε2 ht.1 ht.2
        have hx2 : (1 - t) * ξ.1 + t * (-ε / 2) ∈ Set.Iio (0:ℝ) :=
          segment_mem (convex_Iio (0:ℝ)) hξneg hε2neg ht.1 ht.2
        have hy2 : δ / 2 ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
        have hypos : (0:ℝ) < δ / 2 := by linarith
        exact ⟨⟨hx1, hy2⟩, hx2, Or.inl hypos⟩
      intro t
      exact himg (Path.ofLine_mem hcont hg0 hg1 t)
    exact hvert.trans hhoriz
  exact ⟨((-ε / 2 : ℝ), δ / 2), hbmem, fun y hy => (key y hy).symm⟩

end Work.Drive.Final
