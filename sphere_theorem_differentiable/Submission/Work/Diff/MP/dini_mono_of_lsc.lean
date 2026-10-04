import Mathlib
import Submission.Work.Diff.Alg.Pinch.le_of_dini_right

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Dini monotonicity for a lower semicontinuous function whose upper right Dini
derivative is non-positive

Let `u : ℝ → ℝ` and `α ≤ β`.  Suppose

* `u` is lower semicontinuous at every interior point of `(α, β)` (one-sided form, `hlsc`),
  and at `β` from the left (`hlscβ`);
* the upper right Dini derivative of `u` is non-positive in the quantitative form
  `u (t + h) ≤ u t + ε * h` for every `ε > 0` and all small `h > 0` (`hna`).

Then `u β ≤ u α`.

The proof is the classical "first exit" argument.  Fix `ε > 0` and let
`B = {t ∈ [α, β] : u t ≤ u α + ε * (t - α)}`.  Lower semicontinuity makes `B` closed: on the
complement, if `x` is interior (resp. `x = β`) then `hlsc` (resp. `hlscβ`) pushes `u` strictly
above `u α + ε * (· - α)` on a whole neighbourhood of `x`.  The Dini bound `hna` shows that from
every point of `B` strictly below `β` one can advance a little to the right staying in `B`, so
`sSup_mem_of_forall_lt_extend` gives `β ∈ B`, i.e. `u β ≤ u α + ε * (β - α)`.  Letting
`ε ↓ 0` (`le_of_forall_pos_le_add_mul`) yields `u β ≤ u α`.
-/

namespace Work.Diff.MP

open Set

theorem dini_mono_of_lsc {u : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hlsc : ∀ t ∈ Set.Ioo α β, ∀ η > 0, ∃ δ > 0, ∀ y : ℝ, |y - t| < δ → u t - η < u y)
    (hlscβ : ∀ η > 0, ∃ δ > 0, ∀ y : ℝ, β - δ < y → y ≤ β → u β - η < u y)
    (hna : ∀ t ∈ Set.Ico α β, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ β →
      u (t + h) ≤ u t + ε * h) :
    u β ≤ u α := by
  refine Work.Diff.Alg.Pinch.le_of_forall_pos_le_add_mul (sub_nonneg.mpr hαβ) ?_
  intro ε hε
  -- goal : u β ≤ u α + ε * (β - α)
  set g : ℝ → ℝ := fun t => u α + ε * (t - α) with hgdef
  have hgy : ∀ x t : ℝ, g t = g x + ε * (t - x) := by
    intro x t
    simp only [hgdef]
    ring
  set B : Set ℝ := {t | t ∈ Set.Icc α β ∧ u t ≤ g t} with hBdef
  have hBmem : ∀ t, t ∈ B ↔ t ∈ Set.Icc α β ∧ u t ≤ g t := by
    intro t
    simp only [hBdef, Set.mem_ofPred_eq]
  have hBclosed : IsClosed B := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro x hx
    by_cases hxIcc : x ∈ Set.Icc α β
    · have hgx : g x < u x :=
        lt_of_not_ge (fun hle => hx ((hBmem x).mpr ⟨hxIcc, hle⟩))
      set d : ℝ := u x - g x with hd
      have hdpos : 0 < d := by rw [hd]; linarith
      have hδ₂pos : 0 < d / (2 * ε) := div_pos hdpos (by linarith)
      -- the "g" estimate, independent of the position of x
      have hge : ∀ y, |y - x| < d / (2 * ε) → g y < u x - d / 2 := by
        intro y hy
        rw [hgy x y]
        have hkey : ε * (y - x) ≤ ε * |y - x| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (le_of_lt hε)
        have h2ε : (0 : ℝ) < 2 * ε := by linarith
        have hmul : ε * |y - x| < d / 2 := by
          have h := (lt_div_iff₀ h2ε).mp hy
          -- h : |y - x| * (2 * ε) < d
          nlinarith [h]
        rw [hd] at hmul
        linarith [hkey, hmul]
      by_cases hxβ : x = β
      · -- right endpoint
        obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hlscβ (d / 2) (by linarith)
        refine ⟨min δ₁ (d / (2 * ε)), lt_min hδ₁pos hδ₂pos, ?_⟩
        intro y hy hyB
        rw [Metric.mem_ball, Real.dist_eq] at hy
        obtain ⟨hyIcc, hyu⟩ := (hBmem y).mp hyB
        have hlt1 : |y - x| < δ₁ := lt_of_lt_of_le hy (min_le_left _ _)
        have hlt2 : |y - x| < d / (2 * ε) := lt_of_lt_of_le hy (min_le_right _ _)
        have h1 : u β - d / 2 < u y := by
          apply hδ₁ y _ hyIcc.2
          have hlt := (abs_lt.mp hlt1).1
          rw [hxβ] at hlt
          linarith
        have h2 : g y < u β - d / 2 := by
          have := hge y hlt2
          rwa [hxβ] at this
        exact absurd hyu (not_le.mpr (lt_trans h2 h1))
      · -- interior point
        have hxβ' : x < β := lt_of_le_of_ne hxIcc.2 hxβ
        have hxα : α < x := by
          rcases lt_or_eq_of_le hxIcc.1 with h | h
          · exact h
          · exfalso
            have hgxα : g x = u x := by
              rw [← h]
              simp only [hgdef]
              ring
            linarith [hgx, hgxα]
        obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hlsc x ⟨hxα, hxβ'⟩ (d / 2) (by linarith)
        refine ⟨min δ₁ (d / (2 * ε)), lt_min hδ₁pos hδ₂pos, ?_⟩
        intro y hy hyB
        rw [Metric.mem_ball, Real.dist_eq] at hy
        obtain ⟨hyIcc, hyu⟩ := (hBmem y).mp hyB
        have hlt1 : |y - x| < δ₁ := lt_of_lt_of_le hy (min_le_left _ _)
        have hlt2 : |y - x| < d / (2 * ε) := lt_of_lt_of_le hy (min_le_right _ _)
        have h1 : u x - d / 2 < u y := hδ₁ y hlt1
        have h2 : g y < u x - d / 2 := hge y hlt2
        exact absurd hyu (not_le.mpr (lt_trans h2 h1))
    · -- outside [α, β]
      have hx' : x < α ∨ β < x := by
        rw [Set.mem_Icc] at hxIcc
        by_cases h : x < α
        · exact Or.inl h
        · refine Or.inr ?_
          by_contra hle
          exact hxIcc ⟨le_of_not_gt h, le_of_not_gt hle⟩
      rcases hx' with hxα | hxβ
      · refine ⟨α - x, by linarith, ?_⟩
        intro y hy hyB
        rw [Metric.mem_ball, Real.dist_eq] at hy
        obtain ⟨hyIcc, -⟩ := (hBmem y).mp hyB
        have : y < α := by
          have := (abs_lt.mp hy).2
          linarith
        exact absurd hyIcc.1 (not_le.mpr this)
      · refine ⟨x - β, by linarith, ?_⟩
        intro y hy hyB
        rw [Metric.mem_ball, Real.dist_eq] at hy
        obtain ⟨hyIcc, -⟩ := (hBmem y).mp hyB
        have : β < y := by
          have := (abs_lt.mp hy).1
          linarith
        exact absurd hyIcc.2 (not_le.mpr this)
  have hαB : α ∈ B := (hBmem α).mpr ⟨⟨le_rfl, hαβ⟩, by simp only [hgdef]; linarith⟩
  have hBne : B.Nonempty := ⟨α, hαB⟩
  have hBbd : ∀ t ∈ B, t ≤ β := fun t ht => ((hBmem t).mp ht).1.2
  have hext : ∀ t ∈ B, t < β → ∃ η > 0, Set.Icc t (t + η) ⊆ B := by
    intro t ht htβ
    obtain ⟨htIcc, htu⟩ := (hBmem t).mp ht
    obtain ⟨δ, hδpos, hδ⟩ := hna t ⟨htIcc.1, htβ⟩ ε hε
    refine ⟨min δ (β - t) / 2, ?_, ?_⟩
    · have := lt_min hδpos (sub_pos.mpr htβ)
      linarith
    · intro s hs
      rw [hBmem]
      have hs1 : t ≤ s := hs.1
      have hs2 : s ≤ t + min δ (β - t) / 2 := hs.2
      have hδle : s - t ≤ δ := by
        have := min_le_left δ (β - t); linarith
      have hst : s ≤ β := by
        have := min_le_right δ (β - t); linarith
      rcases eq_or_lt_of_le hs1 with heq | hlt
      · rw [← heq]; exact ⟨htIcc, htu⟩
      · have hspos : 0 < s - t := sub_pos.mpr hlt
        have h := hδ (s - t) hspos hδle (by linarith : t + (s - t) ≤ β)
        rw [add_sub_cancel] at h
        refine ⟨⟨le_trans htIcc.1 hs1, hst⟩, ?_⟩
        calc u s ≤ u t + ε * (s - t) := h
          _ ≤ g t + ε * (s - t) := by linarith [htu]
          _ = g s := (hgy t s).symm
  have hβB : β ∈ B :=
    Work.Diff.Alg.Pinch.sSup_mem_of_forall_lt_extend hBclosed hBne hBbd hext
  exact ((hBmem β).mp hβB).2

end Work.Diff.MP
