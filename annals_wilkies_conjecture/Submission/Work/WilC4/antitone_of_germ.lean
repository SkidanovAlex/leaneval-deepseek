import Mathlib

namespace Work.WilC4

/-- A function on an interval `(a, b)` which is strictly decreasing "through every
point" (both a strict right-descent and a strict left-ascent hold in a
neighbourhood of each point) is strictly decreasing on `(a, b)`; in particular it
is antitone. -/
theorem antitone_of_germ {f : ℝ → ℝ} {a b : ℝ}
    (hL : ∀ x, a < x → x < b → ∃ ε, 0 < ε ∧ ∀ z, x - ε < z → z < x → f x < f z)
    (hR : ∀ x, a < x → x < b → ∃ ε, 0 < ε ∧ ∀ z, x < z → z < x + ε → f z < f x) :
    ∀ x₁ x₂, a < x₁ → x₁ < x₂ → x₂ < b → f x₂ ≤ f x₁ := by
  -- First prove the strict version.
  have key : ∀ x₁ x₂, a < x₁ → x₁ < x₂ → x₂ < b → f x₂ < f x₁ := by
    intro x₁ x₂ hx1 hx12 hx2
    -- Local strict decrease through `x₁`.
    obtain ⟨eL, heLpos, hL1⟩ := hL x₁ hx1 (lt_trans hx12 hx2)
    obtain ⟨eR, heRpos, hR1⟩ := hR x₁ hx1 (lt_trans hx12 hx2)
    let η := min eL eR
    have hηpos : 0 < η := lt_min heLpos heRpos
    have hright : ∀ t, x₁ < t → t < x₁ + η → f t < f x₁ := by
      intro t ht1 ht2
      apply hR1 t ht1
      have : η ≤ eR := min_le_right eL eR
      linarith
    by_contra hc
    push Not at hc
    -- `D` is the (nonempty, bounded below) set of points above `x₁` up to `x₂`
    -- where `f` has already returned to at least `f x₁`.
    let D : Set ℝ := {t | x₁ < t ∧ t ≤ x₂ ∧ f x₁ ≤ f t}
    have hx2D : x₂ ∈ D := ⟨hx12, le_refl x₂, hc⟩
    have hDne : D.Nonempty := ⟨x₂, hx2D⟩
    have hDbdd : BddBelow D := ⟨x₁, by rintro t ⟨ht1, _, _⟩; exact le_of_lt ht1⟩
    let c := sInf D
    have hcle : c ≤ x₂ := csInf_le hDbdd hx2D
    -- `c` lies strictly above `x₁`, because near `x₁` from the right `f < f x₁`.
    have hge : x₁ + η ≤ c := by
      apply le_csInf hDne
      rintro t ⟨ht1, _, hft⟩
      by_contra hlt
      push Not at hlt
      have : f t < f x₁ := hright t ht1 hlt
      linarith
    have hcgt : x₁ < c := by linarith
    have hcltb : c < b := lt_of_le_of_lt hcle hx2
    obtain ⟨ec, hecpos, hLc⟩ := hL c (by linarith) hcltb
    obtain ⟨dc, hdcpos, hRc⟩ := hR c (by linarith) hcltb
    -- Since `c` is the infimum of `D`, points of `D` approach it from above.
    have hex : ∃ t ∈ D, t < c + dc := by
      by_contra hh
      push Not at hh
      have hle : c + dc ≤ c := by
        apply le_csInf hDne
        intro t ht
        exact hh t ht
      linarith
    by_cases hfcc : f c < f x₁
    · -- Then `c ∉ D`, so `c < t`, and the right-descent through `c` contradicts
      -- `t ∈ D`.
      have hcnD : c ∉ D := by
        intro hcD
        linarith [hcD.2.2, hfcc]
      obtain ⟨t, htD, htlt⟩ := hex
      have hft : f x₁ ≤ f t := htD.2.2
      have hct_le : c ≤ t := csInf_le hDbdd htD
      have hct_lt : c < t := lt_of_le_of_ne hct_le (by intro h; exact hcnD (h.symm ▸ htD))
      have : f t < f c := hRc t hct_lt htlt
      linarith
    · -- Otherwise `c ∈ D`, and the left-ascent through `c` produces a point of `D`
      -- strictly below the infimum `c`.
      push Not at hfcc
      have hcD : c ∈ D := ⟨hcgt, hcle, hfcc⟩
      have hmaxlt : max (c - ec) x₁ < c := max_lt (by linarith) hcgt
      let v := (max (c - ec) x₁ + c) / 2
      have hv1 : max (c - ec) x₁ < v := by simp only [v]; linarith
      have hv2 : v < c := by simp only [v]; linarith
      have hvc : c - ec < v := lt_of_le_of_lt (le_max_left _ _) hv1
      have hvx₁ : x₁ < v := lt_of_le_of_lt (le_max_right _ _) hv1
      have hfvc : f c < f v := hLc v hvc hv2
      have hvD : v ∈ D := ⟨hvx₁, by linarith, by linarith⟩
      have : c ≤ v := csInf_le hDbdd hvD
      linarith
  intro x₁ x₂ h1 h2 h3
  exact le_of_lt (key x₁ x₂ h1 h2 h3)

end Work.WilC4
