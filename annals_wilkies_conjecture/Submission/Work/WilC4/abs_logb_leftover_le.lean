import Mathlib

namespace Work.WilC4

theorem abs_logb_leftover_le {f : ℝ → ℝ} {τ v : ℝ} (hτ : 0 < τ) (hv : τ ≤ v)
    (hv2 : v ≤ 2 * τ) (hpos : ∀ z ∈ Set.Icc τ (2 * τ), 0 < f z)
    (hmono : MonotoneOn f (Set.Icc τ (2 * τ)) ∨ AntitoneOn f (Set.Icc τ (2 * τ))) :
    |Real.logb 2 (f v / f (2 * τ))| ≤ |Real.logb 2 (f (2 * τ) / f τ)| := by
  have hτ2τ : τ ≤ 2 * τ := by linarith
  have hfτ : 0 < f τ := hpos τ ⟨le_refl τ, hτ2τ⟩
  have hfv : 0 < f v := hpos v ⟨hv, hv2⟩
  have hf2τ : 0 < f (2 * τ) := hpos (2 * τ) ⟨hτ2τ, le_refl _⟩
  -- write both logarithms of quotients as differences of logarithms
  rw [Real.logb_div (ne_of_gt hfv) (ne_of_gt hf2τ),
      Real.logb_div (ne_of_gt hf2τ) (ne_of_gt hfτ)]
  set A := Real.logb 2 (f v) with hA
  set B := Real.logb 2 (f (2 * τ)) with hB
  set C := Real.logb 2 (f τ) with hC
  -- logb 2 is increasing, so the ordering of the f-values transfers to A, B, C
  rcases hmono with hm | ha
  · -- monotone: f τ ≤ f v ≤ f (2τ), hence C ≤ A ≤ B
    have h1 : f τ ≤ f v := hm ⟨le_refl τ, hτ2τ⟩ ⟨hv, hv2⟩ hv
    have h2 : f v ≤ f (2 * τ) := hm ⟨hv, hv2⟩ ⟨hτ2τ, le_refl _⟩ hv2
    have hCA : C ≤ A := (Real.logb_le_logb (by norm_num) hfτ hfv).mpr h1
    have hAB : A ≤ B := (Real.logb_le_logb (by norm_num) hfv hf2τ).mpr h2
    rw [abs_of_nonpos (by linarith : A - B ≤ 0), abs_of_nonneg (by linarith : 0 ≤ B - C)]
    linarith
  · -- antitone: f (2τ) ≤ f v ≤ f τ, hence B ≤ A ≤ C
    have h1 : f v ≤ f τ := ha ⟨le_refl τ, hτ2τ⟩ ⟨hv, hv2⟩ hv
    have h2 : f (2 * τ) ≤ f v := ha ⟨hv, hv2⟩ ⟨hτ2τ, le_refl _⟩ hv2
    have hAC : A ≤ C := (Real.logb_le_logb (by norm_num) hfv hfτ).mpr h1
    have hBA : B ≤ A := (Real.logb_le_logb (by norm_num) hf2τ hfv).mpr h2
    rw [abs_of_nonneg (by linarith : 0 ≤ A - B), abs_of_nonpos (by linarith : B - C ≤ 0)]
    linarith

end Work.WilC4
