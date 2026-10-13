import Mathlib

namespace Work.WilE7.SheetData

/-- If `h` is continuous and nowhere zero on a preconnected set `s`, then the sign of `h` is
constant on `s`: `h x < 0 ↔ h y < 0` for any two points `x, y ∈ s`.

This is the intermediate value theorem for preconnected sets: if `h x < 0 ≤ h y` then the
preconnected image `h '' s` would contain `0`, contradicting nowhere-vanishing. -/
lemma sign_const_of_preconnected {Y : Type*} [TopologicalSpace Y] {s : Set Y} (hs : IsPreconnected s)
    {h : Y → ℝ} (hh : ContinuousOn h s) (hnz : ∀ x ∈ s, h x ≠ 0) {x y : Y} (hx : x ∈ s)
    (hy : y ∈ s) : (h x < 0 ↔ h y < 0) := by
  constructor
  · intro hxlt
    by_contra hcon
    rw [not_lt] at hcon
    have h0 : (0 : ℝ) ∈ h '' s := hs.intermediate_value hx hy hh ⟨le_of_lt hxlt, hcon⟩
    obtain ⟨z, hzs, hz⟩ := h0
    exact hnz z hzs hz
  · intro hylt
    by_contra hcon
    rw [not_lt] at hcon
    have h0 : (0 : ℝ) ∈ h '' s := hs.intermediate_value hy hx hh ⟨le_of_lt hylt, hcon⟩
    obtain ⟨z, hzs, hz⟩ := h0
    exact hnz z hzs hz

/-- On a nonempty preconnected set `C`, two continuous functions `f g` that are *dichotomous*
(they agree at one point of `C` as soon as they agree at another) satisfy a strict (resp. weak)
inequality at one point of `C` only if they satisfy it at every point of `C`: the difference
`f - g` is continuous and nowhere zero on `C`, so its sign is constant on `C`. -/
theorem transfer_lt_le {p : ℕ} {C : Set (Fin p → ℝ)} (hCne : C.Nonempty) (hpre : IsPreconnected C)
    (f g : (Fin p → ℝ) → ℝ) (hf : ContinuousOn f C) (hg : ContinuousOn g C)
    (hdich : (∃ x ∈ C, f x = g x) → ∀ x ∈ C, f x = g x)
    (x₀ y : Fin p → ℝ) (hx₀ : x₀ ∈ C) (hy : y ∈ C) :
    (f x₀ < g x₀ → f y < g y) ∧ (f x₀ ≤ g x₀ → f y ≤ g y) := by
  by_cases hz : ∃ x ∈ C, f x = g x
  · -- the two functions agree everywhere on `C`
    have hall : ∀ x ∈ C, f x = g x := hdich hz
    constructor
    · intro hlt
      exact absurd hlt (not_lt.mpr (le_of_eq (hall x₀ hx₀).symm))
    · intro _
      exact le_of_eq (hall y hy)
  · -- the two functions differ everywhere on `C`; the sign of `f - g` is constant
    push Not at hz
    have hnz : ∀ x ∈ C, f x - g x ≠ 0 := fun x hx => sub_ne_zero.mpr (hz x hx)
    have hcont : ContinuousOn (fun x => f x - g x) C := hf.sub hg
    have hsign : (f x₀ - g x₀ < 0 ↔ f y - g y < 0) :=
      sign_const_of_preconnected hpre hcont hnz hx₀ hy
    constructor
    · intro hlt
      exact sub_neg.mp (hsign.mp (sub_neg.mpr hlt))
    · intro hle
      have hle' : f x₀ - g x₀ ≤ 0 := sub_nonpos.mpr hle
      have hlt' : f x₀ - g x₀ < 0 := lt_of_le_of_ne hle' (hnz x₀ hx₀)
      exact le_of_lt (sub_neg.mp (hsign.mp hlt'))

end Work.WilE7.SheetData
