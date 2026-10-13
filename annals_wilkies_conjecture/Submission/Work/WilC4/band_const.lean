import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.mid_band_unique
import Submission.Work.WilC4.side_of_avoid

set_option autoImplicit false

namespace Work.WilC4

/-! ## A single reference scale works uniformly on an interval

`mid_band_unique` attaches to every `x > 0`, `x ∉ Mid E`, a *unique* positive `ρ ∈ E` such that no
element of `Mid E` lies strictly between `x` and `ρ` (the "slot" of `x`).  Here we show that on an
interval `(α, β)` on which `f` is continuous, positive and avoids the finite-ish scale set `Mid E`,
one and the same `ρ` works for *every* `x ∈ (α, β)`.

The mechanism is the intermediate value theorem: for a fixed `m ∈ Mid E`, the continuous image
`f '' (α, β)` is preconnected and never hits `m`, so `f` stays on one side of `m` throughout the
interval; hence `f x < m ↔ f x₀ < m` for every `x`, where `x₀` is any reference point.  Combined
with the slot property at the single point `x₀`, this gives the uniform statement.

The dichotomy "`f` stays on one side of `m`" is the general lemma `side_of_avoid`. -/

theorem band_const {E : Set ℝ} (hE : E.Finite) (hne : ∃ ρ ∈ E, 0 < ρ)
    {f : ℝ → ℝ} {α β : ℝ} (hαβ : α < β)
    (hcont : ContinuousOn f (Set.Ioo α β))
    (hpos : ∀ x ∈ Set.Ioo α β, 0 < f x)
    (havoid : ∀ x ∈ Set.Ioo α β, f x ∉ Work.WilC4.Mid E) :
    ∃ ρ ∈ E, 0 < ρ ∧
      ∀ x ∈ Set.Ioo α β, ∀ m ∈ Work.WilC4.Mid E,
        ¬ (min (f x) ρ < m ∧ m < max (f x) ρ) := by
  classical
  obtain ⟨x0, hx0⟩ : ∃ x0 : ℝ, x0 ∈ Set.Ioo α β := ⟨(α + β) / 2, by
    exact ⟨by linarith, by linarith⟩⟩
  obtain ⟨ρ0, hρ0, -⟩ := mid_band_unique hE hne (hpos x0 hx0) (havoid x0 hx0)
  obtain ⟨hρ0E, hρ00, hρ0good⟩ := hρ0
  refine ⟨ρ0, hρ0E, hρ00, ?_⟩
  -- on the whole interval, `f` is on the same side of each `m ∈ Mid E` as it is at `x0`.
  have hside : ∀ m ∈ Mid E, (∀ x ∈ Set.Ioo α β, f x < m) ∨
      (∀ x ∈ Set.Ioo α β, m < f x) :=
    fun m hm => side_of_avoid isPreconnected_Ioo hcont havoid hm
  have hiff : ∀ m ∈ Mid E, ∀ x ∈ Set.Ioo α β, (f x < m ↔ f x0 < m) := by
    intro m hm x hx
    rcases hside m hm with h | h
    · exact iff_of_true (h x hx) (h x0 hx0)
    · exact iff_of_false (not_lt.mpr (le_of_lt (h x hx))) (not_lt.mpr (le_of_lt (h x0 hx0)))
  intro x hx m hm
  have hxne : f x ≠ m := fun h => havoid x hx (h ▸ hm)
  have hx0ne : f x0 ≠ m := fun h => havoid x0 hx0 (h ▸ hm)
  -- at the reference point, `f x0` and `ρ0` are on the same side of `m`.
  have hcase : m ≤ min (f x0) ρ0 ∨ max (f x0) ρ0 ≤ m := by
    rcases not_and_or.mp (hρ0good m hm) with h | h
    · exact Or.inl (not_lt.mp h)
    · exact Or.inr (not_lt.mp h)
  rintro ⟨h1, h2⟩
  rcases hcase with hle | hge
  · -- `m` is below both `f x0` and `ρ0`, hence below `f x` as well
    have hmfx0 : m < f x0 := lt_of_le_of_ne (le_trans hle (min_le_left _ _)) (Ne.symm hx0ne)
    have hmfx_le : m ≤ f x := not_lt.mp fun hfxm =>
      absurd ((hiff m hm x hx).mp hfxm) (not_lt.mpr (le_of_lt hmfx0))
    have hmfx : m < f x := lt_of_le_of_ne hmfx_le (Ne.symm hxne)
    have hmρ0 : m ≤ ρ0 := le_trans hle (min_le_right _ _)
    have hlt : ρ0 < m := by
      rcases min_lt_iff.mp h1 with h | h
      · exact absurd h (not_lt.mpr (le_of_lt hmfx))
      · exact h
    linarith
  · -- `m` is above both `f x0` and `ρ0`, hence above `f x` as well
    have hfx0m : f x0 < m := lt_of_le_of_ne (le_trans (le_max_left _ _) hge) hx0ne
    have hfxm : f x < m := (hiff m hm x hx).mpr hfx0m
    have hρ0m : ρ0 ≤ m := le_trans (le_max_right _ _) hge
    have hlt : m < ρ0 := by
      rcases lt_max_iff.mp h2 with h | h
      · exact absurd h (not_lt.mpr (le_of_lt hfxm))
      · exact h
    linarith

end Work.WilC4
