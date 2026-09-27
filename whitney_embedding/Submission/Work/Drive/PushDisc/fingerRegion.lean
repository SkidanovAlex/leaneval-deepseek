import Mathlib

/-!
# The finger region of the classical Whitney move

The analysis of `Drive/NOTES_NOGO_MODULATED_TRANSLATION.md` shows that no *modulated translation*
can serve as the Whitney push, and that the surviving design is the classical one: the witness `W₀`
is a **finger**, i.e. an open neighbourhood of the arc `γ₂` from `p₂` to `q₂` (rather than of the
single point `p₂`), and the ambient isotopy carries that finger into a *cap* attached to its boundary
and otherwise disjoint from `f '' M`.

This file supplies the first, purely point-set half: the finger exists.  It contains the arc, lies in
`W`, contains `p₂ = γ₂ 0` and `q₂ = γ₂ 1`, and misses `p₁` and `q₁` (both are off the arc by the
bigon hypothesis `hγdisj`), and — given the clean-region hypotheses `hclean`/`hsep` — `f` is
injective on it.

## Contents

* `Work.Drive.PushDisc.exists_finger_region`
* `Work.Drive.PushDisc.exists_finger_region_clean`
-/

namespace Work.Drive.PushDisc

/-- **The finger region.**  Let `γ₂ : ℝ → M` be continuous, `γ₂ '' Icc 0 1 ⊆ W` with `W` open in a
regular space, and let `p₁, q₁` be two points off the arc.  Then there is an open `W₀` with
`γ₂ '' Icc 0 1 ⊆ W₀ ⊆ W`, `γ₂ 0, γ₂ 1 ∈ W₀` and `p₁, q₁ ∉ W₀`. -/
theorem exists_finger_region {M : Type*} [TopologicalSpace M] [T1Space M] [RegularSpace M]
    (γ₂ : ℝ → M) (hγ₂ : Continuous γ₂)
    (W : Set M) (hW : IsOpen W) (hγW : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ∈ W)
    (p₁ q₁ : M)
    (h₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ≠ p₁)
    (h₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ≠ q₁) :
    ∃ W₀ : Set M, IsOpen W₀ ∧ W₀ ⊆ W ∧ γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ W₀ ∧
      p₁ ∉ W₀ ∧ q₁ ∉ W₀ := by
  classical
  have hcpt : IsCompact (γ₂ '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image hγ₂
  have hmem : W ∈ nhdsSet (γ₂ '' Set.Icc (0 : ℝ) 1) :=
    hW.mem_nhdsSet.mpr (by rintro x ⟨t, ht, rfl⟩; exact hγW t ht)
  obtain ⟨U, hUo, hKU, hUcl⟩ := hcpt.exists_isOpen_closure_subset hmem
  have hclosed : IsClosed ({p₁, q₁} : Set M) :=
    isClosed_singleton.union isClosed_singleton
  have h0 : γ₂ 0 ∈ U \ ({p₁, q₁} : Set M) :=
    ⟨hKU ⟨0, by norm_num, rfl⟩, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h₁ 0 (by norm_num), h₂ 0 (by norm_num)⟩⟩
  have h1 : γ₂ 1 ∈ U \ ({p₁, q₁} : Set M) :=
    ⟨hKU ⟨1, by norm_num, rfl⟩, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h₁ 1 (by norm_num), h₂ 1 (by norm_num)⟩⟩
  refine ⟨U \ ({p₁, q₁} : Set M), hUo.sdiff hclosed, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hUcl (subset_closure hx.1)
  · -- the arc is contained: it lies in `U` and avoids the two removed points
    rintro x ⟨t, ht, rfl⟩
    refine ⟨hKU ⟨t, ht, rfl⟩, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h₁ t ht, h₂ t ht⟩
  · intro h
    exact h.2 (by simp)
  · intro h
    exact h.2 (by simp)

/-- **The finger region, with the clean region.**  In the setting of `exists_finger_region`, if
inside `W` the only `f`-coincidences are the two crossing pairs (`hclean`) and nothing in `W`
collides with anything outside it (`hsep`), then the finger can be chosen so that `f` is injective
on it.  (This is the `W₀` of the classical Whitney move: it contains `p₂, q₂`, misses `p₁, q₁`, and
carries no double point at all.) -/
theorem exists_finger_region_clean {n : ℕ} {M : Type*} [TopologicalSpace M] [T1Space M]
    [RegularSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (γ₂ : ℝ → M) (hγ₂ : Continuous γ₂)
    (W : Set M) (hW : IsOpen W) (hγW : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ∈ W)
    (p₁ p₂ q₁ q₂ : M)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (hp₂ : γ₂ 0 = p₂) (hq₂ : γ₂ 1 = q₂)
    (h₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ≠ p₁)
    (h₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ≠ q₁) :
    ∃ W₀ : Set M, IsOpen W₀ ∧ W₀ ⊆ W ∧ γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ W₀ ∧
      p₂ ∈ W₀ ∧ q₂ ∈ W₀ ∧ p₁ ∉ W₀ ∧ q₁ ∉ W₀ ∧
      (∀ x ∈ W₀, ∀ y ∈ W₀, f x = f y → x = y) := by
  obtain ⟨W₀, hW₀o, hW₀W, harc, hp₁, hq₁⟩ :=
    exists_finger_region γ₂ hγ₂ W hW hγW p₁ q₁ h₁ h₂
  refine ⟨W₀, hW₀o, hW₀W, harc, ?_, ?_, hp₁, hq₁, ?_⟩
  · exact harc ⟨0, by norm_num, hp₂⟩
  · exact harc ⟨1, by norm_num, hq₂⟩
  · intro x hx y hy hxy
    rcases hclean x y (hW₀W hx) (hW₀W hy) hxy with h | h | h | h | h
    · exact h
    · exact absurd (h.1 ▸ hx) hp₁
    · exact absurd (h.2 ▸ hy) hp₁
    · exact absurd (h.1 ▸ hx) hq₁
    · exact absurd (h.2 ▸ hy) hq₁

end Work.Drive.PushDisc
