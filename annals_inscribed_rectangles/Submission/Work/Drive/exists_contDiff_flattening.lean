import Mathlib

namespace Work.Drive

open scoped ContDiff

/-- **A smooth "flattening" of `R` into a neighbourhood of the interval `[a,b]`.**

For `a < b` and `ε > 0` there is a globally `C^inf` map `f : R -> R` which is the identity on
`[a,b]` and whose image is contained in the open interval `(a-ε, b+ε)`.

(Explicit construction: `f x = a + ∫_a^x ρ`, where `ρ : R → [0,1]` is smooth, `ρ = 1` on `[a,b]`
and `ρ = 0` outside a small neighbourhood of `[a,b]` of length `< ε`.) -/
theorem exists_contDiff_flattening (a b : ℝ) (hab : a < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      (∀ x ∈ Set.Icc a b, f x = x) ∧
      ∀ x : ℝ, f x ∈ Set.Ioo (a - ε) (b + ε) := by
  -- Explicit construction.  With `δ = ε/2` and `s = Real.smoothTransition` (a global `C^∞`
  -- function which is `0` on `(-∞,0]` and `1` on `[1,∞)`, with values in `[0,1]`), set
  -- `f x = x - (x - a) * s ((a - x)/δ) - (x - b) * s ((x - b)/δ)`.
  -- Then `f` is the identity on `[a,b]`, equals `a` for `x ≤ a - δ`, equals `b` for `x ≥ b + δ`,
  -- is monotone between, and its image lies in `[a - δ, b + δ] ⊂ (a - ε, b + ε)`.
  set δ : ℝ := ε / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδlt : δ < ε := by rw [hδdef]; linarith
  refine ⟨fun x => x + (a - x) * Real.smoothTransition ((a - x) / δ)
      + (b - x) * Real.smoothTransition ((x - b) / δ), ?_, ?_, ?_⟩
  · -- global smoothness
    fun_prop
  · -- the identity on `[a,b]`
    intro x hx
    obtain ⟨hax, hxb⟩ := hx
    have h1 : Real.smoothTransition ((a - x) / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδpos.le)
    have h2 : Real.smoothTransition ((x - b) / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδpos.le)
    simp [h1, h2]
  · -- the image lies in `[a - δ, b + δ]`, and `[a - δ, b + δ] ⊂ (a - ε, b + ε)`
    intro x
    dsimp only
    have hg : ∀ t : ℝ, 0 ≤ t → t * (1 - Real.smoothTransition (t / δ)) ∈ Set.Icc (0:ℝ) δ := by
      intro t ht
      rcases le_or_gt t δ with h | h
      · have hs0 : 0 ≤ Real.smoothTransition (t / δ) := Real.smoothTransition.nonneg _
        have hs1 : Real.smoothTransition (t / δ) ≤ 1 := Real.smoothTransition.le_one _
        refine ⟨mul_nonneg ht (by linarith), ?_⟩
        calc t * (1 - Real.smoothTransition (t / δ)) ≤ t * 1 := by
              apply mul_le_mul_of_nonneg_left _ ht; linarith
          _ = t := mul_one t
          _ ≤ δ := h
      · have hs : Real.smoothTransition (t / δ) = 1 :=
          Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hδpos]; simpa using h.le)
        rw [hs, sub_self, mul_zero]
        exact ⟨le_refl 0, hδpos.le⟩
    rcases le_or_gt x a with hxa | hax
    · -- `x ≤ a`: `f x = a - (a - x) * (1 - s ((a-x)/δ)) ∈ [a - δ, a]`
      have h2 : Real.smoothTransition ((x - b) / δ) = 0 :=
        Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδpos.le)
      have hkey := hg (a - x) (by linarith)
      have hfx : x + (a - x) * Real.smoothTransition ((a - x) / δ)
          + (b - x) * Real.smoothTransition ((x - b) / δ)
          = a - (a - x) * (1 - Real.smoothTransition ((a - x) / δ)) := by
        rw [h2, mul_zero, add_zero]; ring
      rw [hfx]
      obtain ⟨hlo, hhi⟩ := hkey
      constructor <;> linarith [hδlt, hab, hε]
    · rcases le_or_gt x b with hxb | hbx
      · -- `a ≤ x ≤ b`: `f x = x`
        have h1 : Real.smoothTransition ((a - x) / δ) = 0 :=
          Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδpos.le)
        have h2 : Real.smoothTransition ((x - b) / δ) = 0 :=
          Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδpos.le)
        have hfx : x + (a - x) * Real.smoothTransition ((a - x) / δ)
            + (b - x) * Real.smoothTransition ((x - b) / δ) = x := by
          rw [h1, h2]; ring
        rw [hfx]
        constructor <;> linarith [hab, hε]
      · -- `b ≤ x`: `f x = b + (x - b) * (1 - s ((x-b)/δ)) ∈ [b, b + δ]`
        have h1 : Real.smoothTransition ((a - x) / δ) = 0 :=
          Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδpos.le)
        have hkey := hg (x - b) (by linarith)
        have hfx : x + (a - x) * Real.smoothTransition ((a - x) / δ)
            + (b - x) * Real.smoothTransition ((x - b) / δ)
            = b + (x - b) * (1 - Real.smoothTransition ((x - b) / δ)) := by
          rw [h1, mul_zero, add_zero]; ring
        rw [hfx]
        obtain ⟨hlo, hhi⟩ := hkey
        constructor <;> linarith [hδlt, hab, hε]

end Work.Drive
