import Mathlib

namespace Work.RPB1a

/-- A real-valued function which is continuous on a compact set and strictly positive
there has a strictly positive lower bound on that set. -/
theorem exists_pos_le_of_compact {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    {K : Set α} (hK : IsCompact K) (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ μ > 0, ∀ x ∈ K, μ ≤ f x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f x₀, hpos x₀ hx₀K, fun x hx => isMinOn_iff.mp hmin x hx⟩
  · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-- **Uniform separation for large steps.**  For a continuous map `u : ℝ → ℂ` which is
injective modulo `2π`, the displacement `‖u (t + h) - u t‖` is bounded below by a positive
constant `μ` as `(t, h)` ranges over `t ∈ [0, 2π]` and `δ ≤ |h| ≤ π`.  The admissible
set of pairs is compact, `u (t + h) ≠ u t` on it (a coincidence would force `h ∈ 2πℤ`,
which is incompatible with `0 < δ ≤ |h| ≤ π`), and a continuous positive function on a
compact set has a positive lower bound. -/
theorem uniform_large_step (u : ℝ → ℂ) (hcont : Continuous u)
    (hinj : ∀ t t' : ℝ, u t = u t' → ∃ k : ℤ, t' = t + 2 * Real.pi * k)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ μ > 0, ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∀ h : ℝ, δ ≤ |h| → |h| ≤ Real.pi →
      μ ≤ ‖u (t + h) - u t‖ := by
  classical
  -- The admissible `h`-set, written as a union of two intervals so that it is compact.
  set T : Set ℝ := Set.Icc (-Real.pi) (-δ) ∪ Set.Icc δ Real.pi with hT
  -- The compact set of admissible pairs `(t, h)`.
  set K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ T with hK
  have hmemT : ∀ h : ℝ, h ∈ T ↔ δ ≤ |h| ∧ |h| ≤ Real.pi := by
    intro h
    rw [hT]
    simp only [Set.mem_union, Set.mem_Icc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have hneg : h < 0 := by linarith
        rw [abs_of_neg hneg]
        exact ⟨by linarith, by linarith⟩
      · have hpos : 0 ≤ h := by linarith
        rw [abs_of_nonneg hpos]
        exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hh : 0 ≤ h
      · right
        rw [abs_of_nonneg hh] at h1 h2
        exact ⟨h1, h2⟩
      · left
        rw [abs_of_neg (not_le.mp hh)] at h1 h2
        exact ⟨by linarith, by linarith⟩
  have hKcompact : IsCompact K := by
    rw [hK, hT]
    exact isCompact_Icc.prod (isCompact_Icc.union isCompact_Icc)
  -- On `K` the displacement is strictly positive: distinct points of the circle are distinct images.
  have hpos : ∀ p ∈ K, 0 < ‖u (p.1 + p.2) - u p.1‖ := by
    intro p hp
    rw [hK, Set.mem_prod] at hp
    obtain ⟨-, hp2⟩ := hp
    rw [hmemT p.2] at hp2
    obtain ⟨hhδ, hhπ⟩ := hp2
    rw [norm_pos_iff]
    intro hzero
    have heq : u (p.1 + p.2) = u p.1 := sub_eq_zero.mp hzero
    obtain ⟨k, hk⟩ := hinj (p.1 + p.2) p.1 heq
    have hp2eq : p.2 = -(2 * Real.pi * (k : ℝ)) := by linarith
    have hkabs : |(k : ℝ)| ≤ 1 / 2 := by
      have h2 : 2 * Real.pi * |(k : ℝ)| ≤ Real.pi := by
        have habs : |p.2| = 2 * Real.pi * |(k : ℝ)| := by
          rw [hp2eq, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        rw [← habs]
        exact hhπ
      nlinarith [Real.pi_pos]
    have hk0 : k = 0 := by
      have h1 : |(k : ℝ)| < 1 := by linarith
      rw [abs_lt] at h1
      obtain ⟨ha1, ha2⟩ := h1
      have ha1' : (-1 : ℤ) < k := by exact_mod_cast ha1
      have ha2' : k < 1 := by exact_mod_cast ha2
      omega
    rw [hk0] at hp2eq
    simp at hp2eq
    rw [hp2eq] at hhδ
    simp at hhδ
    linarith
  obtain ⟨μ, hμpos, hμ⟩ := exists_pos_le_of_compact (f := fun p : ℝ × ℝ => ‖u (p.1 + p.2) - u p.1‖)
    hKcompact ((by fun_prop : Continuous (fun p : ℝ × ℝ => ‖u (p.1 + p.2) - u p.1‖)).continuousOn) hpos
  refine ⟨μ, hμpos, ?_⟩
  intro t ht h hhδ hhπ
  have hmem : (t, h) ∈ K := by
    rw [hK]
    exact Set.mk_mem_prod ht ((hmemT h).mpr ⟨hhδ, hhπ⟩)
  have := hμ (t, h) hmem
  simpa using this

end Work.RPB1a
