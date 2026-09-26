import Mathlib

set_option linter.style.haveILetI false

namespace Work.Smooth.Morse.Flow

/-- A continuous function `F : ℝ → ℝ → X` whose second variable ranges over the closed
interval `[0, 2π]` and which identifies the two endpoints (`F s (2π) = F s 0`) descends to a
continuous function on `ℝ × AddCircle (2π)`, still denoted by the same values on `[0, 2π]`.

This is the standard "continuous map out of a quotient" fact: the parametrisation
`Icc 0 (2π) → AddCircle (2π)` is a quotient map, and `Prod.map id` of it is a quotient map
because it is a closed surjection (compactness). -/
theorem exists_continuous_addCircle_lift {X : Type*} [TopologicalSpace X]
    (F : ℝ → ℝ → X)
    (hF : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ Set.Icc 0 (2 * Real.pi)))
    (hper : ∀ s : ℝ, F s (2 * Real.pi) = F s 0) :
    ∃ G : ℝ × AddCircle (2 * Real.pi) → X, Continuous G ∧
      ∀ s : ℝ, ∀ u ∈ Set.Icc 0 (2 * Real.pi), G (s, (u : AddCircle (2 * Real.pi))) = F s u := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  -- The representative in `(0, 2π]` of a class in `AddCircle (2π)`.
  let e : AddCircle (2 * Real.pi) ≃ Set.Ioc 0 (0 + 2 * Real.pi) := AddCircle.equivIoc (2 * Real.pi) 0
  let G : ℝ × AddCircle (2 * Real.pi) → X :=
    fun x => F x.1 ((e x.2 : Set.Ioc 0 (0 + 2 * Real.pi)) : ℝ)
  have hGprop : ∀ s : ℝ, ∀ u ∈ Set.Icc 0 (2 * Real.pi),
      G (s, (u : AddCircle (2 * Real.pi))) = F s u := by
    intro s u hu
    simp only [G]
    rcases eq_or_ne u 0 with h | h
    · -- `u = 0`: the chosen representative is `2π`, and `hper` identifies it with `0`.
      subst h
      rw [AddCircle.coe_zero]
      have h0 : (0 : AddCircle (2 * Real.pi)) = (↑(2 * Real.pi) : AddCircle (2 * Real.pi)) :=
        (AddCircle.coe_period (2 * Real.pi)).symm
      have hmem : (2 * Real.pi) ∈ Set.Ioc 0 (0 + 2 * Real.pi) :=
        ⟨by positivity, by rw [zero_add]⟩
      have hval : ((e (0 : AddCircle (2 * Real.pi))) : ℝ) = 2 * Real.pi := by
        rw [h0]
        exact AddCircle.equivIoc_coe_of_mem hmem
      rw [hval]
      exact hper s
    · -- `u ≠ 0`: the chosen representative is `u` itself.
      have hmem : u ∈ Set.Ioc 0 (0 + 2 * Real.pi) :=
        ⟨lt_of_le_of_ne hu.1 h.symm, by rw [zero_add]; exact hu.2⟩
      have hval : ((e (u : AddCircle (2 * Real.pi))) : ℝ) = u :=
        AddCircle.equivIoc_coe_of_mem hmem
      rw [hval]
  refine ⟨G, ?_, hGprop⟩
  -- The parametrisation `Icc 0 (2π) → AddCircle (2π)`, which is a quotient map.
  let π : Set.Icc 0 (2 * Real.pi) → AddCircle (2 * Real.pi) :=
    fun u => ((u : ℝ) : AddCircle (2 * Real.pi))
  have hπcont : Continuous π := (AddCircle.continuous_mk' (2 * Real.pi)).comp continuous_subtype_val
  have hπsurj : Function.Surjective π := by
    intro q
    obtain ⟨x, hx, hxq⟩ := AddCircle.eq_coe_Ioc (p := 2 * Real.pi) q
    exact ⟨⟨x, ⟨le_of_lt hx.1, hx.2⟩⟩, hxq⟩
  have hπproper : IsProperMap π := hπcont.isProperMap
  -- `id × π` is a closed surjection, hence a quotient map.
  have hQclosed : IsClosedMap (Prod.map (id : ℝ → ℝ) π) :=
    ((isProperMap_id (X := ℝ)).prodMap hπproper).isClosedMap
  have hQcont : Continuous (Prod.map (id : ℝ → ℝ) π) :=
    continuous_id.prodMap hπcont
  have hQsurj : Function.Surjective (Prod.map (id : ℝ → ℝ) π) := by
    rintro ⟨s, q⟩
    obtain ⟨u, hu⟩ := hπsurj q
    exact ⟨(s, u), by simp [Prod.map, hu]⟩
  have hQquot : Topology.IsQuotientMap (Prod.map (id : ℝ → ℝ) π) :=
    IsClosedMap.isQuotientMap hQclosed hQcont hQsurj
  -- Continuity of `G` follows from continuity of `G ∘ (id × π) = F` on `univ × Icc 0 (2π)`.
  have hcomp : Continuous (G ∘ Prod.map (id : ℝ → ℝ) π) := by
    have hinner : Continuous
        (Prod.map (id : ℝ → ℝ) (Subtype.val : Set.Icc 0 (2 * Real.pi) → ℝ)) :=
      continuous_id.prodMap continuous_subtype_val
    have hmem : ∀ x, (Prod.map (id : ℝ → ℝ) (Subtype.val : Set.Icc 0 (2 * Real.pi) → ℝ)) x ∈
        Set.univ ×ˢ Set.Icc 0 (2 * Real.pi) := by
      intro x
      exact ⟨trivial, x.2.2⟩
    have hFcont : Continuous (Function.uncurry F ∘
        Prod.map (id : ℝ → ℝ) (Subtype.val : Set.Icc 0 (2 * Real.pi) → ℝ)) :=
      hF.comp_continuous hinner hmem
    have heq : (G ∘ Prod.map (id : ℝ → ℝ) π) = (Function.uncurry F ∘
        Prod.map (id : ℝ → ℝ) (Subtype.val : Set.Icc 0 (2 * Real.pi) → ℝ)) := by
      funext x
      obtain ⟨s, u⟩ := x
      show G (s, π u) = Function.uncurry F (s, (u : ℝ))
      rw [hGprop s (u : ℝ) u.2]
      rfl
    rw [heq]
    exact hFcont
  exact (Topology.IsQuotientMap.continuous_iff hQquot).mpr hcomp

end Work.Smooth.Morse.Flow
