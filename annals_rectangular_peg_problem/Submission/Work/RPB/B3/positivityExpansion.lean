import Mathlib

namespace Work.RPB.B3

/-- **Positivity expands off a slice.** If a continuous `g : ℝ × (ℝ × ℝ) → ℝ` is strictly
positive on the slice `{ρ = 0}` over the rectangle `[a,b] × [c,d]`, then it stays strictly
positive there for all `ρ` in some neighbourhood of `0`.

The proof is a compactness argument: the set `B` of parameters `ρ ∈ [-1,1]` for which some
`(τ,t) ∈ [a,b] × [c,d]` has `g (τ,t,ρ) ≤ 0` is the image under a continuous projection of the
compact set `([a,b] × [c,d] × [-1,1]) ∩ {g ≤ 0}`, hence compact and in particular closed; it does
not contain `0` by hypothesis, so it misses an open ball around `0`. -/
theorem positivityExpansion {g : ℝ × (ℝ × ℝ) → ℝ} (hg : Continuous g)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hpos : ∀ τ ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, 0 < g (τ, t, 0)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ τ ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d,
      ∀ ρ ∈ Set.Icc (-ε₀) ε₀, 0 < g (τ, t, ρ) := by
  classical
  -- The compact box `[a,b] × ([c,d] × [-1,1])` of the domain.
  set C : Set (ℝ × (ℝ × ℝ)) := Set.Icc a b ×ˢ (Set.Icc c d ×ˢ Set.Icc (-1:ℝ) 1) with hC
  have hCc : IsCompact C := by
    rw [hC]; exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  -- The points of the box at which `g` is not positive.
  set A : Set (ℝ × (ℝ × ℝ)) := C ∩ {p | g p ≤ 0} with hA
  have hAc : IsCompact A := by
    rw [hA]; exact hCc.inter_right (isClosed_Iic.preimage hg)
  have hAclosed : IsClosed A := hAc.isClosed
  -- The set of parameters `ρ` for which such a bad point exists.
  set B : Set ℝ := (fun p : ℝ × (ℝ × ℝ) => p.2.2) '' A with hB
  have hBc : IsCompact B := by
    rw [hB]; exact hAc.image continuous_snd.snd
  have hBclosed : IsClosed B := hBc.isClosed
  -- `0` is not one of them, by hypothesis.
  have h0B : (0:ℝ) ∉ B := by
    intro h
    rw [hB, Set.mem_image] at h
    obtain ⟨p, hpA, hp0⟩ := h
    rw [hA, hC, Set.mem_inter_iff, Set.mem_prod, Set.mem_prod, Set.mem_ofPred_eq] at hpA
    obtain ⟨⟨hτ, ht, -⟩, hgle⟩ := hpA
    have hgle' : g (p.1, p.2.1, (0:ℝ)) ≤ 0 := by simpa [← hp0] using hgle
    linarith [hpos p.1 hτ p.2.1 ht]
  -- A closed set missing `0` misses an open ball around `0`.
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hBclosed.isOpen_compl 0 h0B
  refine ⟨min (ε/2) 1, lt_min (half_pos hεpos) one_pos, ?_⟩
  intro τ hτ t ht ρ hρ
  have hρle : |ρ| ≤ min (ε/2) 1 := abs_le.mpr (by simpa [Set.mem_Icc] using hρ)
  by_contra hcon
  have hgle : g (τ, t, ρ) ≤ 0 := le_of_not_gt hcon
  have hρball : ρ ∈ Metric.ball (0:ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have : |ρ| < ε :=
      lt_of_le_of_lt (le_trans hρle (min_le_left _ _)) (half_lt_self hεpos)
    simpa using this
  have hρB : ρ ∈ B := by
    rw [hB, Set.mem_image]
    refine ⟨(τ, t, ρ), ?_, rfl⟩
    rw [hA, hC, Set.mem_inter_iff, Set.mem_prod, Set.mem_prod, Set.mem_ofPred_eq]
    exact ⟨⟨hτ, ht, by
      rw [Set.mem_Icc]
      exact abs_le.mp (le_trans hρle (min_le_right _ _))⟩, hgle⟩
  exact hεsub hρball hρB

end Work.RPB.B3
