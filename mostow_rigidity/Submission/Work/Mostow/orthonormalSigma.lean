import Mathlib

namespace Work.Mostow

/-- Gluing orthonormal families along an internal orthogonal decomposition: if the subspaces
`P i` are pairwise orthogonal and span, and each has an orthonormal family `u i` spanning it,
then the disjoint union family is orthonormal and spans. -/
theorem orthonormalSigma {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {η : Type*} [Fintype η] (P : η → Submodule ℝ W)
    (horth : ∀ i i', i ≠ i' → ∀ x ∈ P i, ∀ y ∈ P i', inner ℝ x y = 0)
    (hspan : ⨆ i, P i = ⊤) {κ : η → Type*} [∀ i, Fintype (κ i)]
    (u : ∀ i, κ i → W) (hu : ∀ i k, u i k ∈ P i)
    (hon : ∀ i, Orthonormal ℝ (u i)) (hsp : ∀ i, Submodule.span ℝ (Set.range (u i)) = P i) :
    Orthonormal ℝ (fun x : (Σ i, κ i) => u x.1 x.2) ∧
    Submodule.span ℝ (Set.range (fun x : (Σ i, κ i) => u x.1 x.2)) = ⊤ := by
  classical
  -- the range of the glued family is the union of the ranges of the pieces
  have hrange : Set.range (fun x : (Σ i, κ i) => u x.1 x.2) = ⋃ i, Set.range (u i) :=
    Set.range_sigma_eq_iUnion_range (fun x : (Σ i, κ i) => u x.1 x.2)
  constructor
  · -- orthonormality: split on whether the two indices lie in the same piece
    rw [orthonormal_iff_ite]
    rintro ⟨i, k⟩ ⟨j, l⟩
    by_cases hij : i = j
    · subst hij
      -- same piece: reduce to orthonormality of `u i`
      have hh := (orthonormal_iff_ite.mp (hon i)) k l
      rw [hh]
      by_cases hkl : k = l
      · subst hkl; simp
      · simp [hkl]
    · -- different pieces: pairwise orthogonality of the decomposition
      have hne : (⟨i, k⟩ : Σ i, κ i) ≠ ⟨j, l⟩ := by
        intro h
        exact hij (by simpa using congrArg Sigma.fst h)
      rw [horth i j hij (u i k) (hu i k) (u j l) (hu j l)]
      simp [hne]
  · -- spanning: the span of the union is the supremum of the spans, which is `⊤`
    rw [hrange, Submodule.span_iUnion, iSup_congr hsp, hspan]

end Work.Mostow
