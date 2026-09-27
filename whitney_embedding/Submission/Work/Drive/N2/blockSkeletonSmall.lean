import Mathlib
import Submission.Work.Drive.N2.blockSkeleton

/-!
# The block skeleton with an arbitrarily small separation constant

`Work.Drive.N2.exists_blockSkeleton` produces the sorted critical values `s : Fin (n+1) → ℝ` and a
separation constant `η > 0` with `4η < 1` and `s j + 4η < s (j+1)`.  The value of `η` produced is
fixed by that proof, while the window lane needs to *choose* it (the exposed windows' bands are
`|f - c| < (ρ j / 8)² η_j` with `η_j < 1/10`, so the skeleton's separation must be smaller than those,
and the window and collar blocks must sit inside them).

Both conditions on `η` are monotone in `η`, so the skeleton can be re-run with any smaller constant.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff
open Set

/-- **The block skeleton with an arbitrarily small separation constant.**  For every `ε > 0` there is
a block skeleton of `f` whose separation constant is `< ε`. -/
theorem exists_blockSkeleton_small {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Nonempty M]
    (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (hn : 0 < n) (s : Fin (n + 1) → ℝ) (η : ℝ),
      StrictMono s ∧ 0 < η ∧ η < ε ∧
      (∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j)) ∧
      (∀ t : ℝ, (∃ x : M, Work.Drive.Morse.IsCritical f x ∧ f x = t) ↔ ∃ j : Fin n, t = s (Fin.castSucc j)) ∧
      (∀ x : M, s 0 ≤ f x ∧ f x ≤ s (Fin.castSucc ⟨n - 1, by omega⟩)) := by
  obtain ⟨n, hn, s, η, hs, hη, hη1, hgap, hcrit, hrange⟩ := exists_blockSkeleton f hf
  refine ⟨n, hn, s, min η (ε / 2), hs, ?_, ?_, ?_, hcrit, hrange⟩
  · exact lt_min hη (by linarith)
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro j
    have hle : min η (ε / 2) ≤ η := min_le_left _ _
    have h := hgap j
    linarith



/-- **Shrinking the separation constant of a fixed skeleton.**  The two conditions on `η`
(`4η < 1` and `s j + 4η < s (j+1)`) are monotone, so a skeleton with a fixed list `s` of critical
values can be re-run with any smaller separation constant.  This is the form the window lane needs:
the exposed windows' bands are narrow, so the *same* list `s` (hence the same critical points) has to
be used with a smaller `η`. -/
theorem blockSkeleton_shrink {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {f : M → ℝ} {n : ℕ} (hn : 0 < n) {s : Fin (n + 1) → ℝ} {η : ℝ}
    (hs : StrictMono s) (hη : 0 < η)
    (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j))
    (hcrit : ∀ t : ℝ, (∃ x : M, Work.Drive.Morse.IsCritical f x ∧ f x = t) ↔
      ∃ j : Fin n, t = s (Fin.castSucc j))
    (hrange : ∀ x : M, s 0 ≤ f x ∧ f x ≤ s (Fin.castSucc ⟨n - 1, by omega⟩))
    {η' : ℝ} (hη' : 0 < η') (hη'η : η' ≤ η) :
    StrictMono s ∧ 0 < η' ∧
      (∀ j : Fin n, s (Fin.castSucc j) + 4 * η' < s (Fin.succ j)) ∧
      (∀ t : ℝ, (∃ x : M, Work.Drive.Morse.IsCritical f x ∧ f x = t) ↔
        ∃ j : Fin n, t = s (Fin.castSucc j)) ∧
      (∀ x : M, s 0 ≤ f x ∧ f x ≤ s (Fin.castSucc ⟨n - 1, by omega⟩)) :=
  ⟨hs, hη', fun j => by have h := hgap j; linarith, hcrit, hrange⟩

end Work.Drive.N2
