import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.ODE

open Set
open scoped Topology ContDiff

/-- If `u` has derivative `w` everywhere on a set `s` with unique derivatives, and `w` is `C^n` on
`s`, then `u` is `C^(n+1)` on `s`. This is the "primitive of a `C^n` function is `C^(n+1)`"
bootstrap step. -/
theorem contDiffOn_succ_of_hasDerivAt_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u w : ℝ → E} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {n : ℕ} (hw : ContDiffOn ℝ n w s)
    (hu : ∀ t ∈ s, HasDerivAt u (w t) t) :
    ContDiffOn ℝ (n + 1) u s := by
  rw [contDiffOn_succ_iff_derivWithin hs]
  have hdiff : DifferentiableOn ℝ u s :=
    fun t ht => (hu t ht).differentiableAt.differentiableWithinAt
  refine ⟨hdiff, ?_, ?_⟩
  · intro h
    exact absurd h (WithTop.natCast_ne_top n)
  · exact hw.congr (fun t ht => (hu t ht).hasDerivWithinAt.derivWithin (hs t ht))

theorem contDiffOn_of_hasDerivAt_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : ℝ → E → E} {y : ℝ → E} {a b : ℝ} {n : ℕ} {U : Set (ℝ × E)}
    (hG : ContDiffOn ℝ n (fun p : ℝ × E => G p.1 p.2) U)
    (hyU : ∀ t ∈ Set.uIcc a b, (t, y t) ∈ U)
    (hy : ∀ t ∈ Set.uIcc a b, HasDerivAt y (G t (y t)) t)
    (hyc : ContinuousOn y (Set.uIcc a b)) :
    ContDiffOn ℝ n y (Set.uIcc a b) := by
  have key : ∀ (a b : ℝ), a ≤ b →
      (∀ t ∈ Set.uIcc a b, (t, y t) ∈ U) →
      (∀ t ∈ Set.uIcc a b, HasDerivAt y (G t (y t)) t) →
      ContinuousOn y (Set.uIcc a b) →
      ContDiffOn ℝ n y (Set.uIcc a b) := by
    intro a b hab hyU hy hyc
    rw [Set.uIcc_of_le hab] at hyU hy hyc ⊢
    rcases eq_or_lt_of_le hab with heq | hlt
    · subst heq
      rw [Set.Icc_self]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact contDiffWithinAt_singleton
    · have hs : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hlt
      have hmain : ∀ k ≤ n, ContDiffOn ℝ k y (Set.Icc a b) := by
        intro k
        induction k with
        | zero =>
            intro _
            rw [Nat.cast_zero, contDiffOn_zero]
            exact hyc
        | succ k ih =>
            intro hk
            have hk' : k ≤ n := Nat.le_of_succ_le hk
            have hyk : ContDiffOn ℝ k y (Set.Icc a b) := ih hk'
            have hGk : ContDiffOn ℝ k (fun p : ℝ × E => G p.1 p.2) U :=
              hG.of_le (Nat.cast_le.mpr hk')
            have hpair : ContDiffOn ℝ k (fun t : ℝ => (t, y t)) (Set.Icc a b) :=
              contDiffOn_id.prodMk hyk
            have hcomp : ContDiffOn ℝ k (fun t => G t (y t)) (Set.Icc a b) := by
              have h := hGk.comp hpair hyU
              simpa only [Function.comp_def] using h
            exact contDiffOn_succ_of_hasDerivAt_of_contDiffOn hs hcomp hy
      exact hmain n le_rfl
  have hI : Set.uIcc (min a b) (max a b) = Set.uIcc a b := by
    simp only [Set.uIcc]
    rw [min_eq_left (min_le_max (a := a) (b := b)),
        max_eq_right (min_le_max (a := a) (b := b))]
  have hk := key (min a b) (max a b) (min_le_max (a := a) (b := b))
    (by rw [hI]; exact hyU) (by rw [hI]; exact hy) (by rw [hI]; exact hyc)
  rwa [hI] at hk

end Commons.Analysis.ODE