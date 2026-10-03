import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.Deps
import Submission.Lib.Unif2.Work.Parabolic.not_exists_hasGreenFunctionWeak_of_not_compact

namespace Work.Parabolic

/-- **The pole of a Green function is genuine**: `E` is unbounded in every neighbourhood of `z₀`.
This is the "coefficient of the logarithmic pole is positive" half of the normalisation of Green
data, and it is what makes the pole of `E` (and hence the zero of the holomorphic modulus
`exp (-E)`) a genuine logarithmic singularity.

Proof (same shape as `Work.Parabolic.not_exists_hasGreenFunctionWeak_of_not_compact`): if `E` were
bounded by `C` near `z₀`, the closed set `{ε ≤ E}` with `ε > C` would miss `z₀` (it is closed: away
from `z₀` because `E` is harmonic there, and `z₀ ∉ closure {ε ≤ E}` by boundedness), so
`Work.Potential.removable_singularity_of_bounded_near` would extend `E` to a non-negative harmonic
`U` on `X`.  Taking `p` with `U p > 0` and the component `Ω` of `{U > U p / 2}` containing `p`
(compact closure, since `{U ≥ c} ⊆ closure {c ≤ E} ∪ {z₀}` by relative compactness of the
superlevel sets of `E`), the maximum principle gives a contradiction — unless `closure Ω = X`,
i.e. `X` compact. -/
theorem unbounded_near_pole_of_isGreenFunctionAt {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ}
    (h : Work.Parabolic.IsGreenFunctionAt (X := X) z₀ E) :
    ∀ A : ℝ, ∀ V : Set X, V ∈ nhds z₀ → ∃ x ∈ V, x ≠ z₀ ∧ A < E x := by
  classical
  intro A V hV
  by_contra hcon
  -- ### Step 1: `E` is bounded in a punctured neighbourhood of `z₀`.
  have hbound : ∃ M : ℝ, ∃ W : Set X, W ∈ nhds z₀ ∧ ∀ x ∈ W, x ≠ z₀ → |E x| ≤ M := by
    refine ⟨|A|, V, hV, fun x hxV hxz => ?_⟩
    have hle : E x ≤ A := by
      by_contra hlt
      exact hcon ⟨x, hxV, hxz, not_le.mp hlt⟩
    rw [abs_of_pos (h.pos hxz)]
    exact le_trans hle (le_abs_self A)
  -- ### Step 2: extension of `E` to a function harmonic on all of `X`.
  obtain ⟨U, hUharm, hUeq⟩ :=
    Work.Potential.removable_singularity_of_bounded_near h.harmonic hbound
  have hUcont : Continuous U := Submission.HarmonicOnX_continuous hUharm
  -- ### Step 3: the superlevel sets of `U` are compact.
  have hUcompact : ∀ ε : ℝ, 0 < ε → IsCompact {x : X | ε ≤ U x} := by
    intro ε hε
    have hsub : {x : X | ε ≤ U x} ⊆ closure {x : X | ε ≤ E x} ∪ {z₀} := by
      intro x hx
      by_cases hxz : x = z₀
      · exact Or.inr (by simp [hxz])
      · refine Or.inl (subset_closure ?_)
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [← hUeq x hxz]
        exact hx
    exact ((h.isCompact_closure_level hε).union isCompact_singleton).of_isClosed_subset
      (isClosed_le continuous_const hUcont) hsub
  -- ### Step 4: `U` attains a global maximum.
  obtain ⟨p, hpne⟩ := exists_ne_of_not_compact hX z₀
  have hUp : 0 < U p := by rw [hUeq p hpne]; exact h.pos hpne
  have hSne : ({x : X | U p ≤ U x}).Nonempty :=
    ⟨p, by simp only [Set.mem_ofPred_eq]; exact le_refl _⟩
  obtain ⟨x₀, hx₀S, hx₀max⟩ := (hUcompact (U p) hUp).exists_isMaxOn hSne hUcont.continuousOn
  have hSp : p ∈ ({x : X | U p ≤ U x}) := by
    simp only [Set.mem_ofPred_eq]; exact le_refl _
  have hp₀ : U p ≤ U x₀ := hx₀max hSp
  have hmax : ∀ x : X, U x ≤ U x₀ := by
    intro x
    by_cases hx : U p ≤ U x
    · exact hx₀max (by simpa only [Set.mem_ofPred_eq] using hx)
    · exact le_trans (le_of_lt (lt_of_not_ge hx)) hp₀
  -- ### Step 5: the strong maximum principle forces `U` to be constant.
  have hconst : ∀ x : X, U x = U x₀ :=
    Submission.SubharmonicOnX.eq_of_isMaxOn
      (hUharm.subharmonic hUcont.continuousOn) hmax
  -- ### Step 6: hence `X` is compact, contradiction.
  have huniv : {x : X | U p / 2 ≤ U x} = Set.univ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rw [hconst x]
    linarith
  have hhalf : 0 < U p / 2 := by linarith
  have hcomp_univ : IsCompact (Set.univ : Set X) := by
    rw [← huniv]
    exact hUcompact (U p / 2) hhalf
  exact hX (isCompact_univ_iff.mp hcomp_univ)

end Work.Parabolic
