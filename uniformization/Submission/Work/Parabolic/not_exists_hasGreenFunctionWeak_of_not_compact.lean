import Mathlib
import Submission.Work.Parabolic.Deps

/-!
# `HasGreenFunctionWeak` is unsatisfiable on a non-compact connected complex curve

The interface `Submission.HasGreenFunctionWeak z₀ E` demands that every superlevel set
`{x | ε ≤ E x}` of `E` (`ε > 0`) be **compact** — not merely relatively compact, and in particular
closed.  This file shows that no such `E` exists on a connected, non-compact complex
one-manifold.

The argument is the classical "no Green function on a parabolic surface" argument, in the
following form.

* Since `E` is finite at the pole, the compact set `{x | ε₀ ≤ E x}` for `ε₀ > max (E z₀) 0` misses
  `z₀`; its complement is therefore a neighbourhood of `z₀` on which `0 < E < ε₀`, i.e. on which
  `E` is bounded.  So the removable-singularity theorem
  `Work.Potential.removable_singularity_of_bounded_near` extends `E` to a function `U` harmonic on
  all of `X`, agreeing with `E` off `z₀`.
* Every superlevel set of `U` is then compact: it differs from the corresponding superlevel set of
  `E` only at the point `z₀` (and is closed because `U` is continuous).
* Choose `p ≠ z₀` (a point distinct from `z₀` exists as soon as `X` is not compact) and let `x₀` be
  a point of the compact set `{x | U p ≤ U x}` maximising `U` there.  Then `U p ≤ U x₀`, so `x₀` is
  a *global* maximum of `U` (off that compact set, `U < U p ≤ U x₀`), and the strong maximum
  principle `Submission.SubharmonicOnX.eq_of_isMaxOn` (`U` is subharmonic on `X`, being harmonic)
  makes `U` constant with value `U x₀ > 0`.
* But then `{x | U p / 2 ≤ U x} = X`, and being a superlevel set of `U` at level `U p / 2 > 0` it
  is compact; so `X` is compact, contradicting `hX`.

No connected-component or frontier argument is needed: the compactness of the superlevel sets is
used only through the *attainment of the maximum* of `U`, which is exactly what makes `E` a
Green function (and is impossible for a non-constant non-negative harmonic function on a parabolic
surface).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Parabolic

/-- **A non-compact space has at least two points.**  Equivalently: if every point of `X` equals
`z₀` then `X` is a singleton, hence compact. -/
theorem exists_ne_of_not_compact {X : Type*} [TopologicalSpace X] (hX : ¬ CompactSpace X)
    (z₀ : X) : ∃ x : X, x ≠ z₀ := by
  by_contra h
  have h' : ∀ x : X, x = z₀ := fun x => by
    by_contra hx
    exact h ⟨x, hx⟩
  have hsub : (Set.univ : Set X).Subsingleton := by
    intro a _ b _
    exact (h' a).trans (h' b).symm
  exact hX (isCompact_univ_iff.mp hsub.isCompact)

/-- **The interface `Submission.HasGreenFunctionWeak` is unsatisfiable on non-compact connected
complex one-manifolds.**  Since `E : X → ℝ` must be finite at the pole `z₀`, the demand that the
superlevel sets `{x | ε ≤ E x}` be *compact* (rather than relatively compact) forces `E` to be
bounded near `z₀`: take `ε₀ > max (E z₀) 0`; the compact set `{ε₀ ≤ E}` is closed and misses `z₀`,
so its complement is a neighbourhood of `z₀` on which `0 < E < ε₀`, i.e. `|E| ≤ ε₀`.  The bounded
`E` extends harmonically across `z₀` (`Work.Potential.removable_singularity_of_bounded_near`),
giving a harmonic function `U` on all of `X` with `U = E` off `z₀`; the superlevel sets of `U` are
compact because they differ from those of `E` only at the point `z₀` and `U` is continuous.
Choosing `p ≠ z₀` (a point distinct from `z₀` exists because `X` is not compact), the compact set
`{U ≥ U p}` contains `p`, so `U` attains there a maximum `U x₀ ≥ U p`, which is a global maximum of
`U` (off that compact set, `U < U p ≤ U x₀`).  The strong maximum principle
(`Submission.SubharmonicOnX.eq_of_isMaxOn`, applied to the subharmonic function `U`) makes `U`
constant with value `U x₀ > 0`, and then `{U ≥ U p / 2} = X`: being a superlevel set at the positive
level `U p / 2` it is compact, so `X` is compact — contradicting `hX`.  Hence no such `E`
exists. -/
theorem not_exists_hasGreenFunctionWeak_of_not_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (z₀ : X) :
    ¬ ∃ E : X → ℝ, Submission.HasGreenFunctionWeak z₀ E := by
  classical
  rintro ⟨E, hpos, hharm, hcomp⟩
  obtain ⟨p, hpne⟩ := exists_ne_of_not_compact hX z₀
  -- ### Step 1: `E` is bounded in a punctured neighbourhood of `z₀`.
  set ε₀ : ℝ := max (E z₀) 0 + 1 with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; linarith [le_max_right (E z₀) (0 : ℝ)]
  have hEz₀lt : E z₀ < ε₀ := by rw [hε₀]; linarith [le_max_left (E z₀) (0 : ℝ)]
  have hK : IsCompact {x : X | ε₀ ≤ E x} := hcomp ε₀ hε₀pos
  have hz₀K : z₀ ∉ {x : X | ε₀ ≤ E x} := fun h => absurd h (not_le.mpr hEz₀lt)
  have hV : {x : X | ε₀ ≤ E x}ᶜ ∈ 𝓝 z₀ := hK.isClosed.isOpen_compl.mem_nhds hz₀K
  have hbound : ∃ M : ℝ, ∃ V : Set X, V ∈ 𝓝 z₀ ∧ ∀ x ∈ V, x ≠ z₀ → |E x| ≤ M :=
    ⟨ε₀, _, hV, fun x hx hxz => by
      have hxlt : E x < ε₀ := by
        simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] using hx
      rw [abs_of_pos (hpos x hxz)]
      exact le_of_lt hxlt⟩
  -- ### Step 2: extension of `E` to a function harmonic on all of `X`.
  obtain ⟨U, hUharm, hUeq⟩ :=
    Work.Potential.removable_singularity_of_bounded_near hharm hbound
  have hUcont : Continuous U := Submission.HarmonicOnX_continuous hUharm
  -- ### Step 3: the superlevel sets of `U` are compact.
  have hUcompact : ∀ ε : ℝ, 0 < ε → IsCompact {x : X | ε ≤ U x} := by
    intro ε hε
    have hsub : {x : X | ε ≤ U x} ⊆ {x : X | ε ≤ E x} ∪ {z₀} := by
      intro x hx
      by_cases hxz : x = z₀
      · exact Or.inr (by simp [hxz])
      · refine Or.inl ?_
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [← hUeq x hxz]
        exact hx
    exact ((hcomp ε hε).union isCompact_singleton).of_isClosed_subset
      (isClosed_le continuous_const hUcont) hsub
  -- ### Step 4: `U` attains a global maximum.
  have hUp : 0 < U p := by rw [hUeq p hpne]; exact hpos p hpne
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
