import Mathlib

/-!
# Uniform integer approximation of continuous real functions on a light profinite set

Let `S` be a light profinite set (a second countable compact Hausdorff totally disconnected
space) and `y : ℕ → C(S, ℝ)` a sequence of continuous real-valued functions.  We show that there
are continuous integer-valued functions `x n : C(S, ℤ)` together with a single natural number `N`
such that `|y n s - x n s| ≤ N` for all `n` and all `s : S`.

The point is that the bound is *uniform in `n`* even though each `x n` is chosen independently:
for a single continuous `f : C(S, ℝ)` we can always find `x : C(S, ℤ)` with `|f s - x s| ≤ 2` for
all `s`.  Indeed, `ℝ` is covered by the neighbourhood of the diagonal
`{(a, b) | |a - b| < 1/2}`, so by
`ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal` the map `f` is `1/2`-approximated
by one factoring through a finite type `Fin n`; rounding the finitely many values with
`Int.floor` (which moves each value by less than `1`) yields a locally constant — hence
continuous, as `Fin n` is discrete — integer-valued function within distance `2`.
-/

namespace Work.ANALYTIC

open Set TopologicalSpace

theorem prodReal_rounding (S : LightProfinite) (y : ℕ → ContinuousMap S ℝ) :
    ∃ x : ℕ → ContinuousMap S ℤ, ∃ N : ℕ, ∀ n : ℕ, ∀ s : S, |y n s - (x n s : ℝ)| ≤ (N : ℝ) := by
  classical
  -- For a single real-valued continuous function we can bound the rounding error by `2`.
  have key : ∀ f : ContinuousMap S ℝ, ∃ x : ContinuousMap S ℤ, ∀ s : S, |f s - (x s : ℝ)| ≤ 2 := by
    intro f
    by_cases hE : IsEmpty S
    · -- On the empty space the statement is vacuous.
      exact ⟨⟨fun s => hE.elim s, continuous_iff_continuousAt.mpr (fun s => hE.elim s)⟩,
        fun s => hE.elim s⟩
    · -- `S` is nonempty: approximate `f` by a map factoring through a finite type.
      have hS : {p : ℝ × ℝ | |p.1 - p.2| < 1 / 2} ∈ nhdsSet (diagonal ℝ) := by
        rw [mem_nhdsSet_iff_forall]
        rintro ⟨a, b⟩ hab
        simp only [diagonal, mem_ofPred_eq] at hab
        subst hab
        exact IsOpen.mem_nhds (isOpen_lt (by fun_prop) continuous_const) (by simp)
      obtain ⟨n, g, h, hg, hgh⟩ := f.exists_finite_approximation_of_mem_nhds_diagonal hS
      refine ⟨⟨fun s => ⌊h (g s)⌋, ?_⟩, fun s => ?_⟩
      · -- `s ↦ ⌊h (g s)⌋` is continuous: `Fin n` is discrete and `g` is continuous.
        exact (continuous_of_discreteTopology (f := fun i : Fin n => ⌊h i⌋)).comp hg
      · -- Error estimate: `1/2` from the approximation, less than `1` from `Int.floor`.
        have h1 : |f s - h (g s)| < 1 / 2 := by
          have := hgh s
          simpa using this
        have h2 : |h (g s) - (⌊h (g s)⌋ : ℝ)| < 1 := by
          rw [abs_lt]
          exact ⟨by have := Int.floor_le (h (g s)); linarith,
            by have := Int.lt_floor_add_one (h (g s)); linarith⟩
        calc |f s - (⌊h (g s)⌋ : ℝ)| ≤ |f s - h (g s)| + |h (g s) - (⌊h (g s)⌋ : ℝ)| :=
              abs_sub_le _ _ _
          _ ≤ 2 := by linarith
  choose x hx using key
  exact ⟨fun n => x (y n), 2, fun n s => by simpa using hx (y n) s⟩

end Work.ANALYTIC
