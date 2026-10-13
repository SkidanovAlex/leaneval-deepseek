/-
  Area G4bF: the derivative relation of a definable unary function is `Ω`-definable.

  `derivRel_mem` is the definability step of the final assembly: if the graph of `g : ℝ → ℝ`
  is an `Ω`-set of format `F` and degree budget `D`, then the set of pairs `(x, c)` for which
  `c` is the derivative of `g` at `x` (in the `ε`-`δ` difference-quotient sense) is an
  `Ω`-set of format `F + K` and degree `p.eval D`.

  The first-order work is done in `Submission/Work/WilG1/Plumb`: `Sset N i f ⊆ ℝ^{N+1}` is
  the `Ω`-set obtained from `graphOf f` by eliminating the quantifiers of the `ε`-`δ`
  formula for the derivative in the direction `i` (each quantifier is a projection and each
  atomic formula is a polynomial inequality or a reindexed copy of `graphOf f`).
  `Sset_omega_aux` proves that `Sset N i f` is `Ω`-definable whenever `graphOf f` is, and
  `Sset_char` identifies it with the `ε`-`δ` form `epsDeriv` (equivalently `HasDerivAt`).
  Here we specialise to `N = 1` and `i = 0`, and rewrite `epsDeriv` as the
  difference-quotient form appearing in the statement (`epsDeriv_iff_drForm`).
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Plumb.junkPartial_mem
import Submission.Work.WilG5.Basic

set_option autoImplicit false

noncomputable section

namespace Work.WilG4bF

open WilkiesDesign WilkiesConjecture

/-- The `ε`-`δ` form of the derivative (`epsDeriv`, i.e. `HasDerivAt` written with
`g (a + h) - g a - c * h`) agrees with the difference-quotient form used in `derivRel_mem`.

The two forms differ only in that the quotient form quantifies over `y ≠ a` (there is no
difference quotient at `y = a`), whereas `epsDeriv` also quantifies over `h = 0`, where its
estimate reads `0 ≤ ε * 0` and is therefore trivial. -/
theorem epsDeriv_iff_drForm (g : ℝ → ℝ) (a c : ℝ) :
    Work.WilG1.Plumb.epsDeriv g a c ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ,
        0 < |y - a| → |y - a| < δ → |(g y - g a) / (y - a) - c| ≤ ε := by
  rw [Work.WilG1.Plumb.epsDeriv]
  constructor
  · intro H ε hε
    obtain ⟨δ, hδ0, hδ⟩ := H ε hε
    refine ⟨δ, hδ0, fun y hy hylt => ?_⟩
    have hne : y - a ≠ 0 := abs_pos.mp hy
    -- the `epsDeriv` estimate at `h = y - a`
    have h1 : |g y - g a - c * (y - a)| ≤ ε * |y - a| := by
      have h := hδ (y - a) hylt
      rwa [show a + (y - a) = y by ring] at h
    -- divide the estimate by `|y - a| > 0`
    have h2 : (g y - g a) / (y - a) - c = (g y - g a - c * (y - a)) / (y - a) := by
      rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
    rw [h2, abs_div, div_le_iff₀ (abs_pos.mpr hne)]
    exact h1
  · intro H ε hε
    obtain ⟨δ, hδ0, hδ⟩ := H ε hε
    refine ⟨δ, hδ0, fun h hh => ?_⟩
    rcases eq_or_ne h 0 with rfl | hh0
    · simp
    · have h1 : 0 < |a + h - a| := by
        rw [show a + h - a = h by ring]; exact abs_pos.mpr hh0
      have h2 : |a + h - a| < δ := by
        rw [show a + h - a = h by ring]; exact hh
      have h3 := hδ (a + h) h1 h2
      rw [show a + h - a = h by ring] at h3
      -- multiply the quotient estimate by `|h|`
      have h4 : g (a + h) - g a - c * h = h * ((g (a + h) - g a) / h - c) := by
        rw [mul_sub, mul_div_cancel₀ _ hh0]
        ring
      rw [h4, abs_mul, mul_comm ε]
      exact mul_le_mul_of_nonneg_left h3 (abs_nonneg h)

theorem derivRel_mem (S : WilkiesDesign.SOMin) {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    ∃ K : ℕ, ∃ p : Polynomial ℕ,
      {z : Fin 2 → ℝ | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ,
          0 < |y - z 0| → |y - z 0| < δ →
            |(g y - g (z 0)) / (y - z 0) - z 1| ≤ ε} ∈ S.Ω (F + K) (p.eval D) 2 := by
  -- `Sset 1 0 ·` is the `Ω`-set constructed from the graph of the one-variable function
  -- `x ↦ g (x 0)` by eliminating the quantifiers of the `ε`-`δ` formula.
  obtain ⟨a, b, hS⟩ := Work.WilG1.Plumb.Sset_omega_aux (S := S) (N := 1) (F := F) (D := D)
    (i := (0 : Fin 1)) hg
  -- It is exactly the derivative relation of the statement.
  have hset : Work.WilG1.Plumb.Sset 1 (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0)) =
      {z : Fin 2 → ℝ | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ,
          0 < |y - z 0| → |y - z 0| < δ →
            |(g y - g (z 0)) / (y - z 0) - z 1| ≤ ε} := by
    rw [Work.WilG1.Plumb.Sset_char (n := 0) (i := (0 : Fin 1))
      (f := fun x : Fin 1 → ℝ => g (x 0))]
    ext z
    simp only [Set.mem_ofPred_eq]
    -- the curve `t ↦ g t` of the construction is `g` itself
    have h1 : (fun t : ℝ => (fun x : Fin 1 → ℝ => g (x 0))
        ((0 : Fin 1).insertNth t ((0 : Fin 1).removeNth (Fin.init z)))) = g := by
      funext t
      simp
    rw [h1]
    rw [← epsDeriv_iff_drForm g (z 0) (z 1)]
    simp [Fin.init]
  -- format and degree bookkeeping: `a` dominates `F`
  refine ⟨a, b, ?_⟩
  rw [← hset]
  exact Work.WilG5.mem_mono hS (F + a) (b.eval D) (Nat.le_add_left a F) le_rfl

end Work.WilG4bF
