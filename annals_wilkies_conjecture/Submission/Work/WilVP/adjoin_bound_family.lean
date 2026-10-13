import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilVP

open FirstOrder FirstOrder.Language

/-- The order embedding `Fin (k+2) → Fin ((k+1)+2)` which omits the coordinate `2`.

So a tuple `z` with `k+3` coordinates splits as `(z 0, z 1, z 2, z 3, …, z (k+2))`, and the
composed tuple `z ∘ skipTwo k = (z 0, z 1, z 3, …, z (k+2))` has the coordinate `2` deleted. -/
def skipTwo (k : ℕ) : Fin (k + 2) → Fin ((k + 1) + 2) :=
  Fin.succAbove (Fin.succ (Fin.succ (0 : Fin (k + 1))))

/-- Deleting the coordinate `2` from a tuple `Fin.cons x (Fin.cons y c')` and then re-indexing
the parameter tuple by `Fin.succ` gives `Fin.cons x (Fin.cons y (c' ∘ Fin.succ))`. -/
lemma cons_skipTwo {M : Type} {k : ℕ} (x y : M) (c' : Fin (k + 1) → M) :
    (Fin.cons x (Fin.cons y c')) ∘ (skipTwo k)
      = Fin.cons x (Fin.cons y (c' ∘ Fin.succ)) := by
  show (Fin.cons x (Fin.cons y c')) ∘ (Fin.succAbove (Fin.succ (Fin.succ (0 : Fin (k + 1)))))
      = Fin.cons x (Fin.cons y (c' ∘ Fin.succ))
  funext i
  simp only [Function.comp_apply]
  have h0 : Fin.succAbove (Fin.succ (Fin.succ (0 : Fin (k + 1)))) (0 : Fin (k + 2))
      = (0 : Fin (k + 3)) := by
    rw [Fin.succAbove_succ_of_le (i := (0 : Fin (k + 2))) (p := Fin.succ (0 : Fin (k + 1)))
      (Fin.zero_le _)]
    exact Fin.castSucc_zero
  have h1 : Fin.succAbove (Fin.succ (Fin.succ (0 : Fin (k + 1)))) (Fin.succ (0 : Fin (k + 1)))
      = (0 : Fin (k + 2)).succ := by
    rw [Fin.succAbove_succ_of_le (i := Fin.succ (0 : Fin (k + 1)))
      (p := Fin.succ (0 : Fin (k + 1))) le_rfl]
    apply Fin.ext
    simp
  have h2 : ∀ j : Fin k, Fin.succAbove (Fin.succ (Fin.succ (0 : Fin (k + 1))))
      (Fin.succ (Fin.succ j)) = (Fin.succ (Fin.succ j)).succ := by
    intro j
    have hlt : Fin.succ (0 : Fin (k + 1)) < Fin.succ (Fin.succ j) := by
      rw [Fin.lt_def]
      simp [Fin.val_succ]
    rw [Fin.succAbove_succ_of_lt (i := Fin.succ (Fin.succ j))
      (p := Fin.succ (0 : Fin (k + 1))) hlt]
  induction i using Fin.cases with
  | zero => rw [h0, Fin.cons_zero, Fin.cons_zero]
  | succ j =>
    induction j using Fin.cases with
    | zero => rw [h1, Fin.cons_succ, Fin.cons_succ, Fin.cons_zero, Fin.cons_zero]
    | succ j' =>
      rw [h2 j', Fin.cons_succ, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]
      rfl

/-- The coordinate `0` of a tuple `Fin.cons x (Fin.cons y c')`. -/
lemma cons_zero_apply {M : Type} {k : ℕ} (x y : M) (c' : Fin (k + 1) → M) :
    ((Fin.cons x (Fin.cons y c') : Fin (k + 3) → M) (0 : Fin (k + 3))) = x :=
  Fin.cons_zero (α := fun _ => M) x (Fin.cons y c' : Fin (k + 2) → M)

/-- The coordinate `2` of a tuple `Fin.cons x (Fin.cons y c')`. -/
lemma cons_two_apply {M : Type} {k : ℕ} (x y : M) (c' : Fin (k + 1) → M) :
    ((Fin.cons x (Fin.cons y c') : Fin (k + 3) → M) (2 : Fin (k + 3))) = c' 0 := by
  have h : (2 : Fin (k + 3)) = Fin.succ (Fin.succ (0 : Fin (k + 1))) := by
    apply Fin.ext
    simp
  rw [h, Fin.cons_succ (α := fun _ => M), Fin.cons_succ (α := fun _ => M)]

/-- The coordinate `2` of a tuple `Fin.cons x (Fin.cons y (Fin.cons R c))`. -/
lemma cons_two_cons {M : Type} {k : ℕ} (x y R : M) (c : Fin k → M) :
    ((Fin.cons x (Fin.cons y (Fin.cons R c)) : Fin (k + 3) → M) (2 : Fin (k + 3))) = R := by
  have h : (2 : Fin (k + 3)) = Fin.succ (Fin.succ (0 : Fin (k + 1))) := by
    apply Fin.ext
    simp
  rw [h, Fin.cons_succ (α := fun _ => M), Fin.cons_succ (α := fun _ => M)]
  rfl

/-- `x * x + u * u = R * R` forces `|x| ≤ |R|` in any ordered field: dropping the square `u²`
from `x² + u² = R²` gives `x² ≤ R²`, and the square is monotone for nonnegative arguments. -/
lemma abs_le_of_sq_sum_eq {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x R u : M} (h : x * x + u * u = R * R) : |x| ≤ |R| := by
  have h1 : x * x ≤ R * R := by nlinarith [mul_self_nonneg u]
  have h2 : x ^ 2 ≤ R ^ 2 := by simpa [sq] using h1
  exact sq_le_sq.mp h2

theorem adjoin_bound_family {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    {k : ℕ} {Y₀ : Set (Fin (k + 2) → M)}
    (hY₀ : (∅ : Set M).Definable WilkiesDesign.CG.LRc Y₀)
    (hfun : ∀ (c' : Fin k → M) (x y y' : M), Fin.cons x (Fin.cons y c') ∈ Y₀ →
        Fin.cons x (Fin.cons y' c') ∈ Y₀ → y = y')
    (hBnd : (∅ : Set M).Definable WilkiesDesign.CG.LRc
      {v : Fin ((k + 1) + 2) → M | ∃ u : M, v 0 * v 0 + u * u = v 2 * v 2}) :
    ∃ Y : Set (Fin ((k + 1) + 2) → M), (∅ : Set M).Definable WilkiesDesign.CG.LRc Y ∧
      (∀ (c' : Fin (k + 1) → M) (x y y' : M), Fin.cons x (Fin.cons y c') ∈ Y →
        Fin.cons x (Fin.cons y' c') ∈ Y → y = y') ∧
      (∀ c' : Fin (k + 1) → M, ∃ R' : M, ∀ x y : M, Fin.cons x (Fin.cons y c') ∈ Y → |x| ≤ R') ∧
      (∀ (x y R : M) (c : Fin k → M), Fin.cons x (Fin.cons y c) ∈ Y₀ →
        (∃ u : M, x * x + u * u = R * R) → Fin.cons x (Fin.cons y (Fin.cons R c)) ∈ Y) := by
  -- Adjoin the coordinate `R` in position `2` as an extra *parameter*: the parameter tuple of
  -- `Y` is `Fin.cons R c`, so the square-sum bound on the coordinate `0` of `Y` bounds the
  -- domain of the `c'`-fibre by `|c' 0|`.
  let Y : Set (Fin ((k + 1) + 2) → M) :=
    ((fun g : Fin ((k + 1) + 2) → M => g ∘ (skipTwo k)) ⁻¹' Y₀) ∩
      {v : Fin ((k + 1) + 2) → M | ∃ u : M, v 0 * v 0 + u * u = v 2 * v 2}
  refine ⟨Y, ?_, ?_, ?_, ?_⟩
  · -- `Y` is definable: a pullback of `Y₀` along a fixed reindexing, intersected with the
    -- definable square-sum relation.
    exact (hY₀.preimage_comp (skipTwo k)).inter hBnd
  · -- `Y` is the graph of a function: its `Y₀`-part is the graph of the same function, with the
    -- parameter tuple re-indexed by `Fin.succ`.
    intro c' x y y' hy hy'
    have h1 : Fin.cons x (Fin.cons y (c' ∘ Fin.succ)) ∈ Y₀ := by
      have hmem := hy.1
      change (Fin.cons x (Fin.cons y c')) ∘ (skipTwo k) ∈ Y₀ at hmem
      rw [cons_skipTwo (k := k) x y c'] at hmem
      exact hmem
    have h2 : Fin.cons x (Fin.cons y' (c' ∘ Fin.succ)) ∈ Y₀ := by
      have hmem := hy'.1
      change (Fin.cons x (Fin.cons y' c')) ∘ (skipTwo k) ∈ Y₀ at hmem
      rw [cons_skipTwo (k := k) x y' c'] at hmem
      exact hmem
    exact hfun (c' ∘ Fin.succ) x y y' h1 h2
  · -- Every fibre is bounded: the two free coordinates `0`, `2` of `Y` satisfy the square-sum
    -- relation, so in the `c'`-fibre the variable `x = z 0` satisfies `|x| ≤ |z 2| = |c' 0|`.
    intro c'
    refine ⟨|c' 0|, ?_⟩
    intro x y hxy
    obtain ⟨u, hu⟩ := hxy.2
    rw [cons_zero_apply (k := k) x y c', cons_two_apply (k := k) x y c'] at hu
    exact abs_le_of_sq_sum_eq hu
  · -- Adjoining the bound: the `Y₀`-tuple `(x, y, c)` is the deletion of the coordinate `2` of
    -- `(x, y, R, c)`, and the bound `∃ u, x² + u² = R²` is exactly the extra conjunct.
    intro x y R c hY0 hbnd
    refine ⟨?_, ?_⟩
    · change (Fin.cons x (Fin.cons y (Fin.cons R c))) ∘ (skipTwo k) ∈ Y₀
      rw [cons_skipTwo (k := k) x y (Fin.cons R c), Fin.cons_comp_succ]
      exact hY0
    · obtain ⟨u, hu⟩ := hbnd
      refine ⟨u, ?_⟩
      rw [cons_zero_apply (k := k) x y (Fin.cons R c),
        cons_two_cons (k := k) x y R c]
      exact hu

end Work.WilVP
