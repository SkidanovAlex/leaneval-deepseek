import Mathlib
import Submission.Work.WilE7.Defs

/-!
  Area E7: elementary (point-level) facts about the coordinate operations `takeZ` / `padZ`
  and the projection `projFirst`.

  All five clauses are pure bookkeeping about `Fin` indices: `padZ` zero-extends a point,
  `takeZ` truncates it, `projFirst n M` is the corresponding truncation, and on `ℝ^{n+0}`
  the projection to the first `n` coordinates is the identity up to the (definitionally
  equal) identification `Fin (n+0) ≃ Fin n`.
-/

namespace Work.WilE7

open WilkiesDesign.E

/-- Evaluation rule for `padZ` inside the "kept" range. -/
theorem padZ_apply_lt {K k : ℕ} (x : Fin k → ℝ) (j : Fin K) (h : j.val < k) :
    padZ K x j = x ⟨j.val, h⟩ := dite_eq_left h

/-- Evaluation rule for `padZ` outside the "kept" range. -/
theorem padZ_apply_ge {K k : ℕ} (x : Fin k → ℝ) (j : Fin K) (h : ¬ j.val < k) :
    padZ K x j = 0 := dite_eq_right h

/-- Evaluation rule for `takeZ`. -/
theorem takeZ_apply {k K : ℕ} (hm : k ≤ K) (x : Fin K → ℝ) (i : Fin k) :
    takeZ hm x i = x ⟨i.val, lt_of_lt_of_le i.isLt hm⟩ := rfl

/-- On `ℝ^{n+0}`, the projection to the first `n` coordinates is the identity. -/
theorem projFirst_zero {n : ℕ} (x : Fin (n + 0) → ℝ) : projFirst n 0 x = x := by
  funext i
  exact congrArg x (Fin.ext rfl)

theorem pad_z :
    (∀ {k K : ℕ} (hm : k ≤ K) (x : Fin k → ℝ),
        Work.WilE7.takeZ hm (Work.WilE7.padZ K x) = x) ∧
    (∀ {k K : ℕ} {x : Fin k → ℝ}, x ∈ WilkiesDesign.E.cubeC k →
        Work.WilE7.padZ K x ∈ WilkiesDesign.E.cubeC K) ∧
    (∀ {n m M : ℕ} (hm : m ≤ M) (x : Fin (n + m) → ℝ),
        WilkiesDesign.E.projFirst n M (Work.WilE7.padZ (n + M) x) =
          WilkiesDesign.E.projFirst n m x) ∧
    (∀ {n M : ℕ} (x : Fin (n + M) → ℝ),
        WilkiesDesign.E.projFirst n M x = Work.WilE7.takeZ (Nat.le_add_right n M) x) ∧
    (∀ {n : ℕ} (S : Set (Fin (n + 0) → ℝ)), WilkiesDesign.E.projFirst n 0 '' S = S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k K hm x
    funext i
    exact (padZ_apply_lt x ⟨i.val, lt_of_lt_of_le i.isLt hm⟩ i.isLt).trans
      (congrArg x (Fin.ext rfl))
  · intro k K x hx
    have hx' : ∀ i : Fin k, |x i| ≤ 1 := hx
    show ∀ i : Fin K, |padZ K x i| ≤ 1
    intro i
    by_cases h : i.val < k
    · rw [padZ_apply_lt x i h]
      exact hx' ⟨i.val, h⟩
    · rw [padZ_apply_ge x i h]
      simp
  · intro n m M hm x
    funext i
    show (padZ (n + M) x) (Fin.castAdd M i) = x (Fin.castAdd m i)
    rw [padZ_apply_lt x (Fin.castAdd M i) (lt_of_lt_of_le i.isLt (Nat.le_add_right n m))]
    exact congrArg x (Fin.ext rfl)
  · intro n M x
    funext i
    show x (Fin.castAdd M i) =
      x ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_add_right n M)⟩
    exact congrArg x (Fin.ext rfl)
  · intro n S
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      rwa [projFirst_zero x]
    · rintro y hy
      exact ⟨y, hy, projFirst_zero y⟩

end Work.WilE7
