import Mathlib
import Submission.Work.Peluse.Ulower.gap_defs

/-!
# The iterated difference does not increase the `ℓ¹`-mass

For a `1`-bounded `F : ℤ → ℂ` with summable norm, the iterated difference
`iterDelta k sh F = Δ'_{sh 0} (Δ'_{sh 1} (⋯ Δ'_{sh (k-1)} F))` of
`Submission/Work/Peluse/Ulower/gap_defs.lean` satisfies

`∑'_x ‖iterDelta k sh F x‖ ≤ ∑'_x ‖F x‖`.

The proof is the obvious one-step induction: `iterDelta (k+1) sh F x = G (x + (sh 0).1) *
star (G (x + (sh 0).2))` where `G = iterDelta k (fun i => sh i.succ) F` is again `1`-bounded
(`norm_iterDelta_le_one`), so `‖iterDelta (k+1) sh F x‖ ≤ ‖G (x + (sh 0).1)‖`; the shift
`x ↦ x + (sh 0).1` is a bijection of `ℤ`, so it preserves both summability and the value of the
`tsum`.

## Main result

* `Work.Peluse.Ulower.iterDelta_tsum_le`
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

/-- The shift `x ↦ x + a` as a permutation of `ℤ`. -/
private def shiftE (a : ℤ) : ℤ ≃ ℤ where
  toFun := fun x => x + a
  invFun := fun x => x - a
  left_inv := fun x => by simp
  right_inv := fun x => by simp

/-- Summability of a real-valued sequence on `ℤ` is invariant under a shift of the index. -/
private lemma summable_add_right {g : ℤ → ℝ} (a : ℤ) (h : Summable g) :
    Summable (fun x : ℤ => g (x + a)) :=
  Summable.comp_injective (f := g) (i := fun x : ℤ => x + a) h
    (fun x y hxy => by
      have hxy' : x + a = y + a := hxy
      omega)

/-- The value of the `tsum` of a real-valued sequence on `ℤ` is invariant under a shift of the
index. -/
private lemma tsum_add_right (g : ℤ → ℝ) (a : ℤ) :
    (∑' x : ℤ, g (x + a)) = ∑' x : ℤ, g x :=
  Equiv.tsum_eq (shiftE a) g

/-- **The induction.**  For a `1`-bounded `F` with summable norm, the iterated difference is
summable and its `ℓ¹`-mass is at most that of `F`. -/
private lemma iterDelta_tsum_aux : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ),
    (∀ x : ℤ, ‖F x‖ ≤ 1) → Summable (fun x : ℤ => ‖F x‖) →
    Summable (fun x : ℤ => ‖iterDelta k sh F x‖) ∧
      (∑' x : ℤ, ‖iterDelta k sh F x‖) ≤ ∑' x : ℤ, ‖F x‖ := by
  intro k
  induction k with
  | zero =>
      intro sh F hbd hsum
      rw [iterDelta_zero]
      exact ⟨hsum, le_rfl⟩
  | succ k ih =>
      intro sh F hbd hsum
      obtain ⟨hS, hleS⟩ := ih (fun i : Fin k => sh i.succ) F hbd hsum
      -- the shift of the inner iterated difference is summable
      have hSsh : Summable
          (fun x : ℤ => ‖iterDelta k (fun i : Fin k => sh i.succ) F (x + (sh 0).1)‖) :=
        summable_add_right (sh 0).1 hS
      -- the pointwise contraction
      have hpt : ∀ x : ℤ, ‖iterDelta (k+1) sh F x‖
          ≤ ‖iterDelta k (fun i : Fin k => sh i.succ) F (x + (sh 0).1)‖ := by
        intro x
        simp only [iterDelta_succ, norm_mul, norm_star]
        have h1 : ‖iterDelta k (fun i : Fin k => sh i.succ) F (x + (sh 0).2)‖ ≤ 1 :=
          norm_iterDelta_le_one k (fun i : Fin k => sh i.succ) F hbd (x + (sh 0).2)
        have h2 : (0 : ℝ) ≤ ‖iterDelta k (fun i : Fin k => sh i.succ) F (x + (sh 0).1)‖ :=
          norm_nonneg _
        calc ‖iterDelta k (fun i : Fin k => sh i.succ) F (x + (sh 0).1)‖ *
              ‖iterDelta k (fun i : Fin k => sh i.succ) F (x + (sh 0).2)‖
            ≤ ‖iterDelta k (fun i : Fin k => sh i.succ) F (x + (sh 0).1)‖ * 1 :=
              mul_le_mul_of_nonneg_left h1 h2
          _ = ‖iterDelta k (fun i : Fin k => sh i.succ) F (x + (sh 0).1)‖ := mul_one _
      have hSnew : Summable (fun x : ℤ => ‖iterDelta (k+1) sh F x‖) :=
        Summable.of_nonneg_of_le (fun x => norm_nonneg _) hpt hSsh
      refine ⟨hSnew, ?_⟩
      have hmain : (∑' x : ℤ, ‖iterDelta (k+1) sh F x‖)
          ≤ ∑' x : ℤ, ‖iterDelta k (fun i : Fin k => sh i.succ) F (x + (sh 0).1)‖ :=
        Summable.tsum_le_tsum hpt hSnew hSsh
      have hshift : (∑' x : ℤ, ‖iterDelta k (fun i : Fin k => sh i.succ) F (x + (sh 0).1)‖)
          = ∑' x : ℤ, ‖iterDelta k (fun i : Fin k => sh i.succ) F x‖ :=
        tsum_add_right (fun y : ℤ => ‖iterDelta k (fun i : Fin k => sh i.succ) F y‖) (sh 0).1
      calc (∑' x : ℤ, ‖iterDelta (k+1) sh F x‖)
          ≤ ∑' x : ℤ, ‖iterDelta k (fun i : Fin k => sh i.succ) F (x + (sh 0).1)‖ := hmain
        _ = ∑' x : ℤ, ‖iterDelta k (fun i : Fin k => sh i.succ) F x‖ := hshift
        _ ≤ ∑' x : ℤ, ‖F x‖ := hleS

theorem iterDelta_tsum_le {k : ℕ} (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ)
    (hbd : ∀ x : ℤ, ‖F x‖ ≤ 1) (hsum : Summable (fun x : ℤ => ‖F x‖)) :
    (∑' x : ℤ, ‖Work.Peluse.Ulower.iterDelta k sh F x‖) ≤ ∑' x : ℤ, ‖F x‖ :=
  (iterDelta_tsum_aux k sh F hbd hsum).2

end

end Work.Peluse.Ulower
