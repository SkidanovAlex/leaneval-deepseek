import Submission.Work.WilkiesD.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Area D (truncation) — pushing a truncated zero set through projections

The frozen structure `WilkiesDesign.SOMin` has a projection axiom only for the *last*
coordinate (`SOMin.proj`, i.e. `projLast`).  The truncation argument needs to project
`boxZero M P ⊆ ℝ^(n+m)` onto its first `n` coordinates, i.e. to drop `m` coordinates.
We therefore define `projFst m A` as the `m`-fold iterate of `projLast` and prove
(`projFst_mem_Ω`) that it adds `m` to the format counter and leaves the degree unchanged.

`projFst_mem_iff` identifies `projFst m A` with the projection `x ↦ (x, w) ↦ w` described
by `Fin.append`, which is the form in which the witnesses of `ExpExist` appear.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesD
open WilkiesDesign WilkiesConjecture

/-- Project `A ⊆ ℝ^(n+m)` onto the first `n` coordinates, by iterating `projLast`. -/
def projFst {n : ℕ} : (m : ℕ) → Set (Fin (n + m) → ℝ) → Set (Fin n → ℝ)
  | 0, A => A
  | m + 1, A => projFst m (projLast A)

@[simp]
theorem projFst_zero {n : ℕ} (A : Set (Fin (n + 0) → ℝ)) : projFst 0 A = A := rfl

theorem projFst_succ {n m : ℕ} (A : Set (Fin (n + (m + 1)) → ℝ)) :
    projFst (m + 1) A = projFst m (projLast A) := rfl

/-- `projFst m A` is the set of `x` for which some `y : Fin m → ℝ` makes `Fin.append x y`
lie in `A`.  This is the form in which the `ExpExist` witnesses are given. -/
theorem projFst_mem_iff {n : ℕ} (m : ℕ) (A : Set (Fin (n + m) → ℝ)) (x : Fin n → ℝ) :
    x ∈ projFst m A ↔ ∃ y : Fin m → ℝ, Fin.append x y ∈ A := by
  induction m with
  | zero =>
      rw [projFst_zero]
      constructor
      · intro hx
        refine ⟨Fin.elim0, ?_⟩
        rw [Fin.append_elim0]
        simpa using hx
      · rintro ⟨y, hy⟩
        rw [show y = (Fin.elim0 : Fin 0 → ℝ) from funext fun i => i.elim0] at hy
        rw [Fin.append_elim0] at hy
        simpa using hy
  | succ m ih =>
      rw [projFst_succ, ih]
      constructor
      · rintro ⟨y, t, ht⟩
        exact ⟨Fin.snoc y t, by rwa [Fin.append_snoc]⟩
      · rintro ⟨y', hy'⟩
        exact ⟨Fin.init y', y' (Fin.last m),
          by rw [← Fin.append_snoc, Fin.snoc_init_self]; exact hy'⟩

theorem projFst_mono {n m : ℕ} {A B : Set (Fin (n + m) → ℝ)} (h : A ⊆ B) :
    projFst m A ⊆ projFst m B := by
  intro x hx
  rw [projFst_mem_iff] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, h hy⟩

end Work.WilkiesD
