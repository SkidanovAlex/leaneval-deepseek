import Mathlib
import Submission.Work.Diff.STE.B3.ENormSq_le_succ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ENormSq_zero_le_ENormSq`: the `L²` energy is controlled by any higher energy

For a smooth function `R` supported in the open unit cube and its periodisation
`P z = ∑' m, R (z + iVec m)` the physical energy of order `0` is bounded by a constant times the
energy of order `k`, for every `k ≥ 1`.

The proof is the `k`-fold iterate of the Sobolev gain `ENormSq_le_succ`
(`ENormSq m P ≤ C_m · ENormSq (m+1) P`, one order of differentiability bought per step):

`ENormSq 0 P ≤ C₀ · ENormSq 1 P ≤ C₀ C₁ · ENormSq 2 P ≤ ⋯ ≤ (∏_{i<k} C_i) · ENormSq k P`.

Since `k` is fixed, the product `∏ C_i` is a genuine (fixed) constant, so an existential constant
quantified before `R, P` suffices.  (No uniformity in `m` is needed, and none is claimed.)
-/

namespace Work.Diff.STE.B3

/-- **The energy chain.**  For every order `m`, the `L²` (`m = 0`) energy of a periodisation is
bounded by a constant (depending only on `ι` and `m`) times its energy of order `m`.  This is the
iteration of `ENormSq_le_succ`. -/
lemma ENormSq_zero_le_of_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R P : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) R →
      Function.support R ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      ContDiff ℝ (⊤ : ℕ∞) P → Work.Diff.STE.Periodic1 P →
      (∀ z : ι → ℝ, P z = ∑' m' : ι → ℤ, R (z + Work.Diff.STE.iVec m')) →
      Work.Diff.STE.ENormSq 0 P ≤ C * Work.Diff.STE.ENormSq m P := by
  induction m with
  | zero =>
      exact ⟨1, zero_le_one,
        fun R P hR hsupp hP hper hrepr => by rw [one_mul]⟩
  | succ m ih =>
      obtain ⟨C, hC, hCp⟩ := ih
      obtain ⟨D, hD, hDp⟩ := ENormSq_le_succ (ι := ι) m
      refine ⟨C * D, mul_nonneg hC hD, fun R P hR hsupp hP hper hrepr => ?_⟩
      calc Work.Diff.STE.ENormSq 0 P
          ≤ C * Work.Diff.STE.ENormSq m P := hCp R P hR hsupp hP hper hrepr
        _ ≤ C * (D * Work.Diff.STE.ENormSq (m + 1) P) :=
              mul_le_mul_of_nonneg_left (hDp R P hR hsupp hP hper hrepr) hC
        _ = (C * D) * Work.Diff.STE.ENormSq (m + 1) P := by ring

theorem ENormSq_zero_le_ENormSq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R P : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) R →
      Function.support R ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      ContDiff ℝ (⊤ : ℕ∞) P → Work.Diff.STE.Periodic1 P →
      (∀ z : ι → ℝ, P z = ∑' m' : ι → ℤ, R (z + Work.Diff.STE.iVec m')) →
      Work.Diff.STE.ENormSq 0 P ≤ C * Work.Diff.STE.ENormSq k P :=
  ENormSq_zero_le_of_le (ι := ι) k

end Work.Diff.STE.B3
