import Mathlib
import Submission.Work.FBif.Glue
import Submission.Work.FBif.glueMu_invariant

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

open Classical Filter Set Function

/-! ## Bounding the pull-back of a constant coefficient

If `‖∂F z‖ ≤ κ ‖∂̄F z‖` and the pulled-back value `m` satisfies `‖m‖ ≤ κ`, then the
coefficient obtained by pulling `m` back along `F` at `z` has norm at most `κ`, provided
either `∂F z = 0` or `m = 0`.  These are the two regimes occurring along the orbit of the
gluing construction: inside the inner ball the perturbation is antiholomorphic
(`∂F = 0`), and at the very first step of the pull-back the seed `0` is used. -/

theorem norm_pullRev_const_le {F : ℂ → ℂ} {κ : ℝ} {z : ℂ} {m : ℂ}
    (hratio : ‖Work.MRMT.dz F z‖ ≤ κ * ‖Work.MRMT.dzbar F z‖)
    (hκ : 0 ≤ κ) (hcond : Work.MRMT.dz F z = 0 ∨ m = 0) (hm : ‖m‖ ≤ κ) :
    ‖Work.MRMT.Found.pullRev (Function.const ℂ m) F z‖ ≤ κ := by
  rw [show Work.MRMT.Found.pullRev (Function.const ℂ m) F z =
      (star (Work.MRMT.dz F z) + star m * Work.MRMT.dzbar F z) /
      (star (Work.MRMT.dzbar F z) + star m * Work.MRMT.dz F z) from rfl]
  by_cases hb : Work.MRMT.dzbar F z = 0
  · have ha : Work.MRMT.dz F z = 0 := by
      have h := hratio
      simp only [hb, norm_zero, mul_zero] at h
      exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    rw [hb, ha]
    simp only [star_zero, zero_mul, mul_zero, zero_add, add_zero, zero_div, norm_zero]
    exact hκ
  · rcases hcond with ha | hm0
    · rw [ha]
      simp only [star_zero, zero_mul, mul_zero, zero_add, add_zero]
      simp only [norm_div, norm_mul, norm_star]
      rw [mul_div_cancel_right₀ ‖m‖ (norm_ne_zero_iff.mpr hb)]
      exact hm
    · rw [hm0]
      simp only [star_zero, zero_mul, mul_zero, zero_add, add_zero]
      simp only [norm_div, norm_star]
      rw [div_le_iff₀ (norm_pos_iff.mpr hb)]
      exact hratio

/-! ## Bounding the iterated pull-back along an escaping orbit -/

theorem pullIter_norm_le {F : ℂ → ℂ} {R α κ : ℝ}
    (hzin : ∀ z : ℂ, ‖z‖ < α → Work.MRMT.dz F z = 0)
    (hesc : ∀ z : ℂ, α ≤ ‖z‖ → R ≤ ‖F z‖)
    (hratio : ∀ z : ℂ, ‖Work.MRMT.dz F z‖ ≤ κ * ‖Work.MRMT.dzbar F z‖)
    (hκ : 0 ≤ κ) :
    ∀ (n : ℕ) (z : ℂ), (∀ j < n, ‖(F^[j]) z‖ < R) → R ≤ ‖(F^[n]) z‖ →
      ‖pullIter F n z‖ ≤ κ := by
  intro n
  induction n with
  | zero =>
    intro z _ _
    rw [pullIter_zero, norm_zero]
    exact hκ
  | succ n ih =>
    intro z hmin hhit
    have hmin' : ∀ j < n, ‖(F^[j]) (F z)‖ < R := by
      intro j hj
      have h := hmin (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at h
    have hhit' : R ≤ ‖(F^[n]) (F z)‖ := by
      have h := hhit
      rwa [Function.iterate_succ_apply] at h
    have hIH : ‖pullIter F n (F z)‖ ≤ κ := ih (F z) hmin' hhit'
    have hstep : pullIter F (n + 1) z =
        Work.MRMT.Found.pullRev (Function.const ℂ (pullIter F n (F z))) F z := by
      rw [pullIter_succ]
      exact pullRev_congr (by rw [Function.const_apply])
    rw [hstep]
    have hcond : Work.MRMT.dz F z = 0 ∨ pullIter F n (F z) = 0 := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · right
        rw [h0]
        exact pullIter_zero F (F z)
      · left
        apply hzin
        by_contra h
        push Not at h
        have h1 : R ≤ ‖(F^[1]) z‖ := by
          rw [Function.iterate_one]
          exact hesc z h
        have h2 : ‖(F^[1]) z‖ < R := hmin 1 (by omega)
        linarith
    exact norm_pullRev_const_le (hratio z) hκ hcond hIH

/-! ## The target lemma -/

theorem norm_glueMu_le {F : ℂ → ℂ} {R α β κ : ℝ}
    (hzout : ∀ z : ℂ, β < ‖z‖ → Work.MRMT.dz F z = 0)
    (hzin : ∀ z : ℂ, ‖z‖ < α → Work.MRMT.dz F z = 0)
    (hesc : ∀ z : ℂ, α ≤ ‖z‖ → R ≤ ‖F z‖)
    (hratio : ∀ z : ℂ, ‖Work.MRMT.dz F z‖ ≤ κ * ‖Work.MRMT.dzbar F z‖)
    (hκ : 0 ≤ κ) :
    ∀ z : ℂ, ‖Work.FBif.glueMu F R z‖ ≤ κ := by
  intro z
  by_cases hz : ∃ n : ℕ, R ≤ ‖(F^[n]) z‖
  · rw [glueMu_eq_pullIter hz]
    refine pullIter_norm_le hzin hesc hratio hκ (Nat.find hz) z ?_ ?_
    · intro j hj
      exact not_le.mp (Nat.find_min hz hj)
    · exact Nat.find_spec hz
  · rw [glueMu_of_not_hit hz, norm_zero]
    exact hκ

end Work.FBif
