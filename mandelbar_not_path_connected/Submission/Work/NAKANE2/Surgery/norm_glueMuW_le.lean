import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

/-! ## Bounding the pull-back seed truncated at the first entrance into `W`

`glueMuW F W z` is the iterated pull-back of `0` along the `F`-orbit of `z`, stopped at the
first time the orbit *enters* `W`.  The hypothesis `hone : ∂F z ≠ 0 → F z ∈ W` says that the
only places where the map can be non-antiholomorphic are those whose image already lies in `W`;
hence, before the first entrance into `W`, `∂F` vanishes identically, and the recursive step of
the pull-back only ever evaluates the division formula where `∂F = 0` (or with the seed `0`).
This is the exact analogue of `Work.FBif.norm_glueMu_le`, with the far ball `{‖·‖ ≥ R}`
replaced by the forward-invariant region `W`. -/

/-- Along a finite orbit whose first entrance into `W` happens at time `n`, the `n`-fold
pull-back of `0` has norm at most `κ`. -/
theorem pullIter_norm_le_of_hit {F : ℂ → ℂ} {W : Set ℂ} {κ : ℝ}
    (hratio : ∀ z : ℂ, ‖Work.MRMT.dz F z‖ ≤ κ * ‖Work.MRMT.dzbar F z‖)
    (hκ : 0 ≤ κ)
    (hone : ∀ z : ℂ, Work.MRMT.dz F z ≠ 0 → F z ∈ W) :
    ∀ (n : ℕ) (z : ℂ), (∀ j < n, (F^[j]) z ∉ W) → (F^[n]) z ∈ W →
      ‖Work.FBif.pullIter F n z‖ ≤ κ := by
  intro n
  induction n with
  | zero =>
    intro z _ _
    rw [Work.FBif.pullIter_zero, norm_zero]
    exact hκ
  | succ n ih =>
    intro z hmin hhit
    have hmin' : ∀ j < n, (F^[j]) (F z) ∉ W := by
      intro j hj
      have h := hmin (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at h
    have hhit' : (F^[n]) (F z) ∈ W := by
      have h := hhit
      rwa [Function.iterate_succ_apply] at h
    have hIH : ‖Work.FBif.pullIter F n (F z)‖ ≤ κ := ih (F z) hmin' hhit'
    have hstep : Work.FBif.pullIter F (n + 1) z =
        Work.MRMT.Found.pullRev (Function.const ℂ (Work.FBif.pullIter F n (F z))) F z := by
      rw [Work.FBif.pullIter_succ]
      exact Work.FBif.pullRev_congr (by rw [Function.const_apply])
    rw [hstep]
    have hcond : Work.MRMT.dz F z = 0 ∨ Work.FBif.pullIter F n (F z) = 0 := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · right
        rw [h0]
        exact Work.FBif.pullIter_zero F (F z)
      · left
        by_contra hne
        have hFzW : F z ∈ W := hone z hne
        have hnotW : (F^[1]) z ∉ W := hmin 1 (by omega)
        rw [Function.iterate_one] at hnotW
        exact hnotW hFzW
    exact Work.FBif.norm_pullRev_const_le (hratio z) hκ hcond hIH

/-- **The target lemma.**  Under the dilatation bound `‖∂F‖ ≤ κ ‖∂̄F‖`, with `0 ≤ κ`, and the
hypothesis that every point with `∂F ≠ 0` already maps into the conformal region `W`, the
invariant coefficient `glueMuW F W` is everywhere bounded by `κ`. -/
theorem norm_glueMuW_le {F : ℂ → ℂ} {W : Set ℂ} {κ : ℝ}
    (hratio : ∀ z : ℂ, ‖Work.MRMT.dz F z‖ ≤ κ * ‖Work.MRMT.dzbar F z‖)
    (hκ : 0 ≤ κ)
    (hone : ∀ z : ℂ, Work.MRMT.dz F z ≠ 0 → F z ∈ W) :
    ∀ z : ℂ, ‖Work.NAKANE2.glueMuW F W z‖ ≤ κ := by
  classical
  intro z
  by_cases hz : ∃ n : ℕ, (F^[n]) z ∈ W
  · rw [Work.NAKANE2.glueMuW_of_hit hz]
    exact pullIter_norm_le_of_hit hratio hκ hone (Nat.find hz) z
      (fun j hj => Nat.find_min hz hj) (Nat.find_spec hz)
  · rw [Work.NAKANE2.glueMuW_of_not_hit hz, norm_zero]
    exact hκ

end Work.NAKANE2.Surgery
