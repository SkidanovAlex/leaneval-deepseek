/-
# The two eight-wedge families cover the square

The filling disk is the square `Sq = [-1,1]²` with layer parameter `nrm p = ‖p‖∞` and perimeter
parameter `u p` (`Work.Cusp.Basic`, `Work.Cusp.Charts`).  For a shift `c` the `k`-th wedge
`wedgeS c k` is the set of points `p` of the square whose perimeter parameter, measured from the
shifted cut `c`, has fractional part in the open quarter `(k/4, (k+1)/4)`:

`wedgeS c k = {p | 0 < nrm p ∧ Int.fract (u p - c) ∈ (k/4, (k+1)/4)}`.

Each family `⋃ k, wedgeS c k` misses exactly the four directions whose shifted perimeter parameter is
a multiple of `1/4`; shifting by `c = 1/8` moves those missed directions to the *other* four
directions (the half-integer multiples of `1/8`).  The two families therefore cover everything:

`p ≠ 0` lies in `⋃ k wedgeS 0 k ∪ ⋃ k wedgeS (1/8) k`.

The proof is purely arithmetic on `Int.fract`: writing `t = Int.fract (u p) ∈ [0,1)`, we have
`Int.fract (u p - 1/8) = Int.fract (t - 1/8)` (one-periodicity of `fract`), and a case split on the
eighth-intervals containing `t` shows that either `t` or `t - 1/8` (the latter wrapped to
`t + 7/8` when `t < 1/8`) falls in one of the four open quarter intervals.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The arithmetic core.**  For every real `x`, either `Int.fract x` or `Int.fract (x - 1/8)`
lies in one of the four open quarter intervals `(k/4, (k+1)/4)`, `k : Fin 4`.

Writing `t = Int.fract x ∈ [0,1)`: the fractional part of `x - 1/8` is the fractional part of
`t - 1/8` (one-periodicity), which is `t + 7/8` when `t < 1/8` (in `(3/4,1)`) and `t - 1/8`
otherwise (in `[0,7/8)`).  In the latter case the eighth-interval containing `t` determines which of
`t`, `t - 1/8` lands in an open quarter. -/
private lemma quarter_cover (x : ℝ) :
    (∃ k : Fin 4, Int.fract x ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)) ∨
    (∃ k : Fin 4, Int.fract (x - 1/8) ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)) := by
  set t := Int.fract x with ht
  have ht0 : 0 ≤ t := Int.fract_nonneg x
  have ht1 : t < 1 := Int.fract_lt_one x
  have hfract : Int.fract (x - 1/8) = Int.fract (t - 1/8) := by
    rw [Int.fract_eq_fract]
    refine ⟨⌊x⌋, ?_⟩
    have hx : x - t = (⌊x⌋ : ℝ) := by
      rw [ht]; linarith [Int.fract_add_floor x]
    linarith
  rw [hfract]
  by_cases hsmall : t < 1/8
  · -- `t < 1/8`: then `Int.fract (t - 1/8) = t + 7/8 ∈ (3/4, 1)`.
    right
    have hfr : Int.fract (t - 1/8) = t + 7/8 := by
      have h1 : Int.fract (t - 1/8) = Int.fract (t + 7/8) := by
        rw [Int.fract_eq_fract]
        exact ⟨-1, by ring⟩
      rw [h1, Int.fract_eq_self.mpr]
      constructor <;> linarith
    rw [hfr]
    refine ⟨3, ?_⟩
    norm_num
    exact ⟨by linarith, by linarith⟩
  · -- `1/8 ≤ t < 1`: then `Int.fract (t - 1/8) = t - 1/8`, and one of the two lands in a quarter.
    push Not at hsmall
    have hfr : Int.fract (t - 1/8) = t - 1/8 := by
      rw [Int.fract_eq_self.mpr]
      constructor <;> linarith
    rw [hfr]
    rcases lt_or_ge t (1/4) with h | h
    · left; refine ⟨0, ?_⟩; norm_num; exact ⟨by linarith, h⟩
    rcases lt_or_ge t (3/8) with h' | h'
    · right; refine ⟨0, ?_⟩; norm_num; exact ⟨by linarith, by linarith⟩
    rcases lt_or_ge t (1/2) with h'' | h''
    · left; refine ⟨1, ?_⟩; norm_num; exact ⟨by linarith, h''⟩
    rcases lt_or_ge t (5/8) with h3 | h3
    · right; refine ⟨1, ?_⟩; norm_num; exact ⟨by linarith, by linarith⟩
    rcases lt_or_ge t (3/4) with h4 | h4
    · left; refine ⟨2, ?_⟩; norm_num; exact ⟨by linarith, h4⟩
    rcases lt_or_ge t (7/8) with h5 | h5
    · right; refine ⟨2, ?_⟩; norm_num; exact ⟨by linarith, by linarith⟩
    · left; refine ⟨3, ?_⟩; norm_num; exact ⟨by linarith, ht1⟩

theorem wedge_cover (p : E2) (h0 : 0 < nrm p) :
    p ∈ (⋃ k : Fin 4, wedgeS 0 k) ∪ (⋃ k : Fin 4, wedgeS (1/8) k) := by
  rcases quarter_cover (u p) with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    exact Set.mem_iUnion.mpr ⟨k, h0, by simpa using hk⟩
  · right
    exact Set.mem_iUnion.mpr ⟨k, h0, hk⟩

end Work.Cusp
