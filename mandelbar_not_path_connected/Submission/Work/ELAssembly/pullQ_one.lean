import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELPull.nearArcsCover_Q
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Numeric facts about the angle data of the `z₁`-nest

These are the elementary real-arithmetic facts behind `pullQ_one`: the two root angles
`α₁ = 371/1023`, `α₂ = 404/1023`, the nest angles `βₙ = α₁ - (α₁-β₀)/1024ⁿ`,
`βₙ' = α₂ + (β₀'-α₂)/1024ⁿ`, and the action of `θ ↦ 1024θ` on them (`1024·α = α + 371` for
`α = α₁`, `1024·α = α + 404` for `α = α₂`). -/

section Numeric

theorem el_alpha1_pos : (0 : ℝ) < Work.EL.alpha1 := by norm_num [Work.EL.alpha1]

theorem el_alpha2_pos : (0 : ℝ) < Work.EL.alpha2 := by norm_num [Work.EL.alpha2]

theorem el_alpha1_lt_alpha2 : Work.EL.alpha1 < Work.EL.alpha2 := by
  norm_num [Work.EL.alpha1, Work.EL.alpha2]

theorem el_alpha2_lt_one : Work.EL.alpha2 < 1 := by norm_num [Work.EL.alpha2]

theorem dA_pos : (0 : ℝ) < Work.EL.alpha2 - Work.EL.alpha1 := by
  norm_num [Work.EL.alpha1, Work.EL.alpha2]

theorem dA_lt_one : Work.EL.alpha2 - Work.EL.alpha1 < 1 := by
  norm_num [Work.EL.alpha1, Work.EL.alpha2]

theorem mul_1024_alpha1 : (1024 : ℝ) * Work.EL.alpha1 = Work.EL.alpha1 + 371 := by
  norm_num [Work.EL.alpha1]

theorem mul_1024_alpha2 : (1024 : ℝ) * Work.EL.alpha2 = Work.EL.alpha2 + 404 := by
  norm_num [Work.EL.alpha2]

theorem mul_1024_dA :
    (1024 : ℝ) * (Work.EL.alpha2 - Work.EL.alpha1) = Work.EL.alpha2 - Work.EL.alpha1 + 33 := by
  have h1 := mul_1024_alpha1
  have h2 := mul_1024_alpha2
  linarith

theorem mul_1024_bAng'_sub (n : ℕ) :
    (1024 : ℝ) * (Work.ELNest.bAng' (n + 1) - Work.EL.alpha2)
      = Work.ELNest.bAng' n - Work.EL.alpha2 := by
  have h1 := Work.ELNest.bAng'_succ_mul n
  have h2 := mul_1024_alpha2
  linarith

theorem mul_1024_shift (n : ℕ) :
    (1024 : ℝ) * (1 + Work.ELNest.bAng (n + 1) - Work.EL.alpha2)
      = 991 + Work.ELNest.bAng n - Work.EL.alpha2 := by
  have h1 := Work.ELNest.bAng_succ_mul n
  have h2 := mul_1024_alpha2
  linarith

theorem mul_1024_one_sub_dA :
    (1024 : ℝ) * (1 - (Work.EL.alpha2 - Work.EL.alpha1))
      = 991 + Work.EL.alpha1 - Work.EL.alpha2 := by
  have h := mul_1024_dA
  linarith

theorem alpha2_le_bAng' (n : ℕ) : Work.EL.alpha2 ≤ Work.ELNest.bAng' n := by
  simpa [Work.EL.alpha2, Work.ELNest.alpha2] using Work.ELNest.alpha2_le_bAng' n

theorem bAng_le_alpha1 (n : ℕ) : Work.ELNest.bAng n ≤ Work.EL.alpha1 := by
  simpa [Work.EL.alpha1, Work.ELNest.alpha1] using Work.ELNest.bAng_le_alpha1 n

theorem bAng'_le_beta0' (n : ℕ) : Work.ELNest.bAng' n ≤ Work.ELNest.beta0' :=
  Work.ELNest.bAng'_le_beta0' n

theorem beta0'_lt_one : Work.ELNest.beta0' < 1 := by norm_num [Work.ELNest.beta0']

theorem bAng_lt_bAng' (n : ℕ) : Work.ELNest.bAng n < Work.ELNest.bAng' n := by
  have h1 := bAng_le_alpha1 n
  have h2 := alpha2_le_bAng' n
  have h3 := el_alpha1_lt_alpha2
  linarith

theorem bAng'_sub_bAng_pos (n : ℕ) : (0 : ℝ) < Work.ELNest.bAng' n - Work.ELNest.bAng n := by
  have h := bAng_lt_bAng' n
  linarith

theorem bAng'_sub_bAng_lt_one (n : ℕ) : Work.ELNest.bAng' n - Work.ELNest.bAng n < 1 := by
  have h1 := Work.ELNest.bAng'_lt_one n
  have h2 := Work.ELNest.bAng_pos n
  linarith

theorem bAng'_sub_alpha2_lt_one (n : ℕ) : Work.ELNest.bAng' n - Work.EL.alpha2 < 1 := by
  have h1 := Work.ELNest.bAng'_lt_one n
  have h2 := el_alpha2_pos
  linarith

theorem beta0'_sub_alpha2 : Work.ELNest.beta0' - Work.EL.alpha2 = 417 / 1047552 := by
  norm_num [Work.ELNest.beta0', Work.EL.alpha2]

end Numeric

/-! ## The coordinate of a point of a near arc -/

/-- **The `α₂`-coordinate of a point of the near arcs of the level-`(n+1)` polygon which
`T^[10]`-lands on the near arc `[α₂, βₙ']` of the level-`n` polygon.**  If `z` lies in the two
(near) arcs of `[P₀, Qp (n+1)]` complementary to the closed far arcs `[α₁,α₂]` and
`[β'_{n+1}, β_{n+1}+1]`, and `T^[10] z ≡ m (mod 1)` with `m` in the near arc `[α₂, βₙ']`, then the
fractional part `u = fract (z - α₂)` satisfies `0 < u`, `1024 u < βₙ' - α₂`, and
`T^[10] z = α₂ + 1024 u`.

Indeed `T^[10] z = fract (1024 z) = fract (α₂ + 1024 u)` because `1024 α₂ = α₂ + 404`; the arc
conditions force `u` into one of the two intervals `(0, β'_{n+1}-α₂)` and
`(1 - (β'_{n+1}-β_{n+1}) + (β'_{n+1}-α₂), 1 - (α₂-α₁))`, and the second one is excluded by the
congruence `T^[10] z ≡ m`: it would give `fract (α₂ + 1024 u) = α₂ + 1024 u - 991 ∈ (βₙ, α₁)`
while `1024 u - 991 - fract (m - α₂) = ⌊m - α₂⌋ + k ∈ ℤ` lies strictly between `-1` and `0`. -/
theorem nearArc_coord (n : ℕ) (m z : ℝ)
    (hm : Work.EL.InClosedArc m Work.EL.alpha2 (Work.ELNest.bAng' n))
    (hz : ¬ Work.EL.InClosedArc z (Work.ELNest.bAng' (n + 1)) (Work.ELNest.bAng (n + 1) + 1))
    (hz' : ¬ Work.EL.InClosedArc z Work.EL.alpha1 Work.EL.alpha2)
    (hzk : ∃ k : ℤ, (Work.EL.T)^[10] z = m + k) :
    0 < Int.fract (z - Work.EL.alpha2) ∧
      (1024 : ℝ) * Int.fract (z - Work.EL.alpha2) < Work.ELNest.bAng' n - Work.EL.alpha2 ∧
      (Work.EL.T)^[10] z = Work.EL.alpha2 + 1024 * Int.fract (z - Work.EL.alpha2) := by
  -- ### Step 1: `z` is in one of the two near arcs.
  -- the first near arc: `fract (z - α₁) ∈ (α₂-α₁, 1)`, whence `u = fract (z - α₂) ∈ (0, 1-...]`
  have harc1 : Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2
      = Work.EL.alpha2 - Work.EL.alpha1 := by
    rw [Work.EL.arcLen]
    exact Int.fract_eq_self.mpr ⟨le_of_lt dA_pos, dA_lt_one⟩
  have hv_gt : Work.EL.alpha2 - Work.EL.alpha1 < Int.fract (z - Work.EL.alpha1) := by
    have h := hz'
    rw [Work.EL.InClosedArc, harc1] at h
    exact not_le.mp (fun hle => h ⟨Int.fract_nonneg _, hle⟩)
  have hv_lt_one : Int.fract (z - Work.EL.alpha1) < 1 := Int.fract_lt_one _
  have huv : Int.fract (z - Work.EL.alpha2)
      = Int.fract (z - Work.EL.alpha1) - (Work.EL.alpha2 - Work.EL.alpha1) := by
    have h1 : Int.fract (Int.fract (z - Work.EL.alpha1) - (Work.EL.alpha2 - Work.EL.alpha1))
        = Int.fract (z - Work.EL.alpha2) := by
      rw [Int.fract_fract_sub (z - Work.EL.alpha1) (Work.EL.alpha2 - Work.EL.alpha1)]
      congr 1
      ring
    rw [h1.symm, Int.fract_eq_self.mpr ⟨by linarith, by linarith [dA_pos]⟩]
  have hu_pos : 0 < Int.fract (z - Work.EL.alpha2) := by rw [huv]; linarith
  have hu_lt : Int.fract (z - Work.EL.alpha2) < 1 - (Work.EL.alpha2 - Work.EL.alpha1) := by
    rw [huv]; linarith
  -- the second far arc: `fract (z - β'_{n+1}) ∈ (1 - h, 1)` with `h = β'_{n+1} - β_{n+1}`
  have harc2 : Work.EL.arcLen (Work.ELNest.bAng' (n + 1)) (Work.ELNest.bAng (n + 1) + 1)
      = 1 - (Work.ELNest.bAng' (n + 1) - Work.ELNest.bAng (n + 1)) := by
    rw [Work.EL.arcLen]
    have h : Work.ELNest.bAng (n + 1) + 1 - Work.ELNest.bAng' (n + 1)
        = 1 - (Work.ELNest.bAng' (n + 1) - Work.ELNest.bAng (n + 1)) := by ring
    rw [h]
    exact Int.fract_eq_self.mpr
      ⟨by linarith [bAng'_sub_bAng_lt_one (n + 1)],
       by linarith [bAng'_sub_bAng_pos (n + 1)]⟩
  have hw_gt : 1 - (Work.ELNest.bAng' (n + 1) - Work.ELNest.bAng (n + 1))
      < Int.fract (z - Work.ELNest.bAng' (n + 1)) := by
    have h := hz
    rw [Work.EL.InClosedArc, harc2] at h
    exact not_le.mp (fun hle => h ⟨Int.fract_nonneg _, hle⟩)
  have hw_lt_one : Int.fract (z - Work.ELNest.bAng' (n + 1)) < 1 := Int.fract_lt_one _
  have huw : Int.fract (z - Work.EL.alpha2)
      = Int.fract (Int.fract (z - Work.ELNest.bAng' (n + 1))
          + (Work.ELNest.bAng' (n + 1) - Work.EL.alpha2)) := by
    have h1 : Int.fract (Int.fract (z - Work.ELNest.bAng' (n + 1))
          + (Work.ELNest.bAng' (n + 1) - Work.EL.alpha2))
        = Int.fract (z - Work.EL.alpha2) := by
      rw [Int.fract_fract_add (z - Work.ELNest.bAng' (n + 1)) (Work.ELNest.bAng' (n + 1) - Work.EL.alpha2)]
      congr 1
      ring
    exact h1.symm
  -- ### Step 2: the dichotomy
  have hsplit : Int.fract (z - Work.EL.alpha2) < Work.ELNest.bAng' (n + 1) - Work.EL.alpha2 ∨
      1 + Work.ELNest.bAng (n + 1) - Work.EL.alpha2 < Int.fract (z - Work.EL.alpha2) := by
    set W := Int.fract (z - Work.ELNest.bAng' (n + 1))
      + (Work.ELNest.bAng' (n + 1) - Work.EL.alpha2) with hW
    have hWlt : W < 1 + (Work.ELNest.bAng' (n + 1) - Work.EL.alpha2) := by
      rw [hW]; linarith
    have hWgt : 1 + Work.ELNest.bAng (n + 1) - Work.EL.alpha2 < W := by
      rw [hW]
      have : 1 - (Work.ELNest.bAng' (n + 1) - Work.ELNest.bAng (n + 1))
          + (Work.ELNest.bAng' (n + 1) - Work.EL.alpha2)
          = 1 + Work.ELNest.bAng (n + 1) - Work.EL.alpha2 := by ring
      linarith
    have hWpos : (0 : ℝ) < 1 + Work.ELNest.bAng (n + 1) - Work.EL.alpha2 := by
      linarith [Work.ELNest.bAng_pos (n + 1), el_alpha2_lt_one]
    have hg_lt : Work.ELNest.bAng' (n + 1) - Work.EL.alpha2 < 1 :=
      bAng'_sub_alpha2_lt_one (n + 1)
    by_cases hW1 : W < 1
    · right
      have hf : Int.fract W = W := Int.fract_eq_self.mpr ⟨by linarith, hW1⟩
      rw [huw, hf]
      linarith
    · left
      have hge : 1 ≤ W := not_lt.mp hW1
      have hf : Int.fract W = W - 1 :=
        Int.fract_eq_iff.mpr ⟨by linarith, by linarith, ⟨1, by push_cast; ring⟩⟩
      rw [huw, hf]
      linarith
  -- ### Step 3: `T^[10] z = fract (α₂ + 1024 u)`
  have hfract1024 : Int.fract (1024 * z)
      = Int.fract (Work.EL.alpha2 + 1024 * Int.fract (z - Work.EL.alpha2)) := by
    apply Int.fract_eq_fract.mpr
    refine ⟨404 + 1024 * ⌊z - Work.EL.alpha2⌋, ?_⟩
    have h2 := mul_1024_alpha2
    have h3 := Int.fract_add_floor (z - Work.EL.alpha2)
    push_cast
    linarith
  rcases hsplit with hcaseA | hcaseB
  · -- ### Step 4a: the first near arc
    have h1024 : (1024 : ℝ) * Int.fract (z - Work.EL.alpha2)
        < Work.ELNest.bAng' n - Work.EL.alpha2 := by
      have h1 : (1024 : ℝ) * Int.fract (z - Work.EL.alpha2)
          < 1024 * (Work.ELNest.bAng' (n + 1) - Work.EL.alpha2) := by linarith
      rwa [mul_1024_bAng'_sub n] at h1
    have hT : (Work.EL.T)^[10] z
        = Work.EL.alpha2 + 1024 * Int.fract (z - Work.EL.alpha2) := by
      rw [Work.ELNest.T_iterate_ten, hfract1024]
      exact Int.fract_eq_self.mpr
        ⟨by linarith [el_alpha2_pos, hu_pos],
         by linarith [h1024, Work.ELNest.bAng'_lt_one n]⟩
    exact ⟨hu_pos, h1024, hT⟩
  · -- ### Step 4b: the second near arc is impossible
    exfalso
    have h1024lo : 991 + Work.ELNest.bAng n - Work.EL.alpha2
        < (1024 : ℝ) * Int.fract (z - Work.EL.alpha2) := by
      have h := mul_1024_shift n
      have h' : (1024 : ℝ) * (1 + Work.ELNest.bAng (n + 1) - Work.EL.alpha2)
          < 1024 * Int.fract (z - Work.EL.alpha2) := by linarith
      linarith
    have h1024hi : (1024 : ℝ) * Int.fract (z - Work.EL.alpha2)
        < 991 + Work.EL.alpha1 - Work.EL.alpha2 := by
      have h := mul_1024_one_sub_dA
      have h' : (1024 : ℝ) * Int.fract (z - Work.EL.alpha2)
          < 1024 * (1 - (Work.EL.alpha2 - Work.EL.alpha1)) := by linarith
      linarith
    have hTz : (Work.EL.T)^[10] z
        = Work.EL.alpha2 + 1024 * Int.fract (z - Work.EL.alpha2) - 991 := by
      rw [Work.ELNest.T_iterate_ten, hfract1024]
      exact Int.fract_eq_iff.mpr
        ⟨by linarith [Work.ELNest.bAng_pos n],
         by linarith [h1024hi, el_alpha1_lt_alpha2, el_alpha2_lt_one],
         ⟨991, by push_cast; ring⟩⟩
    obtain ⟨k, hk⟩ := hzk
    -- `m = α₂ + ε + ⌊m - α₂⌋`
    have harcn : Work.EL.arcLen Work.EL.alpha2 (Work.ELNest.bAng' n)
        = Work.ELNest.bAng' n - Work.EL.alpha2 := by
      rw [Work.EL.arcLen]
      exact Int.fract_eq_self.mpr
        ⟨by linarith [alpha2_le_bAng' n], bAng'_sub_alpha2_lt_one n⟩
    set eps := Int.fract (m - Work.EL.alpha2) with heps
    set j := ⌊m - Work.EL.alpha2⌋ with hj
    have heps_le : eps ≤ Work.ELNest.beta0' - Work.EL.alpha2 := by
      have h := hm
      rw [Work.EL.InClosedArc, harcn] at h
      have hb := bAng'_le_beta0' n
      have : eps ≤ Work.ELNest.bAng' n - Work.EL.alpha2 := by rw [heps]; exact h.2
      linarith
    have heps_nonneg : 0 ≤ eps := by rw [heps]; exact Int.fract_nonneg _
    have hmdec : m = Work.EL.alpha2 + eps + (j : ℝ) := by
      have h := Int.fract_add_floor (m - Work.EL.alpha2)
      rw [← heps, ← hj] at h
      linarith
    have hkey : ((j + k : ℤ) : ℝ)
        = 1024 * Int.fract (z - Work.EL.alpha2) - 991 - eps := by
      have h1 : m + k = Work.EL.alpha2 + 1024 * Int.fract (z - Work.EL.alpha2) - 991 := by
        rw [← hk]; exact hTz
      rw [hmdec] at h1
      push_cast
      linarith
    have hlower : (-1 : ℝ) < ((j + k : ℤ) : ℝ) := by
      have h3 := Work.ELNest.bAng_pos n
      have h4 := beta0'_lt_one
      linarith [hkey, h1024lo, heps_le]
    have hupper : ((j + k : ℤ) : ℝ) < 0 := by
      have h4 := el_alpha1_lt_alpha2
      linarith [hkey, h1024hi, heps_nonneg]
    have h0 : (0 : ℤ) ≤ j + k := by
      have : (-1 : ℤ) < j + k := by exact_mod_cast hlower
      omega
    have hneg : j + k < 0 := by exact_mod_cast hupper
    omega


/-- **At most one pre-image angle of a point of the middle near arc.**  `m` is a point of the
closed near arc `[α₂, βₙ']` of the level-`n` polygon `[P₀, Qp n]` (`Work.EL.midNear` of the
polygon has this form; `hm2` excludes its left end).  If `x` and `y` both lie in the near arcs of
the level-`(n+1)` polygon (i.e. outside its two closed far arcs) and
`T^[10] x ≡ T^[10] y ≡ m  (mod 1)`, then `x ≡ y (mod 1)`.  Reason: `T^[10]` restricted to each
near arc of the level-`(n+1)` polygon is the `1024`-fold dilation onto the corresponding near arc
of the level-`n` polygon, and each source near arc has length `< 1/1024`. -/
theorem pullQ_one (n : ℕ) (m x y : ℝ)
    (hm : Work.EL.InClosedArc m Work.ELNest.alpha2 (Work.ELNest.bAng' n))
    (hm2 : m ≠ Work.ELNest.alpha2)
    (hx : ¬ Work.EL.InClosedArc x (Work.ELNest.bAng' (n + 1)) (Work.ELNest.bAng (n + 1) + 1))
    (hx' : ¬ Work.EL.InClosedArc x Work.EL.alpha1 Work.EL.alpha2)
    (hy : ¬ Work.EL.InClosedArc y (Work.ELNest.bAng' (n + 1)) (Work.ELNest.bAng (n + 1) + 1))
    (hy' : ¬ Work.EL.InClosedArc y Work.EL.alpha1 Work.EL.alpha2)
    (hxk : ∃ k : ℤ, (Work.EL.T)^[10] x = m + k)
    (hyk : ∃ k : ℤ, (Work.EL.T)^[10] y = m + k) :
    ∃ k : ℤ, x = y + k := by
  obtain ⟨kx, hkx⟩ := hxk
  obtain ⟨ky, hky⟩ := hyk
  obtain ⟨hxu_pos, hxu_lt, hxT⟩ := nearArc_coord n m x hm hx hx' ⟨kx, hkx⟩
  obtain ⟨hyu_pos, hyu_lt, hyT⟩ := nearArc_coord n m y hm hy hy' ⟨ky, hky⟩
  -- the two `α₂`-coordinates differ by an integer, and `1024` times their difference is an integer
  have hdiff : (1024 : ℝ) * (Int.fract (x - Work.EL.alpha2) - Int.fract (y - Work.EL.alpha2))
      = ((kx - ky : ℤ) : ℝ) := by
    have h1 : (Work.EL.T)^[10] x - (Work.EL.T)^[10] y = ((kx - ky : ℤ) : ℝ) := by
      rw [hkx, hky]; push_cast; ring
    linarith [hxT, hyT, h1]
  have hbound : |((kx - ky : ℤ) : ℝ)| < 1 := by
    have hd : ((kx - ky : ℤ) : ℝ)
        = 1024 * Int.fract (x - Work.EL.alpha2) - 1024 * Int.fract (y - Work.EL.alpha2) := by
      linarith [hdiff]
    rw [hd, abs_lt]
    have h5 := bAng'_sub_alpha2_lt_one n
    have h3 : (0 : ℝ) ≤ 1024 * Int.fract (x - Work.EL.alpha2) := by linarith [hxu_pos]
    have h4 : (0 : ℝ) ≤ 1024 * Int.fract (y - Work.EL.alpha2) := by linarith [hyu_pos]
    constructor <;> linarith [hxu_lt, hyu_lt, h3, h4, h5]
  have hzero : kx - ky = 0 := by
    have h2 : ((|kx - ky| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact hbound
    have h3 : (|kx - ky| : ℤ) < 1 := by exact_mod_cast h2
    have h4 : (|kx - ky| : ℤ) = 0 := by
      have := abs_nonneg (kx - ky); omega
    exact abs_eq_zero.mp h4
  have huxy : Int.fract (x - Work.EL.alpha2) = Int.fract (y - Work.EL.alpha2) := by
    rw [show (kx - ky : ℤ) = 0 from hzero] at hdiff
    push_cast at hdiff
    linarith
  obtain ⟨k, hk⟩ := Int.fract_eq_fract.mp huxy
  exact ⟨k, by linarith⟩

end Work.ELAssembly
