import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELNest.armChain_nest
import Submission.Work.ELPull.nearArcsCover_Delta
import Submission.Work.ELAssembly.pullD_arc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unusedTactic false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The near arc `[armA2 n, armB1 n]` of the `b₂`-nest

The near arc of the level-`n` `b₂`-polygon which follows the first pair `Za n = (armA1 n, armA2 n)`
is `[armA2 n, armB1 n]`: both ends are the affine functions

`armA2 n = 25/63 - (41/21483)·64⁻ⁿ`,  `armB1 n = 25/63 + (1156/21483)·64⁻ⁿ`

of `y = 64⁻ⁿ` (`Work.ELNest.armChain_nest`), so the arc has length `(1197/21483)·64⁻ⁿ` and is
centred at the tripod angle `25/63`.  The two lemmas below record its length and the resulting
position of a point of the arc. -/

/-- **The length of the level-`n` near arc `[armA2 n, armB1 n]`** is `(1197/21483)·64⁻ⁿ`. -/
lemma arcLen_A2B1 (n : ℕ) :
    Work.EL.arcLen (Work.ELNest.armA2 n) (Work.ELNest.armB1 n)
      = (1197 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ := by
  rw [Work.EL.arcLen, Work.ELNest.armA2_closed n, Work.ELNest.armB1_closed n,
    show ((25 : ℝ) / 63 + (1156 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹)
        - ((25 : ℝ) / 63 - (41 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹)
        = (1197 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ from by ring]
  refine Int.fract_eq_self.mpr ⟨by positivity, ?_⟩
  nlinarith [inv_pow_64_le_one n]

/-- **The position of a point of the near arc.**  If `m` lies in the level-`n` near arc
`[armA2 n, armB1 n]`, then its `22/63`-coordinate `Int.fract (m - 22/63)` satisfies
`1/21 - 41/21483 ≤ Int.fract (m - 22/63) ≤ 1/21 + 1156/21483`: the arc is the tripod angle
`25/63 = 22/63 + 1/21` plus a deviation of at most `1156/21483` (`≤ 1/2`), and it does not wrap. -/
lemma fract_mem_A2B1 (n : ℕ) (m : ℝ)
    (hm : Work.EL.InClosedArc m (Work.ELNest.armA2 n) (Work.ELNest.armB1 n)) :
    (1 : ℝ) / 21 - (41 : ℝ) / 21483 ≤ Int.fract (m - (22 : ℝ) / 63) ∧
      Int.fract (m - (22 : ℝ) / 63) ≤ (1 : ℝ) / 21 + (1156 : ℝ) / 21483 := by
  set Y : ℝ := ((64 : ℝ) ^ n)⁻¹ with hYdef
  have hY0 : 0 < Y := by rw [hYdef]; positivity
  have hY1 : Y ≤ 1 := by rw [hYdef]; exact inv_pow_64_le_one n
  have hA2 : Work.ELNest.armA2 n = (25 : ℝ) / 63 - (41 : ℝ) / 21483 * Y := by
    rw [Work.ELNest.armA2_closed n, hYdef]
  have hlen : Work.EL.arcLen (Work.ELNest.armA2 n) (Work.ELNest.armB1 n)
      = (1197 : ℝ) / 21483 * Y := by rw [arcLen_A2B1 n, hYdef]
  have he0 : 0 ≤ Int.fract (m - Work.ELNest.armA2 n) := Int.fract_nonneg _
  have he1 : Int.fract (m - Work.ELNest.armA2 n) ≤ (1197 : ℝ) / 21483 * Y := by
    have h := hm.2
    rwa [hlen] at h
  have hdec : Int.fract (m - (22 : ℝ) / 63)
      = Int.fract ((1 : ℝ) / 21 - (41 : ℝ) / 21483 * Y
          + Int.fract (m - Work.ELNest.armA2 n)) := by
    rw [Int.fract_eq_fract]
    refine ⟨⌊m - Work.ELNest.armA2 n⌋, ?_⟩
    have hfl := Int.floor_add_fract (m - Work.ELNest.armA2 n)
    push_cast
    linarith [hfl, hA2]
  constructor
  · rw [hdec, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    nlinarith
  · rw [hdec, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    nlinarith

/-! ## The location of a point given by its near arcs

The next lemma is the `u`-coordinate form of `Work.ELAssembly.pullD_arc`: with
`u = Int.fract (z - 22/63)`, a point `z` outside the three closed far arcs of the level-`(n+1)`
polygon lies in one of the four intervals

* `(0, 289/21483 · y)`:                  the near arc `G_CA` through `1` (low part),
* `(1/21 - 41/21483 · y, 1/21 + 1156/21483 · y)`:   the near arc `G_AB` at `25/63`,
* `(5/21 - 164/21483 · y, 5/21 + 4624/21483 · y)`:  the near arc `G_BC` at `37/63`,
* `(1 - 656/21483 · y, 1)`:              the near arc `G_CA` (high part),

where `y = 64⁻⁽ⁿ⁺¹⁾`.  This is `hdisj` of `pullD_arc` extracted as a statement. -/
lemma u_loc (n : ℕ) (y z : ℝ) (hy : y = ((64 : ℝ) ^ (n + 1))⁻¹)
    (hA : ¬ Work.EL.InClosedArc z (Work.ELNest.armA1 (n + 1)) (Work.ELNest.armA2 (n + 1)))
    (hB : ¬ Work.EL.InClosedArc z (Work.ELNest.armB1 (n + 1)) (Work.ELNest.armB2 (n + 1)))
    (hC : ¬ Work.EL.InClosedArc z (Work.ELNest.armC1 (n + 1)) (Work.ELNest.armC2 (n + 1) + 1)) :
    Int.fract (z - (22 : ℝ) / 63) < (289 : ℝ) / 21483 * y ∨
      ((1 : ℝ) / 21 - (41 : ℝ) / 21483 * y < Int.fract (z - (22 : ℝ) / 63) ∧
        Int.fract (z - (22 : ℝ) / 63) < (1 : ℝ) / 21 + (1156 : ℝ) / 21483 * y) ∨
      ((5 : ℝ) / 21 - (164 : ℝ) / 21483 * y < Int.fract (z - (22 : ℝ) / 63) ∧
        Int.fract (z - (22 : ℝ) / 63) < (5 : ℝ) / 21 + (4624 : ℝ) / 21483 * y) ∨
      (1 - (656 : ℝ) / 21483 * y < Int.fract (z - (22 : ℝ) / 63)) := by
  set u : ℝ := Int.fract (z - (22 : ℝ) / 63) with hudef
  have hy1 : y ≤ 1 := by rw [hy]; exact inv_pow_64_le_one (n + 1)
  have hy0 : 0 < y := by rw [hy]; positivity
  have hu1 : u < 1 := by rw [hudef]; exact Int.fract_lt_one _
  -- the six source angles
  have hA1s : Work.ELNest.armA1 (n + 1) = (22 : ℝ) / 63 + ((289 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armA1_closed (n + 1), hy]
  have hA2s : Work.ELNest.armA2 (n + 1) = (25 : ℝ) / 63 - ((41 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armA2_closed (n + 1), hy]
  have hB1s : Work.ELNest.armB1 (n + 1) = (25 : ℝ) / 63 + ((1156 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armB1_closed (n + 1), hy]
  have hB2s : Work.ELNest.armB2 (n + 1) = (37 : ℝ) / 63 - ((164 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armB2_closed (n + 1), hy]
  have hC1s : Work.ELNest.armC1 (n + 1) = (37 : ℝ) / 63 + ((4624 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armC1_closed (n + 1), hy]
  have hC2s : Work.ELNest.armC2 (n + 1) = (22 : ℝ) / 63 - ((656 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armC2_closed (n + 1), hy]
  -- the three source arc lengths
  have hlenA : Work.EL.arcLen (Work.ELNest.armA1 (n + 1)) (Work.ELNest.armA2 (n + 1))
      = (1 : ℝ) / 21 - ((330 : ℝ) / 21483 * y) := by
    rw [Work.EL.arcLen, hA1s, hA2s,
      show ((25 : ℝ) / 63 - (41 : ℝ) / 21483 * y) - ((22 : ℝ) / 63 + (289 : ℝ) / 21483 * y)
        = (1 : ℝ) / 21 - (330 : ℝ) / 21483 * y from by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hlenB : Work.EL.arcLen (Work.ELNest.armB1 (n + 1)) (Work.ELNest.armB2 (n + 1))
      = (4 : ℝ) / 21 - ((1320 : ℝ) / 21483 * y) := by
    rw [Work.EL.arcLen, hB1s, hB2s,
      show ((37 : ℝ) / 63 - (164 : ℝ) / 21483 * y) - ((25 : ℝ) / 63 + (1156 : ℝ) / 21483 * y)
        = (4 : ℝ) / 21 - (1320 : ℝ) / 21483 * y from by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hlenC : Work.EL.arcLen (Work.ELNest.armC1 (n + 1)) (Work.ELNest.armC2 (n + 1) + 1)
      = (16 : ℝ) / 21 - ((5280 : ℝ) / 21483 * y) := by
    rw [Work.EL.arcLen, hC1s, hC2s,
      show ((22 : ℝ) / 63 - (656 : ℝ) / 21483 * y) + 1 - ((37 : ℝ) / 63 + (4624 : ℝ) / 21483 * y)
        = (16 : ℝ) / 21 - (5280 : ℝ) / 21483 * y from by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  -- the three hypotheses, in the coordinate `u`
  have hAu : Int.fract (u - ((289 : ℝ) / 21483 * y))
      > (1 : ℝ) / 21 - ((330 : ℝ) / 21483 * y) := by
    have h := arcLen_lt_fract_of_not_InClosedArc hA
    rw [hlenA, hA1s] at h
    have hx := fract_sub_A z u ((289 : ℝ) / 21483 * y) hudef
    rw [hx] at h
    linarith
  have hBu : Int.fract (u - ((1 : ℝ) / 21 + (1156 : ℝ) / 21483 * y))
      > (4 : ℝ) / 21 - ((1320 : ℝ) / 21483 * y) := by
    have h := arcLen_lt_fract_of_not_InClosedArc hB
    rw [hlenB, hB1s] at h
    have hx := fract_sub_B z u ((1156 : ℝ) / 21483 * y) hudef
    rw [hx] at h
    linarith
  have hCu : Int.fract (u - ((5 : ℝ) / 21 + (4624 : ℝ) / 21483 * y))
      > (16 : ℝ) / 21 - ((5280 : ℝ) / 21483 * y) := by
    have h := arcLen_lt_fract_of_not_InClosedArc hC
    rw [hlenC, hC1s] at h
    have hx := fract_sub_C z u ((4624 : ℝ) / 21483 * y) hudef
    rw [hx] at h
    linarith
  -- the coordinate `u` lies in one of the four intervals
  have h1 : u < (289 : ℝ) / 21483 * y ∨ (1 : ℝ) / 21 - (41 : ℝ) / 21483 * y < u := by
    by_cases h : u < (289 : ℝ) / 21483 * y
    · exact Or.inl h
    · refine Or.inr ?_
      push_neg at h
      have hf : Int.fract (u - (289 : ℝ) / 21483 * y) = u - (289 : ℝ) / 21483 * y :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [hf] at hAu
      linarith
  have h2 : u < (1 : ℝ) / 21 + (1156 : ℝ) / 21483 * y ∨
      (5 : ℝ) / 21 - (164 : ℝ) / 21483 * y < u := by
    by_cases h : u < (1 : ℝ) / 21 + (1156 : ℝ) / 21483 * y
    · exact Or.inl h
    · refine Or.inr ?_
      push_neg at h
      have hf : Int.fract (u - ((1 : ℝ) / 21 + (1156 : ℝ) / 21483 * y))
          = u - ((1 : ℝ) / 21 + (1156 : ℝ) / 21483 * y) :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [hf] at hBu
      linarith
  have h3 : u < (5 : ℝ) / 21 + (4624 : ℝ) / 21483 * y ∨ 1 - (656 : ℝ) / 21483 * y < u := by
    by_cases h : u < (5 : ℝ) / 21 + (4624 : ℝ) / 21483 * y
    · exact Or.inl h
    · refine Or.inr ?_
      push_neg at h
      have hf : Int.fract (u - ((5 : ℝ) / 21 + (4624 : ℝ) / 21483 * y))
          = u - ((5 : ℝ) / 21 + (4624 : ℝ) / 21483 * y) :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [hf] at hCu
      linarith
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · rcases h2 with h2 | h2
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · rcases h3 with h3 | h3
      · exact Or.inr (Or.inr (Or.inl ⟨h2, h3⟩))
      · exact Or.inr (Or.inr (Or.inr h3))

/-! ## The pre-image angle is determined by the image, in a near arc

`Work.EL.T^[6] = θ ↦ Int.fract (64 θ)`, and in the coordinate `u = Int.fract (z - 22/63)` the
three tripod angles `22/63, 25/63, 37/63` satisfy `64 p = p + k_p` with `k_p = 22, 25, 37 ∈ ℤ`;
this is why `Int.fract (T^[6] z - 22/63) = Int.fract (64 u)`.  Since the near arc `[armA2 n,
armB1 n]` around `25/63` is the image of the near arc `G_AB` of the level-`(n+1)` polygon only
(and not of the two other near arcs `G_BC` at `37/63` and `G_CA` at `22/63`), and since `64`
dilates `G_AB` by exactly `64`, the coordinate `u` is determined. -/
lemma u_determined (n : ℕ) (m z : ℝ)
    (hm : Work.EL.InClosedArc m (Work.ELNest.armA2 n) (Work.ELNest.armB1 n))
    (hzA : ¬ Work.EL.InClosedArc z (Work.ELNest.armA1 (n + 1)) (Work.ELNest.armA2 (n + 1)))
    (hzB : ¬ Work.EL.InClosedArc z (Work.ELNest.armB1 (n + 1)) (Work.ELNest.armB2 (n + 1)))
    (hzC : ¬ Work.EL.InClosedArc z (Work.ELNest.armC1 (n + 1)) (Work.ELNest.armC2 (n + 1) + 1))
    (hzk : ∃ k : ℤ, (Work.EL.T)^[6] z = m + k) :
    Int.fract (z - (22 : ℝ) / 63) = (Int.fract (m - (22 : ℝ) / 63) + 3) / 64 := by
  set u : ℝ := Int.fract (z - (22 : ℝ) / 63) with hudef
  set Y : ℝ := ((64 : ℝ) ^ n)⁻¹ with hYdef
  set y : ℝ := ((64 : ℝ) ^ (n + 1))⁻¹ with hydef
  have hyY : Y = 64 * y := by rw [hYdef, hydef, Work.ELNest.inv_pow_succ_64 n]; ring
  have hY0 : 0 < Y := by rw [hYdef]; positivity
  have hY1 : Y ≤ 1 := by rw [hYdef]; exact inv_pow_64_le_one n
  have hu0 : 0 ≤ u := by rw [hudef]; exact Int.fract_nonneg _
  have hu1 : u < 1 := by rw [hudef]; exact Int.fract_lt_one _
  obtain ⟨hwlo, hwhi⟩ := fract_mem_A2B1 n m hm
  -- `w = Int.fract (m - 22/63)` equals `Int.fract (64 u)`
  have hw64 : Int.fract (m - (22 : ℝ) / 63) = Int.fract (64 * u) := by
    obtain ⟨k, hk⟩ := hzk
    have h1 : Int.fract ((Work.EL.T)^[6] z - (22 : ℝ) / 63) = Int.fract (m - (22 : ℝ) / 63) := by
      rw [Int.fract_eq_fract]
      refine ⟨k, ?_⟩
      rw [hk]; push_cast; ring
    rw [← h1, T_iterate_six]
    simpa using fract_pull_A z u 0 hudef
  -- the location of `u`
  have hloc : u < (289 : ℝ) / 21483 * y ∨
      ((1 : ℝ) / 21 - (41 : ℝ) / 21483 * y < u ∧ u < (1 : ℝ) / 21 + (1156 : ℝ) / 21483 * y) ∨
      ((5 : ℝ) / 21 - (164 : ℝ) / 21483 * y < u ∧ u < (5 : ℝ) / 21 + (4624 : ℝ) / 21483 * y) ∨
      (1 - (656 : ℝ) / 21483 * y < u) := u_loc n y z hydef hzA hzB hzC
  rcases hloc with hA | ⟨h1, h2⟩ | ⟨h1, h2⟩ | hD
  · -- `G_CA` (low part): its image lies below `289/21483`, the target arc above `982/21483`
    exfalso
    have h64u : 64 * u < (289 : ℝ) / 21483 := by nlinarith [hA, hyY, hY1]
    have hf : Int.fract (64 * u) = 64 * u := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hw : Int.fract (m - (22 : ℝ) / 63) = 64 * u := by rw [hw64, hf]
    linarith
  · -- `G_AB`: `64 u = 3 + Int.fract (m - 22/63)`
    have h64u1 : (3 : ℝ) < 64 * u := by nlinarith [h1, hyY, hY1]
    have h64u2 : 64 * u < 4 := by nlinarith [h2, hyY, hY1]
    have hf : Int.fract (64 * u) = 64 * u - 3 :=
      fract_eq_sub_of_int (64 * u) 3 (by push_cast; linarith) (by push_cast; linarith)
    have hw : Int.fract (m - (22 : ℝ) / 63) = 64 * u - 3 := by rw [hw64, hf]
    linarith
  · -- `G_BC`: its image lies above `4951/21483`, the target arc below `2179/21483`
    exfalso
    have h64u1 : (15 : ℝ) < 64 * u := by nlinarith [h1, hyY, hY1]
    have h64u2 : 64 * u < 16 := by nlinarith [h2, hyY, hY1]
    have hf : Int.fract (64 * u) = 64 * u - 15 :=
      fract_eq_sub_of_int (64 * u) 15 (by push_cast; linarith) (by push_cast; linarith)
    have hw : Int.fract (m - (22 : ℝ) / 63) = 64 * u - 15 := by rw [hw64, hf]
    linarith
  · -- `G_CA` (high part): its image lies above `20827/21483`, the target arc below `2179/21483`
    exfalso
    have h64u1 : (63 : ℝ) < 64 * u := by nlinarith [hD, hyY, hY1]
    have h64u2 : 64 * u < 64 := by nlinarith [hu1]
    have hf : Int.fract (64 * u) = 64 * u - 63 :=
      fract_eq_sub_of_int (64 * u) 63 (by push_cast; linarith) (by push_cast; linarith)
    have hw : Int.fract (m - (22 : ℝ) / 63) = 64 * u - 63 := by rw [hw64, hf]
    linarith

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`), `open LeanEval.ComplexAnalysis (Tantibar)`.
/-- **At most one pre-image angle of a point of a near arc, for the `b₂`-polygon.**  `m` is a
point of the closed near arc `[armA2 n, armB1 n]` of the level-`n` polygon
`[Za n, Zb n, Zc n]` (`Work.EL.midNear` of that polygon has this form; `hm2` excludes its left
end).  If `x` and `y` lie in the near arcs of the level-`(n+1)` polygon (outside its three closed
far arcs) and `T^[6] x ≡ T^[6] y ≡ m  (mod 1)`, then `x ≡ y (mod 1)`.  Reason: the three near
arcs of `[Za n, Zb n, Zc n]` are pairwise disjoint, `T^[6]` dilates each near arc at level
`n+1` onto the corresponding near arc at level `n`, and each source near arc has length `< 1/64`. -/
theorem pullD_one (n : ℕ) (m x y : ℝ)
    (hm : Work.EL.InClosedArc m (Work.ELNest.armA2 n) (Work.ELNest.armB1 n))
    (hm2 : m ≠ Work.ELNest.armA2 n)
    (hx : ¬ Work.EL.InClosedArc x (Work.ELNest.armA1 (n + 1)) (Work.ELNest.armA2 (n + 1)))
    (hx2 : ¬ Work.EL.InClosedArc x (Work.ELNest.armB1 (n + 1)) (Work.ELNest.armB2 (n + 1)))
    (hx3 : ¬ Work.EL.InClosedArc x (Work.ELNest.armC1 (n + 1)) (Work.ELNest.armC2 (n + 1) + 1))
    (hy : ¬ Work.EL.InClosedArc y (Work.ELNest.armA1 (n + 1)) (Work.ELNest.armA2 (n + 1)))
    (hy2 : ¬ Work.EL.InClosedArc y (Work.ELNest.armB1 (n + 1)) (Work.ELNest.armB2 (n + 1)))
    (hy3 : ¬ Work.EL.InClosedArc y (Work.ELNest.armC1 (n + 1)) (Work.ELNest.armC2 (n + 1) + 1))
    (hxk : ∃ k : ℤ, (Work.EL.T)^[6] x = m + k)
    (hyk : ∃ k : ℤ, (Work.EL.T)^[6] y = m + k) :
    ∃ k : ℤ, x = y + k := by
  have hux := u_determined n m x hm hx hx2 hx3 hxk
  have huy := u_determined n m y hm hy hy2 hy3 hyk
  have hxy : Int.fract (x - (22 : ℝ) / 63) = Int.fract (y - (22 : ℝ) / 63) := by
    rw [hux, huy]
  obtain ⟨k, hk⟩ := Int.fract_eq_fract.mp hxy
  exact ⟨k, by linarith⟩

end Work.ELAssembly
