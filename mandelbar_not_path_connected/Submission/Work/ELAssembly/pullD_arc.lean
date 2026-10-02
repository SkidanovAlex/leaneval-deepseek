/-
# `pullD_arc`: the angle transfer `T^[6]` for the `b₂`-nest

The angle map `Work.EL.T θ = Int.fract (-2θ)` acts on external angles of the antiholomorphic
quadratic family, so `Work.EL.T^[6]` is `θ ↦ Int.fract (64 θ)` (`T_iterate_six`).  The boundary
angles of the level-`n` `b₂`-polygon are the affine functions

* `armA1 n = 22/63 + (289/21483)·64⁻ⁿ`,   `armA2 n = 25/63 − (41/21483)·64⁻ⁿ`,
* `armB1 n = 25/63 + (1156/21483)·64⁻ⁿ`,  `armB2 n = 37/63 − (164/21483)·64⁻ⁿ`,
* `armC1 n = 37/63 + (4624/21483)·64⁻ⁿ`,  `armC2 n = 22/63 − (656/21483)·64⁻ⁿ`

of `y = 64⁻ⁿ` (`Work.ELNest.armChain_nest`), and `T^[6]` carries the level-`(n+1)` angle of each
arm to the level-`n` angle of the same arm (`pullD_pair`).

This file proves the *arc* form: if `x` lies outside the three closed arcs of the level-`(n+1)`
polygon, then `T^[6] x` lies outside the three closed arcs of the level-`n` polygon.

The three closed arcs at level `m` tile the circle up to three tiny gaps

* `G_AB = (25/63 − (41/21483)·64⁻ᵐ, 25/63 + (1156/21483)·64⁻ᵐ)`,
* `G_BC = (37/63 − (164/21483)·64⁻ᵐ, 37/63 + (4624/21483)·64⁻ᵐ)`,
* `G_CA = (22/63 − (656/21483)·64⁻ᵐ, 22/63 + (289/21483)·64⁻ᵐ)   (mod 1, i.e. through `1`),`

each centred at a tripod angle `p ∈ {22/63, 25/63, 37/63}` with `63 p ∈ ℤ`.  Writing
`x = p + δ·64⁻ᵐ` for `x` in such a gap, and using `64·(p + δ·64⁻ᵐ) = p + δ·64⁻⁽ᵐ⁻¹⁾ + 63p`, the
map `T^[6]` sends the level-`(n+1)` gap **onto** the level-`n` gap with the *same* certificate
interval for `δ ∈ ℚ`; this is the rational certificate `Work.ELPull.nearArcsCover_Delta` scaled
by `64ⁿ`.  The proof below runs this argument in the single coordinate

  `u = Int.fract (x - 22/63)`,

in which the three far arcs are the four intervals of `hdisj` and the transfer is the twelve
elementary fractional-part evaluations of `target_conditions`.
-/
import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELAssembly.pullD_pair
import Submission.Work.ELPull.nearArcsCover_Delta
import Submission.Work.ELNest.armChain_nest

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

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Fractional-part bookkeeping -/

/-- Subtracting a constant commutes with taking the fractional part of the integer part:
`Int.fract (Int.fract a - c) = Int.fract (a - c)`. -/
lemma fract_fract_sub (a c : ℝ) : Int.fract (Int.fract a - c) = Int.fract (a - c) := by
  rw [Int.fract_eq_fract]
  refine ⟨-⌊a⌋, ?_⟩
  have h := Int.floor_add_fract a
  push_cast
  linarith

/-- `Int.fract v = v - m` for `v ∈ [m, m + 1)`. -/
lemma fract_eq_sub_of_int (v : ℝ) (m : ℤ) (h1 : (m : ℝ) ≤ v) (h2 : v < (m : ℝ) + 1) :
    Int.fract v = v - (m : ℝ) := by
  rw [Int.fract_eq_iff]
  exact ⟨by linarith, by linarith, ⟨m, by push_cast; ring⟩⟩

/-- **The hypothesis of the transfer**, in raw form: `x` is strictly beyond the end of the closed
arc `[a, b]`, i.e. `arcLen a b < Int.fract (x - a)`. -/
lemma arcLen_lt_fract_of_not_InClosedArc {x a b : ℝ} (h : ¬ Work.EL.InClosedArc x a b) :
    Work.EL.arcLen a b < Int.fract (x - a) := by
  rw [Work.EL.InClosedArc] at h
  push_neg at h
  exact h (Int.fract_nonneg _)

/-- **The conclusion form**: `arcLen a b < Int.fract (y - a)` rules out `InClosedArc y a b`. -/
lemma not_InClosedArc_of_lt_fract {y a b : ℝ} (h : Work.EL.arcLen a b < Int.fract (y - a)) :
    ¬ Work.EL.InClosedArc y a b := by
  intro hc
  rw [Work.EL.InClosedArc] at hc
  linarith [hc.2]

/-! ## The coordinate `u = Int.fract (x - 22/63)`

All boundary angles are of the shape `p + e` with `p ∈ {22/63, 25/63, 37/63} = {22/63, 22/63 +
1/21, 22/63 + 5/21}` the tripod angle and `e` a small multiple of `64⁻ᵐ`; the next two families
of lemmas evaluate `Int.fract (x - (p + e))` resp. `Int.fract (Int.fract (64x) - (p + e))` in
the coordinate `u`, using `x - 22/63 = ⌊x - 22/63⌋ + u`. -/

lemma fract_sub_A (x u e : ℝ) (hu : u = Int.fract (x - (22 : ℝ) / 63)) :
    Int.fract (x - ((22 : ℝ) / 63 + e)) = Int.fract (u - e) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊x - (22 : ℝ) / 63⌋, ?_⟩
  have h := Int.floor_add_fract (x - (22 : ℝ) / 63)
  have h2 : Int.fract (x - (22 : ℝ) / 63) = u := hu.symm
  linarith

lemma fract_sub_B (x u e : ℝ) (hu : u = Int.fract (x - (22 : ℝ) / 63)) :
    Int.fract (x - ((25 : ℝ) / 63 + e)) = Int.fract (u - ((1 : ℝ) / 21 + e)) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊x - (22 : ℝ) / 63⌋, ?_⟩
  have h := Int.floor_add_fract (x - (22 : ℝ) / 63)
  have h2 : Int.fract (x - (22 : ℝ) / 63) = u := hu.symm
  linarith

lemma fract_sub_C (x u e : ℝ) (hu : u = Int.fract (x - (22 : ℝ) / 63)) :
    Int.fract (x - ((37 : ℝ) / 63 + e)) = Int.fract (u - ((5 : ℝ) / 21 + e)) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊x - (22 : ℝ) / 63⌋, ?_⟩
  have h := Int.floor_add_fract (x - (22 : ℝ) / 63)
  have h2 : Int.fract (x - (22 : ℝ) / 63) = u := hu.symm
  linarith

/-- `T^[6]` in the coordinate `u`: `64·(22/63 + δ) = (64·δ) + 22 + 64·⌊x - 22/63⌋`. -/
lemma fract_pull_A (x u e : ℝ) (hu : u = Int.fract (x - (22 : ℝ) / 63)) :
    Int.fract (Int.fract (64 * x) - ((22 : ℝ) / 63 + e)) = Int.fract (64 * u - e) := by
  rw [fract_fract_sub, Int.fract_eq_fract]
  refine ⟨22 + 64 * ⌊x - (22 : ℝ) / 63⌋, ?_⟩
  have h := Int.floor_add_fract (x - (22 : ℝ) / 63)
  have h2 : Int.fract (x - (22 : ℝ) / 63) = u := hu.symm
  push_cast
  linarith

lemma fract_pull_B (x u e : ℝ) (hu : u = Int.fract (x - (22 : ℝ) / 63)) :
    Int.fract (Int.fract (64 * x) - ((25 : ℝ) / 63 + e))
      = Int.fract (64 * u - ((1 : ℝ) / 21 + e)) := by
  rw [fract_fract_sub, Int.fract_eq_fract]
  refine ⟨22 + 64 * ⌊x - (22 : ℝ) / 63⌋, ?_⟩
  have h := Int.floor_add_fract (x - (22 : ℝ) / 63)
  have h2 : Int.fract (x - (22 : ℝ) / 63) = u := hu.symm
  push_cast
  linarith

lemma fract_pull_C (x u e : ℝ) (hu : u = Int.fract (x - (22 : ℝ) / 63)) :
    Int.fract (Int.fract (64 * x) - ((37 : ℝ) / 63 + e))
      = Int.fract (64 * u - ((5 : ℝ) / 21 + e)) := by
  rw [fract_fract_sub, Int.fract_eq_fract]
  refine ⟨22 + 64 * ⌊x - (22 : ℝ) / 63⌋, ?_⟩
  have h := Int.floor_add_fract (x - (22 : ℝ) / 63)
  have h2 : Int.fract (x - (22 : ℝ) / 63) = u := hu.symm
  push_cast
  linarith

/-! ## The four regions of the coordinate `u` and the twelve values of `Int.fract`

The hypotheses say that `u` lies in one of the four intervals

* `(0, 289/21483 · y)`,                                       the gap `G_CA` (low part),
* `(1/21 - 41/21483 · y, 1/21 + 1156/21483 · y)`,             the gap `G_AB`,
* `(5/21 - 164/21483 · y, 5/21 + 4624/21483 · y)`,            the gap `G_BC`,
* `(1 - 656/21483 · y, 1)`,                                   the gap `G_CA` (high part),

where `y = 64^{-(n+1)}`; the conclusion needs the three fractional parts
`Int.fract (64u - c - k·Y)` (with `Y = 64y = 64⁻ⁿ`) to exceed the corresponding level-`n` arc
lengths.  In each region the argument of `Int.fract` runs through an interval of length `< 1`
inside a fixed unit interval `[m, m + 1)`, so `Int.fract` is the argument minus the (explicit)
integer `m = -1, 3, 2, 2, 15, 15, 14` resp. `63`. -/
lemma target_conditions (u Y y : ℝ) (hY : Y = 64 * y) (hY1 : Y ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu : u < (289 : ℝ) / 21483 * y ∨
      ((1 : ℝ) / 21 - (41 : ℝ) / 21483 * y < u ∧ u < (1 : ℝ) / 21 + (1156 : ℝ) / 21483 * y) ∨
      ((5 : ℝ) / 21 - (164 : ℝ) / 21483 * y < u ∧ u < (5 : ℝ) / 21 + (4624 : ℝ) / 21483 * y) ∨
      (1 - (656 : ℝ) / 21483 * y < u)) :
    Int.fract (64 * u - (289 : ℝ) / 21483 * Y) > (1 : ℝ) / 21 - (330 : ℝ) / 21483 * Y ∧
    Int.fract (64 * u - ((1 : ℝ) / 21 + (1156 : ℝ) / 21483 * Y))
      > (4 : ℝ) / 21 - (1320 : ℝ) / 21483 * Y ∧
    Int.fract (64 * u - ((5 : ℝ) / 21 + (4624 : ℝ) / 21483 * Y))
      > (16 : ℝ) / 21 - (5280 : ℝ) / 21483 * Y := by
  rcases hu with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
  · refine ⟨?_, ?_, ?_⟩
    · rw [fract_eq_sub_of_int _ (-1) (by linarith) (by linarith)]; linarith
    · rw [fract_eq_sub_of_int _ (-1) (by linarith) (by linarith)]; linarith
    · rw [fract_eq_sub_of_int _ (-1) (by linarith) (by linarith)]; linarith
  · refine ⟨?_, ?_, ?_⟩
    · rw [fract_eq_sub_of_int _ 3 (by linarith) (by linarith)]; linarith
    · rw [fract_eq_sub_of_int _ 2 (by linarith) (by linarith)]; linarith
    · rw [fract_eq_sub_of_int _ 2 (by linarith) (by linarith)]; linarith
  · refine ⟨?_, ?_, ?_⟩
    · rw [fract_eq_sub_of_int _ 15 (by linarith) (by linarith)]; linarith
    · rw [fract_eq_sub_of_int _ 15 (by linarith) (by linarith)]; linarith
    · rw [fract_eq_sub_of_int _ 14 (by linarith) (by linarith)]; linarith
  · refine ⟨?_, ?_, ?_⟩
    · rw [fract_eq_sub_of_int _ 63 (by linarith) (by linarith)]; linarith
    · rw [fract_eq_sub_of_int _ 63 (by linarith) (by linarith)]; linarith
    · rw [fract_eq_sub_of_int _ 63 (by linarith) (by linarith)]; linarith

/-! ## The statement -/

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`), `open LeanEval.ComplexAnalysis (Tantibar)`.
/-- **The angle map `T^[6]` carries the near arcs of the level-`(n+1)` `b₂`-polygon into the near
arcs of the level-`n` polygon.**  The three pairs are
`(armA1 n, armA2 n)`, `(armB1 n, armB2 n)`, `(armC1 n, armC2 n + 1)` with the closed forms of
`Work.ELNest.armChain_nest` (affine in `y = 64⁻ⁿ`).  The hypotheses say `x` is outside the three
closed far arcs of the level-`(n+1)` polygon; the conclusion says `T^[6] x` is outside the three
closed far arcs of the level-`n` polygon.  `Work.EL.T^[6] = θ ↦ fract (64 θ)`; the content is the
rational certificate `Work.ELPull.nearArcsCover_Delta`, scaled by `64^n`. -/
theorem pullD_arc (n : ℕ) (x : ℝ)
    (hA : ¬ Work.EL.InClosedArc x (Work.ELNest.armA1 (n + 1)) (Work.ELNest.armA2 (n + 1)))
    (hB : ¬ Work.EL.InClosedArc x (Work.ELNest.armB1 (n + 1)) (Work.ELNest.armB2 (n + 1)))
    (hC : ¬ Work.EL.InClosedArc x (Work.ELNest.armC1 (n + 1)) (Work.ELNest.armC2 (n + 1) + 1)) :
    ¬ Work.EL.InClosedArc ((Work.EL.T)^[6] x) (Work.ELNest.armA1 n) (Work.ELNest.armA2 n) ∧
    ¬ Work.EL.InClosedArc ((Work.EL.T)^[6] x) (Work.ELNest.armB1 n) (Work.ELNest.armB2 n) ∧
    ¬ Work.EL.InClosedArc ((Work.EL.T)^[6] x) (Work.ELNest.armC1 n) (Work.ELNest.armC2 n + 1) := by
  -- the two scales and the coordinate
  set Y : ℝ := ((64 : ℝ) ^ n)⁻¹ with hYdef
  set y : ℝ := ((64 : ℝ) ^ (n + 1))⁻¹ with hydef
  set u : ℝ := Int.fract (x - (22 : ℝ) / 63) with hudef
  have hyY : Y = 64 * y := by rw [hYdef, hydef, Work.ELNest.inv_pow_succ_64 n]; ring
  have hY1 : Y ≤ 1 := by rw [hYdef]; exact inv_pow_64_le_one n
  have hY0 : 0 < Y := by rw [hYdef]; positivity
  have hy0 : 0 < y := by rw [hydef]; positivity
  have hu0 : 0 ≤ u := by rw [hudef]; exact Int.fract_nonneg _
  have hu1 : u < 1 := by rw [hudef]; exact Int.fract_lt_one _
  -- the six source angles
  have hA1s : Work.ELNest.armA1 (n + 1) = (22 : ℝ) / 63 + ((289 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armA1_closed (n + 1), hydef]
  have hA2s : Work.ELNest.armA2 (n + 1) = (25 : ℝ) / 63 - ((41 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armA2_closed (n + 1), hydef]
  have hB1s : Work.ELNest.armB1 (n + 1) = (25 : ℝ) / 63 + ((1156 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armB1_closed (n + 1), hydef]
  have hB2s : Work.ELNest.armB2 (n + 1) = (37 : ℝ) / 63 - ((164 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armB2_closed (n + 1), hydef]
  have hC1s : Work.ELNest.armC1 (n + 1) = (37 : ℝ) / 63 + ((4624 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armC1_closed (n + 1), hydef]
  have hC2s : Work.ELNest.armC2 (n + 1) = (22 : ℝ) / 63 - ((656 : ℝ) / 21483 * y) := by
    rw [Work.ELNest.armC2_closed (n + 1), hydef]
  -- the six target angles
  have hA1t : Work.ELNest.armA1 n = (22 : ℝ) / 63 + ((289 : ℝ) / 21483 * Y) := by
    rw [Work.ELNest.armA1_closed n, hYdef]
  have hA2t : Work.ELNest.armA2 n = (25 : ℝ) / 63 - ((41 : ℝ) / 21483 * Y) := by
    rw [Work.ELNest.armA2_closed n, hYdef]
  have hB1t : Work.ELNest.armB1 n = (25 : ℝ) / 63 + ((1156 : ℝ) / 21483 * Y) := by
    rw [Work.ELNest.armB1_closed n, hYdef]
  have hB2t : Work.ELNest.armB2 n = (37 : ℝ) / 63 - ((164 : ℝ) / 21483 * Y) := by
    rw [Work.ELNest.armB2_closed n, hYdef]
  have hC1t : Work.ELNest.armC1 n = (37 : ℝ) / 63 + ((4624 : ℝ) / 21483 * Y) := by
    rw [Work.ELNest.armC1_closed n, hYdef]
  have hC2t : Work.ELNest.armC2 n = (22 : ℝ) / 63 - ((656 : ℝ) / 21483 * Y) := by
    rw [Work.ELNest.armC2_closed n, hYdef]
  -- the three source arc lengths
  have hy1 : y ≤ 1 := by rw [hydef]; exact inv_pow_64_le_one (n + 1)
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
    have hx := fract_sub_A x u ((289 : ℝ) / 21483 * y) hudef
    rw [hx] at h
    linarith
  have hBu : Int.fract (u - ((1 : ℝ) / 21 + (1156 : ℝ) / 21483 * y))
      > (4 : ℝ) / 21 - ((1320 : ℝ) / 21483 * y) := by
    have h := arcLen_lt_fract_of_not_InClosedArc hB
    rw [hlenB, hB1s] at h
    have hx := fract_sub_B x u ((1156 : ℝ) / 21483 * y) hudef
    rw [hx] at h
    linarith
  have hCu : Int.fract (u - ((5 : ℝ) / 21 + (4624 : ℝ) / 21483 * y))
      > (16 : ℝ) / 21 - ((5280 : ℝ) / 21483 * y) := by
    have h := arcLen_lt_fract_of_not_InClosedArc hC
    rw [hlenC, hC1s] at h
    have hx := fract_sub_C x u ((4624 : ℝ) / 21483 * y) hudef
    rw [hx] at h
    linarith
  -- the coordinate `u` lies in one of the four intervals
  have hdisj : u < (289 : ℝ) / 21483 * y ∨
      ((1 : ℝ) / 21 - (41 : ℝ) / 21483 * y < u ∧ u < (1 : ℝ) / 21 + (1156 : ℝ) / 21483 * y) ∨
      ((5 : ℝ) / 21 - (164 : ℝ) / 21483 * y < u ∧ u < (5 : ℝ) / 21 + (4624 : ℝ) / 21483 * y) ∨
      (1 - (656 : ℝ) / 21483 * y < u) := by
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
  obtain ⟨htA, htB, htC⟩ := target_conditions u Y y hyY hY1 hu0 hu1 hdisj
  -- the three target arc lengths
  have hlenA' : Work.EL.arcLen (Work.ELNest.armA1 n) (Work.ELNest.armA2 n)
      = (1 : ℝ) / 21 - ((330 : ℝ) / 21483 * Y) := by
    rw [Work.EL.arcLen, hA1t, hA2t,
      show ((25 : ℝ) / 63 - (41 : ℝ) / 21483 * Y) - ((22 : ℝ) / 63 + (289 : ℝ) / 21483 * Y)
        = (1 : ℝ) / 21 - (330 : ℝ) / 21483 * Y from by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hlenB' : Work.EL.arcLen (Work.ELNest.armB1 n) (Work.ELNest.armB2 n)
      = (4 : ℝ) / 21 - ((1320 : ℝ) / 21483 * Y) := by
    rw [Work.EL.arcLen, hB1t, hB2t,
      show ((37 : ℝ) / 63 - (164 : ℝ) / 21483 * Y) - ((25 : ℝ) / 63 + (1156 : ℝ) / 21483 * Y)
        = (4 : ℝ) / 21 - (1320 : ℝ) / 21483 * Y from by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hlenC' : Work.EL.arcLen (Work.ELNest.armC1 n) (Work.ELNest.armC2 n + 1)
      = (16 : ℝ) / 21 - ((5280 : ℝ) / 21483 * Y) := by
    rw [Work.EL.arcLen, hC1t, hC2t,
      show ((22 : ℝ) / 63 - (656 : ℝ) / 21483 * Y) + 1 - ((37 : ℝ) / 63 + (4624 : ℝ) / 21483 * Y)
        = (16 : ℝ) / 21 - (5280 : ℝ) / 21483 * Y from by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_⟩ <;> rw [T_iterate_six]
  · refine not_InClosedArc_of_lt_fract ?_
    rw [hlenA', hA1t, fract_pull_A x u ((289 : ℝ) / 21483 * Y) hudef]
    exact htA
  · refine not_InClosedArc_of_lt_fract ?_
    rw [hlenB', hB1t, fract_pull_B x u ((1156 : ℝ) / 21483 * Y) hudef]
    exact htB
  · refine not_InClosedArc_of_lt_fract ?_
    rw [hlenC', hC1t, fract_pull_C x u ((4624 : ℝ) / 21483 * Y) hudef]
    exact htC

end Work.ELAssembly
