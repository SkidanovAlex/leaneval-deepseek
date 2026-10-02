/-
# `rot_cut`: the arms of the tripod at `b₂` rotate under `F = (T_c)^{10}`

The cut point of the level-`n` arm pair of the nest at `b₂` is the landing point of the two
rays of the pair, hence of its first angle: `S.cutA n = (Za n).y` is the landing point of the
ray of angle `armA1 n`, and similarly for the arms `B` and `C`.

The action of `F c = (T_c)^{10}` on rays is the tenth iterate of the angle map
`T θ = -2θ mod 1` (`landsN_iterate_F`), so `F c` sends the landing point of the ray of angle
`θ` to the landing point of the ray of angle `T^[10] θ`.  The arithmetic of the first angles of
the arm pairs (`Submission/Work/ELNest/T10_armA1.lean`, `.../T10_armB1.lean`,
`.../T10_armC1.lean`) is

    T^[10] (armA1 n) = armC1 (n - 1),   T^[10] (armB1 n) = armA1 (n - 2),
    T^[10] (armC1 n) = armB1 (n - 2),

i.e. the three arms rotate `A → C → B → A`, with the level of the arms `B`, `C` two steps
ahead of that of the arm `A` (which is exactly the normalisation of the certificate:
`armA1 n = 22/63 + δ/64ⁿ`, `armB1 n = 25/63 + 4δ/64ⁿ`, `armC1 n = 37/63 + 16δ/64ⁿ` with
`δ = 289/21483`).

By uniqueness of landing points, `F c` therefore maps the arm cut points to each other:

    F c (S.cutA n) = S.cutC (n - 1),   F c (S.cutB n) = S.cutA (n - 2),
    F c (S.cutC n) = S.cutB (n - 2),

and the fields `cutA_mem`, `cutB_mem`, `cutC_mem` of `NestData` place the cut points in the
corresponding arms.  This is the arm rotation used by the equator-leak argument.
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.Qp_shift
import Submission.Work.ELNest.T10_armA1
import Submission.Work.ELNest.T10_armB1
import Submission.Work.ELNest.T10_armC1
import Submission.Work.ELPull.armRot_level
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.landsN_map
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

noncomputable section

namespace Work.ELNest

open Work.EL

/-! ## The first angles of the arm pairs land at the cut points -/

/-- The ray of the first angle `armA1 n` of the level-`n` arm-`A` pair lands at the cut point
`S.cutA n`. -/
theorem rot_lands_armA1 {c : ℂ} (S : NestData c) (n : ℕ) :
    LandsN S.d.hN (armA1 n) (S.cutA n) := by
  have h := (S.Za n).lands_a
  rw [S.Zaa n] at h
  exact h

/-- The ray of the first angle `armB1 n` of the level-`n` arm-`B` pair lands at the cut point
`S.cutB n`. -/
theorem rot_lands_armB1 {c : ℂ} (S : NestData c) (n : ℕ) :
    LandsN S.d.hN (armB1 n) (S.cutB n) := by
  have h := (S.Zb n).lands_a
  rw [S.Zba n] at h
  exact h

/-- The ray of the first angle `armC1 n` of the level-`n` arm-`C` pair lands at the cut point
`S.cutC n`. -/
theorem rot_lands_armC1 {c : ℂ} (S : NestData c) (n : ℕ) :
    LandsN S.d.hN (armC1 n) (S.cutC n) := by
  have h := (S.Zc n).lands_a
  rw [S.Zca n] at h
  exact h

/-! ## `F c` maps the cut points to the cut points of the rotated arms -/

/-- **The arm `A` rotates to the arm `C`.**  `F c` maps the level-`n` cut point of the arm `A`
to the level-`(n-1)` cut point of the arm `C`, because the ray of angle `armA1 n` lands at
`S.cutA n`, its image under `F c` is the ray of angle `T^[10] (armA1 n) = armC1 (n-1)`, and
the latter lands at `S.cutC (n-1)`. -/
theorem rot_cutA_map {c : ℂ} (S : NestData c) (n : ℕ) (hn : 1 ≤ n) :
    F c (S.cutA n) = S.cutC (n - 1) := by
  have h2 := landsN_iterate_F S.d.hN S.d.bottcher (rot_lands_armA1 S n)
  rw [T10_armA1 n hn] at h2
  exact (landsN_unique (rot_lands_armC1 S (n - 1)) h2).symm

/-- **The arm `B` rotates to the arm `A`.**  `F c` maps the level-`n` cut point of the arm `B`
to the level-`(n-2)` cut point of the arm `A`. -/
theorem rot_cutB_map {c : ℂ} (S : NestData c) (n : ℕ) (hn : 2 ≤ n) :
    F c (S.cutB n) = S.cutA (n - 2) := by
  have h2 := landsN_iterate_F S.d.hN S.d.bottcher (rot_lands_armB1 S n)
  rw [T10_armB1 n hn] at h2
  exact (landsN_unique (rot_lands_armA1 S (n - 2)) h2).symm

/-- **The arm `C` rotates to the arm `B`.**  `F c` maps the level-`n` cut point of the arm `C`
to the level-`(n-2)` cut point of the arm `B`. -/
theorem rot_cutC_map {c : ℂ} (S : NestData c) (n : ℕ) (hn : 2 ≤ n) :
    F c (S.cutC n) = S.cutB (n - 2) := by
  have h2 := landsN_iterate_F S.d.hN S.d.bottcher (rot_lands_armC1 S n)
  rw [T10_armC1 n hn] at h2
  exact (landsN_unique (rot_lands_armB1 S (n - 2)) h2).symm

/-! ## The arm rotation at the cut points -/

theorem rot_cut {c : ℂ} (S : Work.ELNest.NestData c) :
    ∃ N : ℕ, ∀ n ≥ N, Work.ELNest.F c (S.cutA n) ∈ S.armC ∧
      Work.ELNest.F c (S.cutB n) ∈ S.armA ∧ Work.ELNest.F c (S.cutC n) ∈ S.armB := by
  refine ⟨2, fun n hn => ⟨?_, ?_, ?_⟩⟩
  · rw [rot_cutA_map S n (by omega)]
    exact S.cutC_mem (n - 1)
  · rw [rot_cutB_map S n hn]
    exact S.cutA_mem (n - 2)
  · rw [rot_cutC_map S n hn]
    exact S.cutB_mem (n - 2)

end Work.ELNest
