import Mathlib
import Submission.Work.ELNest.ArmChain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.ELNest

/-! ## Auxiliary steps of the arm-`B` normal form

`armStepOf` is a pair of `Int.fract` applications along the (near or far) arc of the current
pair, shifted by `k/2`.  In the three cases met by the chain `armChainB` the result is affine:

* `NEAR` with `k = 1` (steps `j = 3, 1`): `(x, y) ↦ (1 - x/2, (1 - y)/2)`;
* `FAR` with `k = 1` (steps `j = 5, 4`): `(x, y) ↦ ((1 - y)/2, (1 - x)/2)`;
* `FAR` with `k = 0` (steps `j = 2, 0`): `(x, y) ↦ ((1 - y)/2, 1 - x/2)`.

Each normal form holds as soon as the pair sits in the box that makes the two
`Int.fract` arguments lie in the right half-open unit interval; the bounds are linear in the
input box. -/

/-- `Int.fract X = Y` from `0 ≤ Y < 1` and an integer offset: the `Int.fract_eq_iff` form used
throughout this file. -/
theorem armB_fract_eq_of_sub (X Y : ℝ) (h0 : 0 ≤ Y) (h1 : Y < 1) (k : ℤ)
    (hk : X - Y = (k : ℝ)) : Int.fract X = Y :=
  Int.fract_eq_iff.mpr ⟨h0, h1, k, hk⟩

/-- The value `kB j = 1` of the `k`-pattern, read in `ℝ`. -/
theorem armB_kB_cast_one {j : ℕ} (h : kB j = 1) : (kB j : ℝ) = 1 := by
  rw [h]; norm_num

/-- The value `kB j = 0` of the `k`-pattern, read in `ℝ`. -/
theorem armB_kB_cast_zero {j : ℕ} (h : kB j = 0) : (kB j : ℝ) = 0 := by
  rw [h]; norm_num

/-- The `NEAR`, `k = 1` normal form of `armStepOf`, valid on the box `-1 < x - y < 0`,
`0 < x < 2`, `-1 < y ≤ 1`. -/
theorem armB_step_near_one (j : ℕ) (hn : nearB j = true) (hk : (kB j : ℝ) = 1) (x y : ℝ)
    (hxy0 : x - y < 0) (hxy1 : -1 < x - y) (hx0 : 0 < x) (hx2 : x < 2)
    (hy0 : -1 < y) (hy1 : y ≤ 1) :
    armStepOf nearB kB j (x, y) = (1 - x / 2, (1 - y) / 2) := by
  have hfx : Int.fract (x - y) = x - y + 1 := by
    refine armB_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf1 : Int.fract (-(y + (x - y + 1)) / 2 + 1 / 2) = 1 - x / 2 := by
    refine armB_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf2 : Int.fract (-y / 2 + 1 / 2) = (1 - y) / 2 := by
    refine armB_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  simp only [armStepOf, armArcOf, Work.EL.arcLen, ite_eq_left hn, hk, hfx, hf1, hf2]

/-- The `FAR`, `k = 0` normal form of `armStepOf`, valid on the box `-1 < y - x < 0`,
`-1 < y ≤ 1`, `0 < x < 2`. -/
theorem armB_step_far_zero (j : ℕ) (hn : nearB j = false) (hk : (kB j : ℝ) = 0) (x y : ℝ)
    (hyx0 : y - x < 0) (hyx1 : -1 < y - x) (hy0 : -1 < y) (hy1 : y ≤ 1)
    (hx0 : 0 < x) (hx2 : x < 2) :
    armStepOf nearB kB j (x, y) = ((1 - y) / 2, 1 - x / 2) := by
  have hnt : ¬ (nearB j = true) := by rw [hn]; decide
  have hfx : Int.fract (y - x) = y - x + 1 := by
    refine armB_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf1 : Int.fract (-(x + (y - x + 1)) / 2) = (1 - y) / 2 := by
    refine armB_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf2 : Int.fract (-x / 2) = 1 - x / 2 := by
    refine armB_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  simp only [armStepOf, armArcOf, Work.EL.arcLen, ite_eq_right hnt, hk, zero_div, add_zero,
    hfx, hf1, hf2]

/-- The `FAR`, `k = 1` normal form of `armStepOf`, valid on the box `0 < y - x < 1`,
`-1 < x ≤ 1`, `-1 < y ≤ 1`. -/
theorem armB_step_far_one (j : ℕ) (hn : nearB j = false) (hk : (kB j : ℝ) = 1) (x y : ℝ)
    (hyx0 : 0 < y - x) (hyx1 : y - x < 1) (hx0 : -1 < x) (hx1 : x ≤ 1)
    (hy0 : -1 < y) (hy1 : y ≤ 1) :
    armStepOf nearB kB j (x, y) = ((1 - y) / 2, (1 - x) / 2) := by
  have hnt : ¬ (nearB j = true) := by rw [hn]; decide
  have hfx : Int.fract (y - x) = y - x := by
    refine armB_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  have hf1 : Int.fract (-(x + (y - x)) / 2 + 1 / 2) = (1 - y) / 2 := by
    refine armB_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  have hf2 : Int.fract (-x / 2 + 1 / 2) = (1 - x) / 2 := by
    refine armB_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  simp only [armStepOf, armArcOf, Work.EL.arcLen, ite_eq_right hnt, hk, hfx, hf1, hf2]

/-!
# ELNest N3: the six-step arm-`B` chain is a `1/64`-contraction

`Work.ELNest.armPairOf nearB kB (a,b) 6` is the six-step composite of the certified chain
`Cert.armChainB` (the patterns `nearB`, `kB` of `Submission.Work.ELNest.ArmChain`), read as a map
`R x R -> R x R` on the angle pair.  On the box `25/63 <= a <= 461/1023`, `593/1023 <= b <= 37/63`,
which contains the level-`n` arm-`B` pair `(armB1 n, armB2 n)` for every `n` (these contract toward
the tripod angles `25/63`, `37/63` as `n -> infinity`), the composite is the contraction
`x |-> fix + (x - fix)/64` toward those two tripod angles.

Step-by-step normal forms, all verified exactly over the rationals (NEAR means the arc used is
`(b, b + fract (a-b))`, FAR means `(a, a + fract (b-a))`; "sub k" is the integer subtracted when
taking `Int.fract`):

| step | arc, k | reductions | new pair (x,y) | box of (x,y) |
|------|----------|-----------|------------------|----------------|
| `j=5` | FAR, k=1 | `fract(b-a)=b-a`; `(1-b)/2`, `(1-a)/2` no sub | `((1-b)/2, (1-a)/2)` | `a in [13/63,215/1023]`, `b in [281/1023,19/63]` |
| `j=4` | FAR, k=1 | `fract(b-a)=b-a`; `(1-b1)/2`, `(1-a1)/2` no sub | `(a/4+1/4, b/4+1/4)` | `a in [22/63,371/1023]`, `b in [404/1023,25/63]` |
| `j=3` | NEAR, k=1 | `fract(a-b)=a-b+1`; `-(a2+1)/2` sub 1; `(1-b2)/2` no sub | `(7/8-a/8, 3/8-b/8)` | `a in [1675/2046,52/63]`, `b in [19/63,619/2046]` |
| `j=2` | FAR, k=0 | `fract(b-a)=b-a+1`; `-(b3+1)/2` sub 1; `-a3/2` sub 1 | `(5/16+b/16, 9/16+a/16)` | `a in [1427/4092,22/63]`, `b in [37/63,2417/4092]` |
| `j=1` | NEAR, k=1 | `fract(a-b)=a-b+1`; `-(a4+1)/2` sub 1; `(1-b4)/2` no sub | `(27/32-b/32, 7/32-a/32)` | `a in [52/63,6757/8184]`, `b in [1675/8184,13/63]` |
| `j=0` | FAR, k=0 | `fract(b-a)=b-a+1`; `-(b5+1)/2` sub 1; `-a5/2` sub 1 | `(25/64+a/64, 37/64+b/64)` | - |

The intermediate quantities `a1 = (1-b)/2, b1 = (1-a)/2`, `a2 = a/4+1/4, b2 = b/4+1/4`, ...
are the components of the previous row.  The last row equals
`(25/63 + (a-25/63)/64, 37/63 + (b-37/63)/64)`.

Hints.  Each `Int.fract X = Y` follows from `Int.fract_eq_iff`: need `0 <= Y`, `Y < 1` and an
integer `k` with `X = Y + k`; the bounds are linear in the box data, the integer identity is
polynomial.  Each `arcLen` occurrence is `Work.EL.arcLen` and reduces the same way.  The `if`s of
`armArcOf`/`armStepOf` reduce under `simp [armStepOf, armArcOf, nearB, kB, Work.EL.arcLen]` (the
`Bool` valued `nearB`/`kB` need explicit `decide` facts such as `nearB 5 = false`).
-/

theorem armChainB_norm (a b : ℝ) (h1 : 25 / 63 ≤ a) (h2 : a ≤ 461 / 1023)
    (h3 : 593 / 1023 ≤ b) (h4 : b ≤ 37 / 63) :
    Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (a, b) 6
      = (25 / 63 + (a - 25 / 63) / 64, 37 / 63 + (b - 37 / 63) / 64) := by
  have hexp : armPairOf nearB kB (a, b) 6 = armStepOf nearB kB 0 (armStepOf nearB kB 1 (armStepOf nearB kB 2 (armStepOf nearB kB 3 (armStepOf nearB kB 4 (armStepOf nearB kB 5 (a, b)))))) := rfl
  -- step j = 5 : FAR, k = 1, on `(a, b)`
  have e5 : armStepOf nearB kB 5 (a, b) = ((1 - b) / 2, (1 - a) / 2) :=
    armB_step_far_one 5 (by decide) (armB_kB_cast_one (j := 5) (by decide)) a b
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  -- step j = 4 : FAR, k = 1, on `((1-b)/2, (1-a)/2)`
  have e4 : armStepOf nearB kB 4 ((1 - b) / 2, (1 - a) / 2)
      = ((1 - (1 - a) / 2) / 2, (1 - (1 - b) / 2) / 2) :=
    armB_step_far_one 4 (by decide) (armB_kB_cast_one (j := 4) (by decide)) ((1 - b) / 2) ((1 - a) / 2)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have p4 : ((1 - (1 - a) / 2) / 2, (1 - (1 - b) / 2) / 2) = (1 / 4 + a / 4, 1 / 4 + b / 4) := by
    refine Prod.ext ?_ ?_ <;> ring
  -- step j = 3 : NEAR, k = 1, on `(1/4 + a/4, 1/4 + b/4)`
  have e3 : armStepOf nearB kB 3 (1 / 4 + a / 4, 1 / 4 + b / 4)
      = (1 - (1 / 4 + a / 4) / 2, (1 - (1 / 4 + b / 4)) / 2) :=
    armB_step_near_one 3 (by decide) (armB_kB_cast_one (j := 3) (by decide)) (1 / 4 + a / 4) (1 / 4 + b / 4)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have p3 : (1 - (1 / 4 + a / 4) / 2, (1 - (1 / 4 + b / 4)) / 2) = (7 / 8 - a / 8, 3 / 8 - b / 8) := by
    refine Prod.ext ?_ ?_ <;> ring
  -- step j = 2 : FAR, k = 0, on `(7/8 - a/8, 3/8 - b/8)`
  have e2 : armStepOf nearB kB 2 (7 / 8 - a / 8, 3 / 8 - b / 8)
      = ((1 - (3 / 8 - b / 8)) / 2, 1 - (7 / 8 - a / 8) / 2) :=
    armB_step_far_zero 2 (by decide) (armB_kB_cast_zero (j := 2) (by decide)) (7 / 8 - a / 8) (3 / 8 - b / 8)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have p2 : ((1 - (3 / 8 - b / 8)) / 2, 1 - (7 / 8 - a / 8) / 2) = (5 / 16 + b / 16, 9 / 16 + a / 16) := by
    refine Prod.ext ?_ ?_ <;> ring
  -- step j = 1 : NEAR, k = 1, on `(5/16 + b/16, 9/16 + a/16)`
  have e1 : armStepOf nearB kB 1 (5 / 16 + b / 16, 9 / 16 + a / 16)
      = (1 - (5 / 16 + b / 16) / 2, (1 - (9 / 16 + a / 16)) / 2) :=
    armB_step_near_one 1 (by decide) (armB_kB_cast_one (j := 1) (by decide)) (5 / 16 + b / 16) (9 / 16 + a / 16)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have p1 : (1 - (5 / 16 + b / 16) / 2, (1 - (9 / 16 + a / 16)) / 2) = (27 / 32 - b / 32, 7 / 32 - a / 32) := by
    refine Prod.ext ?_ ?_ <;> ring
  -- step j = 0 : FAR, k = 0, on `(27/32 - b/32, 7/32 - a/32)`
  have e0 : armStepOf nearB kB 0 (27 / 32 - b / 32, 7 / 32 - a / 32)
      = ((1 - (7 / 32 - a / 32)) / 2, 1 - (27 / 32 - b / 32) / 2) :=
    armB_step_far_zero 0 (by decide) (armB_kB_cast_zero (j := 0) (by decide)) (27 / 32 - b / 32) (7 / 32 - a / 32)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have p0 : ((1 - (7 / 32 - a / 32)) / 2, 1 - (27 / 32 - b / 32) / 2) = (25 / 64 + a / 64, 37 / 64 + b / 64) := by
    refine Prod.ext ?_ ?_ <;> ring
  rw [hexp, e5, e4, p4, e3, p3, e2, p2, e1, p1, e0, p0]
  refine Prod.ext ?_ ?_ <;> ring

end Work.ELNest
