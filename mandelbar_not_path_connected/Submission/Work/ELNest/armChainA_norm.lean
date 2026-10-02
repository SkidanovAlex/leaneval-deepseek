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

/-! ## Auxiliary steps of the arm-`A` normal form

`armStepOf` is a pair of `Int.fract` applications along the (near or far) arc of the current
pair, shifted by `k/2`.  In the three cases met by the chain `armChainA` the result is affine:

* `NEAR` with `k = 1` (steps `j = 5, 3`): `(x, y) ↦ (1 - x/2, (1 - y)/2)`;
* `FAR` with `k = 0` (steps `j = 4, 2`): `(x, y) ↦ ((1 - y)/2, 1 - x/2)`;
* `FAR` with `k = 1` (steps `j = 1, 0`): `(x, y) ↦ ((1 - y)/2, (1 - x)/2)`.

Each normal form holds as soon as the pair sits in the box that makes the two
`Int.fract` arguments lie in the right half-open unit interval; the bounds are linear in the
input box. -/

/-- `Int.fract X = Y` from `0 ≤ Y < 1` and an integer offset: the `Int.fract_eq_iff` form used
throughout this file. -/
theorem armA_fract_eq_of_sub (X Y : ℝ) (h0 : 0 ≤ Y) (h1 : Y < 1) (k : ℤ)
    (hk : X - Y = (k : ℝ)) : Int.fract X = Y :=
  Int.fract_eq_iff.mpr ⟨h0, h1, k, hk⟩

/-- The value `kA j = 1` of the `k`-pattern, read in `ℝ`. -/
theorem armA_kA_cast_one {j : ℕ} (h : kA j = 1) : (kA j : ℝ) = 1 := by
  rw [h]; norm_num

/-- The value `kA j = 0` of the `k`-pattern, read in `ℝ`. -/
theorem armA_kA_cast_zero {j : ℕ} (h : kA j = 0) : (kA j : ℝ) = 0 := by
  rw [h]; norm_num

/-- The `NEAR`, `k = 1` normal form of `armStepOf`, valid on the box `-1 < x - y < 0`,
`0 < x < 2`, `-1 < y ≤ 1`. -/
theorem armA_step_near_one (j : ℕ) (hn : nearA j = true) (hk : (kA j : ℝ) = 1) (x y : ℝ)
    (hxy0 : x - y < 0) (hxy1 : -1 < x - y) (hx0 : 0 < x) (hx2 : x < 2)
    (hy0 : -1 < y) (hy1 : y ≤ 1) :
    armStepOf nearA kA j (x, y) = (1 - x / 2, (1 - y) / 2) := by
  have hfx : Int.fract (x - y) = x - y + 1 := by
    refine armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf1 : Int.fract (-(y + (x - y + 1)) / 2 + 1 / 2) = 1 - x / 2 := by
    refine armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf2 : Int.fract (-y / 2 + 1 / 2) = (1 - y) / 2 := by
    refine armA_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  simp only [armStepOf, armArcOf, Work.EL.arcLen, ite_eq_left hn, hk, hfx, hf1, hf2]

/-- The `FAR`, `k = 0` normal form of `armStepOf`, valid on the box `-1 < y - x < 0`,
`-1 < y ≤ 1`, `0 < x < 2`. -/
theorem armA_step_far_zero (j : ℕ) (hn : nearA j = false) (hk : (kA j : ℝ) = 0) (x y : ℝ)
    (hyx0 : y - x < 0) (hyx1 : -1 < y - x) (hy0 : -1 < y) (hy1 : y ≤ 1)
    (hx0 : 0 < x) (hx2 : x < 2) :
    armStepOf nearA kA j (x, y) = ((1 - y) / 2, 1 - x / 2) := by
  have hnt : ¬ (nearA j = true) := by rw [hn]; decide
  have hfx : Int.fract (y - x) = y - x + 1 := by
    refine armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf1 : Int.fract (-(x + (y - x + 1)) / 2) = (1 - y) / 2 := by
    refine armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf2 : Int.fract (-x / 2) = 1 - x / 2 := by
    refine armA_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  simp only [armStepOf, armArcOf, Work.EL.arcLen, ite_eq_right hnt, hk, zero_div, add_zero,
    hfx, hf1, hf2]

/-- The `FAR`, `k = 1` normal form of `armStepOf`, valid on the box `0 < y - x < 1`,
`-1 < x ≤ 1`, `-1 < y ≤ 1`. -/
theorem armA_step_far_one (j : ℕ) (hn : nearA j = false) (hk : (kA j : ℝ) = 1) (x y : ℝ)
    (hyx0 : 0 < y - x) (hyx1 : y - x < 1) (hx0 : -1 < x) (hx1 : x ≤ 1)
    (hy0 : -1 < y) (hy1 : y ≤ 1) :
    armStepOf nearA kA j (x, y) = ((1 - y) / 2, (1 - x) / 2) := by
  have hnt : ¬ (nearA j = true) := by rw [hn]; decide
  have hfx : Int.fract (y - x) = y - x := by
    refine armA_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  have hf1 : Int.fract (-(x + (y - x)) / 2 + 1 / 2) = (1 - y) / 2 := by
    refine armA_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  have hf2 : Int.fract (-x / 2 + 1 / 2) = (1 - x) / 2 := by
    refine armA_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  simp only [armStepOf, armArcOf, Work.EL.arcLen, ite_eq_right hnt, hk, hfx, hf1, hf2]


/-!
# ELNest N3: the six-step arm-`A` chain is a `1/64`-contraction

`Work.ELNest.armPairOf nearA kA (a,b) 6` is the six-step composite of the certified chain
`Cert.armChainA` (the patterns `nearA`, `kA` of `Submission.Work.ELNest.ArmChain`), read as a map
`R x R -> R x R` on the angle pair.  On the box `22/63 <= a <= 371/1023`, `404/1023 <= b <= 25/63`,
which contains the level-`n` arm-`A` pair `(armA1 n, armA2 n)` for every `n` (these contract
toward the tripod angles `22/63`, `25/63` as `n -> infinity`), the composite is the contraction
`x |-> fix + (x - fix)/64` toward those two tripod angles.

Step-by-step normal forms, all verified exactly over the rationals (one step per `armStepOf`, from
`j = 5` down to `j = 0`; NEAR means the arc used is `(b, b + fract (a-b))`, FAR means
`(a, a + fract (b-a))`; "sub k" is the integer subtracted when taking `Int.fract`):

| step | arc, k | reductions | new pair (x,y) | box of (x,y) |
|------|----------|-----------|------------------|----------------|
| `j=5` | NEAR, k=1 | `fract(a-b) = a-b+1`; `(1-(a+1))/2 = -a/2` sub 1; `(1-b)/2` no sub | `(1-a/2, (1-b)/2)` | `a in [1675/2046,52/63]`, `b in [19/63,619/2046]` |
| `j=4` | FAR, k=0 | `fract(b-a)=b-a+1`; `-(b1+1)/2` sub 1; `-a1/2` sub 1 | `(b/4+1/4, a/4+1/2)` | `a in [1427/4092,22/63]`, `b in [37/63,2417/4092]` |
| `j=3` | NEAR, k=1 | `fract(a-b)=a-b+1`; `-(a2+1)/2` sub 1; `(1-b2)/2` no sub | `(7/8-b/8, 1/4-a/8)` | `a in [52/63,6757/8184]`, `b in [1675/8184,13/63]` |
| `j=2` | FAR, k=0 | `fract(b-a)=b-a+1`; `-(b3+1)/2` sub 1; `-a3/2` sub 1 | `(3/8+a/16, 9/16+b/16)` | `a in [25/63,6509/16368]`, `b in [9611/16368,37/63]` |
| `j=1` | FAR, k=1 | `fract(b-a)=b-a` (no sub); `(1-b4)/2`, `(1-a4)/2` no sub | `(7/32-b/32, 5/16-a/32)` | `a in [13/63,6757/32736]`, `b in [9859/32736,19/63]` |
| `j=0` | FAR, k=1 | `fract(b-a)=b-a`; `(1-b5)/2`, `(1-a5)/2` no sub | `(11/32+a/64, 25/64+b/64)` | - |

The intermediate quantities `a1 = 1-a/2, b1 = (1-b)/2`, `a2 = b/4+1/4, b2 = a/4+1/2`, ...
are the components of the previous row.  The last row equals
`(22/63 + (a-22/63)/64, 25/63 + (b-25/63)/64)`.

Hints.  Each `Int.fract X = Y` follows from `Int.fract_eq_iff`: need `0 <= Y`, `Y < 1` and an
integer `k` with `X = Y + k`; the bounds are linear in the box data, the integer identity is
polynomial.  Each `arcLen` occurrence is `Work.EL.arcLen` and reduces the same way.  The `if`s of
`armArcOf`/`armStepOf` reduce under `simp [armStepOf, armArcOf, nearA, kA, Work.EL.arcLen]` (the
`Bool` valued `nearA`/`kA` need explicit `decide` facts such as `nearA 5 = true`).
-/


theorem armChainA_norm (a b : ℝ) (h1 : 22 / 63 ≤ a) (h2 : a ≤ 371 / 1023)
    (h3 : 404 / 1023 ≤ b) (h4 : b ≤ 25 / 63) :
    Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (a, b) 6
      = (22 / 63 + (a - 22 / 63) / 64, 25 / 63 + (b - 25 / 63) / 64) := by
  have hexp : armPairOf nearA kA (a, b) 6 = armStepOf nearA kA 0 (armStepOf nearA kA 1 (armStepOf nearA kA 2 (armStepOf nearA kA 3 (armStepOf nearA kA 4 (armStepOf nearA kA 5 (a, b)))))) := rfl
  have e5 : armStepOf nearA kA 5 (a, b) = (1 - a / 2, (1 - b) / 2) :=
    armA_step_near_one 5 (by decide) (armA_kA_cast_one (j := 5) (by decide)) a b (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have e4 : armStepOf nearA kA 4 (1 - a / 2, (1 - b) / 2) = ((1 - ((1 - b) / 2)) / 2, 1 - (1 - a / 2) / 2) :=
    armA_step_far_zero 4 (by decide) (armA_kA_cast_zero (j := 4) (by decide)) (1 - a / 2) ((1 - b) / 2) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have e3 : armStepOf nearA kA 3 ((1 - ((1 - b) / 2)) / 2, 1 - (1 - a / 2) / 2) = (1 - ((1 - ((1 - b) / 2)) / 2) / 2, (1 - (1 - (1 - a / 2) / 2)) / 2) :=
    armA_step_near_one 3 (by decide) (armA_kA_cast_one (j := 3) (by decide)) ((1 - ((1 - b) / 2)) / 2) (1 - (1 - a / 2) / 2) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have e2 : armStepOf nearA kA 2 (1 - ((1 - ((1 - b) / 2)) / 2) / 2, (1 - (1 - (1 - a / 2) / 2)) / 2) = ((1 - ((1 - (1 - (1 - a / 2) / 2)) / 2)) / 2, 1 - (1 - ((1 - ((1 - b) / 2)) / 2) / 2) / 2) :=
    armA_step_far_zero 2 (by decide) (armA_kA_cast_zero (j := 2) (by decide)) (1 - ((1 - ((1 - b) / 2)) / 2) / 2) ((1 - (1 - (1 - a / 2) / 2)) / 2) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have e1 : armStepOf nearA kA 1 ((1 - ((1 - (1 - (1 - a / 2) / 2)) / 2)) / 2, 1 - (1 - ((1 - ((1 - b) / 2)) / 2) / 2) / 2) = ((1 - (1 - (1 - ((1 - ((1 - b) / 2)) / 2) / 2) / 2)) / 2, (1 - ((1 - ((1 - (1 - (1 - a / 2) / 2)) / 2)) / 2)) / 2) :=
    armA_step_far_one 1 (by decide) (armA_kA_cast_one (j := 1) (by decide)) ((1 - ((1 - (1 - (1 - a / 2) / 2)) / 2)) / 2) (1 - (1 - ((1 - ((1 - b) / 2)) / 2) / 2) / 2) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have e0 : armStepOf nearA kA 0 ((1 - (1 - (1 - ((1 - ((1 - b) / 2)) / 2) / 2) / 2)) / 2, (1 - ((1 - ((1 - (1 - (1 - a / 2) / 2)) / 2)) / 2)) / 2) = ((1 - ((1 - ((1 - ((1 - (1 - (1 - a / 2) / 2)) / 2)) / 2)) / 2)) / 2, (1 - ((1 - (1 - (1 - ((1 - ((1 - b) / 2)) / 2) / 2) / 2)) / 2)) / 2) :=
    armA_step_far_one 0 (by decide) (armA_kA_cast_one (j := 0) (by decide)) ((1 - (1 - (1 - ((1 - ((1 - b) / 2)) / 2) / 2) / 2)) / 2) ((1 - ((1 - ((1 - (1 - (1 - a / 2) / 2)) / 2)) / 2)) / 2) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  rw [hexp, e5, e4, e3, e2, e1, e0]
  refine Prod.ext ?_ ?_ <;> ring



end Work.ELNest
