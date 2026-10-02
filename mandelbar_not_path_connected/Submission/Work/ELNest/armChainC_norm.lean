import Mathlib
import Submission.Work.ELNest.ArmChain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

/-!
# ELNest N3: the six-step arm-`C` chain is a `1/64`-contraction, with the components interchanged

`Work.ELNest.armPairOf nearC kC (a,b) 6` is the six-step composite of the certified chain
`Cert.armChainC` (the patterns `nearC`, `kC` of `Submission.Work.ELNest.ArmChain`), read as a map
`R x R -> R x R` on the angle pair.  On the box `37/63 <= a <= 821/1023`, `326/1023 <= b <= 22/63`,
which contains the level-`n` arm-`C` pair `(armC1 n, armC2 n)` for every `n` (these contract toward
the tripod angle `37/63` in the first component and `22/63` in the second as `n -> infinity`; note
that the angle pair of the `C`-arm is `(armC1 n, armC2 n + 1)` in the certificate, i.e. the
component `armC2 n` lives in the arc just below `22/63`), the composite is the contraction toward
the two tripod angles **with the two components interchanged**:

  `armPairOf nearC kC (a,b) 6 = (22/63 + (b - 22/63)/64, 37/63 + (a - 37/63)/64)`.

The interchange is a genuine feature of the certified `C`-chain (that arm runs the other way round
the tripod); it is exactly what makes the third conjunct of the analogous chain result read
`(armC2 (n+1), armC1 (n+1))`.

Step-by-step normal forms, all verified exactly over the rationals (NEAR means the arc used is
`(b, b + fract (a-b))`, FAR means `(a, a + fract (b-a))`; "sub k" is the integer subtracted when
taking `Int.fract`):

| step | arc, k | reductions | new pair (x,y) | box of (x,y) |
|------|----------|-----------|------------------|----------------|
| `j=5` | FAR, k=1 | `fract(b-a)=b-a+1`; `-(b+1)/2` sub 1; `-a/2` sub 1 | `(1-b/2, (1-a)/2)` | `a in [52/63,860/1023]`, `b in [101/1023,13/63]` |
| `j=4` | FAR, k=0 | `fract(b-a)=b-a+1`; `-(b1+1)/2` sub 1; `-a1/2` sub 1 | `(a/4+1/4, b/4+1/2)` | `a in [25/63,461/1023]`, `b in [593/1023,37/63]` |
| `j=3` | FAR, k=1 | `fract(b-a)=b-a` (no sub); `(1-b2)/2`, `(1-a2)/2` no sub | `(1/4-b/8, 3/8-a/8)` | `a in [13/63,215/1023]`, `b in [281/1023,19/63]` |
| `j=2` | FAR, k=1 | `fract(b-a)=b-a`; `(1-b3)/2`, `(1-a3)/2` no sub | `(5/16+a/16, 3/8+b/16)` | `a in [22/63,371/1023]`, `b in [404/1023,25/63]` |
| `j=1` | NEAR, k=1 | `fract(a-b)=a-b+1`; `-(a4+1)/2` sub 1; `(1-b4)/2` no sub | `(27/32-a/32, 5/16-b/32)` | `a in [1675/2046,52/63]`, `b in [19/63,619/2046]` |
| `j=0` | FAR, k=0 | `fract(b-a)=b-a+1`; `-(b5+1)/2` sub 1; `-a5/2` sub 1 | `(11/32+b/64, 37/64+a/64)` | - |

The intermediate quantities `a1 = 1-b/2, b1 = (1-a)/2`, `a2 = a/4+1/4, b2 = b/4+1/2`, ...
are the components of the previous row.  The last row equals
`(22/63 + (b-22/63)/64, 37/63 + (a-37/63)/64)`.

Hints.  Each `Int.fract X = Y` follows from `Int.fract_eq_iff`: need `0 <= Y`, `Y < 1` and an
integer `k` with `X = Y + k`; the bounds are linear in the box data, the integer identity is
polynomial.  Each `arcLen` occurrence is `Work.EL.arcLen` and reduces the same way.  The `if`s of
`armArcOf`/`armStepOf` reduce under `simp [armStepOf, armArcOf, nearC, kC, Work.EL.arcLen]` (the
`Bool` valued `nearC`/`kC` need explicit `decide` facts such as `nearC 0 = false`).
-/


set_option linter.unusedVariables false

/-! ## The four step normal forms of the arm-`C` chain

Each `armStepOf` is a pair of `Int.fract` applications, along the (near or far) arc of the current
pair and shifted by `k/2`.  All the steps of the certified `C` chain use `k = 1` except `j = 4`
and `j = 0`, which use `k = 0`; for `k = 1`, and depending on the position of the pair, the
fractional parts are either the identity or a shift by `-1`.  The four cases met by the chain are:

* `FAR`, `k = 1`, `y - x` shifted (step `j = 5`): `(x,y) ↦ (1 - y/2, (1-x)/2)`;
* `FAR`, `k = 1`, `y - x` not shifted (steps `j = 3, 2`): `(x,y) ↦ ((1-y)/2, (1-x)/2)`;
* `FAR`, `k = 0`, `y - x` shifted (steps `j = 4, 0`): `(x,y) ↦ ((1-y)/2, 1 - x/2)`;
* `NEAR`, `k = 1`, `x - y` shifted (step `j = 1`): `(x,y) ↦ (1 - x/2, (1-y)/2)`.

Each normal form holds as soon as the pair sits in the box that puts the `Int.fract` arguments in
the right half-open unit interval; the bounds are linear in the input box. -/

/-- `Int.fract X = Y` from `0 ≤ Y < 1` and an integer offset: the `Int.fract_eq_iff` form used
throughout this file. -/
theorem armC_fract_eq_of_sub (X Y : ℝ) (h0 : 0 ≤ Y) (h1 : Y < 1) (k : ℤ)
    (hk : X - Y = (k : ℝ)) : Int.fract X = Y :=
  Int.fract_eq_iff.mpr ⟨h0, h1, k, hk⟩

/-- The value `kC j = 1` of the `k`-pattern, read in `ℝ`. -/
theorem armC_kC_cast_one {j : ℕ} (h : kC j = 1) : (kC j : ℝ) = 1 := by
  rw [h]; norm_num

/-- The value `kC j = 0` of the `k`-pattern, read in `ℝ`. -/
theorem armC_kC_cast_zero {j : ℕ} (h : kC j = 0) : (kC j : ℝ) = 0 := by
  rw [h]; norm_num

/-- The `NEAR`, `k = 1` normal form of `armStepOf`, valid on the box `-1 < x - y < 0`,
`0 < x < 2`, `-1 < y < 1`. -/
theorem armC_step_near_one_sub (j : ℕ) (hn : nearC j = true) (hk : (kC j : ℝ) = 1) (x y : ℝ)
    (hxy0 : x - y < 0) (hxy1 : -1 < x - y) (hx0 : 0 < x) (hx2 : x < 2)
    (hy0 : -1 < y) (hy1 : y < 1) :
    armStepOf nearC kC j (x, y) = (1 - x / 2, (1 - y) / 2) := by
  have hfx : Int.fract (x - y) = x - y + 1 := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf1 : Int.fract (-(y + (x - y + 1)) / 2 + 1 / 2) = 1 - x / 2 := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf2 : Int.fract (-y / 2 + 1 / 2) = (1 - y) / 2 := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  simp only [armStepOf, armArcOf, Work.EL.arcLen, ite_eq_left hn, hk, hfx, hf1, hf2]

/-- The `FAR`, `k = 1` normal form of `armStepOf` with `fract (y - x) = y - x + 1`, valid on the
box `-1 < y - x < 0`, `-1 < x < 1`, `0 < y < 2`. -/
theorem armC_step_far_one_sub (j : ℕ) (hn : nearC j = false) (hk : (kC j : ℝ) = 1) (x y : ℝ)
    (hyx0 : y - x < 0) (hyx1 : -1 < y - x) (hx0 : -1 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy2 : y < 2) :
    armStepOf nearC kC j (x, y) = (1 - y / 2, (1 - x) / 2) := by
  have hnt : ¬ (nearC j = true) := by rw [hn]; decide
  have hfx : Int.fract (y - x) = y - x + 1 := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf1 : Int.fract (-(x + (y - x + 1)) / 2 + 1 / 2) = 1 - y / 2 := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf2 : Int.fract (-x / 2 + 1 / 2) = (1 - x) / 2 := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  simp only [armStepOf, armArcOf, Work.EL.arcLen, ite_eq_right hnt, hk, hfx, hf1, hf2]

/-- The `FAR`, `k = 1` normal form of `armStepOf` with `fract (y - x) = y - x`, valid on the box
`0 < y - x < 1`, `-1 < x < 1`, `-1 < y < 1`. -/
theorem armC_step_far_one (j : ℕ) (hn : nearC j = false) (hk : (kC j : ℝ) = 1) (x y : ℝ)
    (hyx0 : 0 < y - x) (hyx1 : y - x < 1) (hx0 : -1 < x) (hx1 : x < 1)
    (hy0 : -1 < y) (hy1 : y < 1) :
    armStepOf nearC kC j (x, y) = ((1 - y) / 2, (1 - x) / 2) := by
  have hnt : ¬ (nearC j = true) := by rw [hn]; decide
  have hfx : Int.fract (y - x) = y - x := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  have hf1 : Int.fract (-(x + (y - x)) / 2 + 1 / 2) = (1 - y) / 2 := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  have hf2 : Int.fract (-x / 2 + 1 / 2) = (1 - x) / 2 := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) 0 ?_
    ring
  simp only [armStepOf, armArcOf, Work.EL.arcLen, ite_eq_right hnt, hk, hfx, hf1, hf2]

/-- The `FAR`, `k = 0` normal form of `armStepOf` with `fract (y - x) = y - x + 1`, valid on the
box `-1 < y - x < 0`, `0 < x < 2`, `-1 < y < 1`. -/
theorem armC_step_far_zero_sub (j : ℕ) (hn : nearC j = false) (hk : (kC j : ℝ) = 0) (x y : ℝ)
    (hyx0 : y - x < 0) (hyx1 : -1 < y - x) (hx0 : 0 < x) (hx2 : x < 2)
    (hy0 : -1 < y) (hy1 : y < 1) :
    armStepOf nearC kC j (x, y) = ((1 - y) / 2, 1 - x / 2) := by
  have hnt : ¬ (nearC j = true) := by rw [hn]; decide
  have hfx : Int.fract (y - x) = y - x + 1 := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf1 : Int.fract (-(x + (y - x + 1)) / 2) = (1 - y) / 2 := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  have hf2 : Int.fract (-x / 2) = 1 - x / 2 := by
    refine armC_fract_eq_of_sub _ _ (by linarith) (by linarith) (-1) ?_
    ring
  simp only [armStepOf, armArcOf, Work.EL.arcLen, ite_eq_right hnt, hk, zero_div, add_zero,
    hfx, hf1, hf2]

theorem armChainC_norm (a b : ℝ) (h1 : 37 / 63 ≤ a) (h2 : a ≤ 821 / 1023)
    (h3 : 326 / 1023 ≤ b) (h4 : b ≤ 22 / 63) :
    Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (a, b) 6
      = (22 / 63 + (b - 22 / 63) / 64, 37 / 63 + (a - 37 / 63) / 64) := by
  have hexp : armPairOf nearC kC (a, b) 6
      = armStepOf nearC kC 0 (armStepOf nearC kC 1 (armStepOf nearC kC 2
        (armStepOf nearC kC 3 (armStepOf nearC kC 4 (armStepOf nearC kC 5 (a, b)))))) := rfl
  -- j = 5, FAR, k = 1
  have e5 : armStepOf nearC kC 5 (a, b) = (1 - b / 2, (1 - a) / 2) :=
    armC_step_far_one_sub 5 (by decide) (armC_kC_cast_one (j := 5) (by decide)) a b
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  -- j = 4, FAR, k = 0
  have e4 : armStepOf nearC kC 4 (1 - b / 2, (1 - a) / 2) = (a / 4 + 1 / 4, b / 4 + 1 / 2) := by
    have h := armC_step_far_zero_sub 4 (by decide) (armC_kC_cast_zero (j := 4) (by decide))
      (1 - b / 2) ((1 - a) / 2) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [h]
    refine Prod.ext ?_ ?_ <;> ring
  -- j = 3, FAR, k = 1
  have e3 : armStepOf nearC kC 3 (a / 4 + 1 / 4, b / 4 + 1 / 2) = (1 / 4 - b / 8, 3 / 8 - a / 8) := by
    have h := armC_step_far_one 3 (by decide) (armC_kC_cast_one (j := 3) (by decide))
      (a / 4 + 1 / 4) (b / 4 + 1 / 2) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [h]
    refine Prod.ext ?_ ?_ <;> ring
  -- j = 2, FAR, k = 1
  have e2 : armStepOf nearC kC 2 (1 / 4 - b / 8, 3 / 8 - a / 8) = (5 / 16 + a / 16, 3 / 8 + b / 16) := by
    have h := armC_step_far_one 2 (by decide) (armC_kC_cast_one (j := 2) (by decide))
      (1 / 4 - b / 8) (3 / 8 - a / 8) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [h]
    refine Prod.ext ?_ ?_ <;> ring
  -- j = 1, NEAR, k = 1
  have e1 : armStepOf nearC kC 1 (5 / 16 + a / 16, 3 / 8 + b / 16)
      = (27 / 32 - a / 32, 5 / 16 - b / 32) := by
    have h := armC_step_near_one_sub 1 (by decide) (armC_kC_cast_one (j := 1) (by decide))
      (5 / 16 + a / 16) (3 / 8 + b / 16) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [h]
    refine Prod.ext ?_ ?_ <;> ring
  -- j = 0, FAR, k = 0
  have e0 : armStepOf nearC kC 0 (27 / 32 - a / 32, 5 / 16 - b / 32)
      = (11 / 32 + b / 64, 37 / 64 + a / 64) := by
    have h := armC_step_far_zero_sub 0 (by decide) (armC_kC_cast_zero (j := 0) (by decide))
      (27 / 32 - a / 32) (5 / 16 - b / 32) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
    rw [h]
    refine Prod.ext ?_ ?_ <;> ring
  rw [hexp, e5, e4, e3, e2, e1, e0]
  refine Prod.ext ?_ ?_ <;> ring



end Work.ELNest
