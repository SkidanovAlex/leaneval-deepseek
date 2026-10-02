/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# `Work.SeedCert.d1Chart`: the square-root enclosure test (D1) of the ray chain

This is the Boolean checker of `NOTES_LEAD_mandelbar_noncusp.md` §2.4, condition **(D1)**: for a
box `B` of a ray segment at level `k` (in the `q`-variable), the parameter box `X` and a box `C`
of the corresponding piece of the ray at level `k+1` (in the `u`-variable) it certifies

  `∀ q ∈ B, ∀ c ∈ X, ∀ u, T_c u = q → u ∈ C ∨ -u ∈ C`,

i.e. that the preimage of `B` under `T_c(z) = z̄² + c` lies in `C ∪ (-C)`.  This is the one
nonlinear step of the interval pull-back chain: it turns an enclosure of the level-`k` segment
into an enclosure of the level-`k+1` segment.

## How the test works

Write `v = conj u` and `w = v² = q - c`, so that `w` runs over `W = B - X`.  The two square roots
of `w` are `±v`; write `a = Re v`, `b = Im v`, `x = Re w`, `y = Im w`.  Then

* `a² = (‖w‖ + x)/2`, `b² = (‖w‖ - x)/2`.

On the box `W = [x₁,x₂] × [y₁,y₂]` put `M = max |y|` and `m = min |y|`.  The functions
`‖w‖ + x` and `‖w‖ - x` are monotone in each variable (increasing in `x` respectively decreasing,
and increasing in `|y|`), so their extrema over the box are:

* `max (‖w‖ + x) = √(x₂² + M²) + x₂`, `min (‖w‖ + x) = √(x₁² + m²) + x₁`,
* `max (‖w‖ - x) = √(x₁² + M²) - x₁`.

Each square root is eliminated by *squaring*: the generator supplies dyadics
`U ≥ √(x₂² + M²)`, `V ≥ √(x₁² + M²)`, `L ≤ √(x₁² + m²)` and the kernel checks
`x₂² + M² ≤ U²`, `x₁² + M² ≤ V²`, `L² ≤ x₁² + m²`.  The four comparison conditions of `d1Chart`
are then
`U + x₂ ≤ 2·P.rhi²` (`|a| ≤ P.rhi`), `V - x₁ ≤ 2·P.ihi²` (`|b| ≤ P.ihi`) and
`2·P.rlo² ≤ L + x₁` (`|a| ≥ P.rlo`), together with `0 < P.rlo ≤ P.rhi` and `0 < P.ihi`.  Note the
direction of the `L` condition: `L` is a *lower* witness, `L² ≤ x₁² + m²`.

Note that *no orientation hypothesis* on `Im w` is used: unlike an earlier design of this test,
the emitted box `symBox P = [P.rlo,P.rhi] × [-P.ihi,P.ihi]` is symmetric in its imaginary part, so
the conclusion `v ∈ C ∨ -v ∈ C` holds for *both* square roots regardless of the sign of `Im w`
(the four sign combinations `(±|a|, ±|b|)` are all in `C ∪ (-C)` when `|a| ∈ [P.rlo,P.rhi]` and
`|b| ≤ P.ihi`).  This matters: the ray of `α₁` genuinely crosses the line `Im z = Im c` at some
levels, and a test requiring `Im w ≠ 0` would be obstructed there.

## Structure

* `symBox P` — the emitted box of a chart box, conjugation-invariant, in the right half-plane.
* `d1Chart W P U V L` — the core test.
* `D1Ent` — one entry of the chain datum: the upper box `B`, the chart box `P`, the three
  square-root witnesses.
* `d1EntOk X e`, `d1AllOk X l` — the test of one entry / of a list.
* `coverOf l` — the emitted cover boxes `symBox e.P` of a list of entries.

The soundness statements are `d1Chart_sound` and `d1EntOk_sound`, proved in
`Submission/Work/SeedCertNum/`.
-/
import ChallengeDeps
import Submission.Work.SeedCertNum.Box

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

/-- The **emitted box** of a chart box `P`: `[P.rlo,P.rhi] × [-P.ihi,P.ihi]`.  It is invariant
under complex conjugation and, when `P.rlo > 0`, lies in the open right half-plane. -/
def symBox (P : CBox) : CBox := ⟨P.rlo, P.rhi, Dya.neg P.ihi, P.ihi⟩

theorem symBox_conj (P : CBox) : (symBox P).conj = symBox P := by
  simp only [symBox, CBox.conj, Dya.neg_neg]

/-- The **core square-root enclosure test** (D1): `W` is a box of `w = v²`, `P` a first-quadrant
box intended to contain `(|Re v|, |Im v|)`, and `U`, `V`, `L` the generator's square-root
witnesses. -/
def d1Chart (W P : CBox) (U V L : Dya) : Bool :=
  Dya.pos P.rlo && Dya.le P.rlo P.rhi && Dya.pos P.ihi && Dya.nonneg L &&
  (let M := Dya.maxAbs W.ilo W.ihi
   let m := Dya.minAbs W.ilo W.ihi
   Dya.le (Dya.add U W.rhi) (Dya.twice (Dya.mul P.rhi P.rhi)) &&
   Dya.le (Dya.sub V W.rlo) (Dya.twice (Dya.mul P.ihi P.ihi)) &&
   Dya.le (Dya.twice (Dya.mul P.rlo P.rlo)) (Dya.add L W.rlo) &&
   Dya.le (Dya.add (Dya.mul W.rhi W.rhi) (Dya.mul M M)) (Dya.mul U U) &&
   Dya.le (Dya.add (Dya.mul W.rlo W.rlo) (Dya.mul M M)) (Dya.mul V V) &&
   Dya.le (Dya.mul L L) (Dya.add (Dya.mul W.rlo W.rlo) (Dya.mul m m)))

/-- The **emitted box of the second shape**: `[-P.rhi,P.rhi] × [P.ilo,P.ihi]`, tight in the
imaginary part and symmetric in the real part.  It is used when the preimage lies near the
imaginary axis (which happens when the level-`k` segment lies in the left half-plane), where
`symBox` would have to contain the origin. -/
def symBoxIm (P : CBox) : CBox := ⟨Dya.neg P.rhi, P.rhi, P.ilo, P.ihi⟩

/-- The **second square-root enclosure test** (D1''): like `d1Chart`, but the emitted box is
`symBoxIm P`, so the lower bound that has to be certified is the one on `|Im v|`, via the witness
`L'` with `L'² ≤ W.rhi² + m²`. -/
def d1ChartIm (W P : CBox) (U V L' : Dya) : Bool :=
  Dya.pos P.ilo && Dya.le P.ilo P.ihi && Dya.pos P.rhi && Dya.nonneg L' &&
  (let M := Dya.maxAbs W.ilo W.ihi
   let m := Dya.minAbs W.ilo W.ihi
   Dya.le (Dya.add U W.rhi) (Dya.twice (Dya.mul P.rhi P.rhi)) &&
   Dya.le (Dya.sub V W.rlo) (Dya.twice (Dya.mul P.ihi P.ihi)) &&
   Dya.le (Dya.twice (Dya.mul P.ilo P.ilo)) (Dya.sub L' W.rhi) &&
   Dya.le (Dya.add (Dya.mul W.rhi W.rhi) (Dya.mul M M)) (Dya.mul U U) &&
   Dya.le (Dya.add (Dya.mul W.rlo W.rlo) (Dya.mul M M)) (Dya.mul V V) &&
   Dya.le (Dya.mul L' L') (Dya.add (Dya.mul W.rhi W.rhi) (Dya.mul m m)))

/-- The **tight square-root enclosure test** (D1'): when `Im w` has a definite sign `s` on `W`,
the two square roots of `w` have the *same* coordinate-sign pattern, so the emitted box can be
tight in both coordinates.  The emitted box (in the `u`-variable, see `tightBox`) is the
fourth-quadrant box for `s = true` and the first-quadrant box for `s = false`. -/
def d1Tight (W P : CBox) (U V L L2 : Dya) (s : Bool) : Bool :=
  Dya.pos P.rlo && Dya.pos P.ilo && Dya.le P.rlo P.rhi && Dya.le P.ilo P.ihi &&
  Dya.nonneg L && Dya.nonneg L2 &&
  (if s then Dya.pos W.ilo else Dya.negb W.ihi) &&
  (let M := Dya.maxAbs W.ilo W.ihi
   let m := Dya.minAbs W.ilo W.ihi
   Dya.le (Dya.add U W.rhi) (Dya.twice (Dya.mul P.rhi P.rhi)) &&
   Dya.le (Dya.sub V W.rlo) (Dya.twice (Dya.mul P.ihi P.ihi)) &&
   Dya.le (Dya.twice (Dya.mul P.rlo P.rlo)) (Dya.add L W.rlo) &&
   Dya.le (Dya.twice (Dya.mul P.ilo P.ilo)) (Dya.sub L2 W.rhi) &&
   Dya.le (Dya.add (Dya.mul W.rhi W.rhi) (Dya.mul M M)) (Dya.mul U U) &&
   Dya.le (Dya.add (Dya.mul W.rlo W.rlo) (Dya.mul M M)) (Dya.mul V V) &&
   Dya.le (Dya.mul L L) (Dya.add (Dya.mul W.rlo W.rlo) (Dya.mul m m)) &&
   Dya.le (Dya.mul L2 L2) (Dya.add (Dya.mul W.rhi W.rhi) (Dya.mul m m)))

/-- The emitted box of the tight test, in the `u`-variable: `s = true` (`Im w > 0` on `W`) gives
the fourth-quadrant box, `s = false` the first-quadrant box. -/
def tightBox (s : Bool) (P : CBox) : CBox :=
  if s then ⟨P.rlo, P.rhi, Dya.neg P.ihi, Dya.neg P.ilo⟩
  else ⟨P.rlo, P.rhi, P.ilo, P.ihi⟩

/-- One entry of the pull-back chain datum of `NOTES_LEAD_mandelbar_noncusp.md` §2.4: the box `B`
of the level-`k` segment, the chart box `P` of the level-`k+1` segment and the square-root
witnesses of `d1Chart` (`L`) and of `d1ChartIm` (`L2`). -/
structure D1Ent where
  B : CBox
  P : CBox
  U : Dya
  V : Dya
  L : Dya
  L2 : Dya
  /-- Which of the four enclosure tests is used: `0` = `d1Chart` (box symmetric in `Im`, only the
  `|Re|` lower bound), `1` = `d1ChartIm` (symmetric in `Re`), `2` = `d1Tight` with `Im w > 0`,
  `3` = `d1Tight` with `Im w < 0`.  The symmetric shapes need no orientation but are fatter; the
  tight shapes are the ones that let the cover track the ray. -/
  shape : Nat
  /-- Whether the emitted box is the negative of the box of the chosen shape.  The enclosure test
  is symmetric in `C` and `-C`; the *cover* needs the sign whose box contains the true preimage. -/
  flip : Bool
deriving DecidableEq, Repr

/-- The box of the chosen shape of an entry, before the sign choice `flip`. -/
def shapeBox (e : D1Ent) : CBox :=
  match e.shape with
  | 0 => symBox e.P
  | 1 => symBoxIm e.P
  | 2 => tightBox true e.P
  | _ => tightBox false e.P

/-- The emitted box of an entry. -/
def emit (e : D1Ent) : CBox := if e.flip then (shapeBox e).neg else shapeBox e

/-- The test of one chain entry.  The nonnegativity of the two *upper* witnesses is tested here
(not in `d1Chart`/`d1ChartIm`/`d1Tight` themselves, which only compare squares): the generator
always emits nonnegative witnesses, and the soundness statements of the three core tests take
their nonnegativity as an explicit hypothesis. -/
def d1EntOk (X : CBox) (e : D1Ent) : Bool :=
  Dya.nonneg e.U && Dya.nonneg e.V &&
  match e.shape with
  | 0 => d1Chart (e.B.sub X) e.P e.U e.V e.L
  | 1 => d1ChartIm (e.B.sub X) e.P e.U e.V e.L2
  | 2 => d1Tight (e.B.sub X) e.P e.U e.V e.L e.L2 true
  | _ => d1Tight (e.B.sub X) e.P e.U e.V e.L e.L2 false

/-- The test of a whole list of chain entries (one per box of the level-`k` cover). -/
def d1AllOk (X : CBox) (l : List D1Ent) : Bool := l.all (fun e => d1EntOk X e)

/-- The emitted cover boxes of a list of entries. -/
def coverOf (l : List D1Ent) : List CBox := l.map (fun e => emit e)

end Work.SeedCert
