import Mathlib
import Submission.Work.ANum.Ivl

/-!
# `Work.CNum.Fx` — fixed-point primitives for the CNum certificate

All numbers are integer mantissas at scale `SC = 2^30` (`Work.ANum.SC`), interpreted through
`Work.ANum.m2r n = n / SC`.  Every function below is written with the primitive integer
operations `Int.ediv`, `Int.mul`, ... only, so that the kernel can evaluate them with `decide`.

Contents
* integer square root `isqrt` (binary search), same-scale bounds `sqUp`/`sqDn`, and the
  mantissa-level interval square root `IvS`;
* outward-rounded logarithms `lgUp`/`lgDn` of a mantissa `n ≥ SC` via the artanh series, and
  the endpoint-wise versions `logUpM`/`logDnM`;
* complex intervals `Cpx`, their arithmetic, and the fixed `e^{i k π/1024}` table `expI`;
* the boundary points `psiC (e^{iθ_k})` (`ptC1`, `ptC2`, `ptOf`) and the two cusp values
  (`ptCuspA`, `ptCuspB`);
* the point bounds `PB` (centre + radius) with multiplication, and the series bounds
  `serUp`/`serDn` for `log ‖h (q₀)‖` from an enclosing ball.
-/

namespace Work.CNum

open Work.ANum

/-! ## 1. Integer square root -/

/-- `70`-step binary search for `⌊√n⌋` (valid for `n < 2^70`). -/
def isqAux (n : ℕ) (k lo hi : ℕ) : ℕ :=
  match k with
  | 0 => lo
  | (j + 1) =>
      if ((lo + hi) / 2) * ((lo + hi) / 2) ≤ n then isqAux n j ((lo + hi) / 2) hi
      else isqAux n j lo ((lo + hi) / 2)

/-- Integer square root of `n < 2^70`. -/
def isqrt (n : ℕ) : ℕ := isqAux n 70 0 (n + 1)

/-- Upper bound of `√n` (same units). -/
def sqUp (n : ℤ) : ℤ := ((isqrt n.toNat + 1 : ℕ) : ℤ)
/-- Lower bound of `√n` (same units). -/
def sqDn (n : ℤ) : ℤ := (isqrt n.toNat : ℤ)

/-- Lower endpoint of `√(n/SC)`, as a mantissa: an upper bound of `√(n·SC)`. -/
def sqrtLo (n : ℤ) : ℤ := (isqrt (n.toNat * SC.toNat) : ℤ)
/-- Upper endpoint of `√(n/SC)`, as a mantissa. -/
def sqrtHi (n : ℤ) : ℤ := ((isqrt (n.toNat * SC.toNat) + 1 : ℕ) : ℤ)

/-- Interval square root (for intervals with nonnegative lower endpoint). -/
def IvS (I : Iv) : Iv := ⟨sqrtLo I.lo, sqrtHi I.hi⟩

/-! ## 2. Outward rounding and rational intervals -/

def mulD (a b : ℤ) : ℤ := Int.ediv (a * b) SC
def mulU (a b : ℤ) : ℤ := -Int.ediv (-(a * b)) SC
def divD (a : ℤ) (k : ℕ) : ℤ := Int.ediv a (k : ℤ)
def divU (a : ℤ) (k : ℕ) : ℤ := -Int.ediv (-a) (k : ℤ)
def divUz (a b : ℤ) : ℤ := -Int.ediv (-a) b
def divDz (a b : ℤ) : ℤ := Int.ediv a b

/-- The interval `[⌊p·SC/q⌋, ⌈p·SC/q⌉]` (outer enclosure of `p/q`). -/
def ratIv (p : ℤ) (q : ℕ) : Iv :=
  ⟨Int.ediv (p * SC) (q : ℤ), -Int.ediv (-(p * SC)) (q : ℤ)⟩

/-- Interval product via the four corner products (no cancellation blow-up). -/
def IvM (I J : Iv) : Iv :=
  ⟨min (min (mulD I.lo J.lo) (mulD I.lo J.hi)) (min (mulD I.hi J.lo) (mulD I.hi J.hi)),
   max (max (mulU I.lo J.lo) (mulU I.lo J.hi)) (max (mulU I.hi J.lo) (mulU I.hi J.hi))⟩

/-! ## 3. Logarithms -/

/-- Number of artanh terms. -/
def LOGP : ℕ := 18

/-- `⌈log 2 · SC⌉` (from `Real.log_two_lt_d9`). -/
def LOG2UP : ℤ := 744261119
/-- `⌊log 2 · SC⌋` (from `Real.log_two_gt_d9`). -/
def LOG2DN : ℤ := 744261117

/-- Upper rounding of the artanh variable `v = (x-1)/(x+1)`, `x = n/SC ≥ 1`. -/
def lgvUp (n : ℤ) : ℤ := -Int.ediv (-((n - SC) * SC)) (n + SC)
/-- Lower rounding of the artanh variable. -/
def lgvDn (n : ℤ) : ℤ := Int.ediv ((n - SC) * SC) (n + SC)

/-- `q^m` rounded outward (`up` = true : upward). -/
def powM (up : Bool) (q : ℤ) : ℕ → ℤ
  | 0 => SC
  | (m + 1) => (if up then mulU (powM up q m) q else mulD (powM up q m) q)

/-- Partial artanh sum `2 Σ_{i<P} v^{2i+1}/(2i+1)`, each step rounded outward. -/
def lgSerAux (up : Bool) (v2 : ℤ) : ℕ → ℤ → ℕ → ℤ → ℤ
  | 0, _, _, acc => acc
  | (m + 1), q, i, acc =>
      let term := if up then divU q (2 * i + 1) else divD q (2 * i + 1)
      let q' := if up then mulU q v2 else mulD q v2
      lgSerAux up v2 m q' (i + 1) (acc + term)

def lgSer (v : ℤ) (up : Bool) : ℤ :=
  2 * lgSerAux up (if up then mulU v v else mulD v v) LOGP v 0 0

/-- The artanh tail `2 v^{2P+1}/((2P+1)(1-v²))`, rounded outward. -/
def lgRem (v : ℤ) (up : Bool) : ℤ :=
  let q := powM up v LOGP
  let num := 2 * q * (SC * SC)
  let den := (2 * LOGP + 1) * (SC * SC - v * v)
  if up then -Int.ediv (-num) den else Int.ediv num den

/-- Artanh value `log (m2r n)` for `n ∈ [SC, 2·SC)`, rounded outward. -/
def lgCore (n : ℤ) (up : Bool) : ℤ :=
  if up then lgSer (lgvUp n) true + lgRem (lgvUp n) true else lgSer (lgvDn n) false

/-- Number of halvings needed to bring `n` into `[SC, 2·SC)`. -/
def lgNormAux : ℕ → ℤ → ℕ
  | 0, _ => 0
  | (k + 1), n => if n < 2 * SC then 0 else 1 + lgNormAux k (Int.ediv n 2)

def lgNorm (n : ℤ) : ℕ := lgNormAux 64 n

/-- Repeated halving with upward rounding. -/
def halveU : ℕ → ℤ → ℤ
  | 0, n => n
  | (k + 1), n => halveU k (-Int.ediv (-n) 2)
/-- Repeated halving with downward rounding. -/
def halveD : ℕ → ℤ → ℤ
  | 0, n => n
  | (k + 1), n => halveD k (Int.ediv n 2)

/-- Upper bound of `log (m2r n)`, valid for `SC ≤ n ≤ 4·SC`. -/
def lgUp (n : ℤ) : ℤ :=
  if n < SC then 0 else (lgNorm n : ℤ) * LOG2UP + lgCore (halveU (lgNorm n) n) true + 2
/-- Lower bound of `log (m2r n)`, valid for `SC ≤ n ≤ 4·SC`. -/
def lgDn (n : ℤ) : ℤ :=
  if n < SC then 0 else (lgNorm n : ℤ) * LOG2DN + lgCore (halveD (lgNorm n) n) false - 2

/-- Upper bound of `log x` from an upper endpoint `hi` (mantissa), `hi ≥ SC/4`. -/
def logUpM (hi : ℤ) : ℤ := if SC ≤ hi then lgUp hi else -lgDn (Int.ediv (SC * SC) hi)
/-- Lower bound of `log x` from a lower endpoint `lo` (mantissa), `lo ≥ SC/4`. -/
def logDnM (lo : ℤ) : ℤ :=
  if SC ≤ lo then lgDn lo else -lgUp (-Int.ediv (-(SC * SC)) lo)

/-- Upper bound of `log x` for `x ∈ I` (needs `m2r I.hi > 0`). -/
def logUpIv (I : Iv) : ℤ := logUpM I.hi
/-- Lower bound of `log x` for `x ∈ I` (needs `m2r I.lo > 0`). -/
def logDnIv (I : Iv) : ℤ := logDnM I.lo

/-! ## 4. Complex intervals -/

structure Cpx where
  re : Iv
  im : Iv
  deriving DecidableEq

/-- Membership. -/
def Cpx.Mem (I : Cpx) (z : ℂ) : Prop := I.re.Mem z.re ∧ I.im.Mem z.im

/-- The point `(a + b i)/SC`. -/
def Cpx.pt (a b : ℤ) : Cpx := ⟨⟨a, a⟩, ⟨b, b⟩⟩

def Cpx.add (I J : Cpx) : Cpx := ⟨Iv.add I.re J.re, Iv.add I.im J.im⟩
def Cpx.neg (I : Cpx) : Cpx := ⟨Iv.neg I.re, Iv.neg I.im⟩
def Cpx.sub (I J : Cpx) : Cpx := ⟨Iv.sub I.re J.re, Iv.sub I.im J.im⟩
def Cpx.mul (I J : Cpx) : Cpx :=
  ⟨Iv.sub (IvM I.re J.re) (IvM I.im J.im), Iv.add (IvM I.re J.im) (IvM I.im J.re)⟩

/-- Multiplication by a real interval. -/
def Cpx.mulr (I : Cpx) (r : Iv) : Cpx := ⟨IvM I.re r, IvM I.im r⟩

/-- `-i · I`. -/
def Cpx.mulNegI (I : Cpx) : Cpx := ⟨I.im, Iv.neg I.re⟩

/-- Binary exponentiation `I^n` (`I^0 = 1`). -/
def cpowAux (I : Cpx) : ℕ → Cpx → Cpx
  | 0, acc => acc
  | (n + 1), acc =>
      if (n + 1) % 2 = 1 then cpowAux (Cpx.mul I I) ((n + 1) / 2) (Cpx.mul acc I)
      else cpowAux (Cpx.mul I I) ((n + 1) / 2) acc

def Cpx.pow (I : Cpx) (n : ℕ) : Cpx := cpowAux I n (Cpx.pt SC 0)

/-! ## 5. The trigonometric table `e^{i k π/1024}`

`θ_k = kπ/1024 = q·(π/4) + m·(π/1024)` with `q = k/256`, `m = k % 256 ≤ 255`, so
`mπ/1024 ≤ π/4` and `cos θ_k = cos(qπ/4) cos(mπ/1024) - sin(qπ/4) sin(mπ/1024)`, with
`cos(qπ/4), sin(qπ/4) ∈ {0, ±1, ±√2/2}`.  The remaining angle is evaluated by the Taylor
series of `cos`/`sin` (with `Mathlib`'s remainder bounds `Real.cos_bound`, `Real.sin_bound`). -/

/-- `⌊π·SC⌋` (from `Real.pi_gt_d20`). -/
def piLo : ℤ := 3373259426
/-- `⌈π·SC⌉` (from `Real.pi_lt_d20`). -/
def piHi : ℤ := 3373259427

/-- Interval enclosure of `m·π/1024` (`m ≤ 255`). -/
def angIv (m : ℕ) : Iv :=
  ⟨Int.ediv (m * piLo) 1024, -Int.ediv (-(m * piHi)) 1024⟩

/-- Number of Taylor terms. -/
def TAYN : ℕ := 11

/-- Taylor partial sums: state is `(term_cos, term_sin, sum_cos, sum_sin)`. -/
def tayAux (y2 : Iv) : ℕ → ℕ → Iv → Iv → Iv → Iv → Iv × Iv
  | 0, _, _, _, sc, ss => (sc, ss)
  | (k + 1), i, tc, ts, sc, ss =>
      let tc' := IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2)))
      let ts' := IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3)))
      tayAux y2 k (i + 1) tc' ts' (Iv.add sc tc') (Iv.add ss ts')

/-- `√(1/2)` as an interval. -/
def rt2 : Iv := IvS (ratIv 1 2)

/-- Enclosure of `(cos y, sin y)` for `y = mπ/1024`, `m ≤ 255`. -/
def csOf (m : ℕ) : Cpx :=
  let y := angIv m
  let one := ratIv 1 1
  let r := tayAux (IvM y y) TAYN 0 one y one y
  ⟨r.1, r.2⟩

/-- `cos (q·π/4)`, `q ≤ 4`. -/
def qcos (q : ℕ) : Iv :=
  match q with
  | 0 => ratIv 1 1
  | 1 => rt2
  | 2 => ratIv 0 1
  | 3 => Iv.neg rt2
  | _ => ratIv (-1) 1

/-- `sin (q·π/4)`, `q ≤ 4`. -/
def qsin (q : ℕ) : Iv :=
  match q with
  | 0 => ratIv 0 1
  | 1 => rt2
  | 2 => ratIv 1 1
  | 3 => rt2
  | _ => ratIv 0 1

/-- Enclosure of `e^{i k π/1024}` (`k ≤ 1024`). -/
def expI (k : ℕ) : Cpx :=
  let q := k / 256
  let m := k % 256
  let cs := csOf m
  let c := cs.re
  let s := cs.im
  let qc := qcos q
  let qs := qsin q
  ⟨Iv.sub (IvM qc c) (IvM qs s), Iv.add (IvM qs c) (IvM qc s)⟩

/-! ## 6. The boundary points -/

/-- `2(1+c²) = 629/50`, `2A = 791282/10000`, `γ = 27559/395641`, `1/d = 50/429`,
`c₂ = 629/572`, `ρ₂ = 115/143`, `cos(α/2) = 460/629`, `sin(α/2) = 429/629`. -/
def W1 (k : ℕ) (sgn : ℤ) : Cpx :=
  let E := expI k
  let cosT := Iv.sub (Iv.sq E.re) (Iv.sq E.im)
  let X := IvM (ratIv 791282 10000) (Iv.sub cosT (ratIv 27559 395641))
  let P := IvS X
  let Q := IvM (ratIv 629 50) E.im
  let Pi : Iv := if sgn = 1 then P else Iv.neg P
  Cpx.neg (Cpx.mul (Cpx.mulr ⟨Pi, Q⟩ (ratIv 50 429)) E)

/-- `ψ_C` at `θ_k = 2πk/1024` on the first arc `(-α,α)` (`k ≤ 244`): `(3/4)·W`,
`W = -(P + iQ) e^{it}/d`. -/
def ptC1 (k : ℕ) : Cpx := Cpx.mulr (W1 k 1) (ratIv 3 4)

/-- Same on the fourth arc `(2π-α, 2π)` (`k ≥ 780`), where the principal square root of
`e^{iθ}` is `-e^{iθ/2}`: `W = e^{it}(P - iQ)/d`. -/
def ptC1b (k : ℕ) : Cpx := Cpx.mulr (W1 k (-1)) (ratIv 3 4)

/-- Second arc `(α, 2π-α)` (`245 ≤ k ≤ 779`): `W = i(P' - Q) e^{it}/d`,
`P' = √(2A(γ - cos θ))`. -/
def ptC2 (k : ℕ) : Cpx :=
  let E := expI k
  let cosT := Iv.sub (Iv.sq E.re) (Iv.sq E.im)
  let Y := IvM (ratIv 791282 10000) (Iv.sub (ratIv 27559 395641) cosT)
  let P := IvS Y
  let Q := IvM (ratIv 629 50) E.im
  Cpx.mulr (Cpx.mulr (Cpx.mul ⟨⟨0, 0⟩, Iv.sub P Q⟩ E) (ratIv 50 429)) (ratIv 3 4)

/-- The boundary point `psiC (e^{iθ_k})`, `θ_k = 2πk/1024`. -/
def ptOf (k : ℕ) : Cpx :=
  if k ≤ 244 then ptC1 k else if 780 ≤ k then ptC1b k else ptC2 k
/-- The cusp point at `θ = α`: `(3/4)(σ - i C)`. -/
def ptCuspA : Cpx := Cpx.mulr ⟨ratIv 429 629, ratIv (-460) 629⟩ (ratIv 3 4)

/-- The cusp point at `θ = 2π - α`: `(3/4)(σ + i C)`. -/
def ptCuspB : Cpx := Cpx.mulr ⟨ratIv 429 629, ratIv 460 629⟩ (ratIv 3 4)

/-! ## 7. Balls and the series bounds -/

/-- A complex ball: `‖z - (x + i y)/SC‖ ≤ e/SC`. -/
structure PB where
  x : ℤ
  y : ℤ
  e : ℤ
  deriving DecidableEq

/-- Centre of an interval. -/
def ic (I : Iv) : ℤ := (I.lo + I.hi) / 2

/-- Ball obtained from a complex interval (`3/2 > √2` converts `L∞` to `L²`). -/
def toPB (I : Cpx) : PB :=
  let dx := max (ic I.re - I.re.lo) (I.re.hi - ic I.re)
  let dy := max (ic I.im - I.im.lo) (I.im.hi - ic I.im)
  ⟨ic I.re, ic I.im, (3 * max dx dy) / 2 + 4⟩

/-- Multiplication of balls (centre rounded up, error accumulated). -/
def PB.mul (a b : PB) : PB :=
  let re := -Int.ediv (-(a.x * b.x - a.y * b.y)) SC
  let im := -Int.ediv (-(a.x * b.y + a.y * b.x)) SC
  let e := Int.ediv (Int.natAbs a.x * b.e + Int.natAbs b.x * a.e + Int.natAbs a.y * b.e
      + Int.natAbs b.y * a.e + a.e * b.e) SC + 2
  ⟨re, im, e⟩

/-- Upper bound of `‖(x + i y)/SC‖` (mantissa). -/
def nrmUp (x y : ℤ) : ℤ := sqUp (x * x + y * y)
/-- Lower bound of `‖(x + i y)/SC‖` (mantissa). -/
def nrmDn (x y : ℤ) : ℤ := sqDn (x * x + y * y)

/-- Number of series terms. -/
def SERM : ℕ := 44

/-- Upper bound of `log ‖h q₀‖` given `‖q₀ - (x+iy)/SC‖ ≤ e/SC`.
`px,py` track `c^n`, `pe` its error, `sg` a bound of `σ^n`, `acc` the accumulated series. -/
def serAuxB (bX bY σ e : ℤ) : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  | 0, _, _, _, _, acc => acc
  | (n + 1), px, py, pe, sg, acc =>
      let nrm := nrmUp (SC + px) py
      let hi := nrm + pe + (n + 1) * mulU e sg + 4
      let px' := -Int.ediv (-(px * bX - py * bY)) SC
      let py' := -Int.ediv (-(px * bY + py * bX)) SC
      serAuxB bX bY σ e n px' py' (mulU σ pe + 2) (mulU sg σ) (acc + 24 * logUpM hi)

/-- Upper bound of `log ‖h q₀‖` given a ball of centre `(x+iy)/SC` and radius `e/SC`. -/
def serUp (x y e : ℤ) : ℤ :=
  let σ := nrmUp x y + e
  lgUp (256 * SC) + logUpM σ + serAuxB x y σ e SERM x y 0 SC 0
    + 24 * (divUz (SC * powM true σ (SERM + 1)) (SC - σ)
        + divUz (SC * mulU e ((SERM + 1) * powM true σ SERM)) ((SC - σ) * (SC - σ)) + 4)

/-- Lower bound of `log ‖h q₀‖` given a ball of centre `(x+iy)/SC` and radius `e/SC`. -/
def serDnAux (bX bY σ e : ℤ) : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  | 0, _, _, _, _, acc => acc
  | (n + 1), px, py, pe, sg, acc =>
      let nrm := nrmDn (SC + px) py
      let lo := nrm - pe - (n + 1) * mulU e sg - 4
      let px' := Int.ediv (px * bX - py * bY) SC
      let py' := Int.ediv (px * bY + py * bX) SC
      serDnAux bX bY σ e n px' py' (mulU σ pe + 2) (mulU sg σ) (acc + 24 * logDnM lo)

/-- Lower bound of `log ‖h q₀‖` given a ball of centre `(x+iy)/SC` and radius `e/SC`. -/
def serDn (x y e : ℤ) : ℤ :=
  let σ := nrmUp x y + e
  lgDn (256 * SC) + logDnM (nrmDn x y - e) + serDnAux x y σ e SERM x y 0 SC 0
    - 24 * (2 * divUz (SC * powM true σ (SERM + 1)) (SC - σ) + 4096)


/-! ## 8. Per-arc bounds -/

/-- `max |lo| |hi|` of an interval (mantissa). -/
def absMax (I : Iv) : ℤ := max (Int.natAbs I.lo) (Int.natAbs I.hi)

/-- Upper bound of `‖a - b‖/SC` (mantissa) for two interval points. -/
def distUp (a b : Cpx) : ℤ :=
  let dx := absMax (Iv.sub a.re b.re)
  let dy := absMax (Iv.sub a.im b.im)
  sqUp (dx * dx + dy * dy)

/-- Upper bound of `|ΔW|` in the `W = (4/3)·ψ_C` coordinates. -/
def dWup (a b : Cpx) : ℤ := divU (distUp a b * 4) 3 + 4096

/-- Upper bound of `|ΔV|` in the `V = (ψ_C - c₂)/ρ₂` coordinates. -/
def dVup (a b : Cpx) : ℤ := divU (distUp a b * 143) 115 + 4096

/-- `400·(d + d³/12)²` (mantissa): the `C₁`-arc chord term. -/
def chord1 (d : ℤ) : ℤ :=
  let u := d + divU (mulU (mulU d d) d) 12 + 4096
  mulU (mulU u u) (400 * SC)

/-- `1000·(d + d³/12)²` (mantissa): the `C₂`-arc chord term. -/
def chord2 (d : ℤ) : ℤ :=
  let u := d + divU (mulU (mulU d d) d) 12 + 4096
  mulU (mulU u u) (1000 * SC)

/-- Upper bound of `log ‖h q₀‖` at an interval point. -/
def svUp (p : Cpx) : ℤ := let b := toPB p; serUp b.x b.y b.e
/-- Lower bound of `log ‖h q₀‖` at an interval point. -/
def svDn (p : Cpx) : ℤ := let b := toPB p; serDn b.x b.y b.e

/-- Number of arcs. -/
def NTOT : ℕ := 1024

/-- Upper bound for `circleLog` on the arc `k`. -/
def Gv (k : ℕ) : ℤ :=
  if k ≤ 243 then
    max (svUp (ptOf k)) (svUp (ptOf (k + 1))) + chord1 (dWup (ptOf k) (ptOf (k + 1)))
  else if k = 244 then
    max (max (svUp (ptOf 244)) (svUp ptCuspA)) (max (svUp (ptOf 245)) (svUp ptCuspA))
      + max (chord1 (dWup (ptOf 244) ptCuspA)) (chord2 (dVup (ptOf 245) ptCuspA))
  else if k ≤ 778 then
    max (svUp (ptOf k)) (svUp (ptOf (k + 1))) + chord2 (dVup (ptOf k) (ptOf (k + 1)))
  else if k = 779 then
    max (max (svUp (ptOf 779)) (svUp ptCuspB)) (max (svUp (ptOf 780)) (svUp ptCuspB))
      + max (chord2 (dVup (ptOf 779) ptCuspB)) (chord1 (dWup (ptOf 780) ptCuspB))
  else
    max (svUp (ptOf k)) (svUp (ptOf (k + 1))) + chord1 (dWup (ptOf k) (ptOf (k + 1)))

/-- Lower bound for `circleLog` on the arc `k`. -/
def gv (k : ℕ) : ℤ :=
  if k ≤ 243 then
    min (svDn (ptOf k)) (svDn (ptOf (k + 1))) - chord1 (dWup (ptOf k) (ptOf (k + 1)))
  else if k = 244 then
    min (min (svDn (ptOf 244)) (svDn ptCuspA)) (min (svDn (ptOf 245)) (svDn ptCuspA))
      - max (chord1 (dWup (ptOf 244) ptCuspA)) (chord2 (dVup (ptOf 245) ptCuspA))
  else if k ≤ 778 then
    min (svDn (ptOf k)) (svDn (ptOf (k + 1))) - chord2 (dVup (ptOf k) (ptOf (k + 1)))
  else if k = 779 then
    min (min (svDn (ptOf 779)) (svDn ptCuspB)) (min (svDn (ptOf 780)) (svDn ptCuspB))
      - max (chord2 (dVup (ptOf 779) ptCuspB)) (chord1 (dWup (ptOf 780) ptCuspB))
  else
    min (svDn (ptOf k)) (svDn (ptOf (k + 1))) - chord1 (dWup (ptOf k) (ptOf (k + 1)))

/-- The list of arc upper bounds. -/
def gList : List ℤ := (List.range NTOT).map Gv

/-- `Σ_{k,k'} max (G k) (G k')` (mantissas). -/
def pairSum : ℤ := gList.foldl (fun acc x => gList.foldl (fun a y => a + max x y) acc) 0

/-- Upper bound of `log 700000`. -/
def LOG7E5UB : ℤ := lgUp (7 * SC) + 5 * lgUp (10 * SC)
/-- Lower bound of `log (10⁻¹³)`. -/
def LOG1E13DN : ℤ := -(13 * lgUp (10 * SC))

/-- The final numeric certificate. -/
def certOK : Bool :=
  pairSum * 10 ≤ 102 * (NTOT : ℤ) * (NTOT : ℤ) * SC
    && (List.range NTOT).all (fun k => Gv k ≤ LOG7E5UB && LOG1E13DN ≤ gv k)

end Work.CNum
