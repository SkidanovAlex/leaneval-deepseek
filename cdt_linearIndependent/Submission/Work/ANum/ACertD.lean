import Mathlib
import Submission.Work.ANum.ACert
import Submission.Work.ANum.isqrtSpec

/-! # Area ANum — the derivative / logarithm layers of the arc certificate

The naive rectangle evaluation of the five-stage contour `psiA` inflates boxes by a factor ~10⁴
(cancellation in `A - B·w + A·w²`), which is fatal for the `h`-logarithm bound.  The certificate
therefore uses

* the *mean value inequality*: `psiA z` lies in the ball of radius `M·‖z - c‖` about `psiA c`,
  where `M` bounds `‖psiA'‖` on the rectangle and `c` is the rectangle's centre — so the *value* is
  only needed at a point (where the rectangle chain is essentially exact), and
* the same `M` for the derivative term `|d/dt log|h(psiA(c_k e^{2πit}))|| ≤ |h'/h|·M·2πc_k`.

All definitions are computable integer data; the soundness lemmas live in sibling modules.
-/

namespace Work.ANum

open Submission.CDTPlan Complex

/-! ## Mantissa helpers -/

/-- Upper mantissa bound of `√(n)/SC`. -/
def sqrtUp (n : ℤ) : ℤ := (isqrt n.toNat : ℤ) + 1
/-- Lower mantissa bound of `√(n)/SC`. -/
def sqrtDn (n : ℤ) : ℤ := (isqrt n.toNat : ℤ)
/-- Upper mantissa bound of the product of the values `a/SC`, `b/SC`. -/
def mulUp (a b : ℤ) : ℤ := -Int.ediv (-(a * b)) SC
/-- Lower mantissa bound of the product of the values `a/SC`, `b/SC`. -/
def mulDn (a b : ℤ) : ℤ := Int.ediv (a * b) SC
/-- Upper mantissa bound of the quotient of the values `a/SC`, `b/SC`. -/
def divUp (a b : ℤ) : ℤ := -Int.ediv (-(a * SC)) b
/-- `max |x|` over `[a,b]`, as a mantissa. -/
def maxAbs (a b : ℤ) : ℤ := max a.natAbs b.natAbs
/-- `min |x|` over `[a,b]` (0 when the interval contains 0), as a mantissa. -/
def minAbs (a b : ℤ) : ℤ := if a ≤ 0 ∧ 0 ≤ b then 0 else min a.natAbs b.natAbs

/-- Upper mantissa bound for `‖z‖`, `z ∈ D`. -/
def absUp (D : CD) : ℤ := sqrtUp (maxAbs D.re.lo D.re.hi ^ 2 + maxAbs D.im.lo D.im.hi ^ 2)
/-- Lower mantissa bound for `‖z‖`, `z ∈ D`. -/
def absDn (D : CD) : ℤ := sqrtDn (minAbs D.re.lo D.re.hi ^ 2 + minAbs D.im.lo D.im.hi ^ 2)
/-- Lower mantissa bound for `‖z - (a + b i)‖`, `z ∈ D`. -/
def distDn (D : CD) (a b : ℤ) : ℤ :=
  sqrtDn (minAbs (D.re.lo - a) (D.re.hi - a) ^ 2 + minAbs (D.im.lo - b) (D.im.hi - b) ^ 2)
/-- Upper mantissa bound for `‖z - (a + b i)‖`, `z ∈ D`. -/
def distUp (D : CD) (a b : ℤ) : ℤ :=
  sqrtUp (maxAbs (D.re.lo - a) (D.re.hi - a) ^ 2 + maxAbs (D.im.lo - b) (D.im.hi - b) ^ 2)

/-! ## The derivative of the contour stages -/

/-- The Joukowski coefficient `α = (1+r)²/(4r)`, as an upper mantissa: `(p/q)·SC` rounded up. -/
def ratUp (p q : ℕ) : ℤ := ((p * SC.toNat + q - 1) / q : ℤ)

/-- Upper mantissa bound for `|slit r '(w)|` when `w ∈ D` and `slit r w ∈ U`:
`|slit'| = α·|w²-1|·|u|²/(|w|²·|u²-1|)`, `u = slit r w` (from the Joukowski relation
`u + u⁻¹ = α(w + w⁻¹) + β`). -/
def slitDerBnd (αhi : ℤ) (D U : CD) : ℤ :=
  divUp (mulUp (mulUp αhi (distUp (D.mul D) SC 0)) (mulUp (absUp U) (absUp U)))
    (mulDn (mulDn (absDn D) (absDn D)) (distDn (U.mul U) SC 0))

/-- The lune constants `B = 1+c² = 1321/25`, `C = c²-1 = 1271/25`. -/
def lB : Iv := ratIv 1321 25
def lC : Iv := ratIv 1271 25
/-- `BC = B·C = 1678991/625`, `2C² = 3230882/625`. -/
def lBC : Iv := ratIv 1678991 625
def l2C2 : Iv := ratIv 3230882 625

/-- Upper mantissa bound for `|lune c '(z)|` when `z ∈ D` and `lune c z ∈ U`:
`lune' = 1/luneF' = (C+Bw)²/(BC(1+w²)+2C²w)`. -/
def luneDerBnd (U : CD) : ℤ :=
  divUp (mulUp (absUp ((cst lC).add ((cst lB).mul U))) (absUp ((cst lC).add ((cst lB).mul U))))
    (absDn (((cst lBC).mul ((cst (Iv.pt SC)).add (U.mul U))).add ((cst l2C2).mul U)))

/-- The four Joukowski coefficients `α_j = (1+r_j)²/(4r_j)` as upper mantissas. -/
def a1up : ℤ := ratUp 361 360
def a2up : ℤ := ratUp 1008016 947500
def a3up : ℤ := ratUp 3697929 3365000
def a4up : ℤ := ratUp 305795169 299480000

/-- `⌈(4/5)·(491/500)·SC⌉ = ⌈491/625·SC⌉`. -/
def f5up : ℤ := ratUp 491 625

/-- Upper mantissa bound for `‖psiA' z‖`, `z ∈ D`. -/
def psiADerBnd (D : CD) : ℤ :=
  let D0 := S491.mul D
  let U1 := slitEncl cA1 cB1 cE1 cC1 cG1 D0
  let D1 := RW1.mul U1
  let U2 := slitEncl cA2 cB2 cE2 cC2 cG2 D1
  let D2 := RW2.mul U2
  let U3 := slitEncl cA3 cB3 cE3 cC3 cG3 D2
  let D3 := RW3.mul U3
  let U4 := slitEncl cA4 cB4 cE4 cC4 cG4 D3
  let D4 := RW4.mul U4
  mulUp f5up
    (mulUp (slitDerBnd a1up D0 U1)
      (mulUp (slitDerBnd a2up D1 U2)
        (mulUp (slitDerBnd a3up D2 U3)
          (mulUp (slitDerBnd a4up D3 U4) (luneDerBnd D4.neg)))))


/-! ## The logarithm layer for the certificate

`log x` for `x ∈ [1/5, 3]` is `2·atanh((x-1)/(x+1))` with `|(x-1)/(x+1)| ≤ 2/3`; the Taylor
polynomial of `Iv.logSum` plus the geometric tail `2(2/3)^{2K+1}/((2K+1)(1-4/9))` encloses it.
(The range `[1/2,2]` of `Iv.logTail` is too narrow: the arguments of the `h`-logarithm series are
as small as `1-|q| ≥ 1/5`.) -/

/-- The interval `(X-1)/(X+1)`. -/
def logV (X : Iv) : Iv := (X.sub (Iv.pt SC)).mul ((X.add (Iv.pt SC)).invPos)

/-- Mantissa bound for `2(2/3)^{2K+1}/((2K+1)(1-4/9))`. -/
def logTail2N (K : ℕ) : ℤ :=
  Int.ediv (18 * SC * 2 ^ (2 * K + 1)) (5 * ((2 * K + 1) * 3 ^ (2 * K + 1))) + 1

/-- The tail interval `[-logTail2N K, logTail2N K]/SC`. -/
def logTail2 (K : ℕ) : Iv := ⟨-(logTail2N K), logTail2N K⟩

/-- Upper mantissa bound of `log x` for `x ∈ X`, `X ⊆ [1/5, 3]` (no range reduction). -/
def logUp (X : Iv) (K : ℕ) : ℤ := ((Iv.logSum (logV X) K).add (logTail2 K)).hi

/-- The mantissa-scaled interval `X·2^k`. -/
def scaledIv (X : Iv) (k : ℕ) : Iv := ⟨X.lo * 2 ^ k, X.hi * 2 ^ k⟩

/-- Upper mantissa bound of `log x` for `x ∈ X` after a range reduction by `2^k`
(`log x = log (x·2^k) - k·log 2 ≤ logUp (X·2^k) - k·⌊log 2⌋`). -/
def logUpScaled (X : Iv) (k : ℕ) : ℤ := logUp (scaledIv X k) 16 - (k : ℤ) * 744261117


/-! ## The `h`-logarithm bound at a point -/

/-- `j`-fold product of a rectangle (for the powers `q₀^n` of the centre `q₀`). -/
def cpow (c : CD) : ℕ → CD
  | 0 => ONE
  | (n + 1) => (cpow c n).mul c

/-- Upper mantissa bound for `‖1 + q^{n+1}‖`, `|q| ≤ R`. -/
def onePlusPowUp (a b : ℤ) (R : ℤ) (n : ℕ) : ℤ := absUp ((cpow (CD.pt a b) (n + 1)).add ONE)

/-! ## The `h`-logarithm bound, the `|h'/h|` bound and the final per-arc mantissa -/

/-- `n`-fold product of the *value* `R/SC`, as a mantissa. -/
def powUp (R : ℤ) : ℕ → ℤ
  | 0 => SC
  | (n + 1) => mulUp (powUp R n) R

/-- Division of a mantissa by a natural number (rounding up). -/
def divNatUp (a : ℤ) (n : ℕ) : ℤ := -Int.ediv (-a) (n : ℤ)

/-- The `n`-th logarithm argument of the `h`-logarithm bound: an upper bound of `‖1 + q^{n+1}‖`
at the centre plus the radius contribution `(n+1)·R^n·rm` (`R` = the mantissa of `‖q₀‖ + rm`). -/
def hArg (a b rm : ℤ) (n : ℕ) : Iv :=
  let t := onePlusPowUp a b (absUp (CD.pt a b) + rm) n
    + ((n : ℤ) + 1) * mulUp (powUp (absUp (CD.pt a b) + rm) n) rm
  ⟨t, t⟩

/-- The upper mantissa bound of the right-hand side of `Work.ANum.h_log_bound` for a ball of
centre `(a+bi)/SC` and radius `rm/SC`, with `M` series terms (the logarithm of 256 is
`8·log 2 ≤ 5954088944`). -/
def hBnd (a b rm : ℤ) (M : ℕ) (kS : ℕ) : ℤ :=
  let s := absUp (CD.pt a b)
  let R := s + rm
  5954088944 + logUpScaled ⟨s + rm, s + rm⟩ kS
    + 24 * ((List.range M).foldl (fun acc n => acc + logUp (hArg a b rm n) 16) 0)
    + 24 * divUp (powUp R (M + 1)) (SC - R)

/-- `24·Σ_{n<M} (n+1) q^n/(1+q^{n+1})`, as a complex rectangle. -/
def hGradSum (q : CD) : ℕ → CD → CD → CD
  | 0, _, acc => acc
  | (n + 1), qp, acc =>
      let t1 := qp.mul (cst (Iv.pt (((n : ℤ) + 1) * SC)))
      let t2 := (ONE.add (qp.mul q)).inv
      hGradSum q n (qp.mul q) (acc.add (t1.mul t2))

/-- **Corrected log-derivative sum** `Σ_{i<M} (i+1)·q^i/(1+q^{i+1})` at a point.

NOTE: the sibling `hGradSum` above is *wrong*: its `(n : ℤ) + 1` uses the countdown `n` as the
coefficient, so it computes `Σ_k (M-k) q^{k+1}/(1+q^{k+2})` — a ~10× overestimate of `|h'/h|`
(measured: median 289/581 for the two big circles instead of the true 21.3/33.5).  This version
carries the index `i` and is the one to use. -/
def hGradSum2 (q : CD) : ℕ → ℕ → CD → CD → CD
  | 0, _, _, acc => acc
  | (fuel + 1), i, qp, acc =>
      let t2 := (ONE.add (qp.mul q)).inv
      let t1 := qp.mul (cst (Iv.pt (((i : ℤ) + 1) * SC)))
      hGradSum2 q fuel (i + 1) (qp.mul q) (acc.add (t1.mul t2))

/-- The triangle tail `24·R^M·((M+1)/(1-R) + R/(1-R)²)/(1-R^{M+1})` of the log-derivative series
(`R` = mantissa of `|q|`), which the finite sum omits. -/
def hGradTail (R : ℤ) (M : ℕ) : ℤ :=
  let q := SC - R
  let p := powUp R M
  let s := divUp (((M : ℤ) + 1) * SC) q + divUp R (mulUp q q)
  mulUp (mulUp (24 * SC) p) (divUp s (SC - powUp R (M + 1)))

/-- Upper mantissa bound of `‖h'/h‖` at the point `(a+bi)/SC`: the complex sum keeps the
cancellation between the `(n+1)q^n/(1+q^{n+1})` terms (the termwise triangle bound is ~14× too
crude), plus the triangle bound for the omitted tail (`M = 60` makes it ~2.4e-3). -/
def hGrad (a b : ℤ) (M : ℕ) : ℤ :=
  absUp (((hGradSum2 (CD.pt a b) M 0 ONE (CD.pt 0 0)).mul (cst (Iv.pt (24 * SC)))).add
    ((CD.pt a b).inv)) + hGradTail (absUp (CD.pt a b)) M

/-- `2π`, as an upper mantissa (`π < 3.1416`). -/
def pi2Up : ℤ := 6746518852

/-- The mantissa of the scaling `c k` (`1/10⁴`, `283/500`, `1`). -/
def ckUp : Fin 3 → ℤ := ![107375, 607737873, SC]

/-- The centre of the point rectangle `inPt k j`, componentwise. -/
def cenA (k : Fin 3) (j : ℕ) : ℤ := ((inPt k j).re.lo + (inPt k j).re.hi) / 2
def cenB (k : Fin 3) (j : ℕ) : ℤ := ((inPt k j).im.lo + (inPt k j).im.hi) / 2

/-- `psiA` evaluated at the *degenerate* box (the centre of `inPt k j`): the rectangle chain is
essentially exact on a point. -/
def qCen (k : Fin 3) (j : ℕ) : CD := psiAEnclA (CD.pt (cenA k j) (cenB k j))

/-- The half-diagonal (plus one) of the point rectangle, as a mantissa: the `M`-bound of the mean
value inequality is multiplied by it. -/
def radPt (k : Fin 3) (j : ℕ) : ℤ :=
  divNatUp (3 * (max (((inPt k j).re.hi - (inPt k j).re.lo) / 2 + 1)
    (((inPt k j).im.hi - (inPt k j).im.lo) / 2 + 1))) 2

/-- The radius of the ball around the point value that still contains `psiA` on the arc. -/
def radArc (k : Fin 3) (j : ℕ) : ℤ := mulUp (psiADerBnd (inArc k j)) (radPt k j) + 1

/-- The centre of the *image* box `qCen k j` (the point value of `psiA`). -/
def qcA (k : Fin 3) (j : ℕ) : ℤ := ((qCen k j).re.lo + (qCen k j).re.hi) / 2
def qcB (k : Fin 3) (j : ℕ) : ℤ := ((qCen k j).im.lo + (qCen k j).im.hi) / 2

/-- The range-reduction exponent for the `log (‖q₀‖+ρ)` term: the `k = 0` circle has
`|psi_A| ≈ 6.3·10⁻⁵`, so its argument must be scaled by `2¹⁴` to reach `[1/5,3]`. -/
def kSc : Fin 3 → ℕ := ![14, 0, 0]

/-- The final per-arc mantissa bound: the `h`-logarithm bound at the point value (centre `qCen`)
with the mean-value radius `radArc`, plus the derivative term
`|h'/h|·sup|psiA'|·2π·c_k/NARC`. -/
def G (k : Fin 3) (j : ℕ) : ℤ :=
  hBnd (qcA k j) (qcB k j) (radArc k j) 30 (kSc k)
    + divNatUp (mulUp (mulUp (hGrad (qcA k j) (qcB k j) 60) (psiADerBnd (inArc k j)))
        (mulUp pi2Up (ckUp k))) NARC


/-! ## U-free derivative bound and the mean-value-linearised chain

The raw rectangle chain inflates by ~5x per stage over an *arc* box, which makes the `U`-based
`slitDerBnd` degenerate (`|u^2-1| = 0`).  Two devices fix this: the Joukowski relation gives
`|slit'(w)|` from the *input* box alone, and each stage is re-enclosed by the mean value inequality
(point value at the centre + a ball of radius `|slit'|*rad(D)`). -/

/-- The centre of a rectangle, as a point rectangle. -/
def cenPt (D : CD) : CD := CD.pt ((D.re.lo + D.re.hi) / 2) ((D.im.lo + D.im.hi) / 2)

/-- The half-diagonal of `D` (plus one), as a mantissa. -/
def radOf (D : CD) : ℤ :=
  divNatUp (3 * max ((D.re.hi - D.re.lo) / 2 + 1) ((D.im.lo - D.im.hi) / 2 + 1)) 2

/-- The closed ball `{|z| ≤ r/SC}` as a rectangle. -/
def ballCD (r : ℤ) : CD := ⟨⟨-r, r⟩, ⟨-r, r⟩⟩

/-- `γ = α(w + w⁻¹) + β`, the Joukowski quantity of a slit stage, over a box. -/
def gammaBox (α β : Iv) (D : CD) : CD := ((cst α).mul (D.add D.inv)).add (cst β)

/-- Upper mantissa bound of `|slit r '(w)|` for `w ∈ D`, from the Joukowski relation only
(`γ = α(w+w⁻¹)+β`, `|u - 1/u| = √|γ²-4|`, `|u| ≤ (|γ|+√max(γ²-4,0))/2`). -/
def slitDerBnd2 (αhi : ℤ) (α β : Iv) (D : CD) : ℤ :=
  let g := gammaBox α β D
  let gu := absUp g
  let sd := sqrtUp (max (gu * gu - 4 * SC * SC) 0)
  let uu := max SC ((gu + sd) / 2)
  let gl := distDn (g.mul g) 0 0
  let gt := absUp (g.mul g)
  let dl := sqrtDn (SC * max (max (4 * SC - gt) (gl - 4 * SC)) 0)
  divUp (mulUp (mulUp αhi (distUp (D.mul D) SC 0)) uu)
    (mulDn (mulDn (absDn D) (absDn D)) dl)

/-- MVT-linearised enclosure of one slit stage over `D`. -/
def slitEnclLin (A B E C G : Iv) (α β : Iv) (αhi : ℤ) (D : CD) : CD :=
  (slitEncl A B E C G (cenPt D)).add (ballCD (mulUp (slitDerBnd2 αhi α β D) (radOf D) + 1))

/-- The Joukowski constants `α_j = (1+r_j)²/(4r_j)`, `β_j = -(r_j-1)²/(2r_j)`. -/
def al1 : Iv := ratIv 361 360
def be1 : Iv := ratIv (-1) 180
def al2 : Iv := ratIv 1008016 947500
def be2 : Iv := ratIv (-30258) 236875
def al3 : Iv := ratIv 3697929 3365000
def be3 : Iv := ratIv (-332929) 1682500
def al4 : Iv := ratIv 305795169 299480000
def be4 : Iv := ratIv (-6315169) 149740000

/-- Upper mantissa bound for `‖psiA' z‖`, `z ∈ D`, using the linearised stage boxes. -/
def psiADerBnd2 (D : CD) : ℤ :=
  let D0 := S491.mul D
  let U1 := slitEnclLin cA1 cB1 cE1 cC1 cG1 al1 be1 a1up D0
  let D1 := RW1.mul U1
  let U2 := slitEnclLin cA2 cB2 cE2 cC2 cG2 al2 be2 a2up D1
  let D2 := RW2.mul U2
  let U3 := slitEnclLin cA3 cB3 cE3 cC3 cG3 al3 be3 a3up D2
  let D3 := RW3.mul U3
  let U4 := slitEnclLin cA4 cB4 cE4 cC4 cG4 al4 be4 a4up D3
  let D4 := RW4.mul U4
  mulUp f5up
    (mulUp (slitDerBnd2 a1up al1 be1 D0)
      (mulUp (slitDerBnd2 a2up al2 be2 D1)
        (mulUp (slitDerBnd2 a3up al3 be3 D2)
          (mulUp (slitDerBnd2 a4up al4 be4 D3)
            (luneDerBnd (luneEncl cBl cC2l cDcl D4.neg))))))

end Work.ANum
