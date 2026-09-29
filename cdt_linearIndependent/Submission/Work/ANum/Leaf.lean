import Submission.Work.ANum.psiASEncl_stages
import Submission.Work.ANum.slitEnclS_mem
import Submission.Work.ANum.luneEnclS_mem
import Submission.Work.ANum.disc_selfmap_bound_hyper
import Submission.Work.ANum.HBoxDefs

/-! # The per-arc certificate of conjunct 2 (definitions)

This module assembles the *computable data* of one arc of the Theorem-A certificate:

* the scale-`S` point box `inPtB k j` (`S = 2⁴⁸`) and the five-stage chain `psiASEncl` applied to
  it (`B 0, …, B 5`), converted back to scale `SC` (`toSC`);
* the radius recursion `radStep`/`radRun` of `Work.ANum.rad_recursion` in *integer* form: the
  per-stage data are the modulus bounds of the (converted) chain boxes;
* the final per-arc mantissa `Gval k j`, which is the quantity bounded in the certificate: the
  factorwise `hBnd` at the point box plus the `h`-variation term
  `hGradBox (inflated box) · radius`.

The soundness statement (the claim `circleLog (φ_k) t ≤ m2r (Gval k j)` for `t` in the arc) and the
assembly of `rearrInt … ≤ 112/10` from `Gval` are `Work.ANum.cert_sound` /
`Work.ANum.rearrInt_le` (to be proved). -/

namespace Work.ANum

noncomputable section

open Submission.CDTPlan Complex

/-! ## Conversion between the two scales -/

/-- `⌊n / 2^k⌋`. -/
def toSC (k : ℕ) (n : ℤ) : ℤ := Int.ediv n ((2 : ℤ) ^ k)
/-- `⌈n / 2^k⌉`. -/
def toSCu (k : ℕ) (n : ℤ) : ℤ := -Int.ediv (-n) ((2 : ℤ) ^ k)
/-- Outward rounding of an interval from scale `SC · 2^k` to scale `SC`. -/
def ivToSC (k : ℕ) (I : Iv) : Iv := ⟨toSC k I.lo, toSCu k I.hi⟩
/-- Outward rounding of a rectangle from scale `SC · 2^k` to scale `SC`. -/
def cdToSC (k : ℕ) (D : CD) : CD := ⟨ivToSC k D.re, ivToSC k D.im⟩

/-! ## The certificate constants at scale `S = 2⁴⁸` -/

/-- The high-precision scale: `S = SC · 2¹⁸ = 2⁴⁸`. -/
def SB : ℤ := SCsh 18

@[simp] lemma SB_eq : SB = SC * 2 ^ 18 := rfl

/-- The pre-scaling `491/500` at scale `S`. -/
def S491B : CD := CDHi.cst (IvHi.ratIv SB 491 500)
/-- The four stage rotations at scale `S` (shifted from the `SC` boxes). -/
def RW1B : CD := shCD 18 RW1
def RW2B : CD := shCD 18 RW2
def RW3B : CD := shCD 18 RW3
def RW4B : CD := shCD 18 RW4
/-- The `2π/4096` step at scale `S`. -/
def W4096B : CD := shCD 18 W4096
/-- The circle scalings `c k` at scale `S`. -/
def cKB : Fin 3 → Iv :=
  ![IvHi.ratIv SB 1 10000, IvHi.ratIv SB 283 500, IvHi.ratIv SB 1 1]

/-- A rational constant at scale `S`. -/
def ratB (p : ℤ) (q : ℕ) : Iv := IvHi.ratIv SB p q

/-- The 25 slit/lune constants at scale `S`. -/
def A1B : Iv := ratB 361 100
def B1B : Iv := ratB (-359) 50
def E1B : Iv := ratB 1 50
def C1B : Iv := ratB 19 10
def G1B : Iv := ratB 36 5
def A2B : Iv := ratB 1008016 390625
def B2B : Iv := ratB (-1773968) 390625
def E2B : Iv := ratB 121032 390625
def C2B : Iv := ratB 1004 625
def G2B : Iv := ratB 3032 625
def A3B : Iv := ratB 3697929 1562500
def B3B : Iv := ratB (-3032071) 781250
def E3B : Iv := ratB 332929 781250
def C3B : Iv := ratB 1923 1250
def G3B : Iv := ratB 2692 625
def A4B : Iv := ratB 305795169 100000000
def B4B : Iv := ratB (-293164831) 50000000
def E4B : Iv := ratB 6315169 50000000
def C4B : Iv := ratB 17487 10000
def G4B : Iv := ratB 7487 1250
def BlB : Iv := ratB 1321 25
def C2lB : Iv := ratB 20736 25
def DclB : Iv := ratB 2542 25
def RCB : Iv := ratB (-4) 5

/-! ## The chain of one arc -/

/-- The input box of arc `j` of circle `k` at scale `S`: `c_k · rot (j/4096)`. -/
def inPtB (k : Fin 3) (j : ℕ) : CD :=
  CDHi.mul SB (CDHi.cst (cKB k)) (rotPow2S SB W4096B j)

/-- The output box of the whole chain at scale `S`. -/
def qBoxB (k : Fin 3) (j : ℕ) : CD :=
  psiASEncl SB S491B RW1B RW2B RW3B RW4B
    A1B B1B E1B C1B G1B A2B B2B E2B C2B G2B A3B B3B E3B C3B G3B
    A4B B4B E4B C4B G4B BlB C2lB DclB RCB (inPtB k j)

/-- The five intermediate boxes of the chain at scale `S` (the last one is the output). -/
def stgB (k : Fin 3) (j : ℕ) : Fin 5 → CD :=
  ![sIn1S SB S491B (inPtB k j),
    sIn2S SB S491B RW1B A1B B1B E1B C1B G1B (inPtB k j),
    sIn3S SB S491B RW1B RW2B A1B B1B E1B C1B G1B A2B B2B E2B C2B G2B (inPtB k j),
    sIn4S SB S491B RW1B RW2B RW3B A1B B1B E1B C1B G1B A2B B2B E2B C2B G2B
      A3B B3B E3B C3B G3B (inPtB k j),
    sOut4S SB S491B RW1B RW2B RW3B RW4B A1B B1B E1B C1B G1B A2B B2B E2B C2B G2B
      A3B B3B E3B C3B G3B A4B B4B E4B C4B G4B (inPtB k j)]

/-- The successor index in `Fin n` (identity on the last one). -/
def finSucc {n : ℕ} [NeZero n] (i : Fin n) : Fin n := if h : (i : ℕ) + 1 < n then ⟨i + 1, h⟩ else i

/-- The predecessor index `Fin 6 → Fin 5` (clamped at the first one). -/
def finPred6 (i : Fin 6) : Fin 5 :=
  if h : 0 < (i : ℕ) then ⟨i - 1, by omega⟩ else ⟨0, by norm_num⟩

/-- All six boxes: the input box followed by the five stage boxes, converted to scale `SC`. -/
def boxSC (k : Fin 3) (j : ℕ) : Fin 6 → CD := fun i =>
  if h : (i : ℕ) = 0 then cdToSC 18 (inPtB k j) else cdToSC 18 (stgB k j (finPred6 i))

/-! ## The integer radius recursion -/

/-- Radius of a rectangle: `⌈(3/2)·max(width_re, width_im)⌉` (an upper bound for the Euclidean
radius of the box, in mantissas). -/
def boxRad (D : CD) : ℤ :=
  divNatUp (3 * max (D.re.hi - D.re.lo) (D.im.hi - D.im.lo)) 2

/-- Centre mantissas of a rectangle. -/
def boxCtrA (D : CD) : ℤ := (D.re.lo + D.re.hi) / 2
def boxCtrB (D : CD) : ℤ := (D.im.lo + D.im.hi) / 2

/-- One step of the radius recursion: with `A = 1 - fl²` and `D(r) = 1 - cu(cu + r) - r·fu`
(all in mantissas), return `A·r / D(r)`. -/
def radStep (cu fu fl r : ℤ) : ℤ :=
  let A := SC - mulUp fl fl
  let d := SC - mulUp cu (cu + r) - mulUp r fu
  divUp (mulUp A r) d

/-- The five-stage radius recursion; `cu i` bounds `‖c i‖`, `fu i` bounds `‖f i (c i)‖`,
`fl i` bounds `‖f i (c i)‖` from below, and `e i` is the radius of the `i`-th box. -/
def radRun (cu fu fl e : Fin 6 → ℤ) (r0 : ℤ) : ℤ :=
  let r1 := radStep (cu 0) (fu 0) (fl 0) r0 + e 1
  let r2 := radStep (cu 1) (fu 1) (fl 1) r1 + e 2
  let r3 := radStep (cu 2) (fu 2) (fl 2) r2 + e 3
  let r4 := radStep (cu 3) (fu 3) (fl 3) r3 + e 4
  radStep (cu 4) (fu 4) (fl 4) r4 + e 5

/-- The per-stage data of the recursion, read off the six boxes (at scale `SC`). -/
def cuOf (k : Fin 3) (j : ℕ) : Fin 6 → ℤ := fun i => absUp (boxSC k j i)
/-- Upper bound for `‖f i (c i)‖`. -/
def fuOf (k : Fin 3) (j : ℕ) : Fin 6 → ℤ := fun i => absUp (boxSC k j (finSucc i))
/-- Lower bound for `‖f i (c i)‖`. -/
def flOf (k : Fin 3) (j : ℕ) : Fin 6 → ℤ := fun i => absDn (boxSC k j (finSucc i))
/-- The radius of the `i`-th box. -/
def eOf (k : Fin 3) (j : ℕ) : Fin 6 → ℤ := fun i => boxRad (boxSC k j i)

/-- The input radius of the recursion: the half arc-width `c_k · π/4096` plus the input box radius
(we use the full arc width `c_k · 2π/4096` as a safe upper bound for the half-width). -/
def radIn (k : Fin 3) (j : ℕ) : ℤ :=
  divNatUp (mulUp (ckUp k) pi2Up) NARC + 1 + eOf k j 0

/-- The final radius of the arc image, as a mantissa at scale `SC`. -/
def sigOut (k : Fin 3) (j : ℕ) : ℤ := radRun (cuOf k j) (fuOf k j) (flOf k j) (eOf k j) (radIn k j)

/-! ## The per-arc mantissa bound -/

/-- The point box of the `psiA`-value of the arc, at scale `SC`. -/
def qPtSC (k : Fin 3) (j : ℕ) : CD := boxSC k j 5

/-- The radius of the ball around `qPtSC` that contains `psiA` on the whole arc. -/
def radAll (k : Fin 3) (j : ℕ) : ℤ := boxRad (qPtSC k j) + sigOut k j + 1

/-- The inflated box on which the `|h'/h|` bound is evaluated. -/
def qBallSC (k : Fin 3) (j : ℕ) : CD :=
  sqAround (boxCtrA (qPtSC k j)) (boxCtrB (qPtSC k j)) (radAll k j)

/-- The per-arc mantissa: the factorwise `h`-bound at the point box plus the `h`-variation term. -/
def Gval (k : Fin 3) (j : ℕ) : ℤ :=
  hBnd (boxCtrA (qPtSC k j)) (boxCtrB (qPtSC k j)) (boxRad (qPtSC k j) + 1) 30 (kSc k)
    + mulUp (hGradBox (qBallSC k j) 60) (radAll k j)

end

end Work.ANum
