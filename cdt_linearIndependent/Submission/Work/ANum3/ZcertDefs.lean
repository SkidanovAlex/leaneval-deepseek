import Submission.Work.ANum.Leaf

/-!
# The certificate data of `phiA_outer_winding` (definitions)

Scale-`SB` (`SB = 2^48`) correctly rounded enclosures of the five rotation constants of the
Theorem-A contour, used by the arc certificate for `φ_A + 1/72` on `|z| = 1`.
The memberships `rot t ∈ (box)` are `Work.ANum3.tightRot_mem`.
-/

namespace Work.ANum3

open Work.ANum Submission.CDTPlan Complex

/-- The certificate scale: `SB = 2⁴⁸`. -/
abbrev S : ℤ := Work.ANum.SB

/-- `rot (1/65536)`, correctly rounded at scale `SB`. -/
def W65536B : Work.ANum.CD :=
  ⟨⟨281474975417027, 281474975417028⟩, ⟨26986075367, 26986075368⟩⟩

/-- `rot (1/4096)`, correctly rounded at scale `SB`. -/
def W4096B2 : Work.ANum.CD :=
  ⟨⟨281474645541751, 281474645541752⟩, ⟨431777037208, 431777037210⟩⟩

/-- `rot (2033/25000)`, correctly rounded at scale `SB`. -/
def RW1B2 : Work.ANum.CD :=
  ⟨⟨245525278619748, 245525278619750⟩, ⟨137642653537916, 137642653537917⟩⟩

/-- `rot (2927/25000)`, correctly rounded at scale `SB`. -/
def RW2B2 : Work.ANum.CD :=
  ⟨⟨208686830050854, 208686830050855⟩, ⟨188886128335539, 188886128335541⟩⟩

/-- `rot (453/12500)`, correctly rounded at scale `SB`. -/
def RW3B2 : Work.ANum.CD :=
  ⟨⟨274209424297833, 274209424297834⟩, ⟨63540177372393, 63540177372394⟩⟩

/-- `rot (-1971/25000)`, correctly rounded at scale `SB`. -/
def RW4B2 : Work.ANum.CD :=
  ⟨⟨247640173730246, 247640173730247⟩, ⟨-133800249884363, -133800249884361⟩⟩


/-! ## Complex interval helpers at scale `S` -/

/-- `D^n` at scale `S`. -/
def powS (S : ℤ) : Work.ANum.CD → ℕ → Work.ANum.CD
  | _, 0 => Work.ANum.CDHi.ONE S
  | D, (n + 1) => Work.ANum.CDHi.mul S D (powS S D n)

/-- `ceil (a * S / b)`. -/
def divUpB (S : ℤ) (a b : ℤ) : ℤ := -Int.ediv (-(a * S)) b

/-- The truncated product `∏_{n=1}^{N} (1 + q^n)`, carrying the running power `q^n`. -/
def hProdAux (S : ℤ) (D : Work.ANum.CD) : ℕ → Work.ANum.CD × Work.ANum.CD → Work.ANum.CD × Work.ANum.CD
  | 0, acc => acc
  | (n + 1), acc =>
      let qq := Work.ANum.CDHi.mul S acc.2 D
      hProdAux S D n (Work.ANum.CDHi.mul S acc.1 (Work.ANum.CDHi.add (Work.ANum.CDHi.ONE S) qq), qq)

/-- `∏_{n=1}^{N} (1 + q^n)` for `q ∈ D`, at scale `S`. -/
def hProd1 (S : ℤ) (D : Work.ANum.CD) (N : ℕ) : Work.ANum.CD :=
  (hProdAux S D N (Work.ANum.CDHi.ONE S, Work.ANum.CDHi.ONE S)).1

/-- The rectangle `-256·q·(∏_{n=1}^{N}(1+q^n))^24` at scale `S`. -/
def hProdB (S : ℤ) (D : Work.ANum.CD) (N : ℕ) : Work.ANum.CD :=
  Work.ANum.CDHi.mul S (Work.ANum.CDHi.cst (Work.ANum.IvHi.pt (-256 * S)))
    (Work.ANum.CDHi.mul S D (powS S (hProd1 S D N) 24))

/-- Inflate a rectangle by a radius (in mantissas). -/
def infl (D : Work.ANum.CD) (r : ℤ) : Work.ANum.CD :=
  ⟨⟨D.re.lo - r, D.re.hi + r⟩, ⟨D.im.lo - r, D.im.hi + r⟩⟩

/-- The rectangle `(∏_{n=1}^{N}(1+q^n))^24` at scale `S`. -/
def hP24 (S : ℤ) (D : Work.ANum.CD) (N : ℕ) : Work.ANum.CD := powS S (hProd1 S D N) 24

/-- The enclosure of `h(q)` for `q ∈ D`: the truncated product box inflated by the tail `tail`. -/
def hValB (S : ℤ) (D : Work.ANum.CD) (N : ℕ) (tail : ℤ) : Work.ANum.CD :=
  infl (hProdB S D N) tail

/-- A tail bound (in mantissas at scale `S`) for `h(q) + 256·q·(∏_{n≤N}(1+q^n))^24`, valid when
`|q| ≤ R/S` and `absUp` of the truncated product is `≤ P/S`. -/
def hTailB (S : ℤ) (R P : ℤ) (N : ℕ) : ℤ :=
  divUpB S (12288 * R ^ (N + 2) * P) (S ^ (N + 1) * (S - R))

/-- The tight tail bound (in mantissas at scale `S`): `12288·R^{N+2}·P / (S^{N+1}(S-R))` rounded up.
(`Work.ANum3.hTailB` carries an extra factor `S`; the soundness statement of this version is
`Work.ANum3.hTailC_le`.) -/
def hTailC (S : ℤ) (R P : ℤ) (N : ℕ) : ℤ :=
  -Int.ediv (-(12288 * R ^ (N + 2) * P)) (S ^ (N + 1) * (S - R))


/-! ## Second-derivative mantissa bounds (correctly rescaled) -/

/-- Upper mantissa bound for `sup_{‖w-c‖ ≤ ρ}‖slit r '' w‖` with `ρ = m2r del`, `c ∈ D`,
`Qbox ∋ slitQ r c`; the constants `A B E C G` enclose `(1+r)²`, `2(1-6r+r²)`, `2(r-1)²`, `1+r`,
`8r`.  (`√`-arguments are given as *squared* mantissas, as in `absUp`/`absDn`.)

The `1/Slo³` term is evaluated by three *successive* divisions (with a final scaling by `SC`)
rather than by forming the mantissa of `Slo³`, which underflows to `0`/`1` when the centre is close
to a branch point of the slit map (`Q(c) → 0`); the naive form made the bound false (counterexample
found by the prover). -/
def slitM2B (A B E C G : Iv) (Qbox D : CD) (del : ℤ) : ℤ :=
  let Ah := A.hi
  let twoA := 2 * Ah
  let Bh := maxAbs B.lo B.hi
  let Eh := E.hi
  let Ch := C.hi
  let Gl := G.lo
  let wlo := absDn D - del
  let whi := absUp D + del
  let wm1 := distUp D SC 0 + del
  let Qp := mulUp twoA whi + Bh + mulUp del twoA
  let Qlo := absDn Qbox - mulUp del Qp
  let Qhi := absUp Qbox + mulUp del Qp
  let Slo := sqrtDn (Qlo * SC)
  let Shi := sqrtUp (Qhi * SC)
  let N0 := Ah + mulUp Eh whi + mulUp (mulUp Ah whi) whi + mulUp (mulUp Ch wm1) Shi
  let N1 := Eh + mulUp twoA whi + mulUp Ch Shi + divUp (mulUp (mulUp Ch wm1) Qp) (2 * Slo)
  let Xm := mulUp (mulUp Ch wm1) (mulUp twoA (mulUp twoA Qhi) + mulUp Qp Qp)
  let T3 := (divNatUp (divUp (divUp (divUp Xm Slo) Slo) Slo) 4) * SC
  let N2 := twoA + divUp (mulUp Ch Qp) Slo + T3
  divUp (mulUp N2 (mulUp whi whi) + 2 * mulUp N1 whi + 2 * N0)
    (mulUp Gl (mulUp (mulUp wlo wlo) wlo))

/-- Upper mantissa bound for `sup_{‖z-z0‖ ≤ ρ}‖lune (36/5) '' z‖` with `ρ = m2r del`, `z0 ∈ D`,
`Rbox ∋ luneR (36/5) z0`; `B, C2, Dc` enclose `1+c²`, `16c²`, `2(c²-1)`. -/
def luneM2B (B C2 Dc : Iv) (Rbox D : CD) (del : ℤ) : ℤ :=
  let Bh := B.hi
  let C2h := C2.hi
  let Dcl := Dc.lo
  let Rpp := 2 * mulUp Bh Bh
  let oneZ := distUp D (-SC) 0 + del
  let Rp := mulUp Rpp oneZ + C2h
  let Rlo := absDn Rbox - mulUp del Rp
  let Rhi := absUp Rbox + mulUp del Rp
  let Sq := sqrtDn (Rlo * SC)
  divUp (2 * mulUp Rhi Rpp + mulUp Rp Rp) (mulUp (4 * Dcl) (mulUp Rlo Sq))

/-! ## Labels and the winding check -/

/-- The unit `I^j` (`j : ℤ`), as a computable function. -/
def Ipow (j : ℤ) : ℂ :=
  if j % 4 = 0 then 1 else if j % 4 = 1 then Complex.I else if j % 4 = 2 then -1 else -Complex.I

/-- The signed number of quarter turns from label index `a` to label index `b`. -/
def turnI (a b : ℤ) : ℤ :=
  let r := (b - a) % 4
  if r = 3 then -1 else r

/-- The label index of the block containing `i`, from the (sorted) breakpoints `b` and block label
indices `l` (`b` has one more entry than `l`). -/
def labIdxOf : List ℕ → List ℤ → ℕ → ℤ
  | b0 :: b1 :: brest, l0 :: lrest, i => if i < b1 then l0 else labIdxOf (b1 :: brest) lrest i
  | _, _, _ => 0

/-- The cyclic sum of `turnI` over the block label indices. -/
def turnSumI (l : List ℤ) : ℤ := (l.zip (l.rotate 1)).foldl (fun acc p => acc + turnI p.1 p.2) 0

/-- The winding check: `b` is a strictly increasing list of breakpoints from `0` to `n` with one more
entry than the label list `l`, consecutive labels never differ by two quarter turns, and the total
cyclic turn count is `4`. -/
def windOK (n : ℕ) (b : List ℕ) (l : List ℤ) : Bool :=
  (b.length == l.length + 1) && (b.head? == some 0) && (b.getLast? == some n) &&
    b.Pairwise (· < ·) && (turnSumI l == 4) &&
    (l.zip (l.rotate 1)).all (fun p => (turnI p.1 p.2).natAbs != 2)

end Work.ANum3
