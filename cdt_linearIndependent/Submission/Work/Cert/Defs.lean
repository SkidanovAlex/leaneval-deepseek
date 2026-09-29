/-!
# Theorem-A arc certificate: kernel checker (definitions only)

Designed by the lead (FM3-DRIVE §22). A leaf is a circle arc (between the approximate circle points
`A` and `B`, radius `Rk`) together with WITNESSES (square roots, moduli bounds) produced by the Python
generator `REFS/design/cert/gen.py`; `leafOK` recomputes the ψ_A stage chain on Int mantissas at scale
`S = 2^40·10^8` using only `+ - *` and floor division by POSITIVE divisors (`Int.ediv`), checks every
witness by squaring back, and finally checks `expLo (2G - tail) ≥ P2`, which certifies
`log |h(q')| ≤ G / S` for every `q'` in the final disc, hence (soundness theorem, to be proved)
`circleLog φ ≤ G/S` on the arc. The Python file `certref.py` has EXACTLY the same integer semantics.
Soundness theorems are separate requests (`Work.Cert.leafOK_sound`).
-/
namespace Work.Cert

def S : Int := 109951162777600000000
def SLACK : Int := 16777216
def ETOL : Int := 1048576
def K491 : Int := 107972041847603200000
def K45 : Int := 87960930222080000000
def LB : Int := 5809819441168384000000
def LB2 : Int := 306990859271337410560000
def K16 : Int := 91197892454252544000000
def LD : Int := 11179834231226368000000
def L8 : Int := 44719336924905472000000
def LN2HI : Int := 76212338478581045031
def LN2LO : Int := 76212338478581045029
def s0A : Int := 396923697627136000000
def s0B2 : Int := -789449348743168000000
def s0E : Int := 2199023255552000000
def s0C1 : Int := 208907209277440000000
def s0G8 : Int := 791648371998720000000
def s0A2 : Int := 793847395254272000000
def rot0r : Int := 95908311960839462306
def rot0i : Int := 53766661538248679700
def s1A : Int := 283731280123968618496
def s1B2 : Int := -499327601485449003008
def s1E : Int := 34067479381244116992
def s1C1 : Int := 176625547885936640000
def s1G8 : Int := 533395080866693120000
def s1A2 : Int := 567462560247937236992
def rot1r : Int := 81518292988615043513
def rot1i : Int := 73783643881070330236
def s2A : Int := 260218619788164857856
def s2B2 : Int := -426726057055027724288
def s2E : Int := 46855591260650995712
def s2C1 : Int := 169148868817059840000
def s2G8 : Int := 473581648315678720000
def s2A2 : Int := 520437239576329715712
def rot2r : Int := 107113056366341060795
def rot2i : Int := 24820381786091335080
def s3A : Int := 336225344033227014144
def s3B2 : Int := -644676281078971891712
def s3E : Int := 13887203493741068288
def s3C1 : Int := 192271598349189120000
def s3G8 : Int := 658563484572712960000
def s3A2 : Int := 672450688066454028288
def rot3r : Int := 96734442863377519137
def rot3i : Int := -52265722611078878142
def WR : Int := 109951033414746560990
def WI : Int := 168662905159809435
def GTOL : Int := 8
def CTOL : Int := 1024
def NGRID : Nat := 4096


def fdiv (a b : Int) : Int := Int.ediv a b
def md (a b : Int) : Int := fdiv (a * b) S
def mu (a b : Int) : Int := -(fdiv (-(a * b)) S)
def dvu (a b : Int) : Int := -(fdiv (-(a * S)) b)
def iabs (a : Int) : Int := if a < 0 then -a else a
def cmr (a b c d : Int) : Int := md a c - md b d
def cmi (a b c d : Int) : Int := md a d + md b c
def INF : Int := 10 ^ 80
def imin (a b : Int) : Int := if a ≤ b then a else b
def two_pow (k : Nat) : Int := Int.ofNat (2 ^ k)

/-- A complex ball: centre `(x + y i)/S`, radius `r/S`. -/
structure Bl where
  x : Int
  y : Int
  r : Int

/-- `|x| + |y|` ≥ `S·|centre|`. -/
def bmod (a : Bl) : Int := iabs a.x + iabs a.y
/-- the exact constant `k/S`. -/
def bK (k : Int) : Bl := ⟨k, 0, 0⟩
def badd (a b : Bl) : Bl := ⟨a.x + b.x, a.y + b.y, a.r + b.r⟩
def bsub (a b : Bl) : Bl := ⟨a.x - b.x, a.y - b.y, a.r + b.r⟩
/-- product ball (+3 ulps for the four floors of the centre). -/
def bmul (a b : Bl) : Bl :=
  ⟨md a.x b.x - md a.y b.y, md a.x b.y + md a.y b.x, mu (bmod a) b.r + mu (bmod b) a.r + mu a.r b.r + 3⟩
/-- side condition of `binv`: `0 ≤ r < L ≤ S·|centre|` (witness `L`). -/
def binvOK (a : Bl) (L : Int) : Bool :=
  decide (0 ≤ a.r) && decide (a.r < L) && decide (L * L ≤ a.x * a.x + a.y * a.y)
/-- reciprocal ball: centre `S²·conj(c)/|c|²` floored, radius `r S²/((L−r)L) + 2`. -/
def binv (a : Bl) (L : Int) : Bl :=
  let n := a.x * a.x + a.y * a.y
  ⟨fdiv (a.x * S * S) n, -(fdiv (a.y * S * S) n), dvu (a.r * S) ((L - a.r) * L) + 2⟩
/-- principal square-root ball from the witness `s = (sr + si i)/S`, `sr > 0`:
`|√w − s| ≤ (|w − c| + |c − s²|)/Re s`. -/
def bsqrtOK (a : Bl) (sr : Int) : Bool := decide (0 < sr) && decide (0 ≤ a.r)
def bsqrt (a : Bl) (sr si : Int) : Bl :=
  let E := fdiv (iabs (sr * sr - si * si - a.x * S) + iabs (2 * sr * si - a.y * S)) S + 1
  ⟨sr, si, dvu (a.r + E) sr + 1⟩
/-- ceiling of `x/2`. -/
def chalf (x : Int) : Int := -(fdiv (-x) 2)

/-- Witnesses of one slit stage. -/
structure SlitW where
  sr : Int
  si : Int
  L1 : Int
  Ls : Int
  D : Int
  cU : Int
  cL : Int
  qU : Int
  qL : Int
  qpU : Int
  m1U : Int
  sL : Int
  sH : Int
deriving Repr

/-- Witnesses of the lune stage. -/
structure LuneW where
  sr : Int
  si : Int
  Ls : Int
  D : Int
  zU : Int
  RU : Int
  RL : Int
  rpU : Int
  sL : Int
deriving Repr

/-- One leaf of the certificate. `k` = circle index (radius `Rk`), `G` = claimed log bound. -/
structure Leaf where
  k : Nat
  Ax : Int
  Ay : Int
  Bx : Int
  By : Int
  chU : Int
  w0 : SlitW
  w1 : SlitW
  w2 : SlitW
  w3 : SlitW
  wl : LuneW
  mU : Int
  aU : Int
  bL : Int
  G : Int
deriving Repr

/-- A centre/radius state. -/
structure St where
  ok : Bool
  cr : Int
  ci : Int
  rho : Int


def Rk (k : Nat) : Int :=
  if k = 0 then fdiv S 10000 else if k = 1 then fdiv (283 * S) 500 else S

/-- one rotated slit stage `f = rot t · slit r` (constants A B2 E C1 G8 A2, rotation `(ror, roi)` ± 2 ulps).
Centre value `f(c)` and derivative `f'(c)` are enclosed by ball arithmetic at the point `c`; the output
radius is `|f'(c)|ρ + M2 ρ²/2 + rad f(c)` with `M2 = min(explicit, Cauchy)`. -/
def slitStage (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : St :=
  let cr := st.cr
  let ci := st.ci
  let rho := st.rho
  let C : Bl := ⟨cr, ci, 0⟩
  let c2 := bmul C C
  let Q := badd (bsub (bmul (bK A) c2) (bmul (bK B2) C)) (bK A)
  let s := bsqrt Q w.sr w.si
  let cm1 : Bl := ⟨cr - S, ci, 0⟩
  let N := badd (badd (bsub (bK A) (bmul (bK E) C)) (bmul (bK A) c2)) (bmul (bK C1) (bmul cm1 s))
  let den := bmul (bK G8) C
  let inv1 := binv den w.L1
  let v := bmul N inv1
  let RO : Bl := ⟨ror, roi, 2⟩
  let u := bmul RO v
  let Qp := bsub (bmul (bK A2) C) (bK B2)
  let invs := binv s w.Ls
  let qos := bmul (bmul Qp invs) (bK (fdiv S 2))
  let Np := badd (badd (bsub (bmul (bK A2) C) (bK E)) (bmul (bK C1) s)) (bmul (bK C1) (bmul cm1 qos))
  let dn := bsub (bmul Np C) N
  let invc := binv C w.cL
  let fp := bmul RO (bmul (bmul dn inv1) invc)
  let okB := bsqrtOK Q w.sr && binvOK den w.L1 && binvOK s w.Ls && binvOK C w.cL
  let okM := decide (0 ≤ w.D) && decide (fp.x * fp.x + fp.y * fp.y ≤ w.D * w.D) &&
    decide (0 ≤ w.cU) && decide (cr * cr + ci * ci ≤ w.cU * w.cU) &&
    decide (0 ≤ w.qU) && decide (Q.x * Q.x + Q.y * Q.y ≤ w.qU * w.qU) &&
    decide (0 ≤ w.qL) && decide (w.qL * w.qL ≤ Q.x * Q.x + Q.y * Q.y) &&
    decide (0 ≤ w.qpU) && decide (Qp.x * Qp.x + Qp.y * Qp.y ≤ w.qpU * w.qpU) &&
    decide (0 ≤ w.m1U) && decide ((cr - S) * (cr - S) + ci * ci ≤ w.m1U * w.m1U)
  let whi := w.cU + rho + 1
  let wlo := w.cL - rho - 1
  let QpD := w.qpU + Qp.r + mu rho A2 + 1
  let Qhi := w.qU + Q.r + mu rho QpD + 1
  let Qlo := w.qL - Q.r - mu rho QpD - 1
  let useE := decide (0 < Qlo) && decide (0 < wlo)
  let sL := w.sL
  let sH := w.sH
  let okW := !useE || (decide (0 < sL) && decide (sL * sL ≤ Qlo * S) && decide (0 ≤ sH) && decide (Qhi * S ≤ sH * sH))
  let wm1 := w.m1U + rho + 1
  let N0 := A + mu E whi + mu A (mu whi whi) + mu (mu C1 wm1) sH
  let N1 := E + mu A2 whi + mu C1 sH + dvu (mu (mu C1 wm1) QpD) (2 * sL)
  let x := mu (mu (2 * Qhi) A2 + mu QpD QpD) (mu C1 wm1)
  let N2 := A2 + dvu (mu C1 QpD) sL + dvu (dvu (dvu x sL) sL) (4 * sL)
  let num := mu N2 (mu whi whi) + 2 * mu N1 whi + 2 * N0
  let dd := md G8 (md (md wlo wlo) wlo)
  let M2e := if useE && decide (0 < dd) then dvu num dd else INF
  let d := S - w.cU - rho - 1
  let dsq := md d d
  let M2c := if decide (0 < d) && decide (0 < dsq) then dvu (2 * S) dsq else INF
  let M2 := imin M2e M2c
  let rho2 := mu rho (w.D + fp.r) + chalf (mu (mu rho rho) M2) + u.r + 1
  ⟨st.ok && okB && okM && okW && decide (whi < S) && decide (M2 < INF) && decide (0 ≤ rho) &&
    decide (0 ≤ rho2), u.x, u.y, rho2⟩

/-- the lune stage, applied to `z = -u₄`: `v = (LB z − LB + √R(z))/LD`, `R = LB2 (1+z)² − K16 z`. -/
def luneStage (st : St) (w : LuneW) : St :=
  let cr := st.cr
  let ci := st.ci
  let rho := st.rho
  let Z : Bl := ⟨-cr, -ci, 0⟩
  let opz := badd (bK S) Z
  let o2 := bmul opz opz
  let R := bsub (bmul (bK LB2) o2) (bmul (bK K16) Z)
  let s := bsqrt R w.sr w.si
  let INVLD : Bl := ⟨fdiv (S * S) LD, 0, 1⟩
  let v := bmul (badd (bsub (bmul (bK LB) Z) (bK LB)) s) INVLD
  let Rp := bsub (bmul (bK (2 * LB2)) opz) (bK K16)
  let invs := binv s w.Ls
  let vp := bmul (badd (bK LB) (bmul (bmul Rp invs) (bK (fdiv S 2)))) INVLD
  let okB := bsqrtOK R w.sr && binvOK s w.Ls
  let okM := decide (0 ≤ w.D) && decide (vp.x * vp.x + vp.y * vp.y ≤ w.D * w.D) &&
    decide (0 ≤ w.zU) && decide (cr * cr + ci * ci ≤ w.zU * w.zU) &&
    decide (0 ≤ w.RU) && decide (R.x * R.x + R.y * R.y ≤ w.RU * w.RU) &&
    decide (0 ≤ w.RL) && decide (w.RL * w.RL ≤ R.x * R.x + R.y * R.y) &&
    decide (0 ≤ w.rpU) && decide (Rp.x * Rp.x + Rp.y * Rp.y ≤ w.rpU * w.rpU)
  let Rpp := 2 * LB2
  let RpD := w.rpU + Rp.r + mu rho Rpp + 1
  let Rhi := w.RU + R.r + mu rho RpD + 1
  let Rlo := w.RL - R.r - mu rho RpD - 1
  let useE := decide (0 < Rlo)
  let sL := w.sL
  let okW := !useE || (decide (0 < sL) && decide (sL * sL ≤ Rlo * S))
  let num := mu (2 * Rhi) Rpp + mu RpD RpD
  let dd := md (md L8 Rlo) sL
  let M2e := if useE && decide (0 < dd) then dvu num dd else INF
  let d := S - w.zU - rho - 1
  let dsq := md d d
  let M2c := if decide (0 < d) && decide (0 < dsq) then dvu (2 * S) dsq else INF
  let M2 := imin M2e M2c
  let rho2 := mu rho (w.D + vp.r) + chalf (mu (mu rho rho) M2) + v.r + 1
  ⟨st.ok && okB && okM && okW && decide (w.zU + rho + 1 < S) && decide (M2 < INF) && decide (0 ≤ rho) &&
    decide (0 ≤ rho2), v.x, v.y, rho2⟩

/-- state of the theta sums. -/
structure TS where
  pnr : Int
  pni : Int
  pTr : Int
  pTi : Int
  Ar : Int
  Ai : Int
  mn : Int
  mT : Int
  dA : Int
  T : Int

def aStep (qr qi rq m : Int) (n : Nat) (s : TS) : TS :=
  let pnr := cmr s.pnr s.pni qr qi
  let pni := cmi s.pnr s.pni qr qi
  let pTr := cmr s.pTr s.pTi pnr pni
  let pTi := cmi s.pTr s.pTi pnr pni
  let T := s.T + Int.ofNat n
  let mn := mu s.mn m + 1
  let mT := mu s.mT mn + 1
  ⟨pnr, pni, pTr, pTi, s.Ar + pTr, s.Ai + pTi, mn, mT, s.dA + mu (T * dvu mT m) rq + 8 * T + 1, T⟩

def aLoop (qr qi rq m : Int) : Nat → Nat → TS → TS
  | 0, _, s => s
  | fuel + 1, n, s => aLoop qr qi rq m fuel (n + 1) (aStep qr qi rq m n s)

structure BS where
  por : Int
  poi : Int
  psr : Int
  psi : Int
  Br : Int
  Bi : Int
  mo : Int
  ms : Int
  dB : Int

def bStep (q2r q2i rq m : Int) (n : Nat) (s : BS) : BS :=
  let psr := cmr s.psr s.psi s.por s.poi
  let psi := cmi s.psr s.psi s.por s.poi
  let sg : Int := if n % 2 = 1 then -1 else 1
  let nn : Int := Int.ofNat n
  let ms := mu s.ms s.mo + 1
  ⟨cmr s.por s.poi q2r q2i, cmi s.por s.poi q2r q2i, psr, psi, s.Br + 2 * sg * psr, s.Bi + 2 * sg * psi,
    mu s.mo (mu m m + 1) + 1, ms, s.dB + 2 * mu (nn * nn * dvu ms m) rq + 16 * nn * nn + 1⟩

def bLoop (q2r q2i rq m : Int) : Nat → Nat → BS → BS
  | 0, _, s => s
  | fuel + 1, n, s => bLoop q2r q2i rq m fuel (n + 1) (bStep q2r q2i rq m n s)

def KTH : Nat := 12

/-- lower bound of `S·exp(x/S)`. -/
def expTaylor (y : Int) : Nat → Nat → Int → Int → Int
  | 0, _, _, acc => acc
  | fuel + 1, i, t, acc =>
      let t' := fdiv (t * y) (S * Int.ofNat i)
      expTaylor y fuel (i + 1) t' (acc + t')

def expLo (x : Int) : Int :=
  if 0 ≤ x then
    let k := fdiv x LN2HI
    let y := x - k * LN2HI
    expTaylor y 14 1 S S * two_pow k.toNat
  else
    let k := -(fdiv (-x) LN2LO) - 1
    let y := x - k * LN2LO
    fdiv (expTaylor y 14 1 S S) (two_pow (-k).toNat)

/-- The leaf check. -/
def leafOK (L : Leaf) : Bool :=
  let R := Rk L.k
  let Ax := L.Ax
  let Ay := L.Ay
  let Bx := L.Bx
  let By := L.By
  let dx := Bx - Ax
  let dy := By - Ay
  let chU := L.chU
  let okA := decide (0 ≤ chU) && decide (dx * dx + dy * dy ≤ chU * chU) &&
    decide (dx * dx + dy * dy < fdiv (R * R) 4) && decide (0 < Ax * By - Ay * Bx) &&
    decide (0 < Ax * Bx + Ay * By) &&
    decide (iabs (Ax * Ax + Ay * Ay - R * R) ≤ 2 * R * CTOL) && decide (iabs (Bx * Bx + By * By - R * R) ≤ 2 * R * CTOL)
  let rz := fdiv chU 2 + 1 + dvu (mu chU chU) (2 * R) + 1 + ETOL
  let st0 : St := ⟨okA, md K491 (fdiv (Ax + Bx) 2), md K491 (fdiv (Ay + By) 2), mu rz K491 + 2⟩
  let st1 := slitStage s0A s0B2 s0E s0C1 s0G8 s0A2 rot0r rot0i st0 L.w0
  let st2 := slitStage s1A s1B2 s1E s1C1 s1G8 s1A2 rot1r rot1i st1 L.w1
  let st3 := slitStage s2A s2B2 s2E s2C1 s2G8 s2A2 rot2r rot2i st2 L.w2
  let st4 := slitStage s3A s3B2 s3E s3C1 s3G8 s3A2 rot3r rot3i st3 L.w3
  let st5 := luneStage st4 L.wl
  let qr := -(md K45 st5.cr)
  let qi := -(md K45 st5.ci)
  let rq := mu st5.rho K45 + 2
  let mU := L.mU
  let okq := decide (0 ≤ mU) && decide (qr * qr + qi * qi ≤ mU * mU)
  let m := mU + rq + 1
  let okm := decide (m ≤ fdiv (79 * S) 100)
  let A := aLoop qr qi rq m KTH 1 ⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩
  let mK1 := mu A.mn m + 1
  let tailA := dvu (mu A.mT mK1) (S - m) + 1
  let q2r := cmr qr qi qr qi
  let q2i := cmi qr qi qr qi
  let B := bLoop q2r q2i rq m KTH 1 ⟨qr, qi, S, 0, S, 0, m, S, 0⟩
  let tailB := 2 * dvu (mu B.ms B.mo) (S - m) + 1
  let aU := L.aU
  let bL := L.bL
  let okAB := decide (0 ≤ aU) && decide (A.Ar * A.Ar + A.Ai * A.Ai ≤ aU * aU) && decide (0 ≤ bL) &&
    decide (bL * bL ≤ B.Br * B.Br + B.Bi * B.Bi)
  let Aup := aU + A.dA + tailA
  let Blo := bL - B.dB - tailB
  let ratio := dvu (mu Aup Aup) (md Blo Blo)
  let r2 := mu ratio ratio
  let r4 := mu r2 r2
  let r8 := mu r4 r4
  let P2 := mu (mu (65536 * S) (mu m m)) r8
  st5.ok && okq && okm && okAB && decide (0 < Blo) && decide (0 < md Blo Blo) && decide (P2 ≤ expLo (2 * L.G))


/-- An arc of the uniform grid (circle `k`, index `j`, grid point `E_j = (Ex, Ey)`) with its leaves. -/
structure ArcD where
  k : Nat
  j : Nat
  Ex : Int
  Ey : Int
  leaves : List Leaf
  Gmax : Int

/-- consecutive leaves share endpoints; the last one ends at `(nx, ny)`. -/
def chainOK (nx ny : Int) : List Leaf → Bool
  | [] => false
  | [l] => decide (l.Bx = nx) && decide (l.By = ny)
  | l :: m :: rest => decide (l.Bx = m.Ax) && decide (l.By = m.Ay) && chainOK nx ny (m :: rest)

/-- the grid step `E_{j+1} ≈ E_j · W`, `W ≈ e^{2πi/4096}`. -/
def gridStep (ex ey nx ny : Int) : Bool :=
  decide (iabs (nx - cmr ex ey WR WI) ≤ GTOL) && decide (iabs (ny - cmi ex ey WR WI) ≤ GTOL)

def arcOK (a : ArcD) (nx ny : Int) : Bool :=
  (match a.leaves with
    | [] => false
    | l :: _ => decide (l.Ax = a.Ex) && decide (l.Ay = a.Ey)) &&
  chainOK nx ny a.leaves && gridStep a.Ex a.Ey nx ny &&
  a.leaves.all (fun l => decide (l.k = a.k) && decide (l.G ≤ a.Gmax) && leafOK l)

/-- a chunk: consecutive arcs, the last arc ends at `(Fx, Fy)`. -/
def arcsOK (Fx Fy : Int) : List ArcD → Bool
  | [] => true
  | [a] => arcOK a Fx Fy
  | a :: b :: rest => arcOK a b.Ex b.Ey && decide (a.k = b.k) && decide (a.j + 1 = b.j) && arcsOK Fx Fy (b :: rest)


/-! ## Conjunct-2 certificate on the coarser grid (v4, 2026-09-29): `NARC2 = 1024` arcs per circle.
The winding certificate keeps the 4096-grid (`WR`, `WI`, `gridStep`, `arcOK`/`warcOK`); the conjunct-2
chunks use `WR2`, `WI2`, `gridStep2`, `arcOK2`, `arcsOK2`. -/

/-- number of arcs per circle of the conjunct-2 certificate. -/
def NARC2 : Nat := 1024
/-- `S·e^{2πi/1024}` rounded to the nearest integers. -/
def WR2 : Int := 109949092978033035917
def WI2 : Int := 674647651843760786

/-- the grid step `E_{j+1} ≈ E_j · W2`, `W2 ≈ e^{2πi/1024}`. -/
def gridStep2 (ex ey nx ny : Int) : Bool :=
  decide (iabs (nx - cmr ex ey WR2 WI2) ≤ GTOL) && decide (iabs (ny - cmi ex ey WR2 WI2) ≤ GTOL)

def arcOK2 (a : ArcD) (nx ny : Int) : Bool :=
  (match a.leaves with
    | [] => false
    | l :: _ => decide (l.Ax = a.Ex) && decide (l.Ay = a.Ey)) &&
  chainOK nx ny a.leaves && gridStep2 a.Ex a.Ey nx ny &&
  a.leaves.all (fun l => decide (l.k = a.k) && decide (l.G ≤ a.Gmax) && leafOK l)

/-- a conjunct-2 chunk (1024-grid): consecutive arcs, the last arc ends at `(Fx, Fy)`. -/
def arcsOK2 (Fx Fy : Int) : List ArcD → Bool
  | [] => true
  | [a] => arcOK2 a Fx Fy
  | a :: b :: rest => arcOK2 a b.Ex b.Ey && decide (a.k = b.k) && decide (a.j + 1 = b.j) && arcsOK2 Fx Fy (b :: rest)

end Work.Cert
