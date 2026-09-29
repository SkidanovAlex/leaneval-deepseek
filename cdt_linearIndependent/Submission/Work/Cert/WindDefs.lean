import Submission.Work.Cert.Defs

/-! # Winding certificate for `φ_A + 1/72` on `|z| = 1` (lead-built checker, definitions only).
Per 4096-arc `j` of the unit circle one quadrant label `lab ∈ {0,1,2,3}` (`u = I^lab`); every leaf
of the arc has its value disc for `g = h(ψ_A(z)) + 1/72` inside the open half-plane `Re(g·ū) > 0`. -/
set_option maxRecDepth 100000
namespace Work.Cert

/-- the disc `(qr, qi, rq)` for `ψ_A(leaf disc)` — EXACTLY the chain inside `leafOK`. -/
def qChain (L : Leaf) : St :=
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
  ⟨st5.ok, -(md K45 st5.cr), -(md K45 st5.ci), mu st5.rho K45 + 2⟩

/-- a complex disc `(cr, ci, r)`; `sqD` squares it: `(c², 2|c|r + r²)` with `|c| ≤ |cr| + |ci|`. -/
def sqD (c : Int × Int × Int) : Int × Int × Int :=
  (cmr c.1 c.2.1 c.1 c.2.1, cmi c.1 c.2.1 c.1 c.2.1,
    2 * mu (iabs c.1 + iabs c.2.1) c.2.2 + mu c.2.2 c.2.2 + ETOL)

/-- the value disc `(gr, gi, rg)` of `g = h(q) + 1/72` for `q` in the disc of `qChain L`
(`h = -256 q (A/B)^8`); `ok` collects the side conditions. Witness `bU ≥ |B_K(q_c)|`. -/
def gDisc (L : Leaf) (bU : Int) : Bool × Int × Int × Int :=
  let st := qChain L
  let qr := st.cr
  let qi := st.ci
  let rq := st.rho
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
  let eA := A.dA + tailA
  let eB := B.dB + tailB
  let aU := L.aU
  let bL := L.bL
  let okAB := decide (0 ≤ aU) && decide (A.Ar * A.Ar + A.Ai * A.Ai ≤ aU * aU) && decide (0 ≤ bL) &&
    decide (bL * bL ≤ B.Br * B.Br + B.Bi * B.Bi) && decide (0 ≤ bU) &&
    decide (B.Br * B.Br + B.Bi * B.Bi ≤ bU * bU)
  let Blo := bL - eB
  let b2 := fdiv (B.Br * B.Br + B.Bi * B.Bi) S
  let okB := decide (0 < Blo) && decide (0 < md bL Blo) && decide (0 < b2)
  let xr := fdiv (A.Ar * B.Br + A.Ai * B.Bi) b2
  let xi := fdiv (A.Ai * B.Br - A.Ar * B.Bi) b2
  let rx := dvu (mu eA bU + mu aU eB) (md bL Blo) + 2 * fdiv (iabs xr + iabs xi + 2) b2 + 4 + ETOL
  let y := sqD (sqD (sqD (xr, xi, rx)))
  let pr := cmr qr qi y.1 y.2.1
  let pi := cmi qr qi y.1 y.2.1
  let rg := 256 * (mu (iabs qr + iabs qi) y.2.2 + mu (iabs y.1 + iabs y.2.1) rq + mu rq y.2.2) + ETOL + ETOL
  (st.ok && okq && okm && okAB && okB, -256 * pr + fdiv S 72, -256 * pi, rg)

/-- `Re(g · conj(I^lab))` of a centre `(gr, gi)`. -/
def labRe (lab : Nat) (gr gi : Int) : Int :=
  if lab = 0 then gr else if lab = 1 then gi else if lab = 2 then -gr else -gi

/-- the leaf's value disc lies in the open half-plane of label `lab`. -/
def windLeafOK (lab : Nat) (L : Leaf) (bU : Int) : Bool :=
  let g := gDisc L bU
  decide (L.k = 2) && decide (lab < 4) && g.1 && decide (g.2.2.2 < labRe lab g.2.1 g.2.2.1)

/-- A winding arc: grid index `j`, grid point `E_j`, label, leaves with their `bU` witnesses. -/
structure WArc where
  j : Nat
  Ex : Int
  Ey : Int
  lab : Nat
  leaves : List (Leaf × Int)

def wchainOK (nx ny : Int) : List (Leaf × Int) → Bool
  | [] => false
  | [l] => decide (l.1.Bx = nx) && decide (l.1.By = ny)
  | l :: m :: rest => decide (l.1.Bx = m.1.Ax) && decide (l.1.By = m.1.Ay) && wchainOK nx ny (m :: rest)

def warcOK (a : WArc) (nx ny : Int) : Bool :=
  (match a.leaves with
    | [] => false
    | l :: _ => decide (l.1.Ax = a.Ex) && decide (l.1.Ay = a.Ey)) &&
  wchainOK nx ny a.leaves && gridStep a.Ex a.Ey nx ny &&
  a.leaves.all (fun l => windLeafOK a.lab l.1 l.2)

/-- a chunk of consecutive winding arcs; the last one ends at `(Fx, Fy)`. -/
def warcsOK (Fx Fy : Int) : List WArc → Bool
  | [] => true
  | [a] => warcOK a Fx Fy
  | a :: b :: rest => warcOK a b.Ex b.Ey && decide (a.j + 1 = b.j) && warcsOK Fx Fy (b :: rest)

/-- quarter turns between consecutive labels (`none` if opposite). -/
def turn (a b : Nat) : Option Int :=
  let d := (b + 4 - a) % 4
  if d = 0 then some 0 else if d = 1 then some 1 else if d = 3 then some (-1) else none

/-- sum of quarter turns around the cyclic label list `l₀ … l_{n-1} l₀` (`none` on an opposite pair). -/
def turnsFrom (first : Nat) : List Nat → Option Int
  | [] => some 0
  | [a] => turn a first
  | a :: b :: rest => match turn a b, turnsFrom first (b :: rest) with
      | some x, some y => some (x + y)
      | _, _ => none

def labelsOK (labs : List Nat) : Bool :=
  match labs with
  | [] => false
  | a :: _ => decide (turnsFrom a labs = some 4)

end Work.Cert
