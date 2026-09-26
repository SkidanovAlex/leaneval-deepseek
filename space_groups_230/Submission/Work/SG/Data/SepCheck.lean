import Submission.Work.SG.Data.CohomCheck
import Submission.Work.SG.Data.SepTab

/-! Kernel-checked separation certificates for `sgRep_intEquiv_iff` (`decide +kernel`).
See `DATA.md` for the invariants these certify and the soundness lemmas to prove. -/

namespace Work.SG.Data

def M3.tmulV (A : M3) (v : V3) : V3 :=
  ⟨A.a * v.x + A.d * v.y + A.g * v.z, A.b * v.x + A.e * v.y + A.h * v.z,
   A.c * v.x + A.f * v.y + A.i * v.z⟩

def e3 (q : Nat) : V3 := if q = 0 then ⟨1, 0, 0⟩ else if q = 1 then ⟨0, 1, 0⟩ else ⟨0, 0, 1⟩

/-- Class table of representative `k`. -/
def repArith (k : Nat) : ArithData := arithData.getD (repClass k) default

/-- `N_A` for element `A` (sum of powers up to its order). -/
def normOf (A : M3) : M3 := M3.normSum A (M3.ord A)

/-- `v_A = N_A z / n` for element `i` of representative `k` (`z = repZ[k][i]`). -/
def vOf (k i : Nat) : V3 :=
  let D := repArith k
  V3.ediv (M3.mulV (normOf (D.elems.getD i M3.one)) ((repZ.getD k []).getD i V3.zero)) D.n

/-- The element-order certificate check. -/
def ElemCert.chk (k i : Nat) (e : ElemCert) : Bool :=
  let D := repArith k
  let A := D.elems.getD i M3.one
  let N := normOf A
  let z := (repZ.getD k []).getD i V3.zero
  let v := vOf k i
  1 ≤ e.o && V3.dvd D.n (M3.mulV N z) &&
  SpanCert.chk N.cols (V3.smul e.o v) (.yes e.yes) &&
  e.nos.length == (primesOf e.o).length &&
  (List.zipWith (fun p c => SpanCert.chk N.cols (V3.smul (e.o / p : Nat) v) (.no c.1 c.2))
    (primesOf e.o) e.nos).all id

/-- Cheap key `(det, tr, order of v_A)` of element `i` of rep `k`. -/
def ekey (k i : Nat) : Int × Int × Nat :=
  let A := (repArith k).elems.getD i M3.one
  (M3.det A, M3.trace A, ((elemTab.getD k []).getD i default).o)

def elemCount (k : Nat) (d t : Int) (o : Nat) : Nat :=
  (List.range (repArith k).n).countP fun i => ekey k i == (d, t, o)

def SymCert.chk (k : Nat) (s : SymCert) : Bool :=
  let D := repArith k
  let n : Int := D.n
  let zg := fun g => (repZ.getD k []).getD (D.genIdx.getD g 0) V3.zero
  let G := D.gens.length
  1 ≤ s.o &&
  (List.range G).all (fun g =>
    V3.dvd (n * n) (V3.sub (V3.sub s.sig (M3.mulV (D.gens.getD g M3.one) s.sig))
      (V3.smul (s.o * n) (zg g)))) &&
  s.nos.length == (primesOf s.o).length &&
  (List.zipWith (fun p u =>
      let ub := blocks u
      u.length == 3 * G &&
      (List.range G).foldl (fun acc g =>
        V3.add acc (V3.sub (ub.getD g V3.zero) (M3.tmulV (D.gens.getD g M3.one) (ub.getD g V3.zero))))
        V3.zero == V3.zero &&
      (List.range G).foldl (fun acc g =>
        acc + V3.dot (ub.getD g V3.zero) (V3.smul (s.o / p : Nat) (zg g))) 0 % n != 0)
    (primesOf s.o) s.nos).all id

def HandCert.chk (k i : Nat) : Option HandCert → Bool
  | none => let A := (repArith k).elems.getD i M3.one
            M3.det A != 1 || M3.ord A < 3
  | some c =>
    let A := (repArith k).elems.getD i M3.one
    let N := M3.normSum A c.ord
    let v := vOf k i
    M3.det A == 1 && M3.ord A == c.ord && 3 ≤ c.ord &&
    M3.mulV A c.c == c.c && V3.dot c.beta c.c == 1 &&
    0 < M3.det (M3.ofCols (e3 c.q) (M3.mulV A (e3 c.q)) c.c) &&
    N.cols == [V3.smul c.w.x c.c, V3.smul c.w.y c.c, V3.smul c.w.z c.c] &&
    0 < c.h && V3.dvd c.h c.w && V3.dot c.beta2 (V3.ediv c.w c.h) == 1 &&
    v == V3.smul c.j c.c

def handVal : Option HandCert → Option (Nat × Nat × Int)
  | none => none
  | some c => some (c.ord, c.h, c.j % (c.h : Int))

def TfCert.chk (X Y : List V3) : TfCert → Bool
  | .yes cs => cs.length == X.length &&
      (List.zipWith (fun x c => SpanCert.chk Y x (.yes c)) X cs).all id
  | .no col φ m => col < X.length && SpanCert.chk Y (X.getD col V3.zero) (.no φ m)

def PairCert.chk (k : Nat) (p : PairCert) : Bool :=
  let D := repArith k
  let A := D.elems.getD p.i M3.one
  let Bm := D.elems.getD p.j M3.one
  let v := vOf k p.i
  let Nc := (normOf A).cols
  let Bm1 := M3.sub Bm M3.one
  let Bp1 := M3.add Bm M3.one
  let Am1 := (M3.sub A M3.one).cols
  let Ap1 := (M3.add A M3.one).cols
  p.fix.chk (Nc.map (M3.mulV Bm1)) (M3.mulV Bm1 v) &&
  p.afix.chk (Nc.map (M3.mulV Bp1)) (M3.mulV Bp1 v) &&
  p.tf.length == 4 &&
  (p.tf.getD 0 default).chk Am1 Bm1.cols && (p.tf.getD 1 default).chk Ap1 Bp1.cols &&
  (p.tf.getD 2 default).chk Am1 Bp1.cols && (p.tf.getD 3 default).chk Ap1 Bm1.cols

def PairCert.bits (p : PairCert) : List Bool := [p.fix.bit, p.afix.bit] ++ p.tf.map TfCert.bit

/-- Pairs `(i, j)` whose cheap keys match. -/
def pairKeys (k : Nat) (kA kB : Int × Int × Nat) : List (Nat × Nat) :=
  let n := (repArith k).n
  (List.range n).flatMap fun i => (List.range n).filterMap fun j =>
    if ekey k i == kA && ekey k j == kB then some (i, j) else none

def pairCount (k : Nat) (kA kB : Int × Int × Nat) (bits : List Bool) (ls : List PairCert) : Option Nat :=
  if ls.map (fun p => (p.i, p.j)) == pairKeys k kA kB && ls.all (PairCert.chk k) then
    some (ls.countP fun p => p.bits == bits) else none

def affIdx (k : Nat) : Nat := (sgDataList.getD k (0, 1, [], 0)).2.2.2

def Sep.kl : Sep → Nat × Nat
  | .elem k l .. => (k, l) | .sym k l .. => (k, l) | .hand k l .. => (k, l) | .pair k l .. => (k, l)

def Sep.chk : Sep → Bool
  | .elem k l d t o => elemCount k d t o != elemCount l d t o
  | .sym k l a b => a.chk k && b.chk l && a.o != b.o
  | .hand k l o h jm ta tb =>
      affIdx k == affIdx l &&
      ta.length == (repArith k).n && tb.length == (repArith l).n &&
      (List.range ta.length).all (fun i => HandCert.chk k i (ta.getD i none)) &&
      (List.range tb.length).all (fun i => HandCert.chk l i (tb.getD i none)) &&
      ta.countP (fun c => handVal c == some (o, h, jm)) != tb.countP (fun c => handVal c == some (o, h, jm))
  | .pair k l dA tA oA dB tB oB bits la lb =>
      match pairCount k (dA, tA, oA) (dB, tB, oB) bits la, pairCount l (dA, tA, oA) (dB, tB, oB) bits lb with
      | some a, some b => a != b
      | _, _ => false

/-- All same-class pairs `k < l`, lexicographic. -/
def sameClassPairs : List (Nat × Nat) :=
  (List.range 230).flatMap fun k => ((List.range 230).filter fun l => k < l && repClass k == repClass l).map (k, ·)

theorem elemTab_chk : elemTab.length = 230 ∧
    (List.range 230).all (fun k => (elemTab.getD k []).length == (repArith k).n &&
      (List.range (repArith k).n).all fun i => ((elemTab.getD k []).getD i default).chk k i) = true := by
  decide +kernel

theorem sepList_cover : sepList.map Sep.kl = sameClassPairs := by decide +kernel

theorem sepList_chk : sepList.all Sep.chk = true := by decide +kernel

/-- Merges: `det U = -1`, the certificate maps rep `k` to rep `l` (same class, same affine index),
and the list is exactly the same-class pairs with equal affine index. -/
theorem mergeList_chk :
    mergeList.map (fun p => (p.1, p.2.k)) =
      sameClassPairs.filter (fun p => affIdx p.1 == affIdx p.2) ∧
    mergeList.all (fun p =>
      let D := repArith p.1
      M3.det p.2.U == -1 &&
      p.2.chk D (D.genIdx.flatMap fun g => ((repZ.getD p.1 []).getD g V3.zero).toList)) = true := by
  decide +kernel

end Work.SG.Data
