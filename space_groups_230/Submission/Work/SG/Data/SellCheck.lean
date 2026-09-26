import Submission.Work.SG.Data.ArithCheck
import Submission.Work.SG.Data.SellTab

/-! Kernel-checked Selling data for `conj_to_arithRep` (`decide +kernel`). See `DATA.md`. -/

namespace Work.SG.Data

/-- The coset-minimal vectors of graph `E`, enumerated over the box `[-3,3]³`
(first coordinate slowest), with superbase coordinates `x = (0, y₀, y₁, y₂)`. -/
def boxVecs (E : List (Fin 4 × Fin 4)) : List V3 :=
  (List.range 7).flatMap fun a => (List.range 7).flatMap fun b => (List.range 7).filterMap fun c =>
    let y : V3 := ⟨(a : Int) - 3, (b : Int) - 3, (c : Int) - 3⟩
    let x : Fin 4 → Int := ![0, y.x, y.y, y.z]
    if y != V3.zero && E.all (fun e => decide ((x e.1 - x e.2).natAbs ≤ 1)) then some y else none

/-- Unimodular matrices whose columns come from `V` and which map `V` into `V`, in the
enumeration order columns `(c₀, c₁, c₂) ∈ V³` (first column slowest). -/
def stabCands (V : List V3) : List M3 :=
  V.flatMap fun c0 => V.flatMap fun c1 => V.filterMap fun c2 =>
    let A := M3.ofCols c0 c1 c2
    if (M3.det A == 1 || M3.det A == -1) && V.all (fun y => V.contains (M3.mulV A y)) then some A
    else none

def cosetMask (S : SellData) (K r : Nat) : Nat :=
  (List.range S.stab.length).foldl (fun acc k =>
    if K.testBit k then acc ||| (1 <<< ((S.mul.getD k []).getD r 0)) else acc) 0

def SellData.chkVecs (i : Nat) (S : SellData) : Bool :=
  S.vecs == boxVecs (sellingGraphList.getD i [])

def SellData.chkStab (S : SellData) : Bool := S.stab == stabCands S.vecs

def SellData.chkMul (S : SellData) : Bool :=
  let N := S.stab.length
  S.mul.length == N && S.one < N && S.stab.getD S.one M3.one == M3.one &&
  (List.range N).all fun a =>
    let row := S.mul.getD a []
    row.length == N && (List.range N).all fun b =>
      row.getD b 0 < N &&
      S.stab.getD (row.getD b 0) M3.one == M3.mul (S.stab.getD a M3.one) (S.stab.getD b M3.one)

def SellData.chkJoin (S : SellData) (s g : Nat) : Option JoinCert → Bool
  | none => (S.subs.getD s 0).testBit g
  | some (.full t cos) =>
    let K := S.subs.getD s 0
    let T := S.subs.getD t 0
    let rs := cos.foldl (fun rs p =>
      rs ++ [(S.mul.getD (rs.getD p.1 0) []).getD p.2 0]) [S.one]
    !K.testBit g && t < S.subs.length && ((K ||| (1 <<< g)) ||| T) == T &&
    cos.all (fun p => p.2 == g || K.testBit p.2) &&
    (List.range cos.length).all (fun q => (cos.getD q (0, 0)).1 ≤ q) &&
    (T ||| rs.foldl (fun acc r => acc ||| cosetMask S K r) 0) == rs.foldl (fun acc r => acc ||| cosetMask S K r) 0
  | some (.ref g0 k1 k2) =>
    let K := S.subs.getD s 0
    !K.testBit g && K.testBit k1 && K.testBit k2 &&
    g == (S.mul.getD ((S.mul.getD k1 []).getD g0 0) []).getD k2 0 &&
    match (S.joins.getD s []).getD g0 none with
    | some (.full t _) => (S.subs.getD t 0).testBit g
    | _ => false

def SellData.chkSubs (S : SellData) : Bool :=
  let N := S.stab.length
  S.subs.contains (1 <<< S.one) && S.subs.all (fun m => m < 2 ^ N) &&
  S.joins.length == S.subs.length && S.conj.length == S.subs.length

def SellData.chkJoins (S : SellData) (lo cnt : Nat) : Bool :=
  (List.range' lo cnt).all fun s =>
    let row := S.joins.getD s []
    row.length == S.stab.length &&
    (List.range S.stab.length).all fun g => S.chkJoin s g (row.getD g none)

def SellData.chkConj (S : SellData) : Bool :=
  (List.range S.subs.length).all fun s =>
    let K := S.subs.getD s 0
    let c := S.conj.getD s default
    let D := arithData.getD c.j default
    let xs := (List.range S.stab.length).filter K.testBit
    c.j < 73 && M3.det c.U == 1 && M3.mul c.U c.Uinv == M3.one &&
    c.img.length == xs.length && xs.length == D.n && decide c.img.Nodup &&
    (List.zipWith (fun x q => q < D.n &&
      M3.mul (M3.mul c.U (S.stab.getD x M3.one)) c.Uinv == D.elems.getD q M3.one) xs c.img).all id

theorem sellData_length : sellData.length = 6 := by decide +kernel

theorem sell_vecs_0 : (sellData.getD 0 default).chkVecs 0 = true := by decide +kernel
theorem sell_stab_0 : (sellData.getD 0 default).chkStab = true := by decide +kernel
theorem sell_mul_0 : (sellData.getD 0 default).chkMul = true := by decide +kernel
theorem sell_subs_0 : (sellData.getD 0 default).chkSubs = true := by decide +kernel
theorem sell_conj_0 : (sellData.getD 0 default).chkConj = true := by decide +kernel
theorem sell_joins_0_0 : (sellData.getD 0 default).chkJoins 0 25 = true := by decide +kernel
theorem sell_joins_0_25 : (sellData.getD 0 default).chkJoins 25 25 = true := by decide +kernel
theorem sell_joins_0_50 : (sellData.getD 0 default).chkJoins 50 25 = true := by decide +kernel
theorem sell_joins_0_75 : (sellData.getD 0 default).chkJoins 75 23 = true := by decide +kernel

theorem sell_vecs_1 : (sellData.getD 1 default).chkVecs 1 = true := by decide +kernel
theorem sell_stab_1 : (sellData.getD 1 default).chkStab = true := by decide +kernel
theorem sell_mul_1 : (sellData.getD 1 default).chkMul = true := by decide +kernel
theorem sell_subs_1 : (sellData.getD 1 default).chkSubs = true := by decide +kernel
theorem sell_conj_1 : (sellData.getD 1 default).chkConj = true := by decide +kernel
theorem sell_joins_1_0 : (sellData.getD 1 default).chkJoins 0 25 = true := by decide +kernel
theorem sell_joins_1_25 : (sellData.getD 1 default).chkJoins 25 10 = true := by decide +kernel

theorem sell_vecs_2 : (sellData.getD 2 default).chkVecs 2 = true := by decide +kernel
theorem sell_stab_2 : (sellData.getD 2 default).chkStab = true := by decide +kernel
theorem sell_mul_2 : (sellData.getD 2 default).chkMul = true := by decide +kernel
theorem sell_subs_2 : (sellData.getD 2 default).chkSubs = true := by decide +kernel
theorem sell_conj_2 : (sellData.getD 2 default).chkConj = true := by decide +kernel
theorem sell_joins_2_0 : (sellData.getD 2 default).chkJoins 0 25 = true := by decide +kernel
theorem sell_joins_2_25 : (sellData.getD 2 default).chkJoins 25 25 = true := by decide +kernel
theorem sell_joins_2_50 : (sellData.getD 2 default).chkJoins 50 25 = true := by decide +kernel
theorem sell_joins_2_75 : (sellData.getD 2 default).chkJoins 75 23 = true := by decide +kernel

theorem sell_vecs_3 : (sellData.getD 3 default).chkVecs 3 = true := by decide +kernel
theorem sell_stab_3 : (sellData.getD 3 default).chkStab = true := by decide +kernel
theorem sell_mul_3 : (sellData.getD 3 default).chkMul = true := by decide +kernel
theorem sell_subs_3 : (sellData.getD 3 default).chkSubs = true := by decide +kernel
theorem sell_conj_3 : (sellData.getD 3 default).chkConj = true := by decide +kernel
theorem sell_joins_3_0 : (sellData.getD 3 default).chkJoins 0 25 = true := by decide +kernel
theorem sell_joins_3_25 : (sellData.getD 3 default).chkJoins 25 25 = true := by decide +kernel
theorem sell_joins_3_50 : (sellData.getD 3 default).chkJoins 50 4 = true := by decide +kernel

theorem sell_vecs_4 : (sellData.getD 4 default).chkVecs 4 = true := by decide +kernel
theorem sell_stab_4 : (sellData.getD 4 default).chkStab = true := by decide +kernel
theorem sell_mul_4 : (sellData.getD 4 default).chkMul = true := by decide +kernel
theorem sell_subs_4 : (sellData.getD 4 default).chkSubs = true := by decide +kernel
theorem sell_conj_4 : (sellData.getD 4 default).chkConj = true := by decide +kernel
theorem sell_joins_4_0 : (sellData.getD 4 default).chkJoins 0 25 = true := by decide +kernel
theorem sell_joins_4_25 : (sellData.getD 4 default).chkJoins 25 25 = true := by decide +kernel
theorem sell_joins_4_50 : (sellData.getD 4 default).chkJoins 50 25 = true := by decide +kernel
theorem sell_joins_4_75 : (sellData.getD 4 default).chkJoins 75 23 = true := by decide +kernel

theorem sell_vecs_5 : (sellData.getD 5 default).chkVecs 5 = true := by decide +kernel
theorem sell_stab_5 : (sellData.getD 5 default).chkStab = true := by decide +kernel
theorem sell_mul_5 : (sellData.getD 5 default).chkMul = true := by decide +kernel
theorem sell_subs_5 : (sellData.getD 5 default).chkSubs = true := by decide +kernel
theorem sell_conj_5 : (sellData.getD 5 default).chkConj = true := by decide +kernel
theorem sell_joins_5_0 : (sellData.getD 5 default).chkJoins 0 25 = true := by decide +kernel
theorem sell_joins_5_25 : (sellData.getD 5 default).chkJoins 25 25 = true := by decide +kernel
theorem sell_joins_5_50 : (sellData.getD 5 default).chkJoins 50 25 = true := by decide +kernel
theorem sell_joins_5_75 : (sellData.getD 5 default).chkJoins 75 23 = true := by decide +kernel

end Work.SG.Data
