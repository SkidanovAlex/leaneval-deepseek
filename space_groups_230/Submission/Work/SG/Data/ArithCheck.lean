import Submission.Work.SG.Data.ArithTab

/-! Kernel-checked sanity of `arithData` / `repZ` (hand-written checkers, `decide +kernel`).
Soundness lemmas turning these `Bool`s into statements about `arithRep` / `sgTau` are fleet work
(see `DATA.md`). -/

namespace Work.SG.Data

/-- Checks for the class-`j` element table: generators agree with `arithGensList[j]`,
BFS parent relations, `mulGen`, `genIdx`, index bounds, no duplicates. -/
def ArithData.chk (j : Nat) (D : ArithData) : Bool :=
  let el := D.elems
  let gA := fun g => D.gens.getD g M3.one
  let eA := fun i => el.getD i M3.one
  D.gens.map M3.toList == (arithGensList.getD j []).map codeToList &&
  el.length == D.n && el.head? == some M3.one && D.par.length + 1 == D.n &&
  (List.range (D.n - 1)).all (fun i =>
    let p := D.par.getD i (0, 0)
    p.1 < D.gens.length && p.2 ≤ i && eA (i + 1) == M3.mul (gA p.1) (eA p.2)) &&
  D.mulGen.length == D.gens.length &&
  (List.range D.gens.length).all (fun g =>
    let row := D.mulGen.getD g []
    row.length == D.n && (List.range D.n).all fun i =>
      row.getD i 0 < D.n && eA (row.getD i 0) == M3.mul (gA g) (eA i)) &&
  D.genIdx.length == D.gens.length &&
  (List.range D.gens.length).all (fun g => D.genIdx.getD g 0 < D.n && eA (D.genIdx.getD g 0) == gA g) &&
  decide el.Nodup

/-- Class index of representative `k` as a `Nat`. -/
def repClass (k : Nat) : Nat := (sgDataList.getD k (0, 1, [], 0)).1

/-- Checks for representative `k`: `repZ[k]` is a cocycle table on its class (values in `[0,n)`,
`z(1) = 0`, `z(g·A) ≡ z(g) + g z(A) (mod n)` for generators `g`), and at the generators it
equals `n ·` the translations stored in `sgDataList` (`n · num / d`). -/
def repZChk (k : Nat) : Bool :=
  let e := sgDataList.getD k (0, 1, [], 0)
  let D := arithData.getD e.1 default
  let z := repZ.getD k []
  let n : Int := D.n
  let zA := fun i => z.getD i V3.zero
  let gA := fun g => D.gens.getD g M3.one
  z.length == D.n && z.head? == some V3.zero &&
  z.all (fun v => 0 ≤ v.x && v.x < n && 0 ≤ v.y && v.y < n && 0 ≤ v.z && v.z < n) &&
  (List.range D.gens.length).all (fun g =>
    let row := D.mulGen.getD g []
    (List.range D.n).all fun i =>
      zA (row.getD i 0) == (V3.add (zA (D.genIdx.getD g 0)) (M3.mulV (gA g) (zA i))).emod n) &&
  (List.range D.gens.length).all (fun g =>
    let v := zA (D.genIdx.getD g 0)
    (e.2.1 : Int) * v.x == n * e.2.2.1.getD (3 * g) 0 &&
    (e.2.1 : Int) * v.y == n * e.2.2.1.getD (3 * g + 1) 0 &&
    (e.2.1 : Int) * v.z == n * e.2.2.1.getD (3 * g + 2) 0)

theorem arithData_length : arithData.length = 73 := by decide +kernel
theorem repZ_length : repZ.length = 230 := by decide +kernel

theorem arithData_chk : (List.range 73).all (fun j => (arithData.getD j default).chk j) = true := by
  decide +kernel

theorem repZ_chk : (List.range 230).all repZChk = true := by
  decide +kernel

end Work.SG.Data
