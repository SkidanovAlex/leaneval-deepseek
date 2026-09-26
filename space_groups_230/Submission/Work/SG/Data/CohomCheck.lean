import Submission.Work.SG.Data.ArithCheck
import Submission.Work.SG.Data.CohomTab

/-! Kernel-checked cohomology certificates (`decide +kernel`). See `DATA.md` for the meaning of
each check and the soundness lemmas the fleet must prove. -/

namespace Work.SG.Data

def M3.zero : M3 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Rows of a matrix. -/
def M3.rows (A : M3) : List V3 := [⟨A.a, A.b, A.c⟩, ⟨A.d, A.e, A.f⟩, ⟨A.g, A.h, A.i⟩]

/-- `B[i]` = the `k` blocks with `n · τ(elems i) ≡ ∑_g B[i][g] y_g (mod n)` for a cocycle with
generator coordinates `y` (recursion along the BFS parents). -/
def bmats (D : ArithData) : List (List M3) :=
  let k := D.gens.length
  D.par.foldl (fun acc p =>
    let Bp := acc.getD p.2 []
    let gM := D.gens.getD p.1 M3.one
    acc ++ [(List.range k).map fun g' =>
      M3.add (if g' = p.1 then M3.one else M3.zero) (M3.mul gM (Bp.getD g' M3.zero))])
    [List.replicate k M3.zero]

/-- `∑_g B_g y_g`. -/
def applyB (B : List M3) (y : List Int) : V3 :=
  (List.zipWith M3.mulV B (blocks y)).foldr V3.add V3.zero

/-- Relation rows: for generator `g'` and element `i`, the three rows of
`B[g'·i] - (E_{g'} + g' B[i])`, flattened; row index `3 (g' n + i) + r`. -/
def relRows (D : ArithData) : List (List Int) :=
  let Bs := bmats D
  let k := D.gens.length
  (List.range k).flatMap fun g' => (List.range D.n).flatMap fun i =>
    let gM := D.gens.getD g' M3.one
    let lhs := Bs.getD ((D.mulGen.getD g' []).getD i 0) []
    let rhs := (Bs.getD i []).map (M3.mul gM)
    let blk := (List.range k).map fun g =>
      M3.sub (lhs.getD g M3.zero) (M3.add (if g = g' then M3.one else M3.zero) (rhs.getD g M3.zero))
    [0, 1, 2].map fun r => blk.flatMap fun A => ((A.rows).getD r V3.zero).toList

/-- Upper-echelon shape: row `c` has zeros before `c` and a positive entry at `c`. -/
def echelonAt (c : Nat) (row : List Int) : Bool :=
  (List.range c).all (fun q => row.getD q 0 == 0) && 0 < row.getD c 0

/-- Reduce `x` modulo the upper-echelon basis `Bl` (row `c` has pivot at `c`). -/
def reduceBl (Bl : List (List Int × V3)) (x : List Int) : List Int :=
  (List.range Bl.length).foldl (fun x c =>
    let row := (Bl.getD c ([], V3.zero)).1
    let q := x.getD c 0 / row.getD c 1
    List.zipWith (fun a b => a - q * b) x row) x

/-- `((1 - g) σ / n)_g`, flattened. -/
def cobVec (D : ArithData) (n : Int) (σ : V3) : List Int :=
  D.gens.flatMap fun g => (V3.ediv (V3.sub σ (M3.mulV g σ)) n).toList

/-- `U` normalises the table and the integral-equivalence congruence holds on every element:
`n z_k(U A U⁻¹) - n U (B_A y) - σ + (U A U⁻¹) σ ≡ 0 (mod n²)` (with `z_k = repZ[k]`). -/
def ConjCert.chk (D : ArithData) (y : List Int) (t : ConjCert) : Bool :=
  let n : Int := D.n
  let Bs := bmats D
  let zk := repZ.getD t.k []
  M3.mul t.U t.Uinv == M3.one && t.img.length == D.n &&
  (List.range D.n).all fun i =>
    let A := D.elems.getD i M3.one
    let j := t.img.getD i 0
    let A' := D.elems.getD j M3.one
    j < D.n && M3.mul (M3.mul t.U A) t.Uinv == A' &&
    V3.dvd (n * n) (V3.add (V3.sub (V3.sub (V3.smul n (zk.getD j V3.zero))
      (V3.smul n (M3.mulV t.U (applyB (Bs.getD i []) y)))) t.sig) (M3.mulV A' t.sig))

def CohomData.chk (j : Nat) (D : ArithData) (C : CohomData) : Bool :=
  let N3 := 3 * D.gens.length
  let n : Int := D.n
  let R := relRows D
  C.n == D.n && C.H.length == N3 &&
  (List.range N3).all (fun c =>
    let Hc := C.H.getD c []
    Hc.length == N3 && echelonAt c Hc && n % Hc.getD c 1 == 0 &&
    R.all fun row => ldot row Hc % n == 0) &&
  C.wc.length == N3 &&
  (List.range N3).all (fun c =>
    let w := (C.wc.getD c []).foldl (fun acc p =>
      List.zipWith (fun a b => a + p.2 * b) acc (R.getD p.1 [])) (List.replicate N3 0)
    (List.range N3).all (fun q => q ≤ c || w.getD q 0 % n == 0) &&
    (w.getD c 0 - n / (C.H.getD c []).getD c 1) % n == 0) &&
  C.Bl.length == N3 &&
  (List.range N3).all (fun c =>
    let p := C.Bl.getD c ([], V3.zero)
    p.1.length == N3 && echelonAt c p.1 &&
    D.gens.all (fun g => V3.dvd n (V3.sub p.2 (M3.mulV g p.2))) &&
    (List.zipWith (fun a b => (a - b) % n == 0) p.1 (cobVec D n p.2)).all id) &&
  C.reps.head? == some (List.replicate N3 0) &&
  C.reps.all (fun r => r.length == N3 && reduceBl C.Bl r == r) &&
  C.add.length == C.reps.length &&
  (List.range C.reps.length).all (fun h =>
    (List.range N3).all fun c =>
      let t := (C.add.getD h []).getD c 0
      t < C.reps.length &&
      reduceBl C.Bl (List.zipWith (· + ·) (C.reps.getD h []) (C.H.getD c [])) == C.reps.getD t []) &&
  C.targets.length == C.reps.length &&
  (List.range C.reps.length).all (fun h =>
    let t := C.targets.getD h default
    repClass t.k == j && t.k < 230 && M3.det t.U == 1 && t.chk D (C.reps.getD h []))

theorem cohomData_length : cohomData.length = 73 := by decide +kernel

theorem cohomData_chk_0 : (List.range' 0 8).all (fun j =>
    (cohomData.getD j default).chk j (arithData.getD j default)) = true := by
  decide +kernel

theorem cohomData_chk_8 : (List.range' 8 8).all (fun j =>
    (cohomData.getD j default).chk j (arithData.getD j default)) = true := by
  decide +kernel

theorem cohomData_chk_16 : (List.range' 16 8).all (fun j =>
    (cohomData.getD j default).chk j (arithData.getD j default)) = true := by
  decide +kernel

theorem cohomData_chk_24 : (List.range' 24 8).all (fun j =>
    (cohomData.getD j default).chk j (arithData.getD j default)) = true := by
  decide +kernel

theorem cohomData_chk_32 : (List.range' 32 8).all (fun j =>
    (cohomData.getD j default).chk j (arithData.getD j default)) = true := by
  decide +kernel

theorem cohomData_chk_40 : (List.range' 40 8).all (fun j =>
    (cohomData.getD j default).chk j (arithData.getD j default)) = true := by
  decide +kernel

theorem cohomData_chk_48 : (List.range' 48 8).all (fun j =>
    (cohomData.getD j default).chk j (arithData.getD j default)) = true := by
  decide +kernel

theorem cohomData_chk_56 : (List.range' 56 8).all (fun j =>
    (cohomData.getD j default).chk j (arithData.getD j default)) = true := by
  decide +kernel

theorem cohomData_chk_64 : (List.range' 64 8).all (fun j =>
    (cohomData.getD j default).chk j (arithData.getD j default)) = true := by
  decide +kernel

theorem cohomData_chk_72 : (List.range' 72 1).all (fun j =>
    (cohomData.getD j default).chk j (arithData.getD j default)) = true := by
  decide +kernel

end Work.SG.Data
