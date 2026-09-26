import Submission.Work.PTCert.KernelShared

/-!
# PTCert — Bool checks of one certificate (values, row transforms, blocks, class sums)

Signed integers are stored as offset naturals `v + OFF`, `OFF = 2^127`; `sv` recovers the `Int`.
See `NOTES_LEAD_checker.md` §3 for the layout and the mathematics each check stands for.
-/

set_option autoImplicit false

noncomputable section

namespace Submission.PTCert

/-- Offset of signed values. -/
def OFF : ℕ := 170141183460469231731687303715884105728

/-- Signed value of an offset natural. -/
def sv (v : ℕ) : ℤ := (v : ℤ) - (OFF : ℤ)

/-- Packed lookup with `8` fields of `128` bits per leaf. -/
def p8 (t : NT) (i : ℕ) : ℕ :=
  (t.get (i / 8) >>> (128 * (i % 8))) &&& 340282366920938463463374607431768211455

/-- Field `S` (`128` bits) of a packed 32-vector. -/
def f32 (v S : ℕ) : ℤ := sv ((v >>> (128 * S)) &&& 340282366920938463463374607431768211455)

/-- Sign character `χ_S(ν) = (-1)^{|S ∧ ν|}` on 5 bits. -/
def chiS5 (S nu : ℕ) : ℤ :=
  let x := S &&& nu
  bif Nat.beq ((x % 2 + (x / 2) % 2 + (x / 4) % 2 + (x / 8) % 2 + (x / 16) % 2) % 2) 0 then 1 else -1

/-- Walsh–Hadamard transform of a list of length `2^d` (index = `ν`, output index = `S`). -/
def wht : ℕ → List ℤ → List ℤ
  | 0, l => l
  | d + 1, l =>
    let a := wht d (l.take (2 ^ d))
    let b := wht d (l.drop (2 ^ d))
    List.zipWith (· + ·) a b ++ List.zipWith (· - ·) a b

/-- Unpack a packed 32-vector of offset values. -/
def unpack32 (v : ℕ) : List ℤ := (List.range 32).map (fun S => f32 v S)

/-- **Row table check** for one row `r` and reps `ts`: the leaf `t` of `rowT` packs
`Row_S(x₀,t) = Σ_ν χ_S(ν) P(x₀, ν·rep_t)` for all `S < 32`, where `P(x₀, z) = val (key r (lab z))`,
the 32 labels are read from the orbit-label leaf `olT.get t` and the values from `valT`
(`key r g = 2048 r + g`). -/
def rowCheck (valT olT rowT : NT) (r : ℕ) (ts : List ℕ) : Bool :=
  allL ts (fun t =>
    let o := olT.get t
    let vs := (List.range 32).map (fun sc => sv (p8 valT (2048 * r + ((o >>> (11 * sc)) &&& 2047))))
    wht 5 vs == unpack32 (rowT.get t))

/-- The value `Row_S(x₀, t)` from the per-row tables (`rowTs.get r`). -/
def rowVal (rowTs : List NT) (r S t : ℕ) : ℤ := f32 ((rowTs.getD r (NT.leaf 0)).get t) S

/-- Pullback of a character along a permutation code: `S' = {i : pdig pc i ∈ S}`. -/
def pullS (pc S : ℕ) : ℕ :=
  (List.range 5).foldr (fun i acc => acc + (bif Nat.beq ((S >>> pdig pc i) % 2) 1 then 2 ^ i else 0)) 0

/-- The transported value `M_k(x̄, y')` (`y'` an N-rep in `R_k`, `x̄ = π·x₀` with info `(r, πinv, S')`):
`M = χ_{S'}(μ') · Row_{S'}(x₀, t'')` where `πinv·rep_{y'} = ν_{μ'}·rep_{t''}`. -/
def mVal (cm eM repT : NT) (rowTs : List NT) (r piInvTab Sp y' : ℕ) : ℤ :=
  let z := actC cm piInvTab (cG repT y')
  let v := eG eM z - 1
  chiS5 Sp (v % 32) * rowVal rowTs r Sp (v / 32)

/-- Dot product of two lists of integers (up to the shorter). -/
def dotZ (a b : List ℤ) : ℤ := (List.zipWith (· * ·) a b).foldr (· + ·) 0

/-- Entries of the four `ψ`-blocks in row `x̄` against the columns `ys`: for each column `ȳ`,
`ys` gives the four pairs `(t2, s)` of the signed `A`-action `a·ȳ = s · e_{t2}` (packed `2 t2 + [s=-1]`
in 4 fields of 11 bits); `B_ψ(x̄,ȳ) = Σ_a ψ(a) s_a M(x̄, t2_a)`. -/
def blockRow (cm eM repT : NT) (rowTs : List NT) (r piInvTab Sp : ℕ) (ys : List ℕ) : List (List ℤ) :=
  let ms := ys.map (fun yv => (List.range 4).map (fun a =>
      let f := (yv >>> (11 * a)) &&& 2047
      (bif Nat.beq (f % 2) 0 then (1 : ℤ) else -1) * mVal cm eM repT rowTs r piInvTab Sp (f / 2)))
  (List.range 4).map (fun psi => ms.map (fun m4 =>
      (List.range 4).foldr (fun a acc =>
        acc + (bif Nat.beq ((a &&& psi) % 2 + ((a &&& psi) / 2) % 2) 1 then -(m4.getD a 0) else m4.getD a 0)) 0))

/-- **Scaled LDL check of one block, one row at a time.**  Row `i` (0-based): `bi` = the block
entries `B(i, j)` for `j ≥ i`, `wi`/`ws` the scaling weights, `ci` = row `i` of the lower-triangular
factor `C` (length `i+1`), `cs` = rows `j ≥ i` of `C`; the remainder `R_ij = w_i w_j B_ij − ⟨C_i, C_j⟩`
is accumulated in absolute value into `acc` (column sums from earlier rows); returns the updated
accumulator for the rows `> i`, or `none` if diagonal dominance fails at row `i`. -/
def ldlRowStep (bi : List ℤ) (wi : ℤ) (ws : List ℤ) (ci : List ℤ) (cs : List (List ℤ)) (acc : List ℤ) :
    Option (List ℤ) :=
  let rs := List.zipWith (fun (bw : ℤ × ℤ) (cj : List ℤ) => wi * bw.2 * bw.1 - dotZ ci cj) (List.zip bi ws) cs
  let rii := rs.headD 0
  let off := (rs.drop 1).map (fun x => |x|)
  bif decide (acc.headD 0 + off.foldr (· + ·) 0 ≤ rii) then
    some (List.zipWith (· + ·) (acc.drop 1) off) else none

/-- Label (group index) of the code `z` in row `r`: row `0` uses `lab0`, row `r ≥ 1` its label tree. -/
def labOf (eM repInfoT : NT) (labTs : List NT) (r z : ℕ) : ℕ :=
  bif Nat.beq r 0 then lab0 eM repInfoT z else lG (labTs.getD r (NT.leaf 0)) z

/-- **Symmetry of `P`** for the groups `gs` of row `r`: with `z = grep g = ν_sc π_t x₀'` (row `r'`),
`P(x₀, z) = P(x₀', π_t⁻¹ ν_sc x₀)`. -/
def symOK (cm eM nT rowT repInfoT piIT valT grepT : NT) (labTs : List NT) (r : ℕ) (gs : List ℕ) : Bool :=
  allL gs (fun g =>
    let z := cG grepT g
    let v := eG eM z - 1
    let ri := cG repInfoT (v / 32)
    let w := actC cm (piIT.get (ri % 128)) (actC cm (nT.get (v % 32)) (cG rowT r))
    Nat.beq (p8 valT (2048 * r + g)) (p8 valT (2048 * (ri / 128) + labOf eM repInfoT labTs (ri / 128) w)))

/-- The rep `t` lies in `R_S`: every sign flip fixing it is in `ker χ_S`. -/
def inROK (cm nT repT : NT) (S t : ℕ) : Bool :=
  let x := cG repT t
  allR 32 (fun sc => !(Nat.beq (actC cm (nT.get sc) x) x) || decide (chiS5 S sc = 1))

/-- Klein cover data for base character `S`: `kw t = 0` (then `vw t` is a sign code fixing rep `t`
with `χ_S = -1`), or `kw t = 1 + 4 i + b` with `t = rep(κ_b · rep_{ks[i]})` and `t ∈ R_S`. -/
def kleinCoverOK (cm eM nT repT klT kwT vwT : NT) (S : ℕ) (ks : List ℕ) (ts : List ℕ) : Bool :=
  allL ts (fun t =>
    let kw := cG kwT t
    bif Nat.beq kw 0 then
      (let sc := rG vwT t
       Nat.beq (actC cm (nT.get sc) (cG repT t)) (cG repT t) && decide (chiS5 S sc = -1))
    else
      (let i := (kw - 1) / 4
       let b := (kw - 1) % 4
       inROK cm nT repT S t && Nat.blt i ks.length &&
       Nat.beq ((eG eM (actC cm (klT.get b) (cG repT (ks.getD i 0))) - 1) / 32) t))

/-- Klein reps are distinct orbits: `rep(κ_b · rep_{ks[i]})` has Klein index `i`, and `kw (ks[i]) = 1 + 4 i`. -/
def kleinDistinctOK (cm eM repT klT kwT : NT) (ks : List ℕ) : Bool :=
  allIdx ks (fun i t => Nat.beq (cG kwT t) (1 + 4 * i) &&
    allR 4 (fun b => Nat.beq ((cG kwT ((eG eM (actC cm (klT.get b) (cG repT t)) - 1) / 32) - 1) / 4) i)) 0

/-- Column data of the Klein reps: field `b` (11 bits) of `ys[j]` is `2 t₂ + [χ_S(μ) = -1]` where
`κ_b · rep_{ks[j]} = ν_μ · rep_{t₂}`. -/
def klColsOK (cm eM repT klT : NT) (S : ℕ) (ks ys : List ℕ) : Bool :=
  eqL (ks.map (fun _ => 0)) (ys.map (fun _ => 0)) &&
  allIdx ys (fun j yv => allR 4 (fun b =>
    let v := eG eM (actC cm (klT.get b) (cG repT (ks.getD j 0))) - 1
    Nat.beq ((yv >>> (11 * b)) &&& 2047) (2 * (v / 32) + (bif decide (chiS5 S (v % 32) = -1) then 1 else 0)))) 0

/-- Row data of a Klein rep `x̄ = rep_t`: `(r, π⁻¹-table, S')` with `rep_t = π · x₀_r`, `S' = pullS pc S`. -/
def xInfo (repInfoT piIT : NT) (piCodes : List ℕ) (S t : ℕ) : ℕ × ℕ × ℕ :=
  let ri := cG repInfoT t
  (ri / 128, piIT.get (ri % 128), pullS (piCodes.getD (ri % 128) 0 / 32) S)

/-- The four `ψ`-block rows `i` (entries `j ≥ i`) of base character `S`. -/
def blockRows4 (cm eM repT repInfoT piIT : NT) (piCodes : List ℕ) (rowTs : List NT) (S : ℕ)
    (ks ys : List ℕ) (i : ℕ) : List (List ℤ) :=
  let xi := xInfo repInfoT piIT piCodes S (ks.getD i 0)
  blockRow cm eM repT rowTs xi.1 xi.2.1 xi.2.2 (ys.drop i)

/-- **LDL segment**: rows `is` (increasing, consecutive) of the four `ψ`-blocks; `Cs ψ` the factor
rows, `Ws ψ` the weights, `accs` the column accumulators before the segment; returns the
accumulators after it. -/
def ldlSeg (cm eM repT repInfoT piIT : NT) (piCodes : List ℕ) (rowTs : List NT) (S : ℕ)
    (ks ys : List ℕ) (Cs : List (List (List ℤ))) (Ws : List (List ℤ)) :
    List ℕ → List (List ℤ) → Option (List (List ℤ))
  | [], accs => some accs
  | i :: is, accs =>
    let bs := blockRows4 cm eM repT repInfoT piIT piCodes rowTs S ks ys i
    let step := fun (psi : ℕ) => ldlRowStep (bs.getD psi []) (((Ws.getD psi []).getD i 1))
      ((Ws.getD psi []).drop i) ((Cs.getD psi []).getD i []) ((Cs.getD psi []).drop i) (accs.getD psi [])
    match step 0, step 1, step 2, step 3 with
    | some a0, some a1, some a2, some a3 =>
        ldlSeg cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws is [a0, a1, a2, a3]
    | _, _, _, _ => none

/-- Target integer coefficients: `q₁(a,b) = 20·QDelta 5 (13/10) a b`. -/
def cDZ (a : ℕ) : ℤ := bif Nat.beq a 0 then 80 else -1
def qC1 (p : ℕ) : ℤ :=
  let a := p / 81
  let b := p % 81
  20 * cDZ a * cDZ b - 13 * ((bif Nat.beq a 0 then cDZ b else 0) + (bif Nat.beq b 0 then cDZ a else 0))

/-- Integer Adj/Op Gram form (`kop` weight on non-adjacent pairs), mirroring `QAdjOp` without `μ`. -/
def cEdgeZ (e : ℕ × ℕ) (a : ℕ) : ℤ :=
  bif Nat.beq a 0 then 8 else bif (edgeL 5 a == e) then -1 else 0
def adjOpZ (kop : ℤ) (a b : ℕ) : ℤ :=
  let edges := ((List.range 5).flatMap (fun i => (List.range 5).filterMap
    (fun j => if i < j then some (i, j) else none)))
  (edges.map (fun e => (edges.map (fun f =>
      bif (e == f) then 0 else
      (bif (e.1 == f.1 || e.1 == f.2 || e.2 == f.1 || e.2 == f.2) then 1 else kop) *
        cEdgeZ e a * cEdgeZ f b)).sum)).sum
/-- `q₂(a,b) = 200·QAdjOp 5 2 (7/25) a b`. -/
def qC2 (p : ℕ) : ℤ :=
  let a := p / 81
  let b := p % 81
  200 * adjOpZ 2 a b - 28 * ((bif Nat.beq a 0 then cDZ b else 0) + (bif Nat.beq b 0 then cDZ a else 0))

/-- **Class sums** of one certificate for classes `c0, c0+1, …`: for each class, its group keys `ks`
(value `val(k)`, multiplicity `mult(k)`), its target pairs `ts`, and its residual `res(c)`:
`Dq · Σ mult·val − SC · Σ q + res = 0`. -/
def classSumOK (valT multT resT : NT) (q : ℕ → ℤ) (Dq SC : ℤ) (kl tl : List (List ℕ)) (c0 : ℕ) : Bool :=
  (List.rec (motive := fun _ => List (List ℕ) → ℕ → Bool) (fun _ _ => true)
    (fun ks _ ih tl c =>
      let tsL := tl.headD []
      let u := ks.foldr (fun k acc => acc + (pget multT 32 4294967295 k : ℤ) * sv (p8 valT k)) 0
      let tq := tsL.foldr (fun p acc => acc + q p) 0
      decide (Dq * u - SC * tq + sv (p8 resT c) = 0) && ih (tl.drop 1) (c + 1)) kl) tl c0

/-- Residual facts for classes `cs`: `res (icls c) = res c`, `icls (icls c) = c`. -/
def resSymOK (resT iclT : NT) (cs : List ℕ) : Bool :=
  allL cs (fun c => let ic := w34 iclT c / 1048576
    Nat.beq (p8 resT ic) (p8 resT c) && Nat.beq (w34 iclT ic / 1048576) c)

/-- `Σ res = 0` and `16 · Σ |res| ≤ bound` over the classes `cs`. -/
def resBoundOK (resT : NT) (cs : List ℕ) (bound : ℤ) : Bool :=
  decide (cs.foldr (fun c acc => acc + sv (p8 resT c)) 0 = 0) &&
  decide (16 * cs.foldr (fun c acc => acc + |sv (p8 resT c)|) 0 ≤ bound)

/-- Multiplicities of the group keys of row `r` (`gs` groups with `sizes`): `mult = cnt r · size`. -/
def multOK (multT : NT) (r cntr : ℕ) (sizes : List ℕ) : Bool :=
  allIdx sizes (fun g sz => Nat.beq (pget multT 32 4294967295 (2048 * r + g)) (cntr * sz)) 0

/-- Shape of the LDL data: four `ψ`-blocks, `n` weights (positive) and `n` lower-triangular factor rows. -/
def ldlDataOK (Cs : List (List (List ℤ))) (Ws : List (List ℤ)) (n : ℕ) : Bool :=
  allR 4 (fun ψ => Nat.beq (Ws.getD ψ []).length n && Nat.beq (Cs.getD ψ []).length n &&
    allR n (fun i => decide (0 < (Ws.getD ψ []).getD i 1) && Nat.ble ((Cs.getD ψ []).getD i []).length (i + 1)))

end Submission.PTCert

end
