import Submission.Work.PTCert.Kernel

/-!
# PTCert — Bool checks of the shared (certificate-independent) structure

Data layout: `NOTES_LEAD_checker.md` §2.  Every function is a structural recursion
(`List.rec`/`Nat.rec`/`NT.rec`) so that `decide +kernel` evaluates it.
-/

set_option autoImplicit false

noncomputable section

namespace Submission.PTCert

/-- Packed tree lookup: leaves hold `64` fields of `w` bits; `m = 2^w - 1`. -/
def pget (t : NT) (w m i : ℕ) : ℕ := (t.get (i / 64) >>> (w * (i % 64))) &&& m

/-- Field widths of the packed trees. -/
abbrev wE : ℕ := 15
abbrev wL : ℕ := 11
abbrev wC : ℕ := 14
abbrev wR : ℕ := 5
abbrev wK : ℕ := 28
abbrev eG (t : NT) (i : ℕ) : ℕ := pget t wE 32767 i
abbrev lG (t : NT) (i : ℕ) : ℕ := pget t wL 2047 i
abbrev cG (t : NT) (i : ℕ) : ℕ := pget t wC 16383 i
abbrev rG (t : NT) (i : ℕ) : ℕ := pget t wR 31 i
abbrev kG (t : NT) (i : ℕ) : ℕ := pget t wK 268435455 i

/-- `p` holds on every element. -/
def allL (l : List ℕ) (p : ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => p a && ih) l

/-- `p k` for all `k < n`. -/
def allR (n : ℕ) (p : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => p k && ih) n

/-- `p i a` for the elements `a` of `l` with positions `i = i0, i0+1, …`. -/
def allIdx (l : List ℕ) (p : ℕ → ℕ → Bool) (i0 : ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true) (fun a _ ih i => p i a && ih (i + 1)) l i0

/-- Equality of lists of naturals (kernel form). -/
def eqL (l m : List ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun a _ ih m => List.rec (motive := fun _ => Bool) false (fun b t _ => Nat.beq a b && ih t) m) l m

/-- Strictly increasing. -/
def strictInc (l : List ℕ) : Bool :=
  (List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun a _ ih prev => Nat.ble prev a && ih (a + 1)) l) 0

/-- Pack four letters. -/
def pack4 (w : List ℕ) : ℕ := w.foldr (fun k acc => k + 128 * acc) 0

/-- Unpack four letters. -/
def unpack4 (v : ℕ) : List ℕ := [v % 128, (v / 128) % 128, (v / 16384) % 128, (v / 2097152) % 128]

/-- The valid permutation codes, computed. -/
def allPCk : List ℕ := (List.range 32768).filter (fun pc => validPC 5 pc)

/-- Tables `T.get i` are correct for the codes `codes[i]` (`code = 32 pc + sc`). -/
def tabsOK (codes : List ℕ) (T : NT) : Bool :=
  allIdx codes (fun i c => tabOK (c / 32) (c % 32) (T.get i)) 0

/-- **E-structure, per chunk of the E-order list.** Codes are normal, in `E` (membership tree
`eM`: value `32 t + sc + 1`), and `z = ν_sc · rep_t`. -/
def eChunkOK (cm eM nT repT : NT) (l : List ℕ) : Bool :=
  allL l (fun z =>
    let v := eG eM z - 1
    Nat.blt z 10368 && Nat.blt (z % 128) 81 && Nat.blt (z / 128) 81 &&
    Nat.beq (normC cm (z / 128) (z % 128)) z && !(Nat.beq (eG eM z) 0) &&
    Nat.beq (actC cm (nT.get (v % 32)) (cG repT (v / 32))) z)

/-- Completeness of `E`: every normalised pair is in `E` (rows `a ∈ as`). -/
def eCompleteOK (cm eM : NT) (as : List ℕ) : Bool :=
  allL as (fun a => allR 81 (fun b => !(Nat.beq (eG eM (normC cm a b)) 0)))

/-- `E` is exactly the membership tree's support, without repetitions. -/
def eExactOK (eM : NT) (eAll : List ℕ) : Bool :=
  eqL ((List.range 10368).filter (fun c => !(Nat.beq (eG eM c) 0))) (msortK 40 eAll) &&
  strictInc (msortK 40 eAll)

/-- Model key of a code (injective encoding of the images of the generators). -/
def modelKey (c : ℕ) : ℕ :=
  ((List.range 5).map (fun i => prodImg 5 [c / 128, c % 128] i)).foldr
    (fun w acc => (w.foldr (fun l a => (l + 1) + 16 * a) 0) + 16 ^ (w.length) * (11 + 16 * acc)) 0

/-- Faithfulness: distinct codes of `E` are distinct automorphisms. -/
def eFaithfulOK (eAll : List ℕ) : Bool := strictInc (msortK 40 (eAll.map modelKey))

/-- N-reps: rep invariance under the sign flips (reps `t ∈ ts`). -/
def repInvOK (cm eM nT repT : NT) (ts : List ℕ) : Bool :=
  allL ts (fun t => allR 32 (fun sc => Nat.beq ((eG eM (actC cm (nT.get sc) (cG repT t)) - 1) / 32) t))

/-- N-reps are `π · x₀` (info `128 r + π`). -/
def repRowOK (cm piT rowT repT repInfoT : NT) (ts : List ℕ) : Bool :=
  allL ts (fun t => let v := cG repInfoT t
    Nat.beq (actC cm (piT.get (v % 128)) (cG rowT (v / 128))) (cG repT t))

/-- Scan of all codes on a row `x₀ = (a,b)`: the list of codes fixing `x₀`, with a `0` sentinel for
every code mapping `x₀` to a *different* row (`rowIdx`: code ↦ `r + 1`, `0` if not a row). -/
def scanRow (cm rowIdx : NT) (a b x0 : ℕ) (pcs : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) []
    (fun pc _ ih => Nat.rec (motive := fun _ => List ℕ) ih
      (fun sc ih2 =>
        let y := normC cm (actL 5 pc sc a) (actL 5 pc sc b)
        bif Nat.beq y x0 then (32 * pc + sc) :: ih2
        else bif Nat.beq (rG rowIdx y) 0 then ih2 else 0 :: ih2) 32) pcs

/-- Class witness of a 4-letter word `w`: entry `2^20 cls + code`. -/
def clsWitOK (canonT : NT) (w : List ℕ) (v : ℕ) : Bool :=
  let code := v % 1048576
  let cw := kG canonT (v / 1048576)
  let sw := w.map (fun k => actL 5 (code / 32) (code % 32) k)
  validPC 5 (code / 32) && (Nat.beq (pack4 sw) cw || modelEq 5 sw (unpack4 cw))

/-- Packed class-witness lookup: `64` fields of `34` bits, entry `2^20 cls + code`. -/
def w34 (t : NT) (i : ℕ) : ℕ := pget t 34 17179869183 i

/-- Class witnesses of the groups `gs` of row `r`, `x₀ = (a,b)`: key `2048 r + g` in `gclT`. -/
def gclsOK (canonT gclT grepT : NT) (r a b : ℕ) (gs : List ℕ) : Bool :=
  allL gs (fun g => let c := cG grepT g
    clsWitOK canonT [invLk b, invLk a, c / 128, c % 128] (w34 gclT (2048 * r + g)))

/-- Class witnesses of the target terms `p = 81 a + b` (word `[a⁻¹, b]`). -/
def tclsOK (canonT tclT : NT) (ps : List ℕ) : Bool :=
  allL ps (fun p => clsWitOK canonT [invLk (p / 81), p % 81, 0, 0] (w34 tclT p))

/-- Class witnesses of the inverses of the canonical words. -/
def iclsOK (canonT iclT : NT) (cs : List ℕ) : Bool :=
  allL cs (fun c => clsWitOK canonT ((unpack4 (kG canonT c)).reverse.map invLk) (w34 iclT c))

/-- Members of the groups `g0, g0+1, …` of a row, group-major: each group is a list of entries
`4096 z + s` with `z = stab_s · rep_g`, `lab z = g`, `z ∈ E`, codes strictly increasing, and the
group sizes are `sizes`. -/
def memGroupsOK (cm eM labT stabT grepT : NT) (gl : List (List ℕ)) (sizes : List ℕ) (g0 : ℕ) : Bool :=
  eqL (gl.map List.length) sizes &&
  (List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun l _ ih g =>
      strictInc (l.map (fun v => v / 4096)) &&
      allL l (fun v => let z := v / 4096
        !(Nat.beq (eG eM z) 0) && Nat.beq (lG labT z) g &&
        Nat.beq (actC cm (stabT.get (v % 4096)) (cG grepT g)) z) && ih (g + 1)) gl g0)

/-- Sum of a list. -/
def sumL (l : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => a + ih) l

/-- Stabiliser closure of the groups `gs` (all stabiliser indices `ss`). -/
def closOK (cm labT stabT grepT : NT) (ss gs : List ℕ) : Bool :=
  allL gs (fun g => let c := cG grepT g
    allL ss (fun s => Nat.beq (lG labT (actC cm (stabT.get s) c)) g))

/-- Labels of the sign-flip orbit of each rep, for one row: the leaf `t` of `olT` packs the
`32` group ids (11 bits) of `ν_sc · rep_t`, `sc < 32` (`labOf` gives the label of a code in row `r`). -/
def orbLabOK (cm nT repT olT : NT) (labOf : ℕ → ℕ) (ts : List ℕ) : Bool :=
  allL ts (fun t => let v := olT.get t
    allR 32 (fun sc => Nat.beq ((v >>> (11 * sc)) &&& 2047) (labOf (actC cm (nT.get sc) (cG repT t)))))

/-- Label in row `0` (the identity row): the row of the element. -/
def lab0 (eM repInfoT : NT) (z : ℕ) : ℕ := (cG repInfoT ((eG eM z - 1) / 32)) / 128

/-- Class-grouped lists (`kl[c - c0]` for classes `c = c0, c0+1, …`): every entry `k` of the list of
class `c` has class `c` in the witness tree `clT` (`w34 clT k / 2^20 = c`), and `c < ncls`. -/
def classKeysOK (clT : NT) (kl : List (List ℕ)) (c0 ncls : ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun l _ ih c => Nat.blt c ncls && allL l (fun k => Nat.beq (w34 clT k / 1048576) c) && ih (c + 1)) kl c0

/-- All group keys `2048 r + g`, `g < ng[r]`, sorted. -/
def allKeys (ngs : List ℕ) : List ℕ :=
  (List.range ngs.length).flatMap (fun r => (List.range (ngs.getD r 0)).map (fun g => 2048 * r + g))

/-- Count of the elements satisfying `p` (kernel form). -/
def countL (l : List ℕ) (p : ℕ → Bool) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => (bif p a then 1 else 0) + ih) l

/-- Each N-representative is its own entry: `eM (rep t) = 32 t + 1` (sign code `0`). -/
def repSelfOK (eM repT : NT) (ts : List ℕ) : Bool :=
  allL ts (fun t => Nat.blt (cG repT t) 10368 && Nat.beq (eG eM (cG repT t)) (32 * t + 1))

/-- Two letter tables are mutually inverse on the letters `< 81`. -/
def invTabOK (t t' : ℕ) : Bool :=
  allR 81 (fun k => Nat.beq (lk t (lk t' k)) k && Nat.beq (lk t' (lk t k)) k)

/-- `piIT.get i` is the inverse table of `piT.get i`, `i < n`. -/
def piInvOK (piT piIT : NT) (n : ℕ) : Bool := allR n (fun i => invTabOK (piT.get i) (piIT.get i))

/-- Row counts: `cnt[r] = #{z ∈ es : row z = r}` (row via `lab0`). -/
def cntOK (eM repInfoT : NT) (es : List ℕ) (cnt : List ℕ) : Bool :=
  allIdx cnt (fun r c => Nat.beq (countL es (fun z => Nat.beq (lab0 eM repInfoT z) r)) c) 0

/-- Rows are N-representatives' rows: the row code `rowT r` has `lab0 = r`. -/
def rowSelfOK (eM rowT repInfoT : NT) (n : ℕ) : Bool :=
  allR n (fun r => Nat.beq (lab0 eM repInfoT (cG rowT r)) r && Nat.blt (cG rowT r) 10368 &&
    !(Nat.beq (eG eM (cG rowT r)) 0))

/-- The row-index tree marks the row codes: `rowIdx (rowT r) = r + 1`. -/
def rowIdxOK (rowT rowIdx : NT) (n : ℕ) : Bool :=
  allR n (fun r => Nat.beq (rG rowIdx (cG rowT r)) (r + 1))

/-- Group representatives of a row are codes of `E` with their own label. -/
def grepOK (eM labT grepT : NT) (ng : ℕ) : Bool :=
  allR ng (fun g => Nat.blt (cG grepT g) 10368 && !(Nat.beq (eG eM (cG grepT g)) 0) &&
    Nat.beq (lG labT (cG grepT g)) g)

/-- Canonical words have letters `< 81`. -/
def canonOK (canonT : NT) (n : ℕ) : Bool :=
  allR n (fun c => allL (unpack4 (kG canonT c)) (fun k => Nat.blt k 81))

end Submission.PTCert

end
