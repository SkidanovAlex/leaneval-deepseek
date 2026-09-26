import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls
import Submission.Work.PTCert.Data.LabTs
import Submission.Work.PTCert.Data.R0
import Submission.Work.PTCert.Data.K0
import Submission.Work.PTCert.Data.K1
import Submission.Work.PTCert.Data.K2
import Submission.Work.PTCert.Data.K3
import Submission.Work.PTCert.Data.K4
import Submission.Work.PTCert.Data.K5

/-!
# PTCert — glue layer 2: the concrete objects of the rank-5 certificate and the semantic Props

`D.*` are the emitted data (`Data/*.lean`); the kernel theorems are in `Checks/*.lean`.
* Concrete objects: the index type `EI` (codes of B₂), the family `fE`, the action `actE`
  (`conjAct`), the N-action `actN`, the N-representatives `repE`/`nuE`, the matrices `Umat`/`Pmat`
  of a value table `pv : ℕ → ℤ` (key `2048 r + g` ↦ integer value of `P(x₀_r, group g)`).
* Semantic Props of the shared data (`ESem`, `TabSem`, `NSem`, `RowSem`, `GroupSem`, `OrbLabSem`,
  `ClassSem`, `KleinSem k`): each is the plain meaning of a family of kernel checks.
* Math Props (`ActSetup`, `NStructure`, `RowFacts`, ...): see `NOTES_LEAD_glue.md`.
Definitions and Props only.
-/

open OnPropertyT Submission.FreeGroupAut Submission.RouteB
open scoped BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

namespace Submission.PTCert.G

open Submission.PTCert Submission.PTCert.D

/-! ## Per-row / per-character lists of the data -/

def grepTs : List NT := [grepT0, grepT1, grepT2, grepT3, grepT4, grepT5, grepT6, grepT7, grepT8, grepT9, grepT10, grepT11, grepT12, grepT13, grepT14, grepT15, grepT16, grepT17]
def stabLs : List (List ℕ) := [[], stabL1, stabL2, stabL3, stabL4, stabL5, stabL6, stabL7, stabL8, stabL9, stabL10, stabL11, stabL12, stabL13, stabL14, stabL15, stabL16, stabL17]
def stabTs : List NT := [NT.leaf 0, stabT1, stabT2, stabT3, stabT4, stabT5, stabT6, stabT7, stabT8, stabT9, stabT10, stabT11, stabT12, stabT13, stabT14, stabT15, stabT16, stabT17]
def sizesL : List (List ℕ) := [cntL, sizes1, sizes2, sizes3, sizes4, sizes5, sizes6, sizes7, sizes8, sizes9, sizes10, sizes11, sizes12, sizes13, sizes14, sizes15, sizes16, sizes17]
def olTs : List NT := [olT0, olT1, olT2, olT3, olT4, olT5, olT6, olT7, olT8, olT9, olT10, olT11, olT12, olT13, olT14, olT15, olT16, olT17]
def klCodesL : List (List ℕ) := [klCodes0, klCodes1, klCodes2, klCodes3, klCodes4, klCodes5]
def klTs : List NT := [klT0, klT1, klT2, klT3, klT4, klT5]
def ksL : List (List ℕ) := [ks0, ks1, ks2, ks3, ks4, ks5]
def ysL : List (List ℕ) := [ys0, ys1, ys2, ys3, ys4, ys5]
def kwTs : List NT := [kwT0, kwT1, kwT2, kwT3, kwT4, kwT5]
def vwTs : List NT := [vwT0, vwT1, vwT2, vwT3, vwT4, vwT5]
/-- Group keys of each class `c < ncls` (`klist[c]`), target pairs of each class (`tlist[c]`). -/
def klist : List (List ℕ) := kl0 ++ kl1 ++ kl2 ++ kl3 ++ kl4 ++ kl5 ++ kl6 ++ kl7 ++ kl8 ++ kl9 ++ kl10 ++ kl11 ++ kl12 ++ kl13 ++ kl14
def tlist : List (List ℕ) := tl0 ++ tl1 ++ tl2 ++ tl3 ++ tl4 ++ tl5 ++ tl6 ++ tl7 ++ tl8 ++ tl9 ++ tl10 ++ tl11 ++ tl12 ++ tl13 ++ tl14
def ncls : ℕ := 7229

/-! ## Lookups -/

def em (z : ℕ) : ℕ := eG eM z
def rp (t : ℕ) : ℕ := cG repT t
def x0c (r : ℕ) : ℕ := cG rowT r
def rinfo (t : ℕ) : ℕ := cG repInfoT t
def labE (r z : ℕ) : ℕ := labOf eM repInfoT labTs r z
def grepE (r g : ℕ) : ℕ := cG (grepTs.getD r (NT.leaf 0)) g
def ngE (r : ℕ) : ℕ := ngL.getD r 0
def ntab (sc : ℕ) : ℕ := nT.get sc
def stabL (r : ℕ) : List ℕ := stabLs.getD r []
def stabTab (r i : ℕ) : ℕ := (stabTs.getD r (NT.leaf 0)).get i
def sizeE (r g : ℕ) : ℕ := (sizesL.getD r []).getD g 0
def keyOf (r g : ℕ) : ℕ := 2048 * r + g
def gcls (k : ℕ) : ℕ := w34 gclT k / 1048576
def tcls (p : ℕ) : ℕ := w34 tclT p / 1048576
def icls (c : ℕ) : ℕ := w34 iclT c / 1048576
def canonW (c : ℕ) : List ℕ := unpack4 (kG canonT c)
def multE (k : ℕ) : ℕ := pget multT 32 4294967295 k
/-- Action of a code on a `B₂`-code, computed letterwise by `actL`. -/
def actCode (c z : ℕ) : ℕ :=
  normC cmT (actL 5 (c / 32) (c % 32) (z / 128)) (actL 5 (c / 32) (c % 32) (z % 128))
/-- The word of the key `(r, g)`: `f(x₀_r)⁻¹ f(grep g)` as 4 letters. -/
def keyWord (r g : ℕ) : List ℕ :=
  [invL (x0c r % 128), invL (x0c r / 128), grepE r g / 128, grepE r g % 128]

/-! ## The index type, the family, the actions -/

def eS : Finset ℕ := eAll.toFinset
abbrev EI : Type := {z : ℕ // z ∈ eS}
def fE (x : EI) : G5 := eltC x.1
abbrev Sg : Finset G5 := SigmaSet 5
def actE (σ : G5) (x : EI) : EI := conjAct fE σ x
/-- The N-action (sign flips). -/
def actN (a : Fin 5 → ZMod 2) (x : EI) : EI := actE (signAut (zBool a)) x
/-- The element of `EI` with code `z` (or `x` if `z` is not a code of `B₂`). -/
def toEI (z : ℕ) (x : EI) : EI := if h : z ∈ eS then ⟨z, h⟩ else x
def repE (x : EI) : EI := toEI (rp ((em x.1 - 1) / 32)) x
def nuE (x : EI) : Fin 5 → ZMod 2 := zOfSc ((em x.1 - 1) % 32)
/-- The element `rp t` (N-representative number `t`), resp. the row code `x0c r`, as elements of `EI`. -/
def repEI (t : ℕ) (x : EI) : EI := toEI (rp t) x
def x0E (r : ℕ) (x : EI) : EI := toEI (x0c r) x
def stabCard (x : EI) : ℕ := (Sg.filter (fun σ => actE σ x = x)).card
/-- Row-supported matrix of a value table. -/
def Umat (pv : ℕ → ℤ) : Matrix EI EI ℝ := fun x y =>
  ∑ r ∈ Finset.range 18, if x.1 = x0c r then (pv (keyOf r (labE r y.1)) : ℝ) / (stabCard x : ℝ) else 0
/-- The `Σ`-invariant Gram matrix. -/
def Pmat (pv : ℕ → ℤ) : Matrix EI EI ℝ := avgMat Sg actE (Umat pv)
/-- Base characters `S_k = {0, …, k-1}` (bit mask `2^k - 1`). -/
def Sk (k : ℕ) : ℕ := 2 ^ k - 1
def SkF (k : ℕ) : Finset (Fin 5) := maskSet (Sk k)
/-- Klein generators for the base character `k` and the Klein element `b < 4` (`b = b₀ + 2 b₁`). -/
def kg1 (k : ℕ) : Equiv.Perm (Fin 5) :=
  if k ≤ 1 then Equiv.swap 1 2 * Equiv.swap 3 4 else if k ≤ 3 then Equiv.swap 0 1
  else Equiv.swap 0 1 * Equiv.swap 2 3
def kg2 (k : ℕ) : Equiv.Perm (Fin 5) :=
  if k ≤ 1 then Equiv.swap 1 3 * Equiv.swap 2 4 else if k = 2 then Equiv.swap 2 3
  else if k = 3 then Equiv.swap 3 4 else Equiv.swap 0 2 * Equiv.swap 1 3
def kleinPerm (k b : ℕ) : Equiv.Perm (Fin 5) := kg1 k ^ (b % 2) * kg2 k ^ (b / 2)
def bval (b : Fin 2 → ZMod 2) : ℕ := (b 0).val + 2 * (b 1).val
/-- The Klein action on `EI`. -/
def kapE (k : ℕ) (b : Fin 2 → ZMod 2) (x : EI) : EI := actE (permAut (kleinPerm k (bval b))) x

/-! ## Semantic Props of the shared data (each = the meaning of a family of kernel checks) -/

/-- `E`: codes, closure, faithfulness, membership tree. -/
def ESem : Prop :=
  CmSound cmT ∧ eAll.Nodup ∧ (∀ z ∈ eAll, z / 128 < 81 ∧ z % 128 < 81 ∧ normC cmT (z / 128) (z % 128) = z) ∧
  (∀ a < 81, ∀ b < 81, normC cmT a b ∈ eAll) ∧
  (∀ z ∈ eAll, ∀ z' ∈ eAll, eltC z = eltC z' → z = z') ∧
  (∀ z < 10368, z ∈ eAll ↔ em z ≠ 0)

/-- Letter tables of the sign flips and of the row-transport permutations (and their inverses). -/
def TabSem : Prop :=
  (∀ sc < 32, TabOf (signAut (scBits sc)) (ntab sc) ∧ ∀ k < 81, lk (ntab sc) k < 81) ∧
  (∀ i < 120, validPC 5 (piCodes.getD i 0 / 32) = true ∧ piCodes.getD i 0 % 32 = 0 ∧
      TabOf (codeElt (piCodes.getD i 0)) (piT.get i) ∧ TabOf (codeElt (piCodes.getD i 0))⁻¹ (piIT.get i) ∧
      ∀ k < 81, lk (piT.get i) k < 81 ∧ lk (piIT.get i) k < 81)

/-- N-orbit structure: every code is `ν_sc · rep_t`; reps are their own entries; rep invariance. -/
def NSem : Prop :=
  (∀ z ∈ eAll, 1 ≤ em z ∧ (em z - 1) / 32 < 611 ∧
      actC cmT (ntab ((em z - 1) % 32)) (rp ((em z - 1) / 32)) = z) ∧
  (∀ t < 611, rp t ∈ eAll ∧ em (rp t) = 32 * t + 1) ∧
  (∀ t < 611, ∀ sc < 32, (em (actC cmT (ntab sc) (rp t)) - 1) / 32 = t)

/-- Rows: row transport of the reps, row labels, row counts, the stabiliser scan, stabiliser tables. -/
def RowSem : Prop :=
  x0c 0 = 0 ∧ (∀ r < 18, x0c r ∈ eAll) ∧
  (∀ t < 611, rinfo t / 128 < 18 ∧ rinfo t % 128 < 120 ∧
      actC cmT (piT.get (rinfo t % 128)) (x0c (rinfo t / 128)) = rp t) ∧
  (∀ r < 18, labE 0 (x0c r) = r) ∧
  (∀ z ∈ eAll, labE 0 z < 18) ∧
  (∀ r < 18, (eAll.filter (fun z => labE 0 z = r)).length = cntL.getD r 0) ∧
  (∀ r < 18, 1 ≤ r → ∀ c : ℕ, validPC 5 (c / 32) = true →
      ((actCode c (x0c r) = x0c r ↔ c ∈ stabL r) ∧
       ∀ r' < 18, actCode c (x0c r) = x0c r' → r' = r)) ∧
  (∀ r < 18, 1 ≤ r → ∀ i < (stabL r).length,
      validPC 5 ((stabL r).getD i 0 / 32) = true ∧
      ∀ k < 81, lk (stabTab r i) k = actL 5 ((stabL r).getD i 0 / 32) ((stabL r).getD i 0 % 32) k)

/-- Groups of the rows `r ≥ 1`: labels, member witnesses, representatives, closure, sizes. -/
def GroupSem : Prop :=
  ngE 0 = 18 ∧ (∀ g < 18, grepE 0 g = x0c g) ∧
  ∀ r < 18, 1 ≤ r →
    (∀ z ∈ eAll, labE r z < ngE r ∧ ∃ i < (stabL r).length,
        actC cmT (stabTab r i) (grepE r (labE r z)) = z) ∧
    (∀ g < ngE r, grepE r g ∈ eAll ∧ labE r (grepE r g) = g) ∧
    (∀ i < (stabL r).length, ∀ g < ngE r, labE r (actC cmT (stabTab r i) (grepE r g)) = g) ∧
    (∀ g < ngE r, (eAll.filter (fun z => labE r z = g)).length = sizeE r g) ∧
    (sizesL.getD r []).length = ngE r

/-- Orbit labels: field `sc` of `olT_r(t)` is the label of `ν_sc · rep_t` in row `r`. -/
def OrbLabSem : Prop :=
  ∀ r < 18, ∀ t < 611, ∀ sc < 32,
    ((olTs.getD r (NT.leaf 0)).get t >>> (11 * sc)) &&& 2047 = labE r (actC cmT (ntab sc) (rp t))

/-- Classes: canonical words, class witnesses (groups, targets, inverses), the class-grouped
partitions of the keys and of the target pairs, multiplicities. -/
def ClassSem : Prop :=
  (∀ c < ncls, (canonW c).length = 4 ∧ ∀ k ∈ canonW c, k < 81) ∧
  (∀ r < 18, ∀ g < ngE r, gcls (keyOf r g) < ncls ∧ ∃ σ ∈ Sg,
      σ * lprod 5 (keyWord r g) * σ⁻¹ = lprod 5 (canonW (gcls (keyOf r g)))) ∧
  (∀ p < 6561, tcls p < ncls ∧ ∃ σ ∈ Sg,
      σ * lprod 5 [invL (p / 81), p % 81, 0, 0] * σ⁻¹ = lprod 5 (canonW (tcls p))) ∧
  (∀ c < ncls, icls c < ncls ∧ ∃ σ ∈ Sg,
      σ * (lprod 5 (canonW c))⁻¹ * σ⁻¹ = lprod 5 (canonW (icls c))) ∧
  klist.length = ncls ∧ tlist.length = ncls ∧
  klist.flatten.Perm (allKeys ngL) ∧ tlist.flatten.Perm (List.range 6561) ∧
  (∀ c < ncls, ∀ k ∈ klist.getD c [], gcls k = c) ∧ (∀ c < ncls, ∀ p ∈ tlist.getD c [], tcls p = c) ∧
  ngL.length = 18 ∧
  (∀ r < 18, ∀ g < ngE r, multE (keyOf r g) = cntL.getD r 0 * sizeE r g)

/-- Klein data of the base character `k ≤ 5` (see `kleinCoverOK`, `kleinDistinctOK`, `klColsOK`). -/
def KleinSem (k : ℕ) : Prop :=
  let klT := klTs.getD k (NT.leaf 0)
  let ks := ksL.getD k []
  let ys := ysL.getD k []
  let kwT := kwTs.getD k (NT.leaf 0)
  let vwT := vwTs.getD k (NT.leaf 0)
  (∀ b < 4, ∀ j < 81, lk (klT.get b) j = actL 5 (pcOf (kleinPerm k b)) 0 j) ∧
  (∀ t < 611, (cG kwT t = 0 →
      actC cmT (ntab (rG vwT t)) (rp t) = rp t ∧ chiS5 (Sk k) (rG vwT t) = -1) ∧
    (cG kwT t ≠ 0 →
      (∀ sc < 32, actC cmT (ntab sc) (rp t) = rp t → chiS5 (Sk k) sc = 1) ∧
      (cG kwT t - 1) / 4 < ks.length ∧
      (em (actC cmT (klT.get ((cG kwT t - 1) % 4)) (rp (ks.getD ((cG kwT t - 1) / 4) 0))) - 1) / 32 = t)) ∧
  (∀ i < ks.length, cG kwT (ks.getD i 0) = 1 + 4 * i ∧ ∀ b < 4,
      (cG kwT ((em (actC cmT (klT.get b) (rp (ks.getD i 0))) - 1) / 32) - 1) / 4 = i) ∧
  ys.length = ks.length ∧
  (∀ j < ks.length, ∀ b < 4,
      let v := em (actC cmT (klT.get b) (rp (ks.getD j 0))) - 1
      ((ys.getD j 0 >>> (11 * b)) &&& 2047) = 2 * (v / 32) + (if chiS5 (Sk k) (v % 32) = -1 then 1 else 0))

end Submission.PTCert.G

end
