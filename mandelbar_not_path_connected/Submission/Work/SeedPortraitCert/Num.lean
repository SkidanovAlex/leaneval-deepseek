/-
# SeedPortraitCert — the decidable checkers of the ray-chain certificate

Area `Submission/Work/SeedPortraitCert/`.  This module contains the `ℤ`-arithmetic checkers that
the generated data (`Data.lean`) is verified against; they are parametric in the data lists, so
the only generated content is the numerical data and the per-level `decide` theorems
(`Check.lean`).

The conventions are those of the sibling areas `SeedCertRay` and `TripodCert` (whose `Core.lean` /
`Num.lean` this module follows): mantissas are integers at scale `MSZ = 2^40`, disks are
`SeedCertRay.Disk`, the parameter box is `SeedCertRay.Xb` (centre `PXM + i PYM`, radius
`RADM/2^40`), and a step certificate is a triple `(s, ρ, M)`.

The only structural difference to `TripodCert` is that the chain has `10` angle classes forming
*two* cycles of length `5`: the successor of the class `j` is the class of `T (θ j)`, i.e.

  `sucP j = (j % 5 + 1) % 5` for `j < 5` and `sucP j = 5 + (j % 5 + 1) % 5` for `5 ≤ j`.

* `stepOKBP` : (D1) for one pull-back step, identical to `TripodCert.stepOKBT`;
* `chkLevelP` : the ten-by-six checker of one level;
* `hpDiskB`, `chkDirP` : (D2) for one angle: one open half-plane containing all sub-disks of the
  two levels;
* `vdirOfP`, `boxOfP` : the decoding of the direction and disk data.
-/
import Mathlib
import Submission.Work.SeedCertRay.Core
import Submission.Work.SeedCertRay.Q
import Submission.Work.SeedCertRay.Disk
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedPortraitCert

open Work.SeedCertRay

/-- The ten angle classes of the chain. -/
def angQsP : List Nat := List.range 10

theorem mem_angQsP {j : Nat} (hj : j < 10) : j ∈ angQsP := by
  rw [angQsP]; exact List.mem_range.mpr hj

theorem angQsP_eq : angQsP = List.range 10 := rfl

/-- The sub-disk indices of one angle class: there are `NC = 6` of them. -/
def subQsP : List Nat := List.range NC

theorem mem_subQsP {i : Nat} (hi : i < NC) : i ∈ subQsP := by
  rw [subQsP]; exact List.mem_range.mpr hi

/-- **The successor of an angle class**: the class of `T (θ j)`.  Classes `0 … 4` are the
`12/33`-cycle, classes `5 … 9` the `13/33`-cycle. -/
def sucP (j : Nat) : Nat := if j < 5 then (j + 1) % 5 else 5 + ((j + 1) % 5)

/-- The successor of the class `j` is `(j+1) % 5` inside the first cycle. -/
theorem sucP_of_lt {j : Nat} (hj : j < 5) : sucP j = (j + 1) % 5 := by
  simp only [sucP, if_pos hj]

/-- The successor of the class `j` is `5 + (j+1) % 5` inside the second cycle. -/
theorem sucP_of_ge {j : Nat} (hj : 5 ≤ j) : sucP j = 5 + ((j + 1) % 5) := by
  simp only [sucP, if_neg (by omega : ¬ j < 5)]

/-- **(D1) for one step**, in mantissa arithmetic, with the target radius read off the *target*
data (the variant of `SeedCertRay.stepOKB` needed because the periodic family of this certificate
has target radii that are not the sharp radii of the step certificate).  Identical to
`Work.TripodCert.stepOKBT`. -/
def stepOKBP (s t c : List Int) (PX PY RAD : Int) (qs qt : Nat) : Bool :=
  decide (0 ≤ gI c (3*qt)) &&
  decide (0 ≤ gI c (3*qt+1)) &&
  decide (gI c (3*qt+1) ≤ 2*gI c (3*qt)) &&
  decide (0 ≤ gI t (3*qt+2)) &&
  decide (gI t (3*qt+2) ≤ 2*gI c (3*qt)) &&
  decide (gI c (3*qt)*gI c (3*qt) ≤ gI t (3*qt)*gI t (3*qt) + gI t (3*qt+1)*gI t (3*qt+1)) &&
  decide ((gI c (3*qt)*gI c (3*qt) + (gI s (3*qs+2) + RAD)*MSZ)
            * (gI c (3*qt)*gI c (3*qt) + (gI s (3*qs+2) + RAD)*MSZ)
          ≤ MSZ*MSZ*((gI s (3*qs)-PX)*(gI s (3*qs)-PX)
                     + (gI s (3*qs+1)-PY)*(gI s (3*qs+1)-PY))) &&
  decide (gI s (3*qs+2) + RAD ≤ gI c (3*qt+2)) &&
  decide (MSZ*MSZ*((gI c (3*qt+2) - gI s (3*qs+2) - RAD)*(gI c (3*qt+2) - gI s (3*qs+2) - RAD))
          ≥ ((gI s (3*qs)-PX)*MSZ - (gI t (3*qt)*gI t (3*qt) - gI t (3*qt+1)*gI t (3*qt+1)))
            * ((gI s (3*qs)-PX)*MSZ - (gI t (3*qt)*gI t (3*qt) - gI t (3*qt+1)*gI t (3*qt+1)))
            + ((gI s (3*qs+1)-PY)*MSZ + 2*gI t (3*qt)*gI t (3*qt+1))
              * ((gI s (3*qs+1)-PY)*MSZ + 2*gI t (3*qt)*gI t (3*qt+1))) &&
  decide (MSZ*gI c (3*qt+2) ≤ gI t (3*qt+2)*(2*gI c (3*qt) - gI t (3*qt+2)))

/-- The (D1) checker of one level: all `10 × 6` pairs of angle class and sub-disk. -/
def chkLevelP (s t c : List Int) (PX PY RAD : Int) : Bool :=
  allS angQsP (fun j => allS subQsP (fun i =>
    stepOKBP s t c PX PY RAD ((sucP j) * NC + i) (j * NC + i)))

/-- The (D2) mantissa test of one sub-disk of a data list. -/
def hpDiskB (p q : Int) (l : List Int) (j i : Nat) : Bool :=
  hpB p q (gI l (3*(j*NC+i))) (gI l (3*(j*NC+i)+1)) (gI l (3*(j*NC+i)+2))

/-- The (D2) checker of one level: one direction per angle class, tested against the sub-disks of
the target level `t` and of the source level `s`. -/
def chkDirP (dl t s : List Int) : Bool :=
  allS angQsP (fun j => allS subQsP (fun i =>
    hpDiskB (gI dl (2*j)) (gI dl (2*j+1)) t j i &&
    hpDiskB (gI dl (2*j)) (gI dl (2*j+1)) s j i))

/-- The half-plane direction of angle class `j` of a direction list. -/
def vdirOfP (dl : List Int) (j : Nat) : ℚ × ℚ :=
  (Q (gI dl (2*(j % 10))), Q (gI dl (2*(j % 10) + 1)))

/-- The `i`-th sub-disk of angle class `j` of a disk list. -/
def boxOfP (l : List Int) (j : Nat) (i : Fin NC) : Work.SeedCertRay.Disk :=
  Work.SeedCertRay.dskOf l ((j % 10) * NC + i.val)

end Work.SeedPortraitCert
