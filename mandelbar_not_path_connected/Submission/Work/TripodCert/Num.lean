/-
# TripodCert — the decidable checkers of the `b₂`-chain certificate

Area `Submission/Work/TripodCert/`.  This module contains the `ℤ`-arithmetic checkers that the
generated data (`Data.lean`) is verified against; they are parametric in the data lists, so the
only generated content is the numerical data and the per-level `decide` theorems (`Check.lean`).

The conventions are those of the sibling area `SeedCertRay` (whose `Core.lean`/`Q.lean` this
module imports): mantissas are integers at scale `MSZ = 2^40`, boxes/disks are `SeedCertRay.Disk`,
the parameter box is `SeedCertRay.Xb` (centre `PXM + i PYM`, radius `RADM/2^40`), and a step
certificate is a triple `(s, ρ, M)`.

* `stepOKBT` : (D1) for one pull-back step, with the *target radius read off the target data*
  (the variant of `SeedCertRay.stepOKB` needed because the periodic family of this certificate
  has target radii that are not the sharp radii of the step certificate).  Its nine conjuncts are
  those of `SeedCertRay.stepOKB` with the role of the target radius `c1` played by
  `gI t (3*qt+2)`: the two sign/size checks `0 ≤ ρ` and `ρ ≤ 2s` are stated for it, and the last
  check `Ms = gI c (3*qt+1)` is dropped.  Consequently `stepOKBT_sound` is a verbatim
  transcription of `SeedCertRay.stepOKB_sound`;
* `chkLevelT` : the six-by-six checker of one level;
* `hpDiskB`, `chkDirT` : (D2) for one angle: one open half-plane containing all sub-disks of the
  two levels;
* `vdirOf`, `boxOfT` : the decoding of the direction and disk data.
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


namespace Work.TripodCert

open Work.SeedCertRay

/-- The six angle classes of the tripod chain. -/
def angQsT : List Nat := [0, 1, 2, 3, 4, 5]

theorem mem_angQsT {j : Nat} (hj : j < 6) : j ∈ angQsT := by
  interval_cases j <;> decide

theorem angQsT_eq : angQsT = List.range 6 := by decide

/-- **(D1) for one step**, in mantissa arithmetic, with the target radius read off the *target*
data (the variant of `SeedCertRay.stepOKB` for a target family whose radii are prescribed in
advance rather than computed by the step). -/
def stepOKBT (s t c : List Int) (PX PY RAD : Int) (qs qt : Nat) : Bool :=
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

/-- The (D1) checker of one level: all `6 × 6` pairs of angle class and sub-disk. -/
def chkLevelT (s t c : List Int) (PX PY RAD : Int) : Bool :=
  allS angQsT (fun j => allS angQsT (fun i =>
    stepOKBT s t c PX PY RAD (((j + 1) % 6) * NC + i) (j * NC + i)))

/-- The (D2) mantissa test of one sub-disk of a data list. -/
def hpDiskB (p q : Int) (l : List Int) (j i : Nat) : Bool :=
  hpB p q (gI l (3*(j*NC+i))) (gI l (3*(j*NC+i)+1)) (gI l (3*(j*NC+i)+2))

/-- The (D2) checker of one level: one direction per angle class, tested against the sub-disks of
the target level `t` and of the source level `s`. -/
def chkDirT (dl t s : List Int) : Bool :=
  allS angQsT (fun j => allS angQsT (fun i =>
    hpDiskB (gI dl (2*j)) (gI dl (2*j+1)) t j i &&
    hpDiskB (gI dl (2*j)) (gI dl (2*j+1)) s j i))

/-- The half-plane direction of angle class `j` of a direction list. -/
def vdirOf (dl : List Int) (j : Nat) : ℚ × ℚ :=
  (Q (gI dl (2*(j % 6))), Q (gI dl (2*(j % 6) + 1)))

/-- The `i`-th sub-disk of angle class `j` of a disk list. -/
def boxOfT (l : List Int) (j : Nat) (i : Fin NC) : Work.SeedCertRay.Disk :=
  Work.SeedCertRay.dskOf l ((j % 6) * NC + i.val)

/-- **The containment of one sub-disk in a rational closed ball** `‖z - z₀‖ ≤ R`: written in
mantissa arithmetic as `(cx - zx)² + (cy - zy)² ≤ (R - r)²` (with `R ≥ r ≥ 0` this is equivalent
to `‖centre - z₀‖ + r ≤ R`). -/
def inUBall (zx zy R : Int) (l : List Int) (j i : Nat) : Bool :=
  decide ((gI l (3*(j*NC+i)) - zx)*(gI l (3*(j*NC+i)) - zx)
        + (gI l (3*(j*NC+i)+1) - zy)*(gI l (3*(j*NC+i)+1) - zy)
        ≤ (R - gI l (3*(j*NC+i)+2))*(R - gI l (3*(j*NC+i)+2)))

/-- The containment checker of one angle class of a data list. -/
def chkUBall (zx zy R : Int) (l : List Int) (j : Nat) : Bool :=
  allS angQsT (fun i => inUBall zx zy R l j i)

/-- The mantissa test that `‖z‖ ≤ M` for a rational point `z` given by its mantissas. -/
def normLeB (x y M : Int) : Bool := decide (x*x + y*y ≤ M*M)

end Work.TripodCert
