import Submission.Work.SeedCertRay.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.SeedCertRay.Num` — the `NC`-dependent part of the certificate checker (generated)

* `NC` — the number of sub-disks per angle;
* `stepQs`, `dirQs` — the index lists over which the level checks run;
* `dirOKB` — (D2) for one angle: all `NC` disks of the two levels in one open half-plane;
* `petalOKB` — (D3) for one level: all `NC` disks of the `alpha_1`-column in the petal.
-/
namespace Work.SeedCertRay

/-- The number of sub-disks per angle. -/
def NC : Nat := 6

/-- The step indices `(j, i)`. -/
def stepQs : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5)]

/-- The angle indices. -/
def dirQs : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- (D2) for one angle: all `NC` disks of the two levels in one open half-plane. -/
def dirOKB (dl t s : List Int) (j : Nat) : Bool :=
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI t (3*(j*NC+0))) (gI t (3*(j*NC+0)+1)) (gI t (3*(j*NC+0)+2)) &&
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI t (3*(j*NC+1))) (gI t (3*(j*NC+1)+1)) (gI t (3*(j*NC+1)+2)) &&
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI t (3*(j*NC+2))) (gI t (3*(j*NC+2)+1)) (gI t (3*(j*NC+2)+2)) &&
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI t (3*(j*NC+3))) (gI t (3*(j*NC+3)+1)) (gI t (3*(j*NC+3)+2)) &&
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI t (3*(j*NC+4))) (gI t (3*(j*NC+4)+1)) (gI t (3*(j*NC+4)+2)) &&
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI t (3*(j*NC+5))) (gI t (3*(j*NC+5)+1)) (gI t (3*(j*NC+5)+2)) &&
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI s (3*(j*NC+0))) (gI s (3*(j*NC+0)+1)) (gI s (3*(j*NC+0)+2)) &&
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI s (3*(j*NC+1))) (gI s (3*(j*NC+1)+1)) (gI s (3*(j*NC+1)+2)) &&
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI s (3*(j*NC+2))) (gI s (3*(j*NC+2)+1)) (gI s (3*(j*NC+2)+2)) &&
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI s (3*(j*NC+3))) (gI s (3*(j*NC+3)+1)) (gI s (3*(j*NC+3)+2)) &&
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI s (3*(j*NC+4))) (gI s (3*(j*NC+4)+1)) (gI s (3*(j*NC+4)+2)) &&
  hpB (gI dl (2*j)) (gI dl (2*j+1)) (gI s (3*(j*NC+5))) (gI s (3*(j*NC+5)+1)) (gI s (3*(j*NC+5)+2))

/-- (D3) for one level: all `NC` disks of the `alpha_1`-column in the petal. -/
def petalOKB (dl : List Int) (Zx Zy Eta Acx Acy EtaA RR : Int) : Bool :=
  petalDskB (gI dl 0) (gI dl 1) (gI dl 2) Zx Zy Eta Acx Acy EtaA RR &&
  petalDskB (gI dl 3) (gI dl 4) (gI dl 5) Zx Zy Eta Acx Acy EtaA RR &&
  petalDskB (gI dl 6) (gI dl 7) (gI dl 8) Zx Zy Eta Acx Acy EtaA RR &&
  petalDskB (gI dl 9) (gI dl 10) (gI dl 11) Zx Zy Eta Acx Acy EtaA RR &&
  petalDskB (gI dl 12) (gI dl 13) (gI dl 14) Zx Zy Eta Acx Acy EtaA RR &&
  petalDskB (gI dl 15) (gI dl 16) (gI dl 17) Zx Zy Eta Acx Acy EtaA RR


end Work.SeedCertRay
