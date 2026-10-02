/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Third-order jets of `(Tsq c)^[n]` (for item E-E, the Taylor model of the petal)

Item **E-E** of the `SeedCertNum` contract needs the Taylor model
`F (z₁+u) = z₁ + u + A u² + E u` with `‖E u‖ ≤ M‖u‖³` for `‖u‖ ≤ ρ₂`.  The sharp constant comes
from the *third-order* Taylor remainder,
`‖E u‖ ≤ sup_{‖w‖≤ρ₂}‖F'''(z₁+w)‖ · ‖u‖³ / 6`,
so we need an interval enclosure of the *third* derivative of `F = (Tsq c)^[5]`.

This file mirrors `Jet2.lean`: `DJet3 (v, d1, d2, d3)` with the holomorphic third-order chain rule

  `(G∘H)''' = G'''(H)·H'³ + 3·G''(H)·H'·H'' + G'(H)·H'''`,

`G = Tsq c` having `G'(w) = 4w(w²+c̄)`, `G''(w) = 12w²+4c̄`, `G'''(w) = 24w`, and the rounded iterate
`jet3IterR` (rounding is essential: the exponents grow by `4^n` without it, see `Round.lean`).

## Main results

* `DJet3`, `jet3Step`, `jet3IterR`, `DJet3.roundOut`;
* `CBox.maxNorm`, `CBox.normSq` (already in `NormSq.lean`) — soundness `mem_jet3R` is delegated.
-/
import Mathlib
import Submission.Work.SeedCertNum.Round
import Submission.Work.SeedCertNum.NormSq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-- The zero box. -/
def zeroB : CBox := ⟨Dya.zero, Dya.zero, Dya.zero, Dya.zero⟩

/-- A third-order jet of a holomorphic map over a box. -/
structure DJet3 where
  v : CBox
  d1 : CBox
  d2 : CBox
  d3 : CBox
deriving DecidableEq, Repr

/-- One composition step with `G = Tsq c`, over the parameter box `Ctyp`. -/
def jet3Step (Ctyp : CBox) (J : DJet3) : DJet3 :=
  let a := Ctyp.conj
  let wsa := (J.v.sq).add a
  let G1 := (J.v.mulScalar (Dya.ofInt 4)).mul wsa
  let G2 := ((J.v.sq).mulScalar (Dya.ofInt 12)).add (a.mulScalar (Dya.ofInt 4))
  let G3 := J.v.mulScalar (Dya.ofInt 24)
  { v := (wsa.sq).add Ctyp
    d1 := G1.mul J.d1
    d2 := (G2.mul J.d1.sq).add (G1.mul J.d2)
    d3 := ((G3.mul (J.d1.sq.mul J.d1)).add
        ((G2.mul (J.d1.mul J.d2)).mulScalar (Dya.ofInt 3))).add (G1.mul J.d3) }

/-- Round the four boxes of a 3-jet outward. -/
def DJet3.roundOut (K : ℕ) (J : DJet3) : DJet3 :=
  ⟨J.v.roundOut K, J.d1.roundOut K, J.d2.roundOut K, J.d3.roundOut K⟩

/-- The rounded 3-jet recursion of `(Tsq c)^[n]` over `Xz × Xt`. -/
def jet3IterR (K : ℕ) (Ctyp Xz : CBox) : ℕ → DJet3
  | 0 => ⟨Xz.roundOut K, oneBox.roundOut K, zeroB.roundOut K, zeroB.roundOut K⟩
  | n + 1 => (jet3Step Ctyp (jet3IterR K Ctyp Xz n)).roundOut K

end

end Work.SeedCert
