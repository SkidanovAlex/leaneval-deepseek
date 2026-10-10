import Mathlib
import Submission.Work.MotAS.CensusLinAS
import Submission.Work.MotV5.ASChart.Stereo
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `CensusAS` is **false**: the fourth component of the forward chart map vanishes identically

Part of the census `Work.MotAS.CensusAS` (`Submission/Work/MotAS/linkCertAS.lean`) is the
non-degeneracy clause `FdivAS (aK D) (bK D) (fAS 𝕜) ≠ 0`.  It is **not provable**, because
`FdivAS` is the zero polynomial:

* `FdivAS a b g = linAS a b * sAS a b g * fwVecAS a b g 4`, and
* `fwVecAS a b g 4 = kleinPAS a b g (kleinStereoAS (C a) (C b) (pAS K) (chart3 K)) 4`

while, by inspection of `ASData.lean`,

  `kleinPAS a b g y 4 = -kleinQAS a b y`   (polynomial identity in `y`, no `g`),

and `kleinStereoAS` maps into the quadric:

  `kleinQAS a b (kleinStereoAS a b p v) = kleinQAS a b v ^ 2 * kleinQAS a b p`
  (`Work.MotV5.ASChart.kleinQAS_stereoAS`, proved),

with `kleinQAS a b (pAS K) = 0` because every monomial of `kleinQAS` contains a factor `yᵢ yⱼ` with
`i, j ≥ 1` and `pAS = 288 • e₀` is supported in coordinate `0`.

Hence `fwVecAS a b g 4 = 0` identically, `FdivAS a b g = 0`, and every `CensusAS`-shaped statement
(the `Prop` `Work.MotAS.CensusAS` of `linkCertAS.lean`, and its reduced form
`Work.MotAS.CensusAS'`) is **false**, so `linkCertAS_of_censusAS` and
`linkCertAS_of_censusAS'` are vacuous.  This is the degeneracy the `WARNING` in
`Submission/Work/MotAS/ChartDefs.lean` anticipated: it is *not* cured by re-pointing the
stereographic point, because the identity `kleinPAS · 4 = -kleinQAS` holds in the AS model and
*any* point of the quadric makes the stereographic image lie on the quadric.

Consequence for the chapter: the chart data of `ChartDefs.lean` (in particular the "denominators"
`fwVecAS 4`, `bwVecAS 4`) cannot serve as the affine chart of the certificate as they stand; the
forward chart map has to be built on a Pfaffian component that is *not* a multiple of the quadric
(equivalently, the chart must be cut out by a different choice of chart coordinates), and the whole
`CensusAS` interface has to be re-derived before it can be proved.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace Work.MotAS

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- **The fourth AS Pfaffian is minus the AS quadric** (a polynomial identity in the coordinates;
the parameter `g` does not occur). -/
theorem kleinPAS_four_eq_neg {K : Type*} [CommRing K] (a b g : K) (y : Fin 5 → K) :
    kleinPAS a b g y 4 = -kleinQAS a b y := by
  simp only [kleinPAS, kleinPAS4, kleinQAS, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]
  first | refl_ring1 | ring

/-- `pAS` lies on the AS quadric. -/
theorem kleinQAS_pAS {K : Type*} [CommRing K] (a b : K) :
    kleinQAS (C a : MvPolynomial (Fin 3) K) (C b) (pAS K) = 0 := by
  rw [pAS_eq_vec]
  simp only [kleinQAS, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  first | refl_ring1 | ring

/-- **The fourth component of the forward chart map vanishes identically.** -/
theorem fwVecAS_four_eq_zero {K : Type*} [Field K] (a b g : K) : fwVecAS a b g 4 = 0 := by
  have hst := Work.MotV5.ASChart.kleinQAS_stereoAS (C a : MvPolynomial (Fin 3) K) (C b)
    (pAS K) (Work.MotK.chart3 K)
  have hp : kleinQAS (C a : MvPolynomial (Fin 3) K) (C b) (pAS K) = 0 := kleinQAS_pAS a b
  have h4 : fwVecAS a b g 4
      = -kleinQAS (C a : MvPolynomial (Fin 3) K) (C b)
          (kleinStereoAS (C a) (C b) (pAS K) (Work.MotK.chart3 K)) :=
    kleinPAS_four_eq_neg (C a) (C b) (C g) _
  rw [h4, hst, hp, mul_zero, neg_zero]

/-- **`FdivAS` is identically zero**, so the non-degeneracy clause of the census is false. -/
theorem FdivAS_eq_zero {K : Type*} [Field K] (a b g : K) : FdivAS a b g = 0 := by
  simp only [FdivAS, fwVecAS_four_eq_zero, mul_zero]

/-- **`CensusAS` is false** (for `ASGood` data, which exist). -/
theorem not_censusAS (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    ¬ CensusAS D hD := by
  rintro ⟨hpr, hht, hres, hS, hlin, hCub, hFw, hBw, hFne, -, -⟩
  exact hFne (FdivAS_eq_zero (aK D) (bK D) (Work.MotV.fAS 𝕜))

/-- **`CensusAS'` (the reduced census) is false as well.** -/
theorem not_censusAS' (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    ¬ CensusAS' D hD := by
  rintro ⟨hpr, hht, hres, hS, hCub, hFw, hBw, hFne, -, -⟩
  exact hFne (FdivAS_eq_zero (aK D) (bK D) (Work.MotV.fAS 𝕜))

end Work.MotAS
