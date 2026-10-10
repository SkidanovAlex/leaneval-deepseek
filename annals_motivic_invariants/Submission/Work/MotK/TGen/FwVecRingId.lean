import Mathlib
import Submission.Work.MotK.TGen.ChartDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FwVecRingId` — the composed identity `P ∘ y ∘ (π_p ∘ R)` on the affine chart, in ring form

This is the general algebraic identity behind the composed forward map of the T-twisted
Crauder--Katz link, read in the *polynomial* ring `K[x₀,x₁,x₂]` rather than in the localisation
`K[x₀,x₁,x₂][1/Gdiv]`: for `p` on the quadric `{q = 0}` and `w` with `w 0 = 0`,

  `kleinTwP (kleinTwStereo p (π_p (kleinTwR w)))
     = b(p, π_p (kleinTwR w))² · kleinTwSDualV w • w`.

It is `KleinTwLinkComp1` (which gives `b(p, kleinTwR w)`) with the two standard corrections:
`b(p, π_p x) = b(p, x)` for `p` on the quadric (`kleinTwBilin_pi_eq`), and the corrected dual
secant `kleinTwSDualV` in place of `kleinTwSDualInv`
(`kleinTwSDualInv_eq_kleinTwSDualV`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

/-- The composed source-side identity of the T-twisted link in the `kleinTwSDualV` normal form: for
`p` on the twisted quadric and `w 0 = 0`,

  `kleinTwP (kleinTwStereo p (π_p (kleinTwR w)))
     = (b(p, π_p (kleinTwR w)))² · kleinTwSDualV w • w`. -/
private lemma kleinTwP_stereo_pi_R {R : Type*} [CommRing R] (a b h : R) (p w : Fin 5 → R)
    (hp : Work.MotK.kleinTwQ a b h p = 0) (hw : w 0 = 0) :
    Work.MotK.kleinTwP a b h (Work.MotK.kleinTwStereo a b h p
        (Work.MotK.kleinTwPi p (Work.MotK.kleinTwR a b h w)))
      = fun k => (Work.MotK.kleinTwBilin a b h p
            (Work.MotK.kleinTwPi p (Work.MotK.kleinTwR a b h w))) ^ 2
          * Work.MotK.kleinTwSDualV a b h w * w k := by
  rw [Work.MotK.KleinTwLinkComp1 a b h p w hp hw]
  funext k
  rw [Work.MotK.kleinTwSDualInv_eq_kleinTwSDualV,
    ← Work.MotK.kleinTwBilin_pi_eq a b h p (Work.MotK.kleinTwR a b h w) hp]

theorem FwVecRingId {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) (i : Fin 5) :
    Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (Work.MotK.kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (Work.MotK.pRa a b h) (Work.MotK.TGen.bwVec a b h)) i
      = Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (Work.MotK.pRa a b h) (Work.MotK.TGen.bwVec a b h) ^ 2
          * Work.MotK.kleinTwSDualV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (Work.MotK.chart3 K) * Work.MotK.chart3 K i := by
  have hw : Work.MotK.chart3 K 0 = 0 := by simp [Work.MotK.chart3]
  have hmain := kleinTwP_stereo_pi_R (R := MvPolynomial (Fin 3) K)
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (Work.MotK.pRa a b h) (Work.MotK.chart3 K) (Work.MotK.kleinTwQ_pRa a b h ha hh) hw
  rw [show Work.MotK.TGen.bwVec a b h = Work.MotK.kleinTwPi (Work.MotK.pRa a b h)
      (Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (Work.MotK.chart3 K)) from rfl]
  exact congrFun hmain i

end Work.MotK.TGen
