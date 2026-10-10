import Mathlib
import Submission.Work.MotK.TGen.ChartDefs
import Submission.Work.MotK.TGen.KleinTwRChart0
import Submission.Work.MotK.TGen.KleinTwFhomPi
import Submission.Work.MotK.TGen.FwVecRingId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.Phi0FwVec` — the pullback of the forward chart map `f̂` along the inverse chart
map of the T-twisted Crauder--Katz link

The chart isomorphism `Φ : R[1/Fdiv] ≃ₐ[K] R[1/Gdiv]` of the T-twisted link has to be the pullback
`χ^*` of the inverse link map `χ = π_p ∘ kleinTwR` (the map `Phi0 a b h = aeval (psiG a b h)` of
`ChartDefs`).  This file computes its value on the components `f̂ᵢ` of the *forward* link map
`f = kleinTwP ∘ kleinTwStereo` (`fwVec a b h`):

  `Φ(f̂ᵢ) = (1/ǧ₄)^4 · b(p, ǧ)^2 · s'(x) · xᵢ`,

i.e. (after clearing the denominator `ǧ₄ = bwVec a b h 4`) the two charts are inverse to each
other.  The geometric content is the composition `f ∘ χ`:

* `psiG` is the affine chart point `(1/ǧ₄)·ǧ` of `χ`, i.e. `Φ` substitutes `X_j ↦ (1/ǧ₄)·ǧ_{j+1}`;
* `f` is homogeneous of degree `4`, which produces the factor `(1/ǧ₄)^4` (`aeval_smul_fwPoly`);
* on the chart, `ǧ = π_p (R (chart))` and `R (chart)` lies on the quadric, so the inverse
  stereographic identity `KleinTwStereo_pi` turns `kleinTwStereo p (π_p (R x))` into
  `-b(p, R x)·R x`; `kleinTwP` is homogeneous of degree `2` and `kleinTwP (R x) = s'(x)·x`
  (I2'), which gives `b(p, ǧ)^2 · s'(x) · x` -- this is the ring identity `FwVecRingId`, proved in
  the sibling file `Submission.Work.MotK.TGen.FwVecRingId` (it does not involve the localisation).

The two ingredients are combined in the last line of `Phi0FwVec`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

/-! ## The value of `Phi0` on the components of the forward chart map -/

theorem Phi0FwVec {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (i : Fin 5) :
    Phi0 a b h (fwVec a b h i)
      = invG4 a b h ^ 4 *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
            (kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
                (bwVec a b h) ^ 2 *
              kleinTwSDualV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K) *
              chart3 K i) := by
  -- `Phi0 = aeval psiG` substitutes `X_j ↦ (1/ǧ₄)·ǧ_{j+1}`; as a map on the five homogeneous
  -- coordinates this is the point `(1/ǧ₄)·bwVec` (`chartPt3_psiG`)
  have key : (Phi0 a b h).comp (MvPolynomial.aeval (chart3 K))
      = MvPolynomial.aeval (fun j => invG4 a b h *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
            (bwVec a b h j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rw [congrFun (Phi0_chart3 a b h) j, congrFun (chartPt3_psiG a b h) j]
  have hA : Phi0 a b h (fwVec a b h i)
      = MvPolynomial.aeval (fun j => invG4 a b h *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
            (bwVec a b h j)) (fwPoly K a b h i) := by
    rw [fwVec_eq_aeval (K := K) a b h i, ← AlgHom.comp_apply, key]
  -- homogeneity of `f̂ = kleinTwP ∘ kleinTwStereo` (degree `4`): pull out `(1/ǧ₄)^4`
  have hB : MvPolynomial.aeval (fun j => invG4 a b h *
        algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
          (bwVec a b h j)) (fwPoly K a b h i)
      = invG4 a b h ^ 4 * algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (Gdiv a b h))
          (MvPolynomial.aeval (bwVec a b h) (fwPoly K a b h i)) := by
    rw [aeval_smul_fwPoly a b h (invG4 a b h)
      (fun j => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
        (bwVec a b h j)) i]
    rw [show (fun j => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
          (bwVec a b h j))
        = (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))) ∘
            (bwVec a b h) from rfl]
    rw [MvPolynomial.aeval_algebraMap_apply]
  -- `aeval` commutes with the polynomial expression `kleinTwP ∘ kleinTwStereo`
  have hC : MvPolynomial.aeval (bwVec a b h) (fwPoly K a b h i)
      = kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (pRa a b h) (bwVec a b h)) i := by
    rw [AevalFwPoly (A := MvPolynomial (Fin 3) K) a b h (bwVec a b h) i]
    rw [MvPolynomial.algebraMap_eq]
    rfl
  rw [hA, hB, hC, FwVecRingId a b h ha hh i]

end Work.MotK.TGen
