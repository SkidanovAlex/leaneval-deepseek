import Mathlib
import Submission.Work.MotK.TGen.ChartDefs
import Submission.Work.MotK.TGen.AevalBwPoly
import Submission.Work.MotK.KleinTwLinkComp2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.Psi0BwVec` — the pullback of the inverse chart map `ǧ` along the forward chart
map of the T-twisted Crauder--Katz link

The chart isomorphism `Φ : R[1/Fdiv] ≃ₐ[K] R[1/Gdiv]` of the T-twisted link has to be the pullback
`f^*` of the forward link map `f = kleinTwP ∘ kleinTwStereo` (the map `Psi0 a b h = aeval (phiF a b h)`
of `ChartDefs`).  This file computes its value on the components `ǧᵢ` of the *inverse* link map
`χ = π_p ∘ kleinTwR` (`bwVec a b h`):

  `Ψ(ǧᵢ) = (1/f̂₄)^3 · (-(GambT) · xᵢ)`,

the mirror image of `Phi0FwVec`.  The geometric content is the composition `χ ∘ f`:

* `phiF` is the affine chart point `(1/f̂₄)·f̂` of `f`, i.e. `Ψ` substitutes `X_j ↦ (1/f̂₄)·f̂_{j+1}`;
* `ǧ` is homogeneous of degree `3`, which produces the factor `(1/f̂₄)^3` (`aeval_smul_bwPoly`);
* on the chart, `ǧ = π_p (R (v))`, and the composed identity `KleinTwLinkComp2`
  (`π_p (R (P (stereo p v))) = -(F_hom p v) • v`) turns `π_p (R (f̂))` into `-(GambT) • chart`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

theorem Psi0BwVec {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (i : Fin 5) :
    Psi0 a b h (bwVec a b h i)
      = invF4 a b h ^ 3 *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
            (-(GambT a b h) * chart3 K i) := by
  -- `Psi0 = aeval phiF` substitutes `X_j ↦ (1/f̂₄)·f̂_{j+1}`; as a map on the five homogeneous
  -- coordinates this is the point `(1/f̂₄)·fwVec` (`chartPt3_phiF`)
  have key : (Psi0 a b h).comp (MvPolynomial.aeval (chart3 K))
      = MvPolynomial.aeval (fun j => invF4 a b h *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
            (fwVec a b h j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rw [congrFun (Psi0_chart3 a b h) j, congrFun (chartPt3_phiF a b h ha hh) j]
  have hA : Psi0 a b h (bwVec a b h i)
      = MvPolynomial.aeval (fun j => invF4 a b h *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
            (fwVec a b h j)) (bwPoly K a b h i) := by
    rw [bwVec_eq_aeval (K := K) a b h i, ← AlgHom.comp_apply, key]
  -- homogeneity of `ǧ = π_p ∘ kleinTwR` (degree `3`): pull out `(1/f̂₄)^3`
  have hB : MvPolynomial.aeval (fun j => invF4 a b h *
        algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
          (fwVec a b h j)) (bwPoly K a b h i)
      = invF4 a b h ^ 3 * algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (Fdiv a b h))
          (MvPolynomial.aeval (fwVec a b h) (bwPoly K a b h i)) := by
    rw [aeval_smul_bwPoly a b h (invF4 a b h)
      (fun j => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
        (fwVec a b h j)) i]
    rw [show (fun j => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
          (fwVec a b h j))
        = (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))) ∘
            (fwVec a b h) from rfl]
    rw [MvPolynomial.aeval_algebraMap_apply]
  -- `aeval` commutes with the polynomial expression `π_p ∘ kleinTwR`
  have hC : MvPolynomial.aeval (fwVec a b h) (bwPoly K a b h i)
      = kleinTwPi (pRa a b h)
          (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (fwVec a b h)) i := by
    rw [AevalBwPoly (K := K) (A := MvPolynomial (Fin 3) K) a b h (fwVec a b h) i]
    rw [MvPolynomial.algebraMap_eq]
    rfl
  -- the composed identity `χ ∘ f` at the chart point
  have hD : kleinTwPi (pRa a b h)
        (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fwVec a b h)) i = -(GambT a b h) * chart3 K i := by
    have hp0 : pRa a b h 0 = 1 := by simp [pRa, kleinPointT]
    have hv : chart3 K 0 = 0 := by simp [chart3]
    rw [show fwVec a b h = kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
            (chart3 K)) from rfl,
      show GambT a b h = kleinTwFhom (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (pRa a b h) (chart3 K) from rfl]
    exact congrFun (KleinTwLinkComp2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (pRa a b h) (chart3 K) (kleinTwQ_pRa a b h ha hh) hp0 hv) i
  rw [hA, hB, hC, hD]

end Work.MotK.TGen
