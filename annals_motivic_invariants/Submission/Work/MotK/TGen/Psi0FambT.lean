import Mathlib
import Submission.Work.MotK.TGen.ChartDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.Psi0FambT` — the first unit condition, in the forward chart ring

`Psi0 a b h = MvPolynomial.aeval (phiF a b h)` is the pullback `f^*` of the *forward* link map
`f = kleinTwP ∘ kleinTwStereo` on the affine chart `V₀ = 0, V₄ = 1`, taking values in the
localisation `R[1/Fdiv]`, `R = K[x₀,x₁,x₂]` (`ChartDefs`).  This file computes its value on the
*target* equation `FambT a b h = kleinTwGhomV p chart3` (degree `8`):

  `Psi0 (FambT) = (1/f̂₄)^8 · ( -s(y)² · b(p, chart) · GambT )`,

which is the chart-level form of the *first unit condition*
`kleinTwGhomV p (f v) = -s(y)²·b(p,v)·kleinTwFhom p v` (`Work.MotK.kleinTwLinkUnitV`,
dehomogenised as `Work.MotK.GambT_unit`).  Indeed the chart substitution `X_j ↦ phiF j` is the
vector `(1/f̂₄) • f̂` of `ChartDefs`, and `kleinTwGhomV` is homogeneous of degree `8` in that
vector argument (`aeval_smul_GhomPoly`), so

* the coefficient `(1/f̂₄)^8 = invF4 a b h ^ 8` comes out (`hB`),
* the remaining evaluation `aeval (fwVec) (GhomPoly) = kleinTwGhomV p (fwVec)` (`hC`) is the
  `aeval`-computation of the target polynomial (`AevalGhomPoly`), and
* `fwVec` is *definitionally* `kleinTwP ∘ kleinTwStereo` at `chart3`, so the first unit condition
  `GambT_unit` identifies the result.

The mirror statement in the inverse chart ring (`Phi0 a b h (GambT a b h)`) is
`Submission.Work.MotK.TGen.Phi0GambT`; the analogous computation for `Phi0` on the forward chart
coordinates is `Submission.Work.MotK.TGen.Phi0FwVec`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

/-- **The first unit condition of the affine T-twisted link, in the forward chart ring.**  The
pullback of the target equation `FambT` along the forward chart map `f̂ = kleinTwP ∘ kleinTwStereo`
is `(1/f̂₄)^8` times the chart-level unit multiple `-s(y)²·b(p,chart)·GambT` of the source
equation. -/
theorem Psi0FambT {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    Psi0 a b h (FambT a b h)
      = invF4 a b h ^ 8 *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
            (-(kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                  (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
                    (chart3 K))) ^ 2 *
              kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
                (chart3 K) * GambT a b h) := by
  -- `Psi0 = aeval phiF` substitutes `X_j ↦ (1/f̂₄)·f̂_{j+1}`; as a map on the five homogeneous
  -- coordinates this is the point `(1/f̂₄) • fwVec` (`chartPt3_phiF`)
  have key : (Psi0 a b h).comp (MvPolynomial.aeval (chart3 K))
      = MvPolynomial.aeval (fun j => invF4 a b h *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h)) (fwVec a b h j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rw [congrFun (Psi0_chart3 a b h) j, congrFun (chartPt3_phiF a b h ha hh) j]
  -- `FambT` is `GhomPoly` evaluated at the chart point, so `Psi0 (FambT)` is the composite
  have hA : Psi0 a b h (FambT a b h)
      = MvPolynomial.aeval (fun j => invF4 a b h *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h)) (fwVec a b h j))
          (GhomPoly K a b h) := by
    rw [FambT_eq_aeval (K := K) a b h, ← AlgHom.comp_apply, key]
  -- homogeneity of `G_hom` (degree `8`): pull out `(1/f̂₄)^8`, then push `algebraMap` out
  have hB : MvPolynomial.aeval (fun j => invF4 a b h *
        algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h)) (fwVec a b h j))
        (GhomPoly K a b h)
      = invF4 a b h ^ 8 * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
          (MvPolynomial.aeval (fwVec a b h) (GhomPoly K a b h)) := by
    rw [aeval_smul_GhomPoly a b h (invF4 a b h)
      (fun j => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
        (fwVec a b h j))]
    rw [show (fun j => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
          (fwVec a b h j))
        = (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))) ∘ (fwVec a b h)
        from rfl]
    rw [MvPolynomial.aeval_algebraMap_apply]
  -- `aeval` computes the polynomial expression `kleinTwGhomV` at the chart point
  have hC : MvPolynomial.aeval (fwVec a b h) (GhomPoly K a b h)
      = kleinTwGhomV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
          (fwVec a b h) := by
    rw [AevalGhomPoly (K := K) (A := MvPolynomial (Fin 3) K) a b h (fwVec a b h)]
    simp only [MvPolynomial.algebraMap_eq]
    rfl
  rw [hA, hB, hC]
  -- `fwVec` is definitionally `kleinTwP ∘ kleinTwStereo` at the chart: the first unit condition
  rw [show fwVec a b h = kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
          (chart3 K)) from rfl,
      GambT_unit a b h ha hh]

end Work.MotK.TGen
