import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Polar.fsT_parallelogram
import Submission.Work.BoseKinLoc.Word.fsT_const_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Energy.gapBare_hpol`

The *bare mean-free box mass* `gapBare ℓ u ψ = ∫_{Λ(u)} (Q_uψ)²` (FS `eq:DefT`'s second piece
before the prefactor `bℓ⁻²`, see `Work.BoseKinLoc.gapBare`) is a **quadratic form** in the
state `ψ`: it is `2`-homogeneous (`Word.FsTAux.gapBare_const_mul`) and satisfies the
parallelogram identity (`Polar.FsTAux.gapBare_parallelogram`).  This module records the
`ℝ`-homogeneity of its polarisation,

    `gapBare ℓ u (t·f+g) − gapBare ℓ u (t·f−g) = t·(gapBare ℓ u (f+g) − gapBare ℓ u (f−g))`,

which is hypothesis `hpol` of `Work.BoseFixB2.Polar.par_polarisation_hpol`.

## The proof

`Q_u` is linear in the state (`Word.FsTAux.Qfree_const_mul`, `Polar.FsTAux.Qfree_add`,
`Polar.FsTAux.Qfree_sub`), so writing `F := Q_u f`, `G := Q_u g` the four `gapBare`s are the
box integrals of the squares of `tF±G` and `F±G`.  The claim is then the integral-level
identity

    `∫_Λ (tF+G)² − ∫_Λ (tF−G)² = t (∫_Λ (F+G)² − ∫_Λ (F−G)²)`

(both sides equal `4t∫_Λ FG`), which is the pointwise algebra
`(tF+G)² − (tF−G)² = 4t·FG` together with `MeasureTheory.integral_sub` /
`MeasureTheory.integral_const_mul`.  Every integrand is continuous on the compact box
`Λ = lamBox ℓ u` (`Gap.isCompact_lamBox`), hence `IntegrableOn` it, so the linearity of the
Bochner integral applies with no junk-value issue.  This last step is proved here
(`boxInt_sq_hpol_aux`); it is an unconditional statement about continuous functions on the box.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB2.Energy

/-! ## 1. The integral-level polarisation identity for the square -/

/-- **Polarisation identity with a scalar, for the box integral of a square.**  For continuous
`F G` and any real `t`, the difference of the box integrals of `(tF+G)²` and `(tF−G)²` is `t`
times the corresponding difference for `t = 1`.  Both sides equal `4t∫_Λ FG`. -/
private theorem boxInt_sq_hpol_aux {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    (t : ℝ) {F G : EuclideanSpace ℝ (Fin 3) → ℝ} (hF : Continuous F) (hG : Continuous G) :
    (∫ z in Work.BoseKinLoc.lamBox ℓ u, (t * F z + G z) ^ 2)
      - (∫ z in Work.BoseKinLoc.lamBox ℓ u, (t * F z - G z) ^ 2)
      = t * ((∫ z in Work.BoseKinLoc.lamBox ℓ u, (F z + G z) ^ 2)
        - (∫ z in Work.BoseKinLoc.lamBox ℓ u, (F z - G z) ^ 2)) := by
  have hK : IsCompact (Work.BoseKinLoc.lamBox ℓ u) :=
    Work.BoseKinLoc.Gap.isCompact_lamBox hℓ u
  have htF : Continuous (fun z : EuclideanSpace ℝ (Fin 3) => t * F z) :=
    continuous_const.mul hF
  have hd_t :
      (∫ z in Work.BoseKinLoc.lamBox ℓ u, (t * F z + G z) ^ 2)
        - (∫ z in Work.BoseKinLoc.lamBox ℓ u, (t * F z - G z) ^ 2)
      = 4 * t * (∫ z in Work.BoseKinLoc.lamBox ℓ u, F z * G z) := by
    have h1 : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (t * F z + G z) ^ 2)
        (Work.BoseKinLoc.lamBox ℓ u) :=
      ((htF.add hG).pow 2).continuousOn.integrableOn_compact hK
    have h2 : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (t * F z - G z) ^ 2)
        (Work.BoseKinLoc.lamBox ℓ u) :=
      ((htF.sub hG).pow 2).continuousOn.integrableOn_compact hK
    rw [← MeasureTheory.integral_sub h1 h2]
    rw [show (fun z : EuclideanSpace ℝ (Fin 3) =>
            (t * F z + G z) ^ 2 - (t * F z - G z) ^ 2)
          = fun z => (4 * t) * (F z * G z) from by funext z; ring]
    rw [MeasureTheory.integral_const_mul]
  have hd_1 :
      (∫ z in Work.BoseKinLoc.lamBox ℓ u, (F z + G z) ^ 2)
        - (∫ z in Work.BoseKinLoc.lamBox ℓ u, (F z - G z) ^ 2)
      = 4 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, F z * G z) := by
    have h1 : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (F z + G z) ^ 2)
        (Work.BoseKinLoc.lamBox ℓ u) :=
      ((hF.add hG).pow 2).continuousOn.integrableOn_compact hK
    have h2 : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (F z - G z) ^ 2)
        (Work.BoseKinLoc.lamBox ℓ u) :=
      ((hF.sub hG).pow 2).continuousOn.integrableOn_compact hK
    rw [← MeasureTheory.integral_sub h1 h2]
    rw [show (fun z : EuclideanSpace ℝ (Fin 3) => (F z + G z) ^ 2 - (F z - G z) ^ 2)
          = fun z => (4 : ℝ) * (F z * G z) from by funext z; ring]
    rw [MeasureTheory.integral_const_mul]
  rw [hd_t, hd_1]
  ring

/-! ## 2. The requested lemma -/

theorem gapBare_hpol {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) (t : ℝ) {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Work.BoseKinLoc.gapBare ℓ u (fun z => t * f z + g z) - Work.BoseKinLoc.gapBare ℓ u (fun z => t * f z - g z) = t * (Work.BoseKinLoc.gapBare ℓ u (fun z => f z + g z) - Work.BoseKinLoc.gapBare ℓ u (fun z => f z - g z)) := by
  have hft : Continuous (fun z : EuclideanSpace ℝ (Fin 3) => t * f z) :=
    continuous_const.mul hf.continuous
  have hQtf : Work.BoseKinLoc.Qfree ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => t * f z)
      = fun z => t * Work.BoseKinLoc.Qfree ℓ u f z :=
    Work.BoseKinLoc.Word.FsTAux.Qfree_const_mul ℓ u t f
  have hA : Work.BoseKinLoc.Qfree ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => t * f z + g z)
      = fun z => t * Work.BoseKinLoc.Qfree ℓ u f z + Work.BoseKinLoc.Qfree ℓ u g z := by
    rw [Work.BoseFixB2.Polar.FsTAux.Qfree_add hℓ u hft hg.continuous, hQtf]
  have hB : Work.BoseKinLoc.Qfree ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => t * f z - g z)
      = fun z => t * Work.BoseKinLoc.Qfree ℓ u f z - Work.BoseKinLoc.Qfree ℓ u g z := by
    rw [Work.BoseFixB2.Polar.FsTAux.Qfree_sub hℓ u hft hg.continuous, hQtf]
  have hC : Work.BoseKinLoc.Qfree ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => f z + g z)
      = fun z => Work.BoseKinLoc.Qfree ℓ u f z + Work.BoseKinLoc.Qfree ℓ u g z :=
    Work.BoseFixB2.Polar.FsTAux.Qfree_add hℓ u hf.continuous hg.continuous
  have hD : Work.BoseKinLoc.Qfree ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => f z - g z)
      = fun z => Work.BoseKinLoc.Qfree ℓ u f z - Work.BoseKinLoc.Qfree ℓ u g z :=
    Work.BoseFixB2.Polar.FsTAux.Qfree_sub hℓ u hf.continuous hg.continuous
  have e1 : Work.BoseKinLoc.gapBare ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => t * f z + g z)
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u,
          (t * Work.BoseKinLoc.Qfree ℓ u f z + Work.BoseKinLoc.Qfree ℓ u g z) ^ 2 := by
    unfold Work.BoseKinLoc.gapBare
    rw [hA]
  have e2 : Work.BoseKinLoc.gapBare ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => t * f z - g z)
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u,
          (t * Work.BoseKinLoc.Qfree ℓ u f z - Work.BoseKinLoc.Qfree ℓ u g z) ^ 2 := by
    unfold Work.BoseKinLoc.gapBare
    rw [hB]
  have e3 : Work.BoseKinLoc.gapBare ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => f z + g z)
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u,
          (Work.BoseKinLoc.Qfree ℓ u f z + Work.BoseKinLoc.Qfree ℓ u g z) ^ 2 := by
    unfold Work.BoseKinLoc.gapBare
    rw [hC]
  have e4 : Work.BoseKinLoc.gapBare ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => f z - g z)
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u,
          (Work.BoseKinLoc.Qfree ℓ u f z - Work.BoseKinLoc.Qfree ℓ u g z) ^ 2 := by
    unfold Work.BoseKinLoc.gapBare
    rw [hD]
  rw [e1, e2, e3, e4]
  exact boxInt_sq_hpol_aux hℓ u t
    (Work.BoseKinLoc.Kinetic.Qfree_continuous hf.continuous ℓ u)
    (Work.BoseKinLoc.Kinetic.Qfree_continuous hg.continuous ℓ u)

end Work.BoseFixB2.Energy
