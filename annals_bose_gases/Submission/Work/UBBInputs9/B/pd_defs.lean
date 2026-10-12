import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.pd_defs` — objects for the projection-defect proof

Auxiliary definitions used by the proof of `Work.UBBInputs9.B.proj_defect` (and by the
lemmas it delegates).  Notation: `X1 = X 1 = Fin 1 → ℝ³` is the one-particle configuration
space, `abox 1 ℓ` the one-particle centred box, `dlBox ℓ d u` the sliding small box and
`chiB ℓ d u` its smooth cutoff.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

/-- The mean of a one-particle state over the sliding box `B(u)`, i.e. the coefficient of the
box projection `P_{B(u)}`. -/
noncomputable def boxMean (ℓ d : ℝ) (u : ℝ³) (Φ : X1 → ℝ) : ℝ :=
  (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
    ∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (fun _ => z)

/-- The `χ_{B(u)}`-unprojected Dirichlet integrand `Σ_k (∂_k(χ_{B(u)}·Φ))²`. -/
noncomputable def kinInt (ℓ d : ℝ) (Φ : X1 → ℝ) (u : ℝ³) (x : X1) : ℝ :=
  ∑ k : Fin 3,
    (fderiv ℝ (fun y : X1 => Submission.BoseGases.chiB ℓ d u (y 0) * Φ y) x
      (Submission.BoseGases.kcDir 1 0 k)) ^ 2

/-- The `χ_{B(u)}`-projected Dirichlet integrand
`Σ_k (∂_k(χ_{B(u)}·Q_{B(u)}Φ))²`. -/
noncomputable def kinIntPrj (ℓ d : ℝ) (Φ : X1 → ℝ) (u : ℝ³) (x : X1) : ℝ :=
  ∑ k : Fin 3,
    (fderiv ℝ (fun y : X1 =>
        Submission.BoseGases.chiB ℓ d u (y 0) *
          Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) 0 Φ y) x
      (Submission.BoseGases.kcDir 1 0 k)) ^ 2

/-- The window-derivative integrand `Σ_k (∂_k χ_{B(u)})²`. -/
noncomputable def kinIntD (ℓ d : ℝ) (u : ℝ³) (x : X1) : ℝ :=
  ∑ k : Fin 3,
    (fderiv ℝ (fun y : X1 => Submission.BoseGases.chiB ℓ d u (y 0)) x
      (Submission.BoseGases.kcDir 1 0 k)) ^ 2

/-- The product measure on the `(u,x)`-space `ℝ³ × X1` with the `x`-measure restricted to the
centred box `abox 1 ℓ`. -/
noncomputable def pdMu (ℓ : ℝ) : Measure (ℝ³ × X1) :=
  (volume : Measure ℝ³).prod ((volume : Measure X1).restrict (Submission.BoseGases.abox 1 ℓ))

lemma boxP_eq_boxMean (ℓ d : ℝ) (u : ℝ³) (Φ : X1 → ℝ) (x : X1) :
    Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) 0 Φ x = boxMean ℓ d u Φ := by
  unfold Work.SmallBoxTBWord.boxP boxMean
  rw [one_div]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  funext j
  rw [Function.update_apply, if_pos (Fin.eq_zero j)]

lemma boxQ_eq_boxMean (ℓ d : ℝ) (u : ℝ³) (Φ : X1 → ℝ) (x : X1) :
    Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) 0 Φ x = Φ x - boxMean ℓ d u Φ := by
  unfold Work.SmallBoxTBWord.boxQ
  rw [boxP_eq_boxMean]

/-- At `ε = 0` the gap coefficient of `tBwordBInd` vanishes, so the sliding word is its
spectral (Dirichlet) half. -/
lemma tBwordBInd_zero_eq_kinInd {ℓ d : ℝ} (u : ℝ³) (Φ : X1 → ℝ) :
    Work.UBBInputs8.tBwordBInd 1 ℓ d 0 0 u Φ
      = Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u) 0 Φ := by
  unfold Work.UBBInputs8.tBwordBInd Work.UBBInputs8.tBwordInd
  have h : Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) 0 = 0 := by
    unfold Work.SmallBoxTBWord.tbGapCoeff
    ring
  rw [h, zero_mul, zero_add]

end Work.UBBInputs9.B
