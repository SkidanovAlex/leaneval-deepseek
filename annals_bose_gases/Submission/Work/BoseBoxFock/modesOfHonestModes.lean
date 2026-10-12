import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.modeONBCplx_phys
import Submission.Work.BoseBoxFock.qCoeff_eq_ft
import Submission.Work.BoseBoxFock.slotCountsComplex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.modesOfHonestModes` — the mode bundle of the honest model

`Work.BoseBoxFock.modeONBCplx_phys` produces, from the honest mode data `HM`, a complex ONB `e`
of the box model with the orthonormality, the pairings with the physical mode family, the support
`Function.support (e l) ⊆ boxL ℓ` and the bound `MemLp (e l) ⊤`.  The BF3b dictionary rows
(`Submission/Work/BoseBoxFock/BF3B_PLAN_S6.md` §4, and the modules
`bomb_n0_eq_cS1C` / `bomb_nExc_eq_cnPlusC` / `bomb_pair_eq_cS2C`) carry a *fourth* hypothesis, the
**pinning** of the condensate coordinate,

    `∃ c, conj c * c = ℓ⁻³ ∧ e 0 =ᵐ c · thetaFun ℓ`,

which `modeONBCplx_phys` does not state: it is the Cauchy–Schwarz equality case
`Work.BoseBoxFock.e0_prop_theta`, obtained from `‖e 0‖ = 1` together with the pairing
`∫ conj(e 0) θ = ℓ^{3/2}` that `modeONBCplx_phys` *does* supply.

This module packages the four hypotheses into one statement, so that a consumer of the rows can
produce them by a single `obtain`.  (`e 0 =ᵐ c·θ` is an a.e. statement because `e0_prop_theta`
returns it that way.)
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The mode bundle of the honest model.**  For the honest mode data `HM` there is a complex
mode family `e : Fin HM.m → ℝ³ → ℂ` carrying at once

* orthonormality `∫ conj(e l) e l' = δ_{ll'}`,
* boundedness `MemLp (e l) ⊤`,
* box support `Function.support (e l) ⊆ boxL (ellH v μ)`,
* the pinning of the condensate coordinate: `∃ c, conj c * c = (ellH v μ)⁻³` and
  `e 0 =ᵐ c · thetaFun (ellH v μ)`,

which are exactly the hypotheses of the BF3b dictionary rows. -/
theorem exists_modes_honestModes (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (HM : Work.BoseBoxFock.HonestModes v μ) :
    ∃ e : Fin HM.m → EuclideanSpace ℝ (Fin 3) → ℂ,
      (∀ l l', (∫ x, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0) ∧
      (∀ l, MeasureTheory.MemLp (e l) ⊤) ∧
      (∀ l, Function.support (e l) ⊆
        Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) ∧
      (∃ c : ℂ, (starRingEnd ℂ) c * c = ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ ∧
        (∀ᵐ x ∂(volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
          e 0 x = c * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x)) := by
  obtain ⟨e, horth, -, -, hpair, hsupp, hbdd⟩ :=
    Work.BoseBoxFock.modeONBCplx_phys v μ HM
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  -- the box has finite volume, so `MemLp ⊤` gives `MemLp 2` for the box-supported `e 0`
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) ≠ ⊤ := by
    rw [Work.BoseBoxFock.corpusBox_boxL_eq_acube hℓ]
    exact (Submission.BoseGases.acube_lt_top _ hℓ.le).ne
  have hmem2 : MeasureTheory.MemLp (e 0) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    (hbdd 0).mono_exponent_of_measure_support_ne_top
      (s := Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ))
      (fun x hx => Function.notMem_support.mp (fun hmem => hx (hsupp 0 hmem))) hvol le_top
  exact ⟨e, horth, hbdd, hsupp,
    Work.BoseBoxFock.e0_prop_theta hℓ hmem2 (horth 0 0) hpair⟩

end Work.BoseBoxFock
