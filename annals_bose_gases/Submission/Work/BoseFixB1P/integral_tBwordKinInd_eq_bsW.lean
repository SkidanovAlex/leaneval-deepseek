import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.sbWord_marginal_integrable
import Submission.Work.Measure.ae_measure_section_right_null
import Submission.Work.SecondOrder.Main
import Submission.Work.SmallBoxBridge.kinFT_analyticAt
import Submission.Work.hlocWire.boxPInd_smul
import Submission.Work.hlocWire.boxQInd_smul
import Submission.Work.hlocWire.tBdiagFormInd_smul
import Submission.Work.hlocWire2.bsW_le_of_le_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1P.integral_tBwordKinInd_eq_bsW`

**The FS-faithful spectral half of the sliding small-box word, in `bsW` form.**

The round-8 word `Work.UBBInputs8.tBwordKinInd a A volA χ c Ψ` is the `p`-diagonal form
`Work.UBBInputs8.tBdiagFormInd a A volA χ (fsKinCoeff c) Ψ`, i.e. the slot sum

    `Σ_i (2π)⁻³ ∫_p fsKinCoeff c ‖p‖ · ((a³)⁻¹ ∫_{abox N a} ‖tBamp χ p (Q_{A,i}Ψ) i x‖²)`,

built on FS's box projection `Q_{A,i} = 1_A − P_{A,i}` (`Work.UBBInputs8.boxQInd`, which carries
the box indicator).  At a *single* slot the ambient configuration integral cancels the slot
normalisation `(a³)⁻¹` and leaves the `F`-weighted `p`-space norm²
`Work.BSKinetic.Decomp.bsW F` of the windowed mean-free fibre.  The `N = 1` collapse for the
corpus's indicator-free projection is `Work.BSKinetic.tBdiagForm_one_eq_bsW`; the present file
transfers it to the FS-faithful `boxQInd` in the sliding instantiation, where the box indicator
is **invisible**: `χ_{B(u)}` is supported in `B(u) = dlBox ℓ d u`
(`Submission.BoseGases.chiB_support_mem`), so `1_{B(u)}·χ_{B(u)} = χ_{B(u)}`.

## Contents

* `tBamp_boxQInd_eq_boxQ_N1` — at one slot, the windowed amplitude of the FS-faithful projected
  state `Q_{A,0}φ` equals that of the indicator-free projected state, because the two states agree
  on the support of the window;
* `tBdiagFormInd_one_eq_tBdiagForm` — hence `tBdiagFormInd` and `tBdiagForm` agree at `N = 1`;
* `tBwordKinInd_one_eq_bsW` — the `N = 1` collapse of the sliding word to `(2π)⁻³·bsW`, combining
  the previous two with `Work.BSKinetic.tBdiagForm_one_eq_bsW`;
* `integral_tBwordKinInd_eq_bsW` — the requested statement: the `u`-marginal of the sliding word
  is `Integrable` and its `u`-integral is that of the `bsW` form.  The integrability is *not*
  reproved here: it is transported from the delivered **full** word marginal
  `Work.BoseFixB1.integrable_tBwordBInd` at `ε = 0`, where the gap half
  `tbGapCoeff (ℓd) 0 · n₊ = 0` switches off and only the spectral half survives.
-/

namespace Work.BoseFixB1P

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The box indicator is invisible in the windowed amplitude

FS's mean-free projection `Q_{A,i} = 1_A − P_{A,i}` differs from the corpus's indicator-free
`Work.SmallBoxTBWord.boxQ` by the factor `1_A` in slot `i`.  At one slot, on a configuration of
the form `x_{0←z}`, this factor is `1_A z`, and it is invisible once multiplied by a window `χ`
supported in `A`. -/

/-- **The windowed amplitude of the FS-faithful projected state at one slot.**  If the window `χ`
vanishes off `A`, then `Q_{A,0}φ` and `Q_{A}φ` (without indicator) have the same windowed
amplitude, because the box indicator `1_A` acts as the identity on the support of `χ`. -/
lemma tBamp_boxQInd_eq_boxQ_N1 {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχA : ∀ z : EuclideanSpace ℝ (Fin 3), χ z ≠ 0 → z ∈ A)
    (φ : Submission.BoseGases.X 1 → ℝ) (p : EuclideanSpace ℝ (Fin 3))
    (x : Submission.BoseGases.X 1) :
    Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A 0 φ) 0 x
      = Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A 0 φ) 0 x := by
  rw [Work.SmallBoxTBWord.tBamp_eq_kinFT, Work.SmallBoxTBWord.tBamp_eq_kinFT]
  congr 1
  funext z
  by_cases hz : χ z = 0
  · rw [hz]; push_cast; ring
  · have hzA : z ∈ A := hχA z hz
    have hupd : Function.update x (0 : Fin 1) z = (fun _ : Fin 1 => z) := by
      funext j; fin_cases j; simp
    have h1 : Work.UBBInputs8.boxQInd volA A 0 φ (Function.update x 0 z)
        = φ (fun _ : Fin 1 => z) - (1 / volA) * ∫ z' in A, φ (fun _ : Fin 1 => z') := by
      rw [Work.BSKinetic.boxQInd_N1_apply, hupd]
      rw [Set.indicator_of_mem hzA, one_mul]
    have h2 : Work.SmallBoxTBWord.boxQ volA A 0 φ (Function.update x 0 z)
        = φ (fun _ : Fin 1 => z) - (1 / volA) * ∫ z' in A, φ (fun _ : Fin 1 => z') := by
      rw [Work.BSKinetic.boxQ_N1, hupd]
    rw [h1, h2]

/-- **The FS-faithful `p`-diagonal form at one slot equals the corpus's indicator-free one.**  The
two differ only in `boxQInd` versus `boxQ`, which have the same windowed amplitude
(`tBamp_boxQInd_eq_boxQ_N1`). -/
lemma tBdiagFormInd_one_eq_tBdiagForm {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχA : ∀ z : EuclideanSpace ℝ (Fin 3), χ z ≠ 0 → z ∈ A) (F : ℝ → ℝ)
    (φ : Submission.BoseGases.X 1 → ℝ) :
    Work.UBBInputs8.tBdiagFormInd a A volA χ F φ
      = Work.SmallBoxTBWord.tBdiagForm a A volA χ F φ := by
  rw [Work.UBBInputs8.tBdiagFormInd, Work.SmallBoxTBWord.tBdiagForm, Fin.sum_univ_one,
    Fin.sum_univ_one]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  have hinner : (∫ x in Submission.BoseGases.abox 1 a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A 0 φ) 0 x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox 1 a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A 0 φ) 0 x‖ ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [tBamp_boxQInd_eq_boxQ_N1 hχA]
  rw [hinner]

/-! ## 2. The `N = 1` collapse of the sliding word to `bsW` -/

/-- **The `N = 1` sliding spectral half, in `bsW` form.**  At the sliding geometry
`A = dlBox ℓ d u`, `volA = |dlBox ℓ d u|`, `χ = chiB ℓ d u`, the FS-faithful word
`tBwordKinInd` is `(2π)⁻³` times the `fsKinCoeff c`-weighted `p`-space norm² of the windowed
mean-free fibre `z ↦ χ_{B(u)}(z)·(φ(1,z) − ⨍_{B(u)}φ(1,·))`. -/
lemma tBwordKinInd_one_eq_bsW {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (φ : Submission.BoseGases.X 1 → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u) c φ
    = ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
        (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiB ℓ d u z *
          (φ (fun _ : Fin 1 => z) - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ z' in Submission.BoseGases.dlBox ℓ d u, φ (fun _ : Fin 1 => z'))) := by
  rw [Work.UBBInputs8.tBwordKinInd,
    tBdiagFormInd_one_eq_tBdiagForm (fun z hz =>
      Submission.BoseGases.chiB_support_mem hℓ hd u z hz),
    Work.BSKinetic.tBdiagForm_one_eq_bsW hℓ]

/-! ## 3. The requested statement -/

theorem integral_tBwordKinInd_eq_bsW {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hc : 0 ≤ c)
    (φ : Submission.BoseGases.X 1 → ℝ) (hφ : ContDiff ℝ (⊤ : ENat) φ) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => ((2 * Real.pi) ^ 3)⁻¹ *
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiB ℓ d u z *
            (φ (fun _ : Fin 1 => z) - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ d u, φ (fun _ : Fin 1 => z')))) ∧
    (∫ u : EuclideanSpace ℝ (Fin 3),
        Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u) c φ)
      = ∫ u : EuclideanSpace ℝ (Fin 3), ((2 * Real.pi) ^ 3)⁻¹ *
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiB ℓ d u z *
            (φ (fun _ : Fin 1 => z) - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ d u, φ (fun _ : Fin 1 => z'))) := by
  -- the pointwise `N = 1` collapse
  have hpt : ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u) c φ
      = ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiB ℓ d u z *
            (φ (fun _ : Fin 1 => z) - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ d u, φ (fun _ : Fin 1 => z'))) :=
    fun u => tBwordKinInd_one_eq_bsW hℓ hd φ u
  refine ⟨?_, ?_⟩
  · -- integrability: transported from the delivered marginal of the *full* word at `ε = 0`,
    -- where the gap half is switched off and only the spectral half remains
    have hInt : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.UBBInputs8.tBwordBInd 1 ℓ d 0 c u φ) :=
      Work.BoseFixB1.integrable_tBwordBInd (ℓ := ℓ) (d := d) (ε := 0) (c := c) hℓ hd (N := 1) hφ
    refine hInt.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd]
    rw [show Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) 0 = 0 from by
      rw [Work.SmallBoxTBWord.tbGapCoeff]; ring]
    rw [zero_mul, zero_add]
    exact hpt u
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    exact hpt u

end

end Work.BoseFixB1P
