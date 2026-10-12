import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.Aux.pIndOrth` — buildable mirror of `Submission/Work/BoseFixB1S/Aux/pIndOrth.lean`

**Why this file exists.**  The lemma `Work.BoseFixB1S.Aux.pIndOrth` was requested at the workspace
path `Submission/Work/BoseFixB1S/Aux/pIndOrth.lean`.  That *module* can never be built with the
pinned toolchain (Lean v4.33.0): the Lean frontend rejects any module whose name has a component
matching a Windows reserved file name (`CON`, `PRN`, **`AUX`**, `NUL`, `COM1`–`COM9`,
`LPT1`–`LPT9`), with the hard error

    module name 'Submission.Work.BoseFixB1S.Aux.pIndOrth' is not portable:
      'Aux' is a reserved file name on some operating systems

(cf. `Lean/Elab/Import.lean`, `osForbiddenNames` / `checkModuleNamePortability`, which is invoked
unconditionally from `processHeaderCore` *before* any elaboration, so no file content can avoid
it).  The error is emitted on every `lake build` of that module, so neither the file nor anything
importing it can ever be verified.

This file is a byte-for-byte mathematical mirror of the requested file: it defines the *same*
fully qualified name `Work.BoseFixB1S.Aux.pIndOrth` (the namespace, not the module path, determines
the name) with the *same* statement and the *same* proof, but at a legal module path
(`Submission.Work.BoseFixB1S.Auxiliary.pIndOrth`), so that the lemma is available to the compiled
corpus.  If the `Aux`-named path ever becomes usable (toolchain change or file move), one of the
two files should be deleted to avoid a duplicate declaration of the name.

The mathematics: with `Pᵢ = Work.UBBInputs8.boxPInd volA A i Φ` (FS `eq:HBU`,
`P_{B,i}ψ = |B|⁻¹⟨1_B,ψ⟩1_B` in slot `i`) and `σᵢ(x) = 1_A(x i)`, the target identity is

    ∫_{abox N ℓ} PᵢΦ · (σᵢ Φ − PᵢΦ) = 0,

i.e. `Pᵢ` is *orthogonal* to `σᵢ Φ − PᵢΦ`: the box-projected part of `σᵢ Φ` and its complement are
orthogonal in `L²(abox N ℓ)`.  Both integrals reduce to the single slot-peeled quantity of the
corpus:

* `∫ PᵢΦ · (σᵢ Φ) = ∫ Φ · PᵢΦ` **pointwise** — since `PᵢΦ` already carries the factor
  `σᵢ(x i) ∈ {0,1}`, the extra box indicator in the first factor is absorbed (`σᵢ² = σᵢ`); then
  `Work.BoseFixB1S.Q0C.one_self_N` evaluates this at `volA * ∫_{abox n ℓ} (oneRest)²`;
* `∫ PᵢΦ · PᵢΦ = ∫ (PᵢΦ)²`, which by the flat identity `Work.BoseFixB1S.Q0C.one_flat` is the
  *same* value `volA * ∫_{abox n ℓ} (oneRest)²`.

The difference is therefore zero.  Integrability of both products on the compact box is the
boundedness/measurability API of `Work.BoseFixB1S.BoxPIndFlat` (`measurable_boxPInd`,
`abs_boxPInd_le`, `integrableOn_mul_of_bound`), the bound coming from continuity of `Φ` on the
compact `abox N ℓ`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S.Aux

open Submission.BoseGases

set_option maxHeartbeats 800000

/-- **Orthogonality of the FS box projection.**  For `A ⊆ acube ℓ` of measure `volA`,
`Pᵢ = boxPInd volA A i` and continuous `Φ`,

    ∫_{abox N ℓ} (PᵢΦ) · ((1_A(·ᵢ) Φ) − PᵢΦ) = 0. -/
theorem pIndOrth {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x)
          * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
              - Work.UBBInputs8.boxPInd volA A i Φ x)) = 0 := by
  -- `Φ` is bounded on the compact box, hence so are `PᵢΦ` and `1_A(·ᵢ)Φ`.
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have habsC : ∀ x ∈ abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  have hvolA' : volA = (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).real A := by
    rw [MeasureTheory.Measure.real_def]; exact hvolA
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦc.measurable
  have hPb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i habsC
  have hgm : Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) :=
    ((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hΦc.measurable
  have hgb : ∀ x ∈ abox N ℓ, |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
    intro x hx
    rw [abs_mul]
    have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * C :=
          mul_le_mul hind (habsC x hx) (abs_nonneg _) (by norm_num)
      _ = C := one_mul C
  have hint_g : IntegrableOn (fun x : X N =>
      Work.UBBInputs8.boxPInd volA A i Φ x * (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x))
      (abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hPm hgm hPb hgb
  have hint_P : IntegrableOn (fun x : X N =>
      Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)
      (abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hPm hPm hPb hPb
  -- Split the integral of the difference into the difference of the integrals.
  have hsplit :
      (∫ x in abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x)
          * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
              - Work.UBBInputs8.boxPInd volA A i Φ x))
        = (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x)
              * (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x))
          - (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x)
              * Work.UBBInputs8.boxPInd volA A i Φ x) := by
    have h1 : (∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x)
            * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
                - Work.UBBInputs8.boxPInd volA A i Φ x))
        = ∫ x in abox N ℓ, ((Work.UBBInputs8.boxPInd volA A i Φ x)
              * (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
            - (Work.UBBInputs8.boxPInd volA A i Φ x)
              * Work.UBBInputs8.boxPInd volA A i Φ x) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [h1]
    exact MeasureTheory.integral_sub hint_g hint_P
  -- The two integrals agree: `∫ PᵢΦ·(σᵢΦ) = ∫ Φ·PᵢΦ = volA·∫ (oneRest)²` and the same for
  -- `∫ (PᵢΦ)²` — the pointwise identity `σᵢ² = σᵢ` absorbs the extra box indicator.
  have hcross :
      (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x)
              * (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x))
        = (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x)
              * Work.UBBInputs8.boxPInd volA A i Φ x) := by
    rw [show (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x)
              * (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x))
          = ∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Φ x from by
      apply integral_congr_ae
      filter_upwards with x
      rw [Work.UBBInputs8.boxPInd]
      by_cases h : x i ∈ A
      · rw [Set.indicator_of_mem h]; ring
      · rw [Set.indicator_of_notMem h]; ring]
    rw [Work.BoseFixB1S.Q0C.one_self_N (volA := volA) hℓ hvol hA hvolA' hAc i hΦc]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hsplit, hcross, sub_self]

end Work.BoseFixB1S.Aux
