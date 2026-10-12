import ChallengeDeps
import Submission.Work.BoseWire.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseWire/Consumers` — the wire in the shapes callers ask for

Three immediate consequences of the area's main theorem
`Work.BoseWire.HBoxGpTarget_of_LHYBoxBInput`, stated in the shapes a caller (in particular the
lead wiring `Submission.lean`) needs:

* `Work.BoseWire.hpres_of_LHYBoxBInput` — the corpus's pressure-level
  LHY-Background bound `hpres` (the single `sorry` of `Submission.lean`) at the challenge's own
  constants `η = 1/2000`, `K = 1`, in the *exact* shape of the `have hpres : …` block inside
  `Submission.BoseGases.theorem_1_2`;
* `Work.BoseWire.theorem_1_2_of_LHYBoxBInput` — the challenge statement in the corpus's
  `etaBose`/coefficient-`1` form, i.e. the conclusion of `Work.BoseTop.theorem_1_2_of_HBoxGp`
  (the lead converts it to the challenge's `Submission.BoseGases.η`/`𝓒` by `simpa` exactly as
  `Work.BoseTop.WireCheck` does);
* `Work.BoseWire.HBoxGpTarget_of_LHYBoxB` — the wire with the box theorem taken *unbundled*
  (`h : ScatSol v`, `η₀`, `C` explicit), for a caller who has a concrete box theorem rather than
  the packaged `LHYBoxBInput`.

All three are proved from the single theorem `HBoxGpTarget_of_LHYBoxBInput` plus the corpus's
proved pressure-level reductions (`Work.BoseTop.hpres_of_HBoxGp`,
`Work.BoseTop.theorem_1_2_of_HBoxGp`); no new mathematics.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseWire

open _root_.BoseGases Submission.BoseGases
open Work.UBB Work.BoseBoxFix Work.BoseTop

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The corpus's `hpres` from the wire's input -/

/-- **The corpus's pressure-level bound from the wire's input**, at the challenge's constants:
`lhyRhs (a v) 1 (1/2 + etaBose) ρ ≤ gcPressure v ρmax (8π a v ρ) + 8π a v ρ · ρ` eventually.

This is verbatim the shape of the `have hpres : …` block of
`Submission.BoseGases.theorem_1_2`; a caller who has `ηBose = 1/2000` and `𝓒 = 1` converts it
with `simpa [etaBose]` (and `Submission.BoseGases.𝓒`). -/
theorem hpres_of_LHYBoxBInput {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v)
    (hv_radial : BoseGases.IsRadial v) (hv_memL1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hIn : LHYBoxBInput v) :
    ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      Submission.BoseGases.lhyRhs (BoseGases.a v) 1 (1 / 2 + Work.BoseTop.etaBose) ρ ≤
        Submission.BoseGases.gcPressure v ρmax (8 * Real.pi * BoseGases.a v * ρ)
          + 8 * Real.pi * BoseGases.a v * ρ * ρ := by
  obtain ⟨η₀, Cw, hη₀, hη₀le, hCw, hGp⟩ :=
    HBoxGpTarget_of_LHYBoxBInput v hv_nonneg hv_radial hv_memL1 hR hv_supp hIn
  exact Work.BoseTop.hpres_of_HBoxGp hv_nonneg hv_memL1 hR.le hv_supp
    (av_nonneg_of_LHYBoxBInput hv_nonneg hv_radial hR hv_supp hIn)
    (η := Work.BoseTop.etaBose) (η₀ := η₀) (Cw := Cw) (K := 1)
    Work.BoseTop.etaBose_pos (by rw [Work.BoseTop.etaBose]; exact hη₀) hCw (by norm_num) hGp

/-! ## The challenge inequality from the wire's input -/

/-- **The challenge inequality from the wire's input**, in the corpus's own normalisation
(`etaBose = 1/2000`, coefficient `1`): this is exactly the conclusion of
`Work.BoseTop.theorem_1_2_of_HBoxGp`, with its target hypothesis replaced by `LHYBoxBInput v`. -/
theorem theorem_1_2_of_LHYBoxBInput (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v)
    (hv_radial : BoseGases.IsRadial v) (hv_memL1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hIn : LHYBoxBInput v) :
    0 < Work.BoseTop.etaBose ∧ ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      BoseGases.e ρ v ≥ 4 * Real.pi * ρ ^ 2 * BoseGases.a v *
        (1 + (128 / (15 * Real.sqrt Real.pi)) * Real.sqrt (ρ * BoseGases.a v ^ 3) -
          1 * (ρ * BoseGases.a v ^ 3) ^ (1 / 2 + Work.BoseTop.etaBose)) :=
  Work.BoseTop.theorem_1_2_of_HBoxGp v hv_nonneg hv_memL1 hR hv_supp
    (av_nonneg_of_LHYBoxBInput hv_nonneg hv_radial hR hv_supp hIn)
    (HBoxGpTarget_of_LHYBoxBInput v hv_nonneg hv_radial hv_memL1 hR hv_supp hIn)

/-! ## The wire with an unbundled box theorem -/

/-- **The wire with the box theorem unbundled**: a caller holding a concrete scattering solution
`h`, exponent `η₀` and coefficient `C` with `LHYBoxB v h η₀ C` (and the numerical side
conditions) gets `HBoxGpTarget v` directly, without packaging the existential first. -/
theorem HBoxGpTarget_of_LHYBoxB {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v)
    (hv_radial : BoseGases.IsRadial v) (hv_memL1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {h : ScatSol v} {η₀ C : ℝ} (hη₀ : 1 / 2000 < η₀) (hη₀le : η₀ ≤ 1 / 2)
    (hC : 0 ≤ C) (hL : LHYBoxB v h η₀ C) : HBoxGpTarget v :=
  HBoxGpTarget_of_LHYBoxBInput v hv_nonneg hv_radial hv_memL1 hR hv_supp
    (LHYBoxBInput.of_LHYBoxB hη₀ hη₀le hC hL)

/-! ## The wire with the challenge's complete hypothesis list -/

/-- The wire with the challenge's *complete* binder list — including the unused
`¬ v =ᵐ[volume] 0` — so that a caller can discharge it against the challenge's hypotheses
verbatim instead of dropping a binder. -/
theorem HBoxGpTarget_of_LHYBoxBInput_challenge (v : ℝ³ → ℝ) (hv_ne_zero : ¬ v =ᵐ[volume] 0)
    (hv_nonneg : 0 ≤ v) (hv_radial : BoseGases.IsRadial v) (hv_memL1 : MeasureTheory.MemLp v 1
      MeasureTheory.volume)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hIn : LHYBoxBInput v) : HBoxGpTarget v :=
  HBoxGpTarget_of_LHYBoxBInput v hv_nonneg hv_radial hv_memL1 hR hv_supp hIn

end Work.BoseWire
