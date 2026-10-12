import ChallengeDeps
import Submission.Work.BoseWireFix.Pos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseWireFix/hpres_of_LHYBoxBPos` — the corpus's `hpres` from the `∀ h`-box
input, with **no** scattering-solution existence hypothesis

Audit item 2 of `Submission/Work/BOSE_INTEGRATION_AUDIT.md` §4.  Companion of
`Work.BoseWire.hpres_of_LHYBoxBInput` (`Submission/Work/BoseWire/Consumers.lean`), with the
bundle `hIn : LHYBoxBInput v` — whose first component is a *witness* `h : ScatSol v`, i.e. FS's
T1 — replaced by the universally quantified input

    hIn : ∀ h : ScatSol v, 0 < a v → ∃ η₀ C, 1/2000 < η₀ ∧ η₀ ≤ 1/2 ∧ 0 ≤ C ∧ LHYBoxB v h η₀ C.

The proof is the case split the audit asks for:

* **`0 < a v`**: `0 < a v` produces a witness `h : ScatSol v`
  (`Work.BoseWireFix.exists_scatSol_of_av_pos`, from `a_eq_zero_of_not_exists`), `hIn h hav`
  gives `(η₀, C)`, and `Work.BoseWire.hpres_of_LHYBoxBInput` finishes — with
  `LHYBoxBInput v` *constructed*, not assumed;
* **`¬ 0 < a v`**: `0 ≤ a v` is `Work.BoseWireFix.av_nonneg` (the corpus's `av_nonneg`, which
  uses `chosen_av_bounds_weak` in the branch where a witness exists and
  `a_eq_zero_of_not_exists` otherwise), hence `a v = 0`, and
  `Work.BoseTop.hpres_of_HBoxGp` fed with `Work.BoseTop.HBoxGp_of_av_zero` gives the bound
  with no box input at all (`Submission.BoseGases.hpres_of_av_zero` is exactly the inside of
  that call).

So neither T1 (`Submission.ScatFacts.exists_radial_scattering_solution`) nor T2 (`av_pos`)
appears anywhere in this proof.

## Main declarations

| name | statement |
|---|---|
| `hpres_of_LHYBoxBPos` | the corpus `hpres` (the shape of the `have hpres` block of `theorem_1_2`) from the `∀ h`-input |
| `HBoxGpTarget_of_LHYBoxBPos` | the pressure-level target `Work.BoseTop.HBoxGpTarget v` from the `∀ h`-input |
| `theorem_1_2_of_LHYBoxBPos` | the challenge inequality (corpus normalisation `etaBose`, coefficient `1`) from the `∀ h`-input |
| `hpres_of_LHYBoxBPos_challenge` | the same `hpres` at the challenge's complete binder list (including the unused `¬ v =ᵐ 0`) |
-/

/-! ## 0. Where the `∀ h`-input comes from

The B-side produces this predicate directly: `Work.BoseFixGlue.Ports.LHYBoxB_of_grading` takes
`h : ScatSol v`, `hav : 0 < a v`, the two node hypotheses and returns `LHYBoxB v h η₀ (C+1)`.
`Submission/Work/BoseWireFix/OfGrading.lean` in this directory packages that into
`Work.BoseWireFix.LHYBoxBPos_of_grading`, so a caller never has to do the constant arithmetic.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseWireFix

open _root_.BoseGases Submission.BoseGases
open Work.UBB Work.BoseBoxFix Work.BoseTop

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The corpus's `hpres` -/

/-- **The corpus's pressure-level bound from the `∀ h`-box input**, at the challenge's constants:
`lhyRhs (a v) 1 (1/2 + etaBose) ρ ≤ gcPressure v ρmax (8π a v ρ) + 8π a v ρ · ρ` eventually.

This is verbatim the shape of the `have hpres : …` block of `Submission.BoseGases.theorem_1_2`,
with `Work.BoseWire.hpres_of_LHYBoxBInput`'s bundled input `LHYBoxBInput v` replaced by the
`∀ h`-form `LHYBoxBPos v`; a caller who has `ηBose = 1/2000` and `𝓒 = 1` converts it with
`simpa [etaBose]` (and `Submission.BoseGases.𝓒`).

No existence of a scattering solution is used. -/
theorem hpres_of_LHYBoxBPos {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v)
    (hv_radial : _root_.BoseGases.IsRadial v) (hv_memL1 : MemLp v 1 volume)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hIn : LHYBoxBPos v) :
    ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      Submission.BoseGases.lhyRhs (BoseGases.a v) 1 (1 / 2 + Work.BoseTop.etaBose) ρ ≤
        Submission.BoseGases.gcPressure v ρmax (8 * Real.pi * BoseGases.a v * ρ)
          + 8 * Real.pi * BoseGases.a v * ρ * ρ := by
  by_cases hav : 0 < BoseGases.a v
  · -- the box branch: `0 < a v` supplies the witness, so the bundle `LHYBoxBInput` is inhabited
    exact Work.BoseWire.hpres_of_LHYBoxBInput hv_nonneg hv_radial hv_memL1 hR hv_supp
      (LHYBoxBPos.toInput hIn (exists_scatSol_of_av_pos hav) hav)
  · -- the `a v = 0` branch: no box input at all
    have hav0 : BoseGases.a v = 0 := av_eq_zero_of_not_pos hv_nonneg hv_radial hR hv_supp hav
    exact Work.BoseTop.hpres_of_HBoxGp hv_nonneg hv_memL1 hR.le hv_supp (by rw [hav0])
      (η := Work.BoseTop.etaBose) (η₀ := 1 / 4) (Cw := 0) (K := 1)
      Work.BoseTop.etaBose_pos (by rw [Work.BoseTop.etaBose_eq]; norm_num)
      (by norm_num) (by norm_num)
      (Work.BoseTop.HBoxGp_of_av_zero hv_nonneg hv_memL1 hav0)

/-! ## 2. The wire at the `∀ h`-input -/

/-- **The wire's main theorem at the `∀ h`-input**: `LHYBoxBPos v` produces the pressure-level
target `Work.BoseTop.HBoxGpTarget v`.  Same two-branch structure as
`Work.BoseWire.HBoxGpTarget_of_LHYBoxBInput`, but the `a v = 0` branch is decided by
`¬ 0 < a v` (so T2 is not needed) and the `0 < a v` branch builds the `LHYBoxBInput` bundle
from the witness that `0 < a v` supplies (so T1 is not needed). -/
theorem HBoxGpTarget_of_LHYBoxBPos {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v)
    (hv_radial : _root_.BoseGases.IsRadial v) (hv_memL1 : MemLp v 1 volume)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hIn : LHYBoxBPos v) : HBoxGpTarget v := by
  by_cases hav : 0 < BoseGases.a v
  · exact Work.BoseWire.HBoxGpTarget_of_LHYBoxBInput v hv_nonneg hv_radial hv_memL1 hR hv_supp
      (LHYBoxBPos.toInput hIn (exists_scatSol_of_av_pos hav) hav)
  · exact Work.BoseTop.HBoxGpTarget_of_av_zero hv_nonneg hv_memL1
      (av_eq_zero_of_not_pos hv_nonneg hv_radial hR hv_supp hav)

/-- **The challenge inequality from the `∀ h`-input**, in the corpus's normalisation
(`etaBose = 1/2000`, coefficient `1`): exactly the conclusion of
`Work.BoseTop.theorem_1_2_of_HBoxGp`, with its target hypothesis supplied by
`HBoxGpTarget_of_LHYBoxBPos` and its `0 ≤ a v` hypothesis by `Work.BoseWireFix.av_nonneg`. -/
theorem theorem_1_2_of_LHYBoxBPos (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v)
    (hv_radial : _root_.BoseGases.IsRadial v) (hv_memL1 : MemLp v 1 volume)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hIn : LHYBoxBPos v) :
    0 < Work.BoseTop.etaBose ∧ ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      BoseGases.e ρ v ≥ 4 * Real.pi * ρ ^ 2 * BoseGases.a v *
        (1 + (128 / (15 * Real.sqrt Real.pi)) * Real.sqrt (ρ * BoseGases.a v ^ 3) -
          1 * (ρ * BoseGases.a v ^ 3) ^ (1 / 2 + Work.BoseTop.etaBose)) :=
  Work.BoseTop.theorem_1_2_of_HBoxGp v hv_nonneg hv_memL1 hR hv_supp
    (av_nonneg hv_nonneg hv_radial hR hv_supp)
    (HBoxGpTarget_of_LHYBoxBPos hv_nonneg hv_radial hv_memL1 hR hv_supp hIn)

/-! ## 3. The challenge's complete binder list -/

/-- The `hpres` bound with the challenge's *complete* binder list — including the unused
`¬ v =ᵐ[volume] 0` — so that a caller who is replacing the `have hpres` block of
`Submission.BoseGases.theorem_1_2` can discharge the binders verbatim instead of dropping one.
(This is the `LHYBoxBPos` twin of `Work.BoseWire.HBoxGpTarget_of_LHYBoxBInput_challenge`.) -/
theorem hpres_of_LHYBoxBPos_challenge (v : ℝ³ → ℝ) (hv_ne_zero : ¬ v =ᵐ[volume] 0)
    (hv_nonneg : 0 ≤ v) (hv_radial : _root_.BoseGases.IsRadial v)
    (hv_memL1 : MemLp v 1 volume) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hIn : LHYBoxBPos v) :
    ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      Submission.BoseGases.lhyRhs (BoseGases.a v) 1 (1 / 2 + Work.BoseTop.etaBose) ρ ≤
        Submission.BoseGases.gcPressure v ρmax (8 * Real.pi * BoseGases.a v * ρ)
          + 8 * Real.pi * BoseGases.a v * ρ * ρ :=
  hpres_of_LHYBoxBPos hv_nonneg hv_radial hv_memL1 hR hv_supp hIn

end Work.BoseWireFix
