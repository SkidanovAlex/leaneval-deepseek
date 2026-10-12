import ChallengeDeps
import Submission.Work.BoseFixB1.slidingB_holds
import Submission.Work.BoseFixB1B.matchedWindowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.matchedSlidingBCube` — the matched-window localisation reduces to
# its **kinetic half** alone

Holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.  Decision (B) of the lead; vocabulary
`Submission/Work/BoseFixB1B/matchedWindowDefs.lean`.

## What this module adds

`Work.BoseFixB1.slidingB_of_pieces` reduces the frozen localisation `SlidingB` (FS
`eq:BSsliding2` / Bratteli–Solovej Thm 3.10) to *two* halves:

* `KineticHalf` — the sliding kinetic gap plus the `u`-integral of the small-box kinetic words,
  dominated by the anchored large-box kinetic word `kinFormB` (the open analytic core);
* `PotentialHalf` — FS `lem:LocPotential`, which is a **theorem** (`Work.BoseFixB1.potentialHalf_holds`,
  proved: the telescoping identity `∫_u sbPot ≤ ∫_Λ Φ² potWordU`, the kernels being cube-based).

This module runs the *same* reduction at the matched (single cube cutoff) word `sbWordCube =
sbKinCube + sbPot` of `matchedWindowDefs.lean`, whose kinetic slot is the cube-windowed one the
proved Bogoliubov port `Work.BoseFixB1B.SlidingBogPort` consumes.  Since the potential half is
window-independent (the kernels of `sbPot` are *already* cube-based and are not touched by the
matched vocabulary), the matched localisation reduces to a **single** residual:

    Work.BoseFixB1B.SlidingBCube v h    ⟸    Work.BoseFixB1B.KineticHalfCube v h  (+ the proved PotentialHalf)

`KineticHalfCube` is `KineticHalf` with `sbKin ↦ sbKinCube` and nothing else changed — i.e. FS
`eq:BSsliding2`'s kinetic content at the cube cutoff, the object the one-body kinetic half
(`Core.meanMismatch_le` / `Core.spectral_chain` / `Core.pnorm_payment` re-run at the cube window)
is designed to supply.

The constant `C = 1` is taken, exactly as in the frozen reduction (and for the same reason: the
constant one-particle state forces `C = 1`; the matched `sbKinCube` also vanishes there).

## Status

`slidingBCube_of_pieces`, `slidingBCube_of_kineticHalf` are `sorry`-free and axiom-clean; the
residual `KineticHalfCube` is a `def : Prop` (not proved here).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The kinetic half of FS `eq:BSsliding2` at the matched (cube) cutoff**: the sliding kinetic
gap plus the `u`-integral of the cube-windowed small-box kinetic words is dominated by the
anchored large-box kinetic word `kinFormB`, together with the `u`-marginal integrability of the
matched kinetic word.  This is `Work.BoseFixB1.KineticHalf` with `sbKin ↦ sbKinCube` and nothing
else changed. -/
def KineticHalfCube (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      Integrable (fun u : E3 => sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ)) ∧
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
            / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2))
          * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ)
        + (∫ u : E3, sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ))
      ≤ Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
          (Φ : Submission.BoseGases.X n → ℝ)

/-- **The `N = 1` form of the cube kinetic half**: the matched-window analogue of the `N = 1`
inequality consumed by `Work.BoseFixB1.kineticHalf_of_oneBody` — FS `eq:BSsliding2`'s kinetic
content for a one-particle state `φ`.  By the slot decomposition
(`Work.BoseFixB1.kineticHalf_of_oneBody`) this is the only state-level input `KineticHalfCube`
needs, together with the marginal integrability below. -/
def OneBodyKineticHalfCube (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ φ : Submission.BoseGases.X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
          / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2)
          * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) φ
        + (∫ u : E3, sbKinCube v μ u φ)
      ≤ Work.BoseKinLoc.kinFormB 1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b φ

/-- **The `u`-marginal integrability of the matched kinetic word** — the matched-window analogue
of `Work.BoseFixB1.integrable_sbKin_marginal`; it is the integrability conjunct of
`KineticHalfCube`. -/
def SbKinCubeMarginalIntegrable (v : E3 → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      Integrable (fun u : E3 => sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ))

/-- **The reduction at the matched window**: the cube-windowed kinetic half together with the
potential half gives `SlidingBCube` (FS `eq:BSsliding2` at the single cube cutoff), with the
constant `C = 1`.  The proof is the frozen one (`Work.BoseFixB1.slidingB_of_pieces`) verbatim:
`wordB = kinFormB + (potential part)` is `rfl`, `sbWordCube = sbKinCube + sbPot` is `rfl`, and the
`u`-integral splits by the two marginal integrability fields. -/
theorem slidingBCube_of_pieces {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    (hKin : KineticHalfCube v h) (hPot : Work.BoseFixB1.PotentialHalf v h) : SlidingBCube v h := by
  obtain ⟨εK, hεK, hK⟩ := hKin
  obtain ⟨εP, hεP, hP⟩ := hPot
  refine ⟨min εK (min εP 1), 1, le_refl 1, lt_min hεK (lt_min hεP one_pos), ?_⟩
  intro μ hAdm n Φ
  obtain ⟨hμ, hdil, hPOK⟩ := hAdm
  have hAdmK : Work.BoseBoxFix.Adm v εK μ := ⟨hμ, le_trans hdil (min_le_left _ _), hPOK⟩
  have hAdmP : Work.BoseBoxFix.Adm v εP μ :=
    ⟨hμ, le_trans hdil (le_trans (min_le_right _ _) (min_le_left _ _)), hPOK⟩
  obtain ⟨hKinInt, hKinIneq⟩ := hK μ hAdmK n Φ
  obtain ⟨hPotInt, hPotIneq⟩ := hP μ hAdmP n Φ
  have hword : (fun u : E3 => sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
      = fun u : E3 => sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    funext u; rfl
  have hsplit : (∫ u : E3, sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
      = (∫ u : E3, sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ))
        + ∫ u : E3, Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [hword, MeasureTheory.integral_add hKinInt hPotInt]
  have hbox : Work.BoseBoxFix.wordB v h μ n (Φ : Submission.BoseGases.X n → ℝ)
      = Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
            (Φ : Submission.BoseGases.X n → ℝ)
        + ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
              * Work.BoseKinLoc.potWordU n v (g0 v h)
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 x := rfl
  rw [hbox, hsplit]
  norm_num
  linarith [hKinIneq, hPotIneq]

/-- **The matched localisation from the cube kinetic half alone.**  The potential half is a theorem
(`Work.BoseFixB1.potentialHalf_holds`), so `SlidingBCube` follows from `KineticHalfCube` — the
cube-cutoff analogue of `Work.BoseFixB1.slidingB_of_kineticHalf`. -/
theorem slidingBCube_of_kineticHalf {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    (hKin : KineticHalfCube v h) : SlidingBCube v h :=
  slidingBCube_of_pieces hKin
    (Work.BoseFixB1.potentialHalf_holds h hv1 hvrad hR hv_supp hav)

end Work.BoseFixB1B
