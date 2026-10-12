import ChallengeDeps
import Submission.Work.BoseBogFS.honest_denRow
import Submission.Work.BoseBoxFock.Clean.Bessel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honestKAP_final` — the `𝒞`-slot, closed

This module is the **single import** a consumer of the honest `𝒞`-slot needs: it assembles

* `Work.BoseBogFS.honestKAP` — the capstone-shaped reduction to the χ̂-normalisation row, the
  mass row and FS's denominator row;
* the χ̂-normalisation row `Σ_k χ̂(kℓ)² ≤ 1`, discharged by
  `Work.BoseBoxFock.Clean.honest_hatChi_sum_le` (the lattice Parseval identity
  `Σ_{n∈ℤ³}χ̂(2πn)² = ∫χ² = 1`, re-delivered taint-free in the `Clean` subtree);
* the mass row, discharged by `Work.BoseBogFS.honest_W1_mass_rows` (inside `honestKAP`);
* FS's denominator row, discharged by `Work.BoseBogFS.honest_denRow` from the two one-mode rows
  of `Work.BoseBogFS.honest_rows_basic` and the two `N`-window rows `hin`/`hout`.

## What is left open

`hin` and `hout` are the **lattice-cube window** for `N = (HM μ).N`: `hout` needs
`(1−ε_T)π²N² ≥ 1536 K_ℓ²` and `hin` needs `π²N²μa ≤ 65536 ε₀ K_ℓ²`; both are satisfiable
because `ε₀ ≥ μa³`.  They are the exact analogue of `Work.BoseBoxFock.RB4boxDomFS`'s
`∃ Nmin, Nmin μ ≤ (HM μ).N`, i.e. a constraint on the *choice* of the honest mode data.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The capstone's `hKAP` at the honest family, closed.**  All that is assumed is the standing
potential data, the `χ⋆χ` second-order condition (`C`, `r₁`), the regime rows on `ℓ` (`hRℓ`,
`hreg`, `hcond`), the slack bound `honestDD v μ R ≤ 1/2`, and the two `N`-window rows
`hin`/`hout`. -/
theorem honestKAP_final {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {R r₁ C ε₀ : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hε₀1 : ε₀ ≤ 1) (hav : 0 < a v)
    (hRℓ : ∀ μ : ℝ, Adm v ε₀ μ → R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hreg : ∀ μ : ℝ, Adm v ε₀ μ → R / Work.BoseBox.sideAt μ (a v) ≤ r₁)
    (hcond : ∀ μ : ℝ, Adm v ε₀ μ →
      C * (R / Work.BoseBox.sideAt μ (a v)) ^ 2 ≤ 1 / 4)
    (hδD1 : ∀ μ : ℝ, Adm v ε₀ μ → honestDD v μ R ≤ 1 / 2)
    (hin : ∀ μ : ℝ, Adm v ε₀ μ → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
        ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
            ≤ Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (a v)) (HM μ).N →
          R ^ 2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2 / 2
            ≤ honestDD v μ R)
    (hout : ∀ μ : ℝ, Adm v ε₀ μ → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
        Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (a v)) (HM μ).N
            < ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ →
          128 * π * (a v) * μ
            ≤ (1 - (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT)
              * (max 0 (‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
                  - ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.s
                    * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell)⁻¹)) ^ 2) :
    ∀ μ : ℝ, Adm v ε₀ μ → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      ∀ ρ : ℝ, CloseCondFS v μ ρ →
        (∑ k : Work.BoseBoxFock.Lab (HM μ).N, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr
            (bogA (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k)
            (bogB (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k)
            (bogC (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k))
          ≤ (ρ - μ) ^ 2 * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 / 2)
              * ell3 v μ * (1 + honestDelta v μ R C ρ) := by
  refine honestKAP (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM)
    (R := R) (r₁ := r₁) (C := C) (ε₀ := ε₀)
    hR hv hvrad hv_supp hC hr₁ hT hε₀1 hav hreg hcond hδD1 ?_ ?_
  · intro μ hadm hview
    exact Work.BoseBoxFock.Clean.honest_hatChi_sum_le v h fc fu HM μ
  · intro μ hadm hview ρ hclose k
    exact honest_denRow (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM)
      (R := R) (r₁ := r₁) (C := C) (ε₀ := ε₀)
      hR hv hvrad hv_supp hC hr₁ hT hε₀1 hav hRℓ hreg hcond hδD1 hin hout μ hadm hview ρ hclose k

end Work.BoseBogFS
