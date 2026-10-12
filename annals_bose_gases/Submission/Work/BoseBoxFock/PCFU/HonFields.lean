import ChallengeDeps
import Submission.Work.BoseBoxFock.PCFU.honKap_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.HonFields` — the honest env's cubic-row fields

`Work.BoseBoxFock.FRK.PotCubicFreeU`'s left-hand side is
`⟨Θ, potCubic (boxSlotSum e) (HM μ).f (HM μ).g univ E Θ⟩` with
`E = (HonestBoxFam v h fc fu HM μ).E`.  After `cIPn_potCubic_kernelForm` the weights entering the
pinned normal form are `E.fL s`, `E.W1 k` and the factor `E.ell⁻³`.  This module records the three
identifications that let the pinned form be written in the chapter's own frame vocabulary
`fLh`/`W1h`/`ellH` (which is what `MiddleU` and the frame lemmas use):

* `E.ell = ellH v μ` (`Work.BoseRowsFS.honE_ell`),
* `E.W1 k = W1h v h μ fu (HM μ).N k` (`Work.BoseRowsFS.honE_W1_apply` + `honF_kmom`),
* `E.fL s = fLh v fc μ (HM μ).N s` (`Work.BoseRowQ2.RowGchiMaskRowAux.honE_fL_eq` + the
  bridge `honKap v μ = (d²·ellH v μ)⁻¹` proved in `PCFU/honKap_eq.lean`).

All `sorry`-free.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

open Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The honest environment's `ℓ` is `ellH v μ`. -/
theorem honE_ell_eq_local (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    (HonestBoxFam v h fc fu HM μ).E.ell = ellH v μ :=
  Work.BoseRowsFS.honE_ell v h fc fu HM μ hμ hav

/-- The honest environment's `Ŵ₁` is the chapter's `W1h`. -/
theorem honE_W1_eq_W1h (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) (k : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.W1 k = W1h v h μ fu (HM μ).N k := by
  have hside : ellH v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
  rw [Work.BoseRowsFS.honE_W1_apply v h fc fu HM μ hμ hav k, Work.BoseRowsFS.honF_kmom]
  simp only [W1h, Work.BoseRowsFS.honKmom, ← hside]

/-- The honest environment's `f_L` is the chapter's `fLh`. -/
theorem honE_fL_eq_fLh (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) (s : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.fL s = fLh v fc μ (HM μ).N s := by
  rw [Work.BoseRowQ2.RowGchiMaskRowAux.honE_fL_eq HM μ s,
    Work.BoseRowsFS.honF_kmom v h fc fu HM μ,
    honKap_eq v h hμ hav,
    show ellH v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) from by
      rw [ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]]
  rfl

end Work.BoseBoxFock.PCFU


namespace Work.BoseBoxFock.PCFU

open Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The honest env's **atom-1 (annihilation-slot) kernel** is the chapter's `MiddleU`. -/
theorem honE_chOne_eq_MiddleU (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) (x y u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), ∑ k : Lab (HM μ).N,
        (((HonestBoxFam v h fc fu HM μ).E.fL s
            * (HonestBoxFam v h fc fu HM μ).E.W1 k : ℝ) : ℂ)
          * star (pinQ v μ (HM μ).N (s - k) y) * pinTheta v μ (HM μ).N s x
          * star (pinQ v μ (HM μ).N k u))
      = MiddleU v h fc fu μ (HM μ).N x y u := by
  simp only [MiddleU]
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [honE_fL_eq_fLh v h fc fu HM μ hμ hav s, honE_W1_eq_W1h v h fc fu HM μ hμ hav k]

/-- The honest env's **atom-2 (creation-slot) kernel** is the chapter's `MiddleV`. -/
theorem honE_chTwo_eq_MiddleV (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) (c : ℂ) (xi y xj u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), ∑ k : Lab (HM μ).N,
        (((HonestBoxFam v h fc fu HM μ).E.fL s
            * (HonestBoxFam v h fc fu HM μ).E.W1 k : ℝ) : ℂ)
          * pinQ v μ (HM μ).N k xi * star (pinTheta v μ (HM μ).N s y)
          * pinQ v μ (HM μ).N (s - k) xj * star (pinCond v μ c u))
      = MiddleV v h fc fu μ (HM μ).N c xi y xj u := by
  simp only [MiddleV]
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [honE_fL_eq_fLh v h fc fu HM μ hμ hav s, honE_W1_eq_W1h v h fc fu HM μ hμ hav k]

end Work.BoseBoxFock.PCFU
