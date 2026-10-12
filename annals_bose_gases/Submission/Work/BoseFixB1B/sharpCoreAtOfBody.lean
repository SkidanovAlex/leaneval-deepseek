import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.pbwNonneg
import Submission.Work.BoseFixB1B.tendsto_cutProd_mass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.sharpCoreAtOfBody`

**The sharp count core from the count core.**  `CountCoreAt` is the count inequality at *smooth
symmetric in-box* states; `SharpCountCoreAt` is the same inequality at the *sharp* (box-indicator
times smooth) states.  The passage is the analytic content of the sharp extension, and it is
assembled here from four inputs:

* the **geometric** input: a smooth cutoff family of the sliding box
  (`∃ K γ, IsCutFamily L d u K γ`, from `Work.BoseFixB1B.exists_smoothCutoff`);
* the **word convergence** along the approximants `∏ᵢγ_δ(xᵢ)·ψ → 1_{B(u)^k}ψ`
  (`Work.BoseFixB1B.fibreWord_tendsto_cutProd`);
* the **mass convergence** (`Work.BoseFixB1B.tendsto_cutProd_mass`, proved in this directory);
* the **degenerate case**: if the sharp mass `∫(1_{B^k}ψ)²` vanishes then the sharp state vanishes
  a.e. and the word vanishes (`Work.BoseFixB1B.sharpBoxState_ae_eq_zero_of_mass_zero`,
  `Work.BoseFixB1B.fibreWord_ae_eq_zero`).

The nondegenerate case is `sharpCountCoreAt_of_tendsto`; the degenerate case is the two a.e.-zero
lemmas.  Everything else is bookkeeping.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge Work.PerSector Work.SlotWord

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The sharp count core from the count core.** -/
theorem sharpCountCoreAt_of_bodyBox {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ}
    {L d ε c μ : ℝ} {u : E3} {k : ℕ} {T : ℝ}
    (hL : 0 < L) (hd : 0 < d)
    (hcore : CountCoreAt h M L d ε c μ u k T)
    (hIsCut : ∃ K : ℝ, ∃ γ : ℝ → E3 → ℝ, IsCutFamily L d u K γ)
    (hconv : ∀ ψ : X k → ℝ, ContDiff ℝ (⊤ : ENat) ψ →
      ∀ (K : ℝ) (γ : ℝ → E3 → ℝ), IsCutFamily L d u K γ → ∀ Cb : ℝ, 0 ≤ Cb →
        (∀ x ∈ abox k L, |ψ x| ≤ Cb) →
        Filter.Tendsto
          (fun δ : ℝ => Work.SlotWord.fibreWord h M k L d ε c μ u (cutProd (γ δ) ψ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (Work.SlotWord.fibreWord h M k L d ε c μ u
            (sharpBoxState (dlBox L d u) ψ))))
    (hae : ∀ ψ : X k → ℝ, Continuous ψ →
      (∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2) = 0 →
      ∀ᵐ x ∂((volume : Measure (X k)).restrict (abox k L)),
        sharpBoxState (dlBox L d u) ψ x = 0)
    (hfw : ∀ Ψ : X k → ℝ,
      (∀ᵐ x ∂((volume : Measure (X k)).restrict (abox k L)), Ψ x = 0) →
      Work.SlotWord.fibreWord h M k L d ε c μ u Ψ = 0) :
    SharpCountCoreAt h M L d ε c μ u k T := by
  intro ψ hψcd hψperm
  set ms : ℝ := ∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2 with hms
  have hms_nonneg : 0 ≤ ms := integral_nonneg fun x => sq_nonneg _
  rcases lt_or_ge 0 ms with hms0 | hms0
  · -- nondegenerate case: the two convergences
    obtain ⟨K, γ, hcut⟩ := hIsCut
    obtain ⟨Cb, hCb⟩ := (abox_compact k hL).exists_bound_of_continuousOn
      hψcd.continuous.continuousOn
    set Cb' : ℝ := max Cb 0 with hCb'def
    have hCb'0 : 0 ≤ Cb' := le_max_right _ _
    have hψb : ∀ x ∈ abox k L, |ψ x| ≤ Cb' := by
      intro x hx
      rw [← Real.norm_eq_abs]
      exact le_trans (hCb x hx) (le_max_left _ _)
    exact sharpCountCoreAt_of_tendsto (k := k) (T := T) (K := K) (γ := γ)
      (ψ := ψ) hL hd hcut hψcd hψperm hcore
      (hconv ψ hψcd K γ hcut Cb' hCb'0 hψb)
      (tendsto_cutProd_mass (k := k) (L := L) (d := d) (u := u) (ψ := ψ) (K := K)
        (γ := γ) hL hd hcut hψcd.continuous)
      hms0
  · -- degenerate case: both sides vanish
    have hm0 : ms = 0 := le_antisymm hms0 hms_nonneg
    have hI : (∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2) = 0 := hm0
    have hae0 := hae ψ hψcd.continuous hI
    have hfw0 := hfw (sharpBoxState (dlBox L d u) ψ) hae0
    rw [hm0, zero_mul, hfw0]

end Work.BoseFixB1B
