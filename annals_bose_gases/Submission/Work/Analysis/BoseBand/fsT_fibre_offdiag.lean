import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Analysis.BoseBand.gapWord_fibre_offdiag
import Submission.Work.Analysis.BoseBand.mainWord_fibre_offdiag
import Submission.Work.Analysis.BoseBand.momWord_fibre_offdiag
import Submission.Work.Analysis.BoseBand.neuWord_fibre_offdiag
import Submission.Work.Analysis.BoseBand.pieces_integrableOn_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Analysis.BoseBand.fsT_fibre_offdiag`

**The off-diagonal fibre bracket of the localised box kinetic word `fsT` vanishes.**

FS §6 (`lem:LocMatrices`) needs that the joint sector projections `E_S = ∏_{i∈S}Q_i ∏_{i∉S}P_i`
give a *band* structure to the box Hamiltonian.  The kinetic part of the box word `fsT`
(FS `eq:DefT`) is the sum of its four pieces `neuWord + gapWord + momWord + mainWord`, and for
each of them the polarised fibre combination

    ∫_{abox n ℓ} 1_{Λ(0)}(x_j) [ word(fibre_j(E_SΦ+E_TΦ)(x)) − word(fibre_j(E_SΦ−E_TΦ)(x)) ] dx

vanishes whenever `j ∈ S ∩ T` and `S ≠ T` (the two sectors differ in some slot `k ≠ j`, where one
of the two states is mean-free and the other independent of the coordinate `k`).  Summing the four
pieces gives the statement here.

## Proof

Unfold `fsT` as the four-term sum (`fsT_eq_sum`), split the box integral into the four
*individually integrable* pieces (each piece is `IntegrableOn` the box because both of its two
summands are, `KinOffdiag.pieces_integrableOn_fibre`, and `IntegrableOn` is closed under
subtraction), and apply the four off-diagonal lemmas — `gapWord_fibre_offdiag` of this directory,
and `neuWord/momWord/mainWord_fibre_offdiag` — to each of them.
-/

noncomputable section

open MeasureTheory

namespace Work.Analysis.BoseBand

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

theorem fsT_fibre_offdiag {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n) (hjS : (j : ℕ) ∈ S) (hjT : (j : ℕ) ∈ T) (hST : S ≠ T) : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) * (Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x) - Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0 := by
  classical
  -- the two states, and their smoothness
  have hP : ContDiff ℝ (⊤ : ℕ∞)
      (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) :=
    (Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ).add
      (Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ)
  have hMn : ContDiff ℝ (⊤ : ℕ∞)
      (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) :=
    (Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ).sub
      (Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ)
  -- integrability of the four pieces, in each of the two states
  obtain ⟨hGp, hMoP, hMaP, hNp⟩ :=
    pieces_integrableOn_fibre (ℓ := ℓ) (d := d) (s := s)
      (εT := εT) (b := b) hℓ j
      (Φ := Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) hP
  obtain ⟨hGm, hMoM, hMaM, hNm⟩ :=
    pieces_integrableOn_fibre (ℓ := ℓ) (d := d) (s := s)
      (εT := εT) (b := b) hℓ j
      (Φ := Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) hMn
  -- the four difference integrands
  set G : Submission.BoseGases.X n → ℝ := fun x => Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n j
            (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
          - Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n j
            (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)) with hGdef
  set M : Submission.BoseGases.X n → ℝ := fun x => Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n j
            (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
          - Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n j
            (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)) with hMdef
  set Ma : Submission.BoseGases.X n → ℝ := fun x => Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n j
            (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
          - Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n j
            (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)) with hMadef
  set N : Submission.BoseGases.X n → ℝ := fun x => Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n j
            (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
          - Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n j
            (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)) with hNdef
  have hGint : MeasureTheory.IntegrableOn G (Submission.BoseGases.abox n ℓ) := by
    refine (hGp.sub hGm).congr_fun ?_ (Submission.BoseGases.abox_measurable n ℓ)
    intro x hx
    simp only [Pi.sub_apply, hGdef, Work.BoseKinLoc.fibre, Pi.add_apply]
    ring
  have hMint : MeasureTheory.IntegrableOn M (Submission.BoseGases.abox n ℓ) := by
    refine (hMoP.sub hMoM).congr_fun ?_ (Submission.BoseGases.abox_measurable n ℓ)
    intro x hx
    simp only [Pi.sub_apply, hMdef, Work.BoseKinLoc.fibre, Pi.add_apply]
    ring
  have hMaint : MeasureTheory.IntegrableOn Ma (Submission.BoseGases.abox n ℓ) := by
    refine (hMaP.sub hMaM).congr_fun ?_ (Submission.BoseGases.abox_measurable n ℓ)
    intro x hx
    simp only [Pi.sub_apply, hMadef, Work.BoseKinLoc.fibre, Pi.add_apply]
    ring
  have hNint : MeasureTheory.IntegrableOn N (Submission.BoseGases.abox n ℓ) := by
    refine (hNp.sub hNm).congr_fun ?_ (Submission.BoseGases.abox_measurable n ℓ)
    intro x hx
    simp only [Pi.sub_apply, hNdef, Work.BoseKinLoc.fibre, Pi.add_apply]
    ring
  -- the four off-diagonal lemmas
  have hGz : (∫ x in Submission.BoseGases.abox n ℓ, G x) = 0 := by
    have := gapWord_fibre_offdiag (ℓ := ℓ) (b := b) hℓ j hΦ hS hT hjS hjT hST
    simpa only [hGdef] using this
  have hMz : (∫ x in Submission.BoseGases.abox n ℓ, M x) = 0 := by
    have := momWord_fibre_offdiag (ℓ := ℓ) (d := d) (εT := εT) (b := b) hℓ j hΦ hS hT hjS hjT hST
    simpa only [hMdef] using this
  have hMaz : (∫ x in Submission.BoseGases.abox n ℓ, Ma x) = 0 := by
    have := mainWord_fibre_offdiag (ℓ := ℓ) (d := d) (s := s) (εT := εT) hℓ j hΦ hS hT hjS hjT hST
    simpa only [hMadef] using this
  have hNz : (∫ x in Submission.BoseGases.abox n ℓ, N x) = 0 := by
    have := neuWord_fibre_offdiag (ℓ := ℓ) (d := d) (εT := εT) hℓ j hΦ hS hT hjS hjT hST
    simpa only [hNdef] using this
  -- the pointwise splitting of the integrand
  have hpoint : (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n j
            (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
          - Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n j
            (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)))
      = fun x => (G x + M x) + (Ma x + N x) := by
    funext x
    simp only [hGdef, hMdef, hMadef, hNdef, Pi.add_apply, Work.BoseKinLoc.fibre]
    rw [Work.BoseKinLoc.fsT_eq_sum, Work.BoseKinLoc.fsT_eq_sum]
    ring
  -- split the integral
  rw [hpoint]
  have e1 : (∫ x in Submission.BoseGases.abox n ℓ, (G x + M x))
      = (∫ x in Submission.BoseGases.abox n ℓ, G x)
        + ∫ x in Submission.BoseGases.abox n ℓ, M x :=
    MeasureTheory.integral_add hGint hMint
  have e2 : (∫ x in Submission.BoseGases.abox n ℓ, (Ma x + N x))
      = (∫ x in Submission.BoseGases.abox n ℓ, Ma x)
        + ∫ x in Submission.BoseGases.abox n ℓ, N x :=
    MeasureTheory.integral_add hMaint hNint
  have e3 : (∫ x in Submission.BoseGases.abox n ℓ, ((G x + M x) + (Ma x + N x)))
      = (∫ x in Submission.BoseGases.abox n ℓ, (G x + M x))
        + ∫ x in Submission.BoseGases.abox n ℓ, (Ma x + N x) :=
    MeasureTheory.integral_add (hGint.add hMint) (hMaint.add hNint)
  rw [e3, e1, e2, hGz, hMz, hMaz, hNz]
  ring

end Work.Analysis.BoseBand
