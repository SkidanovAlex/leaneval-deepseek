import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.assembly_of_row
import Submission.Work.BoseBoxFock.bf3a
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.RowB` reduces to FS `prop:Hamilton2ndQuant`'s **row table**

`Work.BoseBoxFock.RowB` (the box-side row bound consumed by
`Work.BoseBoxFock.box_to_model_of_row`) is equivalent to the conjunction of

* `Work.BoseBoxFock.FormW2B` (defined here): the model's first-quantised form at `boxRestrict Φ`
  is dominated by FS's first-quantised word `W2B` plus `errKafz·normB` — the *row table* of FS
  `prop:Hamilton2ndQuant` (its kinetic row is the aliasing row, see the docstring of `FormW2B`); and
* `Work.BoseBoxFock.bf3a` (**PROVED**): `W2B ≤ wordB + C·errB·normB`,

with the errors absorbed by `Work.BoseBoxFock.err_arith` (**PROVED**), which supplies
`errB ≤ errKafz v R μ 1`.  `Work.BoseBoxFock.RowB_of_formW2B` is the reduction, so that the
*only* remaining mathematical input of `Work.BoseBoxFock.box_to_model` is `FormW2B`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-- **The box-side *row table***: the model's first-quantised form at `boxRestrict Φ` is dominated
by FS's first-quantised second-quantised word `W2B` plus `errKafz·normB`.

`Work.BoseBoxFock.W2B` is FS `H_Λ^2nd` written row by row (`kinTauB` = the *continuum* `τ̃`-symbol
kinetic word, then the gap, gapH, `q0word`, `q1word`, `q2word`, `q3lowWord` rows), while
`AVgen (boxSlotSum e) id f g T_NH PHs E (8π a v)` is the same expression tree with every row
realised as a first-quantised *slot* form.  Row by row the two agree — except the kinetic row,
where the model's form is the **lattice** symbol `Σ_k τ̃(k)⟨a_k†a_k⟩` and `W2B`'s is the
**continuum** `τ̃(√−Δ)` slot form; that single comparison is the aliasing (sampling) row of
`Work.BoseBoxFock.kinRow_lattice_tauPhi` / `Work.BoseBoxFock.tauPhi_row_closedBall`
(`Submission/Work/BoseBoxFock/FINDING_sharpShiftRow.md`). -/
noncomputable def FormW2B (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        ∀ (e : Fin (HM μ).m → Ω → ℂ),
          (∀ l, Measurable (e l)) →
          (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) →
          (∀ l, Function.support (e l)
            ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) →
          (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
            = (if l = l' then (1 : ℂ) else 0)) →
          (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) →
          (∀ l, MeasureTheory.MemLp (e l) ⊤) →
          (∃ c : ℂ, (starRingEnd ℂ) c * c
              = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
            e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
                (Work.BoseBox.sideAt μ (BoseGases.a v)) x) →
          (∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).f k l : ℝ) : ℂ)) →
          (∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).g s l : ℝ) : ℂ)) →
          (∫ z : Ω, star (e 0 z)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
            = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) →
          ∀ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
                = Work.BoseB4.dGamma (HM μ).m T_NH →
            (∫ x : Submission.BoseGases.X n,
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                      (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                      (HM μ).f (HM μ).g T_NH
                      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (8 * Real.pi * BoseGases.a v)
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Work.BoseBoxFock.W2B v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
                  + Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ


/-- **The reduction**: the row table `FormW2B` plus the *proved* `bf3a` and `err_arith` give
`Work.BoseBoxFock.RowB`. -/
theorem RowB_of_formW2B (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (Nmin : ℝ → ℕ)
    (hF : ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ FormW2B v h fc fu R J Nmin ε₀ C) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ RowB v h fc fu R J Nmin ε₀ C := by
  obtain ⟨ε₁, C₁, hε₁, hC₁, hF'⟩ := hF
  obtain ⟨C₂, ε₂, hC₂, hε₂, hbf⟩ := bf3a v h hv hv1 hvrad hR hv_supp hav fc hB3
  obtain ⟨ε₃, C₃, hε₃, hC₃, herr⟩ := err_arith hav hR
  refine ⟨min ε₁ (min ε₂ ε₃), C₁ + C₂ * C₃, lt_min hε₁ (lt_min hε₂ hε₃), ?_, ?_⟩
  · nlinarith [mul_nonneg hC₂ (le_of_lt hC₃), hC₁]
  intro HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 T_NH hT
  have hε : μ * (BoseGases.a v) ^ 3 ≤ min ε₁ (min ε₂ ε₃) := hAdm.2.1
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hε (min_le_left _ _), hAdm.2.2⟩
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    ⟨hAdm.1, le_trans hε (le_trans (min_le_right _ _) (min_le_left _ _)), hAdm.2.2⟩
  have hAdm₃ : Work.BoseBoxFix.Adm v ε₃ μ :=
    ⟨hAdm.1, le_trans hε (le_trans (min_le_right _ _) (min_le_right _ _)), hAdm.2.2⟩
  have hrow := hF' HM hNmin μ hAdm₁ hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    T_NH hT
  have hbfa := hbf μ hAdm₂ n Φ hn
  obtain ⟨herrB, -⟩ := herr μ hAdm₃ J hJ
  have hlin2 : Work.BoseFixR.errKafz v R μ C₁ + Work.BoseFixR.errKafz v R μ (C₂ * C₃)
      = Work.BoseFixR.errKafz v R μ (C₁ + C₂ * C₃) := by
    simp only [Work.BoseFixR.errKafz]; ring
  have hnorm0 : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := le_of_lt hnorm
  -- `massR` of the box restriction is the box norm
  have hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBox.sideAt_eq_rpow hav hAdm.1]
    exact mul_pos hav (Real.rpow_pos_of_pos (mul_pos hAdm.1 (pow_pos hav 3)) _)
  obtain ⟨-, -, -, -, hmassC⟩ := Work.BoseBoxFock.boxRestrictState hℓ Φ
  have hFold : (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)
      * (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v))).indicator
          (fun _ => (1 : ℝ)) x)
      = boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ := rfl
  have hmass : Work.BoseBoxFock.massR
      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ)
      = Work.BoseBoxFix.normB v μ n Φ := by
    rw [← hFold, hmassC]
    rfl
  have hstep : C₂ * Work.BoseBoxFock.errB v R μ
      ≤ Work.BoseFixR.errKafz v R μ (C₂ * C₃) := by
    have h1' : C₂ * Work.BoseBoxFock.errB v R μ
        ≤ C₂ * Work.BoseFixR.errKafz v R μ C₃ :=
      mul_le_mul_of_nonneg_left herrB hC₂
    have h2' : C₂ * Work.BoseFixR.errKafz v R μ C₃
        = Work.BoseFixR.errKafz v R μ (C₂ * C₃) := by
      simp only [Work.BoseFixR.errKafz]; ring
    rwa [h2'] at h1'
  have harith : (Work.BoseBoxFix.wordB v h μ n Φ
        + Work.BoseFixR.errKafz v R μ (C₂ * C₃) * Work.BoseBoxFix.normB v μ n Φ)
        + Work.BoseFixR.errKafz v R μ C₁ * Work.BoseBoxFix.normB v μ n Φ
      = (Work.BoseBoxFix.wordB v h μ n Φ / Work.BoseBoxFix.normB v μ n Φ
          + Work.BoseFixR.errKafz v R μ (C₁ + C₂ * C₃))
          * Work.BoseBoxFix.normB v μ n Φ := by
    rw [← hlin2]
    field_simp [ne_of_gt hnorm]
    ring
  calc (∫ x : Submission.BoseGases.X n,
        star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
          * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
              (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
              (HM μ).f (HM μ).g T_NH
              ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
              (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
      ≤ Work.BoseBoxFock.W2B v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseFixR.errKafz v R μ C₁ * Work.BoseBoxFix.normB v μ n Φ := hrow
    _ ≤ (Work.BoseBoxFix.wordB v h μ n Φ
          + C₂ * Work.BoseBoxFock.errB v R μ * Work.BoseBoxFix.normB v μ n Φ)
          + Work.BoseFixR.errKafz v R μ C₁ * Work.BoseBoxFix.normB v μ n Φ := by
        linarith [hbfa]
    _ ≤ (Work.BoseBoxFix.wordB v h μ n Φ
          + Work.BoseFixR.errKafz v R μ (C₂ * C₃) * Work.BoseBoxFix.normB v μ n Φ)
          + Work.BoseFixR.errKafz v R μ C₁ * Work.BoseBoxFix.normB v μ n Φ := by
        have := mul_le_mul_of_nonneg_right hstep hnorm0
        linarith
    _ = (Work.BoseBoxFix.wordB v h μ n Φ / Work.BoseBoxFix.normB v μ n Φ
          + Work.BoseFixR.errKafz v R μ (C₁ + C₂ * C₃))
          * Work.BoseBoxFock.massR
              (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) := by
        rw [hmass]
        exact harith

end Work.BoseBoxFock
