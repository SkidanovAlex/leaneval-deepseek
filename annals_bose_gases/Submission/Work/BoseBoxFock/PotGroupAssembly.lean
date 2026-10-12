import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PotGroupDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotGroupAssembly` — `FormW2Bpot` from its four row groups

`Work.BoseBoxFock.FormW2Bpot` (`Submission/Work/BoseBoxFock/rowSplitDefs.lean`) is assembled here
from the four group statements `PotContactChem`, `PotChiLin`, `PotPairRows`, `PotCubic`
(`Submission/Work/BoseBoxFock/PotGroupDefs.lean`) plus the integrability brick
`PotGroupsIntegrable`.

The steps are

1. **the pointwise splitting identity** `AVgen (potOnlyEnv E) = (G₀+G₁) + (G₂+G₃)`
   (`AVgen_potOnly_eq_potGroups`, PROVED — a regrouping of the summands of `AVgen`, using that the
   three kinetic rows vanish at `potOnlyEnv`);
2. **the integral split** `(∫ conj Θ·(Σᵢ Gᵢ Θ)).re = Σᵢ (∫ conj Θ·Gᵢ Θ).re`, from the
   integrability of the four integrands (`MeasureTheory.integral_add` + `Complex.add_re`);
3. **the error arithmetic**: since `errKafz v R μ C = C·(a fixed bracket)` is *linear* in `C`,
   the four per-group errors `(1/2)·errKafz(Cᵢ)·‖Φ‖²` sum **exactly** to
   `(1/2)·errKafz(ΣᵢCᵢ)·‖Φ‖²` (no sign hypothesis on the bracket is needed);
4. **the threshold arithmetic**: `Adm v ε₀ μ` is monotone in `ε₀`, so the four thresholds can be
   combined into `min`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseB4 Work.BoseDict

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- The real part of the integral of a pointwise sum: two integrable terms, in the *distributed*
form used by the assembly. -/
private lemma integral_re_add2 {Ψ : Submission.BoseGases.X n → ℂ}
    {b₁ b₂ : Submission.BoseGases.X n → ℂ}
    (h1 : MeasureTheory.Integrable (fun x => star (Ψ x) * b₁ x))
    (h2 : MeasureTheory.Integrable (fun x => star (Ψ x) * b₂ x)) :
    (∫ x, star (Ψ x) * (b₁ x + b₂ x)).re
      = (∫ x, star (Ψ x) * b₁ x).re + (∫ x, star (Ψ x) * b₂ x).re := by
  have hp : (fun x : Submission.BoseGases.X n => star (Ψ x) * (b₁ x + b₂ x))
      = fun x => star (Ψ x) * b₁ x + star (Ψ x) * b₂ x := by
    funext x
    ring
  rw [hp, MeasureTheory.integral_add h1 h2, Complex.add_re]

/-- The real part of the integral of a pointwise sum of four integrable terms (in the grouping
`(a₀+a₁) + (a₂+a₃)` in which the split of `FormW2Bpot`'s left-hand side is stated). -/
private lemma integral_re_add4 {Ψ : Submission.BoseGases.X n → ℂ}
    {a₀ a₁ a₂ a₃ : Submission.BoseGases.X n → ℂ}
    (h0 : MeasureTheory.Integrable (fun x => star (Ψ x) * a₀ x))
    (h1 : MeasureTheory.Integrable (fun x => star (Ψ x) * a₁ x))
    (h2 : MeasureTheory.Integrable (fun x => star (Ψ x) * a₂ x))
    (h3 : MeasureTheory.Integrable (fun x => star (Ψ x) * a₃ x)) :
    (∫ x, star (Ψ x) * ((a₀ x + a₁ x) + (a₂ x + a₃ x))).re
      = ((∫ x, star (Ψ x) * a₀ x).re + (∫ x, star (Ψ x) * a₁ x).re)
        + ((∫ x, star (Ψ x) * a₂ x).re + (∫ x, star (Ψ x) * a₃ x).re) := by
  have hA : MeasureTheory.Integrable (fun x => star (Ψ x) * (a₀ x + a₁ x)) :=
    (h0.add h1).congr (Filter.Eventually.of_forall (fun x => by
      rw [Pi.add_apply]; dsimp only; rw [mul_add]))
  have hB : MeasureTheory.Integrable (fun x => star (Ψ x) * (a₂ x + a₃ x)) :=
    (h2.add h3).congr (Filter.Eventually.of_forall (fun x => by
      rw [Pi.add_apply]; dsimp only; rw [mul_add]))
  rw [integral_re_add2 (b₁ := fun x => a₀ x + a₁ x) (b₂ := fun x => a₂ x + a₃ x) hA hB]
  rw [integral_re_add2 (b₁ := a₀) (b₂ := a₁) h0 h1,
    integral_re_add2 (b₁ := a₂) (b₂ := a₃) h2 h3]

/-- `errKafz v R μ` is additive in its constant, in the exact form used by the assembly. -/
private lemma errKafz_add (v : ℝ³ → ℝ) (R μ C₁ C₂ : ℝ) :
    Work.BoseFixR.errKafz v R μ (C₁ + C₂)
      = Work.BoseFixR.errKafz v R μ C₁ + Work.BoseFixR.errKafz v R μ C₂ := by
  simp only [Work.BoseFixR.errKafz]
  ring

/-- **`FormW2Bpot` from its four row groups.**  The four `∃ε C` statements are the content
(FS's `lem:2ndQuand` for the four groups of rows); this theorem is the assembly. -/
theorem FormW2Bpot_of_potGroups (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (Nmin : ℝ → ℕ)
    (h0 : ∃ (ε C : ℝ), 0 < ε ∧ 0 ≤ C ∧ PotContactChem v h fc fu R J Nmin ε C)
    (h1 : ∃ (ε C : ℝ), 0 < ε ∧ 0 ≤ C ∧ PotChiLin v h fc fu R J Nmin ε C)
    (h2 : ∃ (ε C : ℝ), 0 < ε ∧ 0 ≤ C ∧ PotPairRows v h fc fu R J Nmin ε C)
    (h3 : ∃ (ε C : ℝ), 0 < ε ∧ 0 ≤ C ∧ PotCubic v h fc fu R J Nmin ε C)
    (hint : ∀ {ε₀ : ℝ}, PotGroupsIntegrable v h hav fc fu R J Nmin ε₀) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ Work.BoseBoxFock.FormW2Bpot v h fc fu R J Nmin ε₀ C := by
  obtain ⟨ε₀, C₀, hε₀, hC₀, hG0⟩ := h0
  obtain ⟨ε₁, C₁, hε₁, hC₁, hG1⟩ := h1
  obtain ⟨ε₂, C₂, hε₂, hC₂, hG2⟩ := h2
  obtain ⟨ε₃, C₃, hε₃, hC₃, hG3⟩ := h3
  refine ⟨min (min (min ε₀ ε₁) ε₂) ε₃, C₀ + C₁ + C₂ + C₃,
    lt_min (lt_min (lt_min hε₀ hε₁) hε₂) hε₃, by linarith, ?_⟩
  intro HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1m h2b h3s h4o h5i h6t h7θ h8q h9t h10θ
    T_NH hT
  -- ## the four threshold instances of `Adm` (`Adm` is monotone in its threshold)
  have hε' : μ * (BoseGases.a v) ^ 3 ≤ min (min (min ε₀ ε₁) ε₂) ε₃ := hAdm.2.1
  have hA0 : Work.BoseBoxFix.Adm v ε₀ μ :=
    ⟨hAdm.1, le_trans hε' (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (min_le_left _ _))), hAdm.2.2⟩
  have hA1 : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hε' (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (min_le_right _ _))), hAdm.2.2⟩
  have hA2 : Work.BoseBoxFix.Adm v ε₂ μ :=
    ⟨hAdm.1, le_trans hε' (le_trans (min_le_left _ _) (min_le_right _ _)), hAdm.2.2⟩
  have hA3 : Work.BoseBoxFix.Adm v ε₃ μ :=
    ⟨hAdm.1, le_trans hε' (min_le_right _ _), hAdm.2.2⟩
  -- ## the four group inequalities, and the integrability of the four integrands
  have hg0 := hG0 HM hNmin μ hA0 hJ n Φ hn hnorm hlow hmom e h1m h2b h3s h4o h5i h6t h7θ h8q h9t
    h10θ T_NH hT
  have hg1 := hG1 HM hNmin μ hA1 hJ n Φ hn hnorm hlow hmom e h1m h2b h3s h4o h5i h6t h7θ h8q h9t
    h10θ T_NH hT
  have hg2 := hG2 HM hNmin μ hA2 hJ n Φ hn hnorm hlow hmom e h1m h2b h3s h4o h5i h6t h7θ h8q h9t
    h10θ T_NH hT
  have hg3 := hG3 HM hNmin μ hA3 hJ n Φ hn hnorm hlow hmom e h1m h2b h3s h4o h5i h6t h7θ h8q h9t
    h10θ T_NH hT
  obtain ⟨hi0, hi1, hi2, hi3⟩ := hint (ε₀ := ε₀) HM hNmin μ hA0 hJ n Φ hn hnorm hlow hmom e h1m h2b
    h3s h4o h5i h6t h7θ h8q h9t h10θ T_NH hT
  -- ## the two rewritings of the right-hand side
  have hwords : Work.BoseBoxFock.W2potB v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
      = Submission.BoseGases.q0word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
            (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h) 0)
            (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g2 v h) 0)
            (Φ : Submission.BoseGases.X n → ℝ)
          + Submission.BoseGases.q1word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
              (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0)
              (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g2 v h) 0)
              (Φ : Submission.BoseGases.X n → ℝ)
          + Submission.BoseGases.q2word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
              (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0)
              (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g2 v h) 0)
              (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseBoxFix.q3lowWord fc
              (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
              (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0)
              (Φ : Submission.BoseGases.X n → ℝ) := by
    simp only [W2potB]
  have herr : (1 / 2) * Work.BoseFixR.errKafz v R μ (C₀ + C₁ + C₂ + C₃)
        * Work.BoseBoxFix.normB v μ n Φ
      = ((1 / 2) * Work.BoseFixR.errKafz v R μ C₀ * Work.BoseBoxFix.normB v μ n Φ
          + (1 / 2) * Work.BoseFixR.errKafz v R μ C₁ * Work.BoseBoxFix.normB v μ n Φ)
        + ((1 / 2) * Work.BoseFixR.errKafz v R μ C₂ * Work.BoseBoxFix.normB v μ n Φ
          + (1 / 2) * Work.BoseFixR.errKafz v R μ C₃ * Work.BoseBoxFix.normB v μ n Φ) := by
    rw [errKafz_add, errKafz_add, errKafz_add]
    ring
  rw [hwords, herr]
  -- ## the pointwise splitting identity, the integral split, and the arithmetic
  have hsplit := AVgen_potOnly_eq_potGroups
    (B := fun T => boxSlotSum e T)
    (idop := (id : (Xn n → ℂ) → (Xn n → ℂ)))
    (f := (HM μ).f) (g := (HM μ).g) (T_NH := T_NH)
    (PHs := (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
    (E := (HonestBoxFam v h fc fu HM μ).E) (gHat0 := 8 * Real.pi * BoseGases.a v)
  have hstep : (∫ x : Submission.BoseGases.X n,
        star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
          * AVgen (fun T => boxSlotSum e T)
              (id : (Xn n → ℂ) → (Xn n → ℂ)) (HM μ).f (HM μ).g T_NH
              ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
              (potOnlyEnv (HonestBoxFam v h fc fu HM μ).E)
              (8 * Real.pi * BoseGases.a v)
              (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
      = ((∫ x : Submission.BoseGases.X n,
            star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
              * potContactChem (fun T => boxSlotSum e T)
                  (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                  (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
          + (∫ x : Submission.BoseGases.X n,
            star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
              * potChiLin (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                  (HonestBoxFam v h fc fu HM μ).E
                  (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re)
        + ((∫ x : Submission.BoseGases.X n,
            star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
              * potPairRows (fun T => boxSlotSum e T) (HM μ).f
                  (HonestBoxFam v h fc fu HM μ).E
                  (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
          + (∫ x : Submission.BoseGases.X n,
            star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
              * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                  ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
                  (HonestBoxFam v h fc fu HM μ).E
                  (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re) := by
    rw [hsplit]
    simp only [Pi.add_apply]
    exact integral_re_add4 (n := n) hi0 hi1 hi2 hi3
  rw [hstep]
  linarith [hg0, hg1, hg2, hg3]

end Work.BoseBoxFock
