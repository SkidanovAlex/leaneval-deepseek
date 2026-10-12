import ChallengeDeps
import Submission.Work.BoseBogFS.CleanRowElem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.ZPCleanRow` — the assembly of `ZPCleanDeficitRow`

This module assembles FS's `I₁` estimate on the full dual lattice —
`ZPCleanDeficitRow`, the `hC` input of `ZPLatticeRowHolds_of_rows` — from the four rows of the
clean row (each filed separately, and each `C`-abstracted here so that the assembly is
independent of their proofs):

* `hsign` — `Work.BoseBogFS.cleanFun_nonneg_of_large`: `cleanFun` is nonnegative beyond an
  explicit momentum `kstar`, so a finite `S` containing the ball of radius `kstar` loses only
  nonnegative terms;
* `hsumm` — `Work.BoseBogFS.cleanFun_summable_integrable`: `Summable`/`Integrable`;
* `hriem` — `Work.BoseBogFS.cleanFun_tsum_le_integral`: the full-lattice sum is at most the
  integral plus `C·errBracket` (the crude one-sided Riemann comparison);
* `hcont` — `Work.BoseBogFS.integral_cleanFun_le`: FS `lem:BogIntegral` in the honest scaling,
  `½(2π)⁻³ℓ³∫cleanFun ≤ −4π·lhyC·ρ²aℓ³√(ρa³) + C·errBracket`.

`Work.BoseBogFS.cleanTerm_zero_nonneg` covers the label `0` (the only one the sign row does not
see) and `Work.BoseBogFS.finset_sum_le_tsum_of_nonneg_compl` performs the finite-sum/`tsum` step.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The clean row of `ZPLatticeRow`, from its four ingredient rows.**  The conclusion is
literally the `hC` hypothesis of `ZPLatticeRowHolds_of_rows`. -/
theorem zpCleanDeficit_of_rows
    (hsign : ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ},
      0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R → 0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
        Work.BoseBoxFock.CloseCondFS v μ ρ →
        ∃ kstar : ℝ, 0 ≤ kstar ∧ ∀ k : EuclideanSpace ℝ (Fin 3), kstar ≤ ‖k‖ →
          0 ≤ cleanFun v h ρ μ k)
    (hsumm : ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ},
      0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R → 0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
        Work.BoseBoxFock.CloseCondFS v μ ρ →
        Summable (fun n : Fin 3 → ℤ => cleanFun v h ρ μ (kAt v μ n))
        ∧ MeasureTheory.Integrable (fun k : EuclideanSpace ℝ (Fin 3) => cleanFun v h ρ μ k))
    (hriem : ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
      {R : ℝ}, 0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R → 0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
        Work.BoseBoxFock.CloseCondFS v μ ρ →
        Summable (fun n : Fin 3 → ℤ => cleanFun v h ρ μ (kAt v μ n)) →
        MeasureTheory.Integrable (fun k : EuclideanSpace ℝ (Fin 3) => cleanFun v h ρ μ k) →
          (∑' n : Fin 3 → ℤ, cleanFun v h ρ μ (kAt v μ n))
            ≤ ((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
                * (∫ k : EuclideanSpace ℝ (Fin 3), cleanFun v h ρ μ k)
              + C * errBracket v R μ)
    (hcont : ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
      {R : ℝ}, 0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R → 0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
        Work.BoseBoxFock.CloseCondFS v μ ρ →
        MeasureTheory.Integrable (fun k : EuclideanSpace ℝ (Fin 3) => cleanFun v h ρ μ k) →
          (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
              * (∫ k : EuclideanSpace ℝ (Fin 3), cleanFun v h ρ μ k))
            ≤ -(4 * Real.pi * Work.UBB.lhyC * ρ ^ 2 * (_root_.BoseGases.a v)
                  * (ell v μ) ^ 3 * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
              + C * errBracket v R μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ},
      0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R → 0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
        Work.BoseBoxFock.CloseCondFS v μ ρ →
        ∃ Lam : ℝ, 0 ≤ Lam ∧ ∀ S : Finset (Fin 3 → ℤ),
          (∀ n : Fin 3 → ℤ, n ≠ 0 → ‖kAt v μ n‖ ≤ Lam → n ∈ S) →
          ∑ n ∈ S, (1 / 2 : ℝ) * cleanTerm v h ρ μ n
            ≤ -(4 * Real.pi * Work.UBB.lhyC * ρ ^ 2 * (_root_.BoseGases.a v) * (ell v μ) ^ 3
                  * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
              + C * errBracket v R μ := by
  obtain ⟨C₃, hC₃0, hriem⟩ := hriem
  obtain ⟨C₄, hC₄0, hcont⟩ := hcont
  refine ⟨C₄ + C₃ / 2, by positivity, ?_⟩
  intro v h R hR hv hvrad hv_supp hav
  obtain ⟨εa, hεa, hsign⟩ := hsign hR hv hvrad hv_supp hav
  obtain ⟨εb, hεb, hsumm⟩ := hsumm hR hv hvrad hv_supp hav
  obtain ⟨εc, hεc, hriem⟩ := hriem hR hv hvrad hv_supp hav
  obtain ⟨εd, hεd, hcont⟩ := hcont hR hv hvrad hv_supp hav
  obtain ⟨εz, hεz, hzero⟩ := cleanTerm_zero_nonneg (v := v) (h := h) (R := R)
    hR hv hvrad hv_supp hav
  refine ⟨min (min (min εa εb) (min εc εd)) εz, lt_min (lt_min (lt_min hεa hεb)
    (lt_min hεc hεd)) hεz, ?_⟩
  intro μ hμ ρ hρ
  have ha : Work.BoseBoxFix.Adm v εa μ := adm_mono (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_left _ _))) hμ
  have hb : Work.BoseBoxFix.Adm v εb μ := adm_mono (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _))) hμ
  have hc : Work.BoseBoxFix.Adm v εc μ := adm_mono (le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _))) hμ
  have hd : Work.BoseBoxFix.Adm v εd μ := adm_mono (le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _))) hμ
  have hz : Work.BoseBoxFix.Adm v εz μ := adm_mono (min_le_right _ _) hμ
  obtain ⟨kstar, hkstar0, hsign⟩ := hsign μ ha ρ hρ
  obtain ⟨hsumm, hint⟩ := hsumm μ hb ρ hρ
  refine ⟨kstar, hkstar0, ?_⟩
  intro S hS
  have hsumm' : Summable (fun n : Fin 3 → ℤ => cleanTerm v h ρ μ n) :=
    hsumm.congr (fun n => (cleanTerm_eq_cleanFun v h ρ μ n).symm)
  have hkey2 : ∑ n ∈ S, cleanTerm v h ρ μ n = ∑ n ∈ S, cleanFun v h ρ μ (kAt v μ n) :=
    Finset.sum_congr rfl fun n _ => cleanTerm_eq_cleanFun v h ρ μ n
  have hmono : ∑' n : Fin 3 → ℤ, cleanTerm v h ρ μ n
      = ∑' n : Fin 3 → ℤ, cleanFun v h ρ μ (kAt v μ n) :=
    tsum_congr fun n => (cleanTerm_eq_cleanFun v h ρ μ n).symm
  have hstep : ∑ n ∈ S, cleanTerm v h ρ μ n ≤ ∑' n : Fin 3 → ℤ, cleanTerm v h ρ μ n := by
    refine finset_sum_le_tsum_of_nonneg_compl hsumm' (fun n hn => ?_)
    by_cases hn0 : n = 0
    · subst hn0
      exact hzero μ hz ρ hρ
    · have hkn : kstar ≤ ‖kAt v μ n‖ := by
        by_contra hlt
        push_neg at hlt
        exact hn (hS n hn0 hlt.le)
      rw [cleanTerm_eq_cleanFun]
      exact hsign (kAt v μ n) hkn
  rw [hkey2, hmono] at hstep
  have hkey : ∑ n ∈ S, (1 / 2 : ℝ) * cleanTerm v h ρ μ n
      = (1 / 2) * ∑ n ∈ S, cleanTerm v h ρ μ n :=
    (Finset.mul_sum S (fun n => cleanTerm v h ρ μ n) (1 / 2)).symm
  rw [hkey, hkey2]
  have h3 := hriem μ hc ρ hρ hsumm hint
  have h4 := hcont μ hd ρ hρ hint
  nlinarith [hstep, h3, h4, hC₃0, hC₄0]

end Work.BoseBogFS
