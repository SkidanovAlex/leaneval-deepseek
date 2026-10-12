import ChallengeDeps
import Submission.Work.BoseB1Cube.nomRow_all_of_windowRows
import Submission.Work.BoseB1Cube.perBoxFNomSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nomAssemble` — the two conjuncts of `perBoxFNom_holds` reduced

* **Conjunct 1 on in-box states**: from the two windowed per-size rows (`hGRP`, `hREM` — the
  delegated residuals `sbWordCube_ge_nomLinRowWindow` / `sbWordCube_ge_nomRowWindow`) one gets
  `PerBoxFNom v h R (1/40) C μ μ n Φ u` for every in-box `BoxState Φ` (`Work.BoseB1Cube.perBoxFNom_inBox`).
  Uses `Work.BoseB1Cube.nomRow_all_of_windowRows` (PROVED) and the in-box collapse
  `Work.BoseB1Cube.perBoxRow_eq_of_inBox` (PROVED).
* **Conjunct 2**: from the crude row on the slotted word at the doubled slot
  (`sbWordSlot v h (4μ) μ u Φ ≥ −K(16μ²a·χ + 4μa)‖Φ‖²` — the delegated `sbWordSlot_crude`, FS
  `eq:badset`) one gets the second conjunct of the target verbatim
  (`Work.BoseB1Cube.conj2_of_crude`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-- For an in-box `BoxState`, the frozen left-hand side `perBoxRow` *is* the nominal row `nomRow`. -/
theorem perBoxRow_eq_nomRow {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μp μ : ℝ} {n : ℕ}
    {Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))} {u : E3}
    (hloc : ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox n (sideAt μ (a v)))),
      (Φ : X n → ℝ) x ≠ 0 → ∀ i : Fin n, x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) :
    perBoxRow v h R c₁ C μp μ n Φ u = nomRow v h R c₁ C μp μ n u (Φ : X n → ℝ) := by
  rw [perBoxRow_eq_of_inBox (Φ := Φ) hloc, nomRow, nomESlot, nomW, nomV, nomChi, nomGamma]
  simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
  ring

/-- **Conjunct 1 on in-box states, from the two windowed rows.** -/
theorem perBoxFNom_inBox_of_windowRows {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {Cn ε₀ C : ℝ} (hCn : 2 ≤ Cn) (hε₀ : 0 < ε₀) (hC : 0 ≤ C)
    (hGRP : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n' : ℕ) (Ψ : X n' → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox n' (sideAt μ (a v)))), Ψ x ≠ 0 →
          ∀ i : Fin n', x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) →
        Cn * μ * nomV v μ u ≤ (n' : ℝ) → (n' : ℝ) ≤ 2 * Cn * μ * nomV v μ u →
        (1 / 18) * μ * ((n' : ℝ) / nomV v μ u) * nomW v h μ u
            * (∫ x in abox n' (sideAt μ (a v)), (Ψ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
    (hREM : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n' : ℕ) (Ψ : X n' → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox n' (sideAt μ (a v)))), Ψ x ≠ 0 →
          ∀ i : Fin n', x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) →
        (n' : ℝ) ≤ 2 * Cn * μ * nomV v μ u →
        ((1 / 4) * (((n' : ℝ) / nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
            * (∫ x in abox n' (sideAt μ (a v)), (Ψ x) ^ 2)
          - nomE v R C μ u * (∫ x in abox n' (sideAt μ (a v)), (Ψ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ) :
    ∃ ε₀' c₁ C' : ℝ, 0 < ε₀' ∧ 0 < c₁ ∧ 0 ≤ C' ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀' μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
          u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox n (sideAt μ (a v)))),
            (Φ : X n → ℝ) x ≠ 0 →
              ∀ i : Fin n, x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) →
          PerBoxFNom v h R c₁ C' μ μ n Φ u := by
  obtain ⟨ε₁, hε₁pos, hε₁le, hrow⟩ :=
    Work.BoseB1Cube.nomRow_all_of_windowRows (v := v) h hv hv1 hvrad hR hv_supp hav
      hCn hε₀ hC hGRP hREM
  refine ⟨ε₁, 1 / 40, C, hε₁pos, by norm_num, hC, ?_⟩
  intro μ hAdm n Φ u hu hloc
  change perBoxRow v h R (1 / 40) C μ μ n Φ u ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
  rw [perBoxRow_eq_nomRow (Φ := Φ) hloc]
  exact hrow μ hAdm n Φ u hu hloc

/-- **Conjunct 2, from the crude row at the doubled slot** (FS `eq:badset`). -/
theorem conj2_of_crude {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hcrude : ∃ ε₀ K : ℝ, 0 < ε₀ ∧ 0 ≤ K ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
          u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
          - K * (16 * μ ^ 2 * (_root_.BoseGases.a v) * nomChi v μ u
                  + 4 * μ * (_root_.BoseGases.a v))
              * (∫ x in abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2)
            ≤ sbWordSlot v h (4 * μ) μ u (Φ : X n → ℝ)) :
    ∃ ε₀ C' : ℝ, 0 < ε₀ ∧ 0 ≤ C' ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
          u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
          - (C' * (16 * μ ^ 2 * (_root_.BoseGases.a v)
                    * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
                  + 4 * μ * (_root_.BoseGases.a v)))
              * normB v μ n (Φ : X n → ℝ)
            ≤ sbWordSlot v h (4 * μ) μ u (Φ : X n → ℝ) := by
  obtain ⟨ε₀, K, hε₀, hK, hrow⟩ := hcrude
  refine ⟨ε₀, K, hε₀, hK, ?_⟩
  intro μ hAdm n Φ u hu
  have h := hrow μ hAdm n Φ u hu
  simp only [nomChi, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] at h ⊢
  linarith [h]

end Work.BoseB1Cube
