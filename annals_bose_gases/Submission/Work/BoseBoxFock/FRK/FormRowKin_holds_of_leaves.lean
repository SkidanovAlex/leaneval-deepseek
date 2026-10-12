import ChallengeDeps
import Submission.Work.BoseBoxFock.FRK.adm_kin_regime
import Submission.Work.BoseBoxFock.FRK.neuWord_nonneg_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.FormRowKin_holds_of_leaves` — the kinetic row assembled from its two
# analytic leaves and the dictionary

This module performs the **assembly** of the FRK route (`LEAD_DESIGN_formrowkin_v2.md` §3): from

* the **`τ̃` row** (R-τ, the `∃K` statement proved as `FRK.tauRow_window_of_valid_W3` once W3/W4 are
  supplied) — its `Kτ` is the reserve coefficient of the `cnPlus` slot;
* the **`η_H` row** (R-η, the `∃K` statement proved as `FRK.etaHRow_window_v2` once S1/W3/majorant
  are supplied) — its `Kη` is the reserve coefficient of the `n₊^H` slot;
* the **dictionary** D4 (`FRK.FormRowKin4_of_oneBody4`), which turns the one-body inequality
  `OBineq4` at the honest parameters into `FormRowKin4`;

we obtain `FormRowKin` at `C = 0`.

The only mathematics here is the *threshold bookkeeping*: `Adm v ε₀ μ` with `ε₀ = s₀^323` gives
`s = (μa³)^{1/323} ≤ s₀` (`FRK.adm_kin_regime`), and `s₀` is chosen at the outset so small that
`Kτ·s₀ ≤ b/20` and `Kη·s₀ ≤ 3` — exactly the two side conditions `hsb`, `hdb` of the proved
`FRK.oneBody_kinGroup_le4`.  Lean reads `paramsAt μ (a v)` as `fsParams (μ (a v)^3)`, so the `d⁴`
slot is covered by `eT·d⁴ ≤ s ≤ s₀`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- **The one-body inequality at the honest parameters.**  From the `τ̃` row and the `η_H` row
(with their constants `Kτ`, `Kη`) the one-body inequality `OBineq4` holds at the parameters
`(ℓ, s, d, eT, b, κ) = (sideAt μ (a v), ·s, ·d, ·eT, ·b, kappaHon v μ)` for every admissible `μ`,
every `N` and every smooth `ψ`. -/
theorem oneBody4_at_honest (v : E3 → ℝ) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (hτ : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ s d eT : ℝ}, 0 < ℓ → 0 < s → 0 < d → d ≤ 1 → 0 ≤ eT → eT ≤ 1 →
      ∀ (N : ℕ) (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
        ≤ Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ
          + K * s * (ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ)
    (hη : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ d κ : ℝ}, 0 < ℓ → 0 < d → d ≤ 1 → (d ^ 2 * ℓ)⁻¹ ≤ κ →
      ∀ (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
        ≤ 24 * Work.BoseKinLoc.momForm ℓ d 0 ψ
          + K * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (N : ℕ) (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      OBineq4 (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).b (kappaHon v μ) fu N ψ := by
  obtain ⟨Kτ, hKτ0, hτ'⟩ := hτ
  obtain ⟨Kη, hKη0, hη'⟩ := hη
  -- the diluteness threshold `s₀`, chosen so that both reserve side conditions hold
  set s₀ : ℝ := min 1 (min (Work.BoseBox.bValue / (20 * max Kτ 1)) (3 / max Kη 1)) with hs₀def
  have hs₀ : 0 < s₀ := by
    rw [hs₀def]
    exact lt_min one_pos (lt_min
      (div_pos (by norm_num [Work.BoseBox.bValue]) (by positivity))
      (div_pos (by norm_num) (by positivity)))
  have hs₀1 : s₀ ≤ 1 := by rw [hs₀def]; exact min_le_left _ _
  have hs₀_Kτ : Kτ * s₀ ≤ Work.BoseBox.bValue / 20 := by
    have h1 : s₀ ≤ Work.BoseBox.bValue / (20 * max Kτ 1) := by
      rw [hs₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : Kτ ≤ max Kτ 1 := le_max_left _ _
    have h3 : (0 : ℝ) ≤ Work.BoseBox.bValue / (20 * max Kτ 1) :=
      le_of_lt (div_pos (by norm_num [Work.BoseBox.bValue]) (by positivity))
    calc Kτ * s₀ ≤ (max Kτ 1) * (Work.BoseBox.bValue / (20 * max Kτ 1)) :=
          mul_le_mul h2 h1 (le_of_lt hs₀) (le_trans hKτ0 h2)
      _ = Work.BoseBox.bValue / 20 := by
          field_simp
  have hs₀_Kη : Kη * s₀ ≤ 3 := by
    have h1 : s₀ ≤ 3 / max Kη 1 := by
      rw [hs₀def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : Kη ≤ max Kη 1 := le_max_left _ _
    have h3 : (0 : ℝ) ≤ 3 / max Kη 1 := le_of_lt (div_pos (by norm_num) (by positivity))
    calc Kη * s₀ ≤ (max Kη 1) * (3 / max Kη 1) :=
          mul_le_mul h2 h1 (le_of_lt hs₀) (le_trans hKη0 h2)
      _ = 3 := by field_simp
  refine ⟨s₀ ^ 323, pow_pos hs₀ 323, ?_⟩
  intro μ hμ N ψ hψ
  have hgate := adm_kin_regime v hav hs₀ hs₀1 hμ
  dsimp only at hgate
  obtain ⟨hℓ, hs, hss₀, hd, hd1, heT, heT1, hed, hb, hκ⟩ := hgate
  have hb0 : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).b := by
    rw [hb]; norm_num [Work.BoseBox.bValue]
  have hsb : Kτ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s ≤
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 20 := by
    rw [hb]
    exact le_trans (mul_le_mul_of_nonneg_left hss₀ hKτ0) hs₀_Kτ
  have hdb : (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT * Kη *
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 4 ≤ 3 := by
    calc (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT * Kη *
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 4
        = Kη * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).eT *
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 4) := by ring
      _ ≤ Kη * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s :=
          mul_le_mul_of_nonneg_left hed hKη0
      _ ≤ Kη * s₀ := mul_le_mul_of_nonneg_left hss₀ hKη0
      _ ≤ 3 := hs₀_Kη
  exact oneBody_kinGroup_le4 hKτ0 hKη0 hτ' hη' hℓ hs hd hd1 heT heT1 hb0 hκ hsb hdb
    fu N ψ hψ (gapBare_nonneg _ _) (momForm_nonneg _ _ _)
    (neuWord_nonneg_general hℓ hd heT ψ hψ)

/-- **The kinetic row of the FRK route, assembled.**  From the `τ̃` row, the `η_H` row and the
dictionary D4 (`∀ ε₀, OBineq4-at-honest-parameters ⟹ FormRowKin4 … ε₀ 0`), the frozen
`FormRowKin` holds with an explicit threshold and constant `C = 0`. -/
theorem FormRowKin_holds_of_leaves (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ) (Nmin : ℝ → ℕ)
    (hτ : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ s d eT : ℝ}, 0 < ℓ → 0 < s → 0 < d → d ≤ 1 → 0 ≤ eT → eT ≤ 1 →
      ∀ (N : ℕ) (ψ : Ω → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
        ≤ Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ
          + K * s * (ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ)
    (hη : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ d κ : ℝ}, 0 < ℓ → 0 < d → d ≤ 1 → (d ^ 2 * ℓ)⁻¹ ≤ κ →
      ∀ (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (ψ : Ω → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
        ≤ 24 * Work.BoseKinLoc.momForm ℓ d 0 ψ
          + K * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ)
    (hD4 : ∀ (ε₀ : ℝ), (∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (N : ℕ) (ψ : Ω → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
        OBineq4 (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).b (kappaHon v μ) fu N ψ) →
      FormRowKin4 v h fc fu R J Nmin ε₀ 0) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ Work.BoseBoxFock.FormRowKin v h fc fu R J Nmin ε₀ C := by
  obtain ⟨ε₀, hε₀, hOB⟩ := oneBody4_at_honest v hav fc fu hτ hη
  exact ⟨ε₀, 0, hε₀, le_refl 0, FormRowKin_of_FormRowKin4 hav (hD4 ε₀ hOB)⟩

end Work.BoseBoxFock.FRK
