import ChallengeDeps
import Submission.Work.MGroupInput.FinalWiring
import Submission.Work.MGroupInput.d4_dl_bound_of_groups_windowCapped
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MGroupInput.D4BoundOfSimpleA2Two` — the DL bound from the proved `m`-arm

This is the chapter's capstone: the DL re-point's two-arm shape, assembled from

* the PROVED `m`-arm in its usable window
  (`Work.MGroupInput.mGroupWindowCapped8_of_simpleA2Two`:
  `MGroupWindowCapped (7 + E₁/μ) 9`) — whose hypotheses come from the two
  PROVED per-state branches (`perState_of_simpleA2Two7`, `perState_zeroCond`),
  which in turn come from the PROVED simple Bogoliubov payment
  (`diagW_simpleA2_two`) and sharp comparison (`wScaled_g0_sharp_ae`);
* the PROVED capped two-arm assembly
  (`Work.MGroupInput.d4_dl_bound_of_groups_windowCapped`).

The only remaining inputs are the *bundle-level* regime data (`hab`, `hgap`,
`hcorr`, `μs³ ≥ 40`, `hcgap`) — the analogue of `D4Regime`'s fields — and the
corpus's PROVED tight block bound at the remainder (`hblk`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.MGroupInput

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The DL two-arm shape from the proved `m`-arm** (`E₁` the `m`-arm's
count-linear constant, `E₂` its `n₊`-coefficient). -/
theorem d4_dl_bound_of_simpleA2Two {s μ R0 R K_B : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} {c₀ cgap Cb E₁ E₂ : ℝ}
    (hs : 0 < s) (hμ : 0 < μ) (hμβ : 1 ≤ μ * s ^ 3) (hav : 0 < a v)
    (hR0 : 0 < R0) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0) (hR0s : R0 ≤ s * chiR0) (hR0R : R0 ≤ R)
    (hKB : 0 < K_B) (hCb : 0 ≤ Cb) (hcgap0 : 0 ≤ cgap)
    (hint : Work.BlockBound4.DiagWKinIntegrable s c₀)
    (hμs10 : 10 ≤ μ * s ^ 3) (hcgap : 1 / (36 * s ^ 2) ≤ cgap)
    (hE₁ : 0 ≤ E₁) (hE₁μ : E₁ ≤ μ)
    (hA2 : SimpleA2Two E₁ E₂ s c₀ v h)
    (hab : ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
      Work.SmallBoxA0.totNCoeff s μ v + E₂ * (a v) * (((P : ℝ) + 1) / s ^ 3) ≤ cgap)
    (hgap : (μ * (a v) * s ^ 2) * (1600 + 1850 * chiSup ^ 2) ≤ 1)
    (hcorr : ∀ (P : ℕ) (Φ : X P → ℝ), 1 ≤ P → ContDiff ℝ ∞ Φ →
      (∫ x in abox P s, (Φ x) ^ 2) = 1 → (P : ℝ) / s ^ 3 ≤ 9 * μ → 0 < cS1 s Φ →
      2 * (s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord s h Φ
        ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ)
    (hblk : ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
      ((1 / 4 : ℝ) * ((P : ℝ) / s ^ 3 - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
        - Cb * μ ^ 2 * (a v) * s ^ 3 * Work.DLRepoint.d4GammaWith R s K_B μ v
        - Cb * μ * (a v)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap)
    (hzero : 0 ≤ Work.BlockBound4.diagWeBAt 0 s μ v h c₀ cgap)
    (N : ℕ) :
    ((1 / 18 : ℝ) * (((N : ℝ) / s ^ 3 - μ) ^ 2 / (1 + ((N : ℝ) / s ^ 3) / μ))
        - (1 / 2 : ℝ) * μ ^ 2) * (8 * π * (a v) * s ^ 3)
      - Cb * μ ^ 2 * (a v) * s ^ 3 * Work.DLRepoint.d4GammaWith R s K_B μ v
      - Cb * μ * (a v)
    ≤ Work.BlockBound4.diagWeBAt N s μ v h c₀ cgap := by
  have hμpos : (0 : ℝ) < μ := hμ
  have hCn : (2 : ℝ) ≤ 7 + E₁ / μ := by
    have : (0 : ℝ) ≤ E₁ / μ := div_nonneg hE₁ (le_of_lt hμpos)
    linarith
  have hCnCn' : (7 + E₁ / μ) + 1 ≤ 9 := by
    have h2 : E₁ / μ ≤ 1 := (div_le_one hμpos).mpr hE₁μ
    linarith
  have hM := mGroupWindowCapped8_of_simpleA2Two (E₁ := E₁) (E₂ := E₂) hR0 hv_nonneg hvrad
    hv_memL1 hv_supp h hR0s hav hs hμ hμs10 hcgap hE₁ hE₁μ hA2 hab hgap hcorr
  have hLin : MGroupLinearCapped (7 + E₁ / μ) 9 s μ v h c₀ cgap :=
    mGroupLinearCapped_of_mGroupWindowCapped hCn hμ hs (le_of_lt hav) hM
  exact d4_dl_bound_of_groups_windowCapped hs hμ hμβ (le_of_lt hav) hR0 hv_nonneg hvrad hv_memL1
    hv_supp hR0s hR0R hKB hCb hcgap0 hint hCn hCnCn' le_rfl hLin hblk hzero N

end Work.MGroupInput
