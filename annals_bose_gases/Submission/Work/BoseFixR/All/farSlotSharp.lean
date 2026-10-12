import ChallengeDeps
import Submission.Work.BoseFixR.All.FarBogPair
import Submission.Work.BoseFixR.All.FarEnvPos
import Submission.Work.BoseFixR.All.epsFar_le_inv_eight
import Submission.Work.BoseFixR.BogZeroPointSharp32
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/farSlotSharp.lean` — the *lossless* far-leg zero-point slot

`Work.BoseFixR.farRadSlot` bounds the radial half `Σ_k ½𝒵_k` of FS §9's zero point by
converting the `ε`-split diagonal back to `τ` **losing a factor ≈ 2.4** (`FarZSumHalf`'s
`ρ²(1/4+32√ε)ΣŴ₁²/𝒜₁` is compared with `τ` and the factor `(1/4+32√ε)(25/(8A₀))` is
dropped under `≤ 1`).  This module proves the **lossless** version, which is what the far
leg actually needs (`NOTE_FarLegDesign.md` §36–§37): with the sharp per-mode bound

  `bogZeroPoint (A1+B) B ≤ (1/2 + 32√ε)·B²/A1`   (`0 ≤ A1`, `|B| ≤ 16π√ε A1`)

(`Work.BoseFixR.BogZeroPointSharp32`, `Submission/Work/BoseFixR/BogZeroPointSharp32.lean`)
the sum keeps its **exact** `ρ²/4` coefficient:

  `Σ_{k∈excited} ½𝒵_k ≤ (ρ²/4)(1+64√ε)·Σ_{k∈excited} Ŵ₁(k)²/τ̃(k)`,

where `𝒵_k = (KzEnvAt (farEnv E v μ ρ) ρ).A k − √((…)² − (…)²)` and
`τ̃ = (farEnv E v μ ρ).tau` is the ε-split diagonal `(1−ε)τ_k + ρε^{−1/2}a`.  No threshold
loss, no `(1−ε_T)` factor, and the `½` is *recovered*.

Everything reduces to the pointwise statement: with `A1 = τ̃_k` one has
`|ℬ_k| = ρ|Ŵ₁(k)| ≤ ρ·16πa ≤ 16π√ε·A1` (because `√ε·ε^{−1/2} = 1` and `A1 ≥ ρε^{−1/2}a`), and
`½·(1/2+32√ε)·ρ²Ŵ₁²/A1 = (ρ²/4)(1+64√ε)·Ŵ₁²/τ̃` **exactly**.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseFixR.All

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The slot -/

theorem farSlotSharp {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ))) (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hW1 : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * BoseGases.a v)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hfar : Work.BoseBoxFock.FarCondFS v μ ρ) :
    (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (1 / 2) * Work.BoseB6.bogZeroPoint
          ((Work.BoseFixR.KzEnvAt (Work.BoseFixR.All.farEnv
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k)
          ((Work.BoseFixR.KzEnvAt (Work.BoseFixR.All.farEnv
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k))
      ≤ (ρ ^ 2 / 4) * (1 + 64 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
          * (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
              ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k) ^ 2
                / ((Work.BoseFixR.All.farEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ ρ).tau k)) := by
  classical
  set E := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E with hE
  set s := Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N) with hs
  have hμ : 0 < μ := hAdm.1
  have hℓpos : 0 < Work.BoseFixR.ell v μ := by
    rw [Work.BoseFixR.ell]; exact Work.BoseBox.sideAt_pos hμ hav
  have hεpos : 0 < Work.BoseFixR.All.epsFar v μ ρ := by
    rw [Work.BoseFixR.All.epsFar]
    exact Real.sqrt_pos_of_pos (div_pos (Work.BoseBox.bigM_pos_of_params hμ hav)
      (mul_pos (by linarith) (pow_pos hℓpos 3)))
  have hεle : Work.BoseFixR.All.epsFar v μ ρ ≤ 1 / 10 ^ 8 :=
    Work.BoseFixR.All.FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav hρ hfar
  have hτ : ∀ k : Work.BoseBoxFock.Lab (HM μ).N, 0 ≤ E.tau k :=
    fun k => Work.BoseFixR.All.farEnvPos_tau_nonneg _ hview k
  have hsqrtmul : Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ)
      * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hεpos]
    norm_num
  have hper : ∀ k ∈ s, (1 / 2) * Work.BoseB6.bogZeroPoint
        ((Work.BoseFixR.KzEnvAt (Work.BoseFixR.All.farEnv E v μ ρ) ρ).A k)
        ((Work.BoseFixR.KzEnvAt (Work.BoseFixR.All.farEnv E v μ ρ) ρ).B k)
      ≤ (ρ ^ 2 / 4) * (1 + 64 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
          * (E.W1 k ^ 2 / (Work.BoseFixR.All.farEnv E v μ ρ).tau k) := by
    intro k hk
    set A1 := (1 - Work.BoseFixR.All.epsFar v μ ρ) * E.tau k
      + ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v with hA1
    have hAeq : (Work.BoseFixR.KzEnvAt (Work.BoseFixR.All.farEnv E v μ ρ) ρ).A k
        = A1 + ρ * E.W1 k := by
      rw [hA1]; rfl
    have hBeq : (Work.BoseFixR.KzEnvAt (Work.BoseFixR.All.farEnv E v μ ρ) ρ).B k
        = ρ * E.W1 k := rfl
    have hτeq : (Work.BoseFixR.All.farEnv E v μ ρ).tau k = A1 := rfl
    have hA1nn : 0 ≤ A1 := by
      rw [hA1]
      have h1 : 0 ≤ (1 - Work.BoseFixR.All.epsFar v μ ρ) * E.tau k :=
        mul_nonneg (by linarith) (hτ k)
      have h2 : 0 ≤ ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v :=
        mul_nonneg (mul_nonneg hρ (Real.rpow_pos_of_pos hεpos _).le) hav.le
      linarith
    have hBnd : |ρ * E.W1 k|
        ≤ 16 * Real.pi * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ) * A1 := by
      have h1 : |ρ * E.W1 k| ≤ ρ * (16 * Real.pi * BoseGases.a v) := by
        rw [abs_mul, abs_of_nonneg hρ]
        exact mul_le_mul_of_nonneg_left (hW1 k) hρ
      have h2 : ρ * (16 * Real.pi * BoseGases.a v)
          ≤ 16 * Real.pi * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ)
              * (ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v) := by
        rw [show 16 * Real.pi * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ)
              * (ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v)
            = ρ * (16 * Real.pi * BoseGases.a v)
              * (Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ)
                  * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ))) by ring,
          hsqrtmul, mul_one]
      have h3 : 16 * Real.pi * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ)
            * (ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v)
          ≤ 16 * Real.pi * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ) * A1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hA1]
        have h1 : 0 ≤ (1 - Work.BoseFixR.All.epsFar v μ ρ) * E.tau k :=
          mul_nonneg (by linarith) (hτ k)
        linarith
      linarith
    have hZ := BogZeroPointSharp32 hA1nn hεpos.le hεle hBnd
    rw [hAeq, hBeq, hτeq]
    refine le_trans (mul_le_mul_of_nonneg_left hZ (by norm_num : (0 : ℝ) ≤ 1 / 2)) (le_of_eq ?_)
    ring
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.mul_sum]

end Work.BoseFixR.All
