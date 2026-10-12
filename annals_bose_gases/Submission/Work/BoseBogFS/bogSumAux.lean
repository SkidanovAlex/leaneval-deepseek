import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.bogCellBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogSumAux` — the shared vocabulary of the lattice sums of the clean row

This module carries the pieces that are common to the three region sums
(`bogS1`/`bogS2`/`bogS3`) and to the final assembly of
`Work.BoseBogFS.cleanFun_tsum_le_integral`:

* the **gated** majorants `bogS1`/`bogS2`/`bogS3` (`bogMajA`/`bogMajB`/`bogMajC` truncated below
  at `0` and gated by the region); they are the summable objects,
* `bogMaj_le_gated` — the pointwise domination of `bogMaj` by the gated pieces (no side
  conditions),
* the **decaying** `β`-bound `bogBeta_le_decay` (the region B/C sums are impossible without it),
* `bogVmaxt_le_vs`,
* the exact normalisations `bogC1_div_mesh` and `bogC2_div_mesh` (`c₁/δ = 1/(4πs)`,
  `c₂/δ = 1/(4πds)`) — the bridge between the *radius* description of the regions and the
  *lattice* sums,
* `bogRLot_eq`/`bogRHit_eq`/`bogRLot_ge_eighth`.

Everything is in the scaled variables `t = k/√(ρ a v)`; see
`Submission/Work/BoseBogFS/FINDING_cleanFun_tsum_session20.md`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The gated majorants (the summable objects) -/

/-- Region A, gated and truncated below at `0`. -/
def bogS1 (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  if bogRHit v ρ μ n ≤ bogC1 v ρ μ then max 0 (bogMajA v h R ρ μ n) else 0

/-- Region B, gated and truncated below at `0`. -/
def bogS2 (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  if bogRHit v ρ μ n ≤ bogBigThr v R ρ μ then max 0 (bogMajB v h R ρ μ n) else 0

/-- Region C, gated and truncated below at `0`. -/
def bogS3 (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  if bogBigThr v R ρ μ < bogRHit v ρ μ n then max 0 (bogMajC v h R ρ μ n) else 0

lemma bogS1_nonneg (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) :
    0 ≤ bogS1 v h R ρ μ n := by
  by_cases hA : bogRHit v ρ μ n ≤ bogC1 v ρ μ
  · simp only [bogS1, if_pos hA]; exact le_max_left _ _
  · simp only [bogS1, if_neg hA]; exact le_refl 0

lemma bogS2_nonneg (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) :
    0 ≤ bogS2 v h R ρ μ n := by
  by_cases hA : bogRHit v ρ μ n ≤ bogBigThr v R ρ μ
  · simp only [bogS2, if_pos hA]; exact le_max_left _ _
  · simp only [bogS2, if_neg hA]; exact le_refl 0

lemma bogS3_nonneg (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) :
    0 ≤ bogS3 v h R ρ μ n := by
  by_cases hA : bogBigThr v R ρ μ < bogRHit v ρ μ n
  · simp only [bogS3, if_pos hA]; exact le_max_left _ _
  · simp only [bogS3, if_neg hA]; exact le_refl 0

/-- **`bogMaj` is dominated by the three gated pieces.**  The only input is the case structure of
`bogMaj` and `max 0 x ≥ x`; **no** side condition is needed. -/
theorem bogMaj_le_gated (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) :
    bogMaj v h R ρ μ n ≤ bogS1 v h R ρ μ n + bogS2 v h R ρ μ n + bogS3 v h R ρ μ n := by
  rw [bogMaj]
  by_cases h0 : n = 0
  · rw [if_pos h0]
    have := bogS1_nonneg v h R ρ μ n
    have := bogS2_nonneg v h R ρ μ n
    have := bogS3_nonneg v h R ρ μ n
    linarith
  · rw [if_neg h0]
    by_cases hA : bogRHit v ρ μ n ≤ bogC1 v ρ μ
    · rw [if_pos hA, bogS1, if_pos hA]
      have h1 : bogMajA v h R ρ μ n ≤ max 0 (bogMajA v h R ρ μ n) := le_max_right _ _
      have h2 := bogS2_nonneg v h R ρ μ n
      have h3 := bogS3_nonneg v h R ρ μ n
      linarith
    · rw [if_neg hA]
      by_cases hB : bogRHit v ρ μ n ≤ bogBigThr v R ρ μ
      · rw [if_pos hB, bogS2, if_pos hB]
        have h1 : bogMajB v h R ρ μ n ≤ max 0 (bogMajB v h R ρ μ n) := le_max_right _ _
        have h2 := bogS1_nonneg v h R ρ μ n
        have h3 := bogS3_nonneg v h R ρ μ n
        linarith
      · rw [if_neg hB, bogS3, if_pos (lt_of_not_ge hB)]
        have h1 : bogMajC v h R ρ μ n ≤ max 0 (bogMajC v h R ρ μ n) := le_max_right _ _
        have h2 := bogS1_nonneg v h R ρ μ n
        have h3 := bogS2_nonneg v h R ρ μ n
        linarith

/-! ## 2. The decaying `β`-bound -/

/-- **The decaying form of `bogBeta_le`**: `|β_s t| ≤ bogBs/(1+√(ρ a v)‖t‖)`.
Region B/C sums are impossible without it. -/
theorem bogBeta_le_decay {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) (t : E3) :
    |betaSc v h ρ μ t| ≤ bogBs v R / (1 + Real.sqrt (ρ * a v) * ‖t‖) := by
  have hspec := bogKB_spec (h := h) hR hρ hav hv hvrad hv_supp hRℓ t
  have hB : bogKB * (1 + R) ^ 3 / a v ≤ bogBs v R := le_max_right _ _
  have hden : (0 : ℝ) < 1 + Real.sqrt (ρ * a v) * ‖t‖ := by positivity
  have hEq : bogKB * (1 + R) ^ 3 / (a v * (1 + Real.sqrt (ρ * a v) * ‖t‖))
      = (bogKB * (1 + R) ^ 3 / a v) / (1 + Real.sqrt (ρ * a v) * ‖t‖) := by
    rw [div_div]
  rw [hEq] at hspec
  exact le_trans hspec (div_le_div_of_nonneg_right hB hden.le)

/-- The cell `β`-oscillation is at most the crude oscillation bound. -/
lemma bogOm_le_oscM {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hR : 0 ≤ R) (hρ : 0 < ρ) (hav : 0 < a v) (hδ : 0 < bogMesh v ρ μ) (hn : n ≠ 0) :
    bogOm v h R ρ μ n ≤ bogOscM v R ρ μ := by
  rw [bogOm, bogOscK, bogOscM]
  have hrlo : 0 ≤ bogRLot v ρ μ n := (bogRLo_pos hδ hn).le
  have hnum : 0 ≤ bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ :=
    mul_nonneg (mul_nonneg (mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3))
      (Real.sqrt_nonneg _)) (bogHalf_pos hδ).le
  have hden : 1 ≤ 1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ n := by
    have := mul_nonneg (Real.sqrt_nonneg (ρ * a v)) hrlo
    linarith
  exact le_trans (div_le_self hnum hden) (le_refl _)

/-- The per-cell `V` is at most `bogVs`. -/
theorem bogVmaxt_le_vs {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    (hδ : 0 < bogMesh v ρ μ) (hn : n ≠ 0) :
    bogVmaxt v h R ρ μ n ≤ bogVs v R ρ μ := by
  have hβ := bogBeta_le (h := h) (t := tSca v ρ μ n) hR hρ hav hv hvrad hv_supp hRℓ
  have hβa := abs_le.mp hβ
  have hom0 : 0 ≤ bogOm v h R ρ μ n := bogOm_nonneg (h := h) hρ hav hR.le hδ hn
  have homle : bogOm v h R ρ μ n ≤ bogOscM v R ρ μ :=
    bogOm_le_oscM (v := v) (h := h) (R := R) (ρ := ρ) (μ := μ) (n := n) hR.le hρ hav hδ hn
  have hlo : |bogVlot v h R ρ μ n| ≤ bogBs v R + bogOm v h R ρ μ n := by
    rw [bogVlot, bogVNt, abs_le]
    exact ⟨by linarith only [hβa.1], by linarith only [hβa.2, hom0]⟩
  have hhi : |bogVhit v h R ρ μ n| ≤ bogBs v R + bogOm v h R ρ μ n := by
    rw [bogVhit, bogVNt, abs_le]
    exact ⟨by linarith only [hβa.1, hom0], by linarith only [hβa.2]⟩
  have hgoal : bogBs v R + bogOm v h R ρ μ n ≤ bogVs v R ρ μ := by
    rw [bogVs]
    have := le_max_right (0 : ℝ) (bogOscM v R ρ μ)
    linarith only [homle, this]
  rw [bogVmaxt]
  exact max_le (le_trans hlo hgoal) (le_trans hhi hgoal)

/-! ## 3. The exact normalisations of the region thresholds -/

/-- **`c₁/δ = 1/(4π s)`** — the region-A threshold in lattice units. -/
theorem bogC1_div_mesh {v : E3 → ℝ} {ρ μ : ℝ} (hρ : 0 < ρ) (hav : 0 < a v)
    (hℓ : 0 < ell v μ) (hs : 0 < (paramsAt μ (a v)).s) :
    bogC1 v ρ μ / bogMesh v ρ μ = (4 * Real.pi * (paramsAt μ (a v)).s)⁻¹ := by
  have hP : 0 < ρ * a v := mul_pos hρ hav
  have hsq : 0 < Real.sqrt (ρ * a v) := Real.sqrt_pos.mpr hP
  rw [bogC1, bogMesh]
  field_simp
  ring

/-- **`c₂/δ = 1/(4π d s)`**. -/
theorem bogC2_div_mesh {v : E3 → ℝ} {ρ μ : ℝ} (hρ : 0 < ρ) (hav : 0 < a v)
    (hℓ : 0 < ell v μ) (hs : 0 < (paramsAt μ (a v)).s) (hd : 0 < (paramsAt μ (a v)).d) :
    bogC2 v ρ μ / bogMesh v ρ μ
      = (4 * Real.pi * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s)⁻¹ := by
  have hP : 0 < ρ * a v := mul_pos hρ hav
  have hsq : 0 < Real.sqrt (ρ * a v) := Real.sqrt_pos.mpr hP
  rw [bogC2, bogMesh]
  field_simp
  ring

/-! ## 4. The cell radii in lattice units -/

lemma bogRLot_eq (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) (hδ : 0 ≤ bogMesh v ρ μ) :
    bogRLot v ρ μ n = bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ - Real.sqrt 3 / 2) := by
  rw [bogRLot, bogHalf, norm_tSca, norm_lpt_eq (bogMesh v ρ μ) hδ n]
  ring

lemma bogRHit_eq (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) (hδ : 0 ≤ bogMesh v ρ μ) :
    bogRHit v ρ μ n = bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ + Real.sqrt 3 / 2) := by
  rw [bogRHit, bogHalf, norm_tSca, norm_lpt_eq (bogMesh v ρ μ) hδ n]
  ring

/-- On a nonzero cell the lower radius is at least `δ/8`. -/
lemma bogRLot_ge_eighth {v : E3 → ℝ} {ρ μ : ℝ} (hδ : 0 < bogMesh v ρ μ) {n : Fin 3 → ℤ}
    (hn : n ≠ 0) : bogMesh v ρ μ / 8 ≤ bogRLot v ρ μ n := by
  rw [bogRLot_eq v ρ μ n hδ.le]
  have h1 : 1 ≤ ‖lpt (1 : ℝ) n‖ := one_le_norm_lpt_one hn
  have h2 : Real.sqrt 3 / 2 ≤ 7 / 8 := by
    have h3 : Real.sqrt 3 ≤ 7 / 4 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    linarith only [h3]
  nlinarith only [h1, h2, hδ]

/-! ## 5. The `fsX` arithmetic -/

lemma fsX_pos {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    0 < Work.BoseFixR.fsX v μ := by
  rw [Work.BoseFixR.fsX, fsXp]
  exact Real.rpow_pos_of_pos (mul_pos hμ (pow_pos hav 3)) _

/-- `X^{323} = dil v μ`: the inverse of the definition `X = dil^{1/323}`. -/
theorem fsX_rpow_323 {v : E3 → ℝ} {μ : ℝ} (h : 0 < dil v μ) :
    (Work.BoseFixR.fsX v μ) ^ (323 : ℝ) = dil v μ := by
  rw [Work.BoseFixR.fsX, fsXp, ← Real.rpow_mul h.le]
  norm_num

end Work.BoseBogFS
