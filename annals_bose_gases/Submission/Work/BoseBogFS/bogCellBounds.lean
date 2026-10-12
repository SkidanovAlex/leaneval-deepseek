import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.bogCellDefs
import Submission.Work.BoseBogFS.integrable_psiSc_of_cleanFun
import Submission.Work.BoseBogFS.psiSc_cell_sqrt_le
import Submission.Work.BoseBogFS.psiSc_sub_le_master
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogCellBounds` — the per-cell bounds of the clean Riemann row

This module proves the case-by-case per-cell inequalities
`psiSc (t_n) − ⍍_{δ-cell} psiSc ≤ bogMajA/B/C n` matching the definitions of
`Work.BoseBogFS.bogCellDefs`.

* **Region A** (`r_hi ≤ c₁`): `τ_s ≡ 0` on the cell, so `ψ = β − β²/(2‖t‖²)` and the
  excess is at most `o + B²/(2 r_lo²)`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Lattice bookkeeping -/

lemma lpt_eq_smul_one (d : ℝ) (n : Fin 3 → ℤ) : lpt d n = d • lpt 1 n := by
  ext i
  simp only [lpt, WithLp.ofLp_smul, Pi.smul_apply, WithLp.ofLp_toLp, smul_eq_mul]
  ring

lemma norm_lpt_eq (d : ℝ) (hd : 0 ≤ d) (n : Fin 3 → ℤ) : ‖lpt d n‖ = d * ‖lpt 1 n‖ := by
  rw [lpt_eq_smul_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd]

lemma one_le_norm_lpt_one {n : Fin 3 → ℤ} (hn : n ≠ 0) : 1 ≤ ‖lpt (1 : ℝ) n‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  have h := PiLp.norm_apply_le (lpt (1 : ℝ) n) i
  rw [lpt_ofLp, one_mul, Real.norm_eq_abs] at h
  have hone : (1 : ℝ) ≤ |((n i : ℤ) : ℝ)| := by
    have habs : (1 : ℤ) ≤ |n i| := by
      have h2 : (0 : ℤ) < |n i| := abs_pos.mpr hi
      omega
    rw [← Int.cast_abs]
    exact_mod_cast habs
  linarith

lemma bogMesh_pos_of {v : E3 → ℝ} {ρ μ : ℝ} (hρ : 0 < ρ) (hav : 0 < a v)
    (hℓ : 0 < ell v μ) : 0 < bogMesh v ρ μ := by
  rw [bogMesh]
  positivity

lemma sqrt_three_div_two_lt_one : Real.sqrt 3 / 2 < 1 := by
  have h : Real.sqrt 3 < 2 := (Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)).mpr (by norm_num)
  linarith

lemma bogRLo_pos {v : E3 → ℝ} {ρ μ : ℝ} (hδ : 0 < bogMesh v ρ μ) {n : Fin 3 → ℤ}
    (hn : n ≠ 0) : 0 < bogRLot v ρ μ n := by
  have h1 : (1 : ℝ) ≤ ‖lpt (1 : ℝ) n‖ := one_le_norm_lpt_one hn
  have h2 : bogMesh v ρ μ ≤ bogMesh v ρ μ * ‖lpt (1 : ℝ) n‖ := by
    nlinarith [hδ, h1]
  have h3 : bogMesh v ρ μ * Real.sqrt 3 / 2 < bogMesh v ρ μ := by
    nlinarith [hδ, sqrt_three_div_two_lt_one]
  rw [bogRLot, bogHalf, norm_tSca, norm_lpt_eq (bogMesh v ρ μ) hδ.le n]
  linarith

/-! ## 2. The `β`-rows -/

/-- `|β_s t| ≤ bogBs v R` as soon as `0 < R`. -/
theorem bogBeta_le {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) (t : E3) :
    |betaSc v h ρ μ t| ≤ bogBs v R := by
  have hb := bogKB_spec (h := h) hR hρ hav hv hvrad hv_supp hRℓ t
  have hpos : 0 < a v * (1 + Real.sqrt (ρ * a v) * ‖t‖) := by positivity
  have hnum : (0 : ℝ) ≤ bogKB * (1 + R) ^ 3 :=
    mul_nonneg bogKB_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ 1 + R) 3)
  have hu : (0 : ℝ) ≤ Real.sqrt (ρ * a v) * ‖t‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg t)
  have h1 : bogKB * (1 + R) ^ 3 / (a v * (1 + Real.sqrt (ρ * a v) * ‖t‖))
      ≤ bogKB * (1 + R) ^ 3 / (a v) := by
    rw [div_le_div_iff₀ hpos hav]
    exact mul_le_mul_of_nonneg_left (by nlinarith [hav, hu] : a v ≤ a v * (1 + Real.sqrt (ρ * a v) * ‖t‖)) hnum
  rw [bogBs]
  exact le_trans hb (le_trans h1 (le_max_right _ _))

/-- The honest `β`-oscillation bound of `bogKOs_spec`, at the cell of `n`. -/
theorem bogOm_spec {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) (hδ : 0 < bogMesh v ρ μ)
    (hn : n ≠ 0) :
    ∀ y : E3, ‖y - tSca v ρ μ n‖ ≤ bogHalf v ρ μ →
      |betaSc v h ρ μ y - betaSc v h ρ μ (tSca v ρ μ n)| ≤ bogOm v h R ρ μ n := by
  have hΔ : 0 ≤ bogHalf v ρ μ := (bogHalf_pos hδ).le
  have hrlo : 0 < bogRLot v ρ μ n := bogRLo_pos hδ hn
  have hfar : bogRLot v ρ μ n + bogHalf v ρ μ ≤ ‖tSca v ρ μ n‖ := by
    rw [bogRLot]; linarith
  intro y hy
  have hb := bogKOs_spec (h := h) hR hρ hav hv hvrad hv_supp hRℓ hΔ hrlo y (tSca v ρ μ n) hy hfar
  simp only [bogOm, bogOscK]
  exact hb

/-! ## 3. Region A: the τ-ball -/

/-- On the τ-ball the scaled kinetic symbol vanishes. -/
lemma tauSc_eq_zero_of_le_c1 {v : E3 → ℝ} {ρ μ : ℝ} (hP : 0 < ρ * a v)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (a v)).eT) (heT1 : (Work.BoseBox.paramsAt μ (a v)).eT ≤ 1)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ) (hc12 : bogC1 v ρ μ ≤ bogC2 v ρ μ)
    {t : E3} (ht : ‖t‖ ≤ bogC1 v ρ μ) : tauSc v ρ μ t = 0 := by
  rw [tauSc_eq_tauScRad, tauScRad_eq v hP]
  have h1 : Work.BoseBoxFock.tauProf (‖t‖ / bogC1 v ρ μ) = 0 :=
    Work.BoseBoxFock.tauProf_eq_zero_of_le_one (by
      rw [div_le_one hc1]; exact ht)
  have h2 : Work.BoseBoxFock.tauProf (‖t‖ / bogC2 v ρ μ) = 0 :=
    Work.BoseBoxFock.tauProf_eq_zero_of_le_one (by
      rw [div_le_one hc2]
      exact le_trans ht hc12)
  rw [h1, h2]
  ring

/-- **Region A per-cell bound** (`r_hi ≤ c₁`): the τ-ball. -/
theorem bogCellA {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < a v) (hμ : 0 < μ)
    (hv : ∀ x, 0 ≤ v x) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    (hδ : 0 < bogMesh v ρ μ) (hn : n ≠ 0)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (a v)).eT) (heT1 : (Work.BoseBox.paramsAt μ (a v)).eT ≤ 1)
    (hc12 : bogC1 v ρ μ ≤ bogC2 v ρ μ)
    (hgate : bogRHit v ρ μ n ≤ bogC1 v ρ μ)
    (hInt : IntegrableOn (psiSc v h ρ μ) (cell (bogMesh v ρ μ) n)) :
    psiSc v h ρ μ (tSca v ρ μ n)
        - ((bogMesh v ρ μ) ^ 3)⁻¹
          * (∫ x in cell (bogMesh v ρ μ) n, psiSc v h ρ μ x)
      ≤ bogMajA v h R ρ μ n := by
  have hΔ : 0 < bogHalf v ρ μ := bogHalf_pos hδ
  have hc1 : 0 < bogC1 v ρ μ := by
    rw [bogRHit] at hgate
    have hrlo := bogRLo_pos hδ hn
    rw [bogRLot] at hrlo
    linarith
  have hc2 : 0 < bogC2 v ρ μ := lt_of_lt_of_le hc1 hc12
  have hP : 0 < ρ * a v := mul_pos hρ hav
  -- τ_s vanishes on the whole cell
  have htau : ∀ x : E3, ‖x - tSca v ρ μ n‖ ≤ bogHalf v ρ μ → tauSc v ρ μ x = 0 := by
    intro x hx
    refine tauSc_eq_zero_of_le_c1 hP heT0 heT1 hc1 hc2 hc12 ?_
    have h1 : ‖x‖ ≤ ‖tSca v ρ μ n‖ + bogHalf v ρ μ := by
      have h2 := norm_add_le (x - tSca v ρ μ n) (tSca v ρ μ n)
      rw [sub_add_cancel] at h2
      linarith
    rw [bogRHit] at hgate
    linarith
  have htn : tauSc v ρ μ (tSca v ρ μ n) = 0 := by
    refine tauSc_eq_zero_of_le_c1 hP heT0 heT1 hc1 hc2 hc12 ?_
    rw [bogRHit] at hgate
    linarith [le_of_lt hΔ]
  have hbeta := bogBeta_le (h := h) hR hρ hav hv hvrad hv_supp hRℓ
  have hosc := bogOm_spec (h := h) hR hρ hav hv hvrad hv_supp hRℓ hδ hn
  have hOmle : bogOm v h R ρ μ n ≤ bogOscM v R ρ μ := by
    rw [bogOm, bogOscM, bogOscK]
    have hden : (0 : ℝ) < 1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ n := by
      have := mul_nonneg (Real.sqrt_nonneg (ρ * a v)) (bogRLo_pos hδ hn).le
      linarith
    have hulo : 0 ≤ Real.sqrt (ρ * a v) * bogRLot v ρ μ n :=
      mul_nonneg (Real.sqrt_nonneg _) (bogRLo_pos hδ hn).le
    rw [div_le_iff₀ hden]
    have hK : 0 ≤ bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ :=
      mul_nonneg (mul_nonneg (mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3))
        (Real.sqrt_nonneg _)) hΔ.le
    nlinarith [hK, hulo, hden]
  have hzp : ∀ B : ℝ, Work.BoseB6.bogZeroPoint (0 + B) B = B := by
    intro B
    rw [Work.BoseB6.bogZeroPoint, show (0 + B) ^ 2 - B ^ 2 = 0 by ring, Real.sqrt_zero,
      sub_zero, zero_add]
  have hpt : ∀ x : E3, ‖x - lpt (bogMesh v ρ μ) n‖ ≤ bogMesh v ρ μ * Real.sqrt 3 / 2 →
      psiSc v h ρ μ (lpt (bogMesh v ρ μ) n) - psiSc v h ρ μ x
        ≤ bogOm v h R ρ μ n + (bogBs v R) ^ 2 / (2 * (bogRLot v ρ μ n) ^ 2) := by
    intro x hx
    have hsub : ‖x - tSca v ρ μ n‖ ≤ bogHalf v ρ μ := by rw [tSca_eq_lpt]; exact hx
    have hxt : tauSc v ρ μ x = 0 := htau x hsub
    have e1 : psiSc v h ρ μ (lpt (bogMesh v ρ μ) n) = betaSc v h ρ μ (tSca v ρ μ n)
        - betaSc v h ρ μ (tSca v ρ μ n) ^ 2 / (2 * ‖tSca v ρ μ n‖ ^ 2) := by
      rw [← tSca_eq_lpt, psiSc, htn]
      simp only [hzp]
    have e2 : psiSc v h ρ μ x = betaSc v h ρ μ x
        - betaSc v h ρ μ x ^ 2 / (2 * ‖x‖ ^ 2) := by
      rw [psiSc, hxt]
      simp only [hzp]
    rw [e1, e2]
    have hbnd : |betaSc v h ρ μ x| ≤ bogBs v R := hbeta x
    have hd1 : betaSc v h ρ μ x ^ 2 ≤ (bogBs v R) ^ 2 := by
      nlinarith [abs_le.mp hbnd, bogBs_pos v R]
    have hxl : bogRLot v ρ μ n ≤ ‖x‖ := by
      have h1 : ‖tSca v ρ μ n‖ - ‖x‖ ≤ ‖x - tSca v ρ μ n‖ := by
        have h2 := norm_sub_norm_le (tSca v ρ μ n) x
        rwa [norm_sub_rev] at h2
      rw [bogRLot]
      linarith
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (bogRLo_pos hδ hn) hxl
    have hden2 : (0 : ℝ) < 2 * ‖x‖ ^ 2 := by positivity
    have hden3 : (0 : ℝ) < 2 * (bogRLot v ρ μ n) ^ 2 := by
      nlinarith [bogRLo_pos hδ hn]
    have hkey : betaSc v h ρ μ x ^ 2 / (2 * ‖x‖ ^ 2)
        ≤ (bogBs v R) ^ 2 / (2 * (bogRLot v ρ μ n) ^ 2) := by
      rw [div_le_div_iff₀ hden2 hden3]
      have hr2 : (bogRLot v ρ μ n) ^ 2 ≤ ‖x‖ ^ 2 :=
        by nlinarith [hxl, bogRLo_pos hδ hn, norm_nonneg x]
      nlinarith [hd1, hr2, sq_nonneg (betaSc v h ρ μ x), sq_nonneg (bogBs v R)]
    have hosc' := hosc x hsub
    have hterm : betaSc v h ρ μ (tSca v ρ μ n) - betaSc v h ρ μ x
        ≤ bogOm v h R ρ μ n := by
      have h2 := neg_abs_le (betaSc v h ρ μ x - betaSc v h ρ μ (tSca v ρ μ n))
      linarith [hosc']
    have hsq : (0 : ℝ) ≤ betaSc v h ρ μ (tSca v ρ μ n) ^ 2 / (2 * ‖tSca v ρ μ n‖ ^ 2) := by
      positivity
    linarith [hterm, hkey, hsq]
  have hmain : psiSc v h ρ μ (lpt (bogMesh v ρ μ) n)
      - ((bogMesh v ρ μ) ^ 3)⁻¹ * (∫ x in cell (bogMesh v ρ μ) n, psiSc v h ρ μ x)
      ≤ bogMajA v h R ρ μ n := by
    rw [bogMajA]
    refine le_trans (cell_excess_le_of_ball hδ n hInt hpt) ?_
    linarith [hOmle]
  rw [← tSca_eq_lpt] at hmain
  exact hmain

/-! ## 4. Region C: the bulk -/

/-- The `W_lo` of the cell of `n`. -/
lemma bogWlo_pos {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hulo : 0 < bogULot v ρ μ n) (huvl : 0 < bogULot v ρ μ n + 2 * bogVlot v h R ρ μ n) :
    0 < Real.sqrt ((bogULot v ρ μ n) ^ 2 + 2 * bogULot v ρ μ n * bogVlot v h R ρ μ n) := by
  rw [Real.sqrt_pos]
  nlinarith [hulo, huvl]

/-- **Region C per-cell bound** (`16√Vs < r_hi`): the master oscillation bound. -/
theorem bogCellC {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < a v) (hμ : 0 < μ)
    (hv : ∀ x, 0 ≤ v x) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    (hdil : dil v μ ≤ 1) (hδ : 0 < bogMesh v ρ μ) (hn : n ≠ 0)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (a v)).eT ≤ 1)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ)
    (hulo : 0 < bogULot v ρ μ n)
    (huhi : bogUHit v ρ μ n ≤ (bogRLot v ρ μ n) ^ 2)
    (huvl : 0 < bogULot v ρ μ n + 2 * bogVlot v h R ρ μ n)
    (hubeta : 2 * bogBs v R ≤ bogULot v ρ μ n)
    (hInt : IntegrableOn (psiSc v h ρ μ) (cell (bogMesh v ρ μ) n)) :
    psiSc v h ρ μ (tSca v ρ μ n)
        - ((bogMesh v ρ μ) ^ 3)⁻¹ * (∫ x in cell (bogMesh v ρ μ) n, psiSc v h ρ μ x)
      ≤ bogMajC v h R ρ μ n := by
  have hΔ : 0 < bogHalf v ρ μ := bogHalf_pos hδ
  have hP : 0 < ρ * a v := mul_pos hρ hav
  have hmono : Monotone (tauScRad v ρ μ) := tauScRad_mono hP heT0 heT1 hc1 hc2
  have hbeta := bogBeta_le (h := h) hR hρ hav hv hvrad hv_supp hRℓ
  have hosc := bogOm_spec (h := h) hR hρ hav hv hvrad hv_supp hRℓ hδ hn
  have hW : 0 < Real.sqrt ((bogULot v ρ μ n) ^ 2 + 2 * bogULot v ρ μ n
      * bogVlot v h R ρ μ n) := bogWlo_pos hulo huvl
  have hS : 0 < bogULot v ρ μ n + bogVlot v h R ρ μ n
      + Real.sqrt ((bogULot v ρ μ n) ^ 2 + 2 * bogULot v ρ μ n * bogVlot v h R ρ μ n) := by
    have := Real.sqrt_nonneg ((bogULot v ρ μ n) ^ 2 + 2 * bogULot v ρ μ n * bogVlot v h R ρ μ n)
    linarith
  have hmain : psiSc v h ρ μ (lpt (bogMesh v ρ μ) n)
      - ((bogMesh v ρ μ) ^ 3)⁻¹ * (∫ x in cell (bogMesh v ρ μ) n, psiSc v h ρ μ x)
      ≤ bogMajC v h R ρ μ n := by
    refine cell_excess_le_of_ball hδ n hInt ?_
    intro x hx
    have hsub : ‖x - tSca v ρ μ n‖ ≤ bogHalf v ρ μ := by rw [tSca_eq_lpt]; exact hx
    -- ranges
    have hrxl : bogRLot v ρ μ n ≤ ‖x‖ := by
      have h1 : ‖tSca v ρ μ n‖ - ‖x‖ ≤ ‖x - tSca v ρ μ n‖ := by
        have h2 := norm_sub_norm_le (tSca v ρ μ n) x
        rwa [norm_sub_rev] at h2
      rw [bogRLot]
      linarith
    have hrxh : ‖x‖ ≤ bogRHit v ρ μ n := by
      have h1 := norm_add_le (x - tSca v ρ μ n) (tSca v ρ μ n)
      rw [sub_add_cancel] at h1
      rw [bogRHit]
      linarith
    have hu : bogULot v ρ μ n ≤ tauSc v ρ μ x ∧ tauSc v ρ μ x ≤ bogUHit v ρ μ n := by
      constructor
      · rw [tauSc_eq_tauScRad]; exact hmono hrxl
      · rw [tauSc_eq_tauScRad]; exact hmono hrxh
    have hb := hosc x hsub
    rw [abs_le] at hb
    have hvbd : bogVlot v h R ρ μ n ≤ betaSc v h ρ μ x
        ∧ betaSc v h ρ μ x ≤ bogVhit v h R ρ μ n := by
      constructor
      · rw [bogVlot, bogVNt]; linarith [hb.1]
      · rw [bogVhit, bogVNt]; linarith [hb.2]
    have hxu : 0 ≤ tauSc v ρ μ x := by
      rw [tauSc_eq_tauScRad]; exact tauScRad_nonneg v hP heT0 heT1 _
    have hxu2 : 0 ≤ tauSc v ρ μ x + 2 * betaSc v h ρ μ x := by
      have h1 : tauSc v ρ μ x ≥ bogULot v ρ μ n := hu.1
      have h2 : betaSc v h ρ μ x ≥ -(bogBs v R) := by
        have := neg_abs_le (betaSc v h ρ μ x); linarith [hbeta x]
      linarith [hubeta]
    have hbox : (let r_lo := ‖tSca v ρ μ n‖ - bogHalf v ρ μ
                 let r_hi := ‖tSca v ρ μ n‖ + bogHalf v ρ μ
                 let u_lo := tauScRad v ρ μ r_lo
                 let u_hi := tauScRad v ρ μ r_hi
                 let v_lo := betaSc v h ρ μ (tSca v ρ μ n) - bogOm v h R ρ μ n
                 let W_lo := Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)
                 let S_lo := u_lo + v_lo + W_lo
                 0 < u_lo ∧ u_hi ≤ r_lo ^ 2 ∧ 0 < u_lo + 2 * v_lo ∧ 0 < S_lo ∧ 0 < W_lo) := by
      dsimp only
      exact ⟨hulo, huhi, huvl, hS, hW⟩
    rw [← tSca_eq_lpt]
    exact psiSc_sub_le_master (h := h) hR hρ hav hv hvrad hv_supp hRℓ hμ hdil hc1 hc2
      heT0 heT1 hΔ hsub hosc hbox hxu hxu2
  rw [← tSca_eq_lpt] at hmain
  exact hmain

/-! ## 5. Region B: the intermediate region -/

/-- **Region B per-cell bound** (`c₁ < r_hi ≤ 16√Vs`): the `√`-difference bound. -/
theorem bogCellB {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hδ : 0 < bogMesh v ρ μ) (hn : n ≠ 0)
    (hInt : IntegrableOn (psiSc v h ρ μ) (cell (bogMesh v ρ μ) n))
    (hsqrt : ∀ x : E3, ‖x - tSca v ρ μ n‖ ≤ bogHalf v ρ μ →
      psiSc v h ρ μ (tSca v ρ μ n) - psiSc v h ρ μ x
        ≤ (bogUHit v ρ μ n - bogULot v ρ μ n)
          + Real.sqrt ((bogUHit v ρ μ n - bogULot v ρ μ n)
              * (2 * bogUHit v ρ μ n + 2 * bogVmaxt v h R ρ μ n))
          + bogOm v h R ρ μ n + Real.sqrt (2 * bogOm v h R ρ μ n * bogUHit v ρ μ n)
          + bogOm v h R ρ μ n * bogVmaxt v h R ρ μ n / (bogRLot v ρ μ n) ^ 2
          + (bogVmaxt v h R ρ μ n) ^ 2
              * (1 / (2 * (bogRLot v ρ μ n) ^ 2) - 1 / (2 * (bogRHit v ρ μ n) ^ 2))) :
    psiSc v h ρ μ (tSca v ρ μ n)
        - ((bogMesh v ρ μ) ^ 3)⁻¹ * (∫ x in cell (bogMesh v ρ μ) n, psiSc v h ρ μ x)
      ≤ bogMajB v h R ρ μ n := by
  have hmain : psiSc v h ρ μ (lpt (bogMesh v ρ μ) n)
      - ((bogMesh v ρ μ) ^ 3)⁻¹ * (∫ x in cell (bogMesh v ρ μ) n, psiSc v h ρ μ x)
      ≤ bogMajB v h R ρ μ n := by
    rw [bogMajB]
    refine cell_excess_le_of_ball hδ n hInt ?_
    intro x hx
    have hsub : ‖x - tSca v ρ μ n‖ ≤ bogHalf v ρ μ := by rw [tSca_eq_lpt]; exact hx
    rw [← tSca_eq_lpt]
    exact hsqrt x hsub
  rw [← tSca_eq_lpt] at hmain
  exact hmain

/-! ## 6. `bogOm` is nonnegative and the full per-cell assembly -/

lemma bogOm_nonneg {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hρ : 0 < ρ) (hav : 0 < a v) (hR : 0 ≤ R) (hδ : 0 < bogMesh v ρ μ) (hn : n ≠ 0) :
    0 ≤ bogOm v h R ρ μ n := by
  rw [bogOm, bogOscK]
  have hrlo := bogRLo_pos hδ hn
  have hΔ : 0 ≤ bogHalf v ρ μ := (bogHalf_pos hδ).le
  have hden : (0 : ℝ) < 1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ n := by
    have := mul_nonneg (Real.sqrt_nonneg (ρ * a v)) hrlo.le
    linarith
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3))
    (Real.sqrt_nonneg _)) hΔ) hden.le

/-- **The full per-cell bound**: for every `n ≠ 0` the scaled cell excess is at most `bogMaj n`.
The four `hulo`/`huhi`/`huvl`/`hubeta` side conditions are only used in the bulk branch. -/
theorem bogCellAll {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < a v) (hμ : 0 < μ)
    (hv : ∀ x, 0 ≤ v x) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    (hdil : dil v μ ≤ 1) (hδ : 0 < bogMesh v ρ μ) (hn : n ≠ 0)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (a v)).eT ≤ 1)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ)
    (hc12 : bogC1 v ρ μ ≤ bogC2 v ρ μ)
    (hInt : IntegrableOn (psiSc v h ρ μ) (cell (bogMesh v ρ μ) n))
    (hulo : 0 < bogULot v ρ μ n)
    (huhi : bogUHit v ρ μ n ≤ (bogRLot v ρ μ n) ^ 2)
    (huvl : 0 < bogULot v ρ μ n + 2 * bogVlot v h R ρ μ n)
    (hubeta : 2 * bogBs v R ≤ bogULot v ρ μ n) :
    psiSc v h ρ μ (tSca v ρ μ n)
        - ((bogMesh v ρ μ) ^ 3)⁻¹ * (∫ x in cell (bogMesh v ρ μ) n, psiSc v h ρ μ x)
      ≤ bogMaj v h R ρ μ n := by
  have hP : 0 < ρ * a v := mul_pos hρ hav
  have hmono : Monotone (tauScRad v ρ μ) := tauScRad_mono hP heT0 heT1 hc1 hc2
  have hosc := bogOm_spec (h := h) hR hρ hav hv hvrad hv_supp hRℓ hδ hn
  have hΔ : 0 < bogHalf v ρ μ := bogHalf_pos hδ
  have hOsc0 : 0 ≤ bogOm v h R ρ μ n := bogOm_nonneg hρ hav hR.le hδ hn
  have hr0 : 0 < bogRLot v ρ μ n := bogRLo_pos hδ hn
  by_cases hA : bogRHit v ρ μ n ≤ bogC1 v ρ μ
  · rw [bogMaj, if_neg hn, if_pos hA]
    exact bogCellA (h := h) hR hρ hav hμ hv hvrad hv_supp hRℓ hδ hn heT0 heT1 hc12 hA hInt
  · by_cases hB : bogRHit v ρ μ n ≤ bogBigThr v R ρ μ
    · rw [bogMaj, if_neg hn, if_neg hA, if_pos hB]
      refine bogCellB (h := h) hδ hn hInt ?_
      intro x hx
      have hrxl : bogRLot v ρ μ n ≤ ‖x‖ := by
        have h1 : ‖tSca v ρ μ n‖ - ‖x‖ ≤ ‖x - tSca v ρ μ n‖ := by
          have h2 := norm_sub_norm_le (tSca v ρ μ n) x
          rwa [norm_sub_rev] at h2
        rw [bogRLot]; linarith
      have hrxh : ‖x‖ ≤ bogRHit v ρ μ n := by
        have h1 := norm_add_le (x - tSca v ρ μ n) (tSca v ρ μ n)
        rw [sub_add_cancel] at h1
        rw [bogRHit]; linarith
      have hbx := abs_le.mp (hosc x hx)
      exact psiSc_cell_sqrt_le (n := n) hΔ hOsc0 hx hosc
        (tauScRad_nonneg v hP heT0 heT1 _)
        (by rw [tauSc_eq_tauScRad]; exact hmono hrxl)
        (by rw [tauSc_eq_tauScRad]; exact hmono hrxh)
        (by rw [tauSc_eq_tauScRad]; exact hmono (by rw [bogRLot]; linarith))
        (by rw [tauSc_eq_tauScRad]; exact hmono (by rw [bogRHit]; linarith))
        (by rw [bogVlot, bogVNt]; linarith [hbx.1])
        (by rw [bogVhit, bogVNt]; linarith [hbx.2])
        (by rw [bogVlot, bogVNt]; linarith [hOsc0])
        (by rw [bogVhit, bogVNt]; linarith [hOsc0])
        hrxl hrxh
        (by rw [bogRLot]; linarith)
        (by rw [bogRHit]; linarith) hr0
    · rw [bogMaj, if_neg hn, if_neg hA, if_neg hB]
      exact bogCellC (h := h) hR hρ hav hμ hv hvrad hv_supp hRℓ hdil hδ hn heT0 heT1 hc1 hc2
        hulo huhi huvl hubeta hInt

end Work.BoseBogFS
