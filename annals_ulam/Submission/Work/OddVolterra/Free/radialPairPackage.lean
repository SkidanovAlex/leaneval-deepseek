import Mathlib
import Submission.Work.OddCurve.LowSlope.RadialLogConstruction
import Submission.Work.OddCurve.LowSlope.radial_system_sharp_small
import Submission.Work.OddCurve.LowSlope.sol_deriv_bounds_sharp
import Submission.Work.OddRadon.RadialDefs

set_option maxHeartbeats 1600000

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Work.OddVolterra.Free

open Work.OddCurve.LowSlope

/-! ## Helpers: the vanishing window, and the `α`-factor first-derivative bound

The two-power radial solution `solR n A B` is `1` wherever the data `A, B` vanish, and the
extra hypotheses `|A'| ≤ δ₁ sin`, `|B'| ≤ δ₁ sin` of the package upgrade the first-derivative
bound `|R'| ≤ 3δ₁/(n+1)` of `rsc2_deriv1_bound` to `|R'| ≤ 3δ₁ sin α ≤ 3δ₁ α`. -/

/-- `solR` is `1` where the data vanish. -/
lemma solR_eq_one_of_data_eq_zero (n : ℕ) {A B : ℝ → ℝ} {β : ℝ}
    (hA : A β = 0) (hB : B β = 0) : solR n A B β = 1 := by
  have hW : solW n A B β = 0 := by
    rw [solW_apply, hA, hB, zero_div]
  rw [solR_apply, solX_apply, hW, radInv_zero, solU_apply, hA]
  rw [show (1 / 2 : ℝ) * (2 + 0) = 1 by norm_num, Real.one_rpow]

/-- `solr` is `1` where the data vanish. -/
lemma solr_eq_one_of_data_eq_zero (n : ℕ) {A B : ℝ → ℝ} {β : ℝ}
    (hA : A β = 0) (hB : B β = 0) : solr n A B β = 1 := by
  have hW : solW n A B β = 0 := by
    rw [solW_apply, hA, hB, zero_div]
  rw [solr_apply, solX_apply, hW, radInv_zero, solU_apply, hA]
  rw [show (1 - 1 / 2 : ℝ) * (2 + 0) = 1 by norm_num, Real.one_rpow]

/-- The sharp box bounds for the pair `(solR, solr)` at a point of `[0, π/2]`. -/
lemma solR_sharpBox (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ : 0 < σ)
    (hσ8 : σ ≤ 1 / 8)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    SharpBox n (solR n A B α) (solr n A B α) :=
  (sol_box_value_sharp n hn hσ hσ8 hA hB (solX_window_sharp n hn hσ hσ8 hA hB hα) hα).1

/-- **The `α`-factor first-derivative bound for `R`.** -/
lemma solR_deriv_le_sin (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ δ₁ : ℝ} (hσ : 0 < σ)
    (hσ8 : σ ≤ 1 / 8)
    (hAc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    (hBc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    (hAval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hBval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hδ₁ : 0 ≤ δ₁)
    (hA1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv A β| ≤ δ₁ * Real.sin β)
    (hB1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv B β| ≤ δ₁ * Real.sin β) :
    ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv (solR n A B) α| ≤ 3 * δ₁ * Real.sin α := by
  intro α hα
  have hσ' : σ ≤ 1 / 2 := by linarith
  have hmem : α ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hα.1], by linarith [hα.2, Real.pi_pos]⟩
  have hAcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A α :=
    hAc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)
  have hBcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B α :=
    hBc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)
  have hRcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solR n A B) α :=
    solR_contDiffAt n hn hσ' hAc hBc hAval hBval hα
  have hrcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solr n A B) α :=
    solr_contDiffAt n hn hσ' hAc hBc hAval hBval hα
  have hRpos : 0 < solR n A B α := solR_pos n hn hσ' hAval hBval hα
  have hrpos : 0 < solr n A B α := solr_pos n hn hσ' hAval hBval hα
  have hsys := sol_system_eventually n hn hσ' hAc hBc hAval hBval hα
  have hbox := solR_sharpBox n hn hσ hσ8 hAval hBval hα
  obtain ⟨hformR, -⟩ := sol_deriv_formulas n hRcd hrcd hAcd hBcd hRpos hrpos hsys
  have hsin0 : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_mem_Icc ⟨hα.1, by linarith [hα.2, Real.pi_pos]⟩
  have hD : 0 ≤ δ₁ * Real.sin α := mul_nonneg hδ₁ hsin0
  obtain ⟨h1, -⟩ := rsc2_deriv1_bound n hn hD hRpos hrpos hbox
    (hA1 α hα) (hB1 α hα) hformR
  have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  calc |deriv (solR n A B) α| ≤ 3 * (δ₁ * Real.sin α) / ((n : ℝ) + 1) := h1
    _ ≤ 3 * δ₁ * Real.sin α := by
        have h0 : (0 : ℝ) ≤ 3 * (δ₁ * Real.sin α) := by linarith [hD]
        have hle := div_le_self h0 hN1
        linarith [hle]

/-- **The `α`-factor first-derivative bound for `r`.** -/
lemma solr_deriv_le_sin (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ δ₁ : ℝ} (hσ : 0 < σ)
    (hσ8 : σ ≤ 1 / 8)
    (hAc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    (hBc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    (hAval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hBval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hδ₁ : 0 ≤ δ₁)
    (hA1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv A β| ≤ δ₁ * Real.sin β)
    (hB1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv B β| ≤ δ₁ * Real.sin β) :
    ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv (solr n A B) α| ≤ 3 * δ₁ * Real.sin α := by
  intro α hα
  have hσ' : σ ≤ 1 / 2 := by linarith
  have hmem : α ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hα.1], by linarith [hα.2, Real.pi_pos]⟩
  have hAcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A α :=
    hAc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)
  have hBcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B α :=
    hBc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)
  have hRcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solR n A B) α :=
    solR_contDiffAt n hn hσ' hAc hBc hAval hBval hα
  have hrcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solr n A B) α :=
    solr_contDiffAt n hn hσ' hAc hBc hAval hBval hα
  have hRpos : 0 < solR n A B α := solR_pos n hn hσ' hAval hBval hα
  have hrpos : 0 < solr n A B α := solr_pos n hn hσ' hAval hBval hα
  have hsys := sol_system_eventually n hn hσ' hAc hBc hAval hBval hα
  have hbox := solR_sharpBox n hn hσ hσ8 hAval hBval hα
  obtain ⟨-, hformr⟩ := sol_deriv_formulas n hRcd hrcd hAcd hBcd hRpos hrpos hsys
  have hsys_sw : ∀ᶠ γ in 𝓝 α,
      (solr n A B) γ ^ (2 * n + 2) + (solR n A B) γ ^ (2 * n + 2) = 2 + A γ ∧
        (solr n A B) γ ^ (2 * n + 1) - (solR n A B) γ ^ (2 * n + 1) = (fun y => -B y) γ := by
    filter_upwards [hsys] with γ hγ
    exact ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
  have hB1' : |deriv (fun y : ℝ => -B y) α| ≤ δ₁ * Real.sin α := by
    rw [sdb_deriv_neg_fun B]
    simpa using hB1 α hα
  have hrform' : deriv (solr n A B) α = (((2 * n + 1 : ℕ) : ℝ) * deriv A α +
        ((2 * n + 2 : ℕ) : ℝ) * solR n A B α * deriv (fun y : ℝ => -B y) α)
      / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * solr n A B α ^ (2 * n)
          * (solr n A B α + solR n A B α)) := by
    rw [hformr, sdb_deriv_neg_fun B]
    congr 1 <;> ring
  have hsin0 : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_mem_Icc ⟨hα.1, by linarith [hα.2, Real.pi_pos]⟩
  have hD : 0 ≤ δ₁ * Real.sin α := mul_nonneg hδ₁ hsin0
  obtain ⟨h1, -⟩ := rsc2_deriv1_bound n hn hD hrpos hRpos (sharpBox_swap hbox)
    (hA1 α hα) hB1' hrform'
  have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  calc |deriv (solr n A B) α| ≤ 3 * (δ₁ * Real.sin α) / ((n : ℝ) + 1) := h1
    _ ≤ 3 * δ₁ * Real.sin α := by
        have h0 : (0 : ℝ) ≤ 3 * (δ₁ * Real.sin α) := by linarith [hD]
        have hle := div_le_self h0 hN1
        linarith [hle]

theorem radialPairPackage (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {A B : ℝ → ℝ} {σ δ₁ δ₂ : ℝ},
      0 < σ → σ ≤ 1 / 8 → 0 ≤ δ₁ → δ₁ ≤ 1 / 20 → 0 ≤ δ₂ →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) →
      (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A α| ≤ σ ∧ |B α| ≤ σ) →
      (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv A α| ≤ δ₁ ∧ |deriv B α| ≤ δ₁) →
      (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        |deriv (deriv A) α| ≤ δ₂ ∧ |deriv (deriv B) α| ≤ δ₂) →
      (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv A α| ≤ δ₁ * Real.sin α) →
      (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv B α| ≤ δ₁ * Real.sin α) →
      A (Real.pi / 2) = 0 → B (Real.pi / 2) = 0 →
      (∀ α ∈ Set.Ioo (Real.pi / 2 - 1 / 4) (Real.pi / 2 + 1 / 4), A α = 0 ∧ B α = 0) →
      ∃ R r : ℝ → ℝ,
        R = Work.OddCurve.LowSlope.solR n A B ∧ r = Work.OddCurve.LowSlope.solr n A B ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2)) ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r (Set.Icc 0 (Real.pi / 2)) ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R
          (Set.Ioo (Real.pi / 2 - 1 / 4) (Real.pi / 2 + 1 / 4)) ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r
          (Set.Ioo (Real.pi / 2 - 1 / 4) (Real.pi / 2 + 1 / 4)) ∧
        Work.OddRadon.RadialSystem n (fun α => (2 + A α) * Real.cos α ^ 2)
          (fun α => B α * Real.cos α) R r ∧
        R (Real.pi / 2) = r (Real.pi / 2) ∧
        (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          1 - C * (σ + δ₁ + δ₂) ≤ R α ∧ 1 - C * (σ + δ₁ + δ₂) ≤ r α ∧
          |deriv R α| ≤ C * (σ + δ₁ + δ₂) * α ∧ |deriv r α| ≤ C * (σ + δ₁ + δ₂) * α ∧
          |deriv (deriv R) α| ≤ C * (σ + δ₁ + δ₂) ∧
          |deriv (deriv r) α| ≤ C * (σ + δ₁ + δ₂)) ∧
        0 ≤ deriv r (Real.pi / 2) / r (Real.pi / 2) +
          deriv R (Real.pi / 2) / R (Real.pi / 2) := by
  refine ⟨4, by norm_num, ?_⟩
  intro A B σ δ₁ δ₂ hσ hσ8 hδ₁ hδ₁le hδ₂ hAc hBc hABval hAB1 hAB2 hAsin hBsin hAend hBend hvan
  have hσ' : σ ≤ 1 / 2 := by linarith
  have hAval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ := fun β hβ => (hABval β hβ).1
  have hBval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ := fun β hβ => (hABval β hβ).2
  have hA1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv A β| ≤ δ₁ :=
    fun β hβ => (hAB1 β hβ).1
  have hB1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv B β| ≤ δ₁ :=
    fun β hβ => (hAB1 β hβ).2
  have hA2 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv A) β| ≤ δ₂ :=
    fun β hβ => (hAB2 β hβ).1
  have hB2 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv B) β| ≤ δ₂ :=
    fun β hβ => (hAB2 β hβ).2
  have hsum0 : 0 ≤ σ + δ₁ + δ₂ := by linarith
  have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine ⟨Work.OddCurve.LowSlope.solR n A B, Work.OddCurve.LowSlope.solr n A B,
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact solR_contDiffOn n hn hσ' hAc hBc hAval hBval
  · exact solr_contDiffOn n hn hσ' hAc hBc hAval hBval
  · intro α hα
    have hev : solR n A B =ᶠ[𝓝 α] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hα] with β hβ
      exact solR_eq_one_of_data_eq_zero n (hvan β hβ).1 (hvan β hβ).2
    exact ((contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq hev).contDiffWithinAt
  · intro α hα
    have hev : solr n A B =ᶠ[𝓝 α] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hα] with β hβ
      exact solr_eq_one_of_data_eq_zero n (hvan β hβ).1 (hvan β hβ).2
    exact ((contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq hev).contDiffWithinAt
  · intro β hβ
    have habs : |solW n A B β| < 1 := by
      have h := solW_abs_le hn hσ' hAval hBval hβ
      linarith
    have hu : 0 < solU A β := by
      have h := solU_mem hσ' hAval hβ
      linarith [h.1]
    obtain ⟨h1, h2⟩ := sol_system n habs hu
    exact ⟨by rw [h1], by rw [h2]⟩
  · rw [solR_end n hAend hBend, solr_end n hAend hBend]
  · intro α hα
    obtain ⟨v1, v2, d1, d2, dd1, dd2⟩ :=
      rsc2_bounds_core_small n hn hσ hσ8 hδ₁ hδ₂ hδ₁le hAc hBc hAval hBval hA1 hB1 hA2 hB2 hα
    have hs1 := solR_deriv_le_sin n hn hσ hσ8 hAc hBc hAval hBval hδ₁ hAsin hBsin α hα
    have hs2 := solr_deriv_le_sin n hn hσ hσ8 hAc hBc hAval hBval hδ₁ hAsin hBsin α hα
    have hsinle : Real.sin α ≤ α := Real.sin_le hα.1
    have hv1 : 1 - 4 * (σ + δ₁ + δ₂) ≤ solR n A B α := by
      have h := neg_le_of_abs_le v1
      have hle : 3 * σ / ((n : ℝ) + 1) ≤ 4 * (σ + δ₁ + δ₂) := by
        have h2 : 3 * σ / ((n : ℝ) + 1) ≤ 3 * σ := div_le_self (by linarith) hN1
        linarith
      linarith
    have hv2 : 1 - 4 * (σ + δ₁ + δ₂) ≤ solr n A B α := by
      have h := neg_le_of_abs_le v2
      have hle : 3 * σ / ((n : ℝ) + 1) ≤ 4 * (σ + δ₁ + δ₂) := by
        have h2 : 3 * σ / ((n : ℝ) + 1) ≤ 3 * σ := div_le_self (by linarith) hN1
        linarith
      linarith
    have hd1' : |deriv (solR n A B) α| ≤ 4 * (σ + δ₁ + δ₂) * α := by
      have hstep : 3 * δ₁ * Real.sin α ≤ 4 * (σ + δ₁ + δ₂) * α := by
        have h1 : 3 * δ₁ * Real.sin α ≤ 3 * δ₁ * α :=
          mul_le_mul_of_nonneg_left hsinle (by linarith)
        have h2 : 3 * δ₁ * α ≤ 4 * (σ + δ₁ + δ₂) * α :=
          mul_le_mul_of_nonneg_right (by linarith) hα.1
        linarith
      linarith [hs1, hstep]
    have hd2' : |deriv (solr n A B) α| ≤ 4 * (σ + δ₁ + δ₂) * α := by
      have hstep : 3 * δ₁ * Real.sin α ≤ 4 * (σ + δ₁ + δ₂) * α := by
        have h1 : 3 * δ₁ * Real.sin α ≤ 3 * δ₁ * α :=
          mul_le_mul_of_nonneg_left hsinle (by linarith)
        have h2 : 3 * δ₁ * α ≤ 4 * (σ + δ₁ + δ₂) * α :=
          mul_le_mul_of_nonneg_right (by linarith) hα.1
        linarith
      linarith [hs2, hstep]
    have hdd1' : |deriv (deriv (solR n A B)) α| ≤ 4 * (σ + δ₁ + δ₂) := by
      have h2 : 4 * (σ + δ₁ + δ₂) / ((n : ℝ) + 1) ≤ 4 * (σ + δ₁ + δ₂) :=
        div_le_self (by linarith) hN1
      linarith [dd1, h2]
    have hdd2' : |deriv (deriv (solr n A B)) α| ≤ 4 * (σ + δ₁ + δ₂) := by
      have h2 : 4 * (σ + δ₁ + δ₂) / ((n : ℝ) + 1) ≤ 4 * (σ + δ₁ + δ₂) :=
        div_le_self (by linarith) hN1
      linarith [dd2, h2]
    exact ⟨hv1, hv2, hd1', hd2', hdd1', hdd2'⟩
  · have hIoo : Set.Ioo (Real.pi / 2 - 1 / 4) (Real.pi / 2 + 1 / 4) ∈ 𝓝 (Real.pi / 2) :=
      isOpen_Ioo.mem_nhds ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hR1 : solR n A B =ᶠ[𝓝 (Real.pi / 2)] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [hIoo] with β hβ
      exact solR_eq_one_of_data_eq_zero n (hvan β hβ).1 (hvan β hβ).2
    have hr1 : solr n A B =ᶠ[𝓝 (Real.pi / 2)] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [hIoo] with β hβ
      exact solr_eq_one_of_data_eq_zero n (hvan β hβ).1 (hvan β hβ).2
    have hdR : deriv (solR n A B) (Real.pi / 2) = 0 := by
      rw [Filter.EventuallyEq.deriv_eq hR1, deriv_const]
    have hdr : deriv (solr n A B) (Real.pi / 2) = 0 := by
      rw [Filter.EventuallyEq.deriv_eq hr1, deriv_const]
    rw [hdR, hdr, solR_end n hAend hBend, solr_end n hAend hBend]
    norm_num

end Work.OddVolterra.Free
