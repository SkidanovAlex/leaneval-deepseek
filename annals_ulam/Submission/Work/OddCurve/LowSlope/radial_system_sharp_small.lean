import Mathlib
import Submission.Work.OddCurve.LowSlope.radial_system_sharp_c2
import Submission.Work.OddRadon.RadialDefs

set_option maxHeartbeats 1000000

namespace Work.OddCurve.LowSlope

/-! ## Sharpened second-derivative bound -/

/-- **The sharp second-derivative bound, with the smallness split off.** -/
lemma rsc2_deriv2_bound_small (n : ℕ) (_hn : 1 ≤ n) {R r A B : ℝ → ℝ} {σ δ₁ δ₂ α : ℝ}
    (hσ : 0 ≤ σ) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ₁le : δ₁ ≤ 1 / 20)
    (hbox : SharpBox n (R α) (r α))
    (hRsq : (deriv R α) ^ 2 ≤ (26 / 5) * δ₁ ^ 2 / (((2 * n + 1 : ℕ) : ℝ)) ^ 2)
    (hrsq : (deriv r α) ^ 2 ≤ (26 / 5) * δ₁ ^ 2 / (((2 * n + 1 : ℕ) : ℝ)) ^ 2)
    (hA2 : |deriv (deriv A) α| ≤ δ₂) (hB2 : |deriv (deriv B) α| ≤ δ₂)
    (hform : deriv (deriv R) α
      = deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))
        + r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))
        - (deriv R α) ^ 2 * ((((2 * n + 2 : ℕ) : ℝ) - 1) - r α / (R α + r α)) / R α
        - (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)) :
    |deriv (deriv R) α| ≤ 4 * (σ + δ₁ + δ₂) / ((n : ℝ) + 1) := by
  set N : ℝ := (n : ℝ) + 1 with hNdef
  set tA : ℝ := deriv (deriv A) α / (↑(2 * n + 2) * R α ^ (2 * n) * (R α + r α)) with htA
  set tB : ℝ := r α * deriv (deriv B) α / (↑(2 * n + 1) * R α ^ (2 * n) * (R α + r α)) with htB
  set tC : ℝ := (deriv R α) ^ 2 * ((((2 * n + 2 : ℕ) : ℝ) - 1) - r α / (R α + r α)) / R α
    with htC
  set tD : ℝ := (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α) with htD
  have hNpos : 0 < N := by rw [hNdef]; positivity
  have hT1 : |tA| ≤ 9 * δ₂ / (25 * N) := by rw [htA, hNdef]; exact rsc2_term1 n hδ₂ hbox hA2
  have hT2 : |tB| ≤ 108 * δ₂ / (125 * N) := by rw [htB, hNdef]; exact rsc2_term2 n hδ₂ hbox hB2
  have hT3 : |tC| ≤ (156 / 25) * δ₁ ^ 2 / N := by
    rw [htC, hNdef]; exact rsc2_term3 n hδ₁ hbox hRsq
  have hT4 : |tD| ≤ (117 / 25) * δ₁ ^ 2 / N := by
    rw [htD, hNdef]; exact rsc2_term4 n hδ₁ hbox hrsq
  have htri : |tA + tB - tC - tD| ≤ |tA| + |tB| + |tC| + |tD| := by
    have h := abs_sub (tA + tB) (tC + tD)
    have h1 := abs_add_le tA tB
    have h2 := abs_add_le tC tD
    calc |tA + tB - tC - tD| = |(tA + tB) - (tC + tD)| := by ring_nf
      _ ≤ |tA + tB| + |tC + tD| := h
      _ ≤ (|tA| + |tB|) + (|tC| + |tD|) := add_le_add h1 h2
      _ = |tA| + |tB| + |tC| + |tD| := by ring
  have hsum : 9 * δ₂ / (25 * N) + 108 * δ₂ / (125 * N) + (156 / 25) * δ₁ ^ 2 / N
      + (117 / 25) * δ₁ ^ 2 / N ≤ 4 * (σ + δ₁ + δ₂) / N := by
    have h1 : 9 * δ₂ / (25 * N) + 108 * δ₂ / (125 * N) + (156 / 25) * δ₁ ^ 2 / N
          + (117 / 25) * δ₁ ^ 2 / N
        = (153 / 125) * (δ₂ / N) + (273 / 25) * (δ₁ ^ 2 / N) := by
      field_simp
      ring
    rw [h1]
    have hsq : δ₁ ^ 2 ≤ δ₁ / 20 := by nlinarith only [hδ₁, hδ₁le]
    have ha : (273 / 25 : ℝ) * δ₁ ^ 2 ≤ 4 * δ₁ := by nlinarith only [hsq, hδ₁]
    have hb : (153 / 125 : ℝ) * δ₂ ≤ 4 * δ₂ := by nlinarith only [hδ₂]
    have hkey : (153 / 125 : ℝ) * δ₂ + (273 / 25) * δ₁ ^ 2 ≤ 4 * (σ + δ₁ + δ₂) := by
      linarith only [ha, hb, hσ, hδ₁, hδ₂]
    have h3 : (153 / 125) * (δ₂ / N) + (273 / 25) * (δ₁ ^ 2 / N)
        = ((153 / 125) * δ₂ + (273 / 25) * δ₁ ^ 2) / N := by
      field_simp
    rw [h3]
    exact div_le_div_of_nonneg_right hkey hNpos.le
  have hmain : |deriv (deriv R) α| ≤ 9 * δ₂ / (25 * N) + 108 * δ₂ / (125 * N)
      + (156 / 25) * δ₁ ^ 2 / N + (117 / 25) * δ₁ ^ 2 / N := by
    rw [hform]
    linarith [htri, hT1, hT2, hT3, hT4]
  linarith [hmain, hsum]


/-- **The pointwise quantitative bounds** for `(solR, solr)` with the sharp second-derivative
constant `4`. -/
lemma rsc2_bounds_core_small (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ δ₁ δ₂ β : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ₁le : δ₁ ≤ 1 / 20)
    (hAc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hBc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hAval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hBval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hA1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv A β| ≤ δ₁)
    (hB1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv B β| ≤ δ₁)
    (hA2 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv A) β| ≤ δ₂)
    (hB2 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv B) β| ≤ δ₂)
    (hβ : β ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |solR n A B β - 1| ≤ 3 * σ / ((n : ℝ) + 1) ∧
    |solr n A B β - 1| ≤ 3 * σ / ((n : ℝ) + 1) ∧
    |deriv (solR n A B) β| ≤ 3 * δ₁ / ((n : ℝ) + 1) ∧
    |deriv (solr n A B) β| ≤ 3 * δ₁ / ((n : ℝ) + 1) ∧
    |deriv (deriv (solR n A B)) β| ≤ 4 * (σ + δ₁ + δ₂) / ((n : ℝ) + 1) ∧
    |deriv (deriv (solr n A B)) β| ≤ 4 * (σ + δ₁ + δ₂) / ((n : ℝ) + 1) := by
  have hσ' : σ ≤ 1 / 2 := by linarith
  have hX := solX_window_sharp n hn hσ hσ8 hAval hBval hβ
  obtain ⟨hbox, hvR, hvr⟩ := sol_box_value_sharp n hn hσ hσ8 hAval hBval hX hβ
  have hRpos : 0 < solR n A B β := solR_pos n hn hσ' hAval hBval hβ
  have hrpos : 0 < solr n A B β := solr_pos n hn hσ' hAval hBval hβ
  have hmem : β ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hβ.1], by linarith [hβ.2, Real.pi_pos]⟩
  have hAcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A β :=
    hAc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)
  have hBcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B β :=
    hBc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)
  have hRcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solR n A B) β :=
    solR_contDiffAt n hn hσ' hAc hBc hAval hBval hβ
  have hrcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solr n A B) β :=
    solr_contDiffAt n hn hσ' hAc hBc hAval hBval hβ
  have hsys : ∀ᶠ γ in nhds β, (solR n A B) γ ^ (2 * n + 2) + (solr n A B) γ ^ (2 * n + 2)
      = 2 + A γ ∧ (solR n A B) γ ^ (2 * n + 1) - (solr n A B) γ ^ (2 * n + 1) = B γ :=
    sol_system_eventually n hn hσ' hAc hBc hAval hBval hβ
  obtain ⟨hRform, hrform⟩ := sol_deriv_formulas n hRcd hrcd hAcd hBcd hRpos hrpos hsys
  obtain ⟨hRd1, hRsq⟩ :=
    rsc2_deriv1_bound n hn hδ₁ hRpos hrpos hbox (hA1 β hβ) (hB1 β hβ) hRform
  -- the system with the two radial functions exchanged and `B` negated
  have hsys_sw : ∀ᶠ γ in nhds β, (solr n A B) γ ^ (2 * n + 2) + (solR n A B) γ ^ (2 * n + 2)
      = 2 + A γ ∧ (solr n A B) γ ^ (2 * n + 1) - (solR n A B) γ ^ (2 * n + 1)
        = (fun y => -B y) γ := by
    filter_upwards [hsys] with γ hγ
    exact ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
  have hB1' : |deriv (fun y => -B y) β| ≤ δ₁ := by
    rw [sdb_deriv_neg_fun B]
    simpa using hB1 β hβ
  have hB2' : |deriv (deriv (fun y => -B y)) β| ≤ δ₂ := by
    rw [show deriv (fun y : ℝ => -B y) = fun y : ℝ => -deriv B y from sdb_deriv_neg_fun B,
      show deriv (fun y : ℝ => -deriv B y) = fun y : ℝ => -deriv (deriv B) y from
        sdb_deriv_neg_fun (deriv B)]
    simpa using hB2 β hβ
  have hrform' : deriv (solr n A B) β = (((2 * n + 1 : ℕ) : ℝ) * deriv A β +
        ((2 * n + 2 : ℕ) : ℝ) * solR n A B β * deriv (fun y => -B y) β)
      / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * solr n A B β ^ (2 * n)
          * (solr n A B β + solR n A B β)) := by
    rw [hrform, sdb_deriv_neg_fun B]
    congr 1 <;> ring
  obtain ⟨hrd1, hrsq⟩ :=
    rsc2_deriv1_bound n hn hδ₁ hrpos hRpos (sharpBox_swap hbox) (hA1 β hβ) hB1' hrform'
  have hformR := sol_deriv2_R_formula_aux n hn hRcd hrcd hAcd hBcd hRpos hrpos hsys
  have hformr := sol_deriv2_R_formula_aux n hn hrcd hRcd hAcd hBcd.neg hrpos hRpos hsys_sw
  have hRd2 := rsc2_deriv2_bound_small n hn hσ.le hδ₁ hδ₂ hδ₁le hbox hRsq hrsq
    (hA2 β hβ) (hB2 β hβ) hformR
  have hrd2 := rsc2_deriv2_bound_small n hn hσ.le hδ₁ hδ₂ hδ₁le (sharpBox_swap hbox) hrsq hRsq
    (hA2 β hβ) hB2' hformr
  exact ⟨hvR, hvr, hRd1, hrd1, hRd2, hrd2⟩


theorem radial_system_sharp_small (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A B : ℝ → ℝ) (σ δ₁ δ₂ : ℝ),
      0 ≤ σ → 0 ≤ δ₁ → 0 ≤ δ₂ → K * (σ + δ₁ + δ₂) ≤ 1 →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) →
      (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A α| ≤ σ ∧ |deriv A α| ≤ δ₁ ∧ |deriv (deriv A) α| ≤ δ₂) →
      (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B α| ≤ σ ∧ |deriv B α| ≤ δ₁ ∧ |deriv (deriv B) α| ≤ δ₂) →
      A (Real.pi / 2) = 0 → B (Real.pi / 2) = 0 →
      ∃ R r : ℝ → ℝ,
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2)) ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r (Set.Icc 0 (Real.pi / 2)) ∧
        Work.OddRadon.RadialSystem n (fun α => (2 + A α) * Real.cos α ^ 2)
          (fun α => B α * Real.cos α) R r ∧
        R (Real.pi / 2) = 1 ∧ r (Real.pi / 2) = 1 ∧
        ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          |R α - 1| ≤ 4 * σ / ((n : ℝ) + 1) ∧ |r α - 1| ≤ 4 * σ / ((n : ℝ) + 1) ∧
          |deriv R α| ≤ 4 * (σ + δ₁) / ((n : ℝ) + 1) ∧
          |deriv r α| ≤ 4 * (σ + δ₁) / ((n : ℝ) + 1) ∧
          |deriv (deriv R) α| ≤ 4 * (σ + δ₁ + δ₂) / ((n : ℝ) + 1) ∧
          |deriv (deriv r) α| ≤ 4 * (σ + δ₁ + δ₂) / ((n : ℝ) + 1) := by
  refine ⟨20, by norm_num, ?_⟩
  intro A B σ δ₁ δ₂ hσ hδ₁ hδ₂ hC hAc hBc hAll hBll hAend hBend
  have hAval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ := fun β hβ => (hAll β hβ).1
  have hBval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ := fun β hβ => (hBll β hβ).1
  have hA1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv A β| ≤ δ₁ :=
    fun β hβ => (hAll β hβ).2.1
  have hB1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv B β| ≤ δ₁ :=
    fun β hβ => (hBll β hβ).2.1
  have hA2 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv A) β| ≤ δ₂ :=
    fun β hβ => (hAll β hβ).2.2
  have hB2 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv B) β| ≤ δ₂ :=
    fun β hβ => (hBll β hβ).2.2
  have hσ20 : σ ≤ 1 / 20 := by nlinarith only [hC, hδ₁, hδ₂]
  have hδ₁20 : δ₁ ≤ 1 / 20 := by nlinarith only [hC, hσ, hδ₂]
  have hδ₂20 : δ₂ ≤ 1 / 20 := by nlinarith only [hC, hσ, hδ₁]
  have hδ₁1 : δ₁ ≤ 1 := by linarith only [hδ₁20]
  by_cases hσ0 : σ = 0
  · subst hσ0
    refine ⟨fun _ => 1, fun _ => 1, contDiffOn_const, contDiffOn_const, ?_, rfl, rfl, ?_⟩
    · intro β hβ
      have hA : A β = 0 := abs_nonpos_iff.mp (hAll β hβ).1
      have hB : B β = 0 := abs_nonpos_iff.mp (hBll β hβ).1
      constructor
      · show (1 ^ (2 * n + 2) + 1 ^ (2 * n + 2)) * Real.cos β ^ 2 = (2 + A β) * Real.cos β ^ 2
        rw [hA]
        norm_num
      · show (1 ^ (2 * n + 1) - 1 ^ (2 * n + 1)) * Real.cos β = B β * Real.cos β
        rw [hB]
        norm_num
    · intro β hβ
      refine ⟨by simp, by simp, ?_, ?_, ?_, ?_⟩
      · rw [show deriv (fun _ : ℝ => (1 : ℝ)) β = 0 from deriv_const β 1]
        simp only [abs_zero]
        positivity
      · rw [show deriv (fun _ : ℝ => (1 : ℝ)) β = 0 from deriv_const β 1]
        simp only [abs_zero]
        positivity
      · have h0 : deriv (deriv (fun _ : ℝ => (1 : ℝ))) β = 0 := by simp
        rw [h0]
        simp only [abs_zero]
        positivity
      · have h0 : deriv (deriv (fun _ : ℝ => (1 : ℝ))) β = 0 := by simp
        rw [h0]
        simp only [abs_zero]
        positivity
  · have hσpos : 0 < σ := lt_of_le_of_ne' hσ hσ0
    have hσ8 : σ ≤ 1 / 8 := by linarith only [hσ20]
    have hσ' : σ ≤ 1 / 2 := by linarith only [hσ8]
    refine ⟨fun α => solR n A B (Work.OddRadon.clampPi α),
      fun α => solr n A B (Work.OddRadon.clampPi α), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (solR_contDiffOn n hn hσ' hAc hBc hAval hBval).congr (fun α hα => by
        show solR n A B (Work.OddRadon.clampPi α) = solR n A B α
        rw [Work.OddRadon.clampPi_of_mem hα])
    · exact (solr_contDiffOn n hn hσ' hAc hBc hAval hBval).congr (fun α hα => by
        show solr n A B (Work.OddRadon.clampPi α) = solr n A B α
        rw [Work.OddRadon.clampPi_of_mem hα])
    · intro β hβ
      have habs : |solW n A B β| < 1 := by
        have h := solW_abs_le hn hσ' hAval hBval hβ
        linarith only [h]
      have hu : 0 < solU A β := by
        have h := solU_mem hσ' hAval hβ
        linarith only [h.1]
      obtain ⟨h1, h2⟩ := sol_system n habs hu
      constructor
      · show (solR n A B (Work.OddRadon.clampPi β) ^ (2 * n + 2)
            + solr n A B (Work.OddRadon.clampPi β) ^ (2 * n + 2)) * Real.cos β ^ 2
          = (2 + A β) * Real.cos β ^ 2
        rw [Work.OddRadon.clampPi_of_mem hβ, h1]
      · show (solR n A B (Work.OddRadon.clampPi β) ^ (2 * n + 1)
            - solr n A B (Work.OddRadon.clampPi β) ^ (2 * n + 1)) * Real.cos β
          = B β * Real.cos β
        rw [Work.OddRadon.clampPi_of_mem hβ, h2]
    · show solR n A B (Work.OddRadon.clampPi (Real.pi / 2)) = 1
      rw [Work.OddRadon.clampPi_of_mem
        ⟨by linarith only [Real.pi_pos], le_refl (Real.pi / 2)⟩]
      exact solR_end n hAend hBend
    · show solr n A B (Work.OddRadon.clampPi (Real.pi / 2)) = 1
      rw [Work.OddRadon.clampPi_of_mem
        ⟨by linarith only [Real.pi_pos], le_refl (Real.pi / 2)⟩]
      exact solr_end n hAend hBend
    · intro β hβ
      dsimp only
      obtain ⟨hv1, hv2, hd1, hd2, hdd1, hdd2⟩ :=
        rsc2_bounds_core_small n hn hσpos hσ8 hδ₁ hδ₂ hδ₁20 hAc hBc hAval hBval hA1 hB1 hA2 hB2 hβ
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Work.OddRadon.clampPi_of_mem hβ]
        refine le_trans hv1 ?_
        apply div_le_div_of_nonneg_right (by linarith only [hσ]) (by positivity)
      · rw [Work.OddRadon.clampPi_of_mem hβ]
        refine le_trans hv2 ?_
        apply div_le_div_of_nonneg_right (by linarith only [hσ]) (by positivity)
      · rcases lt_trichotomy β 0 with hlt | heq | hgt
        · exact absurd hβ.1 (not_le.mpr hlt)
        · subst heq
          rw [Work.OddRadon.deriv_comp_clampPi_eq_zero le_rfl]
          simp only [abs_zero]
          exact div_nonneg (mul_nonneg (by norm_num) (by linarith only [hσ, hδ₁])) (by positivity)
        · rcases lt_trichotomy β (Real.pi / 2) with hlt2 | heq2 | hgt2
          · have hev : (fun t => solR n A B (Work.OddRadon.clampPi t))
                =ᶠ[nhds β] (solR n A B) := by
              filter_upwards [isOpen_Ioo.mem_nhds
                (show β ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hgt, hlt2⟩)] with t ht
              show solR n A B (Work.OddRadon.clampPi t) = solR n A B t
              rw [Work.OddRadon.clampPi_of_mem ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
            rw [hev.deriv_eq]
            refine le_trans hd1 ?_
            apply div_le_div_of_nonneg_right (by linarith only [hδ₁, hσ]) (by positivity)
          · subst heq2
            rw [Work.OddRadon.deriv_comp_clampPi_eq_zero' le_rfl]
            simp only [abs_zero]
            exact div_nonneg (mul_nonneg (by norm_num) (by linarith only [hσ, hδ₁])) (by positivity)
          · exact absurd hβ.2 (not_le.mpr hgt2)
      · rcases lt_trichotomy β 0 with hlt | heq | hgt
        · exact absurd hβ.1 (not_le.mpr hlt)
        · subst heq
          rw [Work.OddRadon.deriv_comp_clampPi_eq_zero le_rfl]
          simp only [abs_zero]
          exact div_nonneg (mul_nonneg (by norm_num) (by linarith only [hσ, hδ₁])) (by positivity)
        · rcases lt_trichotomy β (Real.pi / 2) with hlt2 | heq2 | hgt2
          · have hev : (fun t => solr n A B (Work.OddRadon.clampPi t))
                =ᶠ[nhds β] (solr n A B) := by
              filter_upwards [isOpen_Ioo.mem_nhds
                (show β ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hgt, hlt2⟩)] with t ht
              show solr n A B (Work.OddRadon.clampPi t) = solr n A B t
              rw [Work.OddRadon.clampPi_of_mem ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
            rw [hev.deriv_eq]
            refine le_trans hd2 ?_
            apply div_le_div_of_nonneg_right (by linarith only [hδ₁, hσ]) (by positivity)
          · subst heq2
            rw [Work.OddRadon.deriv_comp_clampPi_eq_zero' le_rfl]
            simp only [abs_zero]
            exact div_nonneg (mul_nonneg (by norm_num) (by linarith only [hσ, hδ₁])) (by positivity)
          · exact absurd hβ.2 (not_le.mpr hgt2)
      · rcases lt_trichotomy β 0 with hlt | heq | hgt
        · exact absurd hβ.1 (not_le.mpr hlt)
        · subst heq
          rw [Work.OddRadon.deriv_deriv_comp_clampPi_eq_zero le_rfl]
          simp only [abs_zero]
          exact div_nonneg (mul_nonneg (by norm_num) (by linarith only [hσ, hδ₁, hδ₂])) (by positivity)
        · rcases lt_trichotomy β (Real.pi / 2) with hlt2 | heq2 | hgt2
          · have hev : (fun t => solR n A B (Work.OddRadon.clampPi t))
                =ᶠ[nhds β] (solR n A B) := by
              filter_upwards [isOpen_Ioo.mem_nhds
                (show β ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hgt, hlt2⟩)] with t ht
              show solR n A B (Work.OddRadon.clampPi t) = solR n A B t
              rw [Work.OddRadon.clampPi_of_mem ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
            rw [(hev.deriv).deriv_eq]
            exact hdd1
          · subst heq2
            rw [Work.OddRadon.deriv_deriv_comp_clampPi_eq_zero' le_rfl]
            simp only [abs_zero]
            exact div_nonneg (mul_nonneg (by norm_num) (by linarith only [hσ, hδ₁, hδ₂])) (by positivity)
          · exact absurd hβ.2 (not_le.mpr hgt2)
      · rcases lt_trichotomy β 0 with hlt | heq | hgt
        · exact absurd hβ.1 (not_le.mpr hlt)
        · subst heq
          rw [Work.OddRadon.deriv_deriv_comp_clampPi_eq_zero le_rfl]
          simp only [abs_zero]
          exact div_nonneg (mul_nonneg (by norm_num) (by linarith only [hσ, hδ₁, hδ₂])) (by positivity)
        · rcases lt_trichotomy β (Real.pi / 2) with hlt2 | heq2 | hgt2
          · have hev : (fun t => solr n A B (Work.OddRadon.clampPi t))
                =ᶠ[nhds β] (solr n A B) := by
              filter_upwards [isOpen_Ioo.mem_nhds
                (show β ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hgt, hlt2⟩)] with t ht
              show solr n A B (Work.OddRadon.clampPi t) = solr n A B t
              rw [Work.OddRadon.clampPi_of_mem ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
            rw [(hev.deriv).deriv_eq]
            exact hdd2
          · subst heq2
            rw [Work.OddRadon.deriv_deriv_comp_clampPi_eq_zero' le_rfl]
            simp only [abs_zero]
            exact div_nonneg (mul_nonneg (by norm_num) (by linarith only [hσ, hδ₁, hδ₂])) (by positivity)
          · exact absurd hβ.2 (not_le.mpr hgt2)

end Work.OddCurve.LowSlope
