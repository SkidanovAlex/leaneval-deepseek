import Mathlib
import Submission.Work.Drive.orbitXH
import Submission.Work.Drive.capSection
import Submission.Work.Drive.exists_planeChart
import Submission.Work.Drive.directionOnly_descent
import Submission.Work.Drive.descent_strip_injective
import Submission.Work.Drive.exists_collar_pair_injective
import Submission.Work.Drive.isPlaneChart_seam_mem_stripImage
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.planeProfiles
import Submission.Work.Drive.exists_profileX
import Submission.Work.Drive.exists_omegaField
import Submission.Work.Drive.gadget_pair_recover
import Submission.Work.Drive.exists_pos_le_on_annulus
import Submission.Work.Drive.exists_radius_le_of_le_sphere

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology
open Filter

noncomputable section


/-- The defining property of `planeChartMap` in the transparent coordinates. -/
lemma cappingSpaceHomeoProj_planeChartMap (r : ℂ → ℝ) (V : ℂ → Eucl 3) (hr : ∀ z : ℂ, 0 < r z)
    (hV : ∀ z : ℂ, V z ≠ 0) (z : ℂ) :
    cappingSpaceHomeoProj (planeChartMap r V hr hV z)
      = (⟨r z, (Set.mem_Ioi.mpr (hr z) : r z ∈ Set.Ioi (0:ℝ))⟩,
          Projectivization.mk ℝ (V z) (hV z)) := by
  have h := Homeomorph.apply_symm_apply cappingSpaceHomeoProj
    ((⟨r z, (Set.mem_Ioi.mpr (hr z) : r z ∈ Set.Ioi (0:ℝ))⟩,
      Projectivization.mk ℝ (V z) (hV z)) : ↑(Set.Ioi (0:ℝ)) × Projectivization ℝ (Eucl 3))
  simpa only [planeChartMap] using h

/-- **The chart point of a cap form.**  If the sphere lift at `z` is the cap form
`capProjVecOf w d` (`‖w‖ = 1`, `‖d‖ ≤ 1`, `w ^ 2 = circleOf θ`), then the chart point is the cap
piece `(r z, θ, d)`. -/
theorem planeChartMap_eq_capPiece {r : ℂ → ℝ} {V : ℂ → Eucl 3} (hr : ∀ z : ℂ, 0 < r z)
    (hV : ∀ z : ℂ, V z ≠ 0) {z w d : ℂ} {θ : UnitAddCircle} (hw : ‖w‖ = 1) (hd : ‖d‖ ≤ 1)
    (htw : w ^ 2 = circleOf θ) (hVz : V z = capProjVecOf w d) :
    planeChartMap r V hr hV z
      = Quotient.mk'' (Sum.inr (⟨(r z, θ, d), hr z, hd⟩ : CapPiece) : ConfigPiece ⊕ CapPiece) := by
  have h2 : cappingSpaceHomeoProj
        (Quotient.mk'' (Sum.inr (⟨(r z, θ, d), hr z, hd⟩ : CapPiece) : ConfigPiece ⊕ CapPiece))
      = (⟨r z, (Set.mem_Ioi.mpr (hr z) : r z ∈ Set.Ioi (0:ℝ))⟩,
         Projectivization.mk ℝ (capProjVecOf w d)
           (capProjVecOf_ne_zero (norm_eq_one_of_sq_eq_circleOf htw) hd)) := by
    have h := cappingSpaceHomeoProj_capPiece (r z, θ, d) (hr z) hd (w := w) htw
    refine h.trans ?_
    refine Prod.ext (Subtype.ext rfl) ?_
    exact projectivizationMk_congr ℝ (Eucl 3)
  have h1 := cappingSpaceHomeoProj_planeChartMap r V hr hV z
  apply cappingSpaceHomeoProj.injective
  rw [h1, h2]
  refine Prod.ext (Subtype.ext rfl) ?_
  refine (Projectivization.mk_eq_mk_iff ℝ (V z) (capProjVecOf w d) (hV z) _).mpr ⟨1, ?_⟩
  rw [one_smul]; exact hVz.symm

/-- **`CapSection` from singleton fibres of `orbitXH`.**  Since `orbitXH` is rotation invariant and
the rotation acts freely, it is enough that the fibres of `orbitXH ∘ Q` on the closed inner disk are
singletons (not that `orbitXH ∘ Q` be injective there). -/
theorem capSection_of_orbitXH_fibres {Q : ℂ → CappingSpace}
    (hfib : ∀ z z' : ℂ, ‖z‖ ≤ 1 / 2 → ‖z'‖ ≤ 1 / 2 →
      orbitXH (Q z) = orbitXH (Q z') → Q z = Q z') :
    CapSection Q := by
  intro z z' w hz hz' heq
  have h1 : orbitXH (Q z) = orbitXH (Q z') := by rw [heq, orbitXH_rotCapping]
  have h2 : Q z = Q z' := hfib z z' hz hz' h1
  have h3 : rotCapping w (Q z') = Q z' := by rw [← heq, h2]
  exact rotCapping_eq_self h3

set_option maxHeartbeats 8000000 in
theorem exists_planeChart_capSection_interior (hU : Submission.Drive.UmlaufProp) (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hW : Work.Drive.WrapData γ) :
    ∃ Q : ℂ → Work.Drive.CappingSpace,
      Work.Drive.IsPlaneChart γ hγne Q ∧ Work.Drive.CapSection Q ∧ Work.Drive.CapInterior Q := by
  classical
  -- ## 0. the descent data and the direction profile
  obtain ⟨M, W, c, hMsm, hWsm, hc, hMval, hWval, hband, hWne, hM0, hW0, hdir, hconst⟩ :=
    directionOnly_descent γ hγ hγne
  obtain ⟨x, hxsm, hxn, hx1, hx16⟩ := exists_profileX
  -- ## 1. the threshold `a` of the band profile
  set a : ℝ := max (1 / 8) (1 / 2 - 2 * c / Real.pi ^ 2) with ha_def
  have ha8 : (1 / 8 : ℝ) ≤ a := le_max_left _ _
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha8
  have ha : a < 1 / 2 := max_lt (by norm_num) (by
    have h : (0 : ℝ) < 2 * c / Real.pi ^ 2 := by positivity
    linarith)
  -- ## 2. the band profile `τ`
  set τ : ℂ → ℝ := fun z => bandProf a ‖z‖ with hτ_def
  have hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ := by
    rw [hτ_def]; exact bandTau_contDiff hapos ha
  have hτ1 : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → τ z = Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2) :=
    fun z hz => bandTau_eq ha hz
  have hτle : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → τ z ≤ 0 := fun z hz => bandTau_nonpos hz
  have habs : ∀ ρ : ℝ, ρ ≤ 1 / 2 → |bandProf a ρ| ≤ c := by
    intro ρ hρ
    have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
    have hle : Real.pi ^ 2 / 2 * (1 / 2 - a) ≤ c := by
      have h1 : 1 / 2 - a ≤ 2 * c / Real.pi ^ 2 := by
        have h2 := le_max_right (1 / 8 : ℝ) (1 / 2 - 2 * c / Real.pi ^ 2)
        have h3 := ha_def
        rw [h3] at *
        linarith
      calc Real.pi ^ 2 / 2 * (1 / 2 - a) ≤ Real.pi ^ 2 / 2 * (2 * c / Real.pi ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = c := by field_simp
    refine le_trans ?_ hle
    by_cases h : ρ ≤ a
    · rw [bandProf_eq_zero ha h, abs_zero]; positivity
    · have hρa : a ≤ ρ := le_of_not_ge h
      have h1 : bandProf a ρ = -(pStep a (1 / 2) ρ * (Real.pi ^ 2 / 2 * (1 / 2 - ρ))) := by
        rw [bandProf]; ring
      rw [h1, abs_neg, abs_of_nonneg (mul_nonneg (pStep_nonneg _ _ _) (by nlinarith))]
      have h2 : pStep a (1 / 2) ρ ≤ 1 := pStep_le_one _ _ _
      have h3 : (0 : ℝ) ≤ Real.pi ^ 2 / 2 * (1 / 2 - ρ) := by nlinarith
      have h4 : Real.pi ^ 2 / 2 * (1 / 2 - ρ) ≤ Real.pi ^ 2 / 2 * (1 / 2 - a) := by
        nlinarith
      nlinarith
  have hτge : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → -c ≤ τ z := by
    intro z hz
    have := habs ‖z‖ hz
    rw [abs_le] at this
    exact this.1
  -- ## 3. the direction profile is the unit direction above `1/8`
  have hxnorm : ∀ z : ℂ, (1 / 8 : ℝ) ≤ ‖z‖ → ‖x z‖ = 1 := by
    intro z hz
    rw [hx1 z hz, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
    exact div_self (ne_of_gt (lt_of_lt_of_le (by norm_num) hz))
  -- ## 4. the collar of injectivity of `(pcA, pcDc)`
  obtain ⟨ρin, hρina, hρin_lt, hcollar⟩ :=
    exists_collar_pair_injective (γ := γ) hγ hγne M W c hMsm hWsm hc hMval hWval hband hWne hM0 hW0
      hdir ha x τ (fun z hz => hx1 z (le_trans ha8 hz)) (fun z => rfl)
  -- ## 5. the radii
  set m : ℝ := max (max ρin a) (1 / 16) with hm_def
  have hm_pos : 0 < m := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hm_lt : m < 1 / 2 := max_lt (max_lt hρin_lt ha) (by norm_num)
  set ρχ : ℝ := (m + 1 / 2) / 2 with hρχ_def
  set ργ : ℝ := (ρχ + 1 / 2) / 2 with hργ_def
  have hm_lt_ρχ : m < ρχ := by rw [hρχ_def]; linarith
  have hρχ_lt_ργ : ρχ < ργ := by rw [hργ_def]; linarith
  have hργ_lt_half : ργ < 1 / 2 := by rw [hργ_def, hρχ_def]; linarith
  have hρχ_pos : 0 < ρχ := by rw [hρχ_def]; linarith
  have hργ_pos : 0 < ργ := lt_trans hρχ_pos hρχ_lt_ργ
  have hρχ_in : ρin < ρχ := lt_of_le_of_lt (le_trans (le_max_left ρin a) (le_max_left _ _)) hm_lt_ρχ
  have hρχ_a : a < ρχ := lt_of_le_of_lt (le_trans (le_max_right ρin a) (le_max_left _ _)) hm_lt_ρχ
  have hχ_thr : (1 / 16 : ℝ) < ρχ :=
    lt_of_le_of_lt (le_max_right (max ρin a) (1 / 16)) hm_lt_ρχ
  have hρin_ργ : ρin < ργ := lt_trans hρχ_in hρχ_lt_ργ
  -- ## 6. the field `H`, its positivity on the annulus `[ρχ, ργ]`
  set H : ℂ → ℝ := fun z => -(τ z) * Complex.normSq (W (x z, τ z)) with hH_def
  have hHsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H := by
    rw [hH_def]
    exact (hτsm.neg).mul (Neutral.contDiff_complexNormSq.comp
      (hWsm.comp (hxsm.prodMk hτsm)))
  have hHcont : Continuous H := hHsm.continuous
  have hHhalf : ∀ z : ℂ, ‖z‖ = 1 / 2 → H z = 0 := by
    intro z hz
    have hτ0 : τ z = 0 := by
      rw [hτ1 z (le_of_eq hz.symm), hz]; ring
    rw [hH_def]; simp only [hτ0, neg_zero, zero_mul]
  have hHnonneg : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → 0 ≤ H z := by
    intro z hz
    rw [hH_def]
    exact mul_nonneg (neg_nonneg.mpr (hτle z hz)) (Complex.normSq_nonneg _)
  have hHpos_of : ∀ z : ℂ, a < ‖z‖ → ‖z‖ < 1 / 2 → 0 < H z := by
    intro z hz1 hz2
    have hτneg : τ z < 0 := bandTau_neg ha hz1 hz2
    have hz8 : (1 / 8 : ℝ) ≤ ‖z‖ := le_trans ha8 (le_of_lt hz1)
    have hxnz : (1 / 8 : ℝ) ≤ ‖x z‖ := by rw [hxnorm z hz8]; norm_num
    have hx2 : ‖x z‖ ≤ 2 := by rw [hxnorm z hz8]; norm_num
    have hWnz : W (x z, τ z) ≠ 0 := hWne (x z) (τ z) hxnz hx2 (hτge z (le_of_lt hz2)) hτneg
    have hns : 0 < Complex.normSq (W (x z, τ z)) := Complex.normSq_pos.mpr hWnz
    rw [hH_def]
    exact mul_pos (neg_pos.mpr hτneg) hns
  have hHann : ∀ z : ℂ, ρχ ≤ ‖z‖ → ‖z‖ ≤ ργ → 0 < H z :=
    fun z h1 h2 => hHpos_of z (lt_of_lt_of_le hρχ_a h1) (lt_of_le_of_lt h2 hργ_lt_half)
  -- ## 7. the two quantitative choices
  obtain ⟨q, hqpos, hq⟩ : ∃ q : ℝ, 0 < q ∧ ∀ z : ℂ, ρχ ≤ ‖z‖ → ‖z‖ ≤ ργ → q ≤ H z :=
    exists_pos_le_on_annulus hHcont hHann
  have hq2pos : (0 : ℝ) < q / 2 := by linarith
  obtain ⟨σ₁, hργ_σ₁, hσ₁_half, hσ₁le⟩ :
      ∃ σ₁ : ℝ, ργ < σ₁ ∧ σ₁ < 1 / 2 ∧
        ∀ z : ℂ, σ₁ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → H z ≤ q / 2 :=
    exists_radius_le_of_le_sphere hHcont hργ_lt_half (fun z hz => by rw [hHhalf z hz]; linarith)
  set σ₂ : ℝ := (σ₁ + 1 / 2) / 2 with hσ₂_def
  set σs : ℝ := (σ₁ + σ₂) / 2 with hσs_def
  have hσ₁_σ₂ : σ₁ < σ₂ := by rw [hσ₂_def]; linarith
  have hσ₂_half : σ₂ < 1 / 2 := by rw [hσ₂_def]; linarith
  have hσs_lt_σ₂ : σs < σ₂ := by rw [hσs_def]; linarith
  have hσ₁_lt_σs : σ₁ < σs := by rw [hσs_def]; linarith
  have hσ₁_pos : 0 < σ₁ := lt_of_lt_of_le hργ_pos (le_of_lt hργ_σ₁)
  have hσ₂_pos : 0 < σ₂ := lt_trans hσ₁_pos hσ₁_σ₂
  -- ## 8. the smooth unit field `Ω` agreeing with `pcW` on `[σ₁, σ₂]`
  set ρ₀ : ℝ := (1 / 8 + σ₁) / 2 with hρ₀_def
  have hρ₀_lt_σ₁ : ρ₀ < σ₁ := by rw [hρ₀_def]; linarith
  have hρ₀_gt : (1 / 8 : ℝ) < ρ₀ := by rw [hρ₀_def]; linarith
  have hρ₀_pos : 0 < ρ₀ := lt_trans (by norm_num) hρ₀_gt
  have hρ₀_half : ρ₀ < 1 / 2 := lt_trans hρ₀_lt_σ₁ hσ₁_half
  have hPcDisc : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → PcDisc M W x τ z := by
    intro z h1 h2
    have hz8 : (1 / 8 : ℝ) ≤ ‖z‖ := le_trans (le_of_lt hρ₀_gt) h1
    refine PcDisc.of_disc (c := c) (fun x τ hx1' hx2 hc' hτ => hband x τ (by linarith) hx2 hc' hτ)
      (fun x τ hx1' hx2 hc' hτ => hWne x τ (by linarith) hx2 hc' hτ)
      (fun x hx1' hx2 => hM0 x (by linarith) hx2) (fun x hx1' hx2 => hW0 x (by linarith) hx2)
      (by rw [hxnorm z hz8]; norm_num) (by rw [hxnorm z hz8])
      (hτge z h2) (hτle z h2)
  have hWsm_ann : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 →
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcW M W x τ) z :=
    fun z h1 h2 => (hPcDisc z h1 h2).dW hMsm hWsm hxsm hτsm
  have hWunit_ann : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → ‖pcW M W x τ z‖ = 1 :=
    fun z h1 h2 => (hPcDisc z h1 h2).normW'
  have hM0q : ∀ y : ℂ, 1 / 4 ≤ ‖y‖ → ‖y‖ ≤ 1 → M (y, 0) ≠ 0 :=
    fun y h1 h2 => hM0 y (by linarith) h2
  have hW0q : ∀ y : ℂ, 1 / 4 ≤ ‖y‖ → ‖y‖ ≤ 1 → W (y, 0) ≠ 0 :=
    fun y h1 h2 => hW0 y (by linarith) h2
  have hMne0 : ∀ y : ℂ, ‖y‖ = 1 → M (y, 0) ≠ 0 := by
    intro y hy
    exact hM0 y (by rw [hy]; norm_num) (by rw [hy])
  have hWne0 : ∀ y : ℂ, ‖y‖ = 1 → W (y, 0) ≠ 0 := by
    intro y hy
    exact hW0 y (by rw [hy]; norm_num) (by rw [hy])
  obtain ⟨Ω, hΩsm, hΩunit, hΩeq⟩ :=
    exists_omegaField (γ := γ) (hU := hU) (hWrap := hW) (hγ := hγ) (hγne := hγne)
      (M := M) (W := W) hMsm hWsm hMval hWval hMne0 hWne0 hM0q hW0q
      (x := x) (τ := τ) (fun z hz => hx1 z (le_trans (by norm_num) hz))
      (fun z hz => hτ1 z hz)
      (ρ₀ := ρ₀) (ρ₁ := σ₁) (ρ₂ := σ₂) (ρ₃ := 1 / 2)
      hρ₀_pos hρ₀_lt_σ₁ hσ₁_σ₂ hσ₂_half hρ₀_half le_rfl hWsm_ann hWunit_ann
  -- ## 9. the cut-offs
  set χ : ℂ → ℝ := pcCut (ρχ ^ 2) (ργ ^ 2) with hχ_def
  have hρχ2_lt : ρχ ^ 2 < ργ ^ 2 := by nlinarith
  have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    rw [hχ_def]; exact contDiff_pcCut _ _
  have hχ0 : ∀ z : ℂ, ‖z‖ ≤ ρχ → χ z = 0 := by
    intro z hz
    rw [hχ_def]
    exact pcCut_eq_zero hρχ2_lt (by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg z) hz 2)
  have hχ1 : ∀ z : ℂ, ργ ≤ ‖z‖ → χ z = 1 := by
    intro z hz
    rw [hχ_def]
    refine pcCut_eq_one hρχ2_lt ?_
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ hργ_pos.le hz 2
  have hχnz : ∀ z : ℂ, χ z ≠ 0 → ρχ < ‖z‖ := by
    intro z hz
    have h1 : ρχ ^ 2 < Complex.normSq z := by
      rw [hχ_def] at hz
      exact (pcCut_pos_iff hρχ2_lt z).mp (lt_of_le_of_ne (pcCut_nonneg _ _ z) (Ne.symm hz))
    exact lt_norm_of_normSq_lt (le_of_lt hρχ_pos) h1
  have hχ_nonneg : ∀ z : ℂ, 0 ≤ χ z := fun z => pcCut_nonneg _ _ z
  have hχ_le : ∀ z : ℂ, χ z ≤ 1 := fun z => pcCut_le_one _ _ z
  set lam : ℝ → ℝ := pStep (q / 2) q with hlam_def
  have hlamsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) lam := by
    rw [hlam_def]; exact contDiff_pStep _ _
  have hqhalf_lt_q : q / 2 < q := by linarith
  have hlam0 : ∀ t : ℝ, t ≤ q / 2 → lam t = 0 := by
    intro t ht; rw [hlam_def]; exact pStep_eq_zero hqhalf_lt_q ht
  have hlam1 : ∀ t : ℝ, q ≤ t → lam t = 1 := by
    intro t ht; rw [hlam_def]; exact pStep_eq_one hqhalf_lt_q ht
  -- ## 10. the gadget
  set k : ℂ → ℝ := fun z => χ z * (1 - lam (H z)) with hk_def
  set hN : ℂ → ℝ := fun z => χ z * H z + (1 - χ z) * (1 + Complex.normSq z) with hhN_def
  set pcA' : ℂ → ℝ := fun z => pcA M W x τ z with hpcA'_def
  set dc' : ℂ → ℂ := fun z => pcDc M W x τ z with hdc'_def
  set uN : ℂ → ℂ := fun z => ((k z : ℝ) : ℂ) * ((Real.sqrt (pcA' z) : ℝ) : ℂ) * dc' z
    with huN_def
  set rN : ℂ → ℝ := fun z => Real.sqrt (‖uN z‖ ^ 2 + hN z) with hrN_def
  set dN : ℂ → ℂ := fun z => uN z / ((rN z : ℝ) : ℂ) with hdN_def
  set wN : ℂ → ℂ := fun z => Ω (k z • z) with hwN_def
  set capN : ℂ → Eucl 3 := fun z => capProjVecOf (wN z) (dN z) with hcapN_def
  set conf : ℂ → Eucl 3 := fun z => confProjVecOf (pcU W x τ z) (pcD M W x τ z) with hconf_def
  set V : ℂ → Eucl 3 := fun z => if ‖z‖ < σs then capN z else conf z with hV_def
  set r : ℂ → ℝ := fun z => if ‖z‖ < σs then rN z else Real.sqrt (pcA' z) with hr_def
  -- ...
  -- ## 11. the gadget: elementary facts
  have hband4 : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2 :=
    fun x τ h1 h2 h3 h4 => hband x τ (by linarith) h2 h3 h4
  have hWne4 : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      W (x, τ) ≠ 0 := fun x τ h1 h2 h3 h4 => hWne x τ (by linarith) h2 h3 h4
  have hM04 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0 :=
    fun x h1 h2 => hM0 x (by linarith) h2
  -- `k > 0` forces the region `χ = 1`
  have hkpos : ∀ z : ℂ, 0 < k z → χ z = 1 ∧ H z < q ∧ ργ ≤ ‖z‖ ∧ hN z = H z := by
    intro z hz
    have hz' : 0 < χ z * (1 - lam (H z)) := by simpa [hk_def] using hz
    have hχpos : 0 < χ z := by
      rcases mul_pos_iff.mp hz' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1
      · exact absurd h1 (not_lt.mpr (hχ_nonneg z))
    have hlam : 0 < 1 - lam (H z) := by
      rcases mul_pos_iff.mp hz' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact absurd h1 (not_lt.mpr (hχ_nonneg z))
    have hρχz : ρχ < ‖z‖ := hχnz z (ne_of_gt hχpos)
    have hHq : H z < q := by
      by_contra h
      have h1 : lam (H z) = 1 := hlam1 (H z) (le_of_not_gt h)
      rw [h1] at hlam
      norm_num at hlam
    have hργz : ργ ≤ ‖z‖ := by
      by_contra h
      exact absurd (hq z (le_of_lt hρχz) (le_of_lt (not_le.mp h)))
        (not_le.mpr hHq)
    have hχz : χ z = 1 := hχ1 z hργz
    exact ⟨hχz, hHq, hργz, by simp only [hhN_def, hχz]; ring⟩
  -- the sign and positivity of `hN`
  have hhNnn : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → 0 ≤ hN z := by
    intro z hz
    by_cases hχ : χ z = 1
    · simp only [hhN_def, hχ, one_mul, sub_self, zero_mul, add_zero]
      exact hHnonneg z hz
    · have h3 : 0 ≤ χ z * H z := mul_nonneg (hχ_nonneg z) (hHnonneg z hz)
      have h4 : 0 ≤ (1 - χ z) * (1 + Complex.normSq z) :=
        mul_nonneg (by linarith [lt_of_le_of_ne (hχ_le z) hχ])
          (by linarith [Complex.normSq_nonneg z])
      simp only [hhN_def]; linarith
  have hhNpos : ∀ z : ℂ, ‖z‖ < 1 / 2 → 0 < hN z := by
    intro z hz
    by_cases hχ : χ z = 1
    · have hρχz : ρχ < ‖z‖ := hχnz z (by rw [hχ]; norm_num)
      have h1 : 0 < H z := hHpos_of z (lt_trans hρχ_a hρχz) hz
      simpa only [hhN_def, hχ, one_mul, sub_self, zero_mul, add_zero] using h1
    · have h3 : 0 ≤ χ z * H z := mul_nonneg (hχ_nonneg z) (hHnonneg z hz.le)
      have h4 : 0 < (1 - χ z) * (1 + Complex.normSq z) :=
        mul_pos (by linarith [lt_of_le_of_ne (hχ_le z) hχ])
          (by linarith [Complex.normSq_nonneg z])
      simp only [hhN_def]; linarith
  have hrN_sq : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → rN z ^ 2 = ‖uN z‖ ^ 2 + hN z := by
    intro z hz
    rw [hrN_def, Real.sq_sqrt (add_nonneg (sq_nonneg _) (hhNnn z hz))]
  have hrNpos : ∀ z : ℂ, ‖z‖ < 1 / 2 → 0 < rN z := by
    intro z hz
    rw [hrN_def]
    exact Real.sqrt_pos.mpr (by nlinarith [norm_nonneg (uN z), hhNpos z hz])
  have hdN_lt : ∀ z : ℂ, ‖z‖ < 1 / 2 → ‖dN z‖ < 1 := by
    intro z hz
    have hRpos : 0 < rN z := hrNpos z hz
    have hlt : ‖uN z‖ < rN z := by
      have := hrN_sq z hz.le
      nlinarith [norm_nonneg (uN z), hhNpos z hz]
    rw [hdN_def, norm_div, Complex.norm_of_nonneg hRpos.le, div_lt_one hRpos]
    exact hlt
  have hid_a : ∀ z : ℂ, ‖z‖ < 1 / 2 → ((rN z : ℝ) : ℂ) * dN z = uN z := by
    intro z hz
    have hR : ((rN z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hrNpos z hz))
    rw [hdN_def]; exact mul_div_cancel₀ _ hR
  have hid_b : ∀ z : ℂ, ‖z‖ < 1 / 2 → rN z ^ 2 * (1 - ‖dN z‖ ^ 2) = hN z := by
    intro z hz
    have hRpos : 0 < rN z := hrNpos z hz
    have hR : rN z ≠ 0 := ne_of_gt hRpos
    have h3 : ‖dN z‖ = ‖uN z‖ / rN z := by
      rw [hdN_def, norm_div, Complex.norm_of_nonneg hRpos.le]
    have h4 : rN z ^ 2 * ‖dN z‖ ^ 2 = ‖uN z‖ ^ 2 := by
      rw [h3, div_pow]
      field_simp
    rw [mul_sub, mul_one, h4, hrN_sq z hz.le]
    ring
  -- the region `σs ≤ ‖z‖`: `k = 1` and `hN = H`
  have hkB : ∀ z : ℂ, σs ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → k z = 1 ∧ hN z = H z := by
    intro z h1 h2
    have hργ : ργ ≤ ‖z‖ :=
      le_trans (le_of_lt hργ_σ₁) (le_trans (le_of_lt hσ₁_lt_σs) h1)
    have hσ₁z : σ₁ ≤ ‖z‖ := le_trans (le_of_lt hσ₁_lt_σs) h1
    have hHq : H z ≤ q / 2 := hσ₁le z hσ₁z h2
    have hl : lam (H z) = 0 := hlam0 (H z) hHq
    have hχz : χ z = 1 := hχ1 z hργ
    refine ⟨?_, ?_⟩
    · simp only [hk_def, hχz, hl, sub_zero, one_mul]
    · simp only [hhN_def, hχz, one_mul, sub_self, zero_mul, add_zero]
  -- the identity `H = pcA * (1 - ‖pcDc‖²)`
  have hHdc : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 →
      H z = pcA' z * (1 - Complex.normSq (dc' z)) := by
    intro z h1 h2
    have hD := hPcDisc z h1 h2
    have hne : pcA' z ≠ 0 := ne_of_gt hD.pos
    have hdn : Complex.normSq (dc' z) = 2 - Complex.normSq (pcD M W x τ z) := hD.dc_normSq_eq
    have hpd : Complex.normSq (pcD M W x τ z) = Complex.normSq (M (x z, τ z)) / pcA' z :=
      normSq_pcD hD.pos.le
    have hpe : pcA' z = Complex.normSq (M (x z, τ z)) + τ z * Complex.normSq (W (x z, τ z)) :=
      rfl
    have hne' : Complex.normSq (M (x z, τ z)) + τ z * Complex.normSq (W (x z, τ z)) ≠ 0 := by
      rw [← hpe]; exact hne
    rw [hH_def, hdn, hpd, hpe]
    field_simp
    ring
  -- the factor `√pcA · pcDc` is smooth on `1/16 < ‖z‖ < 1/2`
  have hfactor : ∀ z : ℂ, (1 / 16 : ℝ) < ‖z‖ → ‖z‖ < 1 / 2 →
      0 < pcA' z ∧ pcD M W x τ z ≠ 0 ∧ Complex.normSq (pcD M W x τ z) ≠ 2 := by
    intro z h1 h2
    have hτ2 : -c ≤ τ z := hτge z (le_of_lt h2)
    by_cases hτ : τ z < 0
    · have haz : a < ‖z‖ := by
        by_contra h
        have hle : ‖z‖ ≤ a := le_of_not_gt h
        have h0 : τ z = 0 := by
          simp only [hτ_def]
          exact bandProf_eq_zero ha hle
        linarith
      have hz8 : (1 / 8 : ℝ) ≤ ‖z‖ := le_trans ha8 haz.le
      have hxN : ‖x z‖ = 1 := hxnorm z hz8
      have h14 : (1 / 4 : ℝ) ≤ ‖x z‖ := by rw [hxN]; norm_num
      have h2' : ‖x z‖ ≤ 2 := by rw [hxN]; norm_num
      exact ⟨pcA_pos_of_neg hband4 hWne4 h14 h2' hτ2 hτ,
        pcD_ne_zero_of_disc hband4 hWne4 hM04 h14 (le_of_eq hxN) hτ2 hτ.le,
        ne_of_lt (normSq_pcD_lt_two_of_neg hband4 hWne4 h14 h2' hτ2 hτ)⟩
    · have hτ0 : τ z = 0 := le_antisymm (hτle z (le_of_lt h2)) (le_of_not_gt hτ)
      have hx8 : (1 / 8 : ℝ) ≤ ‖x z‖ := hx16 z (le_of_lt h1)
      have hx1' : ‖x z‖ ≤ 1 := hxn z
      have hMne : M (x z, τ z) ≠ 0 := by rw [hτ0]; exact hM0 (x z) hx8 hx1'
      have hA0 : pcA M W x τ z = Complex.normSq (M (x z, τ z)) := pcA_apply_zero hτ0
      have hpos : 0 < pcA' z := by
        simp only [hpcA'_def]
        rw [hA0]
        exact Complex.normSq_pos.mpr hMne
      refine ⟨hpos, ?_, ?_⟩
      · show M (x z, τ z) / ((Real.sqrt (pcA M W x τ z) : ℝ) : ℂ) ≠ 0
        rw [hA0]
        exact div_ne_zero hMne (Complex.ofReal_ne_zero.mpr
          (ne_of_gt (Real.sqrt_pos.mpr (Complex.normSq_pos.mpr hMne))))
      · show Complex.normSq (pcD M W x τ z) ≠ 2
        rw [normSq_pcD_of_zero hτ0 hMne]; norm_num
  -- the region data at `σ₁ < ‖z‖`
  have hPcB : ∀ z : ℂ, σ₁ < ‖z‖ →
      0 < pcA' z ∧ W (x z, τ z) ≠ 0 ∧ Complex.normSq (pcD M W x τ z) ≠ 2 := by
    intro z h1
    have hzρ : ρ₀ ≤ ‖z‖ := le_of_lt (lt_trans hρ₀_lt_σ₁ h1)
    by_cases h2 : ‖z‖ ≤ 1 / 2
    · have hD := hPcDisc z hzρ h2
      exact ⟨hD.pos, hD.Wne, hD.Dlt_two⟩
    · have h3 : (1 / 2 : ℝ) ≤ ‖z‖ := le_of_lt (not_le.mp h2)
      have hxn : ‖x z‖ = 1 := hxnorm z (le_trans (by norm_num) h3)
      have hτ0 : 0 ≤ τ z := by rw [hτ1 z h3]; nlinarith [Real.pi_pos]
      have hH := PcHon.of_honest hγ hγne hMval hWval hxn hτ0
      exact ⟨hH.pos, hH.Wne, hH.Dlt_two⟩
  -- `pcDc` does not vanish on the disc (from `PcDisc`)
  have hdDc : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → dc' z ≠ 0 := by
    intro z h1 h2
    have hD := hPcDisc z h1 h2
    have hlt : Complex.normSq (pcD M W x τ z) < 2 := hD.Dlt
    show ((Real.sqrt 2 : ℝ) : ℂ)
        * (pcD M W x τ z / ((Real.sqrt (Complex.normSq (pcD M W x τ z)) : ℝ) : ℂ))
        * ((Real.sqrt (1 - Complex.normSq (pcD M W x τ z) / 2) : ℝ) : ℂ) ≠ 0
    refine mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (by norm_num)) ?_) ?_
    · exact div_ne_zero hD.Dne (Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.sqrt_pos.mpr (Complex.normSq_pos.mpr hD.Dne))))
    · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by linarith)))
  have hdN_le : ∀ z : ℂ, ‖z‖ < 1 / 2 → ‖dN z‖ ≤ 1 := fun z hz => le_of_lt (hdN_lt z hz)
  have hdc_le : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → ‖dc' z‖ ≤ 1 :=
    fun z h1 h2 => (hPcDisc z h1 h2).dc_le

  -- ## 12. the collar of agreement and the smoothness of the chart
  have hkC : ∀ z : ℂ, σ₁ ≤ ‖z‖ → ‖z‖ ≤ σ₂ → k z = 1 ∧ hN z = H z := by
    intro z h1 h2
    have hργ : ργ ≤ ‖z‖ := le_trans (le_of_lt hργ_σ₁) h1
    have hHq : H z ≤ q / 2 := hσ₁le z h1 (le_trans h2 hσ₂_half.le)
    have hl : lam (H z) = 0 := hlam0 (H z) hHq
    have hχz : χ z = 1 := hχ1 z hργ
    refine ⟨?_, ?_⟩
    · simp only [hk_def, hχz, hl, sub_zero, one_mul]
    · simp only [hhN_def, hχz, one_mul, sub_self, zero_mul, add_zero]
  have hksm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) k := by
    rw [hk_def]
    exact hχsm.mul (contDiff_const.sub (hlamsm.comp hHsm))
  have hhNsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hN := by
    rw [hhN_def]
    exact (hχsm.mul hHsm).add ((contDiff_const.sub hχsm).mul
      (contDiff_const.add Neutral.contDiff_complexNormSq))
  have hball : ∀ {c₀ : ℝ} {z y : ℂ}, dist y z < c₀ - ‖z‖ → ‖y‖ < c₀ := by
    intro c₀ z y h
    rw [dist_eq_norm] at h
    calc ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
          conv_lhs => rw [← sub_add_cancel y z]
          exact norm_add_le _ _
      _ < (c₀ - ‖z‖) + ‖z‖ := by linarith
      _ = c₀ := by ring
  have hball' : ∀ {c₀ : ℝ} {z y : ℂ}, dist y z < ‖z‖ - c₀ → c₀ < ‖y‖ := by
    intro c₀ z y h
    rw [dist_comm, dist_eq_norm] at h
    have h2 : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
      conv_lhs => rw [← sub_add_cancel z y]
      exact norm_add_le _ _
    linarith
  have huN_sm : ∀ z : ℂ, ‖z‖ < σs → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) uN z := by
    intro z hz
    have hz16 : ‖z‖ < 1 / 2 := lt_trans hz (lt_trans hσs_lt_σ₂ hσ₂_half)
    by_cases h : (1 / 16 : ℝ) < ‖z‖
    · have hf := hfactor z h hz16
      have hk : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => ((k z : ℝ) : ℂ)) z :=
        Complex.ofRealCLM.contDiff.comp_contDiffAt z hksm.contDiffAt
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : ℂ => ((Real.sqrt (pcA' z) : ℝ) : ℂ)) z :=
        Complex.ofRealCLM.contDiff.comp_contDiffAt z
          ((Real.contDiffAt_sqrt hf.1.ne').comp z (contDiffAt_pcA hMsm hWsm hxsm hτsm z))
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => dc' z) z := by
        simp only [hdc'_def]
        exact contDiffAt_pcDc hMsm hWsm hxsm hτsm hf.1 hf.2.1 hf.2.2
      have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : ℂ => ((k z : ℝ) : ℂ) * ((Real.sqrt (pcA' z) : ℝ) : ℂ) * dc' z) z :=
        (hk.mul h1).mul h2
      simpa only [huN_def] using h3
    · have hzχ : ‖z‖ < ρχ := lt_of_le_of_lt (le_of_not_gt h) hχ_thr
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds z (show (0 : ℝ) < ρχ - ‖z‖ by linarith)] with y hy
      have hy' : ‖y‖ < ρχ := hball hy
      have hχy : χ y = 0 := hχ0 y hy'.le
      have hky : k y = 0 := by simp only [hk_def, hχy, zero_mul]
      show uN y = 0
      simp only [huN_def, hky, Complex.ofReal_zero, zero_mul]
  have hrN_sm : ∀ z : ℂ, ‖z‖ < σs → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rN z := by
    intro z hz
    have hz16 : ‖z‖ < 1 / 2 := lt_trans hz (lt_trans hσs_lt_σ₂ hσ₂_half)
    have hns : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℂ => Complex.normSq (uN z)) z := by
      have h := Neutral.contDiff_complexNormSq.contDiffAt.comp z (huN_sm z hz)
      simpa only [Function.comp_def] using h
    have hsum : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℂ => Complex.normSq (uN z) + hN z) z := hns.add hhNsm.contDiffAt
    have hne : (fun z : ℂ => Complex.normSq (uN z) + hN z) z ≠ 0 := by
      show Complex.normSq (uN z) + hN z ≠ 0
      rw [Complex.normSq_eq_norm_sq]
      exact ne_of_gt (by nlinarith [norm_nonneg (uN z), hhNpos z hz16])
    have h3 := hsum.sqrt hne
    have heq : (fun z : ℂ => Real.sqrt (Complex.normSq (uN z) + hN z)) = rN := by
      funext z
      rw [hrN_def, Complex.normSq_eq_norm_sq]
    rw [heq] at h3
    exact h3
  have hcapN_sm : ∀ z : ℂ, ‖z‖ < σs → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) capN z := by
    intro z hz
    have hz16 : ‖z‖ < 1 / 2 := lt_trans hz (lt_trans hσs_lt_σ₂ hσ₂_half)
    have hd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dN z := by
      have hdiv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : ℂ => uN z * (((rN z : ℝ) : ℂ))⁻¹) z :=
        (huN_sm z hz).mul ((Complex.ofRealCLM.contDiff.comp_contDiffAt z (hrN_sm z hz)).inv
          (Complex.ofReal_ne_zero.mpr (ne_of_gt (hrNpos z hz16))))
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : ℂ => uN z / ((rN z : ℝ) : ℂ)) z := by
        simpa only [div_eq_mul_inv] using hdiv
      simpa only [hdN_def] using h1
    have hkl : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => k z • z) z :=
      hksm.contDiffAt.smul contDiffAt_id
    have hw : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wN z := by
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ω ∘ fun z : ℂ => k z • z) z :=
        hΩsm.contDiffAt.comp z hkl
      simpa only [hwN_def, Function.comp_def] using h1
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℂ => capProjVecOf (wN z) (dN z)) z :=
      pc_contDiffAt_capProjVecOf hw hd (by
        rw [Complex.normSq_eq_norm_sq]
        have := hdN_lt z hz16
        nlinarith [norm_nonneg (dN z)])
    simpa only [hcapN_def] using h2
  have hconf_sm : ∀ z : ℂ, σ₁ < ‖z‖ → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) conf z := by
    intro z hz
    have hB := hPcB z hz
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcU W x τ) z :=
      contDiffAt_pcU hWsm hxsm hτsm hB.2.1
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pcD M W x τ) z :=
      contDiffAt_pcD hMsm hWsm hxsm hτsm hB.1
    have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℂ => confProjVecOf (pcU W x τ z) (pcD M W x τ z)) z :=
      pc_contDiffAt_confProjVecOf h1 h2 hB.2.2
    simpa only [hconf_def] using h3
  have hsqrt_sm : ∀ z : ℂ, σ₁ < ‖z‖ →
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Real.sqrt (pcA' z)) z := by
    intro z hz
    have hB := hPcB z hz
    have h1 := (Real.contDiffAt_sqrt hB.1.ne').comp z (contDiffAt_pcA hMsm hWsm hxsm hτsm z)
    simpa only [Function.comp_def] using h1
  have hrN_root : ∀ z : ℂ, σ₁ ≤ ‖z‖ → ‖z‖ ≤ σ₂ → rN z = Real.sqrt (pcA' z) := by
    intro z h1 h2
    obtain ⟨hk1, hh1⟩ := hkC z h1 h2
    have hD := hPcDisc z (le_trans hρ₀_lt_σ₁.le h1) (le_trans h2 hσ₂_half.le)
    have hA : 0 ≤ pcA' z := hD.pos.le
    have hdc : Complex.normSq (dc' z) = 2 - Complex.normSq (pcD M W x τ z) := hD.dc_normSq_eq
    have hH' : H z = pcA' z * (1 - Complex.normSq (dc' z)) :=
      hHdc z (le_trans hρ₀_lt_σ₁.le h1) (le_trans h2 hσ₂_half.le)
    have hu : uN z = ((Real.sqrt (pcA' z) : ℝ) : ℂ) * dc' z := by
      simp only [huN_def, hk1, Complex.ofReal_one, one_mul]
    have hnorm : Complex.normSq (uN z) = pcA' z * Complex.normSq (dc' z) := by
      rw [hu, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hA]
    have hsum : ‖uN z‖ ^ 2 + hN z = pcA' z := by
      have h1' : ‖uN z‖ ^ 2 = pcA' z * Complex.normSq (dc' z) := by
        rw [← Complex.normSq_eq_norm_sq (uN z)]
        exact hnorm
      rw [h1', hh1, hH', hdc]
      ring
    show Real.sqrt (‖uN z‖ ^ 2 + hN z) = Real.sqrt (pcA' z)
    rw [hsum]
  have hdN_root : ∀ z : ℂ, σ₁ ≤ ‖z‖ → ‖z‖ ≤ σ₂ → dN z = dc' z := by
    intro z h1 h2
    obtain ⟨hk1, hh1⟩ := hkC z h1 h2
    have hApos : 0 < pcA' z := (hPcDisc z (le_trans hρ₀_lt_σ₁.le h1)
      (le_trans h2 hσ₂_half.le)).pos
    have hu : uN z = ((Real.sqrt (pcA' z) : ℝ) : ℂ) * dc' z := by
      simp only [huN_def, hk1, Complex.ofReal_one, one_mul]
    have hne : ((Real.sqrt (pcA' z) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hApos))
    show uN z / ((rN z : ℝ) : ℂ) = dc' z
    rw [hu, hrN_root z h1 h2, mul_div_cancel_left₀ _ hne]
  have hcapN_conf : ∀ z : ℂ, σ₁ ≤ ‖z‖ → ‖z‖ ≤ σ₂ → capN z = conf z := by
    intro z h1 h2
    obtain ⟨hk1, hh1⟩ := hkC z h1 h2
    have hD := hPcDisc z (le_trans hρ₀_lt_σ₁.le h1) (le_trans h2 hσ₂_half.le)
    have hΩ := hΩeq z h1 h2
    have hz : wN z = pcW M W x τ z := by
      simp only [hwN_def, hk1, one_smul]
      exact hΩ
    simp only [hcapN_def, hconf_def, hrN_root z h1 h2, hdN_root z h1 h2, hz]
    exact hD.reflect
  have hVconf : ∀ y : ℂ, σ₁ < ‖y‖ → V y = conf y := by
    intro y hy
    rcases lt_or_ge ‖y‖ σs with h | h
    · have h1 : capN y = conf y :=
        hcapN_conf y (le_of_lt hy) (le_trans (le_of_lt h) hσs_lt_σ₂.le)
      simp only [hV_def, if_pos h, h1]
    · simp only [hV_def, if_neg (not_lt.mpr h)]
  have hrconf : ∀ y : ℂ, σ₁ < ‖y‖ → r y = Real.sqrt (pcA' y) := by
    intro y hy
    rcases lt_or_ge ‖y‖ σs with h | h
    · simp only [hr_def, if_pos h,
        hrN_root y (le_of_lt hy) (le_trans (le_of_lt h) hσs_lt_σ₂.le)]
    · simp only [hr_def, if_neg (not_lt.mpr h)]
  have hVinside : ∀ y : ℂ, ‖y‖ < σs → V y = capN y := fun y hy => by
    simp only [hV_def, if_pos hy]
  have hrinside : ∀ y : ℂ, ‖y‖ < σs → r y = rN y := fun y hy => by
    simp only [hr_def, if_pos hy]
  have hr_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := by
    rw [contDiff_iff_contDiffAt]
    intro z
    rcases lt_or_ge ‖z‖ σs with h | h
    · refine (hrN_sm z h).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds z (show (0 : ℝ) < σs - ‖z‖ by linarith)] with y hy
      exact hrinside y (hball hy)
    · refine (hsqrt_sm z (lt_of_lt_of_le hσ₁_lt_σs h)).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds z (show (0 : ℝ) < ‖z‖ - σ₁ by linarith)] with y hy
      exact hrconf y (hball' hy)
  have hV_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V := by
    rw [contDiff_iff_contDiffAt]
    intro z
    rcases lt_or_ge ‖z‖ σs with h | h
    · refine (hcapN_sm z h).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds z (show (0 : ℝ) < σs - ‖z‖ by linarith)] with y hy
      exact hVinside y (hball hy)
    · refine (hconf_sm z (lt_of_lt_of_le hσ₁_lt_σs h)).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds z (show (0 : ℝ) < ‖z‖ - σ₁ by linarith)] with y hy
      exact hVconf y (hball' hy)
  have hrpos : ∀ z : ℂ, 0 < r z := by
    intro z
    rcases lt_or_ge ‖z‖ σs with h | h
    · rw [hrinside z h]
      exact hrNpos z (lt_trans h (lt_trans hσs_lt_σ₂ hσ₂_half))
    · rw [hrconf z (lt_of_lt_of_le hσ₁_lt_σs h)]
      exact Real.sqrt_pos.mpr (hPcB z (lt_of_lt_of_le hσ₁_lt_σs h)).1
  have hVne : ∀ z : ℂ, V z ≠ 0 := by
    intro z
    rcases lt_or_ge ‖z‖ σs with h | h
    · rw [hVinside z h]
      exact capProjVecOf_ne_zero (hΩunit (k z • z))
        (le_of_lt (hdN_lt z (lt_trans h (lt_trans hσs_lt_σ₂ hσ₂_half))))
    · rw [hVconf z (lt_of_lt_of_le hσ₁_lt_σs h)]
      exact confProjVecOf_ne_zero_of_norm_eq_one
        (norm_pcU (hPcB z (lt_of_lt_of_le hσ₁_lt_σs h)).2.1) _

  -- ## 13. the chart
  have hlam_le : ∀ t : ℝ, lam t ≤ 1 := by
    intro t; rw [hlam_def]; exact pStep_le_one _ _ _
  have hk_nonneg : ∀ z : ℂ, 0 ≤ k z := by
    intro z
    simp only [hk_def]
    exact mul_nonneg (hχ_nonneg z) (by linarith [hlam_le (H z)])
  have hχ_ρ₀ : ρ₀ < ρχ := by
    have h1 : (5 / 16 : ℝ) ≤ ρχ := by
      rw [hρχ_def]
      have : (1 / 8 : ℝ) ≤ m := le_trans ha8 (le_trans (le_max_right ρin a) (le_max_left _ _))
      linarith
    have h2 : ρ₀ < 5 / 16 := by rw [hρ₀_def]; linarith
    linarith
  have hrNpos' : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → uN z ≠ 0 → 0 < rN z := by
    intro z hz hu
    rw [hrN_def]
    exact Real.sqrt_pos.mpr (by
      have := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
      nlinarith [hhNnn z hz])
  have huN_ne : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → k z ≠ 0 → uN z ≠ 0 := by
    intro z hz hk
    have hpos : 0 < k z := lt_of_le_of_ne (hk_nonneg z) (Ne.symm hk)
    have hkp := hkpos z hpos
    have hρχ : ρχ < ‖z‖ := hχnz z (by rw [hkp.1]; norm_num)
    have hD := hPcDisc z (le_of_lt (lt_trans hχ_ρ₀ hρχ)) hz
    have hdc := hdDc z (le_of_lt (lt_trans hχ_ρ₀ hρχ)) hz
    rw [huN_def]
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hD.pos)))) hdc
  have hstrip : ∀ z : ℂ, 1 / 2 < ‖z‖ → ‖z‖ ≤ 1 →
      r z = Real.sqrt (‖M (wCollapse z, bandTau a z)‖ ^ 2
            + bandTau a z * ‖W (wCollapse z, bandTau a z)‖ ^ 2) ∧
      V z = confProjVecOf
        (W (wCollapse z, bandTau a z) / ((‖W (wCollapse z, bandTau a z)‖ : ℝ) : ℂ))
        (M (wCollapse z, bandTau a z)
          / ((Real.sqrt (‖M (wCollapse z, bandTau a z)‖ ^ 2
                + bandTau a z * ‖W (wCollapse z, bandTau a z)‖ ^ 2) : ℝ) : ℂ)) := by
    intro z h1 h2
    have hxw : x z = wCollapse z := by
      rw [hx1 z (by linarith), wCollapse_eq (le_of_lt h1)]
    have hσ : σs < ‖z‖ := lt_trans hσs_lt_σ₂ (lt_trans hσ₂_half h1)
    have hr' : r z = Real.sqrt (pcA' z) := hrconf z (lt_of_lt_of_le hσ₁_lt_σs hσ.le)
    have hV' : V z = conf z := hVconf z (lt_of_lt_of_le hσ₁_lt_σs hσ.le)
    constructor
    · rw [hr']
      congr 1
      simp only [hpcA'_def, pcA, hxw, hτ_def, bandTau, Complex.normSq_eq_norm_sq]
    · rw [hV']
      simp only [hconf_def, pcU_apply, pcD_apply, hpcA'_def, pcA, hxw, hτ_def, bandTau,
        Complex.normSq_eq_norm_sq]
  have hcap : ∀ z : ℂ, ‖z‖ < 1 / 2 → ∃ w dc : ℂ, w ≠ 0 ∧ ‖dc‖ ≤ 1 ∧ V z = capProjVecOf w dc := by
    intro z hz
    rcases lt_or_ge ‖z‖ σs with h | h
    · refine ⟨wN z, dN z, ?_, ?_, ?_⟩
      · intro hw0
        have h1 := hΩunit (k z • z)
        simp only [hwN_def] at hw0
        rw [hw0, norm_zero] at h1
        norm_num at h1
      · exact hdN_le z (lt_trans h (lt_trans hσs_lt_σ₂ hσ₂_half))
      · rw [hVinside z h]
    · have hρ : ρ₀ ≤ ‖z‖ := le_trans hρ₀_lt_σ₁.le (le_trans (le_of_lt hσ₁_lt_σs) h)
      have hD := hPcDisc z hρ (le_of_lt hz)
      refine ⟨pcW M W x τ z, pcDc M W x τ z, hD.Wne', hD.dc_le, ?_⟩
      rw [hVconf z (lt_of_lt_of_le hσ₁_lt_σs h)]
      exact hD.reflect.symm
  have hChart : IsPlaneChart γ hγne (planeChartMap r V hrpos hVne) :=
    isPlaneChart_of_datum γ hγ hγne M W a r V ha hMval hWval hr_sm hV_sm hrpos hVne hstrip hcap
  -- ## 14. the rotation invariant of the chart
  have horbit : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      orbitXH (planeChartMap r V hrpos hVne z) = (uN z, hN z) := by
    intro z hz
    rcases lt_or_ge ‖z‖ σs with h | h
    · have hz16 : ‖z‖ < 1 / 2 := lt_trans h (lt_trans hσs_lt_σ₂ hσ₂_half)
      have hw2 : ‖(wN z) ^ 2‖ = 1 := by rw [norm_pow, hΩunit (k z • z)]; norm_num
      have hQ := planeChartMap_eq_capPiece (r := r) (V := V) hrpos hVne
        (z := z) (w := wN z) (d := dN z) (θ := circOf ((wN z) ^ 2) hw2)
        (hΩunit (k z • z)) (hdN_le z hz16)
        (circleOf_circOf ((wN z) ^ 2) hw2).symm (hVinside z h)
      rw [hQ]
      simp only [orbitXH_mk_inr]
      have hrz : r z = rN z := hrinside z h
      refine Prod.ext ?_ ?_
      · show ((r z : ℝ) : ℂ) * dN z = uN z
        rw [hrz]; exact hid_a z hz16
      · show r z ^ 2 * (1 - ‖dN z‖ ^ 2) = hN z
        rw [hrz]; exact hid_b z hz16
    · have hkB' := hkB z h hz
      have hzρ : ρ₀ ≤ ‖z‖ := le_trans hρ₀_lt_σ₁.le (le_trans (le_of_lt hσ₁_lt_σs) h)
      have hD := hPcDisc z hzρ hz
      have hw2 : ‖(pcW M W x τ z) ^ 2‖ = 1 := by rw [norm_pow, hD.normW']; norm_num
      have hVz : V z = capProjVecOf (pcW M W x τ z) (pcDc M W x τ z) := by
        rw [hVconf z (lt_of_lt_of_le hσ₁_lt_σs h)]
        exact hD.reflect.symm
      have hQ := planeChartMap_eq_capPiece (r := r) (V := V) hrpos hVne
        (z := z) (w := pcW M W x τ z) (d := pcDc M W x τ z)
        (θ := circOf ((pcW M W x τ z) ^ 2) hw2) hD.normW' hD.dc_le
        (circleOf_circOf ((pcW M W x τ z) ^ 2) hw2).symm hVz
      rw [hQ]
      simp only [orbitXH_mk_inr]
      have hrz : r z = Real.sqrt (pcA' z) := hrconf z (lt_of_lt_of_le hσ₁_lt_σs h)
      refine Prod.ext ?_ ?_
      · show ((r z : ℝ) : ℂ) * pcDc M W x τ z = uN z
        rw [hrz]
        simp only [huN_def, hkB'.1, Complex.ofReal_one, one_mul, hdc'_def]
      · show r z ^ 2 * (1 - ‖pcDc M W x τ z‖ ^ 2) = hN z
        rw [hrz, hkB'.2, Real.sq_sqrt hD.pos.le, hHdc z hzρ hz, hdc'_def, hpcA'_def,
          Complex.normSq_eq_norm_sq]

  -- ## 15. `CapInterior`
  have hCapInterior : CapInterior (planeChartMap r V hrpos hVne) := by
    intro z hz c hc
    rcases lt_or_ge ‖z‖ σs with h | h
    · have hz16 : ‖z‖ < 1 / 2 := lt_trans h (lt_trans hσs_lt_σ₂ hσ₂_half)
      have hw2 : ‖(wN z) ^ 2‖ = 1 := by rw [norm_pow, hΩunit (k z • z)]; norm_num
      have hQ := planeChartMap_eq_capPiece (r := r) (V := V) hrpos hVne
        (z := z) (w := wN z) (d := dN z) (θ := circOf ((wN z) ^ 2) hw2)
        (hΩunit (k z • z)) (hdN_le z hz16)
        (circleOf_circOf ((wN z) ^ 2) hw2).symm (hVinside z h)
      have heq : Quotient.mk'' (Sum.inr c) =
          (Quotient.mk'' (Sum.inr (⟨(r z, circOf ((wN z) ^ 2) hw2, dN z), hrpos z,
            hdN_le z hz16⟩ : CapPiece) : ConfigPiece ⊕ CapPiece) : CappingSpace) := by
        rw [← hc, hQ]
      have hce : c = ⟨(r z, circOf ((wN z) ^ 2) hw2, dN z), hrpos z, hdN_le z hz16⟩ :=
        cappingRel_inr_inr.mp (Quotient.exact heq)
      rw [hce]
      exact hdN_lt z hz16
    · have hzρ : ρ₀ ≤ ‖z‖ := le_trans hρ₀_lt_σ₁.le (le_trans (le_of_lt hσ₁_lt_σs) h)
      have hD := hPcDisc z hzρ hz.le
      have hw2 : ‖(pcW M W x τ z) ^ 2‖ = 1 := by rw [norm_pow, hD.normW']; norm_num
      have hVz : V z = capProjVecOf (pcW M W x τ z) (pcDc M W x τ z) := by
        rw [hVconf z (lt_of_lt_of_le hσ₁_lt_σs h)]
        exact hD.reflect.symm
      have hQ := planeChartMap_eq_capPiece (r := r) (V := V) hrpos hVne
        (z := z) (w := pcW M W x τ z) (d := pcDc M W x τ z)
        (θ := circOf ((pcW M W x τ z) ^ 2) hw2) hD.normW' hD.dc_le
        (circleOf_circOf ((pcW M W x τ z) ^ 2) hw2).symm hVz
      have heq : Quotient.mk'' (Sum.inr c) =
          (Quotient.mk'' (Sum.inr (⟨(r z, circOf ((pcW M W x τ z) ^ 2) hw2, pcDc M W x τ z),
            hrpos z, hD.dc_le⟩ : CapPiece) : ConfigPiece ⊕ CapPiece) : CappingSpace) := by
        rw [← hc, hQ]
      have hce : c = ⟨(r z, circOf ((pcW M W x τ z) ^ 2) hw2, pcDc M W x τ z), hrpos z,
          hD.dc_le⟩ := cappingRel_inr_inr.mp (Quotient.exact heq)
      rw [hce]
      have hz_a : a < ‖z‖ := lt_of_lt_of_le hρχ_a
        (le_trans hρχ_lt_ργ.le (le_trans (le_of_lt hργ_σ₁) (le_trans (le_of_lt hσ₁_lt_σs) h)))
      have hτneg : τ z < 0 := bandTau_neg ha hz_a hz
      have hWpos : 0 < Complex.normSq (W (x z, τ z)) := Complex.normSq_pos.mpr hD.Wne
      have hlt : 1 < Complex.normSq (pcD M W x τ z) := by
        rw [normSq_pcD hD.pos.le, one_lt_div hD.pos]
        show pcA M W x τ z < Complex.normSq (M (x z, τ z))
        simp only [pcA]
        nlinarith [mul_neg_of_neg_of_pos hτneg hWpos]
      have h2 : Complex.normSq (pcDc M W x τ z) < 1 := by
        rw [hD.dc_normSq_eq]; linarith
      have h2' : ‖pcDc M W x τ z‖ ^ 2 < 1 := by
        rw [← Complex.normSq_eq_norm_sq]; exact h2
      nlinarith [norm_nonneg (pcDc M W x τ z)]
  -- ## 16. `CapSection`
  have hCapSection : CapSection (planeChartMap r V hrpos hVne) := by
    refine capSection_of_orbitXH_fibres ?_
    intro z z' hz hz' heq
    have h1 : uN z = uN z' ∧ hN z = hN z' := by
      have h := heq
      rw [horbit z hz, horbit z' hz'] at h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    by_cases hk : k z = 0
    · by_cases hk' : k z' = 0
      · -- both points are in the collapsed region
        have hzA : ‖z‖ < σs := by
          by_contra h
          have h1k : k z = 1 := (hkB z (not_lt.mp h) hz).1
          rw [hk] at h1k; norm_num at h1k
        have hzA' : ‖z'‖ < σs := by
          by_contra h
          have h1k : k z' = 1 := (hkB z' (not_lt.mp h) hz').1
          rw [hk'] at h1k; norm_num at h1k
        have huz : uN z = 0 := by simp only [huN_def, hk, Complex.ofReal_zero, zero_mul]
        have huz' : uN z' = 0 := by simp only [huN_def, hk', Complex.ofReal_zero, zero_mul]
        have hdNz : dN z = 0 := by
          show uN z / ((rN z : ℝ) : ℂ) = 0
          rw [huz]; simp
        have hdNz' : dN z' = 0 := by
          show uN z' / ((rN z' : ℝ) : ℂ) = 0
          rw [huz']; simp
        have hwz : wN z = Ω 0 := by simp only [hwN_def, hk, zero_smul]
        have hwz' : wN z' = Ω 0 := by simp only [hwN_def, hk', zero_smul]
        have h0 : ‖(Ω 0) ^ 2‖ = 1 := by rw [norm_pow, hΩunit 0]; norm_num
        have htw₀ : (Ω 0) ^ 2 = circleOf (circOf ((Ω 0) ^ 2) h0) :=
          (circleOf_circOf ((Ω 0) ^ 2) h0).symm
        have hz16 : ‖z‖ < 1 / 2 := lt_trans hzA (lt_trans hσs_lt_σ₂ hσ₂_half)
        have hz16' : ‖z'‖ < 1 / 2 := lt_trans hzA' (lt_trans hσs_lt_σ₂ hσ₂_half)
        have hrz : r z = r z' := by
          rw [hrinside z hzA, hrinside z' hzA']
          show Real.sqrt (‖uN z‖ ^ 2 + hN z) = Real.sqrt (‖uN z'‖ ^ 2 + hN z')
          rw [h1.1, h1.2]
        have hQ := planeChartMap_eq_capPiece (r := r) (V := V) hrpos hVne
          (z := z) (w := wN z) (d := dN z) (θ := circOf ((Ω 0) ^ 2) h0)
          (by rw [hwz]; exact hΩunit 0) (hdN_le z hz16)
          (by rw [hwz]; exact htw₀) (hVinside z hzA)
        have hQ' := planeChartMap_eq_capPiece (r := r) (V := V) hrpos hVne
          (z := z') (w := wN z') (d := dN z') (θ := circOf ((Ω 0) ^ 2) h0)
          (by rw [hwz']; exact hΩunit 0) (hdN_le z' hz16')
          (by rw [hwz']; exact htw₀) (hVinside z' hzA')
        have hcap_eq : (⟨(r z, circOf ((Ω 0) ^ 2) h0, dN z), hrpos z, hdN_le z hz16⟩ : CapPiece)
            = ⟨(r z', circOf ((Ω 0) ^ 2) h0, dN z'), hrpos z', hdN_le z' hz16'⟩ := by
          refine Subtype.ext ?_
          show ((r z, circOf ((Ω 0) ^ 2) h0, dN z) : ℝ × UnitAddCircle × ℂ)
              = (r z', circOf ((Ω 0) ^ 2) h0, dN z')
          rw [hdNz, hdNz', hrz]
        rw [hQ, hQ', hcap_eq]
      · exact absurd (by
          have hux : uN z = 0 := by
            simp only [huN_def, hk, Complex.ofReal_zero, zero_mul]
          rw [← h1.1, hux]) (huN_ne z' hz' hk')
    · have hk' : k z' ≠ 0 := by
        intro h'
        have hux : uN z' = 0 := by
          simp only [huN_def, h', Complex.ofReal_zero, zero_mul]
        exact huN_ne z hz hk (by rw [h1.1, hux])
      have hposz : 0 < k z := lt_of_le_of_ne (hk_nonneg z) (Ne.symm hk)
      have hkp := hkpos z hposz
      have hposz' : 0 < k z' := lt_of_le_of_ne (hk_nonneg z') (Ne.symm hk')
      have hkp' := hkpos z' hposz'
      have hρχ : ρχ < ‖z‖ := hχnz z (by rw [hkp.1]; norm_num)
      have hρz : ρ₀ ≤ ‖z‖ := le_of_lt (lt_trans hχ_ρ₀ hρχ)
      have hD := hPcDisc z hρz hz
      have hdc := hdDc z hρz hz
      have hρχ' : ρχ < ‖z'‖ := hχnz z' (by rw [hkp'.1]; norm_num)
      have hρz' : ρ₀ ≤ ‖z'‖ := le_of_lt (lt_trans hχ_ρ₀ hρχ')
      have hD' := hPcDisc z' hρz' hz'
      have hdc' := hdDc z' hρz' hz'
      have hkχ : k z = 1 - lam (H z) := by simp only [hk_def, hkp.1]; ring
      have hkχ' : k z' = 1 - lam (H z') := by simp only [hk_def, hkp'.1]; ring
      have hHA : H z = pcA' z * (1 - ‖dc' z‖ ^ 2) := by
        rw [← Complex.normSq_eq_norm_sq (dc' z)]
        exact hHdc z hρz hz
      have hHA' : H z' = pcA' z' * (1 - ‖dc' z'‖ ^ 2) := by
        rw [← Complex.normSq_eq_norm_sq (dc' z')]
        exact hHdc z' hρz' hz'
      have hk0 : 0 < 1 - lam (H z) := by rw [← hkχ]; exact hposz
      have hk0' : 0 < 1 - lam (H z') := by rw [← hkχ']; exact hposz'
      have hrN_z : rN z = Real.sqrt (‖((1 - lam (H z) : ℝ) : ℂ)
          * ((Real.sqrt (pcA' z) : ℝ) : ℂ) * dc' z‖ ^ 2 + H z) := by
        simp only [hrN_def, huN_def, hkχ, hkp.2.2.2]
      have hrN_z' : rN z' = Real.sqrt (‖((1 - lam (H z') : ℝ) : ℂ)
          * ((Real.sqrt (pcA' z') : ℝ) : ℂ) * dc' z'‖ ^ 2 + H z') := by
        simp only [hrN_def, huN_def, hkχ', hkp'.2.2.2]
      have hrN_eq : rN z = rN z' := by
        show Real.sqrt (‖uN z‖ ^ 2 + hN z) = Real.sqrt (‖uN z'‖ ^ 2 + hN z')
        rw [h1.1, h1.2]
      have huNz : ((1 - lam (H z) : ℝ) : ℂ) * ((Real.sqrt (pcA' z) : ℝ) : ℂ) * dc' z = uN z := by
        simp only [huN_def, hkχ]
      have huNz' : ((1 - lam (H z') : ℝ) : ℂ) * ((Real.sqrt (pcA' z') : ℝ) : ℂ) * dc' z'
          = uN z' := by
        simp only [huN_def, hkχ']
      have hg := gadget_pair_recover lam hD.pos hD'.pos hdc hdc' hk0 hk0' hHA hHA'
      obtain ⟨hHz, hAz, hdcz⟩ : H z = H z' ∧ pcA' z = pcA' z' ∧ dc' z = dc' z' := by
        refine hg ?_ ?_ ?_ ?_
        · show 0 < Real.sqrt (‖((1 - lam (H z) : ℝ) : ℂ)
              * ((Real.sqrt (pcA' z) : ℝ) : ℂ) * dc' z‖ ^ 2 + H z)
          rw [← hrN_z]; exact hrNpos' z hz (huN_ne z hz hk)
        · show 0 < Real.sqrt (‖((1 - lam (H z') : ℝ) : ℂ)
              * ((Real.sqrt (pcA' z') : ℝ) : ℂ) * dc' z'‖ ^ 2 + H z')
          rw [← hrN_z']; exact hrNpos' z' hz' (huN_ne z' hz' hk')
        · rw [← hrN_z, ← hrN_z']; exact hrN_eq
        · show (((1 - lam (H z) : ℝ) : ℂ) * ((Real.sqrt (pcA' z) : ℝ) : ℂ) * dc' z)
              / ((Real.sqrt (‖((1 - lam (H z) : ℝ) : ℂ)
                  * ((Real.sqrt (pcA' z) : ℝ) : ℂ) * dc' z‖ ^ 2 + H z) : ℝ) : ℂ)
            = (((1 - lam (H z') : ℝ) : ℂ) * ((Real.sqrt (pcA' z') : ℝ) : ℂ) * dc' z')
              / ((Real.sqrt (‖((1 - lam (H z') : ℝ) : ℂ)
                  * ((Real.sqrt (pcA' z') : ℝ) : ℂ) * dc' z'‖ ^ 2 + H z') : ℝ) : ℂ)
          rw [← hrN_z, ← hrN_z', huNz, huNz', hrN_eq, h1.1]
      have hzeq : z = z' :=
        hcollar z z' (le_of_lt (lt_trans hρχ_in hρχ)) hz
          (le_of_lt (lt_trans hρχ_in hρχ')) hz' hAz hdcz
      rw [hzeq]
  exact ⟨planeChartMap r V hrpos hVne, hChart, hCapSection, hCapInterior⟩

end

end Work.Drive
