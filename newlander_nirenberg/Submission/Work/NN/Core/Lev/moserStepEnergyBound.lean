import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.Lev.nnGradBoundPoint
import Submission.Work.NN.Core.contDiff_one_mul_of_support
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
import Submission.Work.NN.Core.volume_polydisc

/-!
# The Moser step: squared `L²` energy bound for the cutoff product

`Work.NN.Core.Lev.moserStepEnergyBound` bounds the squared `L²` norm of the differential of the
cutoff product `W = χ · u^k` by `2(1 + 8nC₀)L²` times the squared `L²` norm of `u^k` on the
polydisc `polydisc 0 s` containing the support of `χ`, given the Caccioppoli hypothesis `hCac` on
`u^k` and the pointwise product rule `hpt`.

The proof splits `fderiv ℝ W` using the product rule (`hpt`), estimates
`‖fderiv ℝ u^k‖² ≤ 8n · Σ_j (|∂_j u^k|² + |∂̄_j u^k|²)`, and applies `hCac`.  Since `u` is only
`C¹` on `polydisc 0 ρ` (whereas the pointwise estimates are global), a smooth bump `θ`, equal to
`1` on a slightly larger polydisc `polydisc 0 s'` and supported in `polydisc 0 ρ`, is used to
replace `u` by the globally `C¹` function `θ · u`; all the integrals below are only over
`tsupport χ ⊆ polydisc 0 s`, where the two agree.
-/

noncomputable section
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NNReal ENNReal ContDiff Topology
open MeasureTheory Filter Set

namespace Work.NN.Core.Lev

/-! ## Closed polydiscs -/

private def closedPolydisc {n : ℕ} (r : Fin n → ℝ) : Set (Work.NN.Core.Cn n) :=
  Set.pi Set.univ (fun j => Metric.closedBall (0 : ℂ) (r j))

private lemma isCompact_closedPolydisc {n : ℕ} (r : Fin n → ℝ) : IsCompact (closedPolydisc r) :=
  isCompact_univ_pi fun j => isCompact_closedBall 0 (r j)

private lemma mem_closedPolydisc {n : ℕ} {r : Fin n → ℝ} {z : Work.NN.Core.Cn n} :
    z ∈ closedPolydisc r ↔ ∀ j, ‖z j‖ ≤ r j := by
  simp only [closedPolydisc, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall,
    dist_eq_norm, sub_zero]

private lemma closedPolydisc_subset_polydisc {n : ℕ} {r r' : Fin n → ℝ}
    (h : ∀ j, r j < r' j) : closedPolydisc r ⊆ Work.CR.Flat.polydisc 0 r' := by
  intro z hz
  simp only [Work.CR.Flat.mem_polydisc, Pi.zero_apply, sub_zero]
  intro j
  exact lt_of_le_of_lt ((mem_closedPolydisc.mp hz) j) (h j)

private lemma polydisc_subset_closedPolydisc {n : ℕ} {r r' : Fin n → ℝ}
    (h : ∀ j, r j < r' j) : Work.CR.Flat.polydisc 0 r ⊆ closedPolydisc r' := by
  intro z hz
  rw [mem_closedPolydisc]
  intro j
  have hzj : ‖z j‖ < r j := by
    simpa only [Work.CR.Flat.mem_polydisc, Pi.zero_apply, sub_zero] using hz j
  exact le_of_lt (lt_trans hzj (h j))

/-! ## `(eLpNorm F 2 μ)^2` is the integral of `‖F‖^2` -/

theorem eLpNormSqEqOfRealIntegral {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {E : Type*} [NormedAddCommGroup E] {F : α → E}
    (hF : MeasureTheory.AEStronglyMeasurable F μ)
    (hint : MeasureTheory.Integrable (fun z => ‖F z‖ ^ 2) μ) :
    (MeasureTheory.eLpNorm F 2 μ) ^ 2 = ENNReal.ofReal (∫ z, ‖F z‖ ^ 2 ∂μ) := by
  have henorm : ∀ x : E, ‖x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖x‖ ^ 2) := by
    intro x
    rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal (p := ‖x‖₊),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two,
      coe_nnnorm]
  have h1 := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := F) (p := (2:NNReal))
    (by norm_num) hF
  simp only [show ((2:NNReal) : ℝ≥0∞) = 2 from by norm_num,
    show ((2:NNReal) : ℝ) = 2 from by norm_num] at h1
  have h1' : (MeasureTheory.eLpNorm F 2 μ) ^ 2 = ∫⁻ z, ‖F z‖ₑ ^ (2:ℝ) ∂μ := by
    rw [← ENNReal.rpow_natCast (MeasureTheory.eLpNorm F 2 μ) 2]
    exact h1
  rw [h1', lintegral_congr (fun z => henorm (F z))]
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z => sq_nonneg _)).symm

/-! ## Boundedness of a `C¹` function on a smaller polydisc -/

theorem existsPolydiscSupBound {n : ℕ} (hn : 0 < n) {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ)) {s : Fin n → ℝ} (hsρ : ∀ j, s j < ρ j) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Work.CR.Flat.polydisc 0 s, ‖u z‖ ≤ M := by
  classical
  set s' : Fin n → ℝ := fun j => (s j + ρ j) / 2 with hs'def
  have hss' : ∀ j, s j < s' j := by
    intro j; simp only [hs'def]; linarith [hsρ j]
  have hs'ρ : ∀ j, s' j < ρ j := by
    intro j; simp only [hs'def]; linarith [hsρ j]
  have hpolyK : Work.CR.Flat.polydisc 0 s ⊆ closedPolydisc s' :=
    polydisc_subset_closedPolydisc hss'
  have hKρ : closedPolydisc s' ⊆ Work.CR.Flat.polydisc 0 ρ :=
    closedPolydisc_subset_polydisc hs'ρ
  have hcont : ContinuousOn u (closedPolydisc s') := hu.continuousOn.mono hKρ
  obtain ⟨C, hC⟩ := (isCompact_closedPolydisc s').exists_bound_of_continuousOn hcont
  exact ⟨max C 0, le_max_right _ _, fun z hz =>
    le_trans (hC z (hpolyK hz)) (le_max_left _ _)⟩

/-! ## A smooth bump adapted to nested polydiscs -/

theorem existsPolydiscBump {n : ℕ} (hn : 0 < n) {ρ s : Fin n → ℝ} (hsρ : ∀ j, s j < ρ j) :
    ∃ (ρ' s' : Fin n → ℝ) (θ : Work.NN.Core.Cn n → ℝ),
      (∀ j, s j < s' j) ∧ (∀ j, s' j < ρ' j) ∧ (∀ j, ρ' j < ρ j) ∧
      ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ ∧
      tsupport θ ⊆ Work.CR.Flat.polydisc 0 ρ' ∧
      (∀ z, (∃ j, ρ' j ≤ ‖z j‖) → θ z = 0) ∧
      (∀ z ∈ Work.CR.Flat.polydisc 0 s', θ z = 1) := by
  classical
  set s' : Fin n → ℝ := fun j => (2 * s j + ρ j) / 3 with hs'def
  set ρ' : Fin n → ℝ := fun j => (s j + 2 * ρ j) / 3 with hρ'def
  have hss' : ∀ j, s j < s' j := by
    intro j; simp only [hs'def]; linarith [hsρ j]
  have hs'ρ' : ∀ j, s' j < ρ' j := by
    intro j; simp only [hs'def, hρ'def]; linarith [hsρ j]
  have hρ'ρ : ∀ j, ρ' j < ρ j := by
    intro j; simp only [hρ'def]; linarith [hsρ j]
  obtain ⟨χ, V, hχcd, hχcs, hχsupp, hVopen, hKV, hχone⟩ :=
    Work.NN.Core.exists_contDiff_bump_of_isCompact_subset (K := closedPolydisc s')
      (isCompact_closedPolydisc s') (Work.CR.Flat.isOpen_polydisc 0 ρ')
      (closedPolydisc_subset_polydisc hs'ρ')
  have hsuppre : Function.support (fun z => (χ z).re) ⊆ Function.support χ := by
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro h0; exact hz (by rw [h0]; simp)
  refine ⟨ρ', s', fun z => (χ z).re, hss', hs'ρ', hρ'ρ, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.reCLM.contDiff.comp hχcd
  · exact hχcs.isCompact.of_isClosed_subset (isClosed_tsupport (fun z => (χ z).re))
      (closure_mono hsuppre)
  · exact (closure_mono hsuppre).trans hχsupp
  · intro z hz
    have hzts : z ∉ tsupport χ := fun hm => by
      have hmem : ∀ j, ‖z j‖ < ρ' j := by
        have h := hχsupp hm
        simpa only [Work.CR.Flat.mem_polydisc, Pi.zero_apply, sub_zero] using h
      obtain ⟨j, hj⟩ := hz
      exact absurd (lt_of_le_of_lt hj (hmem j)) (lt_irrefl _)
    have hχz : χ z = 0 := by
      by_contra hne
      exact hzts (subset_tsupport χ (Function.mem_support.mpr hne))
    simp [hχz]
  · intro z hz
    have hzK : z ∈ closedPolydisc s' := by
      rw [mem_closedPolydisc]
      intro j
      have hzj : ‖z j‖ < s' j := by
        simpa only [Work.CR.Flat.mem_polydisc, Pi.zero_apply, sub_zero] using hz j
      exact le_of_lt hzj
    have h1 : χ z = 1 := hχone z (hKV hzK)
    simp [h1]

/-! ## Pointwise bound of the differential by the Wirtinger derivatives -/

private lemma nnGradBound {n : ℕ} (hn : 0 < n) (v : Work.NN.Core.Cn n → ℂ)
    (z : Work.NN.Core.Cn n) :
    ‖fderiv ℝ v z‖ ^ 2 ≤ 8 * (n : ℝ) * ∑ j, (‖Work.CR.Flat.dCoord j v z‖ ^ 2
      + ‖Work.CR.Flat.dbarCoord j v z‖ ^ 2) := by
  set T : ℝ := ∑ j, (‖Work.CR.Flat.dCoord j v z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j v z‖ ^ 2)
    with hT
  set S : ℝ := ∑ j, (‖Work.CR.Flat.dCoord j v z‖ + ‖Work.CR.Flat.dbarCoord j v z‖) with hS
  have h1 : ‖fderiv ℝ v z‖ ≤ 2 * S := by
    rw [hS]
    exact Work.CR.Flat.Cauchy.bmCz.norm_fderiv_le_sum_wirtinger v z
  have h2 : ‖fderiv ℝ v z‖ ^ 2 ≤ 4 * S ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg (fderiv ℝ v z)) h1 2
    nlinarith [h]
  have h4 : ∀ j : Fin n, (‖Work.CR.Flat.dCoord j v z‖ + ‖Work.CR.Flat.dbarCoord j v z‖) ^ 2
      ≤ 2 * (‖Work.CR.Flat.dCoord j v z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j v z‖ ^ 2) := fun j =>
    by nlinarith [sq_nonneg (‖Work.CR.Flat.dCoord j v z‖ - ‖Work.CR.Flat.dbarCoord j v z‖)]
  have h3 : S ^ 2 ≤ 2 * (n : ℝ) * T := by
    rw [hS, hT]
    calc (∑ j, (‖Work.CR.Flat.dCoord j v z‖ + ‖Work.CR.Flat.dbarCoord j v z‖)) ^ 2
        ≤ (n : ℝ) * ∑ j,
            (‖Work.CR.Flat.dCoord j v z‖ + ‖Work.CR.Flat.dbarCoord j v z‖) ^ 2 := by
          simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
            (f := fun j : Fin n => ‖Work.CR.Flat.dCoord j v z‖
              + ‖Work.CR.Flat.dbarCoord j v z‖)
      _ ≤ (n : ℝ) * ∑ j, 2 * (‖Work.CR.Flat.dCoord j v z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j v z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => h4 j) (by positivity)
      _ = 2 * (n : ℝ) * ∑ j, (‖Work.CR.Flat.dCoord j v z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j v z‖ ^ 2) := by
          rw [← Finset.mul_sum]; ring
  calc ‖fderiv ℝ v z‖ ^ 2 ≤ 4 * S ^ 2 := h2
    _ ≤ 4 * (2 * (n : ℝ) * T) := by nlinarith [h3]
    _ = 8 * (n : ℝ) * T := by ring

/-! ## Continuity of the Wirtinger derivatives -/

private lemma continuous_dCoord_of_contDiff {n : ℕ} {f : Work.NN.Core.Cn n → ℂ}
    (hf : ContDiff ℝ 1 f) (j : Fin n) :
    Continuous (fun z => Work.CR.Flat.dCoord j f z) := by
  have hfd : Continuous (fun y => fderiv ℝ f y) := hf.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun y => fderiv ℝ f y (Pi.single j (1 : ℂ))) :=
    hfd.clm_apply continuous_const
  have h2 : Continuous (fun y => fderiv ℝ f y (Pi.single j Complex.I)) :=
    hfd.clm_apply continuous_const
  have h3 : (fun y => Work.CR.Flat.dCoord j f y)
      = fun y => (1 / 2 : ℂ) * (fderiv ℝ f y (Pi.single j (1 : ℂ))
          - Complex.I * fderiv ℝ f y (Pi.single j Complex.I)) := by
    funext y; rfl
  rw [h3]
  exact (h1.sub (continuous_const.mul h2)).const_mul (1 / 2 : ℂ)

private lemma continuous_dbarCoord_of_contDiff {n : ℕ} {f : Work.NN.Core.Cn n → ℂ}
    (hf : ContDiff ℝ 1 f) (j : Fin n) :
    Continuous (fun z => Work.CR.Flat.dbarCoord j f z) := by
  have hfd : Continuous (fun y => fderiv ℝ f y) := hf.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun y => fderiv ℝ f y (Pi.single j (1 : ℂ))) :=
    hfd.clm_apply continuous_const
  have h2 : Continuous (fun y => fderiv ℝ f y (Pi.single j Complex.I)) :=
    hfd.clm_apply continuous_const
  have h3 : (fun y => Work.CR.Flat.dbarCoord j f y)
      = fun y => (1 / 2 : ℂ) * (fderiv ℝ f y (Pi.single j (1 : ℂ))
          + Complex.I * fderiv ℝ f y (Pi.single j Complex.I)) := by
    funext y; rfl
  rw [h3]
  exact (h1.add (continuous_const.mul h2)).const_mul (1 / 2 : ℂ)


theorem moserStepEnergyBound {n : ℕ} (hn : 0 < n)
    {ρ s : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ} {χ : Work.NN.Core.Cn n → ℝ}
    {C₀ L : ℝ} (hC₀ : 0 ≤ C₀) (hL0 : 0 ≤ L)
    (hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ))
    (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Work.CR.Flat.polydisc 0 s) (hsρ : ∀ j, s j < ρ j)
    (hχnn : ∀ z, 0 ≤ χ z) (hL : ∀ z, ‖fderiv ℝ χ z‖ ≤ L)
    (k : ℕ) (hk : 1 ≤ k)
    (hW : ContDiff ℝ 1 (fun z => (χ z : ℂ) * (u z)^k))
    (hpt : ∀ z, ‖fderiv ℝ (fun z => (χ z : ℂ) * (u z)^k) z‖
        ≤ χ z * ‖fderiv ℝ (fun w => (u w)^k) z‖ + ‖u z‖^k * ‖fderiv ℝ χ z‖)
    (hCac : ∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 *
              (∑ j, (‖Work.CR.Flat.dCoord j (fun w => (u w)^k) z‖^2
                   + ‖Work.CR.Flat.dbarCoord j (fun w => (u w)^k) z‖^2))
            ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ,
                ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) :
    (MeasureTheory.eLpNorm (fderiv ℝ (fun z => (χ z : ℂ) * (u z)^k)) 2 MeasureTheory.volume)^2
      ≤ ENNReal.ofReal (2 * (1 + 8 * (n:ℝ) * C₀) * L^2) *
        (MeasureTheory.eLpNorm (fun z => (u z)^k) 2
          (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)))^2 := by
  classical
  set W : Work.NN.Core.Cn n → ℂ := fun z => (χ z : ℂ) * (u z)^k with hWdef
  obtain ⟨ρ', s', θ, hss', hs'ρ', hρ'ρ, hθcd, hθcs, hθsupp, hθzero, hθone⟩ :=
    existsPolydiscBump hn hsρ
  have hχsupp' : tsupport χ ⊆ Work.CR.Flat.polydisc 0 s' :=
    hχsupp.trans (Work.CR.Flat.polydisc_mono fun j => le_of_lt (hss' j))
  have hχsuppρ : tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρ :=
    hχsupp.trans (Work.CR.Flat.polydisc_mono fun j => le_of_lt (hsρ j))
  have hpoly_s' : Work.CR.Flat.polydisc 0 s ⊆ Work.CR.Flat.polydisc 0 s' :=
    Work.CR.Flat.polydisc_mono fun j => le_of_lt (hss' j)
  set v : Work.NN.Core.Cn n → ℂ := fun z => (θ z : ℂ) * u z with hvdef
  have hvC1 : ContDiff ℝ 1 v := by
    rw [hvdef]
    exact Work.NN.Core.contDiff_one_mul_of_support hθcd hθzero hρ'ρ hu
  have hv_eq : ∀ z ∈ Work.CR.Flat.polydisc 0 s', v z = u z := by
    intro z hz
    rw [hvdef]
    simp [hθone z hz]
  set Av : Work.NN.Core.Cn n → ℝ :=
    fun z => χ z * ‖fderiv ℝ (fun w => (v w)^k) z‖ with hAvdef
  set Bv : Work.NN.Core.Cn n → ℝ := fun z => ‖v z‖^k * ‖fderiv ℝ χ z‖ with hBvdef
  set Ev : Work.NN.Core.Cn n → ℝ :=
    fun z => (χ z)^2 * ∑ j, (‖Work.CR.Flat.dCoord j (fun w => (v w)^k) z‖^2
      + ‖Work.CR.Flat.dbarCoord j (fun w => (v w)^k) z‖^2) with hEvdef
  have hχC1 : ContDiff ℝ 1 χ := ContDiff.of_le hχcd (by norm_num)
  have hdχcont : Continuous (fun z => fderiv ℝ χ z) := hχC1.continuous_fderiv (by norm_num)
  have hvmk : ContDiff ℝ 1 (fun w => (v w)^k) := hvC1.pow k
  have hfdvcont : Continuous (fun z => fderiv ℝ (fun w => (v w)^k) z) :=
    hvmk.continuous_fderiv (by norm_num)
  have hAvcont : Continuous Av := by
    rw [hAvdef]
    exact (hχC1.continuous).mul hfdvcont.norm
  have hBvcont : Continuous Bv := by
    rw [hBvdef]
    exact (hvC1.continuous.norm.pow k).mul hdχcont.norm
  have hEvcont : Continuous Ev := by
    rw [hEvdef]
    refine (hχC1.continuous.pow 2).mul (continuous_finsetSum _ fun j _ => ?_)
    exact ((continuous_dCoord_of_contDiff hvmk j).norm.pow 2).add
      ((continuous_dbarCoord_of_contDiff hvmk j).norm.pow 2)
  have hχ_ev_zero : ∀ z, z ∉ tsupport χ → χ =ᶠ[𝓝 z] 0 := by
    intro z hz
    have hnbhd : (tsupport χ)ᶜ ∈ 𝓝 z := (isClosed_tsupport χ).isOpen_compl.mem_nhds hz
    filter_upwards [hnbhd] with w hw
    by_contra hne
    exact hw (subset_tsupport χ (Function.mem_support.mpr hne))
  have hdχ_off : ∀ z, z ∉ tsupport χ → fderiv ℝ χ z = 0 := by
    intro z hz
    rw [(hχ_ev_zero z hz).fderiv_eq]
    simp
  have hAvsupp : Function.support Av ⊆ tsupport χ := by
    intro z hz
    rw [Function.mem_support] at hz
    exact subset_tsupport χ (Function.mem_support.mpr fun h0 => hz (by simp [hAvdef, h0]))
  have hAvcs : HasCompactSupport Av :=
    hχcs.isCompact.of_isClosed_subset (isClosed_tsupport Av)
      ((closure_mono hAvsupp).trans (isClosed_tsupport χ).closure_subset)
  have hAv2 : Integrable (fun z => (Av z)^2) volume := by
    have hcs : HasCompactSupport (fun z => (Av z)^2) :=
      HasCompactSupport.of_support_subset_isCompact hχcs.isCompact (fun z hz => by
        simp only [Function.mem_support] at hz
        exact subset_tsupport χ (Function.mem_support.mpr
          (fun h0 => hz (by simp [hAvdef, h0]))))
    exact (hAvcont.pow 2).integrable_of_hasCompactSupport hcs
  have hBvsupp : Function.support Bv ⊆ tsupport χ := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hc
    exact hz (by simp [hBvdef, hdχ_off z hc])
  have hBvcs : HasCompactSupport Bv :=
    hχcs.isCompact.of_isClosed_subset (isClosed_tsupport Bv)
      ((closure_mono hBvsupp).trans (isClosed_tsupport χ).closure_subset)
  have hBv2 : Integrable (fun z => (Bv z)^2) volume := by
    have hcs : HasCompactSupport (fun z => (Bv z)^2) :=
      HasCompactSupport.of_support_subset_isCompact hχcs.isCompact (fun z hz => by
        simp only [Function.mem_support] at hz
        by_contra hc
        exact hz (by simp [hBvdef, hdχ_off z hc]))
    exact (hBvcont.pow 2).integrable_of_hasCompactSupport hcs
  have hEvsupp : Function.support Ev ⊆ tsupport χ := by
    intro z hz
    rw [Function.mem_support] at hz
    exact subset_tsupport χ (Function.mem_support.mpr fun h0 => hz (by simp [hEvdef, h0]))
  have hEvcs : HasCompactSupport Ev :=
    hχcs.isCompact.of_isClosed_subset (isClosed_tsupport Ev)
      ((closure_mono hEvsupp).trans (isClosed_tsupport χ).closure_subset)
  have hEvint : Integrable Ev volume := hEvcont.integrable_of_hasCompactSupport hEvcs
  have hfdeqv : ∀ z ∈ Work.CR.Flat.polydisc 0 s',
      fderiv ℝ (fun w => (v w)^k) z = fderiv ℝ (fun w => (u w)^k) z := by
    intro z hz
    have hev : (fun w => (v w)^k) =ᶠ[𝓝 z] (fun w => (u w)^k) := by
      filter_upwards [(Work.CR.Flat.isOpen_polydisc 0 s').mem_nhds hz] with w hw
      rw [hv_eq w hw]
    exact hev.fderiv_eq
  have hAeq : ∀ z, Av z = χ z * ‖fderiv ℝ (fun w => (u w)^k) z‖ := by
    intro z
    by_cases hz : z ∈ Work.CR.Flat.polydisc 0 s'
    · simp only [hAvdef, hfdeqv z hz]
    · have hzts : z ∉ tsupport χ := fun hc => hz (hχsupp' hc)
      have hχz : χ z = 0 := by
        by_contra hne
        exact hzts (subset_tsupport χ (Function.mem_support.mpr hne))
      simp [hAvdef, hχz]
  have hBeq : ∀ z, Bv z = ‖u z‖^k * ‖fderiv ℝ χ z‖ := by
    intro z
    by_cases hz : z ∈ Work.CR.Flat.polydisc 0 s'
    · simp only [hBvdef, hv_eq z hz]
    · have hzts : z ∉ tsupport χ := fun hc => hz (hχsupp' hc)
      simp [hBvdef, hdχ_off z hzts]
  have hEeq : ∀ z, Ev z = (χ z)^2 * ∑ j,
      (‖Work.CR.Flat.dCoord j (fun w => (u w)^k) z‖^2
        + ‖Work.CR.Flat.dbarCoord j (fun w => (u w)^k) z‖^2) := by
    intro z
    by_cases hz : z ∈ Work.CR.Flat.polydisc 0 s'
    · simp only [hEvdef, Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord, hfdeqv z hz]
    · have hzts : z ∉ tsupport χ := fun hc => hz (hχsupp' hc)
      have hχz : χ z = 0 := by
        by_contra hne
        exact hzts (subset_tsupport χ (Function.mem_support.mpr hne))
      simp [hEvdef, hχz]
  have hFcont : Continuous (fun z => fderiv ℝ W z) := hW.continuous_fderiv (by norm_num)
  have hW_ev_zero : ∀ z, z ∉ tsupport χ → W =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [hχ_ev_zero z hz] with w hw
    simp only [hWdef]
    simp [hw]
  have hF_off : ∀ z, z ∉ tsupport χ → fderiv ℝ W z = 0 := by
    intro z hz
    rw [(hW_ev_zero z hz).fderiv_eq]
    simp
  have hFcs : HasCompactSupport (fun z => fderiv ℝ W z) := by
    refine hχcs.isCompact.of_isClosed_subset (isClosed_tsupport (fun z => fderiv ℝ W z))
      ((closure_mono ?_).trans (isClosed_tsupport χ).closure_subset)
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hc
    exact hz (hF_off z hc)
  have hFint : Integrable (fun z => ‖fderiv ℝ W z‖^2) volume := by
    have hcs : HasCompactSupport (fun z => ‖fderiv ℝ W z‖^2) :=
      HasCompactSupport.of_support_subset_isCompact hχcs.isCompact (fun z hz => by
        simp only [Function.mem_support] at hz
        by_contra hc
        exact hz (by simp [hF_off z hc]))
    exact (hFcont.norm.pow 2).integrable_of_hasCompactSupport hcs
  have hL1 : (MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume)^2
      = ENNReal.ofReal (∫ z, ‖fderiv ℝ W z‖^2) :=
    eLpNormSqEqOfRealIntegral hFcont.aestronglyMeasurable hFint
  obtain ⟨M, hM0, hMbd⟩ := existsPolydiscSupBound hn hu hsρ
  have hvol_s_lt : volume (Work.CR.Flat.polydisc 0 s) < ⊤ := by
    rw [Work.NN.Core.volume_polydisc]
    refine ENNReal.prod_lt_top fun j _ => ?_
    rw [pow_two]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Work.CR.Flat.polydisc 0 s)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hvol_s_lt⟩
  have hmeasN : MeasureTheory.AEStronglyMeasurable (fun z => (u z)^k)
      (volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
    refine (hvmk.continuous.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet] with z hz
    rw [hv_eq z (hpoly_s' hz)]
  have hmeasN2 : MeasureTheory.AEStronglyMeasurable (fun z => ‖(u z)^k‖^2)
      (volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
    refine ((hvmk.continuous.norm.pow 2).aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet] with z hz
    show ‖v z ^ k‖ ^ 2 = ‖u z ^ k‖ ^ 2
    rw [hv_eq z (hpoly_s' hz)]
  have hNint : Integrable (fun z => ‖(u z)^k‖^2)
      (volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
    refine Integrable.of_bound hmeasN2 (M ^ (2*k)) ?_
    filter_upwards [ae_restrict_mem (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet] with z hz
    have h1 : ‖u z‖ ≤ M := hMbd z hz
    have h2 : ‖(u z)^k‖ = ‖u z‖^k := norm_pow _ _
    rw [Real.norm_of_nonneg (by positivity), h2]
    calc (‖u z‖^k)^2 = ‖u z‖^(2*k) := by rw [← pow_mul, Nat.mul_comm k 2]
      _ ≤ M^(2*k) := pow_le_pow_left₀ (norm_nonneg _) h1 (2*k)
  have hL2id : (MeasureTheory.eLpNorm (fun z => (u z)^k) 2
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)))^2
      = ENNReal.ofReal (∫ z in Work.CR.Flat.polydisc 0 s, ‖(u z)^k‖^2) :=
    eLpNormSqEqOfRealIntegral hmeasN hNint
  have hABint : Integrable (fun z => (Av z + Bv z)^2) volume := by
    have hcs : HasCompactSupport (fun z => (Av z + Bv z)^2) :=
      HasCompactSupport.of_support_subset_isCompact hχcs.isCompact (fun z hz => by
        simp only [Function.mem_support] at hz
        by_contra hc
        have hχz : χ z = 0 := by
          by_contra hne
          exact hc (subset_tsupport χ (Function.mem_support.mpr hne))
        exact hz (by simp [hAvdef, hBvdef, hχz, hdχ_off z hc]))
    exact ((hAvcont.add hBvcont).pow 2).integrable_of_hasCompactSupport hcs
  have hbd : ∀ z, ‖fderiv ℝ W z‖ ≤ Av z + Bv z := by
    intro z
    have h := hpt z
    rw [← hAeq z, ← hBeq z] at h
    simpa only [hWdef] using h
  have hstep1 : ∫ z, ‖fderiv ℝ W z‖^2 ≤ ∫ z, (Av z + Bv z)^2 :=
    integral_mono hFint hABint fun z => pow_le_pow_left₀ (norm_nonneg _) (hbd z) 2
  have hstep2 : ∫ z, (Av z + Bv z)^2
      ≤ 2 * (∫ z, (Av z)^2) + 2 * (∫ z, (Bv z)^2) := by
    have hpt2 : ∀ z, (Av z + Bv z)^2 ≤ 2 * (Av z)^2 + 2 * (Bv z)^2 :=
      fun z => by nlinarith [sq_nonneg (Av z - Bv z)]
    have h2int : Integrable (fun z => 2 * (Av z)^2 + 2 * (Bv z)^2) volume :=
      (hAv2.const_mul 2).add (hBv2.const_mul 2)
    have hsplit : ∫ z, (2 * (Av z)^2 + 2 * (Bv z)^2)
        = 2 * (∫ z, (Av z)^2) + 2 * (∫ z, (Bv z)^2) := by
      rw [integral_add (hAv2.const_mul 2) (hBv2.const_mul 2), integral_const_mul,
        integral_const_mul]
    calc ∫ z, (Av z + Bv z)^2 ≤ ∫ z, (2 * (Av z)^2 + 2 * (Bv z)^2) :=
          integral_mono hABint h2int hpt2
      _ = 2 * (∫ z, (Av z)^2) + 2 * (∫ z, (Bv z)^2) := hsplit
  have hstep3 : ∫ z, (Av z)^2 ≤ 8 * (n:ℝ) * ∫ z, Ev z := by
    have hpt3 : ∀ z, (Av z)^2 ≤ 8 * (n:ℝ) * Ev z := by
      intro z
      rw [hAvdef, hEvdef]
      calc (χ z * ‖fderiv ℝ (fun w => (v w)^k) z‖)^2
          = (χ z)^2 * ‖fderiv ℝ (fun w => (v w)^k) z‖^2 := by ring
        _ ≤ (χ z)^2 * (8 * (n:ℝ) * ∑ j, (‖Work.CR.Flat.dCoord j (fun w => (v w)^k) z‖^2
              + ‖Work.CR.Flat.dbarCoord j (fun w => (v w)^k) z‖^2)) :=
            mul_le_mul_of_nonneg_left (nnGradBound hn (fun w => (v w)^k) z) (sq_nonneg (χ z))
        _ = 8 * (n:ℝ) * ((χ z)^2 * ∑ j, (‖Work.CR.Flat.dCoord j (fun w => (v w)^k) z‖^2
              + ‖Work.CR.Flat.dbarCoord j (fun w => (v w)^k) z‖^2)) := by ring
    have h3int : Integrable (fun z => 8 * (n:ℝ) * Ev z) volume := hEvint.const_mul _
    have h := integral_mono hAv2 h3int hpt3
    rwa [integral_const_mul] at h
  have hstep4 : ∫ z, Ev z ≤ C₀ * ∫ z, (Bv z)^2 := by
    have hEv_off : ∀ z, z ∉ Work.CR.Flat.polydisc 0 ρ → Ev z = 0 := by
      intro z hz
      have hzts : z ∉ tsupport χ := fun hc => hz (hχsuppρ hc)
      have hχz : χ z = 0 := by
        by_contra hne
        exact hzts (subset_tsupport χ (Function.mem_support.mpr hne))
      simp [hEvdef, hχz]
    have hB_off : ∀ z, z ∉ Work.CR.Flat.polydisc 0 ρ → (Bv z)^2 = 0 := by
      intro z hz
      have hzts : z ∉ tsupport χ := fun hc => hz (hχsuppρ hc)
      simp [hBvdef, hdχ_off z hzts]
    have hBv2form : ∀ z, ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k = (Bv z)^2 := by
      intro z
      have h1 : (‖u z‖^2)^k = (‖u z‖^k)^2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      rw [hBeq z, h1]
      ring
    have hCacE : ∫ z in Work.CR.Flat.polydisc 0 ρ, Ev z
        = ∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 *
            (∑ j, (‖Work.CR.Flat.dCoord j (fun w => (u w)^k) z‖^2
              + ‖Work.CR.Flat.dbarCoord j (fun w => (u w)^k) z‖^2)) :=
      setIntegral_congr_fun (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
        (fun z _ => hEeq z)
    have hCacB : ∫ z in Work.CR.Flat.polydisc 0 ρ,
          ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k
        = ∫ z in Work.CR.Flat.polydisc 0 ρ, (Bv z)^2 :=
      setIntegral_congr_fun (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
        (fun z _ => hBv2form z)
    have h1 : ∫ z, Ev z = ∫ z in Work.CR.Flat.polydisc 0 ρ, Ev z :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hEv_off).symm
    have h2 : ∫ z, (Bv z)^2 = ∫ z in Work.CR.Flat.polydisc 0 ρ, (Bv z)^2 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hB_off).symm
    have hmain4 : ∫ z in Work.CR.Flat.polydisc 0 ρ, Ev z
        ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ, (Bv z)^2 := by
      rw [hCacE, ← hCacB]
      exact hCac
    calc ∫ z, Ev z = ∫ z in Work.CR.Flat.polydisc 0 ρ, Ev z := h1
      _ ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ, (Bv z)^2 := hmain4
      _ = C₀ * ∫ z, (Bv z)^2 := by rw [h2]
  have hstep5 : ∫ z, (Bv z)^2 ≤ L^2 * ∫ z in Work.CR.Flat.polydisc 0 s, ‖(u z)^k‖^2 := by
    have hB_off_s : ∀ z, z ∉ Work.CR.Flat.polydisc 0 s → (Bv z)^2 = 0 := by
      intro z hz
      have hzts : z ∉ tsupport χ := fun hc => hz (hχsupp hc)
      simp [hBvdef, hdχ_off z hzts]
    have h1 : ∫ z, (Bv z)^2 = ∫ z in Work.CR.Flat.polydisc 0 s, (Bv z)^2 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hB_off_s).symm
    have hlt : ∀ z, ‖fderiv ℝ χ z‖^2 ≤ L^2 := fun z =>
      pow_le_pow_left₀ (norm_nonneg _) (hL z) 2
    have hpt5 : ∀ z, (Bv z)^2 ≤ L^2 * ‖(u z)^k‖^2 := by
      intro z
      have h1' : (Bv z)^2 = ‖u z‖^(2*k) * ‖fderiv ℝ χ z‖^2 := by
        rw [hBeq z, mul_pow, ← pow_mul, Nat.mul_comm k 2]
      have h2' : ‖(u z)^k‖^2 = ‖u z‖^(2*k) := by
        rw [norm_pow, ← pow_mul, Nat.mul_comm k 2]
      calc (Bv z)^2 = ‖u z‖^(2*k) * ‖fderiv ℝ χ z‖^2 := h1'
        _ ≤ ‖u z‖^(2*k) * L^2 := mul_le_mul_of_nonneg_left (hlt z) (by positivity)
        _ = L^2 * ‖u z‖^(2*k) := by ring
        _ = L^2 * ‖(u z)^k‖^2 := by rw [h2']
    rw [h1]
    have hIntL : Integrable (fun z => (Bv z)^2)
        (volume.restrict (Work.CR.Flat.polydisc 0 s)) :=
      hBv2.mono_measure Measure.restrict_le_self
    have hIntR : Integrable (fun z => L^2 * ‖(u z)^k‖^2)
        (volume.restrict (Work.CR.Flat.polydisc 0 s)) := hNint.const_mul _
    have h := integral_mono hIntL hIntR hpt5
    rwa [integral_const_mul] at h
  have hnR : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h8n0 : (0:ℝ) ≤ 8 * (n:ℝ) := by positivity
  set IF : ℝ := ∫ z, ‖fderiv ℝ W z‖^2 with hIF
  set IE : ℝ := ∫ z, Ev z with hIE
  set IN : ℝ := ∫ z in Work.CR.Flat.polydisc 0 s, ‖(u z)^k‖^2 with hIN
  have hcombine : IF ≤ 2 * (1 + 8 * (n:ℝ) * C₀) * L^2 * IN := by
    have p1 : 8 * (n:ℝ) * IE ≤ 8 * (n:ℝ) * (C₀ * ∫ z, (Bv z)^2) :=
      mul_le_mul_of_nonneg_left hstep4 h8n0
    have p2 : 8 * (n:ℝ) * (C₀ * ∫ z, (Bv z)^2) ≤ 8 * (n:ℝ) * (C₀ * (L^2 * IN)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep5 hC₀) h8n0
    have hA2 : ∫ z, (Av z)^2 ≤ 8 * (n:ℝ) * C₀ * L^2 * IN := by
      have h := le_trans (le_trans hstep3 p1) p2
      calc ∫ z, (Av z)^2 ≤ 8 * (n:ℝ) * (C₀ * (L^2 * IN)) := h
        _ = 8 * (n:ℝ) * C₀ * L^2 * IN := by ring
    have hA := mul_le_mul_of_nonneg_left hA2 (by norm_num : (0:ℝ) ≤ 2)
    have hB := mul_le_mul_of_nonneg_left hstep5 (by norm_num : (0:ℝ) ≤ 2)
    have h12 := le_trans hstep1 hstep2
    calc IF ≤ 2 * (∫ z, (Av z)^2) + 2 * (∫ z, (Bv z)^2) := h12
      _ ≤ 2 * (8 * (n:ℝ) * C₀ * L^2 * IN) + 2 * (L^2 * IN) := add_le_add hA hB
      _ = 2 * (1 + 8 * (n:ℝ) * C₀) * L^2 * IN := by ring
  have hKnn : 0 ≤ 2 * (1 + 8 * (n:ℝ) * C₀) * L^2 := by
    have h1 : 0 ≤ 8 * (n:ℝ) * C₀ := mul_nonneg (mul_nonneg (by norm_num) hnR) hC₀
    have h2 : 0 ≤ 1 + 8 * (n:ℝ) * C₀ := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num) h2) (sq_nonneg L)
  calc (MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume)^2
      = ENNReal.ofReal IF := hL1
    _ ≤ ENNReal.ofReal (2 * (1 + 8 * (n:ℝ) * C₀) * L^2 * IN) :=
        ENNReal.ofReal_le_ofReal hcombine
    _ = ENNReal.ofReal (2 * (1 + 8 * (n:ℝ) * C₀) * L^2) * ENNReal.ofReal IN :=
        ENNReal.ofReal_mul hKnn
    _ = ENNReal.ofReal (2 * (1 + 8 * (n:ℝ) * C₀) * L^2)
          * (MeasureTheory.eLpNorm (fun z => (u z)^k) 2
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)))^2 := by
        rw [← hL2id]

end Work.NN.Core.Lev
