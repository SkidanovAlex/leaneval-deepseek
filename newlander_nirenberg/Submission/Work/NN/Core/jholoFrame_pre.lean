import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.DbarCnPertAux
import Submission.Work.NN.Core.betaCoef_Bop_contDiff
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
import Submission.Work.CR.Flat.Cauchy.isClosedForm_dbarCoord_cutoff
import Submission.Work.CR.Flat.Holder.Bilinear

/-!
# Private copy of the `jholoFrame_aux` cut-off/Hölder toolkit

A verbatim (namespaced) copy of the auxiliary lemmas of
`Submission/Work/NN/Core/jholoFrame_aux.lean` that are needed by
`Work.NN.Core.jholoFrame_setup`, placed in the separate namespace
`Work.NN.Core.JFPre` so that `jholoFrame_setup` does not have to depend on the
(separately evolving) `jholoFrame_aux` module.
-/

namespace Work.NN.Core.JFPre

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

noncomputable section

variable {n : ℕ}

lemma jf_isCompact_closedPolydisc (r : Fin n → ℝ) :
    IsCompact {z : Cn n | ∀ j, ‖z j‖ ≤ r j} := by
  have h : {z : Cn n | ∀ j, ‖z j‖ ≤ r j}
      = Set.pi Set.univ (fun j => Metric.closedBall (0 : ℂ) (r j)) := by
    ext z
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [h]
  exact isCompact_univ_pi (fun j => isCompact_closedBall (0 : ℂ) (r j))

lemma jf_exists_cutoff_polydisc {σ ρ : Fin n → ℝ} (hσρ : ∀ j, σ j < ρ j) :
    ∃ (χ : Cn n → ℝ) (V : Set (Cn n)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρ ∧ IsOpen V ∧
      {z : Cn n | ∀ j, ‖z j‖ ≤ σ j} ⊆ V ∧ (∀ y ∈ V, χ y = 1) ∧
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) := by
  have hK : IsCompact {z : Cn n | ∀ j, ‖z j‖ ≤ σ j} := jf_isCompact_closedPolydisc σ
  have hU : IsOpen (Work.CR.Flat.polydisc 0 ρ) := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hKU : {z : Cn n | ∀ j, ‖z j‖ ≤ σ j} ⊆ Work.CR.Flat.polydisc 0 ρ :=
    fun z hz j => lt_of_le_of_lt (by simpa using hz j) (hσρ j)
  obtain ⟨R, -, hR⟩ := hK.isBounded.exists_pos_norm_le
  have hball : {z : Cn n | ∀ j, ‖z j‖ ≤ σ j} ⊆ Metric.ball (0 : Cn n) (R + 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (hR z hz) (lt_add_one R)
  have hU' : IsOpen (Work.CR.Flat.polydisc 0 ρ ∩ Metric.ball (0 : Cn n) (R + 1)) :=
    hU.inter Metric.isOpen_ball
  have hKU' : {z : Cn n | ∀ j, ‖z j‖ ≤ σ j} ⊆
      Work.CR.Flat.polydisc 0 ρ ∩ Metric.ball (0 : Cn n) (R + 1) :=
    fun z hz => ⟨hKU hz, hball hz⟩
  obtain ⟨V₀, hV₀o, hKV₀, hclV₀⟩ := hK.exists_isOpen_closure_subset (hU'.mem_nhdsSet.mpr hKU')
  obtain ⟨V, hVo, hKV, hclV⟩ := hK.exists_isOpen_closure_subset (hV₀o.mem_nhdsSet.mpr hKV₀)
  obtain ⟨f, hfsm, hfrange, hfsupp, hfone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) (s := V₀) (t := closure V)
      hV₀o isClosed_closure hclV
  have htsupp : tsupport f = closure V₀ := by rw [tsupport, hfsupp]
  refine ⟨f, V, hfsm, ?_, ?_, hVo, hKV, ?_, ?_⟩
  · rw [HasCompactSupport, htsupp]
    exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Cn n) (R + 1)) isClosed_closure
      (hclV₀.trans (inter_subset_right.trans Metric.ball_subset_closedBall))
  · intro z hz
    have hz' : z ∈ closure V₀ := by rw [← htsupp]; exact hz
    exact (hclV₀ hz').1
  · intro y hy
    exact (hfone y).mp (subset_closure hy)
  · intro z
    exact ⟨(hfrange (Set.mem_range_self z)).1, (hfrange (Set.mem_range_self z)).2⟩

lemma jf_exists_holder_const_of_contDiff_hasCompactSupport {φ : Cn n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) :
    ∃ L : ℝ, 0 < L ∧ (∀ z, ‖φ z‖ ≤ L) ∧ (∀ z z', ‖φ z - φ z'‖ ≤ L * ‖z - z'‖ ^ α) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hcont : Continuous φ := hφ1.continuous
  obtain ⟨C₁, hC₁⟩ := hcont.bounded_above_of_compact_support hc
  obtain ⟨C₂, hC₂⟩ := (hφ1.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (HasCompactSupport.fderiv ℝ hc)
  set M : ℝ := max 0 (max C₁ C₂) with hM
  have hM0 : 0 ≤ M := le_max_left _ _
  have hC₁M : ∀ z, ‖φ z‖ ≤ M := fun z =>
    le_trans (hC₁ z) (le_trans (le_max_left C₁ C₂) (le_max_right 0 (max C₁ C₂)))
  have hC₂M : ∀ z, ‖fderiv ℝ φ z‖ ≤ M := fun z =>
    le_trans (hC₂ z) (le_trans (le_max_right C₁ C₂) (le_max_right 0 (max C₁ C₂)))
  refine ⟨2 * M + 1, by positivity, fun z => le_trans (hC₁M z) (by linarith), ?_⟩
  intro z z'
  have hlip : ‖φ z - φ z'‖ ≤ M * ‖z - z'‖ := by
    have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := φ) (C := M)
      (fun y _ => hφ1.differentiable_one y) (fun y _ => hC₂M y)
      (x := z') (y := z) (Set.mem_univ _) (Set.mem_univ _)
    simpa using h
  by_cases h1 : ‖z - z'‖ ≤ 1
  · have h2 : ‖z - z'‖ ≤ ‖z - z'‖ ^ α := by
      rcases eq_or_lt_of_le (norm_nonneg (z - z')) with h | h
      · rw [← h, Real.zero_rpow (ne_of_gt hα0)]
      · simpa using Real.rpow_le_rpow_of_exponent_ge h h1 hα1
    calc ‖φ z - φ z'‖ ≤ M * ‖z - z'‖ := hlip
      _ ≤ M * ‖z - z'‖ ^ α := mul_le_mul_of_nonneg_left h2 hM0
      _ ≤ (2 * M + 1) * ‖z - z'‖ ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  · have h1' : 1 < ‖z - z'‖ := lt_of_not_ge h1
    have h2 : (1 : ℝ) ≤ ‖z - z'‖ ^ α := Real.one_le_rpow h1'.le hα0.le
    have h3 : ‖φ z - φ z'‖ ≤ 2 * M := by
      have h := norm_sub_le (φ z) (φ z')
      linarith [hC₁M z, hC₁M z']
    have h4 : 2 * M ≤ (2 * M + 1) * ‖z - z'‖ ^ α := by
      have h5 : (2 * M + 1) * 1 ≤ (2 * M + 1) * ‖z - z'‖ ^ α :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      linarith
    linarith [h3, h4]

lemma jf_eventuallyEq_zero_of_notMem_tsupport {f : Cn n → ℂ} {z : Cn n} (hz : z ∉ tsupport f) :
    f =ᶠ[nhds z] 0 := by
  change ∀ᶠ y in 𝓝 z, f y = (0 : Cn n → ℂ) y
  rw [Metric.eventually_nhds_iff]
  by_contra h
  push_neg at h
  refine hz (Metric.mem_closure_iff.mpr ?_)
  intro ε hε
  obtain ⟨y, hy, hyne⟩ := h ε hε
  exact ⟨y, Function.mem_support.mpr hyne, by rwa [dist_comm] at hy⟩

lemma jf_dCoord_eq_zero_of_eventuallyEq_zero {j : Fin n} {f : Cn n → ℂ} {z : Cn n}
    (h : f =ᶠ[nhds z] 0) : Work.CR.Flat.dCoord j f z = 0 := by
  have hfd : fderiv ℝ f z = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq h]
    simp
  simp [Work.CR.Flat.dCoord, hfd]

lemma jf_dCoord_mul_local (j : Fin n) (u w : Cn n → ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) (hw : DifferentiableAt ℝ w z) :
    Work.CR.Flat.dCoord j (fun z => u z * w z) z
      = Work.CR.Flat.dCoord j u z * w z + u z * Work.CR.Flat.dCoord j w z := by
  have hmul : (fun z => u z * w z) = u * w := by funext z; rw [Pi.mul_apply]
  rw [hmul]
  have hfg : fderiv ℝ (u * w) z = u z • fderiv ℝ w z + w z • fderiv ℝ u z := by
    simpa using (hu.hasFDerivAt.mul hw.hasFDerivAt).fderiv
  rw [Work.CR.Flat.dCoord, hfg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [Work.CR.Flat.dCoord, Work.CR.Flat.dCoord]
  ring

lemma jf_contDiff_one_mul_of_contDiffOn {U : Set (Cn n)} (hU : IsOpen U) {w : Cn n → ℂ}
    (hw : ContDiffOn ℝ 1 w U) {ψ : Cn n → ℂ} (hψ : ContDiff ℝ 1 ψ) (hts : tsupport ψ ⊆ U) :
    ContDiff ℝ 1 (fun z => w z * ψ z) := by
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  by_cases hz : z ∈ tsupport ψ
  · have h1 : ContDiffAt ℝ 1 w z := hw.contDiffAt (hU.mem_nhds (hts hz))
    exact h1.mul (hψ.contDiffAt)
  · have h0 : ψ =ᶠ[nhds z] 0 := jf_eventuallyEq_zero_of_notMem_tsupport hz
    have h1 : (fun y => w y * ψ y) =ᶠ[nhds z] (0 : Cn n → ℂ) := by
      filter_upwards [h0] with y hy
      simp [hy]
    have h2 : (fun y => w y * ψ y) =ᶠ[𝓝[Set.univ] z] (fun _ : Cn n => (0 : ℂ)) := by
      rw [nhdsWithin_univ]; exact h1
    have h3 : (fun y => w y * ψ y) z = (fun _ : Cn n => (0 : ℂ)) z := by
      have h4 : ψ z = (0 : Cn n → ℂ) z := h0.eq_of_nhds
      simp [h4]
    rw [← contDiffWithinAt_univ]
    exact (Filter.EventuallyEq.congr_contDiffWithinAt (f₁ := fun y => w y * ψ y)
      (f := fun _ : Cn n => (0 : ℂ)) (x := z) (s := Set.univ) h2 h3).mpr
      (contDiffWithinAt_const (c := (0 : ℂ)) (x := z) (s := Set.univ))

lemma jf_norm_mul_sub_le_of_holderOn {α B L M η : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hη0 : 0 ≤ η) {U : Set (Cn n)} {χ F : Cn n → ℂ} (hts : tsupport χ ⊆ U)
    (hχB : ∀ z, ‖χ z‖ ≤ B) (hχL : ∀ z z', ‖χ z - χ z'‖ ≤ L * ‖z - z'‖ ^ α)
    (hF : ∀ z ∈ U, ‖F z‖ ≤ M) (hFH : ∀ z ∈ U, ∀ z' ∈ U, ‖F z - F z'‖ ≤ η * ‖z - z'‖ ^ α) :
    (∀ z, ‖χ z * F z‖ ≤ B * M) ∧
      ∀ z z', ‖χ z * F z - χ z' * F z'‖ ≤ (B * η + M * L) * ‖z - z'‖ ^ α := by
  have hrpow : ∀ z z' : Cn n, (0:ℝ) ≤ ‖z - z'‖ ^ α := fun z z' =>
    Real.rpow_nonneg (norm_nonneg _) _
  constructor
  · intro z
    by_cases hz : χ z = 0
    · simp only [hz, zero_mul, norm_zero]
      exact mul_nonneg hB0 hM0
    · have hzU : z ∈ U := hts (subset_tsupport χ (Function.mem_support.mpr hz))
      calc ‖χ z * F z‖ = ‖χ z‖ * ‖F z‖ := norm_mul _ _
        _ ≤ B * M := mul_le_mul (hχB z) (hF z hzU) (norm_nonneg _) hB0
  · intro z z'
    have key : ‖χ z * F z - χ z' * F z'‖
        ≤ ‖χ z‖ * ‖F z - F z'‖ + ‖F z'‖ * ‖χ z - χ z'‖ := by
      calc ‖χ z * F z - χ z' * F z'‖
          = ‖χ z * (F z - F z') + (χ z - χ z') * F z'‖ := by ring_nf
        _ ≤ ‖χ z * (F z - F z')‖ + ‖(χ z - χ z') * F z'‖ := norm_add_le _ _
        _ = ‖χ z‖ * ‖F z - F z'‖ + ‖F z'‖ * ‖χ z - χ z'‖ := by
            rw [norm_mul, norm_mul, mul_comm ‖F z'‖]
    by_cases hz : χ z = 0
    · by_cases hz' : χ z' = 0
      · rw [hz, hz']
        simp only [zero_mul, sub_self, norm_zero]
        exact mul_nonneg (add_nonneg (mul_nonneg hB0 hη0) (mul_nonneg hM0 hL0)) (hrpow z z')
      · have hz'U : z' ∈ U := hts (subset_tsupport χ (Function.mem_support.mpr hz'))
        have h1 : ‖χ z * F z - χ z' * F z'‖ = ‖χ z' * F z'‖ := by
          rw [hz, zero_mul, zero_sub, norm_neg]
        rw [h1, norm_mul]
        have h2 : ‖χ z'‖ = ‖χ z' - χ z‖ := by rw [hz, sub_zero]
        rw [h2]
        calc ‖χ z' - χ z‖ * ‖F z'‖
            ≤ (L * ‖z' - z‖ ^ α) * M :=
              mul_le_mul (hχL z' z) (hF z' hz'U) (norm_nonneg _)
                (mul_nonneg hL0 (hrpow z' z))
          _ = (M * L) * ‖z - z'‖ ^ α := by rw [norm_sub_rev]; ring
          _ ≤ (B * η + M * L) * ‖z - z'‖ ^ α :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hB0 hη0)) (hrpow z z')
    · have hzU : z ∈ U := hts (subset_tsupport χ (Function.mem_support.mpr hz))
      by_cases hz' : χ z' = 0
      · have h1 : ‖χ z * F z - χ z' * F z'‖ = ‖χ z * F z‖ := by rw [hz', zero_mul, sub_zero]
        rw [h1, norm_mul]
        have h2 : ‖χ z‖ = ‖χ z - χ z'‖ := by rw [hz', sub_zero]
        rw [h2]
        calc ‖χ z - χ z'‖ * ‖F z‖
            ≤ (L * ‖z - z'‖ ^ α) * M :=
              mul_le_mul (hχL z z') (hF z hzU) (norm_nonneg _)
                (mul_nonneg hL0 (hrpow z z'))
          _ = (M * L) * ‖z - z'‖ ^ α := by ring
          _ ≤ (B * η + M * L) * ‖z - z'‖ ^ α :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hB0 hη0)) (hrpow z z')
      · have hz'U : z' ∈ U := hts (subset_tsupport χ (Function.mem_support.mpr hz'))
        calc ‖χ z * F z - χ z' * F z'‖
            ≤ ‖χ z‖ * ‖F z - F z'‖ + ‖F z'‖ * ‖χ z - χ z'‖ := key
          _ ≤ B * (η * ‖z - z'‖ ^ α) + M * (L * ‖z - z'‖ ^ α) :=
              add_le_add (mul_le_mul (hχB z) (hFH z hzU z' hz'U) (norm_nonneg _) hB0)
                (mul_le_mul (hF z' hz'U) (hχL z z') (norm_nonneg _) hM0)
          _ = (B * η + M * L) * ‖z - z'‖ ^ α := by ring

lemma jf_holderNorm_zero_le_ofReal {α : ℝ} {f : Cn n → ℂ} {B L : ℝ} (hB0 : 0 ≤ B)
    (hL0 : 0 ≤ L) (h1 : ∀ z, ‖f z‖ ≤ B) (h2 : ∀ z z', ‖f z - f z'‖ ≤ L * ‖z - z'‖ ^ α) :
    Work.CR.Flat.holderNorm 0 α f Set.univ ≤ ENNReal.ofReal (B + L) := by
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_one]
  refine le_trans (add_le_add ?_ ?_) (le_of_eq (ENNReal.ofReal_add hB0 hL0).symm)
  · rw [Work.CR.Flat.iterDerivNorm_zero]
    refine iSup₂_le fun z _ => ENNReal.ofReal_le_ofReal (h1 z)
  · simp only [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
    rw [div_le_iff₀ hpos]
    exact h2 x y

lemma jf_dbarCoord_eq_beltrami_implicit {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n} {u : Cn n → ℂ}
    {z : Cn n} {k : Fin n}
    (hk : Work.CR.Flat.dbarCoord k u z + Lcoef A u k z = 0) :
    Work.CR.Flat.dbarCoord k u z = ∑ j : Fin n,
      (betaCoef A k j z * Work.CR.Flat.dCoord j u z
        - starRingEnd ℂ (betaCoef A k j z) * Work.CR.Flat.dbarCoord j u z) := by
  have hL : Lcoef A u k z = (Complex.I / 2) * ∑ j : Fin n,
      ((A z (Pi.single k (1 : ℂ))) j * Work.CR.Flat.dCoord j u z
        + starRingEnd ℂ ((A z (Pi.single k (1 : ℂ))) j) * Work.CR.Flat.dbarCoord j u z) := by
    rw [Lcoef, fderiv_eq_sum_dCoord_dbarCoord]
  rw [hL] at hk
  have hconj : ∀ j : Fin n, starRingEnd ℂ (betaCoef A k j z)
      = (Complex.I / 2) * starRingEnd ℂ ((A z (Pi.single k (1 : ℂ))) j) := by
    intro j
    simp only [betaCoef, map_mul, map_neg, map_div₀, map_ofNat, Complex.conj_I]
    ring
  have hgoal : (∑ j : Fin n, (betaCoef A k j z * Work.CR.Flat.dCoord j u z
        - starRingEnd ℂ (betaCoef A k j z) * Work.CR.Flat.dbarCoord j u z))
      = (-(Complex.I / 2)) * ∑ j : Fin n,
          ((A z (Pi.single k (1 : ℂ))) j * Work.CR.Flat.dCoord j u z
            + starRingEnd ℂ ((A z (Pi.single k (1 : ℂ))) j) * Work.CR.Flat.dbarCoord j u z) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hconj j, betaCoef]
    ring
  rw [hgoal, hL] at *
  linear_combination hk

end

end Work.NN.Core.JFPre
