import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.gagliardoNirenbergGeomMean
import Submission.Work.NN.Core.Lev.realMoserAux
import Submission.Work.NN.Core.Lev.exists_polydisc_cutoff_lipschitz
import Submission.Work.NN.Core.Lev.moserStepEnergyBound
import Submission.Work.NN.Core.contDiff_one_mul_of_support
import Submission.Work.NN.Core.volume_polydisc

/-!
# The real-exponent Moser one-step boost
-/

namespace Work.NN.Core.Lev

set_option maxHeartbeats 4000000
open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter

noncomputable section

variable {n : ℕ}

/-- `a² ≤ ofReal c · b²` with `c ≥ 0` gives `a ≤ ofReal √c · b` in `ℝ≥0∞`. -/
lemma sq_le_ofReal_mul_sq {a b : ENNReal} {c : ℝ} (hc : 0 ≤ c)
    (h : a ^ (2:ℝ) ≤ ENNReal.ofReal c * b ^ (2:ℝ)) :
    a ≤ ENNReal.ofReal (Real.sqrt c) * b := by
  have hsq : ENNReal.ofReal (Real.sqrt c) ^ (2:ℝ) = ENNReal.ofReal c := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg c) (by norm_num),
      show (Real.sqrt c) ^ (2:ℝ) = Real.sqrt c ^ 2 from Real.rpow_two _, Real.sq_sqrt hc]
  have hZ : (ENNReal.ofReal (Real.sqrt c) * b) ^ (2:ℝ) = ENNReal.ofReal c * b ^ (2:ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq]
  refine (ENNReal.rpow_le_rpow_iff (show (0:ℝ) < 2 by norm_num)).mp ?_
  rw [hZ]; exact h

/-- `(x²)^γ = x^(2γ)` for `x ≥ 0`. -/
lemma sq_rpow_eq {x : ℝ} (hx : 0 ≤ x) (γ : ℝ) : (x ^ 2) ^ γ = x ^ (2 * γ) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]; norm_num

/-- `eLpNorm` of `z ↦ ((‖h z‖²)^γ : ℂ)` equals the `2γ`-th power of the `L^{2γp}`-norm of `‖h ·‖`. -/
lemma eLpNorm_normSq_rpow_eq {h : Cn n → ℂ} {γ : ℝ} (hγ : 0 < γ) {μ : MeasureTheory.Measure (Cn n)}
    {p : ENNReal}
    (hf : AEStronglyMeasurable (fun z => (((‖h z‖ ^ 2) ^ γ : ℝ) : ℂ)) μ)
    (hv : AEStronglyMeasurable (fun z => ‖h z‖) μ) :
    MeasureTheory.eLpNorm (fun z => (((‖h z‖ ^ 2) ^ γ : ℝ) : ℂ)) p μ
      = (MeasureTheory.eLpNorm (fun z => ‖h z‖) (p * ENNReal.ofReal (2 * γ)) μ) ^ (2 * γ) := by
  have hcont : Continuous (fun x : ℝ => ‖x‖ ^ (2 * γ)) :=
    continuous_norm.rpow_const (fun x => Or.inr (by positivity : (0:ℝ) ≤ 2 * γ))
  have hg : AEStronglyMeasurable (fun z => ‖(fun w : Cn n => ‖h w‖) z‖ ^ (2 * γ)) μ :=
    hcont.comp_aestronglyMeasurable hv
  refine (MeasureTheory.eLpNorm_congr_norm_ae hf hg ?_).trans ?_
  · refine Eventually.of_forall fun z => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (‖h z‖^2)^γ)]
    rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖(fun w : Cn n => ‖h w‖) z‖ ^ (2*γ))]
    rw [show ‖(fun w : Cn n => ‖h w‖) z‖ = ‖h z‖ from Real.norm_of_nonneg (norm_nonneg (h z))]
    exact sq_rpow_eq (norm_nonneg (h z)) γ
  · exact MeasureTheory.eLpNorm_norm_rpow (fun w : Cn n => ‖h w‖) hv (by linarith)


/-- **The Moser one-step boost, exponent `P ≥ 4`.** -/
theorem realMoserStep_high {n : ℕ} (hn : 0 < n) {CGN C : ℝ} (hC : 0 < C) (hCGN : 0 < CGN)
    (hGN : ∀ W : Cn n → ℂ, ContDiff ℝ 1 W → HasCompactSupport W →
      (MeasureTheory.eLpNorm W ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
          MeasureTheory.volume) ^ 2
        ≤ ENNReal.ofReal CGN * MeasureTheory.eLpNorm W 2 MeasureTheory.volume
            * MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume)
    {ρ s r : Fin n → ℝ} (hrs : ∀ j, r j < s j) (hsρ : ∀ j, s j < ρ j)
    {h : Cn n → ℂ} (hh : ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ))
    (hH : ∀ γ : ℝ, 1 ≤ γ → ∀ ψ : Cn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ ψ z) →
        ∫ z in Work.CR.Flat.polydisc 0 ρ, (ψ z) ^ 2 * ‖h z‖ ^ (2 * γ - 2) * wEnergy h z
          ≤ C * ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ ψ z‖ ^ 2 * ‖h z‖ ^ (2 * γ))
    {χ : Cn n → ℝ} (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Work.CR.Flat.polydisc 0 s) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hχinner : ∀ z ∈ Work.CR.Flat.polydisc 0 r, χ z = 1)
    {P L : ℝ} (hP : 4 ≤ P) (hL : 0 ≤ L) (hχL : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) :
    MeasureTheory.eLpNorm (fun z => ‖h z‖) (ENNReal.ofReal (P * moserQ n))
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      ≤ (ENNReal.ofReal (CGN * (3 + 4 * (n : ℝ) * P ^ 2 * C) * (1 + L))) ^ (1 / P)
        * MeasureTheory.eLpNorm (fun z => ‖h z‖) (ENNReal.ofReal P)
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
  have hP0 : 0 < P := by linarith [hP]
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set γ : ℝ := P / 4 with hγdef
  have hγ1 : 1 ≤ γ := by rw [hγdef]; linarith
  have hγ0 : 0 < γ := lt_of_lt_of_le one_pos hγ1
  have h4γ : 4 * γ = P := by rw [hγdef]; ring
  have h2γ : 2 * γ = P / 2 := by rw [hγdef]; ring
  have hsub_rs : Work.CR.Flat.polydisc 0 r ⊆ Work.CR.Flat.polydisc 0 s :=
    Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hrs j))
  have hsub_sρ : Work.CR.Flat.polydisc 0 s ⊆ Work.CR.Flat.polydisc 0 ρ :=
    Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hsρ j))
  have hsub_rρ : Work.CR.Flat.polydisc 0 r ⊆ Work.CR.Flat.polydisc 0 ρ := hsub_rs.trans hsub_sρ
  obtain ⟨M, hM0, hMbd⟩ := existsPolydiscSupBound hn hh hsρ
  obtain ⟨Kw, hKw0, hKwbd⟩ := exists_bound_wEnergy hsρ hh
  have hvol_lt : MeasureTheory.volume (Work.CR.Flat.polydisc 0 s) ≠ ⊤ := by
    rw [Work.NN.Core.volume_polydisc]
    exact ne_of_lt (ENNReal.prod_lt_top fun j _ =>
      ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top)
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hvol_lt
  set Q : ℝ := ∫ z in Work.CR.Flat.polydisc 0 s, ‖h z‖ ^ P with hQdef
  set Xe : ENNReal := MeasureTheory.eLpNorm (fun z => ‖h z‖) (ENNReal.ofReal P)
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) with hXedef
  set Ye : ENNReal := MeasureTheory.eLpNorm (fun z => ‖h z‖) (ENNReal.ofReal (P * moserQ n))
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)) with hYedef
  set qE : ENNReal := (2 : ENNReal) * ENNReal.ofReal (moserQ n) with hqEdef
  have hqE_bridge : NNReal.conjExponent (2 * n) = NNReal.conjExponent ((2 * n : ℕ) : ℝ≥0) := by
    congr 1
    push_cast
    ring
  have hqE_eq : ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal) = ENNReal.ofReal (moserQ n) := by
    rw [hqE_bridge, moserQ, ENNReal.ofReal_coe_nnreal]
  have hGN' : ∀ W : Cn n → ℂ, ContDiff ℝ 1 W → HasCompactSupport W →
      (MeasureTheory.eLpNorm W qE MeasureTheory.volume) ^ 2
        ≤ ENNReal.ofReal CGN * MeasureTheory.eLpNorm W 2 MeasureTheory.volume
            * MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume := by
    intro W h1 h2
    rw [hqEdef, ← hqE_eq]
    exact hGN W h1 h2
  -- AESM facts
  have hv_s : AEStronglyMeasurable (fun z => ‖h z‖)
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) :=
    ((hh.continuousOn.mono hsub_sρ).norm).aestronglyMeasurable
      (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet
  have hv_r : AEStronglyMeasurable (fun z => ‖h z‖)
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)) :=
    ((hh.continuousOn.mono hsub_rρ).norm).aestronglyMeasurable
      (Work.CR.Flat.isOpen_polydisc 0 r).measurableSet
  -- u and W
  set u : Cn n → ℂ := fun z => (((‖h z‖ ^ 2) ^ γ : ℝ) : ℂ) with hudef
  have hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) :=
    contDiffOn_normSq_rpow_complex h hγ1 hh
  have hu_c : ContinuousOn u (Work.CR.Flat.polydisc 0 ρ) := hu.continuousOn
  have hχzero : ∀ z, (∃ j, s j ≤ ‖z j‖) → χ z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hne)
    obtain ⟨j, hj⟩ := hz
    exact absurd (hχsupp hmem j) (not_lt.mpr (by simpa using hj))
  set W : Cn n → ℂ := fun z => (χ z : ℂ) * u z with hWdef
  have hWcd : ContDiff ℝ 1 W := by
    rw [hWdef]
    exact Work.NN.Core.contDiff_one_mul_of_support hχcd hχzero hsρ hu
  have hWcs : HasCompactSupport W := by
    have hts_eq : tsupport (fun z : Cn n => (χ z : ℂ)) = tsupport χ := by
      have hsupp_eq : Function.support (fun z : Cn n => (χ z : ℂ)) = Function.support χ := by
        ext z; simp [Function.mem_support]
      unfold tsupport; rw [hsupp_eq]
    have htsub : tsupport W ⊆ tsupport χ := by
      rw [hWdef]
      exact (tsupport_mul_subset_left (f := fun z : Cn n => (χ z : ℂ)) (g := u)).trans
        (le_of_eq hts_eq)
    exact hχcs.isCompact.of_isClosed_subset (isClosed_tsupport W) htsub
  -- norm of chi's derivative
  have hdchi_vec : ∀ z, fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z
      = Complex.ofRealCLM.comp (fderiv ℝ χ z) := by
    intro z
    rw [show (fun z : Cn n => (χ z : ℂ)) = Complex.ofRealCLM ∘ χ from rfl]
    rw [fderiv_comp z Complex.ofRealCLM.differentiableAt
      ((hχcd.differentiable (by simp)).differentiableAt)]
    rw [ContinuousLinearMap.fderiv]
  have hdchi_le : ∀ z, ‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ ≤ L := by
    intro z; rw [hdchi_vec z, norm_comp_ofRealCLM]; exact hχL z
  -- pointwise bound on the derivative of W
  have hpt : ∀ z ∈ Work.CR.Flat.polydisc 0 ρ,
      ‖fderiv ℝ W z‖ ^ 2 ≤ 2 * (‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ * ‖u z‖) ^ 2
        + 2 * (χ z * ‖fderiv ℝ u z‖) ^ 2 := by
    intro z hz
    have hd1 : DifferentiableAt ℝ (fun z : Cn n => (χ z : ℂ)) z :=
      Complex.ofRealCLM.differentiableAt.comp z ((hχcd.differentiable (by simp)).differentiableAt)
    have hd2 : DifferentiableAt ℝ u z := (hu.differentiableOn (by norm_num)).differentiableAt
      ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hz)
    have hmul : fderiv ℝ W z = (χ z : ℂ) • fderiv ℝ u z + u z • fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z := by
      rw [hWdef]; exact fderiv_mul hd1 hd2
    rw [hmul]
    have h1 : ‖(χ z : ℂ) • fderiv ℝ u z‖ = χ z * ‖fderiv ℝ u z‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hχ0 z)]
    have h2 : ‖u z • fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖
        = ‖u z‖ * ‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ := by
      rw [norm_smul]
    calc ‖(χ z : ℂ) • fderiv ℝ u z + u z • fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ ^ 2
        ≤ (χ z * ‖fderiv ℝ u z‖ + ‖u z‖ * ‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖) ^ 2 := by
          rw [← h1, ← h2]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ ≤ 2 * (χ z * ‖fderiv ℝ u z‖) ^ 2
            + 2 * (‖u z‖ * ‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖) ^ 2 := by
          have hs := sq_nonneg (χ z * ‖fderiv ℝ u z‖
            - ‖u z‖ * ‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖)
          nlinarith [hs]
      _ = 2 * (‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ * ‖u z‖) ^ 2
            + 2 * (χ z * ‖fderiv ℝ u z‖) ^ 2 := by ring
  -- pointwise bound on the derivative of u
  have hdu_le : ∀ z ∈ Work.CR.Flat.polydisc 0 ρ,
      ‖fderiv ℝ u z‖ ^ 2 ≤ 32 * (n:ℝ) * γ ^ 2 * ‖h z‖ ^ (P - 2) * wEnergy h z := by
    intro z hz
    have hZ : (‖h z‖ ^ 2) ^ (2 * (γ - 1)) * ‖h z‖ ^ 2 = ‖h z‖ ^ (P - 2) := by
      by_cases hz0 : ‖h z‖ = 0
      · rw [hz0, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
        have hP2 : P - 2 ≠ 0 := by linarith
        rw [Real.zero_rpow hP2]
        by_cases hg : 2 * (γ - 1) = 0
        · rw [hg, Real.rpow_zero, one_mul]
        · rw [Real.zero_rpow hg, zero_mul]
      · have hx : (0:ℝ) < ‖h z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
        have e1 : (‖h z‖ ^ 2) ^ (2 * (γ - 1)) = ‖h z‖ ^ (2 * (2 * (γ - 1))) :=
          sq_rpow_eq (norm_nonneg _) _
        rw [e1, ← Real.rpow_natCast (‖h z‖) 2, ← Real.rpow_add hx]
        congr 1; ring
    have h1 : ‖fderiv ℝ u z‖ ≤ γ * (‖h z‖ ^ 2) ^ (γ - 1) * (2 * ‖h z‖ * ‖fderiv ℝ h z‖) := by
      rw [hudef]
      exact normSq_rpow_fderiv_complex_le h hγ1 hh hz
    have h3 := pow_le_pow_left₀ (norm_nonneg (fderiv ℝ u z)) h1 2
    have h4 : (γ * (‖h z‖ ^ 2) ^ (γ - 1) * (2 * ‖h z‖ * ‖fderiv ℝ h z‖))^2
        = 4 * γ^2 * ((‖h z‖ ^ 2) ^ (2 * (γ - 1)) * ‖h z‖ ^ 2) * ‖fderiv ℝ h z‖^2 := by
      have e : ((‖h z‖ ^ 2) ^ (γ - 1))^2 = (‖h z‖ ^ 2) ^ (2 * (γ - 1)) := by
        rw [show ((‖h z‖ ^ 2) ^ (γ - 1))^2 = ((‖h z‖ ^ 2) ^ (γ - 1)) ^ (2:ℝ) from
          (Real.rpow_natCast ((‖h z‖ ^ 2) ^ (γ - 1)) 2).symm]
        rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ‖h z‖ ^ 2)]
        congr 1; ring
      calc (γ * (‖h z‖ ^ 2) ^ (γ - 1) * (2 * ‖h z‖ * ‖fderiv ℝ h z‖))^2
          = γ^2 * (((‖h z‖ ^ 2) ^ (γ - 1))^2) * (2 * ‖h z‖ * ‖fderiv ℝ h z‖)^2 := by ring
        _ = γ^2 * ((‖h z‖ ^ 2) ^ (2 * (γ - 1))) * (4 * ‖h z‖^2 * ‖fderiv ℝ h z‖^2) := by
            rw [e]; ring
        _ = 4 * γ^2 * ((‖h z‖ ^ 2) ^ (2 * (γ - 1)) * ‖h z‖ ^ 2) * ‖fderiv ℝ h z‖^2 := by ring
    rw [h4] at h3
    rw [hZ] at h3
    calc ‖fderiv ℝ u z‖ ^ 2
        ≤ 4 * γ^2 * ‖h z‖ ^ (P - 2) * ‖fderiv ℝ h z‖^2 := h3
      _ ≤ 4 * γ^2 * ‖h z‖ ^ (P - 2) * (8 * (n:ℝ) * wEnergy h z) :=
          mul_le_mul_of_nonneg_left (fderiv_le_wEnergy hn h z) (by positivity)
      _ = 32 * (n:ℝ) * γ ^ 2 * ‖h z‖ ^ (P - 2) * wEnergy h z := by ring
  have hnorm_u : ∀ z, ‖u z‖ ^ 2 = ‖h z‖ ^ P := by
    intro z
    have h1 : ‖u z‖ = (‖h z‖ ^ 2) ^ γ := by
      rw [hudef, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h1, show (((‖h z‖ ^ 2) ^ γ))^2 = (‖h z‖ ^ 2) ^ (2 * γ) from by
      rw [← Real.rpow_natCast ((‖h z‖ ^ 2) ^ γ) 2,
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ‖h z‖ ^ 2)]
      congr 1; ring]
    rw [sq_rpow_eq (norm_nonneg _)]
    congr 1; ring
  have hsuppW : Function.support W ⊆ Work.CR.Flat.polydisc 0 s := by
    intro z hz
    rw [Function.mem_support] at hz
    refine hχsupp (subset_tsupport χ (Function.mem_support.mpr fun h0 => ?_))
    exact hz (by rw [hWdef]; simp [h0])
  have hW_aesm : AEStronglyMeasurable W MeasureTheory.volume := hWcd.continuous.aestronglyMeasurable
  have hχoff : ∀ z ∉ Work.CR.Flat.polydisc 0 s, χ z = 0 := by
    intro z hz
    refine hχzero z ?_
    rw [Work.CR.Flat.mem_polydisc] at hz
    push Not at hz
    obtain ⟨j, hj⟩ := hz
    exact ⟨j, by simpa using hj⟩
  have hχderiv_off : ∀ z ∉ tsupport χ, fderiv ℝ χ z = 0 := by
    intro z hz
    have hnbhd : (tsupport χ)ᶜ ∈ 𝓝 z := (isClosed_tsupport χ).isOpen_compl.mem_nhds hz
    have hev : χ =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnbhd] with w hw
      by_contra hne
      exact hw (subset_tsupport χ (Function.mem_support.mpr hne))
    rw [hev.fderiv_eq]; simp
  have hF_off : ∀ z, z ∉ tsupport χ → fderiv ℝ W z = 0 := by
    intro z hz
    have hnbhd : (tsupport χ)ᶜ ∈ 𝓝 z := (isClosed_tsupport χ).isOpen_compl.mem_nhds hz
    have hev : W =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
      filter_upwards [hnbhd] with w hw
      have hw0 : χ w = 0 := by
        by_contra hne
        exact hw (subset_tsupport χ (Function.mem_support.mpr hne))
      rw [hWdef]; simp [hw0]
    rw [hev.fderiv_eq]; simp
  have hF_int : MeasureTheory.Integrable (fun z => ‖fderiv ℝ W z‖ ^ 2) MeasureTheory.volume := by
    have hcs : HasCompactSupport (fun z => ‖fderiv ℝ W z‖ ^ 2) :=
      HasCompactSupport.of_support_subset_isCompact hχcs.isCompact (fun z hz => by
        simp only [Function.mem_support] at hz
        by_contra hc
        exact hz (by simp [hF_off z hc]))
    exact ((hWcd.continuous_fderiv (by norm_num)).norm.pow 2).integrable_of_hasCompactSupport hcs
  have hp_aesm : AEStronglyMeasurable (fun z => ‖h z‖ ^ P)
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) :=
    (continuous_id.rpow_const (fun x => Or.inr hP0.le)).comp_aestronglyMeasurable hv_s
  have hQint : MeasureTheory.Integrable (fun z => ‖h z‖ ^ P)
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
    refine MeasureTheory.Integrable.of_bound hp_aesm (M ^ P) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet] with z hz
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) P)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hMbd z hz) hP0.le
  have hXP : Xe ^ P = ENNReal.ofReal Q := by
    rw [hXedef, eLpNorm_ofReal_rpow hP0 hv_s (Filter.Eventually.of_forall fun z => norm_nonneg _)]
    rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun z =>
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (h z)) hP0.le))]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hQint
      (Filter.Eventually.of_forall fun z => by positivity)]
  have hfu_s : AEStronglyMeasurable (fun z => (((‖h z‖ ^ 2) ^ γ : ℝ) : ℂ))
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) :=
    (hu.continuousOn.mono hsub_sρ).aestronglyMeasurable
      (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet
  have hfu_r : AEStronglyMeasurable (fun z => (((‖h z‖ ^ 2) ^ γ : ℝ) : ℂ))
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)) :=
    (hu.continuousOn.mono hsub_rρ).aestronglyMeasurable
      (Work.CR.Flat.isOpen_polydisc 0 r).measurableSet
  have hmosQ0 : 0 ≤ moserQ n := le_of_lt (moserQ_pos hn)
  have hexpP : ENNReal.ofReal P = (2 : ENNReal) * ENNReal.ofReal (2 * γ) := by
    rw [show (2:ENNReal) = ENNReal.ofReal (2:ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [← h4γ]; ring
  have hu_2 : MeasureTheory.eLpNorm u 2
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) = Xe ^ (2 * γ) := by
    rw [hXedef]
    rw [show MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s))
        = (MeasureTheory.eLpNorm (fun z => ‖h z‖) (ENNReal.ofReal P)
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)))^(2*γ) from by
      rw [hudef]
      rw [eLpNorm_normSq_rpow_eq hγ0 hfu_s hv_s, ← hexpP]]
  have h7 : MeasureTheory.eLpNorm W 2 MeasureTheory.volume ≤ Xe ^ (2 * γ) := by
    rw [← MeasureTheory.eLpNorm_restrict_eq_of_support_subset hW_aesm hsuppW]
    calc MeasureTheory.eLpNorm W 2 (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s))
        ≤ MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
          refine MeasureTheory.eLpNorm_mono hW_aesm.restrict (fun z => ?_)
          rw [hWdef]
          simp only [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg (hχ0 z)]
          exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 z)
      _ = Xe ^ (2 * γ) := hu_2
  have h6b : MeasureTheory.eLpNorm u qE (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      = Ye ^ (2 * γ) := by
    rw [hYedef]
    rw [show MeasureTheory.eLpNorm u qE (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
        = (MeasureTheory.eLpNorm (fun z => ‖h z‖) (ENNReal.ofReal (P * moserQ n))
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)))^(2*γ) from by
      rw [hudef, eLpNorm_normSq_rpow_eq hγ0 hfu_r hv_r]
      congr 1
      rw [hqEdef]
      rw [show (2 : ENNReal) = ENNReal.ofReal (2:ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * moserQ n)]
      congr 1; rw [← h4γ]; ring]
  have h6a : MeasureTheory.eLpNorm u qE (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      ≤ MeasureTheory.eLpNorm W qE MeasureTheory.volume := by
    have hae : u =ᵐ[MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)] W := by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (Work.CR.Flat.isOpen_polydisc 0 r).measurableSet] with z hz
      rw [hWdef]; simp only; rw [hχinner z hz, Complex.ofReal_one, one_mul]
    rw [MeasureTheory.eLpNorm_congr_ae hae]
    exact MeasureTheory.eLpNorm_mono_measure _ MeasureTheory.Measure.restrict_le_self
  set g1 : Cn n → ℝ := fun z => (‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ * ‖u z‖) ^ 2 with hg1def
  set g2 : Cn n → ℝ := fun z => (χ z * ‖fderiv ℝ u z‖) ^ 2 with hg2def
  have hint_u : MeasureTheory.Integrable (fun z => L ^ 2 * ‖u z‖ ^ 2)
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
    refine MeasureTheory.Integrable.of_bound ?_ (L ^ 2 * M ^ P) ?_
    · exact ((continuousOn_const.mul ((hu_c.mono hsub_sρ).norm.pow 2)).aestronglyMeasurable
        (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet)
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet] with z hz
      rw [Real.norm_of_nonneg (by positivity)]
      have h2 : ‖u z‖ ^ 2 ≤ M ^ P := by
        rw [hnorm_u]
        exact Real.rpow_le_rpow (norm_nonneg _) (hMbd z hz) hP0.le
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
  have hg1_le : ∫ z in Work.CR.Flat.polydisc 0 s, g1 z ≤ L ^ 2 * Q := by
    calc ∫ z in Work.CR.Flat.polydisc 0 s, g1 z
        ≤ ∫ z in Work.CR.Flat.polydisc 0 s, L ^ 2 * ‖u z‖ ^ 2 := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z => by positivity) hint_u
            (Filter.Eventually.of_forall fun z => ?_)
          rw [hg1def]
          have h1 : ‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ ≤ L := hdchi_le z
          have ha2 : ‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ ^ 2 ≤ L ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
          calc (‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ * ‖u z‖)^2
              = ‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖^2 * ‖u z‖^2 := by ring
            _ ≤ L^2 * ‖u z‖^2 := mul_le_mul_of_nonneg_right ha2 (by positivity)
      _ = L ^ 2 * ∫ z in Work.CR.Flat.polydisc 0 s, ‖u z‖ ^ 2 := by
          rw [MeasureTheory.integral_const_mul]
      _ = L ^ 2 * Q := by
          congr 1
          rw [hQdef]
          exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hnorm_u)
  have hwE_cont : ContinuousOn (fun z => wEnergy h z) (Work.CR.Flat.polydisc 0 s) := by
    have hcont_s : ContinuousOn (fderiv ℝ h) (Work.CR.Flat.polydisc 0 s) :=
      (hh.continuousOn_fderiv_of_isOpen (Work.CR.Flat.isOpen_polydisc 0 ρ) (by norm_num)).mono
        hsub_sρ
    have hcd : ∀ j : Fin n, ContinuousOn (fun z => Work.CR.Flat.dCoord j h z)
        (Work.CR.Flat.polydisc 0 s) := by
      intro j
      have h1 : ContinuousOn (fun z => fderiv ℝ h z (Pi.single j (1:ℂ)))
          (Work.CR.Flat.polydisc 0 s) := hcont_s.clm_apply continuousOn_const
      have h2 : ContinuousOn (fun z => fderiv ℝ h z (Pi.single j Complex.I))
          (Work.CR.Flat.polydisc 0 s) := hcont_s.clm_apply continuousOn_const
      unfold Work.CR.Flat.dCoord
      exact continuousOn_const.mul (h1.sub (continuousOn_const.mul h2))
    have hdcd : ∀ j : Fin n, ContinuousOn (fun z => Work.CR.Flat.dbarCoord j h z)
        (Work.CR.Flat.polydisc 0 s) := by
      intro j
      have h1 : ContinuousOn (fun z => fderiv ℝ h z (Pi.single j (1:ℂ)))
          (Work.CR.Flat.polydisc 0 s) := hcont_s.clm_apply continuousOn_const
      have h2 : ContinuousOn (fun z => fderiv ℝ h z (Pi.single j Complex.I))
          (Work.CR.Flat.polydisc 0 s) := hcont_s.clm_apply continuousOn_const
      unfold Work.CR.Flat.dbarCoord
      exact continuousOn_const.mul (h1.add (continuousOn_const.mul h2))
    unfold wEnergy
    refine continuousOn_finsetSum _ fun j _ => ((hcd j).norm.pow 2).add ((hdcd j).norm.pow 2)
  have hSig_cont : ContinuousOn (fun z => ‖h z‖ ^ (P-2) * wEnergy h z)
      (Work.CR.Flat.polydisc 0 s) :=
    ((continuous_id.rpow_const (fun x => Or.inr (by linarith : (0:ℝ) ≤ P-2))).comp_continuousOn
      ((hh.continuousOn.mono hsub_sρ).norm)).mul hwE_cont
  have hSigaesm : AEStronglyMeasurable (fun z => ‖h z‖ ^ (P-2) * wEnergy h z)
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) :=
    hSig_cont.aestronglyMeasurable (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet
  have hℓ : 1 ≤ P/2 := by linarith
  have hHapp : ∫ z in Work.CR.Flat.polydisc 0 ρ, χ z ^ 2 * ‖h z‖ ^ (P-2) * wEnergy h z
      ≤ C * ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ χ z‖ ^ 2 * ‖h z‖ ^ P := by
    have h0 := hH (P/2) hℓ χ hχcd hχcs (hχsupp.trans hsub_sρ) hχ0
    rw [show (2:ℝ)*(P/2) - 2 = P - 2 from by ring,
      show (2:ℝ)*(P/2) = P from by ring] at h0
    exact h0
  have hE1 : ∫ z in Work.CR.Flat.polydisc 0 s, χ z ^ 2 * ‖h z‖ ^ (P-2) * wEnergy h z
      = ∫ z in Work.CR.Flat.polydisc 0 ρ, χ z ^ 2 * ‖h z‖ ^ (P-2) * wEnergy h z := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Work.CR.Flat.polydisc 0 s) (f := fun z => χ z ^ 2 * ‖h z‖ ^ (P-2) * wEnergy h z)
        (fun z hz => by rw [hχoff z hz]; simp),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Work.CR.Flat.polydisc 0 ρ) (f := fun z => χ z ^ 2 * ‖h z‖ ^ (P-2) * wEnergy h z)
        (fun z hz => by rw [hχoff z (fun hc => hz (hsub_sρ hc))]; simp)]
  have hE2 : ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ χ z‖ ^ 2 * ‖h z‖ ^ P
      = ∫ z in Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ χ z‖ ^ 2 * ‖h z‖ ^ P := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Work.CR.Flat.polydisc 0 ρ) (f := fun z => ‖fderiv ℝ χ z‖ ^ 2 * ‖h z‖ ^ P)
        (fun z hz => by rw [hχderiv_off z (fun hc => hz (hsub_sρ (hχsupp hc)))]; simp),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Work.CR.Flat.polydisc 0 s) (f := fun z => ‖fderiv ℝ χ z‖ ^ 2 * ‖h z‖ ^ P)
        (fun z hz => by rw [hχderiv_off z (fun hc => hz (hχsupp hc))]; simp)]
  have hb : ∀ z ∈ Work.CR.Flat.polydisc 0 s,
      g2 z ≤ χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z) := by
    intro z hz
    rw [hg2def]
    have hdu := hdu_le z (hsub_sρ hz)
    calc (χ z * ‖fderiv ℝ u z‖) ^ 2
        = χ z ^ 2 * ‖fderiv ℝ u z‖ ^ 2 := by ring
      _ ≤ χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z) :=
          mul_le_mul_of_nonneg_left hdu (sq_nonneg (χ z))
  have hb_all : ∀ z, g2 z ≤ χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z) := by
    intro z
    by_cases hz : z ∈ Work.CR.Flat.polydisc 0 s
    · exact hb z hz
    · have h0 : g2 z = 0 := by
        simp only [hg2def]
        rw [hχoff z hz]; ring
      rw [h0]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (sq_nonneg γ)) (Real.rpow_nonneg (norm_nonneg _) _)) (wEnergy_nonneg h z))
  have hint_e : MeasureTheory.Integrable
      (fun z => χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z))
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
    refine MeasureTheory.Integrable.of_bound ?_ (32 * (n:ℝ) * γ^2 * Kw * M ^ (P-2)) ?_
    · have hcontf : ContinuousOn
          (fun z => χ z ^ 2 * (32 * (n:ℝ) * γ^2 * (‖h z‖ ^ (P-2) * wEnergy h z)))
          (Work.CR.Flat.polydisc 0 s) :=
        ((hχcd.continuous.continuousOn.mono hsub_sρ).pow 2).mul
          (continuousOn_const.mul hSig_cont)
      refine (hcontf.aestronglyMeasurable
        (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet).congr ?_
      filter_upwards with z
      ring
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet] with z hz
      have hnnf : (0:ℝ) ≤ χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z) :=
        mul_nonneg (sq_nonneg (χ z))
          (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg γ))
            (Real.rpow_nonneg (norm_nonneg (h z)) (P-2))) (wEnergy_nonneg h z))
      rw [Real.norm_of_nonneg hnnf]
      have hχ2 : χ z ^ 2 ≤ 1 := by nlinarith [hχ0 z, hχ1 z]
      have hp2 : ‖h z‖ ^ (P-2) ≤ M ^ (P-2) :=
        Real.rpow_le_rpow (norm_nonneg _) (hMbd z hz) (by linarith)
      have hw : wEnergy h z ≤ Kw := hKwbd z hz
      have hc : 32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z
          ≤ 32 * (n:ℝ) * γ^2 * M ^ (P-2) * Kw := by
        have h1 : ‖h z‖ ^ (P-2) * wEnergy h z ≤ M ^ (P-2) * Kw :=
          mul_le_mul hp2 hw (wEnergy_nonneg h z) (Real.rpow_nonneg hM0 (P-2))
        calc 32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z
            = 32 * (n:ℝ) * γ^2 * (‖h z‖ ^ (P-2) * wEnergy h z) := by ring
          _ ≤ 32 * (n:ℝ) * γ^2 * (M ^ (P-2) * Kw) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 32 * (n:ℝ) * γ^2 * M ^ (P-2) * Kw := by ring
      have hX : (0:ℝ) ≤ 32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z :=
        mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg γ))
          (Real.rpow_nonneg (norm_nonneg _) _)) (wEnergy_nonneg h z)
      calc χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z)
          ≤ 1 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z) :=
            mul_le_mul_of_nonneg_right hχ2 hX
        _ ≤ 1 * (32 * (n:ℝ) * γ^2 * M ^ (P-2) * Kw) :=
            mul_le_mul_of_nonneg_left hc (by norm_num)
        _ = 32 * (n:ℝ) * γ^2 * Kw * M ^ (P-2) := by ring
  have hg2_e : ∫ z in Work.CR.Flat.polydisc 0 s,
        χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z)
      ≤ 32 * (n:ℝ) * γ^2 * C * L^2 * Q := by
    calc ∫ z in Work.CR.Flat.polydisc 0 s,
            χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z)
        = 32 * (n:ℝ) * γ^2 *
            ∫ z in Work.CR.Flat.polydisc 0 s, χ z ^ 2 * ‖h z‖ ^ (P-2) * wEnergy h z := by
          rw [← MeasureTheory.integral_const_mul]
          congr 1; ext z; ring
      _ = 32 * (n:ℝ) * γ^2 *
            ∫ z in Work.CR.Flat.polydisc 0 ρ, χ z ^ 2 * ‖h z‖ ^ (P-2) * wEnergy h z := by
          rw [hE1]
      _ ≤ 32 * (n:ℝ) * γ^2 *
            (C * ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ χ z‖ ^ 2 * ‖h z‖ ^ P) :=
          mul_le_mul_of_nonneg_left hHapp (by positivity)
      _ = 32 * (n:ℝ) * γ^2 * C *
            ∫ z in Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ χ z‖ ^ 2 * ‖h z‖ ^ P := by
          rw [hE2]; ring
      _ ≤ 32 * (n:ℝ) * γ^2 * C * (L^2 * Q) := by
          gcongr
          calc ∫ z in Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ χ z‖ ^ 2 * ‖h z‖ ^ P
              ≤ ∫ z in Work.CR.Flat.polydisc 0 s, L ^ 2 * ‖h z‖ ^ P := by
                refine MeasureTheory.integral_mono_of_nonneg
                  (Filter.Eventually.of_forall fun z => by positivity)
                  (MeasureTheory.Integrable.const_mul hQint (L^2))
                  (Filter.Eventually.of_forall fun z => ?_)
                exact mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ (norm_nonneg _) (hχL z) 2)
                  (Real.rpow_nonneg (norm_nonneg _) P)
            _ = L ^ 2 * Q := by rw [MeasureTheory.integral_const_mul, hQdef]
      _ = 32 * (n:ℝ) * γ^2 * C * L^2 * Q := by ring
  have hg2_final : ∫ z in Work.CR.Flat.polydisc 0 s, g2 z ≤ 32 * (n:ℝ) * γ^2 * C * L^2 * Q :=
    (MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity)
      hint_e (Filter.Eventually.of_forall fun z => hb_all z)).trans hg2_e
  have hpt_s : ∀ z ∈ Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ W z‖ ^ 2 ≤ 2 * g1 z + 2 * g2 z := by
    intro z hz
    have h := hpt z (hsub_sρ hz)
    rw [hg1def, hg2def]
    exact h
  have hint2 : MeasureTheory.Integrable
      (fun z => 2 * (L ^ 2 * ‖u z‖ ^ 2)
        + 2 * (χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z)))
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) :=
    (MeasureTheory.Integrable.const_mul hint_u 2).add
      (MeasureTheory.Integrable.const_mul hint_e 2)
  have hInt_le : ∫ z in Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ W z‖ ^ 2
      ≤ (2 + 4 * (n:ℝ) * P^2 * C) * L^2 * Q := by
    have hstep : ∫ z in Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ W z‖ ^ 2
        ≤ ∫ z in Work.CR.Flat.polydisc 0 s,
            2 * (L ^ 2 * ‖u z‖ ^ 2)
            + 2 * (χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z)) := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => by positivity) hint2 ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet] with z hz
      have h1 := hpt_s z hz
      have h2 : g1 z ≤ L ^ 2 * ‖u z‖ ^ 2 := by
        rw [hg1def]
        have hb1 : ‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ ≤ L := hdchi_le z
        have hb2 : ‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ ^ 2 ≤ L ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb1 2
        calc (‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖ * ‖u z‖)^2
            = ‖fderiv ℝ (fun z : Cn n => (χ z : ℂ)) z‖^2 * ‖u z‖^2 := by ring
          _ ≤ L^2 * ‖u z‖^2 := mul_le_mul_of_nonneg_right hb2 (by positivity)
      have h3 : g2 z ≤ χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z) :=
        hb_all z
      linarith
    have hmid : ∫ z in Work.CR.Flat.polydisc 0 s,
            2 * (L ^ 2 * ‖u z‖ ^ 2)
            + 2 * (χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z))
        = 2 * (L ^ 2 * Q)
            + 2 * ∫ z in Work.CR.Flat.polydisc 0 s,
                χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z) := by
      rw [MeasureTheory.integral_add (MeasureTheory.Integrable.const_mul hint_u 2)
          (MeasureTheory.Integrable.const_mul hint_e 2),
        MeasureTheory.integral_const_mul (r := (2:ℝ)),
        MeasureTheory.integral_const_mul (r := (2:ℝ))]
      congr 2
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [hQdef]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hnorm_u)
    calc ∫ z in Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ W z‖ ^ 2
        ≤ _ := hstep
      _ = 2 * (L ^ 2 * Q)
            + 2 * ∫ z in Work.CR.Flat.polydisc 0 s,
                χ z ^ 2 * (32 * (n:ℝ) * γ^2 * ‖h z‖ ^ (P-2) * wEnergy h z) := hmid
      _ ≤ 2 * (L ^ 2 * Q) + 2 * (32 * (n:ℝ) * γ^2 * C * L^2 * Q) := by
          gcongr
      _ = (2 + 4 * (n:ℝ) * P^2 * C) * L^2 * Q := by
          have hγ2 : γ ^ 2 = P ^ 2 / 16 := by rw [hγdef]; ring
          rw [hγ2]; ring
  have h8a : (MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((2 + 4 * (n:ℝ) * P^2 * C) * L^2) * Xe ^ P := by
    rw [show (MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume) ^ (2:ℝ)
        = (MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume) ^ 2 from
      ENNReal.rpow_natCast _ 2,
      eLpNormSqEqOfRealIntegral ((hWcd.continuous_fderiv one_ne_zero).aestronglyMeasurable) hF_int,
      hXP]
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 + 4 * (n:ℝ) * P^2 * C) * L^2)]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Work.CR.Flat.polydisc 0 s) (f := fun z => ‖fderiv ℝ W z‖ ^ 2)
      (fun z hz => by rw [hF_off z (fun hc => hz (hχsupp hc))]; simp)]
    exact ENNReal.ofReal_le_ofReal hInt_le
  have h8 : MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume
      ≤ ENNReal.ofReal (Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) * L) * Xe ^ (2*γ) := by
    have hb : (Xe ^ (2 * γ)) ^ (2:ℝ) = Xe ^ P := by
      rw [← ENNReal.rpow_mul]; congr 1; linarith [h4γ]
    have hs := sq_le_ofReal_mul_sq (a := MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume)
      (b := Xe ^ (2*γ)) (c := (2 + 4 * (n:ℝ) * P^2 * C) * L^2) (by positivity) (by
        rw [hb]; exact h8a)
    rwa [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 + 4 * (n:ℝ) * P^2 * C) (L^2),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hL] at hs
  have hkey : Ye ^ P ≤ ENNReal.ofReal (CGN * (3 + 4 * (n:ℝ) * P^2 * C) * (1 + L)) * Xe ^ P := by
    have hPY : Ye ^ P = (Ye ^ (2*γ)) ^ (2:ℝ) := by
      rw [← ENNReal.rpow_mul]; congr 1; linarith [h4γ]
    calc Ye ^ P = (Ye ^ (2*γ)) ^ (2:ℝ) := hPY
      _ = (MeasureTheory.eLpNorm u qE
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))) ^ (2:ℝ) := by rw [h6b]
      _ ≤ (MeasureTheory.eLpNorm W qE MeasureTheory.volume) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow h6a (by norm_num)
      _ = (MeasureTheory.eLpNorm W qE MeasureTheory.volume) ^ 2 := ENNReal.rpow_natCast _ 2
      _ ≤ ENNReal.ofReal CGN * MeasureTheory.eLpNorm W 2 MeasureTheory.volume
            * MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume := hGN' W hWcd hWcs
      _ ≤ ENNReal.ofReal CGN * Xe ^ (2*γ)
            * (ENNReal.ofReal (Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) * L) * Xe ^ (2*γ)) :=
          mul_le_mul' (mul_le_mul' le_rfl h7) h8
      _ = ENNReal.ofReal (CGN * (Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) * L)) * Xe ^ P := by
          have hA : Xe ^ (2*γ) * Xe ^ (2*γ) = Xe ^ P := by
            rw [show Xe ^ (2*γ) * Xe ^ (2*γ) = (Xe ^ (2*γ)) ^ (2:ℝ) from by
              rw [ENNReal.rpow_two, pow_two], ← ENNReal.rpow_mul]
            congr 1; linarith [h4γ]
          have hCGN : ENNReal.ofReal CGN * ENNReal.ofReal (Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) * L)
              = ENNReal.ofReal (CGN * (Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) * L)) :=
            (ENNReal.ofReal_mul (le_of_lt hCGN)).symm
          calc ENNReal.ofReal CGN * Xe ^ (2*γ)
                * (ENNReal.ofReal (Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) * L) * Xe ^ (2*γ))
              = (ENNReal.ofReal CGN * ENNReal.ofReal (Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) * L))
                  * (Xe ^ (2*γ) * Xe ^ (2*γ)) := by ring
            _ = ENNReal.ofReal (CGN * (Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) * L))
                  * (Xe ^ (2*γ) * Xe ^ (2*γ)) := by rw [hCGN]
            _ = ENNReal.ofReal (CGN * (Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) * L)) * Xe ^ P := by
                rw [hA]
      _ ≤ ENNReal.ofReal (CGN * (3 + 4 * (n:ℝ) * P^2 * C) * (1 + L)) * Xe ^ P := by
          have key : CGN * (Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) * L)
              ≤ CGN * (3 + 4 * (n:ℝ) * P^2 * C) * (1 + L) := by
            have h0 : (0:ℝ) ≤ 2 + 4 * (n:ℝ) * P^2 * C := by positivity
            have h1 : Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) ≤ 1 + (2 + 4 * (n:ℝ) * P^2 * C) := by
              nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (2 + 4 * (n:ℝ) * P^2 * C),
                sq_nonneg (Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) - 1)]
            have h2 : Real.sqrt (2 + 4 * (n:ℝ) * P^2 * C) * L
                ≤ (1 + (2 + 4 * (n:ℝ) * P^2 * C)) * (1 + L) :=
              mul_le_mul h1 (by linarith) hL (by linarith)
            have h3 := mul_le_mul_of_nonneg_left h2 hCGN.le
            nlinarith [h3]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal key) le_rfl
  calc Ye = (Ye ^ P) ^ (1/P) := by
        rw [← ENNReal.rpow_mul, show P * (1/P) = 1 by field_simp, ENNReal.rpow_one]
    _ ≤ (ENNReal.ofReal (CGN * (3 + 4 * (n:ℝ) * P^2 * C) * (1 + L)) * Xe ^ P) ^ (1/P) :=
        ENNReal.rpow_le_rpow hkey (by positivity)
    _ = (ENNReal.ofReal (CGN * (3 + 4 * (n:ℝ) * P^2 * C) * (1 + L))) ^ (1/P) * Xe := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          show P * (1/P) = 1 by field_simp, ENNReal.rpow_one]

end
end Work.NN.Core.Lev
