import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.conjAux
import Submission.Work.MRMT.Found.lintegralAbsDbar_comp_eq
import Submission.Work.MRMT.Found.differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto
import Submission.Work.MRMT.Found.tendstoLocallyUniformly_conj_comp
import Submission.Work.MRMT.Found.tendsto_lintegral_ofReal_mul_mul_of_tendsto_L2
import Submission.Work.MRMT.Found.ae_tendsto_defect_global
import Submission.Work.MRMT.Found.volume_preimage_null_localDiffeo
import Submission.Work.MRMT.Found.exists_isCompact_disjoint_tendsto_symm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-!
# The conjugate composite `star o phi o f o phi^{-1}` is holomorphic

Main result: `Work.MRMT.Found.conj_contDiff`. If `mu` is admissible, `phi` is a principal
solution of the Beltrami equation for `mu`, `f` is `C^1` and orientation reversing
(`|df| < |dbar f|`) off a set `S` meeting every compact set in a finite set, and the complex
dilatation of `f` satisfies `mu = pullRev mu f` almost everywhere, then
`z |-> conj (phi (f (phi^{-1} z)))` is complex differentiable.

The proof approximates `phi` by the `C^1` diffeomorphisms `F n` of `PrincipalData`:

* `G n = star o F n o f o (F n)^{-1}` is `C^1` and converges locally uniformly to `G`
  (`tendstoLocallyUniformly_conj_comp`);
* the `L^1`-size of `dbar (G n)` on a compact `L` is rewritten by the change of variables
  `lintegralAbsDbar_comp_eq` as the integral of `|nu n| * |dF n o f| * |dF n|` over
  `K = (F n)^{-1} '' L`, where `nu n` is the defect `conjNum - mu n * conjDen`; this tends to `0`
  by the engine `tendsto_lintegral_ofReal_mul_mul_of_tendsto_L2` together with the a.e.
  vanishing of the defect (`ae_tendsto_defect_global`, where `hrev` and `hinv` are used) and the
  pull-back bound `lintegral_comp_le_of_isCompact_disjoint`;
* `differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto` gives holomorphy on
  `(phi '' S)^c`, and Riemann's removable singularity theorem extends it over the isolated
  points of `phi '' S`.
-/

lemma isClosed_of_eventually_notMem {S : Set ℂ}
    (hS : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, w ∉ S) : IsClosed S := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  have h := hS z
  rw [eventually_nhdsWithin_iff] at h
  refine Filter.mem_of_superset h ?_
  intro x hx hxS
  by_cases hxz : x = z
  · exact hz (hxz ▸ hxS)
  · exact hx (by simpa [Set.mem_compl_iff] using hxz) hxS

private lemma finite_inter_isCompact {S : Set ℂ} (hS : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, w ∉ S)
    {K : Set ℂ} (hK : IsCompact K) : (S ∩ K).Finite := by
  classical
  have hex : ∀ z : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, w ≠ z → dist w z < r → w ∉ S := by
    intro z
    have h := hS z
    rw [eventually_nhdsWithin_iff] at h
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp h
    exact ⟨r, hr, fun w hw hdist =>
      hball (by simpa [Metric.mem_ball, dist_comm] using hdist) (by simpa [Set.mem_compl_iff] using hw)⟩
  choose R hRpos hR using hex
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : ↥K => Metric.ball (i : ℂ) (R (i : ℂ) / 2))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by linarith [hRpos x])⟩)
  refine (t.finite_toSet.image fun i : ↥K => (i : ℂ)).subset ?_
  intro z hz
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (ht hz.2)
  rw [Metric.mem_ball] at hzi
  have hlt : dist z (i : ℂ) < R (i : ℂ) := by linarith [hRpos (i : ℂ)]
  have hz_eq : z = (i : ℂ) := by
    by_contra hne
    exact hR (i : ℂ) z hne hlt hz.1
  exact ⟨i, hi, hz_eq.symm⟩

private lemma volume_eq_zero_of_eventually_notMem {S : Set ℂ}
    (hS : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, w ∉ S) :
    (MeasureTheory.volume : MeasureTheory.Measure ℂ) S = 0 := by
  have hfin : ∀ j : ℕ, (S ∩ Metric.closedBall (0 : ℂ) j).Finite := fun j =>
    finite_inter_isCompact hS (isCompact_closedBall (0 : ℂ) j)
  have hcov : S = ⋃ j : ℕ, (S ∩ Metric.closedBall (0 : ℂ) j) := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := exists_nat_ge ‖z‖
      exact Set.mem_iUnion.mpr ⟨j, hz, by rwa [Metric.mem_closedBall, dist_zero_right]⟩
    · intro hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      exact (Set.mem_inter_iff _ _ _).mp hj |>.1
  rw [hcov]
  refine le_antisymm ?_ bot_le
  calc (MeasureTheory.volume : MeasureTheory.Measure ℂ)
        (⋃ j : ℕ, (S ∩ Metric.closedBall (0 : ℂ) j))
      ≤ ∑' j : ℕ, (MeasureTheory.volume : MeasureTheory.Measure ℂ)
          (S ∩ Metric.closedBall (0 : ℂ) j) := measure_iUnion_le _
    _ = 0 := by simp [(hfin _).measure_zero]


private theorem star_contDiff : ContDiff ℝ 1 (star : ℂ → ℂ) := by
  have h : ContDiff ℝ 1 (fun z : ℂ => Complex.conjCLE z) :=
    ContinuousLinearEquiv.contDiff (Complex.conjCLE) (𝕜 := ℝ) (n := 1)
  have h2 : (fun z : ℂ => Complex.conjCLE z) = (star : ℂ → ℂ) := by
    funext z
    exact Complex.conjCLE_apply z
  rwa [h2] at h

private lemma measurable_star' : Measurable (star : ℂ → ℂ) := by
  have h : Measurable (fun z : ℂ => Complex.conjCLE z) := Complex.conjCLE.continuous.measurable
  have h2 : (fun z : ℂ => Complex.conjCLE z) = (star : ℂ → ℂ) := by
    funext z
    exact Complex.conjCLE_apply z
  rwa [h2] at h

private lemma continuous_dz_of_cd {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) : Continuous (Work.MRMT.dz g) := by
  have hc : Continuous fun p : ℂ × ℂ => fderiv ℝ g p.1 p.2 :=
    hg.continuous_fderiv_apply (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have h1 : Continuous fun z : ℂ => fderiv ℝ g z (1 : ℂ) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have hI : Continuous fun z : ℂ => fderiv ℝ g z Complex.I :=
    hc.comp (continuous_id.prodMk continuous_const)
  rw [show Work.MRMT.dz g = fun z : ℂ =>
    (fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) / 2 from rfl]
  exact (h1.sub (continuous_const.mul hI)).div_const 2

private lemma continuous_dzbar_of_cd {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) : Continuous (Work.MRMT.dzbar g) := by
  have hc : Continuous fun p : ℂ × ℂ => fderiv ℝ g p.1 p.2 :=
    hg.continuous_fderiv_apply (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have h1 : Continuous fun z : ℂ => fderiv ℝ g z (1 : ℂ) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have hI : Continuous fun z : ℂ => fderiv ℝ g z Complex.I :=
    hc.comp (continuous_id.prodMk continuous_const)
  rw [show Work.MRMT.dzbar g = fun z : ℂ =>
    (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) / 2 from rfl]
  exact (h1.add (continuous_const.mul hI)).div_const 2

/-! ## Bridges between `eLpNorm` bounds and `∫⁻ ‖·‖²` bounds -/

/-- `‖x‖ₑ ^ (2:ℝ) = ENNReal.ofReal ‖x‖ ^ 2`. -/
private lemma enorm_rpow_two (x : ℂ) : ‖x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [ENNReal.rpow_two]
  have h : ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by norm_num [enorm_eq_nnnorm]
  rw [h, ← ENNReal.ofReal_pow (norm_nonneg x)]

private lemma ofReal_sq_eq (r : ℝ) (hr : 0 ≤ r) : ENNReal.ofReal r ^ 2 = ENNReal.ofReal (r ^ 2) := by
  rw [← ENNReal.ofReal_pow hr]

/-- If `eLpNorm φ 2 ν ≤ ofReal δ` then `∫⁻ ‖φ z‖² ∂ν ≤ ofReal (δ²)`. -/
private lemma lintegral_normSq_le_of_eLpNorm_le {φ : ℂ → ℂ} {ν : MeasureTheory.Measure ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hφ : AEStronglyMeasurable φ ν)
    (h : MeasureTheory.eLpNorm φ 2 ν ≤ ENNReal.ofReal δ) :
    ∫⁻ z, ENNReal.ofReal (‖φ z‖ ^ 2) ∂ν ≤ ENNReal.ofReal (δ ^ 2) := by
  have h2 := MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (f := φ) (μ := ν)
    (by norm_num) (by norm_num) hφ
  rw [ENNReal.toReal_ofNat] at h2
  have h3 : (∫⁻ z, ‖φ z‖ₑ ^ (2:ℝ) ∂ν) ^ ((1:ℝ) / 2) ≤ ENNReal.ofReal δ := by
    rw [← h2]; exact h
  have h4 : (∫⁻ z, ‖φ z‖ₑ ^ (2:ℝ) ∂ν) ≤ (ENNReal.ofReal δ) ^ (2:ℝ) := by
    have h5 := ENNReal.rpow_le_rpow h3 (by norm_num : (0:ℝ) ≤ 2)
    rwa [← ENNReal.rpow_mul, show ((1:ℝ) / 2) * 2 = 1 by norm_num, ENNReal.rpow_one] at h5
  calc ∫⁻ z, ENNReal.ofReal (‖φ z‖ ^ 2) ∂ν
      = ∫⁻ z, ‖φ z‖ₑ ^ (2:ℝ) ∂ν := lintegral_congr fun z => (enorm_rpow_two (φ z)).symm
    _ ≤ (ENNReal.ofReal δ) ^ (2:ℝ) := h4
    _ = ENNReal.ofReal (δ ^ 2) := by rw [ENNReal.rpow_two, ofReal_sq_eq δ hδ]

/-- In `L²(ν)`, `eLpNorm`-convergence to `D` implies the Cauchy condition in the form used by
`tendsto_lintegral_ofReal_mul_mul_of_tendsto_L2`. -/
private lemma cauchy_lintegral_normSq_of_tendsto_eLpNorm {ν : MeasureTheory.Measure ℂ}
    {u : ℕ → ℂ → ℂ} {D : ℂ → ℂ}
    (hcon : Tendsto (fun n => MeasureTheory.eLpNorm (fun z => u n z - D z) 2 ν) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ z, ENNReal.ofReal (‖u n z - u m z‖ ^ 2) ∂ν ≤ ENNReal.ofReal ε := by
  intro ε hε
  set δ : ℝ := Real.sqrt (ε / 8) with hδdef
  have hδpos : 0 < δ := Real.sqrt_pos.mpr (by linarith)
  have hδsq : δ ^ 2 = ε / 8 := Real.sq_sqrt (by linarith)
  have hev : ∀ᶠ n in atTop,
      MeasureTheory.eLpNorm (fun z => u n z - D z) 2 ν ≤ ENNReal.ofReal δ :=
    hcon.eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr hδpos))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n m hn hm => ?_⟩
  have hmn : AEStronglyMeasurable (fun z => u n z - D z) ν :=
    MeasureTheory.aestronglyMeasurable_of_eLpNorm_ne_top
      (ne_of_lt (lt_of_le_of_lt (hN n hn) ENNReal.ofReal_lt_top))
  have hmm : AEStronglyMeasurable (fun z => u m z - D z) ν :=
    MeasureTheory.aestronglyMeasurable_of_eLpNorm_ne_top
      (ne_of_lt (lt_of_le_of_lt (hN m hm) ENNReal.ofReal_lt_top))
  have hbn := lintegral_normSq_le_of_eLpNorm_le hδpos.le hmn (hN n hn)
  have hbm := lintegral_normSq_le_of_eLpNorm_le hδpos.le hmm (hN m hm)
  have hpt : ∀ z : ℂ, ENNReal.ofReal (‖u n z - u m z‖ ^ 2)
      ≤ 2 * ENNReal.ofReal (‖u n z - D z‖ ^ 2) + 2 * ENNReal.ofReal (‖u m z - D z‖ ^ 2) := by
    intro z
    have h1 : ‖u n z - u m z‖ ≤ ‖u n z - D z‖ + ‖u m z - D z‖ := by
      have h : u n z - u m z = (u n z - D z) - (u m z - D z) := by ring
      rw [h]
      exact norm_sub_le _ _
    have h2 : ‖u n z - u m z‖ ^ 2
        ≤ 2 * ‖u n z - D z‖ ^ 2 + 2 * ‖u m z - D z‖ ^ 2 := by
      have hsq : ‖u n z - u m z‖ ^ 2
          ≤ (‖u n z - D z‖ + ‖u m z - D z‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [hsq, sq_nonneg (‖u n z - D z‖ - ‖u m z - D z‖)]
    have h2nn : (0 : ℝ) ≤ 2 := by norm_num
    have hprod : ENNReal.ofReal (2 * ‖u n z - D z‖ ^ 2 + 2 * ‖u m z - D z‖ ^ 2)
        = 2 * ENNReal.ofReal (‖u n z - D z‖ ^ 2) + 2 * ENNReal.ofReal (‖u m z - D z‖ ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul h2nn, ENNReal.ofReal_mul h2nn, ENNReal.ofReal_ofNat]
    rw [← hprod]
    exact ENNReal.ofReal_le_ofReal h2
  have hA_meas : AEMeasurable (fun z => ENNReal.ofReal (‖u n z - D z‖ ^ 2)) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hmn.aemeasurable.norm.pow_const 2)
  have hB_meas : AEMeasurable (fun z => ENNReal.ofReal (‖u m z - D z‖ ^ 2)) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hmm.aemeasurable.norm.pow_const 2)
  have hsplit : ∫⁻ z, (2 * ENNReal.ofReal (‖u n z - D z‖ ^ 2)
        + 2 * ENNReal.ofReal (‖u m z - D z‖ ^ 2)) ∂ν
      = 2 * (∫⁻ z, ENNReal.ofReal (‖u n z - D z‖ ^ 2) ∂ν)
        + 2 * (∫⁻ z, ENNReal.ofReal (‖u m z - D z‖ ^ 2) ∂ν) := by
    rw [lintegral_add_right' (fun z => 2 * ENNReal.ofReal (‖u n z - D z‖ ^ 2))
        (hB_meas.const_mul 2),
      lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
      lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
  have hfinal : (2 : ℝ≥0∞) * ENNReal.ofReal (δ ^ 2) + 2 * ENNReal.ofReal (δ ^ 2)
      ≤ ENNReal.ofReal ε := by
    have h4 : (4 : ℝ≥0∞) * ENNReal.ofReal (δ ^ 2) = ENNReal.ofReal (4 * (δ ^ 2)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
    calc (2 : ℝ≥0∞) * ENNReal.ofReal (δ ^ 2) + 2 * ENNReal.ofReal (δ ^ 2)
        = 4 * ENNReal.ofReal (δ ^ 2) := by ring
      _ = ENNReal.ofReal (4 * (δ ^ 2)) := h4
      _ = ENNReal.ofReal (ε / 2) := by rw [hδsq, show (4:ℝ) * (ε/8) = ε/2 by ring]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)
  calc ∫⁻ z, ENNReal.ofReal (‖u n z - u m z‖ ^ 2) ∂ν
      ≤ ∫⁻ z, (2 * ENNReal.ofReal (‖u n z - D z‖ ^ 2)
          + 2 * ENNReal.ofReal (‖u m z - D z‖ ^ 2)) ∂ν := lintegral_mono hpt
    _ = 2 * (∫⁻ z, ENNReal.ofReal (‖u n z - D z‖ ^ 2) ∂ν)
        + 2 * (∫⁻ z, ENNReal.ofReal (‖u m z - D z‖ ^ 2) ∂ν) := hsplit
    _ ≤ 2 * ENNReal.ofReal (δ ^ 2) + 2 * ENNReal.ofReal (δ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hbn (zero_le : (0:ℝ≥0∞) ≤ 2))
          (mul_le_mul_of_nonneg_left hbm (zero_le : (0:ℝ≥0∞) ≤ 2))
    _ ≤ ENNReal.ofReal ε := hfinal

private lemma lintegral_ofReal_pow_two_congr (ν : MeasureTheory.Measure ℂ) (g : ℂ → ℂ) :
    ∫⁻ z, ENNReal.ofReal ‖g z‖ ^ 2 ∂ν = ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) ∂ν :=
  lintegral_congr fun z => ofReal_sq_eq _ (norm_nonneg _)

private lemma ofReal_sq_sub_le (w x y : ℂ) :
    ENNReal.ofReal (‖w - x‖ ^ 2)
      ≤ 2 * ENNReal.ofReal (‖w - y‖ ^ 2) + 2 * ENNReal.ofReal (‖x - y‖ ^ 2) := by
  have h1 : ‖w - x‖ ≤ ‖w - y‖ + ‖x - y‖ := by
    have h : w - x = (w - y) - (x - y) := by ring
    rw [h]
    exact norm_sub_le _ _
  have h2 : ‖w - x‖ ^ 2 ≤ 2 * ‖w - y‖ ^ 2 + 2 * ‖x - y‖ ^ 2 := by
    have hsq : ‖w - x‖ ^ 2 ≤ (‖w - y‖ + ‖x - y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [hsq, sq_nonneg (‖w - y‖ - ‖x - y‖)]
  have h2nn : (0 : ℝ) ≤ 2 := by norm_num
  have hprod : ENNReal.ofReal (2 * ‖w - y‖ ^ 2 + 2 * ‖x - y‖ ^ 2)
      = 2 * ENNReal.ofReal (‖w - y‖ ^ 2) + 2 * ENNReal.ofReal (‖x - y‖ ^ 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul h2nn, ENNReal.ofReal_mul h2nn, ENNReal.ofReal_ofNat]
  rw [← hprod]
  exact ENNReal.ofReal_le_ofReal h2

/-! ## The integral limit -/

/-- The Wirtinger defect of the composite `star ∘ F ∘ f` at `z`, for a map `F` with coefficient `μn`. -/
private def conjDefect (μn f : ℂ → ℂ) (z : ℂ) : ℂ :=
  conjNum μn f z - μn z * conjDen μn f z

/-- `K`-truncation of the defect. -/
private def conjDefectTrunc (K : Set ℂ) (μn f : ℂ → ℂ) : ℂ → ℂ :=
  K.indicator (conjDefect μn f)

private theorem tendsto_lintegralAbsDbar_conj_of_defect {μ : ℂ → ℂ} (d : PrincipalData μ)
    {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) {S : Set ℂ}
    (hS : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, w ∉ S)
    (hrev : ∀ z ∉ S, ‖Work.MRMT.dz f z‖ < ‖Work.MRMT.dzbar f z‖)
    (hdefect : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), Filter.Tendsto
      (fun n => conjNum (d.μn n) f z - d.μn n z * conjDen (d.μn n) f z) Filter.atTop (nhds 0))
    {L : Set ℂ} (hL : IsCompact L) (hLdisj : Disjoint L ((d.φ : ℂ → ℂ) '' S)) :
    Filter.Tendsto (fun n => lintegralAbsDbar
      (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ)) L) Filter.atTop (nhds 0) := by
  classical
  obtain ⟨K, hKcpt, hKdisj, N, hKN⟩ := exists_isCompact_disjoint_tendsto_symm d hS hL hLdisj
  obtain ⟨C, hCpos, hCbound⟩ := lintegral_comp_le_of_isCompact_disjoint hf hrev hKcpt hKdisj
  obtain ⟨D, hDtend⟩ := d.dz_tendsto
  have hk0 : 0 ≤ d.k := le_trans (norm_nonneg (d.μn 0 0)) (d.norm_μn 0 0)
  have hΦcpt : IsCompact (f '' K) := hKcpt.image hf.continuous
  have hΨcpt : IsCompact (K ∪ f '' K) := hKcpt.union hΦcpt
  have hΨfin : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (K ∪ f '' K) ≠ ⊤ :=
    hΨcpt.measure_lt_top.ne
  -- ## 1. a uniform bound for the derivatives of `f` on `K`
  have hdzf_cont : Continuous (Work.MRMT.dz f) := continuous_dz_of_cd hf
  have hdzbf_cont : Continuous (Work.MRMT.dzbar f) := continuous_dzbar_of_cd hf
  obtain ⟨M, hMnn, hMK⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K,
      ‖Work.MRMT.dz f z‖ ≤ M ∧ ‖Work.MRMT.dzbar f z‖ ≤ M := by
    obtain ⟨M₁, hM₁⟩ := hKcpt.exists_bound_of_continuousOn hdzf_cont.continuousOn
    obtain ⟨M₂, hM₂⟩ := hKcpt.exists_bound_of_continuousOn hdzbf_cont.continuousOn
    refine ⟨max (max M₁ M₂) 0, le_max_right _ _, fun z hz => ⟨?_, ?_⟩⟩
    · exact (hM₁ z hz).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hM₂ z hz).trans ((le_max_right _ _).trans (le_max_left _ _))
  -- ## 2. the truncated defect `ν` and its properties
  have hDf_meas : ∀ n, Measurable (conjDefect (d.μn n) f) := by
    intro n
    have h1 : Measurable (fun z => Work.MRMT.dz f z) := hdzf_cont.measurable
    have h2 : Measurable (fun z => Work.MRMT.dzbar f z) := hdzbf_cont.measurable
    have h3 : Measurable (fun z => d.μn n (f z)) :=
      (d.contDiff_μn n).continuous.measurable.comp hf.continuous.measurable
    have h4 : Measurable (fun z => d.μn n z) := (d.contDiff_μn n).continuous.measurable
    have hst3 : Measurable (fun z => star (d.μn n (f z))) := measurable_star'.comp h3
    have hst1 : Measurable (fun z => star (Work.MRMT.dz f z)) := measurable_star'.comp h1
    have hst2 : Measurable (fun z => star (Work.MRMT.dzbar f z)) := measurable_star'.comp h2
    have hnum : Measurable (fun z => conjNum (d.μn n) f z) := by
      simp only [conjNum]; exact hst1.add (hst3.mul h2)
    have hden : Measurable (fun z => conjDen (d.μn n) f z) := by
      simp only [conjDen]; exact hst2.add (hst3.mul h1)
    rw [show conjDefect (d.μn n) f = fun z => conjNum (d.μn n) f z - d.μn n z * conjDen (d.μn n) f z from rfl]
    exact hnum.sub (h4.mul hden)
  have hνmeas : ∀ n, AEStronglyMeasurable (conjDefectTrunc K (d.μn n) f)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := fun n =>
    (hDf_meas n).aestronglyMeasurable.indicator hKcpt.measurableSet
  have hνval : ∀ n z, z ∈ K → conjDefectTrunc K (d.μn n) f z = conjDefect (d.μn n) f z :=
    fun n z hz => Set.indicator_of_mem hz _
  have hνzero : ∀ n z, z ∉ K → conjDefectTrunc K (d.μn n) f z = 0 :=
    fun n z hz => Set.indicator_of_notMem hz _
  have hν0 : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Tendsto (fun n => conjDefectTrunc K (d.μn n) f z) atTop (nhds 0) := by
    filter_upwards [hdefect] with z hz
    by_cases hzK : z ∈ K
    · rw [show (fun n => conjDefectTrunc K (d.μn n) f z)
          = fun n => conjDefect (d.μn n) f z from funext fun n => hνval n z hzK]
      simpa only [conjDefect] using hz
    · rw [show (fun n => conjDefectTrunc K (d.μn n) f z) = fun _ => (0:ℂ) from
        funext fun n => hνzero n z hzK]
      exact tendsto_const_nhds
  have hνb : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖conjDefectTrunc K (d.μn n) f z‖ ≤ B := by
    refine ⟨(1 + d.k) ^ 2 * M, by positivity, fun n => Eventually.of_forall fun z => ?_⟩
    by_cases hzK : z ∈ K
    · rw [hνval n z hzK]
      have hcn := norm_conjNum_le (μF := d.μn n) (f := f) hk0 (d.norm_μn n (f z))
        (hMK z hzK).1 (hMK z hzK).2
      have hcd := norm_conjDen_le (μF := d.μn n) (f := f) hk0 (d.norm_μn n (f z))
        (hMK z hzK).1 (hMK z hzK).2
      have hb : ‖conjDefect (d.μn n) f z‖ ≤ (1 + d.k) * M + d.k * ((1 + d.k) * M) := by
        rw [show conjDefect (d.μn n) f z
          = conjNum (d.μn n) f z - d.μn n z * conjDen (d.μn n) f z from rfl]
        refine (norm_sub_le _ _).trans (add_le_add hcn ?_)
        rw [norm_mul]
        exact mul_le_mul (d.norm_μn n z) hcd (norm_nonneg _) hk0
      calc ‖conjDefect (d.μn n) f z‖ ≤ (1 + d.k) * M + d.k * ((1 + d.k) * M) := hb
        _ = (1 + d.k) ^ 2 * M := by ring
    · rw [hνzero n z hzK]
      simpa using (show (0:ℝ) ≤ (1 + d.k) ^ 2 * M by positivity)
  -- ## 3. `ρ = ∂F n` is Cauchy in `L²(K ∪ f '' K)` and uniformly bounded in `L²` after a shift
  have hρmeas : ∀ n, AEStronglyMeasurable (fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    fun n => (continuous_dz_of_cd (d.contDiff_Fn n)).measurable.aestronglyMeasurable
  have hconvρ : Tendsto (fun n => MeasureTheory.eLpNorm
      (fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z - D z) 2
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict (K ∪ f '' K))) atTop (nhds 0) :=
    hDtend (K ∪ f '' K) hΨcpt
  have hcauρ := cauchy_lintegral_normSq_of_tendsto_eLpNorm
    (ν := (MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict (K ∪ f '' K)) hconvρ
  obtain ⟨N₁, hN₁⟩ := hcauρ 1 (by norm_num)
  have hbase_fin : ∫⁻ z in K ∪ f '' K,
      ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2) ≠ ⊤ := by
    obtain ⟨M₀, hM₀⟩ := hΨcpt.exists_bound_of_continuousOn
      (continuous_dz_of_cd (d.contDiff_Fn N₁)).continuousOn
    have hle : ∫⁻ z in K ∪ f '' K,
        ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)
        ≤ ENNReal.ofReal (M₀ ^ 2) * (MeasureTheory.volume : MeasureTheory.Measure ℂ) (K ∪ f '' K) := by
      calc ∫⁻ z in K ∪ f '' K, ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)
          ≤ ∫⁻ _z in K ∪ f '' K, ENNReal.ofReal (M₀ ^ 2) := by
            refine setLIntegral_mono_ae' hΨcpt.measurableSet (Eventually.of_forall fun z hz => ?_)
            exact ENNReal.ofReal_le_ofReal (by nlinarith [hM₀ z hz, norm_nonneg (Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z)])
        _ = ENNReal.ofReal (M₀ ^ 2) * (MeasureTheory.volume : MeasureTheory.Measure ℂ) (K ∪ f '' K) := by
            rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΨfin) hle
  have hρbdd : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ∫⁻ z in K ∪ f '' K,
      ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z‖ ^ 2) ≤ ENNReal.ofReal B := by
    refine ⟨2 + 2 * (∫⁻ z in K ∪ f '' K,
      ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)).toReal, by positivity, fun n => ?_⟩
    have hpt : ∀ z : ℂ, ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z‖ ^ 2)
        ≤ 2 * ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z
              - Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)
          + 2 * ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2) := by
      intro z
      have h := ofReal_sq_sub_le (Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z) 0
        (Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z)
      simpa using h
    have hfin : ∫⁻ z in K ∪ f '' K,
        ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)
        = ENNReal.ofReal ((∫⁻ z in K ∪ f '' K,
          ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)).toReal) :=
      (ENNReal.ofReal_toReal hbase_fin).symm
    have hcau := hN₁ (n + N₁) N₁ (by omega) le_rfl
    calc ∫⁻ z in K ∪ f '' K, ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z‖ ^ 2)
        ≤ ∫⁻ z in K ∪ f '' K, (2 * ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z
              - Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)
            + 2 * ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)) :=
          lintegral_mono hpt
      _ = 2 * (∫⁻ z in K ∪ f '' K, ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z
              - Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2))
          + 2 * (∫⁻ z in K ∪ f '' K,
              ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)) := by
          rw [lintegral_add_right' (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict (K ∪ f '' K))
            (fun z => 2 * ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z
              - Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2))
            (by
              have hg : AEMeasurable (fun z : ℂ =>
                  ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2))
                  (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
                ENNReal.measurable_ofReal.comp_aemeasurable
                  (((hρmeas N₁).aemeasurable.norm).pow_const 2)
              exact (hg.const_mul 2).mono_measure MeasureTheory.Measure.restrict_le_self),
            lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
            lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
      _ ≤ 2 * ENNReal.ofReal 1 + 2 * (∫⁻ z in K ∪ f '' K,
              ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hcau (zero_le : (0:ℝ≥0∞) ≤ 2)) le_rfl
      _ ≤ ENNReal.ofReal (2 + 2 * (∫⁻ z in K ∪ f '' K,
              ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)).toReal) := by
          have hS : (∫⁻ z in K ∪ f '' K,
              ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2))
              ≤ ENNReal.ofReal ((∫⁻ z in K ∪ f '' K,
              ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn N₁) : ℂ → ℂ) z‖ ^ 2)).toReal) :=
            le_of_eq (ENNReal.ofReal_toReal hbase_fin).symm
          refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left hS (zero_le : (0:ℝ≥0∞) ≤ 2))).trans ?_
          rw [ENNReal.ofReal_one, mul_one, ← ENNReal.ofReal_ofNat (n := 2),
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ← ENNReal.ofReal_add (by norm_num) (by positivity)]

  -- ## 4. the engine
  have hν0' : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Tendsto (fun n => conjDefectTrunc K (d.μn (n + N₁)) f z) atTop (nhds 0) := by
    filter_upwards [hν0] with z hz
    exact hz.comp (tendsto_add_atTop_nat N₁)
  have hνb' : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖conjDefectTrunc K (d.μn (n + N₁)) f z‖ ≤ B := by
    obtain ⟨B, hB0, hB⟩ := hνb
    exact ⟨B, hB0, fun n => hB (n + N₁)⟩
  have hcauρ' : ∀ ε : ℝ, 0 < ε → ∃ N' : ℕ, ∀ n m : ℕ, N' ≤ n → N' ≤ m →
      ∫⁻ z in K ∪ f '' K, ENNReal.ofReal (‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z
        - Work.MRMT.dz ((d.Fn (m + N₁)) : ℂ → ℂ) z‖ ^ 2) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N', hN'⟩ := hcauρ ε hε
    exact ⟨N', fun n m hn hm => hN' (n + N₁) (m + N₁) (by omega) (by omega)⟩
  have hρbdd' : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ∫⁻ z in K ∪ f '' K,
      ENNReal.ofReal ‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z‖ ^ 2 ≤ ENNReal.ofReal B := by
    obtain ⟨B, hB0, hB⟩ := hρbdd
    refine ⟨B, hB0, fun n => ?_⟩
    rw [lintegral_ofReal_pow_two_congr]
    exact hB n
  have hcauρ'' : ∀ ε : ℝ, 0 < ε → ∃ N' : ℕ, ∀ n m : ℕ, N' ≤ n → N' ≤ m →
      ∫⁻ z in K ∪ f '' K, ENNReal.ofReal ‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z
        - Work.MRMT.dz ((d.Fn (m + N₁)) : ℂ → ℂ) z‖ ^ 2 ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N', hN'⟩ := hcauρ' ε hε
    refine ⟨N', fun n m hn hm => ?_⟩
    rw [lintegral_ofReal_pow_two_congr]
    exact hN' n m hn hm
  have hmain : Tendsto (fun n => ∫⁻ z in K, ENNReal.ofReal
      (‖conjDefectTrunc K (d.μn (n + N₁)) f z‖
        * ‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) (f z)‖
        * ‖Work.MRMT.dz ((d.Fn (n + N₁)) : ℂ → ℂ) z‖)) atTop (nhds 0) :=
    tendsto_lintegral_ofReal_mul_mul_of_tendsto_L2 hKcpt.measurableSet hKcpt.measure_lt_top.ne
      hΦcpt.measurableSet hΦcpt.measure_lt_top.ne hf.continuous ⟨C, hCpos, hCbound⟩
      (fun n => hνmeas (n + N₁)) hν0' hνb' (fun n => hρmeas (n + N₁)) hcauρ'' hρbdd'
  -- ## 5. change of variables and comparison with the engine's integrand
  have himg : ∀ n, ((d.Fn n) : ℂ → ℂ) '' (((d.Fn n).symm : ℂ → ℂ) '' L) = L := by
    intro n
    rw [Set.image_image]
    have h : (fun x => (d.Fn n) ((d.Fn n).symm x)) = id := by
      funext x; exact Homeomorph.apply_symm_apply _ x
    rw [h, Set.image_id]
  have hcmp : ∀ n ≥ N, lintegralAbsDbar
        (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ)) L
      ≤ ∫⁻ z in K, ENNReal.ofReal (‖conjDefectTrunc K (d.μn n) f z‖
          * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) (f z)‖
          * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖) := by
    intro n hn
    have hK'cpt : IsCompact (((d.Fn n).symm : ℂ → ℂ) '' L) :=
      hL.image (d.contDiff_symm_Fn n).continuous
    have hK'sub : (((d.Fn n).symm : ℂ → ℂ) '' L) ⊆ K := fun z hz => by
      obtain ⟨w, hwL, rfl⟩ := hz
      exact hKN n hn w hwL
    have hcd : ContDiff ℝ 1 (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f) := by
      have h := star_contDiff.comp ((d.contDiff_Fn n).comp hf)
      simpa [Function.comp_assoc] using h
    obtain ⟨Cn, hCn⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK'cpt
      hcd.locallyLipschitz.locallyLipschitzOn
    have hcv := lintegralAbsDbar_comp_eq (F := d.Fn n) (μF := d.μn n)
      (H := star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f) (K := ((d.Fn n).symm : ℂ → ℂ) '' L) hK'cpt
      (d.contDiff_Fn n) (d.contDiff_symm_Fn n) (d.beltrami_Fn n) Cn hCn
    rw [show ((d.Fn n) : ℂ → ℂ) '' (((d.Fn n).symm : ℂ → ℂ) '' L) = L from himg n] at hcv
    rw [show ((star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f) ∘ ((d.Fn n).symm : ℂ → ℂ))
        = (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ)) from rfl] at hcv
    rw [hcv]
    unfold lintegralAbsBeltrami
    have hpt : ∀ z ∈ (((d.Fn n).symm : ℂ → ℂ) '' L),
        ENNReal.ofReal (‖Work.MRMT.dzbar (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f) z
              - d.μn n z * Work.MRMT.dz (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f) z‖
            * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖)
          = ENNReal.ofReal (‖conjDefectTrunc K (d.μn n) f z‖
              * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) (f z)‖
              * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖) := by
      intro z hz
      have hid := dzbar_sub_mul_dz_eq (F := ((d.Fn n) : ℂ → ℂ)) (f := f) (μF := d.μn n)
        ((d.contDiff_Fn n).contDiffAt.differentiableAt (by norm_num))
        (hf.contDiffAt.differentiableAt (by norm_num)) (d.beltrami_Fn n (f z))
      rw [hid, hνval n z (hK'sub hz)]
      simp only [conjDefect, norm_mul, norm_star]
      ring_nf
    calc ∫⁻ z in (((d.Fn n).symm : ℂ → ℂ) '' L),
            ENNReal.ofReal (‖Work.MRMT.dzbar (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f) z
              - d.μn n z * Work.MRMT.dz (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f) z‖
              * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖)
        = ∫⁻ z in (((d.Fn n).symm : ℂ → ℂ) '' L),
            ENNReal.ofReal (‖conjDefectTrunc K (d.μn n) f z‖
              * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) (f z)‖
              * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖) :=
          setLIntegral_congr_fun hK'cpt.measurableSet hpt
      _ ≤ ∫⁻ z in K, ENNReal.ofReal (‖conjDefectTrunc K (d.μn n) f z‖
              * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) (f z)‖
              * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖) :=
          lintegral_mono_set hK'sub
  -- ## 6. assemble
  have hmain' : Tendsto (fun n => ∫⁻ z in K, ENNReal.ofReal
      (‖conjDefectTrunc K (d.μn n) f z‖
        * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) (f z)‖
        * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖)) atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat N₁).mp hmain
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun n => ∫⁻ z in K, ENNReal.ofReal
      (‖conjDefectTrunc K (d.μn n) f z‖
        * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) (f z)‖
        * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖))
    tendsto_const_nhds hmain' (Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hcmp n hn


lemma ae_comp_of_ae_of_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) {S : Set ℂ}
    (hSfin : ∀ K : Set ℂ, IsCompact K → (S ∩ K).Finite)
    (hrev : ∀ z ∉ S, ‖Work.MRMT.dz f z‖ < ‖Work.MRMT.dzbar f z‖) {p : ℂ → Prop}
    (hp : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), p z) :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), p (f z) := by
  rw [MeasureTheory.ae_iff] at hp ⊢
  exact volume_preimage_null_localDiffeo hf hSfin hrev hp

theorem conj_contDiff {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) {S : Set ℂ} (hS : ∀ z : ℂ, Filter.Eventually (fun w => w ∉ S) (nhdsWithin z {z}ᶜ))
    (hrev : ∀ z ∉ S, ‖dz f z‖ < ‖dzbar f z‖)
    (hinv : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), μ z = pullRev μ f z) :
    Differentiable ℂ (star ∘ (d.φ : ℂ → ℂ) ∘ f ∘ ((d.φ).symm : ℂ → ℂ)) := by
  have hSclosed : IsClosed S := isClosed_of_eventually_notMem hS
  have hSfin : ∀ K : Set ℂ, IsCompact K → (S ∩ K).Finite := fun K hK =>
    finite_inter_isCompact hS hK
  -- the a.e. bound on `μ` with the constant `d.k`
  have hμb : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ w‖ ≤ d.k := by
    filter_upwards [d.tendsto_μn] with w hw
    exact le_of_tendsto hw.norm (Eventually.of_forall fun n => d.norm_μn n w)
  -- transfer the a.e. statements along `f`
  have hμnc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => d.μn n (f z)) Filter.atTop (nhds (μ (f z))) :=
    ae_comp_of_ae_of_contDiff hf hSfin hrev d.tendsto_μn
  have hμbc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ (f z)‖ ≤ d.k :=
    ae_comp_of_ae_of_contDiff hf hSfin hrev hμb
  have hdefect : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), Filter.Tendsto
      (fun n => conjNum (d.μn n) f z - d.μn n z * conjDen (d.μn n) f z) Filter.atTop (nhds 0) :=
    ae_tendsto_defect_global hSfin hrev d.hk d.norm_μn d.tendsto_μn hμnc hμb hμbc hinv
  -- the master theorem on the open set `(φ '' S)ᶜ`
  have hVopen : IsOpen (((d.φ : ℂ → ℂ) '' S)ᶜ) := (Homeomorph.isClosedMap d.φ S hSclosed).isOpen_compl
  have hGn : ∀ n, LocallyLipschitzOn (((d.φ : ℂ → ℂ) '' S)ᶜ)
      (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ)) := by
    intro n
    have hcd : ContDiff ℝ 1 (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ)) := by
      have h1 : ContDiff ℝ 1 ((star ∘ (((d.Fn n) : ℂ → ℂ) ∘ f)) ∘ ((d.Fn n).symm : ℂ → ℂ)) :=
        (star_contDiff.comp ((d.contDiff_Fn n).comp hf)).comp (d.contDiff_symm_Fn n)
      simpa [Function.comp_assoc] using h1
    exact hcd.locallyLipschitz.locallyLipschitzOn
  have hconv : TendstoLocallyUniformly
      (fun n => star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ))
      (star ∘ (d.φ : ℂ → ℂ) ∘ f ∘ ((d.φ).symm : ℂ → ℂ)) Filter.atTop :=
    tendstoLocallyUniformly_conj_comp d hf
  have hdiffOn : DifferentiableOn ℂ (star ∘ (d.φ : ℂ → ℂ) ∘ f ∘ ((d.φ).symm : ℂ → ℂ))
      (((d.φ : ℂ → ℂ) '' S)ᶜ) := by
    refine differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto hVopen hGn hconv ?_
    intro L hL hLV
    refine tendsto_lintegralAbsDbar_conj_of_defect d hf hS hrev hdefect hL ?_
    rw [Set.disjoint_left]
    intro z hzL hzS
    exact hLV hzL hzS
  -- continuity of the limit
  have hGcont : Continuous (star ∘ (d.φ : ℂ → ℂ) ∘ f ∘ ((d.φ).symm : ℂ → ℂ)) :=
    star_contDiff.continuous.comp
      ((d.φ).continuous.comp (hf.continuous.comp (d.φ.symm).continuous))
  -- differentiability everywhere: use the extension across the isolated set `φ '' S`
  intro w
  by_cases hwS : w ∈ (d.φ : ℂ → ℂ) '' S
  · obtain ⟨s, hsS, hsw⟩ := hwS
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (by
      have := hS s
      rwa [eventually_nhdsWithin_iff] at this)
    have hsymm_cont : ContinuousAt ((d.φ).symm : ℂ → ℂ) w := (d.φ.symm).continuous.continuousAt
    obtain ⟨ε, hε, hεb⟩ := Metric.continuousAt_iff.mp hsymm_cont ρ hρ
    have hsymmw : ((d.φ).symm : ℂ → ℂ) w = s := by
      rw [← hsw]
      exact d.φ.symm_apply_apply s
    have hiso : ∀ᶠ z in 𝓝[≠] w, z ∉ (d.φ : ℂ → ℂ) '' S := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds w hε] with z hz hzw hzS
      obtain ⟨t, htS, htz⟩ := hzS
      have h1 : dist ((d.φ).symm z) s < ρ := by
        have := hεb hz
        rwa [hsymmw] at this
      have h2 : ((d.φ).symm : ℂ → ℂ) z = s := by
        by_contra hne
        have hzS' : ((d.φ).symm : ℂ → ℂ) z ∈ S := by
          rw [← htz, d.φ.symm_apply_apply t]
          exact htS
        exact hρsub (by simpa [Metric.mem_ball] using h1) (by simpa [Set.mem_compl_iff] using hne) hzS'
      have : z = w := by
        have h3 : (d.φ : ℂ → ℂ) (((d.φ).symm : ℂ → ℂ) z) = (d.φ : ℂ → ℂ) s := by rw [h2]
        rw [d.φ.apply_symm_apply] at h3
        exact h3.trans hsw
      exact hzw this
    refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hGcont.continuousAt).differentiableAt
    filter_upwards [hiso] with z hz
    exact hdiffOn.differentiableAt (hVopen.mem_nhds hz)
  · exact hdiffOn.differentiableAt (hVopen.mem_nhds hwS)


end Work.MRMT.Found
