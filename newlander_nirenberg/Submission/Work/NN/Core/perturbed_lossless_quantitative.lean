import Mathlib
import Submission.Work.NN.Core.bmPotential_gain
import Submission.Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul
import Submission.Work.NN.Core.Lcoef_uniform_estimate_on
import Submission.Work.NN.Core.holderNorm_fderiv_apply_le
import Submission.Work.NN.Core.holderNorm_const_mul_le
import Submission.Work.NN.Core.holderNorm_fderiv_le_dir
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_neg
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.integrable_bmWeight
import Submission.Work.NN.Core.flatMulNorm
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

noncomputable section

variable {n : ℕ}

/-! ## Auxiliary lemmas -/

/-- A function which is `C^m` on the (open) polydisc `polydisc 0 ρ` and vanishes off the smaller
closed polydisc `polydisc 0 ρ'` (with `ρ' < ρ` coordinatewise) is globally `C^m`. -/
private lemma contDiff_of_contDiffOn_of_vanishing {m : ℕ} {ρ ρ' : Fin n → ℝ}
    (hρ' : ∀ j, ρ' j < ρ j) {v : Cn n → ℂ}
    (hv : ContDiffOn ℝ ((m : ℕ) : WithTop ENat) v (Work.CR.Flat.polydisc 0 ρ))
    (hvan : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → v z = 0) :
    ContDiff ℝ ((m : ℕ) : WithTop ENat) v := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ Work.CR.Flat.polydisc 0 ρ
  · exact (hv.contDiffWithinAt hz).contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hz)
  · rw [Work.CR.Flat.mem_polydisc] at hz
    push Not at hz
    obtain ⟨i, hi⟩ := hz
    have hiρ : ρ i ≤ ‖z i‖ := by simpa using hi
    have hopen : IsOpen {w : Cn n | ρ' i < ‖w i‖} :=
      isOpen_lt continuous_const ((continuous_apply i).norm)
    have hev : v =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
      filter_upwards [hopen.mem_nhds (lt_of_lt_of_le (hρ' i) hiρ)] with w hw
      exact hvan w ⟨i, le_of_lt hw⟩
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev

/-- The support of such a `v` is compact. -/
private lemma hasCompactSupport_of_vanishing {ρ' : Fin n → ℝ} {v : Cn n → ℂ}
    (hvan : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → v z = 0) : HasCompactSupport v := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall (0 : Cn n) (∑ i : Fin n, ρ' i)) (isCompact_closedBall _ _) ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  rw [not_le] at hcon
  refine hz (hvan z ?_)
  by_contra hc
  push Not at hc
  have h1 : ‖z‖ ≤ ∑ i : Fin n, ‖z i‖ := by
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    exact fun i => Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ i : Fin n, ‖z i‖ ≤ ∑ i : Fin n, ρ' i :=
    Finset.sum_le_sum fun i _ => le_of_lt (hc i)
  linarith

/-- The Fréchet derivative of a globally `C^{m+1}` function vanishing on the closed complement of
`polydisc 0 ρ'` vanishes there as well. -/
private lemma fderiv_eq_zero_of_vanishing {m : ℕ} {ρ' : Fin n → ℝ} (hρ'0 : ∀ j, 0 < ρ' j)
    {v : Cn n → ℂ} (hv : ContDiff ℝ (((m + 1 : ℕ)) : WithTop ENat) v)
    (hvan : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → v z = 0) :
    ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → fderiv ℝ v z = 0 := by
  intro z hz
  have h1 : iteratedFDeriv ℝ 1 v z = 0 :=
    iteratedFDeriv_eq_zero_of_vanishing_closedComplement (ρ := ρ') hρ'0 (m := m + 1) hv hvan 1
      (by omega) z hz
  ext u
  have h2 := iteratedFDeriv_one_apply (𝕜 := ℝ) (f := v) (x := z) (fun _ : Fin 1 => u)
  rw [h1] at h2
  simpa using h2.symm

/-- The coordinate `(0,1)`-derivative of a `C^{k+1}` function is `C^k`. -/
private lemma contDiff_dbarCoord_of_contDiff {k : ℕ} {v : Cn n → ℂ}
    (hv : ContDiff ℝ (((k + 1 : ℕ)) : WithTop ENat) v) (l : Fin n) :
    ContDiff ℝ ((k : ℕ) : WithTop ENat) (fun z => Work.CR.Flat.dbarCoord l v z) := by
  have h1 : ContDiff ℝ ((k : ℕ) : WithTop ENat) (fderiv ℝ v) :=
    hv.fderiv_right (by rw [← Nat.cast_one, ← Nat.cast_add])
  have h2 : ContDiff ℝ ((k : ℕ) : WithTop ENat)
      (Work.CR.Flat.Polydisc.dbarCoordPhi l ∘ fderiv ℝ v) :=
    (Work.CR.Flat.Polydisc.dbarCoordPhi l).contDiff.comp h1
  rw [show (fun z => Work.CR.Flat.dbarCoord l v z)
      = Work.CR.Flat.Polydisc.dbarCoordPhi l ∘ fderiv ℝ v from
    funext (fun z => congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp l v) z)]
  exact h2

/-- The `l`-th coefficient of `∂̄_{Jstd + A} v` is `C^k` when `A` is smooth and `v` is `C^{k+1}`. -/
private lemma contDiff_dbarCn_single {k : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n}
    (hA : ∀ m : ℕ, ContDiff ℝ (m : WithTop ENat) A) {v : Cn n → ℂ}
    (hv : ContDiff ℝ (((k + 1 : ℕ)) : WithTop ENat) v) (l : Fin n) :
    ContDiff ℝ ((k : ℕ) : WithTop ENat)
      (fun z => dbarCn (JstdCn n + A) v z (Pi.single l 1)) := by
  have h1 : ContDiff ℝ ((k : ℕ) : WithTop ENat) (fun z => Work.CR.Flat.dbarCoord l v z) :=
    contDiff_dbarCoord_of_contDiff hv l
  have hfd : ContDiff ℝ ((k : ℕ) : WithTop ENat) (fderiv ℝ v) :=
    hv.fderiv_right (by rw [← Nat.cast_one, ← Nat.cast_add])
  have hAv : ContDiff ℝ ((k : ℕ) : WithTop ENat) (fun z => A z (Pi.single l 1)) :=
    (hA k).clm_apply contDiff_const
  have h2 : ContDiff ℝ ((k : ℕ) : WithTop ENat)
      (fun z => (Complex.I / 2) * (fderiv ℝ v z (A z (Pi.single l 1)))) :=
    contDiff_const.mul (hfd.clm_apply hAv)
  have hpoint : ∀ z, dbarCn (JstdCn n + A) v z (Pi.single l 1)
      = Work.CR.Flat.dbarCoord l v z
        + (Complex.I / 2) * (fderiv ℝ v z (A z (Pi.single l 1))) := by
    intro z
    have hlin := congrArg (fun w : Cn n →L[ℝ] ℂ => w (Pi.single l 1))
      (dbarCn_lin (n := n) A v z)
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
      Work.NN.Core.stdForm_coef_dbar_std] at hlin
    exact hlin
  rw [← contDiffOn_univ]
  refine ContDiffOn.congr (f := fun z => Work.CR.Flat.dbarCoord l v z
      + (Complex.I / 2) * (fderiv ℝ v z (A z (Pi.single l 1)))) ?_ ?_
  · exact (h1.add h2).contDiffOn
  · intro z _
    exact hpoint z

/-- Absorption in `ℝ≥0∞`: if `a ≠ ⊤`, `t ≤ 1/2` and `a ≤ b + t·a`, then `a ≤ 2b`. -/
private lemma ennreal_le_two_mul_of_le_add {a b t : ℝ≥0∞} (ha : a ≠ ⊤) (ht : t ≤ 1 / 2)
    (h : a ≤ b + t * a) : a ≤ 2 * b := by
  have ht2 : (2 : ℝ≥0∞) * t ≤ 1 := by
    calc (2 : ℝ≥0∞) * t ≤ (2 : ℝ≥0∞) * (1 / 2) := by gcongr
      _ = 1 := by
          rw [one_div]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have h2 : (2 : ℝ≥0∞) * a ≤ (2 : ℝ≥0∞) * (b + t * a) := by gcongr
  rw [mul_add] at h2
  rw [← mul_assoc] at h2
  have h3 : (2 : ℝ≥0∞) * t * a ≤ a := by
    calc (2 : ℝ≥0∞) * t * a ≤ 1 * a := by gcongr
      _ = a := one_mul a
  have h4 : a + a ≤ (2 : ℝ≥0∞) * b + a := by
    calc a + a = (2 : ℝ≥0∞) * a := (two_mul a).symm
      _ ≤ (2 : ℝ≥0∞) * b + (2 : ℝ≥0∞) * t * a := h2
      _ ≤ (2 : ℝ≥0∞) * b + a := add_le_add le_rfl h3
  exact (ENNReal.add_le_add_iff_right ha).mp h4

/-! ## The main theorem -/

theorem perturbed_lossless_quantitative {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ ρ' : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ'0 : ∀ j, 0 < ρ' j) (hρ' : ∀ j, ρ' j < ρ j) (k : ℕ) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ {A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)}, (∀ m : ℕ, ContDiff ℝ m A) → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε₀ → (∀ i j : Fin n, Work.CR.Flat.holderNorm (k+1) α (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) → (∀ z v : (Fin n → ℂ), (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) → ∀ v : (Fin n → ℂ) → ℂ, (∀ z, (∃ i, ρ' i ≤ ‖z i‖) → v z = 0) → ContDiffOn ℝ (((k+1 : ℕ)) : WithTop ENat) v (Work.CR.Flat.polydisc 0 ρ) → Work.CR.Flat.holderNorm (k+1) α v (Work.CR.Flat.polydisc 0 ρ') < ⊤ → Work.CR.Flat.holderNorm (k+1) α v (Work.CR.Flat.polydisc 0 ρ') ≤ ENNReal.ofReal C * (∑ j : Fin n, Work.CR.Flat.holderNorm k α (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) v z (Pi.single j 1)) (Work.CR.Flat.polydisc 0 ρ')) := by
  classical
  obtain ⟨C₁, hC₁pos, hC₁⟩ := bmPotential_gain (n := n) hn hα0 hα1 hρ'0 k
  obtain ⟨C₂, hC₂pos, hC₂⟩ := holderNorm_fderiv_apply_le (n := n) (α := α) hα0
    (Ω := Work.CR.Flat.polydisc 0 ρ') (Work.CR.Flat.isOpen_polydisc 0 ρ') (k := k+1) (by omega)
  have hγ : Work.CR.Flat.Cauchy.bmGamma n ≠ 0 :=
    Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
  have hcpos : 0 < ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ := by
    rw [norm_pos_iff]; exact inv_ne_zero hγ
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set K : ℝ := ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁ * ((n : ℝ) * ((1 / 2) * C₂))
    with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  refine ⟨1 / (2 * K), by positivity, 2 * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁),
    by positivity, ?_⟩
  intro A hA ε hε0 hεε₀ hsmall hJ v hv0 hvC hvfin
  -- ### global regularity of `v`
  have hvglob : ContDiff ℝ (((k + 1 : ℕ)) : WithTop ENat) v :=
    contDiff_of_contDiffOn_of_vanishing hρ' hvC hv0
  have hvcs : HasCompactSupport v := hasCompactSupport_of_vanishing hv0
  have hfdzero : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → fderiv ℝ v z = 0 :=
    fderiv_eq_zero_of_vanishing hρ'0 hvglob hv0
  -- ### the data
  set D : Fin n → Cn n → ℂ := fun l z => Work.CR.Flat.dbarCoord l v z with hDdef
  set P : Fin n → Cn n → ℂ := fun l z => dbarCn (JstdCn n + A) v z (Pi.single l 1) with hPdef
  set R : Fin n → Cn n → ℂ :=
    fun l z => (Complex.I / 2) * (fderiv ℝ v z (A z (Pi.single l 1))) with hRdef
  set a : ℝ≥0∞ := Work.CR.Flat.holderNorm (k+1) α v (Work.CR.Flat.polydisc 0 ρ') with hadef
  set s : ℝ≥0∞ := ∑ l : Fin n, Work.CR.Flat.holderNorm k α (P l) (Work.CR.Flat.polydisc 0 ρ')
    with hsdef
  set E : ℝ := (n : ℝ) * ((1 / 2) * (C₂ * ε)) with hEdef
  have hΩ : IsOpen (Work.CR.Flat.polydisc 0 ρ') := Work.CR.Flat.isOpen_polydisc 0 ρ'
  have hΩu : UniqueDiffOn ℝ (Work.CR.Flat.polydisc 0 ρ') := hΩ.uniqueDiffOn
  -- ### pointwise identity `D = P - R`
  have hpoint : ∀ l z, D l z = P l z - R l z := by
    intro l z
    have hlin := congrArg (fun w : Cn n →L[ℝ] ℂ => w (Pi.single l 1))
      (dbarCn_lin (n := n) A v z)
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
      Work.NN.Core.stdForm_coef_dbar_std] at hlin
    simp only [hDdef, hPdef, hRdef]
    rw [hlin]
    ring
  -- ### smoothness
  have hDsm : ∀ l, ContDiff ℝ ((k : ℕ) : WithTop ENat) (D l) := fun l => by
    simp only [hDdef]
    exact contDiff_dbarCoord_of_contDiff hvglob l
  have hPsm : ∀ l, ContDiff ℝ ((k : ℕ) : WithTop ENat) (P l) := fun l => by
    simp only [hPdef]
    exact contDiff_dbarCn_single hA hvglob l
  have hfdglob : ContDiff ℝ ((k : ℕ) : WithTop ENat) (fderiv ℝ v) :=
    hvglob.fderiv_right (by rw [← Nat.cast_one, ← Nat.cast_add])
  have hRsm : ∀ l, ContDiff ℝ ((k : ℕ) : WithTop ENat) (R l) := by
    intro l
    have hAv : ContDiff ℝ ((k : ℕ) : WithTop ENat) (fun z => A z (Pi.single l 1)) :=
      (hA k).clm_apply contDiff_const
    have hthis : ContDiff ℝ ((k : ℕ) : WithTop ENat)
        (fun z => (Complex.I / 2 : ℂ) * (fderiv ℝ v z (A z (Pi.single l 1)))) :=
      (contDiff_const (c := (Complex.I / 2 : ℂ))).mul (hfdglob.clm_apply hAv)
    simpa only [hRdef] using hthis
  -- ### vanishing
  have hDzero : ∀ l z, (∃ i, ρ' i ≤ ‖z i‖) → D l z = 0 := by
    intro l z hz
    have h0 := hfdzero z hz
    simp only [hDdef]
    simp [Work.CR.Flat.dbarCoord, h0]
  have hRzero : ∀ l z, (∃ i, ρ' i ≤ ‖z i‖) → R l z = 0 := by
    intro l z hz
    have h0 := hfdzero z hz
    simp only [hRdef]
    simp [h0]
  have hPzero : ∀ l z, (∃ i, ρ' i ≤ ‖z i‖) → P l z = 0 := by
    intro l z hz
    have h := hpoint l z
    rw [hDzero l z hz, hRzero l z hz] at h
    simpa using h.symm
  -- ### compact support
  have hDcs : ∀ l, HasCompactSupport (D l) := by
    intro l
    refine (Work.CR.Flat.Cauchy.bmPotDbar_hasCompactSupport_fderiv hvcs).mono ?_
    intro z hz
    rw [Function.mem_support] at hz ⊢
    exact fun hzf => hz (by simp only [hDdef]; simp [Work.CR.Flat.dbarCoord, hzf])
  -- ### finiteness of the univ norms
  have hDfin : ∀ l, Work.CR.Flat.holderNorm k α (D l) Set.univ < ⊤ := by
    intro l
    have hle : Work.CR.Flat.holderNorm k α (D l) Set.univ
        ≤ Work.CR.Flat.holderNorm k α (D l) (Work.CR.Flat.polydisc 0 ρ') :=
      holderNorm_univ_le_holderNorm_polydisc_of_contDiff_vanishing hα0 hρ'0 (hDsm l) (hDzero l)
    have hcongr : Work.CR.Flat.holderNorm k α (D l) (Work.CR.Flat.polydisc 0 ρ')
        = Work.CR.Flat.holderNorm k α
            (Work.CR.Flat.Polydisc.dbarCoordPhi l ∘ fderiv ℝ v) (Work.CR.Flat.polydisc 0 ρ') :=
      holderNorm_congr_eqOn (fun z _ => by
        simp only [hDdef]
        exact congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp l v) z)
    have hcomp := holderNorm_comp_fderiv_le_mul (n := n) k α hΩ
      (hvC.mono (Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρ' j))))
      (Work.CR.Flat.Polydisc.dbarCoordPhi l)
    have hfin2 : Work.CR.Flat.holderNorm k α
        (Work.CR.Flat.Polydisc.dbarCoordPhi l ∘ fderiv ℝ v) (Work.CR.Flat.polydisc 0 ρ') < ⊤ :=
      lt_of_le_of_lt hcomp (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvfin)
    rw [hcongr] at hle
    exact lt_of_le_of_lt hle hfin2
  -- ### the Bochner--Martinelli representation
  have hbm : ∀ z, Work.CR.Flat.Cauchy.bmGamma n * v z = Work.CR.Flat.Cauchy.bmPotential D z := by
    intro z
    have h := Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul (n := n) hn (W := v)
      (hvglob.of_le (by simp)) hvcs z
    simpa only [hDdef] using h
  have hveq : ∀ z ∈ Work.CR.Flat.polydisc 0 ρ',
      v z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPotential D z := by
    intro z _
    rw [← hbm z, ← mul_assoc, inv_mul_cancel₀ hγ, one_mul]
  -- ### step 1: representation and homogeneity
  have hstep1 : a ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
      * Work.CR.Flat.holderNorm (k+1) α (Work.CR.Flat.Cauchy.bmPotential D)
          (Work.CR.Flat.polydisc 0 ρ') := by
    rw [hadef]
    rw [holderNorm_congr_eqOn hveq]
    exact holderNorm_const_mul_le hΩu _ _
  -- ### step 2: the Bochner--Martinelli gain
  have hstep2 : Work.CR.Flat.holderNorm (k+1) α (Work.CR.Flat.Cauchy.bmPotential D)
        (Work.CR.Flat.polydisc 0 ρ')
      ≤ ENNReal.ofReal C₁ * ∑ l, Work.CR.Flat.holderNorm k α (D l) Set.univ :=
    (hC₁ D hDsm hDcs hDfin hDzero).2
  -- ### step 3: shrinking the datum region
  have hstep3 : ∑ l, Work.CR.Flat.holderNorm k α (D l) Set.univ
      ≤ ∑ l, Work.CR.Flat.holderNorm k α (D l) (Work.CR.Flat.polydisc 0 ρ') :=
    Finset.sum_le_sum fun l _ =>
      holderNorm_univ_le_holderNorm_polydisc_of_contDiff_vanishing hα0 hρ'0 (hDsm l) (hDzero l)
  -- ### step 4: `D = P - R`
  have hstep4 : ∑ l, Work.CR.Flat.holderNorm k α (D l) (Work.CR.Flat.polydisc 0 ρ')
      ≤ (∑ l, Work.CR.Flat.holderNorm k α (P l) (Work.CR.Flat.polydisc 0 ρ'))
        + ∑ l, Work.CR.Flat.holderNorm k α (R l) (Work.CR.Flat.polydisc 0 ρ') := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun l _ => ?_
    have hfun : D l = P l + (-(R l)) := by
      funext z
      have := hpoint l z
      simp only [Pi.add_apply, Pi.neg_apply]
      rw [this]; ring
    have hPc : ContDiffOn ℝ ((k : ℕ) : WithTop ENat) (P l) (Work.CR.Flat.polydisc 0 ρ') :=
      (hPsm l).contDiffOn.mono (Set.subset_univ _)
    have hRc : ContDiffOn ℝ ((k : ℕ) : WithTop ENat) (R l) (Work.CR.Flat.polydisc 0 ρ') :=
      (hRsm l).contDiffOn.mono (Set.subset_univ _)
    calc Work.CR.Flat.holderNorm k α (D l) (Work.CR.Flat.polydisc 0 ρ')
        = Work.CR.Flat.holderNorm k α (P l + (-(R l))) (Work.CR.Flat.polydisc 0 ρ') := by
          rw [hfun]
      _ ≤ Work.CR.Flat.holderNorm k α (P l) (Work.CR.Flat.polydisc 0 ρ')
            + Work.CR.Flat.holderNorm k α (-(R l)) (Work.CR.Flat.polydisc 0 ρ') :=
          Work.CR.Flat.Holder.holderNorm_add_le hPc hRc.neg hΩu
      _ = Work.CR.Flat.holderNorm k α (P l) (Work.CR.Flat.polydisc 0 ρ')
            + Work.CR.Flat.holderNorm k α (R l) (Work.CR.Flat.polydisc 0 ρ') := by
          rw [Work.CR.Flat.Holder.holderNorm_neg hRc hΩu]
  -- ### step 5: the perturbation term
  have hRstep : ∀ l, Work.CR.Flat.holderNorm k α (R l) (Work.CR.Flat.polydisc 0 ρ')
      ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal C₂ * (ENNReal.ofReal ε * a)) := by
    intro l
    have hconst : Work.CR.Flat.holderNorm k α (R l) (Work.CR.Flat.polydisc 0 ρ')
        ≤ ENNReal.ofReal ‖(Complex.I / 2 : ℂ)‖
          * Work.CR.Flat.holderNorm k α
              (fun z => fderiv ℝ v z (A z (Pi.single l 1))) (Work.CR.Flat.polydisc 0 ρ') := by
      rw [hRdef]
      exact holderNorm_const_mul_le hΩu _ _
    have hk1 : (k + 1) - 1 = k := by omega
    have hW : ∀ j : Fin n, ContDiffOn ℝ (((k + 1) - 1 : ℕ) : WithTop ENat)
        (fun z => A z (Pi.single l 1) j) (Work.CR.Flat.polydisc 0 ρ') := by
      intro j
      rw [hk1]
      exact ((contDiff_pi.mp ((hA k).clm_apply contDiff_const)) j).contDiffOn.mono
        (Set.subset_univ _)
    have hb : ∀ j : Fin n, Work.CR.Flat.holderNorm ((k + 1) - 1) α
        (fun z => A z (Pi.single l 1) j) (Work.CR.Flat.polydisc 0 ρ')
        ≤ ENNReal.ofReal ε := by
      intro j
      rw [hk1]
      calc Work.CR.Flat.holderNorm k α (fun z => A z (Pi.single l 1) j)
              (Work.CR.Flat.polydisc 0 ρ')
          ≤ Work.CR.Flat.holderNorm (k+1) α (fun z => A z (Pi.single l 1) j)
              (Work.CR.Flat.polydisc 0 ρ') :=
            Work.CR.Flat.holderNorm_mono_k (Nat.le_succ k) α _ _
        _ ≤ Work.CR.Flat.holderNorm (k+1) α (fun z => A z (Pi.single l 1) j)
              (Work.CR.Flat.polydisc 0 ρ) :=
            Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 ρ) hΩ
              (Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρ' j))) (k+1) α _
        _ ≤ ENNReal.ofReal ε := hsmall l j
    have hfdapp : Work.CR.Flat.holderNorm k α
        (fun z => fderiv ℝ v z (A z (Pi.single l 1))) (Work.CR.Flat.polydisc 0 ρ')
        ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal ε * a) := by
      have hraw := hC₂ (u := v)
        (hvC.mono (Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρ' j))))
        (W := fun z => A z (Pi.single l 1)) hW hε0 hb
      rw [hadef]
      simpa only [hk1] using hraw
    calc Work.CR.Flat.holderNorm k α (R l) (Work.CR.Flat.polydisc 0 ρ')
        ≤ ENNReal.ofReal ‖(Complex.I / 2 : ℂ)‖
            * Work.CR.Flat.holderNorm k α
                (fun z => fderiv ℝ v z (A z (Pi.single l 1))) (Work.CR.Flat.polydisc 0 ρ') := hconst
      _ ≤ ENNReal.ofReal ‖(Complex.I / 2 : ℂ)‖
            * (ENNReal.ofReal C₂ * (ENNReal.ofReal ε * a)) := by gcongr
      _ = ENNReal.ofReal (1 / 2) * (ENNReal.ofReal C₂ * (ENNReal.ofReal ε * a)) := by
          rw [show ‖(Complex.I / 2 : ℂ)‖ = 1 / 2 from by norm_num [Complex.normSq]]
  have hkey5 : (n : ℝ≥0∞) * (ENNReal.ofReal (1 / 2) * (ENNReal.ofReal C₂
        * (ENNReal.ofReal ε * a))) = ENNReal.ofReal E * a := by
    rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) from (ENNReal.ofReal_natCast n).symm]
    rw [show ENNReal.ofReal E = ENNReal.ofReal (n : ℝ)
        * (ENNReal.ofReal (1 / 2) * (ENNReal.ofReal C₂ * ENNReal.ofReal ε)) from by
      rw [hEdef, ENNReal.ofReal_mul (Nat.cast_nonneg n),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), ENNReal.ofReal_mul hC₂pos.le]]
    ac_rfl
  have hstep5 : ∑ l, Work.CR.Flat.holderNorm k α (R l) (Work.CR.Flat.polydisc 0 ρ')
      ≤ ENNReal.ofReal E * a := by
    calc ∑ l, Work.CR.Flat.holderNorm k α (R l) (Work.CR.Flat.polydisc 0 ρ')
        ≤ ∑ _l : Fin n, ENNReal.ofReal (1 / 2) * (ENNReal.ofReal C₂ * (ENNReal.ofReal ε * a)) :=
          Finset.sum_le_sum (fun l _ => hRstep l)
      _ = (n : ℝ≥0∞) * (ENNReal.ofReal (1 / 2) * (ENNReal.ofReal C₂
            * (ENNReal.ofReal ε * a))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal E * a := hkey5
  -- ### assembling the chain
  have hs' : ∑ l, Work.CR.Flat.holderNorm k α (D l) (Work.CR.Flat.polydisc 0 ρ')
      ≤ s + ENNReal.ofReal E * a := by
    rw [hsdef]
    exact hstep4.trans (add_le_add le_rfl hstep5)
  have hchain1 : a ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
      * (ENNReal.ofReal C₁ * (s + ENNReal.ofReal E * a)) := by
    calc a ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * Work.CR.Flat.holderNorm (k+1) α (Work.CR.Flat.Cauchy.bmPotential D)
              (Work.CR.Flat.polydisc 0 ρ') := hstep1
      _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
            * (ENNReal.ofReal C₁ * ∑ l, Work.CR.Flat.holderNorm k α (D l) Set.univ) := by gcongr
      _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
            * (ENNReal.ofReal C₁
                * ∑ l, Work.CR.Flat.holderNorm k α (D l) (Work.CR.Flat.polydisc 0 ρ')) := by gcongr
      _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
            * (ENNReal.ofReal C₁ * (s + ENNReal.ofReal E * a)) := by
          gcongr
  have hmain : a ≤ ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁) * s
      + (ENNReal.ofReal K * ENNReal.ofReal ε) * a := by
    have h1 : ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * ENNReal.ofReal C₁
        = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁) :=
      (ENNReal.ofReal_mul (norm_nonneg _)).symm
    calc a ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * (ENNReal.ofReal C₁ * (s + ENNReal.ofReal E * a)) := hchain1
      _ = (ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * ENNReal.ofReal C₁)
            * (s + ENNReal.ofReal E * a) := by rw [mul_assoc]
      _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁)
            * (s + ENNReal.ofReal E * a) := by rw [h1]
      _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁) * s
            + ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁)
                * (ENNReal.ofReal E * a) := by rw [mul_add]
      _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁) * s
            + (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁)
                * ENNReal.ofReal E) * a := by rw [mul_assoc]
      _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁) * s
            + (ENNReal.ofReal K * ENNReal.ofReal ε) * a := by
          rw [show ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁)
                * ENNReal.ofReal E = ENNReal.ofReal K * ENNReal.ofReal ε from by
            rw [← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) hC₁pos.le),
              ← ENNReal.ofReal_mul hKpos.le]
            rw [show (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁) * E = K * ε from by
              rw [hEdef, hKdef]; ring]]
  -- ### absorption
  have hKeps : ENNReal.ofReal K * ENNReal.ofReal ε ≤ 1 / 2 := by
    rw [← ENNReal.ofReal_mul hKpos.le]
    have hreal : K * ε ≤ 1 / 2 := by
      calc K * ε ≤ K * (1 / (2 * K)) := mul_le_mul_of_nonneg_left hεε₀ hKpos.le
        _ = 1 / 2 := by field_simp
    calc ENNReal.ofReal (K * ε) ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal hreal
      _ = 1 / 2 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
            ENNReal.ofReal_ofNat, one_div]
  have hfin_a : a ≠ ⊤ := by rw [hadef]; exact ne_of_lt hvfin
  have habs := ennreal_le_two_mul_of_le_add (a := a)
    (b := ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁) * s)
    (t := ENNReal.ofReal K * ENNReal.ofReal ε) hfin_a hKeps hmain
  change a ≤ ENNReal.ofReal (2 * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁)) * s
  refine habs.trans (le_of_eq ?_)
  rw [show (2 : ℝ≥0∞) * (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁) * s)
      = ENNReal.ofReal (2 * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * C₁)) * s from by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) from (ENNReal.ofReal_ofNat 2).symm,
      ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]]

end

end Work.NN.Core
