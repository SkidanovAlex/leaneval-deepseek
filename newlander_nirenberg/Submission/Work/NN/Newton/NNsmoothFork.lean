import Submission.Work.CR.Flat.Polydisc.dbarCoord_add
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm
import Submission.Work.NN.Core.telescopeTwo
import Submission.Work.NN.Core.fiberPot_dbarCoord
import Submission.Work.NN.Core.fiberPot_dbarCoord_self
import Submission.Work.NN.Core.contDiff_fiberPot
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
import Submission.Work.NN.Core.TelTwoDF.Rec2
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.TelTwoDF.EstimateDefs
import Submission.Work.NN.Core.TelTwoDF.ContDiffRec
import Submission.Work.NN.Core.TelTwoDF.S2Bound
import Submission.Work.NN.Core.TelTwoDF.dbarTransform_Eset_le
import Submission.Work.NN.Core.TelTwoDF.holderNorm_dbarTransform_le
import Submission.Work.NN.Core.TelTwoDF.contDiff_dbarTransform_univ
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.bmDefect_eq
import Submission.Work.NN.Core.bmRow_holder
import Submission.Work.NN.Final.bmRow_bound
import Submission.Work.CR.Flat.Cauchy.polydiscCutoff
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc_Ck
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.NN.Core.bmDefectClosed
import Submission.Work.NN.Core.bmRowCutoffEstimate
import Submission.Work.NN.Core.bmPotCutoffEstimate
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_neg
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmPotential_tendsto_of_tendsto
import Submission.Work.NN.Core.bmPot_riesz_Ck
import Submission.Work.NN.Core.bmPot_holder_C0a
import Submission.Work.NN.Core.holderNorm_le_of_tendsto
import Submission.Work.NN.Core.fderiv_eq_zero_of_vanishing_off_polydisc
import Submission.Work.NN.Core.exists_holderNorm_wirtinger_le
import Submission.Work.NN.Core.flatMulSharp
import Submission.Work.NN.Core.flatMulNorm
import Submission.Work.NN.Core.bmPotential_gain
import Submission.Work.NN.Core.holderNorm_interp_le
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le_two
import Submission.Work.NN.Core.bmPotential_top_gain_uniform
import Submission.Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded
import Submission.Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul
import Submission.Work.NN.Core.holderNorm_const_mul_le
import Submission.Work.NN.Core.dbarCoord_finite_of_perturbed_data
import Submission.Work.NN.Core.perturbed_aux
import Submission.Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport
import Submission.Work.NN.Core.exists_beltramiCoef_small_smooth
import Submission.Work.NN.Core.jholoFrame_pre
import Submission.Work.CR.Flat.Holder.holderNorm_add_ne_top
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Core.DbarCnPertAux
import Submission.Work.NN.Core.dbarCn_implicit_form
import Submission.Work.NN.Core.dbarCoord_eq_beltramiCoeff
import Submission.Work.NN.Core.dbarCoord_eq_beltramiCoeff_pointwise
import Submission.Work.NN.Core.betaCoef_Bop_contDiff
import Submission.Work.NN.Final.BeltramiSourceDefs
import Submission.Work.NN.Core.isInvertible_one_add_and_inverse_norm_le

/-! Merged, privatised fork of the perturbed-dbar regularity chain. -/


noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace Work.NN.Final

variable {n : ℕ}

/-! ## Tracking regions and fibre cylinders -/

/-- The `m`-th tracking radius in coordinate `k`: the first `m` coordinates are tracked in the
`R`-disc, the remaining ones in the `R'`-disc. -/
private def telRegB (R R' : ℝ) (m : ℕ) (k : Fin n) : ℝ := if (k : ℕ) < m then R else R'

/-- The `m`-th tracking region: `z` with `‖z k‖ < telRegB R R' m k` for all `k`. -/
private def telReg (R R' : ℝ) (m : ℕ) : Set (Work.NN.Core.Cn n) :=
  {z | ∀ k, ‖z k‖ < telRegB R R' m k}

/-- The `j`-fibre cylinder: the `j`-th coordinate varies in the closed ball of radius `R`, the
other coordinates within `ρ` of `z`. -/
private def telCyl (R ρ : ℝ) (j : Fin n) (z : Work.NN.Core.Cn n) : Set (Work.NN.Core.Cn n) :=
  {y | ∀ k : Fin n, y k ∈ Metric.closedBall (Function.update z j 0 k)
        (if k = j then R else ρ)}

@[simp] lemma mem_telRegFK {R R' : ℝ} {m : ℕ} {z : Work.NN.Core.Cn n} :
    z ∈ telReg R R' m ↔ ∀ k, ‖z k‖ < telRegB R R' m k := Iff.rfl

private lemma telRegB_zero (R R' : ℝ) (k : Fin n) : telRegB R R' 0 k = R' := by
  simp [telRegB]

private lemma telRegB_self (R R' : ℝ) (k : Fin n) : telRegB R R' n k = R := by
  simp [telRegB, k.isLt]

private lemma telRegB_le {R R' : ℝ} (hRR' : R ≤ R') (m : ℕ) (k : Fin n) :
    telRegB R R' m k ≤ R' := by
  unfold telRegB
  split <;> linarith

private lemma telRegB_mono {R R' : ℝ} (hRR' : R ≤ R') {m m' : ℕ} (h : m ≤ m') (k : Fin n) :
    telRegB R R' m' k ≤ telRegB R R' m k := by
  unfold telRegB
  by_cases h1 : (k : ℕ) < m
  · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 h)]
  · rw [if_neg h1]
    by_cases h2 : (k : ℕ) < m'
    · rw [if_pos h2]; exact hRR'
    · rw [if_neg h2]

private lemma telReg_mono {R R' : ℝ} (hRR' : R ≤ R') {m m' : ℕ} (h : m ≤ m') :
    telReg (n := n) R R' m' ⊆ telReg (n := n) R R' m :=
  fun z hz k => lt_of_lt_of_le (hz k) (telRegB_mono hRR' h k)

private lemma telReg_zero (R R' : ℝ) : telReg R R' 0 = Work.CR.Flat.polydisc 0 (fun _ : Fin n => R') := by
  ext z; simp only [mem_telRegFK, Work.CR.Flat.mem_polydisc, telRegB_zero, Pi.zero_apply,
    sub_zero]

private lemma telReg_n (R R' : ℝ) : telReg R R' n = Work.CR.Flat.polydisc 0 (fun _ : Fin n => R) := by
  ext z; simp only [mem_telRegFK, Work.CR.Flat.mem_polydisc, telRegB_self, Pi.zero_apply, sub_zero]

private lemma telReg_subset_polydisc {R R' : ℝ} (hRR' : R ≤ R') (m : ℕ) :
    telReg R R' m ⊆ Work.CR.Flat.polydisc 0 (fun _ : Fin n => R') := by
  intro z hz k
  simpa using lt_of_lt_of_le (hz k) (telRegB_le hRR' m k)

private lemma isOpen_telReg (R R' : ℝ) (m : ℕ) : IsOpen (telReg (n := n) R R' m) := by
  have h : telReg (n := n) R R' m = ⋂ k, {z : Work.NN.Core.Cn n | ‖z k‖ < telRegB R R' m k} := by
    ext z; simp [telReg]
  rw [h]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_lt ((continuous_apply k).norm) continuous_const

@[simp] lemma mem_telCylFK {R ρ : ℝ} {j : Fin n} {z y : Work.NN.Core.Cn n} :
    y ∈ telCyl R ρ j z ↔ ‖y j‖ ≤ R ∧ ∀ k, k ≠ j → ‖y k - z k‖ ≤ ρ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h j
      simpa [telCyl, Function.update_self, dist_eq_norm] using this
    · intro k hk
      have := h k
      rw [Function.update_of_ne hk, ite_eq_right hk] at this
      simpa [dist_eq_norm] using this
  · rintro ⟨h1, h2⟩ k
    by_cases hk : k = j
    · subst hk; simpa [telCyl, Function.update_self, dist_eq_norm] using h1
    · have := h2 k hk
      rw [ite_eq_right hk]
      simpa [telCyl, Function.update_of_ne hk, dist_eq_norm, sub_eq_add_neg] using this

private lemma isCompact_telCyl (R ρ : ℝ) (j : Fin n) (z : Work.NN.Core.Cn n) :
    IsCompact (telCyl R ρ j z) := by
  have h : telCyl R ρ j z = {y | ∀ k : Fin n, y k ∈
      Metric.closedBall (Function.update z j 0 k) (if k = j then R else ρ)} := rfl
  rw [h]
  exact isCompact_pi_infinite fun k => isCompact_closedBall _ _

/-! ## Bump extension of data that is locally smooth -/

/-- If `χ` is smooth with `tsupport χ ⊆ V` (`V` open) and `g` is `C^k` on `V`, then `χ * g` is
globally `C^k` (the product is `0` off the support of `χ`). -/
private lemma contDiff_mul_of_contDiffOnFK {k : ℕ} {χ g : Work.NN.Core.Cn n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    {V : Set (Work.NN.Core.Cn n)} (hV : IsOpen V) (hts : tsupport χ ⊆ V)
    (hg : ContDiffOn ℝ k g V) : ContDiff ℝ k (fun y => χ y * g y) := by
  rw [← contDiffOn_univ]
  refine contDiffOn_of_locally_contDiffOn (fun x _ => ?_)
  by_cases hx : x ∈ V
  · exact ⟨V, hV, hx, by rw [Set.univ_inter]; exact ((hχ.contDiffOn).of_le (by simp)).mul hg⟩
  · refine ⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl, fun h => hx (hts h), ?_⟩
    rw [Set.univ_inter]
    refine ContDiffOn.congr (contDiffOn_const (c := (0 : ℂ))) (fun y hy => ?_)
    have hy' : y ∉ tsupport χ := hy
    have h0 : χ y = 0 := by
      by_contra h
      exact hy' (subset_tsupport χ (Function.mem_support.mpr h))
    rw [h0, zero_mul]

/-- Extension of data that is `C^k` on an open set containing the cylinder. -/
private lemma exists_contDiff_ext_of_telCyl {k : ℕ} {R ρ : ℝ} {j : Fin n} {z : Work.NN.Core.Cn n}
    {V : Set (Work.NN.Core.Cn n)} (hV : IsOpen V) (hCV : telCyl R ρ j z ⊆ V)
    {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiffOn ℝ k u V) :
    ∃ ũ : Work.NN.Core.Cn n → ℂ, ContDiff ℝ k ũ ∧
      ∀ y ∈ telCyl R ρ j z, ũ y = u y := by
  obtain ⟨χ, W, hχ, _hcs, hts, _hWo, hCW, hχW⟩ :=
    Work.NN.Core.exists_contDiff_bump_of_isCompact_subset (K := telCyl R ρ j z) (U := V)
      (isCompact_telCyl R ρ j z) hV hCV
  exact ⟨fun y => χ y * u y, contDiff_mul_of_contDiffOnFK hχ hV hts hu,
    fun y hy => by simp only [hχW y (hCW hy), one_mul]⟩

/-! ## Local fibre-potential lemmas -/

/-- A point of a smaller cylinder is an interior point of a bigger one. -/
private lemma telCyl_mem_nhds {R ρ R' ρ' : ℝ} (hR : R' < R) (hρ : ρ' < ρ)
    {j : Fin n} {z y : Work.NN.Core.Cn n} (hy : y ∈ telCyl R' ρ' j z) :
    telCyl R ρ j z ∈ 𝓝 y := by
  rw [Metric.mem_nhds_iff]
  refine ⟨min ((R - R') / 2) ((ρ - ρ') / 2), lt_min (by linarith) (by linarith), ?_⟩
  intro y' hy'
  rw [Metric.mem_ball, dist_eq_norm] at hy'
  rw [mem_telCylFK] at hy ⊢
  obtain ⟨hy1, hy2⟩ := hy
  have hεR : ‖y' - y‖ < (R - R') / 2 := lt_of_lt_of_le hy' (min_le_left _ _)
  have hερ : ‖y' - y‖ < (ρ - ρ') / 2 := lt_of_lt_of_le hy' (min_le_right _ _)
  constructor
  · have h1 : ‖y' j - y j‖ ≤ ‖y' - y‖ := by simpa using norm_le_pi_norm (y' - y) j
    have h2 : ‖y' j‖ ≤ ‖y' j - y j‖ + ‖y j‖ := by
      calc ‖y' j‖ = ‖(y' j - y j) + y j‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  · intro k hk
    have h1 : ‖y' k - y k‖ ≤ ‖y' - y‖ := by simpa using norm_le_pi_norm (y' - y) k
    have h2 : ‖y' k - z k‖ ≤ ‖y' k - y k‖ + ‖y k - z k‖ := by
      calc ‖y' k - z k‖ = ‖(y' k - y k) + (y k - z k)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith [hy2 k hk]

/-- If the data agree on a cylinder then the fibre potentials agree on the corresponding ball. -/
private lemma fiberPot_congr_of_telCyl {R ρ : ℝ} (hρ : 0 < ρ) {j : Fin n} {z : Work.NN.Core.Cn n}
    {u ũ : Work.NN.Core.Cn n → ℂ} (h : ∀ y ∈ telCyl R (2 * ρ) j z, u y = ũ y) :
    ∀ y ∈ Metric.ball z ρ,
      Work.NN.Core.fiberPot R j u y = Work.NN.Core.fiberPot R j ũ y := by
  intro y hy
  rw [Work.NN.Core.fiberPot_apply, Work.NN.Core.fiberPot_apply]
  congr 1
  refine setIntegral_congr_fun measurableSet_ball (fun w hw => ?_)
  have hw' : ‖w‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hw
  have hy' : ‖y - z‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hy
  have hmem : Function.update y j w ∈ telCyl R (2 * ρ) j z := by
    rw [mem_telCylFK]
    refine ⟨?_, ?_⟩
    · rw [Function.update_self]; exact le_of_lt hw'
    · intro k hk
      rw [Function.update_of_ne hk]
      calc ‖y k - z k‖ ≤ ‖y - z‖ := by simpa using norm_le_pi_norm (y - z) k
        _ ≤ 2 * ρ := by linarith
  rw [h _ hmem]

/-- Fibre potentials of data vanishing on the cylinder vanish on the ball. -/
private lemma fiberPot_eq_zero_of_telCyl {R ρ : ℝ} (hρ : 0 < ρ) {j : Fin n} {z : Work.NN.Core.Cn n}
    {u : Work.NN.Core.Cn n → ℂ} (h : ∀ y ∈ telCyl R (2 * ρ) j z, u y = 0) :
    ∀ y ∈ Metric.ball z ρ, Work.NN.Core.fiberPot R j u y = 0 := by
  intro y hy
  exact (fiberPot_congr_of_telCyl (R := R) (ρ := ρ) hρ (j := j) (z := z) (u := u)
    (ũ := fun _ => (0 : ℂ)) (fun y' hy' => by rw [h y' hy']) y hy).trans (by simp)

/-- **Local self-inverse of the fibre potential.** -/
private lemma dbarCoord_fiberPot_self_of_telCyl {R ρ : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    {j : Fin n} {z : Work.NN.Core.Cn n} {u ũ : Work.NN.Core.Cn n → ℂ}
    (hũ : ContDiff ℝ 1 ũ) (h : ∀ y ∈ telCyl R (2 * ρ) j z, u y = ũ y) (hz : ‖z j‖ < R) :
    Work.CR.Flat.dbarCoord j (Work.NN.Core.fiberPot R j u) z = u z := by
  have heq : Work.NN.Core.fiberPot R j u =ᶠ[𝓝 z] Work.NN.Core.fiberPot R j ũ := by
    filter_upwards [Metric.ball_mem_nhds z hρ] with y hy
    exact fiberPot_congr_of_telCyl hρ h y hy
  have hfd : fderiv ℝ (Work.NN.Core.fiberPot R j u) z
      = fderiv ℝ (Work.NN.Core.fiberPot R j ũ) z := heq.fderiv_eq
  have hL : Work.CR.Flat.dbarCoord j (Work.NN.Core.fiberPot R j u) z
      = Work.CR.Flat.dbarCoord j (Work.NN.Core.fiberPot R j ũ) z := by
    rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, hfd]
  rw [hL, Work.NN.Core.fiberPot_dbarCoord_self R hR j hũ hz]
  exact (h z (by rw [mem_telCylFK]; exact ⟨le_of_lt hz, fun k _ => by
    simp only [sub_self, norm_zero]; positivity⟩)).symm

/-- **Local commutation of the fibre potential with the other `∂̄`s.** -/
private lemma dbarCoord_fiberPot_of_telCyl {R ρ : ℝ} (hρ : 0 < ρ) {j k : Fin n} (hkj : k ≠ j)
    {z : Work.NN.Core.Cn n} {u ũ : Work.NN.Core.Cn n → ℂ} (hũ : ContDiff ℝ 1 ũ)
    (h : ∀ y ∈ telCyl R (2 * ρ) j z, u y = ũ y)
    (hdiff : DifferentiableAt ℝ (Work.NN.Core.fiberPot R j u) z) :
    Work.CR.Flat.dbarCoord k (Work.NN.Core.fiberPot R j u) z
      = Work.NN.Core.fiberPot R j (Work.CR.Flat.dbarCoord k u) z := by
  have heq : Work.NN.Core.fiberPot R j u =ᶠ[𝓝 z] Work.NN.Core.fiberPot R j ũ := by
    filter_upwards [Metric.ball_mem_nhds z hρ] with y hy
    exact fiberPot_congr_of_telCyl hρ h y hy
  have hfd : fderiv ℝ (Work.NN.Core.fiberPot R j u) z
      = fderiv ℝ (Work.NN.Core.fiberPot R j ũ) z := heq.fderiv_eq
  have hdiff' : DifferentiableAt ℝ (Work.NN.Core.fiberPot R j ũ) z :=
    (heq.differentiableAt_iff).mp hdiff
  have hL : Work.CR.Flat.dbarCoord k (Work.NN.Core.fiberPot R j u) z
      = Work.CR.Flat.dbarCoord k (Work.NN.Core.fiberPot R j ũ) z := by
    rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, hfd]
  rw [hL, Work.NN.Core.fiberPot_dbarCoord R j hkj hũ z hdiff']
  have hkey : ∀ w : ℂ, ‖w‖ < R →
      Work.CR.Flat.dbarCoord k u (Function.update z j w)
        = Work.CR.Flat.dbarCoord k ũ (Function.update z j w) := by
    intro w hw
    have hy : Function.update z j w ∈ telCyl (‖w‖) ρ j z := by
      rw [mem_telCylFK]
      refine ⟨by rw [Function.update_self], fun k' hk' => ?_⟩
      rw [Function.update_of_ne hk', sub_self, norm_zero]; exact le_of_lt hρ
    have hnhds : telCyl R (2 * ρ) j z ∈ 𝓝 (Function.update z j w) :=
      telCyl_mem_nhds (R' := ‖w‖) (ρ' := ρ) (by linarith) (by linarith) hy
    have hev : u =ᶠ[𝓝 (Function.update z j w)] ũ := by
      filter_upwards [hnhds] with y' hy'
      exact h y' hy'
    rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, hev.fderiv_eq]
  have hcongr : Work.NN.Core.fiberPot R j (Work.CR.Flat.dbarCoord k ũ) z
      = Work.NN.Core.fiberPot R j (Work.CR.Flat.dbarCoord k u) z := by
    rw [Work.NN.Core.fiberPot_apply, Work.NN.Core.fiberPot_apply]
    congr 1
    refine setIntegral_congr_fun measurableSet_ball (fun w hw => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hw
    rw [hkey w hw]
  rw [hcongr]

/-- **Local smoothness of the fibre potential.** -/
private lemma contDiffOn_fiberPot_of_telCyl {R ρ : ℝ} (hρ : 0 < ρ) {j : Fin n} {k : ℕ}
    {z : Work.NN.Core.Cn n} {u ũ : Work.NN.Core.Cn n → ℂ} (hũ : ContDiff ℝ k ũ)
    (h : ∀ y ∈ telCyl R (2 * ρ) j z, u y = ũ y) (hρR : ρ + ‖z j‖ ≤ R) :
    ContDiffOn ℝ k (Work.NN.Core.fiberPot R j u) (Metric.ball z ρ) := by
  have hball : Metric.ball z ρ ⊆ {y | ‖y j‖ < R} := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have h1 : ‖y j - z j‖ ≤ ‖y - z‖ := by simpa using norm_le_pi_norm (y - z) j
    have h2 : ‖y j‖ ≤ ‖y j - z j‖ + ‖z j‖ := by
      calc ‖y j‖ = ‖(y j - z j) + z j‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    calc ‖y j‖ ≤ ‖y j - z j‖ + ‖z j‖ := h2
      _ ≤ ‖y - z‖ + ‖z j‖ := add_le_add_left h1 _
      _ < ρ + ‖z j‖ := add_lt_add_left hy _
      _ ≤ R := hρR
  exact (Work.NN.Core.contDiff_fiberPot R k j hũ).congr_mono
    (fun y hy => fiberPot_congr_of_telCyl hρ h y hy) hball

/-! ## Shrinking the tracking region -/

/-- A cylinder with small radius around a point of `telReg R R' (m+1)` is contained in
`telReg R R' m`. -/
private lemma telCyl_subset_telReg {R R' : ℝ} (hRR' : R < R') {m : ℕ} (hm : m < n)
    {z : Work.NN.Core.Cn n} {s : ℝ}
    (hz : z ∈ telReg R R' (m+1))
    (hs : ∀ k : Fin n, k ≠ (⟨m, hm⟩ : Fin n) →
      ‖z k‖ + 2 * s < telRegB R R' (m+1) k) :
    telCyl R (2 * s) (⟨m, hm⟩ : Fin n) z ⊆ telReg R R' m := by
  intro y hy
  rw [mem_telCylFK] at hy
  obtain ⟨hy1, hy2⟩ := hy
  intro k
  by_cases hk : k = (⟨m, hm⟩ : Fin n)
  · subst hk
    have hb : telRegB R R' m (⟨m, hm⟩ : Fin n) = R' := by
      simp [telRegB]
    rw [hb]
    linarith
  · have hbd : ‖y k‖ < telRegB R R' (m+1) k := by
      have h1 : ‖y k - z k‖ ≤ 2 * s := hy2 k hk
      have h2 : ‖y k‖ ≤ ‖y k - z k‖ + ‖z k‖ := by
        calc ‖y k‖ = ‖(y k - z k) + z k‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith [hs k hk]
    exact lt_of_lt_of_le hbd (telRegB_mono hRR'.le (by omega) k)

/-- A ball of small radius around a point of `telReg R R' (m+1)` stays in
`telReg R R' (m+1)`. -/
private lemma ball_subset_telReg {R R' : ℝ} {m : ℕ} {z : Work.NN.Core.Cn n} {s : ℝ}
    (hs : ∀ k : Fin n, ‖z k‖ + s < telRegB R R' (m+1) k) :
    Metric.ball z s ⊆ telReg R R' (m+1) := by
  intro y hy k
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h1 : ‖y k - z k‖ ≤ ‖y - z‖ := by simpa using norm_le_pi_norm (y - z) k
  have h2 : ‖y k‖ ≤ ‖y k - z k‖ + ‖z k‖ := by
    calc ‖y k‖ = ‖(y k - z k) + z k‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  linarith [hs k]

/-- The shrinking radius attached to a point of the tracking region. -/
private lemma exists_rho_of_mem_telReg {R R' : ℝ} (hRR' : R < R') {m : ℕ} (hm : m < n)
    (hn : 0 < n) {z : Work.NN.Core.Cn n} (hz : z ∈ telReg R R' (m+1)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ + ‖z (⟨m, hm⟩ : Fin n)‖ ≤ R ∧
      Metric.ball z ρ ⊆ telReg R R' (m+1) ∧
      telCyl R (2 * ρ) (⟨m, hm⟩ : Fin n) z ⊆ telReg R R' m := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set j : Fin n := ⟨m, hm⟩ with hj
  have hzj : ‖z j‖ < R := by
    have := hz j
    simpa [telRegB, hj] using this
  set δ : ℝ := (Finset.univ : Finset (Fin n)).inf' Finset.univ_nonempty
    (fun k => telRegB R R' (m+1) k - ‖z k‖) with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    intro k _
    have := hz k
    linarith
  have hδk : ∀ k : Fin n, δ ≤ telRegB R R' (m+1) k - ‖z k‖ := by
    intro k
    rw [hδ]; exact Finset.inf'_le _ (Finset.mem_univ k)
  set ρ : ℝ := min (δ / 4) ((R - ‖z j‖) / 2) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact lt_min (by linarith) (by linarith)
  refine ⟨ρ, hρpos, ?_, ?_, ?_⟩
  · rw [hρdef] at *
    have : ρ ≤ (R - ‖z j‖) / 2 := min_le_right _ _
    linarith
  · refine ball_subset_telReg (fun k => ?_)
    have h3 : ρ ≤ δ / 4 := min_le_left _ _
    have := hδk k
    linarith
  · refine telCyl_subset_telReg hRR' hm hz (fun k hk => ?_)
    have h3 : 2 * ρ ≤ δ / 2 := by
      have hle : ρ ≤ δ / 4 := min_le_left _ _
      linarith
    have := hδk k
    linarith

/-! ## `∂̄`-calculus helpers -/

/-- The `∂̄`-derivative of a `C^{k+1}` function is `C^k`. -/
private lemma contDiffOn_dbarCoord_le {k : ℕ} {u : Work.NN.Core.Cn n → ℂ}
    {s : Set (Work.NN.Core.Cn n)} (hs : IsOpen s) (hu : ContDiffOn ℝ (k + 1) u s) (j : Fin n) :
    ContDiffOn ℝ k (fun z => Work.CR.Flat.dbarCoord j u z) s := by
  have hfd : ContDiffOn ℝ k (fun z => fderiv ℝ u z) s :=
    hu.fderiv_of_isOpen hs (by push_cast; rfl)
  have hfun : (fun z => Work.CR.Flat.dbarCoord j u z)
      = fun z => (Work.CR.Flat.Polydisc.dbarCoordPhi j) (fderiv ℝ u z) := by
    funext z
    exact congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp j u) z
  rw [hfun]
  exact ((Work.CR.Flat.Polydisc.dbarCoordPhi j).contDiff.contDiffOn).comp hfd
    (fun x _ => Set.mem_univ _)

/-- `∂̄` of a difference, at differentiable points. -/
private lemma dbarCoord_sub_apply {u v : Work.NN.Core.Cn n → ℂ} {z : Work.NN.Core.Cn n}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin n) :
    Work.CR.Flat.dbarCoord j (fun y => u y - v y) z
      = Work.CR.Flat.dbarCoord j u z - Work.CR.Flat.dbarCoord j v z := by
  have hfd : fderiv ℝ (fun y => u y - v y) z = fderiv ℝ u z - fderiv ℝ v z :=
    fderiv_sub hu hv
  simp only [Work.CR.Flat.dbarCoord, hfd, sub_apply]
  ring

/-- `∂̄` only depends on the germ. -/
private lemma dbarCoord_congr_of_eventuallyEq {f g : Work.NN.Core.Cn n → ℂ} {z : Work.NN.Core.Cn n}
    (h : f =ᶠ[𝓝 z] g) (j : Fin n) :
    Work.CR.Flat.dbarCoord j f z = Work.CR.Flat.dbarCoord j g z := by
  rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, h.fderiv_eq]

/-- `∂̄` of a function vanishing near a point vanishes there. -/
private lemma dbarCoord_eq_zero_of_eventuallyEq_zero {f : Work.NN.Core.Cn n → ℂ}
    {z : Work.NN.Core.Cn n} (h : f =ᶠ[𝓝 z] 0) (j : Fin n) :
    Work.CR.Flat.dbarCoord j f z = 0 := by
  rw [dbarCoord_congr_of_eventuallyEq h j, Work.CR.Flat.dbarCoord,
    show (0 : Work.NN.Core.Cn n → ℂ) = Function.const _ (0 : ℂ) from rfl, fderiv_const]
  simp

/-- `∂̄` commutes with finite sums, at points where every summand is differentiable. -/
private lemma dbarCoord_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Work.NN.Core.Cn n → ℂ)
    (j : Fin n) (z : Work.NN.Core.Cn n) (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    Work.CR.Flat.dbarCoord j (fun w => ∑ i ∈ s, f i w) z
      = ∑ i ∈ s, Work.CR.Flat.dbarCoord j (f i) z := by
  have hfun : (fun w => ∑ i ∈ s, f i w) = (∑ i ∈ s, f i : Work.NN.Core.Cn n → ℂ) := by
    funext w; simp
  have hsum : fderiv ℝ (∑ i ∈ s, f i : Work.NN.Core.Cn n → ℂ) z
      = ∑ i ∈ s, fderiv ℝ (f i) z := fderiv_sum h
  rw [hfun, Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
  simp only [Function.comp_apply]
  rw [hsum, map_sum]
  simp only [Work.CR.Flat.Polydisc.dbarCoord_eq_comp, Function.comp_apply]

/-- The stage-`m` potential is the fibre potential of the `m`-th row of the stage-`m` defect. -/
private lemma telPsi_eq_fiberPot (R : ℝ) (ζ : Fin n → Fin n → Work.NN.Core.Cn n → ℂ) {m : ℕ}
    (hm : m < n) :
    Work.NN.Core.telPsi R ζ m
      = fun l z => Work.NN.Core.fiberPot R ⟨m, hm⟩
          (Work.NN.Core.telD R ζ m ⟨m, hm⟩ l) z := by
  cases m with
  | zero =>
      funext l z
      rw [Work.NN.Core.telPsi_zero]; simp only [dif_pos hm]
  | succ k =>
      funext l z
      rw [Work.NN.Core.telPsi_succ]; simp only [dif_pos hm]

/-! ## The exponent bookkeeping -/

/-- The regularity exponent `n + 2 - m` of the `m`-th stage, as an element of `WithTop ℕ∞`. -/
private abbrev telExp (n m : ℕ) : WithTop ℕ∞ := ((n + 2 - m : ℕ) : WithTop ℕ∞)

private lemma telExp_zero (n : ℕ) : telExp n 0 = ((n : WithTop ℕ∞) + 2) := by
  simp only [telExp, Nat.sub_zero, Nat.cast_add, Nat.cast_ofNat]

private lemma telExp_succ_le {n m : ℕ} (hm : m ≤ n) : telExp n (m + 1) ≤ telExp n m := by
  unfold telExp
  exact_mod_cast (by omega : n + 2 - (m + 1) ≤ n + 2 - m)

private lemma telExp_succ_add_one {n m : ℕ} (hm : m ≤ n) : telExp n (m + 1) + 1 = telExp n m := by
  unfold telExp
  exact_mod_cast (by omega : n + 2 - (m + 1) + 1 = n + 2 - m)

private lemma contDiffOn_telExp_succ {n m : ℕ} {f : Work.NN.Core.Cn n → ℂ}
    {s : Set (Work.NN.Core.Cn n)} (h : ContDiffOn ℝ (telExp n m) f s) (hm : m ≤ n) :
    ContDiffOn ℝ (telExp n (m + 1)) f s := h.of_le (telExp_succ_le hm)

private lemma contDiffOn_dbarCoord_telExp {n m : ℕ} {u : Work.NN.Core.Cn n → ℂ}
    {s : Set (Work.NN.Core.Cn n)} (hs : IsOpen s) (hu : ContDiffOn ℝ (telExp n m) u s)
    (hm : m ≤ n) (j : Fin n) :
    ContDiffOn ℝ (telExp n (m + 1)) (fun z => Work.CR.Flat.dbarCoord j u z) s := by
  have hk : telExp n m = (((n + 2 - (m + 1)) + 1 : ℕ) : WithTop ℕ∞) := by
    rw [telExp]; congr 1; omega
  rw [hk] at hu
  have h := contDiffOn_dbarCoord_le (k := n + 2 - (m + 1)) hs hu j
  rw [telExp]
  exact h

/-- The `∂̄`-derivative of a `C²` function is differentiable. -/
private lemma diffAt_dbarCoordNN {u : Work.NN.Core.Cn n → ℂ} {z : Work.NN.Core.Cn n}
    (hu : ContDiffAt ℝ 2 u z) (j : Fin n) :
    DifferentiableAt ℝ (fun y => Work.CR.Flat.dbarCoord j u y) z := by
  have hdw : DifferentiableAt ℝ (fun y => fderiv ℝ u y) z :=
    (hu.fderiv_right (m := (1 : ℕ∞)) (by norm_num)).differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ (fun y => (fderiv ℝ u y) (Pi.single j 1)) z :=
    hdw.clm_apply (differentiableAt_const _)
  have h2 : DifferentiableAt ℝ (fun y => (fderiv ℝ u y) (Pi.single j Complex.I)) z :=
    hdw.clm_apply (differentiableAt_const _)
  have h : (fun y => Work.CR.Flat.dbarCoord j u y) = fun y =>
      (1 / 2 : ℂ) * ((fderiv ℝ u y) (Pi.single j 1)
        + Complex.I * (fderiv ℝ u y) (Pi.single j Complex.I)) := rfl
  rw [h]
  exact (differentiableAt_const (1 / 2 : ℂ)).mul
    (h1.add ((differentiableAt_const Complex.I).mul h2))

/-- `∂̄` of a function vanishing on an open set vanishes there. -/
private lemma dbarCoord_eq_zero_of_eq_zero_on_open {s : Set (Work.NN.Core.Cn n)} (hs : IsOpen s)
    {f : Work.NN.Core.Cn n → ℂ} {z : Work.NN.Core.Cn n} (hz : z ∈ s)
    (h0 : ∀ y ∈ s, f y = 0) (j : Fin n) : Work.CR.Flat.dbarCoord j f z = 0 :=
  dbarCoord_eq_zero_of_eventuallyEq_zero
    (Filter.eventually_of_mem (hs.mem_nhds hz) (fun y hy => h0 y hy)) j

end Work.NN.Final

/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The parameterised `(0,2)`-telescoping solves the equation

Adapts `Submission/Work/NN/Final/uS2_solves.lean` to the parametric cutoffs: the per-stage identity
`∂̄_a (uPsi G η s)_b - ∂̄_b (uPsi G η s)_a = (uD G η s)_{ab} - (uD G η (s+1))_{ab}` on the tracking
region, and the telescoping sum giving `∂̄_a (S2 G η)_b - ∂̄_b (S2 G η)_a = η_{ab}` on the solving
polydisc `solveSet G`, for data which are `∂̄`-closed on `{∀ k, ‖z k‖ < G.b k}`.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set Finset

namespace Work.NN.Core.TelTwoDF

variable {n : ℕ}

/-- The one-coordinate identity behind the telescoping: the transform of `kappa · ∂̄_s D` plus the
transform of `kappabar · D` is `D`. -/
private lemma TL_kappa_dbarCoord_add (G : Geom n) {s : Fin n} {D : (Fin n → ℂ) → ℂ}
    (hD : ContDiff ℝ 1 D) {z : Fin n → ℂ} (hzs : ‖z s‖ < G.a s) :
    TL G s (fun y => kappa G s y * Work.CR.Flat.dbarCoord s D y) z
      + TL G s (fun y => kappabar G s y * D y) z = D z := by
  have hG : ContDiff ℝ 1 (fun y => kappa G s y * D y) :=
    ((contDiff_kappa G s).of_le (le_infty'' 1)).mul hD
  have hsum : (fun y => kappa G s y * Work.CR.Flat.dbarCoord s D y)
      + (fun y : Fin n → ℂ => kappabar G s y * D y)
      = fun y => Work.CR.Flat.dbarCoord s (fun y' => kappa G s y' * D y') y := by
    funext y
    rw [Pi.add_apply,
      Work.CR.Flat.Polydisc.dbarCoord_mul s (kappa G s) D y
        ((contDiff_kappa G s).contDiffAt.differentiableAt (by simp))
        ((hD.differentiable one_ne_zero).differentiableAt),
      dbarCoord_kappa G s y]
    ring
  have hcont1 : Continuous (fun y : Fin n → ℂ => kappa G s y * Work.CR.Flat.dbarCoord s D y) :=
    (contDiff_kappa G s).continuous.mul (continuous_dbarCoord hD s)
  have hcont2 : Continuous (fun y : Fin n → ℂ => kappabar G s y * D y) :=
    (contDiff_kappabar G s).continuous.mul hD.continuous
  rw [show TL G s (fun y => kappa G s y * Work.CR.Flat.dbarCoord s D y) z
        + TL G s (fun y => kappabar G s y * D y) z
      = (TL G s (fun y => kappa G s y * Work.CR.Flat.dbarCoord s D y)
        + TL G s (fun y => kappabar G s y * D y)) z from rfl,
    ← map_add, hsum, TL_eq G s (continuous_dbarCoord hG s)]
  have hsupp : ∀ y : Fin n → ℂ, G.r s / 2 ≤ ‖y s‖ → kappa G s y * D y = 0 := fun y hy => by
    rw [kappa_eq_zero G s (le_trans (G.hbr s) hy), zero_mul]
  have hzs' : ‖z s‖ < G.r s / 2 :=
    lt_of_lt_of_le hzs (le_trans (G.hab s).le (G.hbr s))
  rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord_self (G.hr s) s hG hsupp hzs']
  rw [kappa_eq_one G s (le_of_lt hzs), one_mul]

/-- The difference of two transforms is the transform of the difference. -/
private lemma TL_sub (G : Geom n) (s : Fin n) (g h : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    TL G s g z - TL G s h z = TL G s (g - h) z := by
  rw [show TL G s g z - TL G s h z = (TL G s g - TL G s h) z from rfl, map_sub]

/-- The sum of two transforms is the transform of the sum. -/
private lemma TL_add (G : Geom n) (s : Fin n) (g h : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    TL G s (g + h) z = TL G s g z + TL G s h z := by
  rw [map_add]; rfl

/-- The per-term computation: the `(0,2)`-form of `uPsi G η s` is `uD G η s - uD G η (s+1)`. -/
private lemma dbarCoord_uPsi_sub (G : Geom n) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hanti : ∀ i l z, η i l z = - η l i z)
    (hcl : ∀ i l m' z, (∀ k : Fin n, ‖z k‖ < G.b k) →
      Work.CR.Flat.dbarCoord i (η l m') z - Work.CR.Flat.dbarCoord l (η i m') z
        + Work.CR.Flat.dbarCoord m' (η i l) z = 0)
    (s : Fin n) (a b : Fin n) {z : Fin n → ℂ} (hz : z ∈ solveSet G) :
    Work.CR.Flat.dbarCoord a (uPsi G η s b) z - Work.CR.Flat.dbarCoord b (uPsi G η s a) z
      = uD G η (s : ℕ) a b z - uStep G s (uD G η (s : ℕ)) a b z := by
  have hsn : (s : ℕ) ≤ n := le_of_lt s.isLt
  have hzr : ∀ l, ‖z l‖ < G.e l := hz
  have hzs : ‖z s‖ < G.a s := lt_trans (hzr s) (G.hea s)
  have hD : ∀ i l, ContDiff ℝ 1 (uD G η (s : ℕ) i l) :=
    fun i l => uD_contDiff G hη (s : ℕ) hsn i l
  have hantiD : ∀ i l w, uD G η (s : ℕ) i l w = - uD G η (s : ℕ) l i w :=
    fun i l w => uD_antisymm G hanti (s : ℕ) i l w
  have hss_pt : ∀ w : Fin n → ℂ, uD G η (s : ℕ) s s w = 0 :=
    fun w => add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp (hantiD s s w))
  have hss_fun : uD G η (s : ℕ) s s = 0 := funext hss_pt
  have hclosed := uD_closed_E G hη hanti hcl (s : ℕ) hsn
  have h1 : Work.CR.Flat.dbarCoord a (uPsi G η s b) z
      = if a = s then uD G η (s : ℕ) s b z
        else TL G s (fun y => kappa G s y * Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y) z := by
    show Work.CR.Flat.dbarCoord a
      (TL G s (fun y => kappa G s y * uD G η (s : ℕ) s b y)) z = _
    exact dbarCoord_TL_kappa G (hD s b) hzs a
  have h2 : Work.CR.Flat.dbarCoord b (uPsi G η s a) z
      = if b = s then uD G η (s : ℕ) s a z
        else TL G s (fun y => kappa G s y * Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y) z := by
    show Work.CR.Flat.dbarCoord b
      (TL G s (fun y => kappa G s y * uD G η (s : ℕ) s a y)) z = _
    exact dbarCoord_TL_kappa G (hD s a) hzs b
  rw [h1, h2, uStep_apply]
  have hzero_a : TL G s
      (fun y => kappa G s y * Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s s) y) z = 0 := by
    have hfun : (fun y => kappa G s y * Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s s) y)
        = (0 : (Fin n → ℂ) → ℂ) := by
      funext y
      simp [hss_fun, dbarCoord_zero]
    rw [hfun, map_zero]
    rfl
  have hzero_b : TL G s
      (fun y => kappa G s y * Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s s) y) z = 0 := by
    have hfun : (fun y => kappa G s y * Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s s) y)
        = (0 : (Fin n → ℂ) → ℂ) := by
      funext y
      simp [hss_fun, dbarCoord_zero]
    rw [hfun, map_zero]
    rfl
  by_cases ha : a = s
  · by_cases hb : b = s
    · rw [ite_eq_left ha, ite_eq_left hb, ite_eq_left (Or.inl ha), kappa_eq_one G s (le_of_lt hzs),
        ha, hb, hss_pt z]
      ring
    · rw [ite_eq_left ha, ite_eq_right hb, ite_eq_left (Or.inl ha),
        kappa_eq_one G s (le_of_lt hzs), ha, hzero_a]
      ring
  · by_cases hb : b = s
    · rw [ite_eq_right ha, ite_eq_left hb, ite_eq_left (Or.inr hb),
        kappa_eq_one G s (le_of_lt hzs), hb, hzero_b, hantiD a s z]
      ring
    · rw [ite_eq_right ha, ite_eq_right hb,
        ite_eq_right (fun h : a = s ∨ b = s => h.elim ha hb),
        kappa_eq_one G s (le_of_lt hzs), sub_self, zero_mul, zero_add]
      have hzero : TL G s (fun y => kappa G s y
          * (Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y
            - Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y
            - Work.CR.Flat.dbarCoord s (uD G η (s : ℕ) a b) y)) z = 0 := by
        have hcont : Continuous (fun y : Fin n → ℂ => kappa G s y
            * (Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y
              - Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y
              - Work.CR.Flat.dbarCoord s (uD G η (s : ℕ) a b) y)) :=
          (contDiff_kappa G s).continuous.mul
            (((continuous_dbarCoord (hD s b) a).sub (continuous_dbarCoord (hD s a) b)).sub
              (continuous_dbarCoord (hD a b) s))
        rw [TL_eq G s hcont]
        refine Work.CR.Flat.Cauchy.dbarTransform_eq_zero_of_fiber (ρ := G.r s) (j := s)
          (fun y hy => ?_)
        by_cases hyc : ‖y s‖ < G.b s
        · have hyE : y ∈ E G (s : ℕ) := by
            intro m
            refine ⟨?_, ?_⟩
            · intro hm
              have hms : m ≠ s := by intro h; rw [h] at hm; omega
              rw [hy m hms]
              exact hzr m
            · intro hm
              rcases eq_or_ne m s with hms | hms
              · rw [hms]; exact hyc
              · rw [hy m hms]
                exact lt_trans (hzr m) (G.e_lt_b m)
          have hcl' := hclosed s a b y hyE
          have hZ : Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y
              - Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y
              - Work.CR.Flat.dbarCoord s (uD G η (s : ℕ) a b) y = 0 := by
            linear_combination -hcl'
          rw [hZ, mul_zero]
        · rw [kappa_eq_zero G s (le_of_not_gt hyc), zero_mul]
      have hAB : (fun y : Fin n → ℂ => kappa G s y * Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y)
          - (fun y => kappa G s y * Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y)
          = (fun y => kappa G s y * Work.CR.Flat.dbarCoord s (uD G η (s : ℕ) a b) y)
            + (fun y => kappa G s y
                * (Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y
                  - Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y
                  - Work.CR.Flat.dbarCoord s (uD G η (s : ℕ) a b) y)) := by
        funext y
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      rw [TL_sub, hAB, TL_add, hzero, add_zero]
      have hself := TL_kappa_dbarCoord_add G (s := s) (D := uD G η (s : ℕ) a b) (hD a b) hzs
      linear_combination hself

/-- **The parameterised telescoping solves the `(0,2)`-equation** on `solveSet G`, for data which
are antisymmetric and `∂̄`-closed on `{∀ k, ‖z k‖ < G.b k}`. -/
private theorem S2_solves (G : Geom n) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hanti : ∀ i l z, η i l z = - η l i z)
    (hcl : ∀ i l m' z, (∀ k : Fin n, ‖z k‖ < G.b k) →
      Work.CR.Flat.dbarCoord i (η l m') z - Work.CR.Flat.dbarCoord l (η i m') z
        + Work.CR.Flat.dbarCoord m' (η i l) z = 0) :
    ∀ a b : Fin n, ∀ z : Fin n → ℂ, z ∈ solveSet G →
      Work.CR.Flat.dbarCoord a (S2 G η b) z - Work.CR.Flat.dbarCoord b (S2 G η a) z = η a b z := by
  intro a b z hz
  have hzr : ∀ l, ‖z l‖ < G.e l := hz
  have hdiff : ∀ (s l : Fin n), DifferentiableAt ℝ (uPsi G η s l) z := by
    intro s l
    have hs : (s : ℕ) ≤ n := le_of_lt s.isLt
    have hD : ContDiff ℝ 1 (uD G η (s : ℕ) s l) := uD_contDiff G hη (s : ℕ) hs s l
    have hCd : ContDiff ℝ 1 (uPsi G η s l) := by
      show ContDiff ℝ 1 (TL G s (fun y => kappa G s y * uD G η (s : ℕ) s l y))
      exact contDiff_TL G (((contDiff_kappa G s).of_le (le_infty'' 1)).mul hD)
        (fun y hy => by rw [kappa_eq_zero G s hy, zero_mul])
    exact (hCd.differentiable one_ne_zero).differentiableAt
  have h1 : Work.CR.Flat.dbarCoord a (S2 G η b) z
      = ∑ s : Fin n, Work.CR.Flat.dbarCoord a (uPsi G η s b) z := by
    rw [show S2 G η b = fun w => ∑ s : Fin n, uPsi G η s b w from by
      funext w; simp [S2_apply]]
    exact Work.NN.Final.dbarCoord_finset_sum Finset.univ (fun s w => uPsi G η s b w) a z
      (fun s _ => hdiff s b)
  have h2 : Work.CR.Flat.dbarCoord b (S2 G η a) z
      = ∑ s : Fin n, Work.CR.Flat.dbarCoord b (uPsi G η s a) z := by
    rw [show S2 G η a = fun w => ∑ s : Fin n, uPsi G η s a w from by
      funext w; simp [S2_apply]]
    exact Work.NN.Final.dbarCoord_finset_sum Finset.univ (fun s w => uPsi G η s a w) b z
      (fun s _ => hdiff s a)
  have hterm : ∀ s : Fin n, Work.CR.Flat.dbarCoord a (uPsi G η s b) z
      - Work.CR.Flat.dbarCoord b (uPsi G η s a) z
      = uD G η (s : ℕ) a b z - uD G η ((s : ℕ) + 1) a b z := by
    intro s
    have hstep : uStep G s (uD G η (s : ℕ)) a b z = uD G η ((s : ℕ) + 1) a b z := by
      rw [uD_succ_of_lt G η s.isLt]
    rw [dbarCoord_uPsi_sub G hη hanti hcl s a b hz, hstep]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun s _ => hterm s)]
  rw [Fin.sum_univ_eq_sum_range (fun m => uD G η m a b z - uD G η (m + 1) a b z) n,
    Finset.sum_range_sub' (fun m => uD G η m a b z) n, uD_zero,
    uD_vanish G hη n le_rfl a b (Or.inl a.isLt) z (fun k _ => lt_trans (hzr k) (G.hea k)),
    sub_zero]

end Work.NN.Core.TelTwoDF


namespace Work.NN.Core.TelTwoDF


/-- Loss-free `C^{k,α}` estimate and regularity for the parameterised `(0,2)` telescoping
`Work.NN.Core.TelTwoDF.S2` (`Submission/Work/NN/Core/TelTwoDF/Defs.lean`): for `0 < α < 1` and
`G : Geom n` there are constants `C k > 0` with, for every `k` and every family
`η : Fin n → Fin n → (ℂⁿ → ℂ)` with `C^k` components,

`‖(S2 G η)_j‖_{C^{k,α}(polydisc 0 G.e)} ≤ C k · Σ_{i,l} ‖η_{il}‖_{C^{k,α}(polydisc 0 G.b)}`,

and `(S2 G η)_j` is `C^k` on `polydisc 0 G.e`; moreover if `η` has (globally) smooth components
then `(S2 G η)_j` is smooth on `polydisc 0 G.e`.  The recursion (`uD`, `uPsi`, `S2` in
`TelTwoDF/Defs.lean`, with `uD_contDiff`, `E`, `E_mono`, `E_fiber`, `uD_vanish` in
`TelTwoDF/Rec2.lean`) multiplies the previous stage by the smooth cutoffs `1 - kappa G s` and
applies the Cauchy-type transform `TL G s`; the tracking sets `E G m` are polydiscs contained in
`polydisc 0 G.b`, so only a *localized* transform bound (data norm over `E G m`, cf.
`E_fiber`) is needed. -/
private theorem S2Estimate {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (G : Work.NN.Core.TelTwoDF.Geom n) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      (∀ (k : ℕ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
        (∀ i l, ContDiff ℝ k (η i l)) →
        (∀ j : Fin n, ContDiffOn ℝ k (Work.NN.Core.TelTwoDF.S2 G η j)
            (Work.CR.Flat.polydisc 0 G.e)) ∧
        (∀ j : Fin n, Work.CR.Flat.holderNorm k α (Work.NN.Core.TelTwoDF.S2 G η j)
            (Work.CR.Flat.polydisc 0 G.e)
          ≤ ENNReal.ofReal (C k) * ∑ i, ∑ l,
              Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 G.b)))
      ∧ (∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
          (∀ i l, ContDiff ℝ (⊤ : ℕ∞) (η i l)) →
          ∀ j : Fin n, ContDiffOn ℝ (⊤ : ℕ∞) (Work.NN.Core.TelTwoDF.S2 G η j)
            (Work.CR.Flat.polydisc 0 G.e)) := by
  classical
  -- the estimate of `S2` at order `k`, with an `ENNReal` constant
  have hmain : ∀ k : ℕ, ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ), (∀ i l, ContDiff ℝ k (η i l)) →
      ∀ j : Fin n, Work.CR.Flat.holderNorm k α (S2 G η j) (Work.CR.Flat.polydisc 0 G.e)
        ≤ C * ∑ i : Fin n, ∑ l : Fin n,
            Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 G.b) := by
    intro k
    obtain ⟨C, hCne, hC⟩ := S2_holderNorm_E_le_of_transform (n := n) hα0 hα1 k G
      (dbarTransform_Eset_le (n := n) hα0 hα1 k G)
    refine ⟨C, hCne, fun η hη j => ?_⟩
    have h := hC η hη j
    rw [Eset_n, Eset_zero] at h
    exact h
  choose Ce hCe using hmain
  refine ⟨fun k => (Ce k).toReal + 1, fun k => by positivity, ?_, ?_⟩
  · intro k η hη
    refine ⟨fun j => (S2_contDiff_k G hη j).contDiffOn, fun j => ?_⟩
    refine le_trans ((hCe k).2 η hη j) ?_
    have hle : Ce k ≤ ENNReal.ofReal ((Ce k).toReal + 1) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num : (0 : ℝ) ≤ 1),
        ENNReal.ofReal_toReal (hCe k).1, ENNReal.ofReal_one]
      exact le_add_right le_rfl
    exact mul_le_mul_left hle _
  · intro η hη j
    exact (S2_contDiff_top G hη j).contDiffOn

end Work.NN.Core.TelTwoDF


namespace Work.NN.Core

set_option maxHeartbeats 1000000

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter
open Work.CR.Flat

noncomputable section

/-! ## Elementary helpers -/

/-- Additivity of `bmPot` for continuous compactly supported data. -/
private lemma bmPot_add_of_cont {n : ℕ} (hn : 0 < n) {f g : Fin n → (Cn n → ℂ)}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j))
    (hfs : ∀ j, HasCompactSupport (f j)) (hgs : ∀ j, HasCompactSupport (g j)) :
    Work.CR.Flat.Cauchy.bmPot (f + g) = Work.CR.Flat.Cauchy.bmPot f + Work.CR.Flat.Cauchy.bmPot g := by
  funext z
  show Work.CR.Flat.Cauchy.bmPot (f + g) z
      = Work.CR.Flat.Cauchy.bmPot f z + Work.CR.Flat.Cauchy.bmPot g z
  simp only [Work.CR.Flat.Cauchy.bmPot, Pi.add_apply]
  trans ∑ j : Fin n, ((∫ x : Cn n, Work.CR.Flat.Cauchy.bmKernel j x * f j (z + x))
      + ∫ x : Cn n, Work.CR.Flat.Cauchy.bmKernel j x * g j (z + x))
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hi1 : Integrable (fun x : Cn n => Work.CR.Flat.Cauchy.bmKernel j x * f j (z + x)) :=
      integrable_bmKernel_mul hn j ((hf j).comp (continuous_const.add continuous_id))
        ((hfs j).comp_homeomorph (Homeomorph.addLeft z))
    have hi2 : Integrable (fun x : Cn n => Work.CR.Flat.Cauchy.bmKernel j x * g j (z + x)) :=
      integrable_bmKernel_mul hn j ((hg j).comp (continuous_const.add continuous_id))
        ((hgs j).comp_homeomorph (Homeomorph.addLeft z))
    rw [← MeasureTheory.integral_add hi1 hi2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring_nf
  · rw [Finset.sum_add_distrib]

/-- Scalar linearity of `bmPot`. -/
private lemma bmPot_smul_of_cont {n : ℕ} (f : Fin n → (Cn n → ℂ)) (c : ℝ) :
    Work.CR.Flat.Cauchy.bmPot (fun j => fun w => c • f j w) = c • Work.CR.Flat.Cauchy.bmPot f := by
  have h : (fun j => fun w => c • f j w) = fun j => c • f j := rfl
  rw [h]
  funext z
  show Work.CR.Flat.Cauchy.bmPot (fun j => c • f j) z = c • (Work.CR.Flat.Cauchy.bmPot f z)
  simp only [Work.CR.Flat.Cauchy.bmPot, Pi.smul_apply]
  trans ∑ j : Fin n, c • (∫ x : Cn n, Work.CR.Flat.Cauchy.bmKernel j x * f j (z + x))
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (fun x : Cn n => Work.CR.Flat.Cauchy.bmKernel j x * (c • f j (z + x)))
        = fun x : Cn n => c • (Work.CR.Flat.Cauchy.bmKernel j x * f j (z + x)) from by
      funext x; simp only [Complex.real_smul]; ring_nf]
    rw [MeasureTheory.integral_smul]
  · rw [Finset.smul_sum]

/-- `∂̄` of a pointwise negation. -/
private lemma dbarCoord_neg_local {n : ℕ} (j : Fin n) (u : Cn n → ℂ) (z : Cn n) :
    dbarCoord j (- u) z = - dbarCoord j u z := by
  simp only [dbarCoord, fderiv_neg, neg_apply]
  ring_nf

/-- `∂̄` of a difference at a point where both are differentiable. -/
private lemma dbarCoord_sub_local {n : ℕ} (j : Fin n) {u v : Cn n → ℂ} {z : Cn n}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbarCoord j (fun y => u y - v y) z = dbarCoord j u z - dbarCoord j v z := by
  have hfun : (fun y : Cn n => u y - v y) = (fun y : Cn n => u y + (- v) y) := rfl
  rw [hfun, Work.CR.Flat.Polydisc.dbarCoord_add j u (- v) z hu hv.neg, dbarCoord_neg_local]
  ring_nf

/-- If two functions agree on an open neighbourhood of a point then their `∂̄`-derivatives agree. -/
private lemma dbarCoord_congr_of_eventuallyEq_local {n : ℕ} {f g : Cn n → ℂ} {y : Cn n}
    (h : f =ᶠ[𝓝 y] g) (j : Fin n) : dbarCoord j f y = dbarCoord j g y := by
  rw [dbarCoord, dbarCoord, h.fderiv_eq]

/-- Closedness transfers from one function to another that agrees with it on an open set. -/
private lemma closedOn_of_eq_on_open {n : ℕ} {U : Set (Cn n)} (hU : IsOpen U)
    {D E : Fin n → Fin n → Cn n → ℂ}
    (hDE : ∀ j k y, y ∈ U → D j k y = E j k y)
    (hE : ∀ i l k y, dbarCoord i (E l k) y - dbarCoord l (E i k) y
      + dbarCoord k (E i l) y = 0) :
    ∀ i l k y, y ∈ U →
      dbarCoord i (D l k) y - dbarCoord l (D i k) y + dbarCoord k (D i l) y = 0 := by
  intro i l k y hy
  have h1 : dbarCoord i (D l k) y = dbarCoord i (E l k) y :=
    dbarCoord_congr_of_eventuallyEq_local
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hy) (fun z hz => hDE l k z hz)) i
  have h2 : dbarCoord l (D i k) y = dbarCoord l (E i k) y :=
    dbarCoord_congr_of_eventuallyEq_local
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hy) (fun z hz => hDE i k z hz)) l
  have h3 : dbarCoord k (D i l) y = dbarCoord k (E i l) y :=
    dbarCoord_congr_of_eventuallyEq_local
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hy) (fun z hz => hDE i l z hz)) k
  rw [h1, h2, h3, hE]

/-- A compactly supported function vanishes beyond a positive radius. -/
private lemma radius_of_hasCompactSupport {n : ℕ} {f : Cn n → ℂ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ z, R ≤ ‖z‖ → f z = 0 := by
  obtain ⟨C, hC⟩ := hf.isCompact.isBounded.exists_norm_le
  refine ⟨max C 0 + 1, by positivity, fun z hz => ?_⟩
  by_contra hne
  have hzmem : z ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hne)
  have h1 : ‖z‖ ≤ C := hC z hzmem
  have h2 : C ≤ max C 0 := le_max_left C 0
  have h3 : max C 0 + 1 ≤ ‖z‖ := hz
  linarith

/-- If a `C¹` function vanishes on the exterior of the open polydisc `polydisc 0 r` (in the sense
`∃ i, r i ≤ ‖z i‖`) then its `∂̄`-derivatives vanish there as well. -/
private lemma dbarCoord_eq_zero_of_vanishing_exterior {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    {f : Cn n → ℂ} (hf : ContDiff ℝ 1 f) (hsupp : ∀ z, (∃ i, r i ≤ ‖z i‖) → f z = 0)
    (j : Fin n) {z : Cn n} (hz : ∃ i, r i ≤ ‖z i‖) : dbarCoord j f z = 0 := by
  obtain ⟨i₀, hi₀⟩ := hz
  have hzi : z i₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hi₀; exact absurd hi₀ (not_le.mpr (hr i₀))
  set w : Cn n := Pi.single i₀ (z i₀) with hw
  have hw₀ : w i₀ = z i₀ := by rw [hw]; simp
  have hcont : Continuous (fun t : ℝ => dbarCoord j f (z + t • w)) :=
    (Work.CR.Flat.Cauchy.continuous_dbarCoord hf j).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hzero : ∀ t : ℝ, 0 < t → dbarCoord j f (z + t • w) = 0 := by
    intro t ht
    have hy : (z + t • w) i₀ = z i₀ * (1 + (t : ℂ)) := by
      rw [Pi.add_apply, Pi.smul_apply, hw₀, Complex.real_smul]; ring_nf
    have hnorm : r i₀ < ‖(z + t • w) i₀‖ := by
      rw [hy, norm_mul]
      have h1 : 1 + t ≤ ‖(1 : ℂ) + (t : ℂ)‖ := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + t)]
      have h2 : 0 < ‖z i₀‖ := lt_of_lt_of_le (hr i₀) hi₀
      nlinarith [norm_nonneg (z i₀), mul_nonneg h2.le (norm_nonneg ((1:ℂ) + (t:ℂ)))]
    have hnb : ∀ᶠ y in 𝓝 (z + t • w), f y = 0 := by
      have hop : IsOpen {y : Cn n | r i₀ < ‖y i₀‖} :=
        isOpen_lt continuous_const ((continuous_apply i₀).norm)
      filter_upwards [hop.mem_nhds hnorm] with y hy
      exact hsupp y ⟨i₀, le_of_lt hy⟩
    rw [dbarCoord_congr_of_eventuallyEq_local hnb j]
    simp [dbarCoord]
  have h1 : Filter.Tendsto (fun t : ℝ => dbarCoord j f (z + t • w)) (𝓝[>] (0 : ℝ))
      (𝓝 (dbarCoord j f z)) := by
    have h : Filter.Tendsto (fun t : ℝ => dbarCoord j f (z + t • w)) (𝓝 (0 : ℝ))
        (𝓝 (dbarCoord j f z)) := by
      have h := hcont.tendsto (0 : ℝ)
      rwa [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun t : ℝ => dbarCoord j f (z + t • w)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact (hzero t ht).symm)
  exact tendsto_nhds_unique h1 h2

/-- A function vanishing on the exterior of a polydisc (in the sense `∃ i, r i ≤ ‖z i‖`) has
compact support. -/
private lemma hasCompactSupport_of_vanishing_polydisc {n : ℕ} {r : Fin n → ℝ} (hr : ∀ j, 0 < r j)
    {f : Cn n → ℂ} (hf : ∀ z, (∃ i, r i ≤ ‖z i‖) → f z = 0) : HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Cn n) (∑ i, r i)) ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  rw [not_le] at hcon
  rw [Function.mem_support] at hz
  have hex : ∃ i, r i ≤ ‖z i‖ := by
    by_contra h
    push_neg at h
    have h2 : ‖z‖ ≤ ∑ i, r i := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => (hr i).le)]
      intro i
      exact le_trans (le_of_lt (h i))
        (Finset.single_le_sum (fun i _ => (hr i).le) (Finset.mem_univ i))
    linarith
  exact hz (hf z hex)

/-- Continuity of `f · η` when `f` is continuous and vanishes outside a polydisc on which `η` is
continuous (and `f`'s support polydisc is strictly inside). -/
private lemma continuous_mul_of_continuousOn_of_vanishing {n : ℕ} {f η : Cn n → ℂ} {r ρ : Fin n → ℝ}
    (hρr : ∀ j, r j < ρ j) (hη : ContDiffOn ℝ 1 η (polydisc 0 ρ))
    (hf : Continuous f) (hfzero : ∀ z, (∃ i, r i ≤ ‖z i‖) → f z = 0) :
    Continuous (fun w => f w * η w) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x ∈ polydisc 0 ρ
  · exact (hf.continuousAt.mul
      (hη.continuousOn.continuousAt ((isOpen_polydisc 0 ρ).mem_nhds hx)))
  · have hx' : ∃ i, r i < ‖x i‖ := by
      by_contra h; push_neg at h
      exact hx (fun i => by simpa using lt_of_le_of_lt (h i) (hρr i))
    obtain ⟨i, hi⟩ := hx'
    have hnb : ∀ᶠ y in 𝓝 x, f y = 0 := by
      have hop : IsOpen {y : Cn n | r i < ‖y i‖} :=
        isOpen_lt continuous_const ((continuous_apply i).norm)
      filter_upwards [hop.mem_nhds hi] with y hy
      exact hfzero y ⟨i, le_of_lt hy⟩
    exact (continuousAt_const (x := x)).congr (by
      filter_upwards [hnb] with y hy
      rw [hy, zero_mul])

/-- `∂̄` of a smooth function is smooth.

NOTE (import-walls session): the *canonical* public declaration of this name in namespace
`Work.NN.Core` is the more general one in `Core/holderNorm_fiberPot_of_vanishing.lean`
(`ContDiff ℝ (k+1) η → ContDiff ℝ k (∂̄ η)`, whose 7 closure-users dominate this file's 1).  This
copy is therefore *renamed* here (and in its five dependent users: `Core/dbarHonestTwoLocal`,
`Core/closedProjectionK`, `Core/closedProjectionKNoW`, `Core/closedProjection0_of_crux`,
`Core/exists_sourceSolverC1a`); the two chains then no longer declare the same constant.  Note
`private` would have been enough for the name clash but it hides the declaration from those five
dependents, which see it through this file.  See `NOTES_uniformDbarL2_session.md` §13. -/
private lemma contDiff_dbarCoord_of_smooth_top {n : ℕ} {f : Cn n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (dbarCoord j f) := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi j).contDiff.comp (hf.fderiv_right (by simp))

/-- The Bochner–Martinelli potential of smooth compactly supported data is smooth. -/
private lemma contDiff_bmPot_top {n : ℕ} (hn : 0 < n) {f : Fin n → Cn n → ℂ}
    (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (hcs : ∀ j, HasCompactSupport (f j)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => Work.CR.Flat.Cauchy.bmPot f y) := by
  have heq : (fun y => Work.CR.Flat.Cauchy.bmPot f y)
      = fun y => Work.CR.Flat.Cauchy.bmPotential f y := by
    funext y; exact (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f y).symm
  rw [heq, contDiff_infty]
  intro m
  exact Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn (i := m)
    (fun j => (hf j).of_le (by simp)) hcs

/-- The Bochner–Martinelli potential of compactly supported data of class `C^m` (`m` finite). -/
private lemma contDiff_bmPot_of {n : ℕ} (hn : 0 < n) {m : ℕ} {f : Fin n → Cn n → ℂ}
    (hf : ∀ j, ContDiff ℝ m (f j)) (hcs : ∀ j, HasCompactSupport (f j)) :
    ContDiff ℝ m (fun y => Work.CR.Flat.Cauchy.bmPot f y) := by
  have heq : (fun y => Work.CR.Flat.Cauchy.bmPot f y)
      = fun y => Work.CR.Flat.Cauchy.bmPotential f y := by
    funext y; exact (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f y).symm
  rw [heq]
  exact Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn hf hcs

/-- `bmRow` of compactly supported data of class `C^m` (`m` finite) is of class `C^m`. -/
private lemma contDiff_bmRow_of {n : ℕ} (hn : 0 < n) {m : ℕ} {f : Fin n → Fin n → Cn n → ℂ}
    (hf : ∀ j l, ContDiff ℝ m (f j l)) (hcs : ∀ j l, HasCompactSupport (f j l)) (j : Fin n) :
    ContDiff ℝ m (bmRow f j) := by
  have heq : (bmRow f j) = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      * Work.CR.Flat.Cauchy.bmPot (fun l => f j l) y := rfl
  rw [heq]
  exact contDiff_const.mul (contDiff_bmPot_of hn (fun l => hf j l) (fun l => hcs j l))

/-- `bmRow` of smooth compactly supported data is smooth. -/
private lemma contDiff_bmRow_top {n : ℕ} (hn : 0 < n) {f : Fin n → Fin n → Cn n → ℂ}
    (hf : ∀ j l, ContDiff ℝ (⊤ : ℕ∞) (f j l)) (hcs : ∀ j l, HasCompactSupport (f j l))
    (j : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (bmRow f j) := by
  have heq : (bmRow f j) = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      * Work.CR.Flat.Cauchy.bmPot (fun l => f j l) y := rfl
  rw [heq]
  exact contDiff_const.mul (contDiff_bmPot_top hn (fun l => hf j l) (fun l => hcs j l))

/-- Associativity of `ENNReal.ofReal` with a product in the middle. -/
private lemma ofReal_mul_mul_assoc {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (X : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * X) = ENNReal.ofReal (a * b) * X := by
  rw [ENNReal.ofReal_mul (q := b) ha, mul_assoc]

/-- Subadditivity of the `C^{k,α}` norm along a difference. -/
private lemma holderNorm_sub_le {n : ℕ} {k : ℕ} {α : ℝ} {f g : Cn n → ℂ} {Ω : Set (Cn n)}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hg : ContDiffOn ℝ (k : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω) :
    holderNorm k α (f - g) Ω ≤ holderNorm k α f Ω + holderNorm k α g Ω := by
  have hfun : (f - g) = f + (-g) := rfl
  calc holderNorm k α (f - g) Ω
      = holderNorm k α (f + (-g)) Ω := by rw [hfun]
    _ ≤ holderNorm k α f Ω + holderNorm k α (-g) Ω :=
        Work.CR.Flat.Holder.holderNorm_add_le hf hg.neg hΩ
    _ = holderNorm k α f Ω + holderNorm k α g Ω := by
        rw [Work.CR.Flat.Holder.holderNorm_neg hg hΩ]

/-- A smooth function of compact support (vanishing outside a polydisc strictly inside) times a
function smooth on that polydisc is globally smooth. -/
private lemma contDiff_mul_of_contDiffOnFK {n : ℕ} {r ρ : Fin n → ℝ} (hρr : ∀ j, r j < ρ j)
    (m : WithTop ℕ∞) {χ η : Cn n → ℂ} (hχ : ContDiff ℝ m χ)
    (hη : ContDiffOn ℝ m η (polydisc 0 ρ))
    (hχzero : ∀ z : Cn n, (∃ i, r i ≤ ‖z i‖) → χ z = 0) :
    ContDiff ℝ m (fun w => χ w * η w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ polydisc 0 ρ
  · exact hχ.contDiffAt.mul (hη.contDiffAt ((isOpen_polydisc 0 ρ).mem_nhds hx))
  · have hx' : ∃ i, r i < ‖x i‖ := by
      by_contra h; push_neg at h
      exact hx (fun i => lt_of_le_of_lt (by simpa using h i) (hρr i))
    obtain ⟨i, hi⟩ := hx'
    have hnb : ∀ᶠ y in 𝓝 x, χ y = 0 := by
      have hop : IsOpen {y : Cn n | r i < ‖y i‖} :=
        isOpen_lt continuous_const ((continuous_apply i).norm)
      filter_upwards [hop.mem_nhds hi] with y hy
      exact hχzero y ⟨i, le_of_lt hy⟩
    have h2 : (fun w => χ w * η w) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [hnb] with y hy
      simp [hy]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq h2

/-- **The analytic core of the `(0,2)` Poincaré lemma on a polydisc.** -/
private theorem dbarHonestTwo {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j) :
    ∃ (T2 : (Fin n → Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] (Fin n → (Fin n → ℂ) → ℂ))
      (C : ℕ → ℝ),
      (∀ k, 0 < C k) ∧
      (∀ η, (∀ j l, ContDiff ℝ 1 (η j l)) →
        (∀ j l z, η j l z = -η l j z) →
        (∀ j l m z, Work.CR.Flat.dbarCoord j (η l m) z - Work.CR.Flat.dbarCoord l (η j m) z
          + Work.CR.Flat.dbarCoord m (η j l) z = 0) →
        ∀ j l (z : Fin n → ℂ), z ∈ Work.CR.Flat.polydisc 0 ρ' →
          Work.CR.Flat.dbarCoord j (T2 η l) z - Work.CR.Flat.dbarCoord l (T2 η j) z = η j l z) ∧
      (∀ (k : ℕ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
        (∀ j l, ContDiff ℝ (k + 1) (η j l)) →
        (∀ j l z, η j l z = -η l j z) →
        (∀ j l m z, Work.CR.Flat.dbarCoord j (η l m) z - Work.CR.Flat.dbarCoord l (η j m) z
          + Work.CR.Flat.dbarCoord m (η j l) z = 0) →
        (∀ j, ContDiffOn ℝ (k + 1) (T2 η j) (Work.CR.Flat.polydisc 0 ρ')) ∧
        (∀ j, Work.CR.Flat.holderNorm (k + 1) α (T2 η j) (Work.CR.Flat.polydisc 0 ρ')
          ≤ ENNReal.ofReal (C k) *
              ∑ j, ∑ l, Work.CR.Flat.holderNorm k α (η j l) (Work.CR.Flat.polydisc 0 ρ))) ∧
      (∀ η, (∀ j l, ContDiffOn ℝ (⊤ : ℕ∞) (η j l) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, η j l z = -η l j z) →
        (∀ j l m z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (η l m) z - Work.CR.Flat.dbarCoord l (η j m) z
            + Work.CR.Flat.dbarCoord m (η j l) z = 0) →
        ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (T2 η j) (Work.CR.Flat.polydisc 0 ρ')) := by
  classical
  -- (0) the distinguished coordinate
  obtain ⟨m, -, hmle⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun j => ρ' j)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  -- (1) intermediate multi-radii
  set ρ'' : Fin n → ℝ := fun j => (2 * ρ' j + ρ j) / 3 with hρ''def
  set ρ''' : Fin n → ℝ := fun j => (ρ' j + 2 * ρ j) / 3 with hρ'''def
  have hρ''pos : ∀ j, 0 < ρ'' j := fun j => by
    show 0 < (2 * ρ' j + ρ j) / 3; linarith [hρ' j, hρ j]
  have hρ'''pos : ∀ j, 0 < ρ''' j := fun j => by
    show 0 < (ρ' j + 2 * ρ j) / 3; linarith [hρ' j, hρ j]
  have hρ'ρ'' : ∀ j, ρ' j < ρ'' j := fun j => by
    show ρ' j < (2 * ρ' j + ρ j) / 3; linarith [hlt j]
  have hρ''ρ''' : ∀ j, ρ'' j < ρ''' j := fun j => by
    show (2 * ρ' j + ρ j) / 3 < (ρ' j + 2 * ρ j) / 3; linarith [hlt j]
  have hρ'''ρ : ∀ j, ρ''' j < ρ j := fun j => by
    show (ρ' j + 2 * ρ j) / 3 < ρ j; linarith [hlt j]
  have hρ''ρ : ∀ j, ρ'' j < ρ j := fun j => lt_trans (hρ''ρ''' j) (hρ'''ρ j)
  -- (2) the cutoff
  obtain ⟨u, hu_sm, _hu01, hu_one, hu_zero, hu_cs, _hu_dbar_sm, _hu_dbar_cs⟩ :=
    Work.CR.Flat.Cauchy.polydiscCutoff (n := n) (c := (0 : Cn n)) (r₁ := ρ'') (r₂ := ρ''') 0
      hρ''pos hρ''ρ'''
  set χ : Cn n → ℂ := fun z => (u z : ℂ) with hχdef
  have hχ_sm : ContDiff ℝ (⊤ : ℕ∞) χ := by
    rw [hχdef]; exact Complex.ofRealCLM.contDiff.comp hu_sm
  have hχ_cd1 : ContDiff ℝ 1 χ := hχ_sm.of_le (by simp)
  have hχ_cs : HasCompactSupport χ := hu_cs
  have hχ_one : ∀ z : Cn n, (∀ j, ‖z j‖ ≤ ρ'' j) → χ z = 1 := by
    intro z hz
    show (u z : ℂ) = 1
    rw [hu_one z (fun j => by simpa using hz j)]; norm_num
  have hχ_zero : ∀ z : Cn n, (∃ j, ρ''' j ≤ ‖z j‖) → χ z = 0 := by
    intro z hz
    show (u z : ℂ) = 0
    rw [hu_zero z (by obtain ⟨j, hj⟩ := hz; exact ⟨j, by simpa using hj⟩)]; norm_num
  have hχdbar_zero : ∀ (s : Fin n) (z : Cn n), (∃ j, ρ''' j ≤ ‖z j‖) → dbarCoord s χ z = 0 :=
    fun s z hz => dbarCoord_eq_zero_of_vanishing_exterior hρ'''pos hχ_cd1 hχ_zero s hz
  obtain ⟨Rχ, hRχpos, hRχsupp⟩ := radius_of_hasCompactSupport hχ_cs
  -- (3) the geometry of the telescoping
  set G : TelTwoDF.Geom n :=
    { e := ρ'
      a := fun j => (ρ' j + (ρ' j + ρ'' j) / 2) / 2
      b := fun j => (ρ' j + ρ'' j) / 2
      r := fun j => 2 * ((ρ' j + ρ'' j) / 2)
      he := hρ'
      hea := fun j => by linarith [hρ'ρ'' j]
      ha := fun j => by linarith [hρ' j, hρ''pos j]
      hab := fun j => by linarith [hρ'ρ'' j]
      hr := fun j => by linarith [hρ' j, hρ''pos j]
      hbr := fun j => by linarith } with hGdef
  have hGb : ∀ j, G.b j = (ρ' j + ρ'' j) / 2 := fun j => rfl
  have hGbg : ∀ j, G.b j < ρ'' j := fun j => by rw [hGb j]; linarith [hρ'ρ'' j]
  have hGe : G.e = ρ' := rfl
  -- (4) the defect and the operator
  set Ddef : (Fin n → Fin n → Cn n → ℂ) → Fin n → Fin n → Cn n → ℂ :=
    fun η j k y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η j k l) y with hDdefdef
  have hDdef_apply : ∀ η j k y, Ddef η j k y = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η j k l) y := fun _ _ _ _ => rfl
  have hopFun_apply : ∀ (η : Fin n → Fin n → Cn n → ℂ) l z,
      (bmRow (fun i l' w => χ w * η i l' w) l - TelTwoDF.S2 G (Ddef η) l) z
        = bmRow (fun i l' w => χ w * η i l' w) l z - TelTwoDF.S2 G (Ddef η) l z :=
    fun _ _ _ => rfl
  let opFun : (Fin n → Fin n → Cn n → ℂ) → (Fin n → Cn n → ℂ) :=
    fun η l => bmRow (fun i l' w => χ w * η i l' w) l - TelTwoDF.S2 G (Ddef η) l
  -- (5) the domain of the linear operator
  let V : Submodule ℝ (Fin n → Fin n → Cn n → ℂ) :=
    { carrier := {η | ∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ)}
      zero_mem' := fun i l => contDiffOn_const
      add_mem' := fun {f g} hf hg => by
        intro i l
        exact (hf i l).add (hg i l)
      smul_mem' := fun c {f} hf => by
        intro i l
        exact (hf i l).const_smul c }
  have hVmem : ∀ η : Fin n → Fin n → Cn n → ℂ,
      η ∈ V ↔ ∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ) := fun _ => Iff.rfl
  -- smoothness of the pieces
  have hbmH_cd : ∀ (i : ℕ) (η : Fin n → Fin n → Cn n → ℂ), (∀ j l, ContDiff ℝ i (η j l)) →
      ∀ j k l, ContDiff ℝ i (bmH χ η j k l) := by
    intro i η hη j k l
    have hd : ∀ s : Fin n, ContDiff ℝ i (dbarCoord s χ) := fun s =>
      (contDiff_dbarCoord_of_smooth_top hχ_sm s).of_le (by simp)
    show ContDiff ℝ i (fun w => dbarCoord l χ w * η j k w + dbarCoord j χ w * η k l w
      - dbarCoord k χ w * η j l w)
    exact (((hd l).mul (hη j k)).add ((hd j).mul (hη k l))).sub ((hd k).mul (hη j l))
  have hbmH_cs : ∀ (η : Fin n → Fin n → Cn n → ℂ), ∀ j k l, HasCompactSupport (bmH χ η j k l) := by
    intro η j k l
    refine hasCompactSupport_of_vanishing_polydisc hρ'''pos (fun z hz => ?_)
    show dbarCoord l χ z * η j k z + dbarCoord j χ z * η k l z - dbarCoord k χ z * η j l z = 0
    rw [hχdbar_zero l z hz, hχdbar_zero j z hz, hχdbar_zero k z hz]; ring_nf
  have hbmH_cont : ∀ (η : Fin n → Fin n → Cn n → ℂ),
      (∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ)) →
      ∀ j k l, Continuous (bmH χ η j k l) := by
    intro η hη j k l
    have hd : ∀ s : Fin n, Continuous (dbarCoord s χ) := fun s =>
      Work.CR.Flat.Cauchy.continuous_dbarCoord hχ_cd1 s
    have h1 : Continuous (fun w => dbarCoord l χ w * η j k w) :=
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ (hη j k) (hd l) (hχdbar_zero l)
    have h2 : Continuous (fun w => dbarCoord j χ w * η k l w) :=
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ (hη k l) (hd j) (hχdbar_zero j)
    have h3 : Continuous (fun w => dbarCoord k χ w * η j l w) :=
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ (hη j l) (hd k) (hχdbar_zero k)
    show Continuous (fun w => dbarCoord l χ w * η j k w + dbarCoord j χ w * η k l w
      - dbarCoord k χ w * η j l w)
    exact (h1.add h2).sub h3
  -- additivity of the defect
  have hDdef_add : ∀ η₁ η₂ : Fin n → Fin n → Cn n → ℂ, η₁ ∈ V → η₂ ∈ V →
      Ddef (η₁ + η₂) = Ddef η₁ + Ddef η₂ := by
    intro η₁ η₂ h₁ h₂
    funext j k y
    have hc₁ : ∀ l, Continuous (fun y => bmH χ η₁ j k l y) :=
      fun l => hbmH_cont η₁ ((hVmem η₁).mp h₁) j k l
    have hc₂ : ∀ l, Continuous (fun y => bmH χ η₂ j k l y) :=
      fun l => hbmH_cont η₂ ((hVmem η₂).mp h₂) j k l
    have hsum : (fun l => bmH χ (η₁ + η₂) j k l)
        = (fun l => bmH χ η₁ j k l) + (fun l => bmH χ η₂ j k l) := by
      funext l y
      show dbarCoord l χ y * (η₁ + η₂) j k y + dbarCoord j χ y * (η₁ + η₂) k l y
          - dbarCoord k χ y * (η₁ + η₂) j l y
        = (dbarCoord l χ y * η₁ j k y + dbarCoord j χ y * η₁ k l y
            - dbarCoord k χ y * η₁ j l y)
          + (dbarCoord l χ y * η₂ j k y + dbarCoord j χ y * η₂ k l y
            - dbarCoord k χ y * η₂ j l y)
      simp only [Pi.add_apply]; ring
    show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ (η₁ + η₂) j k l) y
        = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η₁ j k l) y
          + -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η₂ j k l) y
    rw [hsum, bmPot_add_of_cont hn hc₁ hc₂ (fun l => hbmH_cs η₁ j k l)
      (fun l => hbmH_cs η₂ j k l)]
    simp only [Pi.add_apply]
    ring
  have hDdef_smul : ∀ (c : ℝ) (η : Fin n → Fin n → Cn n → ℂ), η ∈ V →
      Ddef (c • η) = c • Ddef η := by
    intro c η h
    funext j k y
    have hsum : (fun l => bmH χ (c • η) j k l) = fun l => c • bmH χ η j k l := by
      funext l y
      show dbarCoord l χ y * (c • η) j k y + dbarCoord j χ y * (c • η) k l y
          - dbarCoord k χ y * (c • η) j l y
        = c • (dbarCoord l χ y * η j k y + dbarCoord j χ y * η k l y
            - dbarCoord k χ y * η j l y)
      simp only [Pi.smul_apply, Complex.real_smul]; ring
    show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ (c • η) j k l) y
        = c • (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η j k l) y)
    rw [hsum]
    rw [show (fun l => c • bmH χ η j k l)
        = (fun l => fun w => c • bmH χ η j k l w) from rfl]
    rw [bmPot_smul_of_cont]
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  -- additivity of the operator
  have hopFun_add : ∀ η₁ η₂ : Fin n → Fin n → Cn n → ℂ, η₁ ∈ V → η₂ ∈ V →
      opFun (η₁ + η₂) = opFun η₁ + opFun η₂ := by
    intro η₁ η₂ h₁ h₂
    funext l z
    have hcont₁ : ∀ l', Continuous (fun w => χ w * η₁ l l' w) := fun l' =>
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ ((hVmem η₁).mp h₁ l l')
        hχ_sm.continuous hχ_zero
    have hcont₂ : ∀ l', Continuous (fun w => χ w * η₂ l l' w) := fun l' =>
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ ((hVmem η₂).mp h₂ l l')
        hχ_sm.continuous hχ_zero
    have hcs₁ : ∀ l', HasCompactSupport (fun w => χ w * η₁ l l' w) := fun l' =>
      hasCompactSupport_of_vanishing_polydisc hρ'''pos
        (fun z hz => by rw [hχ_zero z hz, zero_mul])
    have hcs₂ : ∀ l', HasCompactSupport (fun w => χ w * η₂ l l' w) := fun l' =>
      hasCompactSupport_of_vanishing_polydisc hρ'''pos
        (fun z hz => by rw [hχ_zero z hz, zero_mul])
    have hsum : (fun l' => fun w => χ w * (η₁ l l' w + η₂ l l' w))
        = (fun l' => fun w => χ w * η₁ l l' w) + (fun l' => fun w => χ w * η₂ l l' w) := by
      funext l' w; simp only [Pi.add_apply]; ring
    have hrow : bmRow (fun i l' w => χ w * (η₁ i l' w + η₂ i l' w)) l z
        = bmRow (fun i l' w => χ w * η₁ i l' w) l z
          + bmRow (fun i l' w => χ w * η₂ i l' w) l z := by
      simp only [Work.NN.Core.bmRow]
      rw [hsum, bmPot_add_of_cont hn hcont₁ hcont₂ hcs₁ hcs₂]
      simp only [Pi.add_apply]
      ring
    have hS2 : TelTwoDF.S2 G (Ddef (η₁ + η₂)) l z
        = TelTwoDF.S2 G (Ddef η₁) l z + TelTwoDF.S2 G (Ddef η₂) l z := by
      rw [show Ddef (η₁ + η₂) = Ddef η₁ + Ddef η₂ from hDdef_add η₁ η₂ h₁ h₂,
        TelTwoDF.S2_add]
      rfl
    show bmRow (fun i l' w => χ w * (η₁ i l' w + η₂ i l' w)) l z
        - TelTwoDF.S2 G (Ddef (η₁ + η₂)) l z
      = (bmRow (fun i l' w => χ w * η₁ i l' w) l z - TelTwoDF.S2 G (Ddef η₁) l z)
        + (bmRow (fun i l' w => χ w * η₂ i l' w) l z - TelTwoDF.S2 G (Ddef η₂) l z)
    rw [hrow, hS2]
    ring
  have hopFun_smul : ∀ (c : ℝ) (η : Fin n → Fin n → Cn n → ℂ), η ∈ V →
      opFun (c • η) = c • opFun η := by
    intro c η h
    funext l z
    have hcont : ∀ l', Continuous (fun w => χ w * η l l' w) := fun l' =>
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ ((hVmem η).mp h l l')
        hχ_sm.continuous hχ_zero
    have hsum : (fun l' => fun w => χ w * ((c • η) l l' w))
        = fun l' => fun w => c • (χ w * η l l' w) := by
      funext l' w; simp only [Pi.smul_apply, Complex.real_smul]; ring
    have hrow : bmRow (fun i l' w => χ w * ((c • η) i l' w)) l z
        = c • bmRow (fun i l' w => χ w * η i l' w) l z := by
      simp only [Work.NN.Core.bmRow]
      rw [hsum, bmPot_smul_of_cont]
      simp only [Pi.smul_apply, Complex.real_smul]
      ring
    have hS2 : TelTwoDF.S2 G (Ddef (c • η)) l z = c • TelTwoDF.S2 G (Ddef η) l z := by
      rw [show Ddef (c • η) = c • Ddef η from hDdef_smul c η h, TelTwoDF.S2_smul]
      rfl
    show bmRow (fun i l' w => χ w * ((c • η) i l' w)) l z
        - TelTwoDF.S2 G (Ddef (c • η)) l z
      = (c : ℂ) * (bmRow (fun i l' w => χ w * η i l' w) l z
          - TelTwoDF.S2 G (Ddef η) l z)
    rw [hrow, hS2]
    simp only [Complex.real_smul]
    ring
  -- (6) the linear operator
  let opLin : V →ₗ[ℝ] (Fin n → Cn n → ℂ) :=
    { toFun := fun η => opFun η.1
      map_add' := fun η₁ η₂ => hopFun_add η₁.1 η₂.1 η₁.2 η₂.2
      map_smul' := fun c η => hopFun_smul c η.1 η.2 }
  obtain ⟨T2, hT2⟩ := LinearMap.exists_extend opLin
  have hT2_apply : ∀ (η : Fin n → Fin n → Cn n → ℂ) (h : η ∈ V), T2 η = opFun η := by
    intro η h
    have hh := congrArg (fun (g : V →ₗ[ℝ] (Fin n → Cn n → ℂ)) => g ⟨η, h⟩) hT2
    have h1 : opLin ⟨η, h⟩ = opFun η := rfl
    rw [h1] at hh
    simpa [LinearMap.comp_apply] using hh
  obtain ⟨CS, hCSpos, hCSreg, hCSsm⟩ := Work.NN.Core.TelTwoDF.S2Estimate hα hα1 G
  have hρ'ρ''' : ∀ j, ρ' j < ρ''' j := fun j => lt_trans (hρ'ρ'' j) (hρ''ρ''' j)
  have hρ'''2ρ'' : ∀ j, ρ''' j < 2 * ρ'' j := fun j => by
    show (ρ' j + 2 * ρ j) / 3 < 2 * ((2 * ρ' j + ρ j) / 3)
    linarith [hρ' j]
  obtain ⟨Crow, hCrowpos, hCrowbd⟩ :=
    Work.NN.Core.bmRowCutoffEstimate hn hα hα1 hρ'''pos hρ'ρ''' hρ'''ρ χ hχ_sm hχ_cs hχ_zero
  obtain ⟨Cpot, hCpotpos, hCpotbd⟩ :=
    Work.NN.Core.bmPotCutoffEstimate hn hα hα1 hρ''pos hρ'''2ρ'' hρ'''ρ χ hχ_sm hχ_cs hχ_zero
  have hχη_cs_all : ∀ (η' : Fin n → Fin n → Cn n → ℂ) (i l : Fin n),
      HasCompactSupport (fun w => χ w * η' i l w) := fun η' i l =>
    hasCompactSupport_of_vanishing_polydisc hρ'''pos
      (fun z hz => by rw [hχ_zero z hz, zero_mul])
  have hbmH_cs_all : ∀ (η' : Fin n → Fin n → Cn n → ℂ) (j kk l : Fin n),
      HasCompactSupport (bmH χ η' j kk l) := fun η' j kk l =>
    hasCompactSupport_of_vanishing_polydisc hρ'''pos (fun z hz => by
      show dbarCoord l χ z * η' j kk z + dbarCoord j χ z * η' kk l z
          - dbarCoord kk χ z * η' j l z = 0
      rw [hχdbar_zero l z hz, hχdbar_zero j z hz, hχdbar_zero kk z hz]; ring_nf)
  refine ⟨T2, fun k => Crow k + CS (k + 1) * ((n : ℝ) * (n : ℝ)
      * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)), ?_, ?_, ?_, ?_⟩
  · intro k
    have h2 : 0 ≤ CS (k + 1) * ((n : ℝ) * (n : ℝ)
        * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)) := by
      have h1 := hCSpos (k + 1)
      have h3 := hCpotpos k
      positivity
    linarith [hCrowpos k]
  · -- clause (a)
    intro η hη hanti hcl
    intro j l z hz
    have hV : η ∈ V := by
      rw [hVmem]; intro i l; exact (hη i l).contDiffOn
    have hbmdef := Work.NN.Core.bmDefect_eq hn hRχpos χ hχ_cd1 hRχsupp η hη hcl
    have hχη_cs : ∀ i l, HasCompactSupport (fun w => χ w * η i l w) := fun i l =>
      hasCompactSupport_of_vanishing_polydisc hρ'''pos
        (fun z hz => by rw [hχ_zero z hz, zero_mul])
    have hD_cd1 : ∀ i l, ContDiff ℝ 1 (Ddef η i l) := by
      intro i l
      have hc : ∀ l', ContDiff ℝ 1 (bmH χ η i l l') := fun l' =>
        hbmH_cd 1 η (fun j m => hη j m) i l l'
      have h := (contDiff_const (c := -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))).mul
        (Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport
          hn (i := 1) hc (fun l' => hbmH_cs η i l l'))
      have heq : (fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPotential (fun l' => bmH χ η i l l') y) = Ddef η i l := by
        funext y
        show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPotential (fun l' => bmH χ η i l l') y
            = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y
        rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
      rw [← heq]; exact h
    have hD_anti : ∀ i l z, Ddef η i l z = - Ddef η l i z := by
      intro i l z
      have hswap : ∀ m w, bmH χ η i l m w = - bmH χ η l i m w := by
        intro m w
        show dbarCoord m χ w * η i l w + dbarCoord i χ w * η l m w - dbarCoord l χ w * η i m w
          = -(dbarCoord m χ w * η l i w + dbarCoord l χ w * η i m w
              - dbarCoord i χ w * η l m w)
        rw [hanti i l w]; ring
      show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η i l m) z
          = - (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η l i m) z)
      have hfam : (fun m => bmH χ η i l m) = fun m => fun w => (-1 : ℝ) • bmH χ η l i m w := by
        funext m w; rw [hswap m w]; simp
      rw [hfam, bmPot_smul_of_cont]
      show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * (((-1 : ℝ) • Work.CR.Flat.Cauchy.bmPot (bmH χ η l i)) z)
          = - (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (bmH χ η l i) z)
      rw [Pi.smul_apply, neg_one_smul]
      ring
    have hD_closed : ∀ i l k y, y ∈ polydisc 0 ρ'' →
        dbarCoord i (Ddef η l k) y - dbarCoord l (Ddef η i k) y
          + dbarCoord k (Ddef η i l) y = 0 := by
      refine closedOn_of_eq_on_open (isOpen_polydisc 0 ρ'') (fun j k y hy => ?_)
        (Work.NN.Core.bmDefectClosed hn hχ_sm hχ_cs hη hanti hcl)
      have hcy : χ y = 1 := hχ_one y (fun i => le_of_lt (by simpa using hy i))
      show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j k m) y
          = bmDefect χ η j k y
      have hdef : bmDefect χ η j k y = (χ y - 1) * η j k y
            + -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j k m) y := by
        show (χ y - 1) * η j k y - ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j k m) y
            = (χ y - 1) * η j k y + -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j k m) y
        ring
      rw [hdef, hcy]; ring
    have hsolve := TelTwoDF.S2_solves G (η := Ddef η) hD_cd1 hD_anti
      (fun i l k z hz2 => hD_closed i l k z
        (fun j => lt_of_lt_of_le (lt_trans (by simpa using hz2 j) (hGbg j)) (le_refl _)))
    have hdrow : ∀ i : Fin n,
        DifferentiableAt ℝ (bmRow (fun i' l' w => χ w * η i' l' w) i) z := by
      intro i
      have h := (contDiff_const (c := -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))).mul
        (Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport
          hn (i := 1) (fun l' => hχ_cd1.mul (hη i l')) (fun l' => hχη_cs i l'))
      have heq : bmRow (fun i' l' w => χ w * η i' l' w) i
          = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPotential (fun l' => fun w => χ w * η i l' w) y := by
        funext y; rw [Work.NN.Core.bmRow_apply, Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
      rw [heq]; exact (h.differentiable (by norm_num)).differentiableAt
    have hdS2 : ∀ i : Fin n, DifferentiableAt ℝ (TelTwoDF.S2 G (Ddef η) i) z := by
      intro i
      have hcd := hCSreg 1 (Ddef η) hD_cd1
      exact ((hcd.1 i).contDiffAt
        ((isOpen_polydisc 0 G.e).mem_nhds (by rw [hGe]; exact hz))).differentiableAt one_ne_zero
    have hsol : dbarCoord j (TelTwoDF.S2 G (Ddef η) l) z
        - dbarCoord l (TelTwoDF.S2 G (Ddef η) j) z = Ddef η j l z :=
      hsolve j l z (by
        intro k
        show ‖z k‖ < G.e k
        rw [hGe]
        exact by simpa using hz k)
    have hbf : bmDefect χ η j l z = (χ z - 1) * η j l z + Ddef η j l z := by
      show (χ z - 1) * η j l z - ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j l m) z
        = (χ z - 1) * η j l z + Ddef η j l z
      rw [show Ddef η j l z = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j l m) z from rfl]
      ring
    have hcz : χ z = 1 := hχ_one z
      (fun i => le_of_lt (lt_trans (by simpa using hz i) (hρ'ρ'' i)))
    have hbr := hbmdef j l z
    rw [hbf, hcz] at hbr
    rw [hT2_apply η hV]
    show dbarCoord j (opFun η l) z - dbarCoord l (opFun η j) z = η j l z
    rw [show opFun η l = fun w => bmRow (fun i l' w => χ w * η i l' w) l w
          - TelTwoDF.S2 G (Ddef η) l w from rfl,
      show opFun η j = fun w => bmRow (fun i l' w => χ w * η i l' w) j w
          - TelTwoDF.S2 G (Ddef η) j w from rfl,
      dbarCoord_sub_local j (hdrow l) (hdS2 l), dbarCoord_sub_local l (hdrow j) (hdS2 j)]
    linear_combination hbr - hsol
  · -- clause (b)
    intro k η hη hanti hcl
    have hV : η ∈ V := by
      rw [hVmem]; intro i l
      exact ((hη i l).of_le (by simp)).contDiffOn
    have hχη_cd : ∀ i l, ContDiff ℝ (k + 1) (fun w => χ w * η i l w) := fun i l =>
      (hχ_sm.of_le (by simp)).mul (hη i l)
    have hbmH_cd : ∀ j kk l, ContDiff ℝ (k + 1) (bmH χ η j kk l) := by
      intro j kk l
      have hd : ∀ s : Fin n, ContDiff ℝ (k + 1) (dbarCoord s χ) := fun s =>
        (contDiff_dbarCoord_of_smooth_top hχ_sm s).of_le (by simp)
      show ContDiff ℝ (k + 1) (fun w => dbarCoord l χ w * η j kk w
        + dbarCoord j χ w * η kk l w - dbarCoord kk χ w * η j l w)
      exact (((hd l).mul (hη j kk)).add ((hd j).mul (hη kk l))).sub ((hd kk).mul (hη j l))
    have hDη_cd : ∀ i l, ContDiff ℝ (k + 1) (Ddef η i l) := by
      intro i l
      have h := (contDiff_const (c := -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))).mul
        (Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn (i := k + 1)
          (fun l' => hbmH_cd i l l') (fun l' => hbmH_cs_all η i l l'))
      have heq : (fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPotential (fun l' => bmH χ η i l l') y) = Ddef η i l := by
        funext y
        show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPotential (fun l' => bmH χ η i l l') y
            = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y
        rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
      rw [← heq]; exact h
    have hbrow_sm_all : ∀ j : Fin n,
        ContDiffOn ℝ (k + 1) (bmRow (fun i l w => χ w * η i l w) j) (polydisc 0 ρ') :=
      fun j => (contDiff_bmRow_of hn hχη_cd (fun i l => hχη_cs_all η i l) j).contDiffOn
    have hs2_sm_all : ∀ j : Fin n,
        ContDiffOn ℝ (k + 1) (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 ρ') := fun j => by
      have h := (hCSreg (k + 1) (Ddef η) hDη_cd).1 j
      rwa [hGe] at h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [hT2_apply η hV]
      rw [show opFun η j = fun w => bmRow (fun i l w => χ w * η i l w) j w
          - TelTwoDF.S2 G (Ddef η) j w from rfl]
      exact (hbrow_sm_all j).sub (hs2_sm_all j)
    · set S : ℝ≥0∞ := ∑ j, ∑ l, holderNorm k α (η j l) (polydisc 0 ρ) with hSdef
      have hrow : holderNorm (k + 1) α (bmRow (fun i l w => χ w * η i l w) j) (polydisc 0 ρ')
          ≤ ENNReal.ofReal (Crow k) * S := by
        have h := hCrowbd k η hη j
        rwa [← hSdef] at h
      have hinner : ∀ i l : Fin n, holderNorm (k + 1) α (Ddef η i l) (polydisc 0 G.b)
          ≤ ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S := by
        intro i l
        have hmono : holderNorm (k + 1) α (Ddef η i l) (polydisc 0 G.b)
            ≤ holderNorm (k + 1) α (Ddef η i l) (polydisc 0 ρ'') :=
          holderNorm_mono_set (isOpen_polydisc 0 ρ'') (isOpen_polydisc 0 G.b)
            (fun z hz j => lt_of_lt_of_le (hz j) (le_of_lt (hGbg j))) (k + 1) α (Ddef η i l)
        have hcont : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞)
            (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y)
            (polydisc 0 ρ'') := by
          have heq : (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y)
              = fun y => Work.CR.Flat.Cauchy.bmPotential (fun l' => bmH χ η i l l') y := by
            funext y; exact (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot _ y).symm
          rw [heq]
          exact (Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn (i := k + 1)
            (fun l' => hbmH_cd i l l') (fun l' => hbmH_cs_all η i l l')).contDiffOn
        have hsm : holderNorm (k + 1) α (Ddef η i l) (polydisc 0 ρ'')
            = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
              * holderNorm (k + 1) α
                  (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y)
                  (polydisc 0 ρ'') := by
          have hD_eq : Ddef η i l = ((-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) : ℂ)
              • (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y) := by
            funext y; rfl
          rw [hD_eq, Work.CR.Flat.Holder.holderNorm_smul _ hcont
            (isOpen_polydisc 0 ρ'').uniqueDiffOn, norm_neg]
        have hpot := hCpotbd k η hη i l
        rw [← hSdef] at hpot
        calc holderNorm (k + 1) α (Ddef η i l) (polydisc 0 G.b)
            ≤ holderNorm (k + 1) α (Ddef η i l) (polydisc 0 ρ'') := hmono
          _ = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
              * holderNorm (k + 1) α
                  (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y)
                  (polydisc 0 ρ'') := hsm
          _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
              * (ENNReal.ofReal (Cpot k) * S) :=
              mul_le_mul_of_nonneg_left hpot bot_le
          _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S :=
            ofReal_mul_mul_assoc (a := ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖) (b := Cpot k)
              (norm_nonneg _) (le_of_lt (hCpotpos k)) S
      have hs2bd : holderNorm (k + 1) α (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 ρ')
          ≤ ENNReal.ofReal (CS (k + 1) * ((n : ℝ) * (n : ℝ)
              * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))) * S := by
        have hsum1 : (∑ _i : Fin n, ∑ _l : Fin n,
              (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S))
            = ENNReal.ofReal ((n : ℝ) * (n : ℝ)
                * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)) * S := by
          have h1 : (∑ _i : Fin n, ∑ _l : Fin n,
                (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S))
              = (n : ℝ≥0∞) * ((n : ℝ≥0∞)
                  * (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)
                      * S)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            rw [nsmul_eq_mul, nsmul_eq_mul]
          rw [h1, ← ENNReal.ofReal_natCast]
          rw [ofReal_mul_mul_assoc (a := (n : ℝ)) (b := (n : ℝ)) (Nat.cast_nonneg n)
            (Nat.cast_nonneg n)
            (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S)]
          exact ofReal_mul_mul_assoc (a := (n : ℝ) * (n : ℝ))
            (b := ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)
            (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n))
            (mul_nonneg (norm_nonneg _) (le_of_lt (hCpotpos k))) S
        calc holderNorm (k + 1) α (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 ρ')
            = holderNorm (k + 1) α (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 G.e) := by rw [hGe]
          _ ≤ ENNReal.ofReal (CS (k + 1))
              * ∑ i, ∑ l, holderNorm (k + 1) α (Ddef η i l) (polydisc 0 G.b) :=
                (hCSreg (k + 1) (Ddef η) hDη_cd).2 j
          _ ≤ ENNReal.ofReal (CS (k + 1))
              * ∑ i : Fin n, ∑ l : Fin n,
                  (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S) :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
                  Finset.sum_le_sum fun l _ => hinner i l) bot_le
          _ = ENNReal.ofReal (CS (k + 1))
              * (ENNReal.ofReal ((n : ℝ) * (n : ℝ)
                  * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)) * S) := by rw [hsum1]
          _ = ENNReal.ofReal (CS (k + 1) * ((n : ℝ) * (n : ℝ)
              * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))) * S :=
            ofReal_mul_mul_assoc (a := CS (k + 1))
              (b := (n : ℝ) * (n : ℝ) * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))
              (le_of_lt (hCSpos (k + 1)))
              (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n))
                (mul_nonneg (norm_nonneg _) (le_of_lt (hCpotpos k)))) S
      have hsub := holderNorm_sub_le (k := k + 1) (α := α) (hbrow_sm_all j) (hs2_sm_all j)
        (isOpen_polydisc 0 ρ').uniqueDiffOn
      calc holderNorm (k + 1) α (T2 η j) (polydisc 0 ρ')
          = holderNorm (k + 1) α (fun w => bmRow (fun i l w => χ w * η i l w) j w
              - TelTwoDF.S2 G (Ddef η) j w) (polydisc 0 ρ') := by
            rw [hT2_apply η hV]
            rw [show opFun η j = fun w => bmRow (fun i l w => χ w * η i l w) j w
                - TelTwoDF.S2 G (Ddef η) j w from rfl]
        _ ≤ holderNorm (k + 1) α (bmRow (fun i l w => χ w * η i l w) j) (polydisc 0 ρ')
            + holderNorm (k + 1) α (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 ρ') := hsub
        _ ≤ ENNReal.ofReal (Crow k) * S
            + ENNReal.ofReal (CS (k + 1) * ((n : ℝ) * (n : ℝ)
                * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))) * S :=
              add_le_add hrow hs2bd
        _ = ENNReal.ofReal (Crow k + CS (k + 1) * ((n : ℝ) * (n : ℝ)
              * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))) * S := by
            have hq : (0 : ℝ) ≤ CS (k + 1) * ((n : ℝ) * (n : ℝ)
                * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)) :=
              mul_nonneg (le_of_lt (hCSpos (k + 1)))
                (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n))
                  (mul_nonneg (norm_nonneg ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
                    (le_of_lt (hCpotpos k))))
            rw [← add_mul, ← ENNReal.ofReal_add (q := CS (k + 1) * ((n : ℝ) * (n : ℝ)
                * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))) (le_of_lt (hCrowpos k)) hq]
  · -- clause (c)
    intro η hη hanti hcl
    have hV : η ∈ V := by rw [hVmem]; intro i l; exact (hη i l).of_le (by simp)
    have hχη_sm : ∀ i l, ContDiff ℝ (⊤ : ℕ∞) (fun w => χ w * η i l w) := fun i l =>
      contDiff_mul_of_contDiffOnFK hρ'''ρ (⊤ : ℕ∞) hχ_sm (hη i l) hχ_zero
    have hbmH_sm : ∀ j kk l, ContDiff ℝ (⊤ : ℕ∞) (bmH χ η j kk l) := by
      intro j kk l
      show ContDiff ℝ (⊤ : ℕ∞) (fun w => dbarCoord l χ w * η j kk w
        + dbarCoord j χ w * η kk l w - dbarCoord kk χ w * η j l w)
      exact (((contDiff_mul_of_contDiffOnFK hρ'''ρ (⊤ : ℕ∞)
            (contDiff_dbarCoord_of_smooth_top hχ_sm l) (hη j kk) (hχdbar_zero l)).add
          (contDiff_mul_of_contDiffOnFK hρ'''ρ (⊤ : ℕ∞)
            (contDiff_dbarCoord_of_smooth_top hχ_sm j) (hη kk l) (hχdbar_zero j))).sub
        (contDiff_mul_of_contDiffOnFK hρ'''ρ (⊤ : ℕ∞)
          (contDiff_dbarCoord_of_smooth_top hχ_sm kk) (hη j l) (hχdbar_zero kk)))
    have hDη_sm : ∀ i l, ContDiff ℝ (⊤ : ℕ∞) (Ddef η i l) := by
      intro i l
      have h := (contDiff_const (c := -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))).mul
        (contDiff_bmPot_top hn (fun l' => hbmH_sm i l l') (fun l' => hbmH_cs_all η i l l'))
      have heq : (Ddef η i l) = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y := rfl
      rw [heq]; exact h
    intro j
    have hbrow_sm : ContDiffOn ℝ (⊤ : ℕ∞) (bmRow (fun i l w => χ w * η i l w) j)
        (polydisc 0 ρ') :=
      (contDiff_bmRow_top hn hχη_sm (fun i l => hχη_cs_all η i l) j).contDiffOn
    have hs2_sm : ContDiffOn ℝ (⊤ : ℕ∞) (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 ρ') := by
      have h := hCSsm (Ddef η) hDη_sm j
      rwa [hGe] at h
    rw [hT2_apply η hV]
    rw [show opFun η j = fun w => bmRow (fun i l w => χ w * η i l w) j w
        - TelTwoDF.S2 G (Ddef η) j w from rfl]
    exact hbrow_sm.sub hs2_sm

end

end Work.NN.Core


noncomputable section

set_option maxHeartbeats 1000000

open scoped NNReal ENNReal ContDiff Topology
open Set Filter
open Work.CR.Flat
open Work.CR.Flat.Holder

namespace Work.NN.Core

variable {n : ℕ}

/-! ## The `(1,0)`-derivative: the calculus needed for the product rule -/

private lemma dCoord_add (j : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dCoord j (u + v) z = dCoord j u z + dCoord j v z := by
  have hfd : fderiv ℝ (fun w => (u + v) w) z = fderiv ℝ u z + fderiv ℝ v z := by
    rw [fderiv_add hu hv]
  simp only [dCoord, hfd, add_apply]
  ring

private lemma dCoord_sub (j : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dCoord j (u - v) z = dCoord j u z - dCoord j v z := by
  have hfd : fderiv ℝ (fun w => (u - v) w) z = fderiv ℝ u z - fderiv ℝ v z := by
    rw [fderiv_sub hu hv]
  simp only [dCoord, hfd, sub_apply]
  ring

private lemma dCoord_mul (j : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dCoord j (u * v) z = dCoord j u z * v z + u z * dCoord j v z := by
  have hfg : fderiv ℝ (u * v) z = u z • fderiv ℝ v z + v z • fderiv ℝ u z := by
    have h := (hu.hasFDerivAt.mul hv.hasFDerivAt).fderiv
    simpa using h
  rw [dCoord, hfg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [dCoord, dCoord]
  ring

/-! ## The derivative loss for `∂_j` -/

/-- `∂_j w` is globally `C^m` whenever `w` is globally `C^{m+1}`, and its `C^{m,α}`-norm on
`Set.univ` is at most the `C^{m+1,α}`-norm of `w`. -/
private lemma holderNorm_dCoord_le {α : ℝ} (j : Fin n) {m : ℕ} {w : (Fin n → ℂ) → ℂ}
    (hw : ContDiff ℝ (m + 1) w) :
    ContDiff ℝ m (fun z => dCoord j w z) ∧
      holderNorm m α (fun z => dCoord j w z) Set.univ
        ≤ holderNorm (m + 1) α w Set.univ := by
  have hfun : (fun z => dCoord j w z) = dCoordLin j ∘ (fderiv ℝ w) :=
    funext fun z => congrFun (dCoord_eq_comp j w) z
  have hm : ((m : ℕ) : WithTop ℕ∞) + 1 ≤ (((m + 1 : ℕ)) : WithTop ℕ∞) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  constructor
  · rw [hfun]
    exact (dCoordLin j).contDiff.comp (hw.fderiv_right (m := m) hm)
  · rw [hfun]
    exact holderNorm_comp_fderiv_le m α isOpen_univ hw.contDiffOn (dCoordLin j)
      (norm_dCoordLin_le j)

/-- If `g` is `C¹` and vanishes off the open polydisc `polydisc 0 ρ`, then `∂_j g` vanishes
there too. -/
private lemma dCoord_eq_zero_of_vanishing {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ 1 g) (hg0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → g z = 0) (k : Fin n) :
    ∀ z, (∃ j, ρ j ≤ ‖z j‖) → dCoord k g z = 0 := by
  intro z hz
  have h := fderiv_eq_zero_of_vanishing_off_polydisc (n := n) hρ hg hg0 z hz
  simp [dCoord, h]

/-- `∂_j v` is `C^N` on the polydisc whenever `v` is `C^{N+1}` there. -/
private lemma dCoord_contDiffOn {ρ : Fin n → ℝ} {N : ℕ} {v : (Fin n → ℂ) → ℂ}
    (hv : ContDiffOn ℝ (((N + 1 : ℕ)) : ℕ∞) v (Work.CR.Flat.polydisc 0 ρ)) (j : Fin n) :
    ContDiffOn ℝ ((N : ℕ) : ℕ∞) (fun z => dCoord j v z) (Work.CR.Flat.polydisc 0 ρ) := by
  have hsub : ((N : ℕ) : WithTop ℕ∞) + 1 ≤ (((N + 1 : ℕ)) : WithTop ℕ∞) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfd : ContDiffOn ℝ ((N : ℕ) : ℕ∞) (fun z => fderiv ℝ v z)
      (Work.CR.Flat.polydisc 0 ρ) := hv.fderiv_of_isOpen (isOpen_polydisc 0 ρ) hsub
  have hcomp : ContDiffOn ℝ ((N : ℕ) : ℕ∞) (fun z => dCoordLin j (fderiv ℝ v z))
      (Work.CR.Flat.polydisc 0 ρ) := (dCoordLin j).contDiff.comp_contDiffOn hfd
  have hfun : (fun z => dCoord j v z) = fun z => dCoordLin j (fderiv ℝ v z) :=
    funext fun z => congrFun (dCoord_eq_comp j v) z
  rw [hfun]
  exact hcomp

/-- **The datum estimate.**  For `b` smooth with support contained in the open polydisc and `v` of
private class `C^{N+1}` on the polydisc with finite `C^{N+1,α}`-norm, the `(0,1)`-form `∑_j b l j ∂_j v` is
globally `C^N`, and its `C^{N,α}`-norm on all of `ℂⁿ` is bounded by the `C^{N+1,α}`-norms of the
coefficients and of `v`. -/
private theorem holderNorm_datum_le {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : Fin n → Fin n → (Fin n → ℂ) → ℂ) (v : (Fin n → ℂ) → ℂ),
      (∀ l j, ContDiff ℝ ⊤ (b l j)) → (∀ l j, HasCompactSupport (b l j)) →
      (∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
      ContDiffOn ℝ (((N + 1 : ℕ)) : ℕ∞) v (Work.CR.Flat.polydisc 0 ρ) →
      Work.CR.Flat.holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤ →
      ∀ l, ContDiff ℝ N (fun y => ∑ j, b l j y * dCoord j v y) ∧
        holderNorm N α (fun y => ∑ j, b l j y * dCoord j v y) Set.univ
          ≤ ENNReal.ofReal C * (∑ j, holderNorm (N + 1) α (b l j) Set.univ)
              * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ) := by
  obtain ⟨Cw, hCwpos, hCw⟩ := exists_holderNorm_wirtinger_le (n := n) (k := N) (α := α)
    (Ω := Work.CR.Flat.polydisc 0 ρ) (isOpen_polydisc 0 ρ)
  obtain ⟨Cf, hCfpos, hCf⟩ := flatMulNorm (n := n) (α := α) hα0 hα1 hρ N
  refine ⟨Cf * Cw + 1, by positivity, ?_⟩
  intro b v hb hbcs hbsupp hv hvf l
  have hbvan : ∀ j z, (∃ i, ρ i ≤ ‖z i‖) → b l j z = 0 := by
    intro j z hz
    by_contra hc
    obtain ⟨i, hi⟩ := hz
    have h := (Work.CR.Flat.mem_polydisc.mp (hbsupp l j z hc)) i
    simp only [Pi.zero_apply, sub_zero] at h
    exact absurd h (not_lt.mpr hi)
  have hdv_cont : ∀ j, ContDiffOn ℝ ((N : ℕ) : ℕ∞) (fun z => dCoord j v z)
      (Work.CR.Flat.polydisc 0 ρ) := fun j => dCoord_contDiffOn (n := n) hv j
  have hdv_norm : ∀ j, holderNorm N α (fun z => dCoord j v z) (Work.CR.Flat.polydisc 0 ρ)
      ≤ ENNReal.ofReal Cw * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ) :=
    fun j => (hCw v hv j).2
  have hdv_fin : ∀ j, holderNorm N α (fun z => dCoord j v z)
        (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvf) (hdv_norm j)
  have hterm_smooth : ∀ j, ContDiff ℝ N (fun y => b l j y * dCoord j v y) := fun j =>
    flatMulSharp (n := n) hρ (hb l j) (fun z hz => hbvan j z hz) (hdv_cont j) (hdv_fin j)
  have hterm_norm : ∀ j, holderNorm N α (fun y => b l j y * dCoord j v y) Set.univ
      ≤ ENNReal.ofReal Cf * holderNorm N α (b l j) Set.univ
          * holderNorm N α (fun z => dCoord j v z) (Work.CR.Flat.polydisc 0 ρ) := fun j =>
    hCf (b l j) (fun z => dCoord j v z) (hb l j) (fun z hz => hbvan j z hz) (hdv_cont j)
      (hdv_fin j) (hterm_smooth j)
  constructor
  · exact ContDiff.sum fun j _ => hterm_smooth j
  · have hsum : holderNorm N α (fun y => ∑ j, b l j y * dCoord j v y) Set.univ
        ≤ ∑ j, holderNorm N α (fun y => b l j y * dCoord j v y) Set.univ := by
      have h := holderNorm_sum_le (s := (Finset.univ : Finset (Fin n))) (k := N) (α := α)
        (g := fun j y => b l j y * dCoord j v y) (Ω := Set.univ)
        (fun j _ => (hterm_smooth j).contDiffOn) uniqueDiffOn_univ
      simpa using h
    refine hsum.trans ?_
    have hstep : ∑ j, holderNorm N α (fun y => b l j y * dCoord j v y) Set.univ
        ≤ ∑ j, ENNReal.ofReal Cf * holderNorm N α (b l j) Set.univ
            * (ENNReal.ofReal Cw * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ)) := by
      refine Finset.sum_le_sum fun j _ => ?_
      calc holderNorm N α (fun y => b l j y * dCoord j v y) Set.univ
          ≤ ENNReal.ofReal Cf * holderNorm N α (b l j) Set.univ
              * holderNorm N α (fun z => dCoord j v z) (Work.CR.Flat.polydisc 0 ρ) :=
            hterm_norm j
        _ ≤ ENNReal.ofReal Cf * holderNorm N α (b l j) Set.univ
              * (ENNReal.ofReal Cw * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ)) :=
            mul_le_mul_of_nonneg_left (hdv_norm j) bot_le
    refine hstep.trans ?_
    have hmono : ∑ j, holderNorm N α (b l j) Set.univ
        ≤ ∑ j, holderNorm (N + 1) α (b l j) Set.univ :=
      Finset.sum_le_sum fun j _ => holderNorm_mono_k (Nat.le_succ N) α (b l j) Set.univ
    have hfirst : (∑ j, ENNReal.ofReal Cf * holderNorm N α (b l j) Set.univ
            * (ENNReal.ofReal Cw * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ)))
        = (ENNReal.ofReal Cf * ENNReal.ofReal Cw
              * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
            * ∑ j, holderNorm N α (b l j) Set.univ := by
      rw [← Finset.sum_mul]
      rw [show (∑ j, ENNReal.ofReal Cf * holderNorm N α (b l j) Set.univ)
            = ENNReal.ofReal Cf * ∑ j, holderNorm N α (b l j) Set.univ from by
          rw [Finset.mul_sum]]
      ac_rfl
    rw [hfirst]
    have hsecond : (ENNReal.ofReal Cf * ENNReal.ofReal Cw
            * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
          * ∑ j, holderNorm N α (b l j) Set.univ
        ≤ (ENNReal.ofReal (Cf * Cw + 1)
            * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
          * ∑ j, holderNorm N α (b l j) Set.univ := by
      have h : ENNReal.ofReal Cf * ENNReal.ofReal Cw ≤ ENNReal.ofReal (Cf * Cw + 1) := by
        rw [← ENNReal.ofReal_mul hCfpos.le]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h bot_le) bot_le
    refine hsecond.trans ?_
    calc (ENNReal.ofReal (Cf * Cw + 1)
            * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
          * ∑ j, holderNorm N α (b l j) Set.univ
        ≤ (ENNReal.ofReal (Cf * Cw + 1)
            * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
          * ∑ j, holderNorm (N + 1) α (b l j) Set.univ :=
          mul_le_mul_of_nonneg_left hmono bot_le
      _ = ENNReal.ofReal (Cf * Cw + 1) * (∑ j, holderNorm (N + 1) α (b l j) Set.univ)
            * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ) := by ac_rfl

/-- **The iteration estimate.**  For `b` smooth with support in the open polydisc and `v` of class
`C^{N+1}` on the polydisc with finite `C^{N+1,α}`-norm, the potential of the datum
`∑_j b l j ∂_j v` is `C^{N+1}` on the polydisc, with a `C^{N+1,α}`-norm bounded by
`C · (∑_{l,j} ‖b l j‖_{N+1,α}) · ‖v‖_{N+1,α}`. -/
private theorem iterate_estimate {ρ : Fin n → ℝ} (hn : 0 < n) (hρ : ∀ j, 0 < ρ j) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : Fin n → Fin n → (Fin n → ℂ) → ℂ) (v : (Fin n → ℂ) → ℂ),
      (∀ l j, ContDiff ℝ ⊤ (b l j)) → (∀ l j, HasCompactSupport (b l j)) →
      (∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
      (∀ l j, Work.CR.Flat.holderNorm (N + 1) α (b l j) Set.univ < ⊤) →
      ContDiffOn ℝ (((N + 1 : ℕ)) : ℕ∞) v (Work.CR.Flat.polydisc 0 ρ) →
      Work.CR.Flat.holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤ →
      ContDiffOn ℝ (((N + 1 : ℕ)) : ℕ∞) (fun z => Work.CR.Flat.Cauchy.bmPotential
            (fun l y => ∑ j, b l j y * dCoord j v y) z) (Work.CR.Flat.polydisc 0 ρ) ∧
      holderNorm (N + 1) α (fun z => Work.CR.Flat.Cauchy.bmPotential
            (fun l y => ∑ j, b l j y * dCoord j v y) z) (Work.CR.Flat.polydisc 0 ρ)
        ≤ ENNReal.ofReal C * (∑ l, ∑ j, holderNorm (N + 1) α (b l j) Set.univ)
            * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ) := by
  obtain ⟨Cd, hCdpos, hdatum⟩ := holderNorm_datum_le (n := n) hρ hα0 (le_of_lt hα1) N
  obtain ⟨Cg, hCgpos, hgain⟩ := bmPotential_gain (n := n) hn hα0 hα1 hρ N
  refine ⟨Cg * Cd + 1, by positivity, ?_⟩
  intro b v hb hbcs hbsupp hbfin hv hvf
  have hd := fun l => hdatum b v hb hbcs hbsupp hv hvf l
  have hdc : ∀ l, ContDiff ℝ N (fun y => ∑ j, b l j y * dCoord j v y) := fun l => (hd l).1
  have hdn : ∀ l, holderNorm N α (fun y => ∑ j, b l j y * dCoord j v y) Set.univ
      ≤ ENNReal.ofReal Cd * (∑ j, holderNorm (N + 1) α (b l j) Set.univ)
          * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ) := fun l => (hd l).2
  have hdfin : ∀ l, holderNorm N α (fun y => ∑ j, b l j y * dCoord j v y) Set.univ < ⊤ := by
    intro l
    refine lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top ?_ (hdn l))
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) hvf
    exact ENNReal.sum_ne_top.mpr fun j _ => ne_of_lt (hbfin l j)
  have hGsupp : ∀ l z, (∃ i, ρ i ≤ ‖z i‖) → (∑ j, b l j z * dCoord j v z) = 0 := by
    intro l z hz
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show b l j z = 0 from by
      by_contra hc
      obtain ⟨i, hi⟩ := hz
      have h := (Work.CR.Flat.mem_polydisc.mp (hbsupp l j z hc)) i
      simp only [Pi.zero_apply, sub_zero] at h
      exact absurd h (not_lt.mpr hi), zero_mul]
  have hGcs : ∀ l, HasCompactSupport (fun y => ∑ j, b l j y * dCoord j v y) := fun l =>
    Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0) (r := fun j => 2 * ρ j)
      (fun j => by linarith [hρ j]) (fun z hz => by
        obtain ⟨k, hk⟩ := hz
        have hk' : ρ k ≤ ‖z k‖ := by
          have : (2 * ρ k) / 2 = ρ k := by ring
          rw [this] at hk
          simpa using hk
        exact hGsupp l z ⟨k, hk'⟩)
  obtain ⟨hcont, hbound⟩ := hgain (fun l y => ∑ j, b l j y * dCoord j v y) hdc hGcs hdfin hGsupp
  refine ⟨hcont, ?_⟩
  have hstep : ∑ l, holderNorm N α (fun y => ∑ j, b l j y * dCoord j v y) Set.univ
      ≤ ∑ l, ENNReal.ofReal Cd * (∑ j, holderNorm (N + 1) α (b l j) Set.univ)
          * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ) :=
    Finset.sum_le_sum fun l _ => hdn l
  have hfirst : (∑ l, ENNReal.ofReal Cd * (∑ j, holderNorm (N + 1) α (b l j) Set.univ)
          * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
      = (ENNReal.ofReal Cd * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
          * ∑ l, ∑ j, holderNorm (N + 1) α (b l j) Set.univ := by
    rw [Finset.sum_congr rfl (fun l _ => show
      ENNReal.ofReal Cd * (∑ j, holderNorm (N + 1) α (b l j) Set.univ)
          * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ)
        = (ENNReal.ofReal Cd * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
            * (∑ j, holderNorm (N + 1) α (b l j) Set.univ) from by ac_rfl), ← Finset.mul_sum]
  calc holderNorm (N + 1) α (fun z => Work.CR.Flat.Cauchy.bmPotential
          (fun l y => ∑ j, b l j y * dCoord j v y) z) (Work.CR.Flat.polydisc 0 ρ)
      ≤ ENNReal.ofReal Cg * ∑ l, holderNorm N α (fun y => ∑ j, b l j y * dCoord j v y) Set.univ :=
        hbound
    _ ≤ ENNReal.ofReal Cg * ((ENNReal.ofReal Cd
            * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
            * ∑ l, ∑ j, holderNorm (N + 1) α (b l j) Set.univ) := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        rw [← hfirst]
        exact hstep
    _ ≤ ENNReal.ofReal (Cg * Cd + 1) * (∑ l, ∑ j, holderNorm (N + 1) α (b l j) Set.univ)
          * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ) := by
        have hle : ENNReal.ofReal Cg * ENNReal.ofReal Cd
            ≤ ENNReal.ofReal (Cg * Cd + 1) := by
          rw [← ENNReal.ofReal_mul hCgpos.le]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        have h1 : ENNReal.ofReal Cg * ((ENNReal.ofReal Cd
              * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
              * ∑ l, ∑ j, holderNorm (N + 1) α (b l j) Set.univ)
            = (ENNReal.ofReal Cg * ENNReal.ofReal Cd
                * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
              * ∑ l, ∑ j, holderNorm (N + 1) α (b l j) Set.univ := by ac_rfl
        rw [h1]
        calc (ENNReal.ofReal Cg * ENNReal.ofReal Cd
                * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
              * ∑ l, ∑ j, holderNorm (N + 1) α (b l j) Set.univ
            ≤ (ENNReal.ofReal (Cg * Cd + 1)
                * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ))
              * ∑ l, ∑ j, holderNorm (N + 1) α (b l j) Set.univ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle bot_le) bot_le
          _ = ENNReal.ofReal (Cg * Cd + 1)
                * (∑ l, ∑ j, holderNorm (N + 1) α (b l j) Set.univ)
              * holderNorm (N + 1) α v (Work.CR.Flat.polydisc 0 ρ) := by ac_rfl


/-! ## The datum is continuous, and the potential is linear in the datum -/

/-- A uniform bound for `∂_j v` on the polydisc, from the finiteness of the `C^{1,α}`-norm. -/
private lemma dCoord_bound_on_polydisc {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {α : ℝ} (hα0 : 0 < α)
    {v : (Fin n → ℂ) → ℂ} (hv : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ))
    (hvf : Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ) < ⊤) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j y, y ∈ Work.CR.Flat.polydisc 0 ρ → ‖dCoord j v y‖ ≤ M := by
  obtain ⟨C, hCpos, hC⟩ := exists_holderNorm_wirtinger_le (n := n) (k := 0) (α := α)
    (Ω := Work.CR.Flat.polydisc 0 ρ) (isOpen_polydisc 0 ρ)
  refine ⟨∑ j, (holderNorm 0 α (fun z => dCoord j v z) (Work.CR.Flat.polydisc 0 ρ)).toReal,
    Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg, fun j y hy => ?_⟩
  have hfin : holderNorm 0 α (fun z => dCoord j v z) (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hvf)) (hC v hv j).2
  have h0 : ENNReal.ofReal ‖dCoord j v y‖
      ≤ iterDerivNorm 0 (fun z => dCoord j v z) (Work.CR.Flat.polydisc 0 ρ) := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    exact le_iSup₂_of_le y hy le_rfl
  have h1 : ENNReal.ofReal ‖dCoord j v y‖
      ≤ holderNorm 0 α (fun z => dCoord j v z) (Work.CR.Flat.polydisc 0 ρ) :=
    le_trans h0 (iterDerivNorm_le_holderNorm 0 α _ _ (Nat.zero_le 0))
  have h2 : ‖dCoord j v y‖
      ≤ (holderNorm 0 α (fun z => dCoord j v z) (Work.CR.Flat.polydisc 0 ρ)).toReal := by
    refine (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp ?_
    rw [ENNReal.ofReal_toReal hfin]
    exact h1
  exact h2.trans (Finset.single_le_sum
    (f := fun i => (holderNorm 0 α (fun z => dCoord i v z) (Work.CR.Flat.polydisc 0 ρ)).toReal)
    (fun i _ => ENNReal.toReal_nonneg) (Finset.mem_univ j))

/-- The datum vanishes off the polydisc whenever the coefficients do. -/
private lemma beltramiDatum_vanishing {ρ : Fin n → ℝ} {b : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hbsupp : ∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    (l : Fin n) (v : (Fin n → ℂ) → ℂ) :
    ∀ z, (∃ i, ρ i ≤ ‖z i‖) → (∑ j, b l j z * dCoord j v z) = 0 := by
  intro z hz
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show b l j z = 0 from by
    by_contra hc
    obtain ⟨i, hi⟩ := hz
    have h := (Work.CR.Flat.mem_polydisc.mp (hbsupp l j z hc)) i
    simp only [Pi.zero_apply, sub_zero] at h
    exact absurd h (not_lt.mpr hi), zero_mul]

/-- The datum `∑_j b l j ∂_j v` is continuous (the coefficients vanish off the polydisc). -/
private lemma continuous_beltramiDatum {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {α : ℝ} (hα0 : 0 < α)
    {b : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hb : ∀ l j, ContDiff ℝ ⊤ (b l j))
    (hbsupp : ∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {v : (Fin n → ℂ) → ℂ} (hv : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ))
    (hvf : Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ) < ⊤) (l : Fin n) :
    Continuous (fun y => ∑ j, b l j y * dCoord j v y) := by
  obtain ⟨M, hM0, hM⟩ := dCoord_bound_on_polydisc (n := n) hρ hα0 hv hvf
  have hbcont : ∀ j, Continuous (b l j) := fun j => (hb l j).continuous
  have hbound : ∀ y, ‖∑ j, b l j y * dCoord j v y‖ ≤ (∑ j, ‖b l j y‖) * M := by
    intro y
    by_cases hy : y ∈ Work.CR.Flat.polydisc 0 ρ
    · calc ‖∑ j, b l j y * dCoord j v y‖ ≤ ∑ j, ‖b l j y * dCoord j v y‖ := norm_sum_le _ _
        _ = ∑ j, ‖b l j y‖ * ‖dCoord j v y‖ := by
            exact Finset.sum_congr rfl fun j _ => norm_mul _ _
        _ ≤ ∑ j, ‖b l j y‖ * M :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hM j y hy) (norm_nonneg _)
        _ = (∑ j, ‖b l j y‖) * M := by rw [Finset.sum_mul]
    · have hzero : ∀ j, b l j y = 0 := fun j => by
        by_contra hc
        exact hy (hbsupp l j y hc)
      simp only [hzero, zero_mul, Finset.sum_const_zero, norm_zero]
      positivity
  rw [continuous_iff_continuousAt]
  intro y₀
  by_cases hy₀ : y₀ ∈ Work.CR.Flat.polydisc 0 ρ
  · have hcontOn : ContinuousOn (fun y => ∑ j, b l j y * dCoord j v y)
        (Work.CR.Flat.polydisc 0 ρ) := by
      refine continuousOn_finsetSum _ fun j _ => ?_
      exact (hbcont j).continuousOn.mul (dCoord_contDiffOn (n := n) (N := 0) hv j).continuousOn
    exact hcontOn.continuousAt ((isOpen_polydisc 0 ρ).mem_nhds hy₀)
  · have hb0 : ∀ j, b l j y₀ = 0 := fun j => by
      by_contra hc
      exact hy₀ (hbsupp l j y₀ hc)
    have hlim : Filter.Tendsto (fun y => (∑ j, ‖b l j y‖) * M) (𝓝 y₀) (𝓝 0) := by
      have h1 : Filter.Tendsto (fun y => ∑ j, ‖b l j y‖) (𝓝 y₀) (𝓝 (∑ j, ‖b l j y₀‖)) :=
        tendsto_finsetSum _ fun j _ => ((hbcont j).continuousAt).norm
      have hconst : Filter.Tendsto (fun _ : Fin n → ℂ => M) (𝓝 y₀) (𝓝 M) := tendsto_const_nhds
      have h2 := h1.mul hconst
      have h3 : (∑ j, ‖b l j y₀‖) = 0 := by simp [hb0]
      simpa [h3] using h2
    have hzero : (∑ j, b l j y₀ * dCoord j v y₀) = 0 := by simp [hb0]
    rw [ContinuousAt, hzero]
    exact squeeze_zero_norm' (Filter.Eventually.of_forall hbound) hlim

/-! ## Linearity of the potential in the datum -/

private lemma bmPotential_add_of_cont {n : ℕ} (hn : 0 < n) {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j))
    (hfs : ∀ j, HasCompactSupport (f j)) (hgs : ∀ j, HasCompactSupport (g j)) :
    Work.CR.Flat.Cauchy.bmPotential (f + g)
      = Work.CR.Flat.Cauchy.bmPotential f + Work.CR.Flat.Cauchy.bmPotential g := by
  funext z
  simp only [Pi.add_apply]
  rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot, Work.CR.Flat.Cauchy.bmPotential_eq_bmPot,
    Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
  simpa using congrFun (Work.NN.Core.bmPot_add_of_cont hn hf hg hfs hgs) z

private lemma bmPotential_add_of_cont_apply {n : ℕ} (hn : 0 < n) {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j))
    (hfs : ∀ j, HasCompactSupport (f j)) (hgs : ∀ j, HasCompactSupport (g j))
    (z : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.bmPotential (f + g) z
      = Work.CR.Flat.Cauchy.bmPotential f z + Work.CR.Flat.Cauchy.bmPotential g z := by
  simpa only [Pi.add_apply] using congrFun (bmPotential_add_of_cont hn hf hg hfs hgs) z

private lemma bmPotential_neg_of_cont {n : ℕ} {g : Fin n → (Fin n → ℂ) → ℂ} :
    Work.CR.Flat.Cauchy.bmPotential (fun j y => - g j y)
      = - Work.CR.Flat.Cauchy.bmPotential g := by
  funext z
  simp only [Pi.neg_apply]
  rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot, Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
  have h := congrFun (Work.NN.Core.bmPot_smul_of_cont g (-1 : ℝ)) z
  simpa only [neg_one_smul, Pi.neg_apply] using h

private lemma bmPotential_sub_of_cont {n : ℕ} (hn : 0 < n) {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j))
    (hfs : ∀ j, HasCompactSupport (f j)) (hgs : ∀ j, HasCompactSupport (g j)) :
    Work.CR.Flat.Cauchy.bmPotential (f - g)
      = Work.CR.Flat.Cauchy.bmPotential f - Work.CR.Flat.Cauchy.bmPotential g := by
  have h1 : (f - g) = f + (fun j y => - g j y) := by
    funext j y; simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [h1]
  have h2 := bmPotential_add_of_cont (n := n) hn (f := f) (g := fun j y => - g j y)
    hf (fun j => (hg j).neg) hfs (fun j => (hgs j).neg)
  rw [h2, bmPotential_neg_of_cont]
  funext z
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
  ring

private lemma bmPotential_sub_of_cont_apply {n : ℕ} (hn : 0 < n) {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j))
    (hfs : ∀ j, HasCompactSupport (f j)) (hgs : ∀ j, HasCompactSupport (g j))
    (z : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.bmPotential (f - g) z
      = Work.CR.Flat.Cauchy.bmPotential f z - Work.CR.Flat.Cauchy.bmPotential g z := by
  simpa only [Pi.sub_apply] using congrFun (bmPotential_sub_of_cont hn hf hg hfs hgs) z

/-! ## The Beltrami operator and its linearity -/

/-- The Beltrami operator `v ↦ bmPotential (∑_j b l j ∂_j v)`. -/
private def beltramiOp (b : Fin n → Fin n → (Fin n → ℂ) → ℂ) (v : (Fin n → ℂ) → ℂ) :
    (Fin n → ℂ) → ℂ :=
  fun z => Work.CR.Flat.Cauchy.bmPotential (fun l y => ∑ j, b l j y * dCoord j v y) z

private lemma beltramiOp_zero (b : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    beltramiOp b 0 = 0 := by
  have h0 : (fun l y => ∑ j, b l j y * dCoord j (0 : (Fin n → ℂ) → ℂ) y) = 0 := by
    funext l y
    refine Finset.sum_eq_zero fun j _ => ?_
    have hd : dCoord j (0 : (Fin n → ℂ) → ℂ) y = 0 := by simp [dCoord]
    rw [hd, mul_zero]
  funext z
  rw [beltramiOp, h0]
  simp [Work.CR.Flat.Cauchy.bmPotential]

/-- The datum is additive in the function (on functions that are `C¹` on the polydisc). -/
private lemma beltramiDatum_add {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {b : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hbsupp : ∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {v w : (Fin n → ℂ) → ℂ}
    (hv : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ))
    (hw : ContDiffOn ℝ 1 w (Work.CR.Flat.polydisc 0 ρ)) :
    (fun l y => ∑ j, b l j y * dCoord j (v + w) y)
      = (fun l y => ∑ j, b l j y * dCoord j v y)
        + (fun l y => ∑ j, b l j y * dCoord j w y) := by
  funext l y
  simp only [Pi.add_apply]
  by_cases hy : y ∈ Work.CR.Flat.polydisc 0 ρ
  · have hv' : DifferentiableAt ℝ v y :=
      ((hv y hy).differentiableWithinAt one_ne_zero).differentiableAt
        ((isOpen_polydisc 0 ρ).mem_nhds hy)
    have hw' : DifferentiableAt ℝ w y :=
      ((hw y hy).differentiableWithinAt one_ne_zero).differentiableAt
        ((isOpen_polydisc 0 ρ).mem_nhds hy)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dCoord_add j v w y hv' hw']
    ring
  · have hzero : ∀ j, b l j y = 0 := fun j => by
      by_contra hc
      exact hy (hbsupp l j y hc)
    simp only [hzero, zero_mul, Finset.sum_const_zero, add_zero]

/-- The datum is subtractive in the function. -/
private lemma beltramiDatum_sub {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {b : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hbsupp : ∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {v w : (Fin n → ℂ) → ℂ}
    (hv : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ))
    (hw : ContDiffOn ℝ 1 w (Work.CR.Flat.polydisc 0 ρ)) :
    (fun l y => ∑ j, b l j y * dCoord j (v - w) y)
      = (fun l y => ∑ j, b l j y * dCoord j v y)
        - (fun l y => ∑ j, b l j y * dCoord j w y) := by
  funext l y
  simp only [Pi.sub_apply]
  by_cases hy : y ∈ Work.CR.Flat.polydisc 0 ρ
  · have hv' : DifferentiableAt ℝ v y :=
      ((hv y hy).differentiableWithinAt one_ne_zero).differentiableAt
        ((isOpen_polydisc 0 ρ).mem_nhds hy)
    have hw' : DifferentiableAt ℝ w y :=
      ((hw y hy).differentiableWithinAt one_ne_zero).differentiableAt
        ((isOpen_polydisc 0 ρ).mem_nhds hy)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dCoord_sub j v w y hv' hw']
    ring
  · have hzero : ∀ j, b l j y = 0 := fun j => by
      by_contra hc
      exact hy (hbsupp l j y hc)
    simp only [hzero, zero_mul, Finset.sum_const_zero, sub_zero]

private lemma beltramiOp_add {ρ : Fin n → ℝ} (hn : 0 < n) (hρ : ∀ j, 0 < ρ j) {α : ℝ} (hα0 : 0 < α)
    {b : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hb : ∀ l j, ContDiff ℝ ⊤ (b l j))
    (hbsupp : ∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {v w : (Fin n → ℂ) → ℂ}
    (hv : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ))
    (hw : ContDiffOn ℝ 1 w (Work.CR.Flat.polydisc 0 ρ))
    (hvf : Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ) < ⊤)
    (hwf : Work.CR.Flat.holderNorm 1 α w (Work.CR.Flat.polydisc 0 ρ) < ⊤) :
    beltramiOp b (v + w) = beltramiOp b v + beltramiOp b w := by
  funext z
  have hdat := beltramiDatum_add (n := n) hρ hbsupp hv hw
  have hcs : ∀ m, HasCompactSupport
      (fun y => ∑ j, b m j y * dCoord j v y) := fun m =>
    Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0) (r := fun j => 2 * ρ j)
      (fun j => by linarith [hρ j]) (fun z hz => by
        obtain ⟨k, hk⟩ := hz
        have hk' : ρ k ≤ ‖z k‖ := by
          have h2 : (2 * ρ k) / 2 = ρ k := by ring
          rw [h2] at hk
          simpa using hk
        exact beltramiDatum_vanishing hbsupp m v z ⟨k, hk'⟩)
  have hcs' : ∀ m, HasCompactSupport (fun y => ∑ j, b m j y * dCoord j w y) := fun m =>
    Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0) (r := fun j => 2 * ρ j)
      (fun j => by linarith [hρ j]) (fun z hz => by
        obtain ⟨k, hk⟩ := hz
        have hk' : ρ k ≤ ‖z k‖ := by
          have h2 : (2 * ρ k) / 2 = ρ k := by ring
          rw [h2] at hk
          simpa using hk
        exact beltramiDatum_vanishing hbsupp m w z ⟨k, hk'⟩)
  have hcontv : ∀ m, Continuous (fun y => ∑ j, b m j y * dCoord j v y) := fun m =>
    continuous_beltramiDatum (n := n) hρ hα0 hb hbsupp hv hvf m
  have hcontw : ∀ m, Continuous (fun y => ∑ j, b m j y * dCoord j w y) := fun m =>
    continuous_beltramiDatum (n := n) hρ hα0 hb hbsupp hw hwf m
  simp only [beltramiOp, Pi.add_apply]
  rw [hdat]
  exact bmPotential_add_of_cont_apply hn hcontv hcontw hcs hcs' z

private lemma beltramiOp_sub {ρ : Fin n → ℝ} (hn : 0 < n) (hρ : ∀ j, 0 < ρ j) {α : ℝ} (hα0 : 0 < α)
    {b : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hb : ∀ l j, ContDiff ℝ ⊤ (b l j))
    (hbsupp : ∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {v w : (Fin n → ℂ) → ℂ}
    (hv : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ))
    (hw : ContDiffOn ℝ 1 w (Work.CR.Flat.polydisc 0 ρ))
    (hvf : Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ) < ⊤)
    (hwf : Work.CR.Flat.holderNorm 1 α w (Work.CR.Flat.polydisc 0 ρ) < ⊤) :
    beltramiOp b (v - w) = beltramiOp b v - beltramiOp b w := by
  funext z
  have hdat := beltramiDatum_sub (n := n) hρ hbsupp hv hw
  have hcs : ∀ m, HasCompactSupport
      (fun y => ∑ j, b m j y * dCoord j v y) := fun m =>
    Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0) (r := fun j => 2 * ρ j)
      (fun j => by linarith [hρ j]) (fun z hz => by
        obtain ⟨k, hk⟩ := hz
        have hk' : ρ k ≤ ‖z k‖ := by
          have h2 : (2 * ρ k) / 2 = ρ k := by ring
          rw [h2] at hk
          simpa using hk
        exact beltramiDatum_vanishing hbsupp m v z ⟨k, hk'⟩)
  have hcs' : ∀ m, HasCompactSupport (fun y => ∑ j, b m j y * dCoord j w y) := fun m =>
    Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0) (r := fun j => 2 * ρ j)
      (fun j => by linarith [hρ j]) (fun z hz => by
        obtain ⟨k, hk⟩ := hz
        have hk' : ρ k ≤ ‖z k‖ := by
          have h2 : (2 * ρ k) / 2 = ρ k := by ring
          rw [h2] at hk
          simpa using hk
        exact beltramiDatum_vanishing hbsupp m w z ⟨k, hk'⟩)
  have hcontv : ∀ m, Continuous (fun y => ∑ j, b m j y * dCoord j v y) := fun m =>
    continuous_beltramiDatum (n := n) hρ hα0 hb hbsupp hv hvf m
  have hcontw : ∀ m, Continuous (fun y => ∑ j, b m j y * dCoord j w y) := fun m =>
    continuous_beltramiDatum (n := n) hρ hα0 hb hbsupp hw hwf m
  simp only [beltramiOp, Pi.sub_apply]
  rw [hdat]
  exact bmPotential_sub_of_cont_apply hn hcontv hcontw hcs hcs' z


/-! ## Arithmetic and series lemmas used by the Neumann iteration -/

/-- The partial geometric sums `Σ_{i<M} q^i` are at most `2` when `0 ≤ q ≤ 1/2`. -/
private lemma geom_sum_le_two {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (M : ℕ) :
    ∑ i ∈ Finset.range M, q ^ i ≤ 2 := by
  have hmain : ∀ M : ℕ, ∑ i ∈ Finset.range M, q ^ i ≤ 2 - 2 * q ^ M := by
    intro M
    induction M with
    | zero =>
      rw [Finset.sum_range_zero, pow_zero]
      norm_num
    | succ M ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hM0 : 0 ≤ q ^ M := pow_nonneg hq0 M
      have h2q : 2 * q ≤ 1 := by linarith
      have hthis : q ^ M * (2 * q) ≤ q ^ M * 1 := mul_le_mul_of_nonneg_left h2q hM0
      nlinarith [ih, hthis]
  have hlast : 0 ≤ q ^ M := pow_nonneg hq0 M
  linarith [hmain M]

/-- The tail `Σ_{m ≤ i < M} q^i` of a geometric series with `0 ≤ q ≤ 1/2`. -/
private lemma geom_tail_le_two {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (m M : ℕ) :
    ∑ i ∈ Finset.Ico m M, q ^ i ≤ 2 * q ^ m := by
  rw [Finset.sum_Ico_eq_sum_range]
  calc ∑ k ∈ Finset.range (M - m), q ^ (m + k)
      = ∑ k ∈ Finset.range (M - m), q ^ m * q ^ k :=
        Finset.sum_congr rfl fun k _ => pow_add q m k
    _ = q ^ m * ∑ k ∈ Finset.range (M - m), q ^ k := (Finset.mul_sum _ _ _).symm
    _ ≤ q ^ m * 2 := mul_le_mul_of_nonneg_left (geom_sum_le_two hq0 hq _) (pow_nonneg hq0 m)
    _ = 2 * q ^ m := by ring

/-- The `ENNReal` bookkeeping for the geometric decay of the iterates. -/
private lemma ofReal_iter_le {A D q : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (h : A * D ≤ q) (m : ℕ) :
    ENNReal.ofReal A * ENNReal.ofReal D * ENNReal.ofReal (q ^ m)
      ≤ ENNReal.ofReal (q ^ (m + 1)) := by
  have hq0 : 0 ≤ q := le_trans (mul_nonneg hA hD) h
  have hpow : 0 ≤ q ^ m := pow_nonneg hq0 m
  calc ENNReal.ofReal A * ENNReal.ofReal D * ENNReal.ofReal (q ^ m)
      = ENNReal.ofReal (A * D) * ENNReal.ofReal (q ^ m) := by rw [ENNReal.ofReal_mul hA]
    _ = ENNReal.ofReal (A * D * q ^ m) := by rw [ENNReal.ofReal_mul (mul_nonneg hA hD)]
    _ ≤ ENNReal.ofReal (q ^ (m + 1)) := ENNReal.ofReal_le_ofReal (by
          rw [pow_succ]
          calc A * D * q ^ m ≤ q * q ^ m := mul_le_mul_of_nonneg_right h hpow
            _ = q ^ m * q := by ring)

/-- The `n²` coefficient functions of a Beltrami datum have total `C^{m,α}`-norm bounded by
`n²δ`, as soon as their `C^{k,α}`-norms are bounded by `δ` and `m ≤ k`. -/
private lemma sum_sum_holderNorm_le {n : ℕ} {α δ : ℝ} (hδ : 0 ≤ δ) {m k : ℕ} (hmk : m ≤ k)
    {b : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hbδ : ∀ l j, holderNorm k α (b l j) Set.univ ≤ ENNReal.ofReal δ) :
    (∑ l, ∑ j, holderNorm m α (b l j) Set.univ)
      ≤ ENNReal.ofReal ((n : ℝ) * (n : ℝ) * δ) := by
  have h1 : ∀ l, (∑ j, holderNorm m α (b l j) Set.univ)
      ≤ ENNReal.ofReal ((n : ℝ) * δ) := by
    intro l
    calc (∑ j, holderNorm m α (b l j) Set.univ)
        ≤ ∑ _j : Fin n, ENNReal.ofReal δ :=
          Finset.sum_le_sum fun j _ =>
            (holderNorm_mono_k hmk α (b l j) Set.univ).trans (hbδ l j)
      _ = (Finset.univ : Finset (Fin n)).card • ENNReal.ofReal δ := Finset.sum_const _
      _ = (n : ℝ≥0∞) * ENNReal.ofReal δ := by
          rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal ((n : ℝ) * δ) := by
          rw [← ENNReal.ofReal_natCast n, ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  calc (∑ l, ∑ j, holderNorm m α (b l j) Set.univ)
      ≤ ∑ _l : Fin n, ENNReal.ofReal ((n : ℝ) * δ) := Finset.sum_le_sum fun l _ => h1 l
    _ = (Finset.univ : Finset (Fin n)).card • ENNReal.ofReal ((n : ℝ) * δ) := Finset.sum_const _
    _ = (n : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) * δ) := by
        rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * δ)) := by
        rw [← ENNReal.ofReal_natCast n]
        exact (ENNReal.ofReal_mul (p := (n : ℝ)) (q := (n : ℝ) * δ)
          (Nat.cast_nonneg n)).symm
    _ = ENNReal.ofReal ((n : ℝ) * (n : ℝ) * δ) := by
        congr 1
        ring

/-- The Beltrami operator depends only on the values of the function on the polydisc. -/
private lemma beltramiOp_congr {n : ℕ} {ρ : Fin n → ℝ} {b : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hbsupp : ∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {v w : (Fin n → ℂ) → ℂ} (hvw : EqOn v w (Work.CR.Flat.polydisc 0 ρ)) :
    beltramiOp b v = beltramiOp b w := by
  have hdata : (fun l y => ∑ j, b l j y * dCoord j v y)
      = (fun l y => ∑ j, b l j y * dCoord j w y) := by
    funext l y
    by_cases hy : y ∈ Work.CR.Flat.polydisc 0 ρ
    · have hfl : v =ᶠ[𝓝 y] w := by
        filter_upwards [(isOpen_polydisc (0 : Fin n → ℂ) ρ).mem_nhds hy] with z hz
        exact hvw hz
      have hfd : fderiv ℝ v y = fderiv ℝ w y := hfl.fderiv_eq
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show dCoord j v y = dCoordLin j (fderiv ℝ v y) from
            congrFun (dCoord_eq_comp j v) y,
          show dCoord j w y = dCoordLin j (fderiv ℝ w y) from
            congrFun (dCoord_eq_comp j w) y, hfd]
    · have hb : ∀ j, b l j y = 0 := fun j => by
        by_contra hc
        exact hy (hbsupp l j y hc)
      simp [hb]
  funext z
  simp only [beltramiOp]
  rw [hdata]

private theorem contDiffOn_of_beltrami_fixedPoint {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j)
    (hlt : ∀ j, ρ' j < ρ j) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (b : Fin n → Fin n → (Fin n → ℂ) → ℂ) (F u : (Fin n → ℂ) → ℂ),
        (∀ l j, ContDiff ℝ ⊤ (b l j)) →
        (∀ l j, HasCompactSupport (b l j)) →
        (∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        (∀ l j, Work.CR.Flat.holderNorm k α (b l j) Set.univ ≤ ENNReal.ofReal δ) →
        ContDiffOn ℝ (k : ℕ∞) F (Work.CR.Flat.polydisc 0 ρ) →
        Work.CR.Flat.holderNorm k α F (Work.CR.Flat.polydisc 0 ρ) < ⊤ →
        ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
        Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc 0 ρ) < ⊤ →
        (∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          u z = Work.CR.Flat.Cauchy.bmPotential
                  (fun l y => ∑ j, b l j y * Work.CR.Flat.dCoord j u y) z + F z) →
        ContDiffOn ℝ (k : ℕ∞) u (Work.CR.Flat.polydisc 0 ρ') ∧
          Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ')
            ≤ ENNReal.ofReal C
                * (1 + Work.CR.Flat.holderNorm k α F (Work.CR.Flat.polydisc 0 ρ)) := by
  classical
  obtain ⟨N, hNk⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
  subst hNk
  obtain ⟨C₁, hC₁pos, hiter₁⟩ := iterate_estimate (n := n) hn hρ hα0 hα1 0
  obtain ⟨C₂, hC₂pos, hiter₂⟩ := iterate_estimate (n := n) hn hρ hα0 hα1 N
  set M₀ : ℝ := (C₁ + C₂ + 1) * ((n : ℝ) * (n : ℝ) + 1) with hM₀def
  have hM₀pos : 0 < M₀ := by
    rw [hM₀def]
    have h1 : (0 : ℝ) < C₁ + C₂ + 1 := by linarith
    have h2 : (0 : ℝ) < (n : ℝ) * (n : ℝ) + 1 := by nlinarith [sq_nonneg (n : ℝ)]
    exact mul_pos h1 h2
  set δ : ℝ := 1 / (2 * M₀) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos one_pos (by linarith)
  have hM₀δ : M₀ * δ = 1 / 2 := by
    rw [hδdef]
    field_simp
  have hmul : ∀ c : ℝ, c ≤ C₁ + C₂ + 1 → c * ((n : ℝ) * (n : ℝ)) ≤ M₀ := by
    intro c hc
    rw [hM₀def]
    have hle2 : (0 : ℝ) ≤ (n : ℝ) * (n : ℝ) := mul_self_nonneg _
    have hle3 : (n : ℝ) * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) + 1 := by linarith
    exact mul_le_mul hc hle3 hle2 (by linarith)
  have hkey₁ : C₁ * ((n : ℝ) * (n : ℝ) * δ) ≤ 1 / 2 := by
    rw [show C₁ * ((n : ℝ) * (n : ℝ) * δ) = C₁ * ((n : ℝ) * (n : ℝ)) * δ by ring]
    calc C₁ * ((n : ℝ) * (n : ℝ)) * δ ≤ M₀ * δ :=
          mul_le_mul_of_nonneg_right (hmul C₁ (by linarith)) hδpos.le
      _ = 1 / 2 := hM₀δ
  have hkey₂ : C₂ * ((n : ℝ) * (n : ℝ) * δ) ≤ 1 / 2 := by
    rw [show C₂ * ((n : ℝ) * (n : ℝ) * δ) = C₂ * ((n : ℝ) * (n : ℝ)) * δ by ring]
    calc C₂ * ((n : ℝ) * (n : ℝ)) * δ ≤ M₀ * δ :=
          mul_le_mul_of_nonneg_right (hmul C₂ (by linarith)) hδpos.le
      _ = 1 / 2 := hM₀δ
  refine ⟨2, δ, by norm_num, hδpos, ?_⟩
  intro b F u hb hbcs hbsupp hbδ hF hFf hu huf heq
  have hPopen : IsOpen (polydisc (0 : Fin n → ℂ) ρ) := isOpen_polydisc 0 ρ
  have hP'open : IsOpen (polydisc (0 : Fin n → ℂ) ρ') := isOpen_polydisc 0 ρ'
  have hP'P : polydisc (0 : Fin n → ℂ) ρ' ⊆ polydisc (0 : Fin n → ℂ) ρ :=
    polydisc_mono (fun j => le_of_lt (hlt j))
  have huniq : UniqueDiffOn ℝ (polydisc (0 : Fin n → ℂ) ρ) := hPopen.uniqueDiffOn
  have huniq' : UniqueDiffOn ℝ (polydisc (0 : Fin n → ℂ) ρ') := hP'open.uniqueDiffOn
  have hF1 : ContDiffOn ℝ (1 : ℕ∞) F (polydisc (0 : Fin n → ℂ) ρ) :=
    hF.of_le (by exact_mod_cast (show (1 : ℕ) ≤ N + 1 by omega))
  have hF1f : holderNorm 1 α F (polydisc (0 : Fin n → ℂ) ρ) < ⊤ :=
    lt_of_le_of_lt (holderNorm_mono_k (show 1 ≤ N + 1 by omega) α F _) hFf
  have hb1 : ∀ l j, holderNorm 1 α (b l j) Set.univ < ⊤ := fun l j =>
    lt_of_le_of_lt
      ((holderNorm_mono_k (show 1 ≤ N + 1 by omega) α (b l j) Set.univ).trans (hbδ l j))
      ENNReal.ofReal_lt_top
  have hbk : ∀ l j, holderNorm (N + 1) α (b l j) Set.univ < ⊤ := fun l j =>
    lt_of_le_of_lt (hbδ l j) ENNReal.ofReal_lt_top
  have hbsum1 : (∑ l, ∑ j, holderNorm 1 α (b l j) Set.univ)
      ≤ ENNReal.ofReal ((n : ℝ) * (n : ℝ) * δ) :=
    sum_sum_holderNorm_le hδpos.le (show 1 ≤ N + 1 by omega) hbδ
  have hbsumk : (∑ l, ∑ j, holderNorm (N + 1) α (b l j) Set.univ)
      ≤ ENNReal.ofReal ((n : ℝ) * (n : ℝ) * δ) :=
    sum_sum_holderNorm_le hδpos.le le_rfl hbδ
  -- the Neumann iterates and their partial sums
  let w : ℕ → (Fin n → ℂ) → ℂ := fun m => (beltramiOp b)^[m] F
  have hw0 : w 0 = F := by
    show (beltramiOp b)^[0] F = F
    rw [Function.iterate_zero_apply]
  have hws : ∀ m, w (m + 1) = beltramiOp b (w m) := by
    intro m
    show (beltramiOp b)^[m + 1] F = beltramiOp b ((beltramiOp b)^[m] F)
    rw [Function.iterate_succ_apply']
  let A : ℕ → (Fin n → ℂ) → ℂ := fun M => fun z => ∑ i ∈ Finset.range M, w i z
  have hA0 : A 0 = 0 := by
    funext z
    show (∑ i ∈ Finset.range 0, w i z) = (0 : (Fin n → ℂ) → ℂ) z
    simp
  have hAs : ∀ M, A (M + 1) = A M + w M := by
    intro M
    funext z
    show (∑ i ∈ Finset.range (M + 1), w i z) = (∑ i ∈ Finset.range M, w i z) + w M z
    rw [Finset.sum_range_succ]
  -- the `C^{1,α}` iteration
  have hw1 : ∀ m, ContDiffOn ℝ (1 : ℕ∞) (w m) (polydisc (0 : Fin n → ℂ) ρ) ∧
      holderNorm 1 α (w m) (polydisc (0 : Fin n → ℂ) ρ)
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m)
            * holderNorm 1 α F (polydisc (0 : Fin n → ℂ) ρ) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · show ContDiffOn ℝ (1 : ℕ∞) F (polydisc (0 : Fin n → ℂ) ρ)
        exact hF1
      · show holderNorm 1 α F (polydisc (0 : Fin n → ℂ) ρ)
            ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ 0)
                * holderNorm 1 α F (polydisc (0 : Fin n → ℂ) ρ)
        simp
    | succ m ih =>
      obtain ⟨hcm, hbm⟩ := ih
      have hfin : holderNorm 1 α (w m) (polydisc (0 : Fin n → ℂ) ρ) < ⊤ :=
        lt_of_le_of_lt hbm (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF1f)
      obtain ⟨hc, hbd⟩ := hiter₁ b (w m) hb hbcs hbsupp hb1 hcm (ne_of_lt hfin)
      refine ⟨?_, ?_⟩
      · rw [hws m]
        exact hc
      · calc holderNorm 1 α (w (m + 1)) (polydisc (0 : Fin n → ℂ) ρ)
            = holderNorm 1 α (beltramiOp b (w m)) (polydisc (0 : Fin n → ℂ) ρ) := by
              rw [hws m]
          _ ≤ ENNReal.ofReal C₁ * (∑ l, ∑ j, holderNorm 1 α (b l j) Set.univ)
                * holderNorm 1 α (w m) (polydisc (0 : Fin n → ℂ) ρ) := hbd
          _ ≤ ENNReal.ofReal C₁ * ENNReal.ofReal ((n : ℝ) * (n : ℝ) * δ)
                * (ENNReal.ofReal ((1 / 2 : ℝ) ^ m)
                    * holderNorm 1 α F (polydisc (0 : Fin n → ℂ) ρ)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hbsum1 bot_le) hbm bot_le bot_le
          _ = (ENNReal.ofReal C₁ * ENNReal.ofReal ((n : ℝ) * (n : ℝ) * δ)
                * ENNReal.ofReal ((1 / 2 : ℝ) ^ m))
                * holderNorm 1 α F (polydisc (0 : Fin n → ℂ) ρ) := by ring
          _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (m + 1))
                * holderNorm 1 α F (polydisc (0 : Fin n → ℂ) ρ) :=
              mul_le_mul_of_nonneg_right
                (ofReal_iter_le hC₁pos.le (by positivity) hkey₁ m) bot_le
  -- the `C^{k,α}` iteration
  have hwk : ∀ m, ContDiffOn ℝ (((N + 1 : ℕ)) : ℕ∞) (w m) (polydisc (0 : Fin n → ℂ) ρ) ∧
      holderNorm (N + 1) α (w m) (polydisc (0 : Fin n → ℂ) ρ)
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m)
            * holderNorm (N + 1) α F (polydisc (0 : Fin n → ℂ) ρ) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · show ContDiffOn ℝ (((N + 1 : ℕ)) : ℕ∞) F (polydisc (0 : Fin n → ℂ) ρ)
        exact hF
      · show holderNorm (N + 1) α F (polydisc (0 : Fin n → ℂ) ρ)
            ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ 0)
                * holderNorm (N + 1) α F (polydisc (0 : Fin n → ℂ) ρ)
        simp
    | succ m ih =>
      obtain ⟨hcm, hbm⟩ := ih
      have hfin : holderNorm (N + 1) α (w m) (polydisc (0 : Fin n → ℂ) ρ) < ⊤ :=
        lt_of_le_of_lt hbm (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFf)
      obtain ⟨hc, hbd⟩ := hiter₂ b (w m) hb hbcs hbsupp hbk hcm (ne_of_lt hfin)
      refine ⟨?_, ?_⟩
      · rw [hws m]
        exact hc
      · calc holderNorm (N + 1) α (w (m + 1)) (polydisc (0 : Fin n → ℂ) ρ)
            = holderNorm (N + 1) α (beltramiOp b (w m)) (polydisc (0 : Fin n → ℂ) ρ) := by
              rw [hws m]
          _ ≤ ENNReal.ofReal C₂ * (∑ l, ∑ j, holderNorm (N + 1) α (b l j) Set.univ)
                * holderNorm (N + 1) α (w m) (polydisc (0 : Fin n → ℂ) ρ) := hbd
          _ ≤ ENNReal.ofReal C₂ * ENNReal.ofReal ((n : ℝ) * (n : ℝ) * δ)
                * (ENNReal.ofReal ((1 / 2 : ℝ) ^ m)
                    * holderNorm (N + 1) α F (polydisc (0 : Fin n → ℂ) ρ)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hbsumk bot_le) hbm bot_le bot_le
          _ = (ENNReal.ofReal C₂ * ENNReal.ofReal ((n : ℝ) * (n : ℝ) * δ)
                * ENNReal.ofReal ((1 / 2 : ℝ) ^ m))
                * holderNorm (N + 1) α F (polydisc (0 : Fin n → ℂ) ρ) := by ring
          _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (m + 1))
                * holderNorm (N + 1) α F (polydisc (0 : Fin n → ℂ) ρ) :=
              mul_le_mul_of_nonneg_right
                (ofReal_iter_le hC₂pos.le (by positivity) hkey₂ m) bot_le
  have hw1fin : ∀ m, holderNorm 1 α (w m) (polydisc (0 : Fin n → ℂ) ρ) < ⊤ := fun m =>
    lt_of_le_of_lt (hw1 m).2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF1f)
  have hwkfin : ∀ m, holderNorm (N + 1) α (w m) (polydisc (0 : Fin n → ℂ) ρ) < ⊤ := fun m =>
    lt_of_le_of_lt (hwk m).2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFf)
  have hAsmP : ∀ m, ContDiffOn ℝ (((N + 1 : ℕ)) : ℕ∞) (A m) (polydisc (0 : Fin n → ℂ) ρ) :=
    fun m => ContDiffOn.sum fun i _ => (hwk i).1
  have hA1mP : ∀ m, ContDiffOn ℝ (1 : ℕ∞) (A m) (polydisc (0 : Fin n → ℂ) ρ) :=
    fun m => ContDiffOn.sum fun i _ => (hw1 i).1
  have hA1fin : ∀ m, holderNorm 1 α (A m) (polydisc (0 : Fin n → ℂ) ρ) < ⊤ := fun m =>
    lt_of_le_of_lt (holderNorm_sum_le (Finset.range m) (fun i _ => (hw1 i).1) huniq)
      (ENNReal.sum_lt_top.mpr fun i _ => hw1fin i)
  set K : ℝ := (holderNorm (N + 1) α F (polydisc (0 : Fin n → ℂ) ρ)).toReal with hKdef
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hFi : holderNorm (N + 1) α F (polydisc (0 : Fin n → ℂ) ρ) = ENNReal.ofReal K := by
    rw [hKdef]
    exact (ENNReal.ofReal_toReal (ne_of_lt hFf)).symm
  -- the family is bounded on the smaller polydisc
  have hAbound : ∀ m, holderNorm (N + 1) α (A m) (polydisc (0 : Fin n → ℂ) ρ')
      ≤ ENNReal.ofReal (2 * (1 + K)) := by
    intro m
    have h1 : holderNorm (N + 1) α (A m) (polydisc (0 : Fin n → ℂ) ρ')
        ≤ holderNorm (N + 1) α (A m) (polydisc (0 : Fin n → ℂ) ρ) :=
      holderNorm_mono_set hPopen hP'open hP'P (N + 1) α (A m)
    have h2 : holderNorm (N + 1) α (A m) (polydisc (0 : Fin n → ℂ) ρ)
        ≤ ∑ i ∈ Finset.range m, ENNReal.ofReal ((1 / 2 : ℝ) ^ i) * ENNReal.ofReal K := by
      calc holderNorm (N + 1) α (A m) (polydisc (0 : Fin n → ℂ) ρ)
          ≤ ∑ i ∈ Finset.range m, holderNorm (N + 1) α (w i) (polydisc (0 : Fin n → ℂ) ρ) :=
            holderNorm_sum_le (Finset.range m) (fun i _ => (hwk i).1) huniq
        _ ≤ ∑ i ∈ Finset.range m, ENNReal.ofReal ((1 / 2 : ℝ) ^ i) * ENNReal.ofReal K := by
            refine Finset.sum_le_sum fun i _ => ?_
            calc holderNorm (N + 1) α (w i) (polydisc (0 : Fin n → ℂ) ρ)
                ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ i)
                    * holderNorm (N + 1) α F (polydisc (0 : Fin n → ℂ) ρ) := (hwk i).2
              _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ i) * ENNReal.ofReal K := by rw [hFi]
    have h3 : ∑ i ∈ Finset.range m, ENNReal.ofReal ((1 / 2 : ℝ) ^ i) * ENNReal.ofReal K
        = ENNReal.ofReal (∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i) * ENNReal.ofReal K := by
      rw [← Finset.sum_mul,
        ENNReal.ofReal_sum_of_nonneg (s := Finset.range m)
          (f := fun i => (1 / 2 : ℝ) ^ i) (fun i _ => pow_nonneg (by norm_num) i)]
    have h4 : ENNReal.ofReal (∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i) * ENNReal.ofReal K
        ≤ ENNReal.ofReal (2 * (1 + K)) := by
      have hg : ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i ≤ 2 :=
        geom_sum_le_two (by norm_num) (by norm_num) m
      calc ENNReal.ofReal (∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i) * ENNReal.ofReal K
          ≤ ENNReal.ofReal 2 * ENNReal.ofReal K :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hg) bot_le
        _ = ENNReal.ofReal (2 * K) := (ENNReal.ofReal_mul (by norm_num)).symm
        _ ≤ ENNReal.ofReal (2 * (1 + K)) := ENNReal.ofReal_le_ofReal (by linarith)
    exact h1.trans (h2.trans (h3.le.trans h4))
  -- the tail of a difference of two partial sums
  have htail : ∀ a b : ℕ, holderNorm (N + 1) α (fun z => ∑ i ∈ Finset.Ico a b, w i z)
        (polydisc (0 : Fin n → ℂ) ρ')
      ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ a * K) := by
    intro a b
    calc holderNorm (N + 1) α (fun z => ∑ i ∈ Finset.Ico a b, w i z)
            (polydisc (0 : Fin n → ℂ) ρ')
        ≤ ∑ i ∈ Finset.Ico a b, holderNorm (N + 1) α (w i) (polydisc (0 : Fin n → ℂ) ρ') :=
          holderNorm_sum_le (Finset.Ico a b) (fun i _ => (hwk i).1.mono hP'P) huniq'
      _ ≤ ∑ i ∈ Finset.Ico a b, ENNReal.ofReal ((1 / 2 : ℝ) ^ i * K) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc holderNorm (N + 1) α (w i) (polydisc (0 : Fin n → ℂ) ρ')
              ≤ holderNorm (N + 1) α (w i) (polydisc (0 : Fin n → ℂ) ρ) :=
                holderNorm_mono_set hPopen hP'open hP'P (N + 1) α (w i)
            _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ i)
                  * holderNorm (N + 1) α F (polydisc (0 : Fin n → ℂ) ρ) := (hwk i).2
            _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ i * K) := by
                rw [hFi, ENNReal.ofReal_mul (pow_nonneg (by norm_num) i)]
      _ = ∑ i ∈ Finset.Ico a b, ENNReal.ofReal ((1 / 2 : ℝ) ^ i) * ENNReal.ofReal K := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_mul (pow_nonneg (by norm_num) i)]
      _ = ENNReal.ofReal (∑ i ∈ Finset.Ico a b, (1 / 2 : ℝ) ^ i) * ENNReal.ofReal K := by
          rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (s := Finset.Ico a b)
            (f := fun i => (1 / 2 : ℝ) ^ i) (fun i _ => pow_nonneg (by norm_num) i)]
      _ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ a) * ENNReal.ofReal K :=
          mul_le_mul_of_nonneg_right
            (ENNReal.ofReal_le_ofReal (geom_tail_le_two (by norm_num) (by norm_num) a b)) bot_le
      _ = ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ a * K) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  -- Cauchyness of the partial sums
  have hcau : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m m' : ℕ, M ≤ m → M ≤ m' →
      holderNorm (N + 1) α (A m - A m') (polydisc (0 : Fin n → ℂ) ρ')
        ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨M, hMle⟩ : ∃ M : ℕ, 2 * (1 / 2 : ℝ) ^ M * K ≤ ε := by
      have ht : Tendsto (fun M : ℕ => 2 * ((1 / 2 : ℝ) ^ M) * K) atTop (𝓝 (2 * 0 * K)) :=
        Filter.Tendsto.mul_const K (Filter.Tendsto.const_mul 2
          (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
            (by norm_num) (by norm_num)))
      have hev : ∀ᶠ M in atTop, 2 * ((1 / 2 : ℝ) ^ M) * K < ε := by
        have hmem : Set.Iio ε ∈ 𝓝 (2 * 0 * K) := by
          rw [show (2 * 0 * K : ℝ) = 0 by ring]
          exact isOpen_Iio.mem_nhds hε
        exact ht.eventually hmem
      obtain ⟨M, hMs⟩ := Filter.eventually_atTop.mp hev
      exact ⟨M, le_of_lt (hMs M le_rfl)⟩
    refine ⟨M, fun m m' hm hm' => ?_⟩
    rcases le_total m m' with hle | hle
    · have hneg : A m - A m' = - (fun z => ∑ i ∈ Finset.Ico m m', w i z) := by
        funext z
        show (∑ i ∈ Finset.range m, w i z) - (∑ i ∈ Finset.range m', w i z)
            = -(∑ i ∈ Finset.Ico m m', w i z)
        rw [Finset.sum_Ico_eq_sub _ hle]
        ring
      have hsm : ContDiffOn ℝ (((N + 1 : ℕ)) : ℕ∞)
          (fun z => ∑ i ∈ Finset.Ico m m', w i z) (polydisc (0 : Fin n → ℂ) ρ') :=
        ContDiffOn.sum fun i _ => (hwk i).1.mono hP'P
      rw [hneg,
        holderNorm_neg (f := fun z => ∑ i ∈ Finset.Ico m m', w i z) hsm huniq']
      calc holderNorm (N + 1) α (fun z => ∑ i ∈ Finset.Ico m m', w i z)
              (polydisc (0 : Fin n → ℂ) ρ')
          ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ m * K) := htail m m'
        _ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ M * K) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hpow : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ M :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
            have hml := mul_le_mul_of_nonneg_right hpow hK0
            linarith
        _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hMle
    · have hpos : A m - A m' = fun z => ∑ i ∈ Finset.Ico m' m, w i z := by
        funext z
        show (∑ i ∈ Finset.range m, w i z) - (∑ i ∈ Finset.range m', w i z)
            = (∑ i ∈ Finset.Ico m' m, w i z)
        rw [Finset.sum_Ico_eq_sub _ hle]
      rw [hpos]
      calc holderNorm (N + 1) α (fun z => ∑ i ∈ Finset.Ico m' m, w i z)
              (polydisc (0 : Fin n → ℂ) ρ')
          ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ m' * K) := htail m' m
        _ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ M * K) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hpow : (1 / 2 : ℝ) ^ m' ≤ (1 / 2 : ℝ) ^ M :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hm'
            have hml := mul_le_mul_of_nonneg_right hpow hK0
            linarith
        _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hMle
  -- the fixed point identity in terms of the Beltrami operator
  have hPhiA : ∀ M, beltramiOp b (A M) = A (M + 1) - F := by
    intro M
    induction M with
    | zero =>
      rw [hA0, beltramiOp_zero, hAs 0, hA0, hw0]
      funext z
      show (0 : (Fin n → ℂ) → ℂ) z = ((0 + F) - F) z
      simp
    | succ M ih =>
      rw [hAs M,
        beltramiOp_add (v := A M) (w := w M) hn hρ hα0 hb hbsupp
          (hA1mP M) (hw1 M).1 (hA1fin M) (hw1fin M)]
      rw [ih, ← hws M, hAs (M + 1)]
      funext z
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
  -- the iterates of `u` under the Beltrami operator
  let vseq : ℕ → (Fin n → ℂ) → ℂ := fun M => (beltramiOp b)^[M] u
  have hvseq0 : vseq 0 = u := by
    show (beltramiOp b)^[0] u = u
    rw [Function.iterate_zero_apply]
  have hvseqs : ∀ M, vseq (M + 1) = beltramiOp b (vseq M) := by
    intro M
    show (beltramiOp b)^[M + 1] u = beltramiOp b ((beltramiOp b)^[M] u)
    rw [Function.iterate_succ_apply']
  have hvseqm : ∀ M, ContDiffOn ℝ (1 : ℕ∞) (vseq M) (polydisc (0 : Fin n → ℂ) ρ) ∧
      holderNorm 1 α (vseq M) (polydisc (0 : Fin n → ℂ) ρ)
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ M)
            * holderNorm 1 α u (polydisc (0 : Fin n → ℂ) ρ) := by
    intro M
    induction M with
    | zero =>
      refine ⟨?_, ?_⟩
      · show ContDiffOn ℝ (1 : ℕ∞) u (polydisc (0 : Fin n → ℂ) ρ)
        exact hu
      · show holderNorm 1 α u (polydisc (0 : Fin n → ℂ) ρ)
            ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ 0)
                * holderNorm 1 α u (polydisc (0 : Fin n → ℂ) ρ)
        simp
    | succ M ih =>
      obtain ⟨hcm, hbm⟩ := ih
      have hfin : holderNorm 1 α (vseq M) (polydisc (0 : Fin n → ℂ) ρ) < ⊤ :=
        lt_of_le_of_lt hbm (ENNReal.mul_lt_top ENNReal.ofReal_lt_top huf)
      obtain ⟨hc, hbd⟩ := hiter₁ b (vseq M) hb hbcs hbsupp hb1 hcm (ne_of_lt hfin)
      refine ⟨?_, ?_⟩
      · rw [hvseqs M]
        exact hc
      · calc holderNorm 1 α (vseq (M + 1)) (polydisc (0 : Fin n → ℂ) ρ)
            = holderNorm 1 α (beltramiOp b (vseq M)) (polydisc (0 : Fin n → ℂ) ρ) := by
              rw [hvseqs M]
          _ ≤ ENNReal.ofReal C₁ * (∑ l, ∑ j, holderNorm 1 α (b l j) Set.univ)
                * holderNorm 1 α (vseq M) (polydisc (0 : Fin n → ℂ) ρ) := hbd
          _ ≤ ENNReal.ofReal C₁ * ENNReal.ofReal ((n : ℝ) * (n : ℝ) * δ)
                * (ENNReal.ofReal ((1 / 2 : ℝ) ^ M)
                    * holderNorm 1 α u (polydisc (0 : Fin n → ℂ) ρ)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hbsum1 bot_le) hbm bot_le bot_le
          _ = (ENNReal.ofReal C₁ * ENNReal.ofReal ((n : ℝ) * (n : ℝ) * δ)
                * ENNReal.ofReal ((1 / 2 : ℝ) ^ M))
                * holderNorm 1 α u (polydisc (0 : Fin n → ℂ) ρ) := by ring
          _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (M + 1))
                * holderNorm 1 α u (polydisc (0 : Fin n → ℂ) ρ) :=
              mul_le_mul_of_nonneg_right
                (ofReal_iter_le hC₁pos.le (by positivity) hkey₁ M) bot_le
  -- on the polydisc, the iterates of `u` agree with the errors `u - A M`
  have hE : ∀ M, EqOn (vseq M) (u - A M) (polydisc (0 : Fin n → ℂ) ρ) := by
    intro M
    induction M with
    | zero =>
      rw [hvseq0, hA0]
      intro z hz
      simp
    | succ M ih =>
      intro z hz
      rw [hvseqs M]
      rw [beltramiOp_congr (b := b) hbsupp ih]
      rw [beltramiOp_sub (v := u) (w := A M) hn hρ hα0 hb hbsupp hu (hA1mP M) huf
        (hA1fin M)]
      rw [hPhiA M]
      have hez : u z = beltramiOp b u z + F z := by
        simpa only [beltramiOp] using heq z hz
      simp only [Pi.sub_apply]
      rw [hez]
      ring
  -- pointwise convergence
  set U : ℝ := (holderNorm 1 α u (polydisc (0 : Fin n → ℂ) ρ)).toReal with hUdef
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  have hUi : holderNorm 1 α u (polydisc (0 : Fin n → ℂ) ρ) = ENNReal.ofReal U := by
    rw [hUdef]
    exact (ENNReal.ofReal_toReal (ne_of_lt huf)).symm
  have hconv : ∀ z ∈ polydisc (0 : Fin n → ℂ) ρ', Tendsto (fun M => A M z) atTop (𝓝 (u z)) := by
    intro z hz'
    have hz : z ∈ polydisc (0 : Fin n → ℂ) ρ := hP'P hz'
    have hle : ∀ M, ‖u z - A M z‖ ≤ ((1 / 2 : ℝ) ^ M) * U := by
      intro M
      refine (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg (by norm_num) M) hU0)).mp ?_
      calc ENNReal.ofReal ‖u z - A M z‖ = ENNReal.ofReal ‖vseq M z‖ := by
            rw [show vseq M z = u z - A M z from hE M hz]
        _ ≤ holderNorm 1 α (vseq M) (polydisc (0 : Fin n → ℂ) ρ) :=
            norm_apply_le_holderNorm 1 α (vseq M) _ hz
        _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ M) * holderNorm 1 α u (polydisc (0 : Fin n → ℂ) ρ) :=
            (hvseqm M).2
        _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ M) * ENNReal.ofReal U := by rw [hUi]
        _ = ENNReal.ofReal (((1 / 2 : ℝ) ^ M) * U) :=
            (ENNReal.ofReal_mul (pow_nonneg (by norm_num) M)).symm
    have h0 : Tendsto (fun M : ℕ => ((1 / 2 : ℝ) ^ M) * U) atTop (𝓝 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
        (by norm_num) (by norm_num)
      simpa using Filter.Tendsto.mul_const U h
    have hz2 : Tendsto (fun M => u z - A M z) atTop (𝓝 0) := squeeze_zero_norm hle h0
    have h3 : Tendsto (fun M => u z - (u z - A M z)) atTop (𝓝 (u z - 0)) :=
      tendsto_const_nhds.sub hz2
    simpa using h3
  -- assembly
  have hAsmQ : ∀ m, ContDiffOn ℝ (((N + 1 : ℕ)) : ℕ∞) (A m) (polydisc (0 : Fin n → ℂ) ρ') :=
    fun m => (hAsmP m).mono hP'P
  obtain ⟨hbnd, hsm⟩ := holderNorm_le_of_tendsto (X := Fin n → ℂ) (k := N + 1) (α := α)
    (P := polydisc (0 : Fin n → ℂ) ρ') hP'open (C := 2 * (1 + K))
    (by positivity) (F := A) (v := u) hAsmQ hAbound hconv hcau
  have hCe : ENNReal.ofReal (2 * (1 + K))
      = ENNReal.ofReal 2 * (1 + holderNorm (N + 1) α F (polydisc (0 : Fin n → ℂ) ρ)) := by
    rw [hFi, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact ⟨hsm, hbnd.trans hCe.le⟩

end Work.NN.Core


namespace Work.NN.Core

set_option maxHeartbeats 1600000

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

noncomputable section

variable {n : ℕ}

/-! ## Auxiliary: the two-term Leibniz bound with an explicit constant -/

/-- The two-term Leibniz bound for the `C^{k,α}` norm of a product, with the constant
`(k+1)·2^{k+1}` made explicit (it is independent of the two functions). -/
private lemma holderNorm_mul_le_two_exp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {α : ℝ} {f g : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hg : ContDiffOn ℝ (k : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω)
    (hf' : Work.CR.Flat.holderNorm k α f Ω ≠ ⊤)
    (hg' : Work.CR.Flat.holderNorm k α g Ω ≠ ⊤) :
    Work.CR.Flat.holderNorm k α (fun x => f x * g x) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f Ω * Work.CR.Flat.holderNorm k α g Ω
        + ENNReal.ofReal (((k : ℝ) + 1) * (2 : ℝ) ^ (k + 1))
            * (Work.CR.Flat.holderNorm k α f Ω
                * Work.CR.Flat.holderNorm (k - 1) α g Ω) := by
  have hsum2 : (∑ i ∈ Finset.range (k + 1), (2 : ℝ≥0∞) ^ i)
      ≤ ENNReal.ofReal (((k : ℝ) + 1) * (2 : ℝ) ^ (k + 1)) := by
    rw [Work.CR.Flat.Holder.ofReal_const_eq]
    exact Work.CR.Flat.Holder.sum_pow_two_le k
  have hkg : Work.CR.Flat.holderNorm k α g Ω
      = ∑ i ∈ Finset.range (k + 1),
          (Work.CR.Flat.Holder.iDN i g Ω + Work.CR.Flat.Holder.hSN i α g Ω) := rfl
  rw [show Work.CR.Flat.holderNorm k α (fun x => f x * g x) Ω
      = ∑ i ∈ Finset.range (k + 1),
          (Work.CR.Flat.Holder.iDN i (fun x => f x * g x) Ω
            + Work.CR.Flat.Holder.hSN i α (fun x => f x * g x) Ω) from rfl]
  refine (Finset.sum_le_sum fun i hi =>
      Work.CR.Flat.Holder.iDN_add_hSN_mul_le_two (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        hf hg hΩ).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Work.CR.Flat.Holder.holderNorm_zero_eq α f Ω, ← hkg]
  exact add_le_add le_rfl (mul_le_mul_left hsum2 _)

/-! ## The flat two-term product bound in ambient norms -/

/-- If `b` is smooth and vanishes on the closed complement of the open polydisc `polydisc 0 ρ`,
and `h` is `C^{m,α}` on that polydisc with finite norm (so that `b h` is globally `C^m`), then

  `‖b·h‖_{C^{m,α}(ℂⁿ)} ≤ ‖b‖_{C^{0,α}(ℂⁿ)}·‖h‖_{C^{m,α}(P)} +
        (m+1)2^{m+1}·‖b‖_{C^{m,α}(ℂⁿ)}·‖h‖_{C^{m-1,α}(P)}`.

The point is the *explicit* coefficient `1 = ` of the top-order term `‖b‖_{0,α}·‖h‖_{m,α}`. -/
private lemma flatMul_two_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (m : ℕ) :
    ∀ (b h : (Fin n → ℂ) → ℂ),
      ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) b →
      (∀ z, (∃ j, ρ j ≤ ‖z j‖) → b z = 0) →
      ContDiffOn ℝ ((m : ℕ) : ℕ∞) h (Work.CR.Flat.polydisc 0 ρ) →
      Work.CR.Flat.holderNorm m α h (Work.CR.Flat.polydisc 0 ρ) < ⊤ →
      ContDiff ℝ ((m : ℕ) : ℕ∞) (fun z => b z * h z) →
      Work.CR.Flat.holderNorm m α (fun z => b z * h z) Set.univ
        ≤ Work.CR.Flat.holderNorm 0 α b Set.univ
            * Work.CR.Flat.holderNorm m α h (Work.CR.Flat.polydisc 0 ρ)
          + ENNReal.ofReal (((m : ℝ) + 1) * (2 : ℝ) ^ (m + 1))
            * (Work.CR.Flat.holderNorm m α b Set.univ
                * Work.CR.Flat.holderNorm (m - 1) α h (Work.CR.Flat.polydisc 0 ρ)) := by
  intro b h hbsm hbvan hhm hhfin hbhcd
  set P : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 ρ with hP
  have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hPud : UniqueDiffOn ℝ P := hPopen.uniqueDiffOn
  have hbm : ContDiffOn ℝ ((m : ℕ) : ℕ∞) b P := (hbsm.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hbcs : HasCompactSupport b :=
    Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0)
      (r := fun j => 2 * ρ j) (fun j => by linarith [hρ j]) (fun z hz => by
        obtain ⟨k, hk⟩ := hz
        have h2 : (2 * ρ k) / 2 = ρ k := by ring
        rw [h2] at hk
        refine hbvan z ⟨k, ?_⟩
        simpa using hk)
  have hbfin_univ : Work.CR.Flat.holderNorm m α b Set.univ ≠ ⊤ :=
    Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport' hα0.le hα1.le
      (hbsm.of_le (WithTop.coe_le_coe.mpr le_top)) hbcs
  have hbfin : Work.CR.Flat.holderNorm m α b P ≠ ⊤ :=
    ne_top_of_le_ne_top hbfin_univ
      (Work.CR.Flat.holderNorm_mono_set isOpen_univ hPopen (fun x _ => trivial) m α b)
  have hhfin' : Work.CR.Flat.holderNorm m α h P ≠ ⊤ := ne_of_lt hhfin
  have hleib := holderNorm_mul_le_two_exp (f := b) (g := h) (Ω := P) hbm hhm hPud hbfin hhfin'
  have hred : Work.CR.Flat.holderNorm m α (fun z => b z * h z) Set.univ
      ≤ Work.CR.Flat.holderNorm m α (fun z => b z * h z) P :=
    Work.NN.Core.holderNorm_univ_le_holderNorm_polydisc_of_contDiff_vanishing hα0 hρ hbhcd
      (fun z hz => by rw [hbvan z hz, zero_mul])
  refine hred.trans (hleib.trans ?_)
  have hb0mono : Work.CR.Flat.holderNorm 0 α b P ≤ Work.CR.Flat.holderNorm 0 α b Set.univ :=
    Work.CR.Flat.holderNorm_mono_set isOpen_univ hPopen (fun x _ => trivial) 0 α b
  have hbmmono : Work.CR.Flat.holderNorm m α b P ≤ Work.CR.Flat.holderNorm m α b Set.univ :=
    Work.CR.Flat.holderNorm_mono_set isOpen_univ hPopen (fun x _ => trivial) m α b
  calc Work.CR.Flat.holderNorm 0 α b P * Work.CR.Flat.holderNorm m α h P
        + ENNReal.ofReal (((m : ℝ) + 1) * (2 : ℝ) ^ (m + 1))
            * (Work.CR.Flat.holderNorm m α b P * Work.CR.Flat.holderNorm (m - 1) α h P)
      ≤ Work.CR.Flat.holderNorm 0 α b Set.univ * Work.CR.Flat.holderNorm m α h P
        + ENNReal.ofReal (((m : ℝ) + 1) * (2 : ℝ) ^ (m + 1))
            * (Work.CR.Flat.holderNorm m α b Set.univ * Work.CR.Flat.holderNorm (m - 1) α h P) := by
        gcongr
    _ = Work.CR.Flat.holderNorm 0 α b Set.univ * Work.CR.Flat.holderNorm m α h P
        + ENNReal.ofReal (((m : ℝ) + 1) * (2 : ℝ) ^ (m + 1))
            * (Work.CR.Flat.holderNorm m α b Set.univ
                * Work.CR.Flat.holderNorm (m - 1) α h (Work.CR.Flat.polydisc 0 ρ)) := rfl


/-! ## The summability of a linearly recursive sequence -/

/-- If a nonnegative real sequence `x` satisfies `x (m+1) ≤ θ * x m + K * y m` with
`0 ≤ θ < 1`, `K ≥ 0` and `y` nonnegative summable, then `x` is summable and bounded. -/
private lemma summable_of_linear_recursion {x y : ℕ → ℝ} {θ K : ℝ}
    (hx : ∀ m, 0 ≤ x m) (hy : ∀ m, 0 ≤ y m)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hK : 0 ≤ K)
    (hrec : ∀ m, x (m + 1) ≤ θ * x m + K * y m)
    (hys : Summable y) :
    Summable x ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ m, x m ≤ C := by
  set Y : ℝ := ∑' m, y m with hY
  have hY0 : 0 ≤ Y := tsum_nonneg hy
  have hden : 0 < 1 - θ := by linarith
  have hpartial : ∀ N, ∑ m ∈ Finset.range N, x m ≤ (x 0 + K * Y) / (1 - θ) := by
    intro N
    have hTmono : ∑ m ∈ Finset.range N, x m ≤ ∑ m ∈ Finset.range (N + 1), x m := by
      rw [Finset.sum_range_succ]
      exact le_add_of_nonneg_right (hx N)
    have hstep : ∑ m ∈ Finset.range (N + 1), x m
        ≤ x 0 + θ * (∑ m ∈ Finset.range N, x m) + K * Y := by
      rw [Finset.sum_range_succ']
      have hsum : ∑ k ∈ Finset.range N, x (k + 1)
          ≤ ∑ k ∈ Finset.range N, (θ * x k + K * y k) :=
        Finset.sum_le_sum fun k _ => hrec k
      have hyN : ∑ k ∈ Finset.range N, y k ≤ Y := hys.sum_le_tsum _ (fun i _ => hy i)
      calc ∑ k ∈ Finset.range N, x (k + 1) + x 0
          ≤ ∑ k ∈ Finset.range N, (θ * x k + K * y k) + x 0 := by linarith
        _ = θ * (∑ k ∈ Finset.range N, x k) + K * (∑ k ∈ Finset.range N, y k) + x 0 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ θ * (∑ k ∈ Finset.range N, x k) + K * Y + x 0 := by
            have := mul_le_mul_of_nonneg_left hyN hK
            linarith
        _ = x 0 + θ * (∑ k ∈ Finset.range N, x k) + K * Y := by ring
    have hkey : ∑ m ∈ Finset.range N, x m ≤ x 0 + θ * (∑ m ∈ Finset.range N, x m) + K * Y :=
      le_trans hTmono hstep
    have hTN0 : 0 ≤ ∑ m ∈ Finset.range N, x m := Finset.sum_nonneg fun i _ => hx i
    rw [le_div_iff₀ hden]
    have : (1 - θ) * (∑ m ∈ Finset.range N, x m)
        = ∑ m ∈ Finset.range N, x m - θ * (∑ m ∈ Finset.range N, x m) := by ring
    linarith
  refine ⟨summable_of_sum_range_le hx hpartial, ?_⟩
  refine ⟨(x 0 + K * Y) / (1 - θ),
    div_nonneg (add_nonneg (hx 0) (mul_nonneg hK hY0)) hden.le, fun m => ?_⟩
  have h1 : x m ≤ ∑ i ∈ Finset.range (m + 1), x i := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => hx i)
  exact le_trans h1 (hpartial (m + 1))


/-! ## The Wirtinger derivative bound with constant one -/

/-- `‖∂_j f‖_{C^{k,α}(Ω)} ≤ ‖f‖_{C^{k+1,α}(Ω)}` with constant `1` (uniform in `k`). -/
private lemma holderNorm_dCoord_le_one {m : ℕ} {α : ℝ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {f : (Fin n → ℂ) → ℂ} (hf : ContDiffOn ℝ (((m + 1 : ℕ)) : ℕ∞) f Ω) (j : Fin n) :
    Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j f z) Ω
      ≤ Work.CR.Flat.holderNorm (m + 1) α f Ω := by
  have hdc_eq : Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j f z) Ω
      = Work.CR.Flat.holderNorm m α (Work.NN.Core.dCoordLin j ∘ fderiv ℝ f) Ω :=
    Work.NN.Core.holderNorm_congr fun z _ => congrFun (Work.NN.Core.dCoord_eq_comp j f) z
  rw [hdc_eq]
  exact Work.NN.Core.holderNorm_comp_fderiv_le m α hΩ hf (Work.NN.Core.dCoordLin j)
    (Work.NN.Core.norm_dCoordLin_le j)


/-! ## Two elementary factorisations of `ℝ≥0∞`-sums -/

private lemma enat_sum_mul_le {ι : Type*} (s : Finset ι) (A B : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ i ∈ s, B i ≤ C) : ∑ i ∈ s, A i * B i ≤ (∑ i ∈ s, A i) * C := by
  calc ∑ i ∈ s, A i * B i ≤ ∑ i ∈ s, A i * C :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi) bot_le
    _ = (∑ i ∈ s, A i) * C := (Finset.sum_mul ..).symm

private lemma enat_sum_const_mul {ι : Type*} (s : Finset ι) (A : ι → ℝ≥0∞) (c C : ℝ≥0∞) :
    ∑ i ∈ s, c * (A i * C) = c * ((∑ i ∈ s, A i) * C) := by
  rw [Finset.sum_mul, Finset.mul_sum]


private lemma enat_ofReal_mul3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (a * b * c) = ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c := by
  rw [ENNReal.ofReal_mul (mul_nonneg ha hb), ENNReal.ofReal_mul ha]

/-! ## The one-step Beltrami estimate -/

/-- A single application of the Beltrami operator gains `C^L`-regularity with a top-order
coefficient proportional to the coefficients' `C^{0,α}`-norm through a constant `Cstar`
independent of `L`, all remaining terms being absorbed into a constant `M` (which may depend on
`L` and on `b`). -/
private lemma beltramiOp_step_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hn : 0 < n) :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ (b : Fin n → Fin n → (Fin n → ℂ) → ℂ),
        (∀ l j, ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (b l j)) →
        (∀ l j, HasCompactSupport (b l j)) →
        (∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ (v : (Fin n → ℂ) → ℂ),
          ContDiffOn ℝ ((L : ℕ) : ℕ∞) v (Work.CR.Flat.polydisc 0 ρ) →
          Work.CR.Flat.holderNorm L α v (Work.CR.Flat.polydisc 0 ρ) < ⊤ →
          ContDiffOn ℝ ((L : ℕ) : ℕ∞) (beltramiOp b v) (Work.CR.Flat.polydisc 0 ρ) ∧
          Work.CR.Flat.holderNorm L α (beltramiOp b v) (Work.CR.Flat.polydisc 0 ρ)
            ≤ ENNReal.ofReal Cstar
                * (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                * Work.CR.Flat.holderNorm L α v (Work.CR.Flat.polydisc 0 ρ)
              + ENNReal.ofReal M
                * Work.CR.Flat.holderNorm (L - 1) α v (Work.CR.Flat.polydisc 0 ρ) := by
  classical
  obtain ⟨Ctop, hCtpos, hCtop⟩ := bmPotential_top_gain_uniform (n := n) hn (c := 0)
    (r := fun j => 2 * ρ j) hα0 hα1 (fun j => by linarith [hρ j])
  obtain ⟨Cg0, hCg0pos, hCg0⟩ := bmPotential_gain (n := n) hn (α := α) hα0 hα1 hρ 0
  have hr2 : (fun j : Fin n => (2 * ρ j) / 2) = ρ := funext fun j => by ring
  refine ⟨5 * (Ctop + Cg0) + 1, by positivity, ?_⟩
  intro L hL b hbsm hbcs hbsupp
  have hvan2 : ∀ (l j : Fin n) (z : Fin n → ℂ), (∃ i, ρ i ≤ ‖z i‖) → b l j z = 0 := by
    intro l j z hz
    by_contra hc
    obtain ⟨i, hi⟩ := hz
    have hmem := (Work.CR.Flat.mem_polydisc.mp (hbsupp l j z hc)) i
    simp only [Pi.zero_apply, sub_zero] at hmem
    exact absurd hmem (not_lt.mpr hi)
  have hvan3 : ∀ (l j : Fin n) (z : Fin n → ℂ), (∃ i, (2 * ρ i) / 2 ≤ ‖z i - (0:Fin n → ℂ) i‖) → b l j z = 0 := by
    intro l j z hz
    obtain ⟨i, hi⟩ := hz
    refine hvan2 l j z ⟨i, ?_⟩
    rw [show (2 * ρ i) / 2 = ρ i from by ring] at hi
    simpa using hi
  set P : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 ρ with hP
  have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc 0 ρ
  obtain ⟨Cg1, hCg1pos, hCg1⟩ := bmPotential_gain (n := n) hn (α := α) hα0 hα1 hρ (L - 1)
  have hLower : ∃ CgL : ℝ, 0 ≤ CgL ∧ ∀ (g : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ (((L - 1 : ℕ)) : ℕ∞) (g j)) →
      (∀ j, HasCompactSupport (g j)) →
      (∀ j, Work.CR.Flat.holderNorm (L - 1) α (g j) Set.univ ≠ ⊤) →
      (∀ j z, (∃ i, ρ i ≤ ‖z i‖) → g j z = 0) →
      Work.CR.Flat.holderNorm (L - 1) α (Work.CR.Flat.Cauchy.bmPotential g) P
        ≤ ENNReal.ofReal CgL * ∑ j, Work.CR.Flat.holderNorm (L - 2) α (g j) Set.univ := by
    rcases eq_or_lt_of_le hL with h1 | h2
    · subst h1
      refine ⟨Cg0, hCg0pos.le, ?_⟩
      intro g hgm hgcs hgfin hgvan
      have hmono : Work.CR.Flat.holderNorm 0 α (Work.CR.Flat.Cauchy.bmPotential g) P
          ≤ Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential g) P :=
        Work.CR.Flat.holderNorm_mono_k (Nat.zero_le 1) α _ P
      exact hmono.trans (by simpa using (hCg0 g hgm hgcs (fun j => lt_top_iff_ne_top.mpr (hgfin j)) hgvan).2)
    · obtain ⟨Cg2, hCg2pos, hCg2⟩ := bmPotential_gain (n := n) hn (α := α) hα0 hα1 hρ (L - 2)
      refine ⟨Cg2, hCg2pos.le, ?_⟩
      intro g hgm hgcs hgfin hgvan
      have hsub : L - 2 ≤ L - 1 := Nat.sub_le_sub_left (show 1 ≤ 2 by norm_num) L
      have hgm' : ∀ j, ContDiff ℝ (((L - 2 : ℕ)) : ℕ∞) (g j) :=
        fun j => (hgm j).of_le (by exact_mod_cast hsub)
      have hgfin' : ∀ j, Work.CR.Flat.holderNorm (L - 2) α (g j) Set.univ < ⊤ :=
        fun j => lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_k hsub α (g j) Set.univ)
          (lt_top_iff_ne_top.mpr (hgfin j))
      have hcast : L - 2 + 1 = L - 1 := by omega
      have hres := (hCg2 g hgm' hgcs (hgfin') hgvan).2
      simpa [hcast] using hres
  obtain ⟨CgL, hCgL0, hCgL⟩ := hLower
  have hb_fin : ∀ (m : ℕ) (l j : Fin n),
      Work.CR.Flat.holderNorm m α (b l j) Set.univ ≠ ⊤ := by
    intro m l j
    exact Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport' hα0.le hα1.le
      ((hbsm l j).of_le (WithTop.coe_le_coe.mpr le_top)) (hbcs l j)
  set Bs : ℝ := (∑ l, ∑ j, Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ).toReal with hBsdef
  have hBsz : 0 ≤ Bs := ENNReal.toReal_nonneg
  have hBsfin : (∑ l, ∑ j, Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ) < ⊤ :=
    ENNReal.sum_lt_top.mpr fun l _ => ENNReal.sum_lt_top.mpr fun j _ =>
      lt_top_iff_ne_top.mpr (hb_fin (L - 1) l j)
  have hBseq : (∑ l, ∑ j, Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ)
      = ENNReal.ofReal Bs := by
    rw [hBsdef]
    exact (ENNReal.ofReal_toReal (ne_of_lt hBsfin)).symm
  set Cp : ℕ → ℝ := fun m => ((m : ℝ) + 1) * (2 : ℝ) ^ (m + 1) with hCpdef
  have hCpnn : ∀ m, 0 ≤ Cp m := fun m => by
    rw [hCpdef]
    exact mul_nonneg (by positivity) (by positivity)
  have hMval0 : 0 ≤ (Ctop * Cp (L - 1) + 3 * CgL + CgL * Cp (L - 2)) * (Bs + 1) + 1 := by
    have h2 := hCpnn (L - 1); have h3 := hCpnn (L - 2)
    have h1a : 0 ≤ Ctop * Cp (L - 1) := mul_nonneg hCtpos.le h2
    have h1b : 0 ≤ 3 * CgL := by linarith [hCgL0]
    have h1c : 0 ≤ CgL * Cp (L - 2) := mul_nonneg hCgL0 h3
    exact add_nonneg (mul_nonneg (by linarith) (by linarith)) zero_le_one
  refine ⟨(Ctop * Cp (L - 1) + 3 * CgL + CgL * Cp (L - 2)) * (Bs + 1) + 1, hMval0, ?_⟩
  intro v hv hvfin
  set g : Fin n → (Fin n → ℂ) → ℂ := fun l y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y
    with hgdef
  have hop : (fun z => Work.CR.Flat.Cauchy.bmPotential g z) = beltramiOp b v := rfl
  have hdD : ∀ (m : ℕ), m + 1 ≤ L → ∀ j : Fin n,
      ContDiffOn ℝ (((m : ℕ)) : ℕ∞) (fun z => Work.CR.Flat.dCoord j v z) P := by
    intro m hm j
    exact Work.NN.Core.dCoord_contDiffOn (hv.of_le (by exact_mod_cast hm)) j
  have hdDfin : ∀ (m : ℕ), m + 1 ≤ L → ∀ j : Fin n,
      Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j v z) P < ⊤ := by
    intro m hm j
    have hw : Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j v z) P
        ≤ Work.CR.Flat.holderNorm (m + 1) α v P :=
      holderNorm_dCoord_le_one hPopen (hv.of_le (by exact_mod_cast hm)) j
    exact lt_of_le_of_lt (le_trans hw
      (Work.CR.Flat.holderNorm_mono_k (by omega) α v P)) hvfin
  have hprod_sm : ∀ (m : ℕ), m + 1 ≤ L → ∀ l j : Fin n,
      ContDiff ℝ (((m : ℕ)) : ℕ∞) (fun z => b l j z * Work.CR.Flat.dCoord j v z) := by
    intro m hm l j
    exact Work.NN.Core.contDiff_flatMul_of_smooth_sharp (n := n) hρ (hbsm l j) (hvan2 l j)
      (hdD m hm j) (ne_of_lt (hdDfin m hm j))
  have hg_sm : ∀ (m : ℕ), m + 1 ≤ L → ∀ l : Fin n,
      ContDiff ℝ (((m : ℕ)) : ℕ∞) (g l) := by
    intro m hm l
    have h := ContDiff.sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun j : Fin n => fun z => b l j z * Work.CR.Flat.dCoord j v z)
      (fun j _ => hprod_sm m hm l j)
    simpa [hgdef] using h
  have hg_cs : ∀ l : Fin n, HasCompactSupport (g l) := by
    intro l
    refine Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0)
      (r := fun j => 2 * ρ j) (fun j => by linarith [hρ j]) (fun z hz => ?_)
    obtain ⟨k, hk⟩ := hz
    have hk' : ρ k ≤ ‖z k‖ := by
      have h2 : (2 * ρ k) / 2 = ρ k := by ring
      rw [h2] at hk
      simpa using hk
    have h := Work.NN.Core.beltramiDatum_vanishing (ρ := ρ) hbsupp l v z ⟨k, hk'⟩
    simpa [hgdef] using h
  have hg_van : ∀ (l : Fin n) (z : Fin n → ℂ), (∃ i, ρ i ≤ ‖z i‖) → g l z = 0 := by
    intro l z hz
    have h := Work.NN.Core.beltramiDatum_vanishing (ρ := ρ) hbsupp l v z hz
    simpa [hgdef] using h
  have hg_van2 : ∀ (l : Fin n) (z : Fin n → ℂ),
      (∃ i, (2 * ρ i) / 2 ≤ ‖z i - (0:Fin n → ℂ) i‖) → g l z = 0 := by
    intro l z hz
    obtain ⟨i, hi⟩ := hz
    refine hg_van l z ⟨i, ?_⟩
    rw [show (2 * ρ i) / 2 = ρ i from by ring] at hi
    simpa using hi
  -- the datum norm bound
  have hsum : ∀ (m : ℕ), m ≤ L - 1 →
      (∑ l, Work.CR.Flat.holderNorm m α (g l) Set.univ)
        ≤ ENNReal.ofReal 3 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm (m + 1) α v P)
          + ENNReal.ofReal (Cp m)
              * ((∑ l, ∑ j, Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ)
                  * Work.CR.Flat.holderNorm ((m - 1) + 1) α v P) := by
    intro m hm
    have hmL : m + 1 ≤ L := by omega
    have hstep1 : (∑ l, Work.CR.Flat.holderNorm m α (g l) Set.univ)
        ≤ ∑ l, ∑ j, Work.CR.Flat.holderNorm m α
            (fun z => b l j z * Work.CR.Flat.dCoord j v z) Set.univ := by
      refine Finset.sum_le_sum fun l _ => ?_
      have h := Work.CR.Flat.Holder.holderNorm_sum_le (Finset.univ : Finset (Fin n))
        (g := fun j z => b l j z * Work.CR.Flat.dCoord j v z)
        (k := m) (α := α) (fun j _ => (hprod_sm m hmL l j).contDiffOn) uniqueDiffOn_univ
      simpa [hgdef] using h
    have hstep2 : ∀ l j : Fin n,
        Work.CR.Flat.holderNorm m α (fun z => b l j z * Work.CR.Flat.dCoord j v z) Set.univ
          ≤ Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
              * Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j v z) P
            + ENNReal.ofReal (Cp m) * (Work.CR.Flat.holderNorm m α (b l j) Set.univ
                * Work.CR.Flat.holderNorm (m - 1) α (fun z => Work.CR.Flat.dCoord j v z) P) := by
      intro l j
      exact flatMul_two_le hα0 hα1 hρ m (b l j) (fun z => Work.CR.Flat.dCoord j v z)
        (hbsm l j) (hvan2 l j) (hdD m hmL j) (hdDfin m hmL j) (hprod_sm m hmL l j)
    have hw1 : ∀ j : Fin n, Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j v z) P
        ≤ Work.CR.Flat.holderNorm (m + 1) α v P :=
      fun j => holderNorm_dCoord_le_one hPopen (hv.of_le (by exact_mod_cast hmL)) j
    have hw2 : ∀ j : Fin n,
        Work.CR.Flat.holderNorm (m - 1) α (fun z => Work.CR.Flat.dCoord j v z) P
        ≤ Work.CR.Flat.holderNorm ((m - 1) + 1) α v P := by
      intro j
      have hle : (m - 1) + 1 ≤ L := by omega
      exact holderNorm_dCoord_le_one hPopen (hv.of_le (by exact_mod_cast hle)) j
    have hbm : ∀ l j : Fin n, Work.CR.Flat.holderNorm m α (b l j) Set.univ
        ≤ Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ :=
      fun l j => Work.CR.Flat.holderNorm_mono_k (by omega) α _ _
    have hA : ∑ l, ∑ j, (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
            * Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j v z) P)
        ≤ (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
            * Work.CR.Flat.holderNorm (m + 1) α v P := by
      calc ∑ l, ∑ j, (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
            * Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j v z) P)
          ≤ ∑ l, (∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm (m + 1) α v P :=
              Finset.sum_le_sum fun l _ =>
                enat_sum_mul_le Finset.univ (fun j => Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                  (fun j => Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j v z) P)
                  (Work.CR.Flat.holderNorm (m + 1) α v P) (fun j _ => hw1 j)
        _ = (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm (m + 1) α v P := by rw [← Finset.sum_mul]
    have hB : ∑ l, ∑ j, (ENNReal.ofReal (Cp m) * (Work.CR.Flat.holderNorm m α (b l j) Set.univ
            * Work.CR.Flat.holderNorm (m - 1) α (fun z => Work.CR.Flat.dCoord j v z) P))
        ≤ ENNReal.ofReal (Cp m)
            * ((∑ l, ∑ j, Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ)
                * Work.CR.Flat.holderNorm ((m - 1) + 1) α v P) := by
      calc ∑ l, ∑ j, (ENNReal.ofReal (Cp m) * (Work.CR.Flat.holderNorm m α (b l j) Set.univ
            * Work.CR.Flat.holderNorm (m - 1) α (fun z => Work.CR.Flat.dCoord j v z) P))
          ≤ ∑ l, ∑ j, (ENNReal.ofReal (Cp m) * (Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ
              * Work.CR.Flat.holderNorm ((m - 1) + 1) α v P)) := by
              refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ => ?_
              refine mul_le_mul_of_nonneg_left ?_ bot_le
              exact mul_le_mul (hbm l j) (hw2 j) bot_le bot_le
        _ = ENNReal.ofReal (Cp m)
            * ((∑ l, ∑ j, Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ)
                * Work.CR.Flat.holderNorm ((m - 1) + 1) α v P) := by
              rw [Finset.sum_congr rfl (fun l _ =>
                    enat_sum_const_mul Finset.univ
                      (fun j => Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ)
                      (ENNReal.ofReal (Cp m))
                      (Work.CR.Flat.holderNorm ((m - 1) + 1) α v P))]
              exact enat_sum_const_mul Finset.univ
                (fun l => ∑ j, Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ)
                (ENNReal.ofReal (Cp m))
                (Work.CR.Flat.holderNorm ((m - 1) + 1) α v P)
    calc (∑ l, Work.CR.Flat.holderNorm m α (g l) Set.univ)
        ≤ ∑ l, ∑ j, Work.CR.Flat.holderNorm m α
            (fun z => b l j z * Work.CR.Flat.dCoord j v z) Set.univ := hstep1
      _ ≤ ∑ l, ∑ j, (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
              * Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j v z) P
            + ENNReal.ofReal (Cp m) * (Work.CR.Flat.holderNorm m α (b l j) Set.univ
                * Work.CR.Flat.holderNorm (m - 1) α (fun z => Work.CR.Flat.dCoord j v z) P)) :=
            Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ => hstep2 l j
      _ = (∑ l, ∑ j, (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
              * Work.CR.Flat.holderNorm m α (fun z => Work.CR.Flat.dCoord j v z) P))
            + ∑ l, ∑ j, (ENNReal.ofReal (Cp m) * (Work.CR.Flat.holderNorm m α (b l j) Set.univ
                * Work.CR.Flat.holderNorm (m - 1) α (fun z => Work.CR.Flat.dCoord j v z) P)) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [← Finset.sum_add_distrib]
      _ ≤ (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm (m + 1) α v P
            + ENNReal.ofReal (Cp m)
              * ((∑ l, ∑ j, Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ)
                  * Work.CR.Flat.holderNorm ((m - 1) + 1) α v P) := add_le_add hA hB
      _ ≤ ENNReal.ofReal 3 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm (m + 1) α v P)
          + ENNReal.ofReal (Cp m)
              * ((∑ l, ∑ j, Work.CR.Flat.holderNorm (L - 1) α (b l j) Set.univ)
                  * Work.CR.Flat.holderNorm ((m - 1) + 1) α v P) := by
            refine add_le_add ?_ le_rfl
            calc (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                  * Work.CR.Flat.holderNorm (m + 1) α v P
                = 1 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                  * Work.CR.Flat.holderNorm (m + 1) α v P) := by rw [one_mul]
              _ ≤ ENNReal.ofReal 3 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                  * Work.CR.Flat.holderNorm (m + 1) α v P) := by
                  gcongr
                  norm_num
  have hg_fin : ∀ (m : ℕ), m ≤ L - 1 → ∀ l : Fin n,
      Work.CR.Flat.holderNorm m α (g l) Set.univ ≠ ⊤ := by
    intro m hm l
    have hsingle : Work.CR.Flat.holderNorm m α (g l) Set.univ
        ≤ ∑ l', Work.CR.Flat.holderNorm m α (g l') Set.univ :=
      Finset.single_le_sum (f := fun l' => Work.CR.Flat.holderNorm m α (g l') Set.univ)
        (fun l' _ => bot_le) (Finset.mem_univ l)
    refine ne_of_lt (lt_of_le_of_lt (le_trans hsingle (hsum m hm)) ?_)
    refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
    · refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      refine ENNReal.mul_lt_top ?_ ?_
      · exact ENNReal.sum_lt_top.mpr fun l _ => ENNReal.sum_lt_top.mpr fun j _ =>
          lt_top_iff_ne_top.mpr (hb_fin 0 l j)
      · exact lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_k (by omega) α v P) hvfin
    · refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      refine ENNReal.mul_lt_top ?_ ?_
      · rw [hBseq]
        exact ENNReal.ofReal_lt_top
      · exact lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_k (by omega) α v P) hvfin
  have htop : Work.CR.Flat.iterDerivNorm L (Work.CR.Flat.Cauchy.bmPotential g) P
      + Work.CR.Flat.holderSeminorm L α (Work.CR.Flat.Cauchy.bmPotential g) P
      ≤ ENNReal.ofReal Ctop * ∑ l, Work.CR.Flat.holderNorm (L - 1) α (g l) Set.univ := by
    have h := hCtop (L - 1) g (fun j => hg_sm (L - 1) (by omega) j)
      (fun j => lt_top_iff_ne_top.mpr (hg_fin (L - 1) (by omega) j)) (fun j z hz => hg_van2 j z hz)
    have h1 : (((L - 1) + 1 : ℕ)) = L := by omega
    simpa [hr2, h1] using h
  have hlow : Work.CR.Flat.holderNorm (L - 1) α (Work.CR.Flat.Cauchy.bmPotential g) P
      ≤ ENNReal.ofReal CgL * ∑ l, Work.CR.Flat.holderNorm (L - 2) α (g l) Set.univ :=
    hCgL g (fun j => hg_sm (L - 1) (by omega) j)
      (fun j => hg_cs j) (fun j => hg_fin (L - 1) (by omega) j) (fun j z hz => hg_van j z hz)
  have hreg : ContDiffOn ℝ ((L : ℕ) : ℕ∞) (Work.CR.Flat.Cauchy.bmPotential g) P := by
    have h1 : (((L - 1) + 1 : ℕ)) = L := by omega
    have h := (hCg1 g (fun j => hg_sm (L - 1) (by omega) j) (fun j => hg_cs j)
      (fun j => lt_top_iff_ne_top.mpr (hg_fin (L - 1) (by omega) j))
      (fun j z hz => hg_van j z hz)).1
    simpa [h1] using h
  refine ⟨?_, ?_⟩
  · rw [← hop]
    exact hreg
  rw [← hop]
  have hsplit : Work.CR.Flat.holderNorm L α (Work.CR.Flat.Cauchy.bmPotential g) P
      = Work.CR.Flat.holderNorm (L - 1) α (Work.CR.Flat.Cauchy.bmPotential g) P
        + (Work.CR.Flat.iterDerivNorm L (Work.CR.Flat.Cauchy.bmPotential g) P
            + Work.CR.Flat.holderSeminorm L α (Work.CR.Flat.Cauchy.bmPotential g) P) := by
    have h1 : ((L - 1) + 1 : ℕ) = L := Nat.sub_add_cancel hL
    have h2 := Work.NN.Core.holderNorm_succ_eq (L - 1) α (Work.CR.Flat.Cauchy.bmPotential g) P
    rw [h1] at h2
    exact h2
  rw [hsplit]
  -- the real normalisations
  have hS0fin : (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun l _ => ENNReal.sum_ne_top.mpr fun j _ => hb_fin 0 l j
  have hVLfin : Work.CR.Flat.holderNorm L α v P ≠ ⊤ := ne_of_lt hvfin
  have hVL1fin : Work.CR.Flat.holderNorm (L - 1) α v P ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_k (by omega) α v P) hvfin)
  have hBsS0 : L = 1 → Bs = (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ).toReal := by
    intro hL1
    rw [hBsdef, hL1]
  set S0c : ℝ := (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ).toReal with hS0cdef
  set VLc : ℝ := (Work.CR.Flat.holderNorm L α v P).toReal with hVLcdef
  set VL1c : ℝ := (Work.CR.Flat.holderNorm (L - 1) α v P).toReal with hVL1cdef
  have hS0e : (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ) = ENNReal.ofReal S0c := by
    rw [hS0cdef]; exact (ENNReal.ofReal_toReal hS0fin).symm
  have hVLe : Work.CR.Flat.holderNorm L α v P = ENNReal.ofReal VLc := by
    rw [hVLcdef]; exact (ENNReal.ofReal_toReal hVLfin).symm
  have hVL1e : Work.CR.Flat.holderNorm (L - 1) α v P = ENNReal.ofReal VL1c := by
    rw [hVL1cdef]; exact (ENNReal.ofReal_toReal hVL1fin).symm
  have hS0c0 : 0 ≤ S0c := ENNReal.toReal_nonneg
  have hVLc0 : 0 ≤ VLc := ENNReal.toReal_nonneg
  have hVL1c0 : 0 ≤ VL1c := ENNReal.toReal_nonneg
  have hS0cBs : S0c ≤ Bs := by
    rw [hS0cdef, hBsdef]
    exact ENNReal.toReal_mono (ne_of_lt hBsfin)
      (Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ =>
        Work.CR.Flat.holderNorm_mono_k (by omega) α _ _)
  rcases eq_or_lt_of_le hL with hLone | hLtwo
  · -- ## the case `L = 1`
    subst hLone
    -- the two pieces, with the constants `Cg0` and `Ctop` at level `0`
    have hlow0 : Work.CR.Flat.holderNorm 0 α (Work.CR.Flat.Cauchy.bmPotential g) P
        ≤ ENNReal.ofReal Cg0 * ∑ l, Work.CR.Flat.holderNorm 0 α (g l) Set.univ := by
      have h := (hCg0 g (fun j => hg_sm 0 (by norm_num) j) (fun j => hg_cs j)
        (fun j => lt_top_iff_ne_top.mpr (hg_fin 0 (by norm_num) j))
        (fun j z hz => hg_van j z hz)).2
      have hmono : Work.CR.Flat.holderNorm 0 α (Work.CR.Flat.Cauchy.bmPotential g) P
          ≤ Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential g) P :=
        Work.CR.Flat.holderNorm_mono_k (Nat.zero_le 1) α _ P
      exact hmono.trans h
    have htop0 : Work.CR.Flat.iterDerivNorm 1 (Work.CR.Flat.Cauchy.bmPotential g) P
        + Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential g) P
        ≤ ENNReal.ofReal Ctop * ∑ l, Work.CR.Flat.holderNorm 0 α (g l) Set.univ := by
      have h := hCtop 0 g (fun j => hg_sm 0 (by norm_num) j)
        (fun j => lt_top_iff_ne_top.mpr (hg_fin 0 (by norm_num) j)) (fun j z hz => hg_van2 j z hz)
      simpa [hr2] using h
    have hsum0 : ∑ l, Work.CR.Flat.holderNorm 0 α (g l) Set.univ
        ≤ ENNReal.ofReal 5 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
            * Work.CR.Flat.holderNorm 1 α v P) := by
      have h := hsum 0 (by norm_num)
      have hcp : Cp 0 = 2 := by rw [hCpdef]; norm_num
      rw [hcp] at h
      simp only [Nat.reduceAdd, Nat.reduceSub] at h
      have h5 : ENNReal.ofReal 3 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
            * Work.CR.Flat.holderNorm 1 α v P)
          + ENNReal.ofReal 2 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
            * Work.CR.Flat.holderNorm 1 α v P)
          = ENNReal.ofReal 5 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
            * Work.CR.Flat.holderNorm 1 α v P) := by
        rw [← add_mul]
        congr 1
        norm_num
      rwa [h5] at h
    have hfinal1 : Work.CR.Flat.holderNorm 0 α (Work.CR.Flat.Cauchy.bmPotential g) P
          + (Work.CR.Flat.iterDerivNorm 1 (Work.CR.Flat.Cauchy.bmPotential g) P
              + Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential g) P)
        ≤ ENNReal.ofReal (5 * (Ctop + Cg0) + 1)
            * (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
            * Work.CR.Flat.holderNorm 1 α v P
          + ENNReal.ofReal ((Ctop * Cp (1 - 1) + 3 * CgL + CgL * Cp (1 - 2)) * (Bs + 1) + 1)
            * Work.CR.Flat.holderNorm (1 - 1) α v P := by
      have hstep : ENNReal.ofReal Cg0 * ∑ l, Work.CR.Flat.holderNorm 0 α (g l) Set.univ
            + ENNReal.ofReal Ctop * ∑ l, Work.CR.Flat.holderNorm 0 α (g l) Set.univ
          ≤ ENNReal.ofReal (5 * (Ctop + Cg0) + 1)
              * (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm 1 α v P := by
        have h1 : ENNReal.ofReal Cg0 + ENNReal.ofReal Ctop = ENNReal.ofReal (Cg0 + Ctop) :=
          (ENNReal.ofReal_add hCg0pos.le hCtpos.le).symm
        calc ENNReal.ofReal Cg0 * ∑ l, Work.CR.Flat.holderNorm 0 α (g l) Set.univ
              + ENNReal.ofReal Ctop * ∑ l, Work.CR.Flat.holderNorm 0 α (g l) Set.univ
            = (ENNReal.ofReal Cg0 + ENNReal.ofReal Ctop)
                * ∑ l, Work.CR.Flat.holderNorm 0 α (g l) Set.univ := by rw [add_mul]
          _ = ENNReal.ofReal (Cg0 + Ctop) * ∑ l, Work.CR.Flat.holderNorm 0 α (g l) Set.univ := by
                rw [h1]
          _ ≤ ENNReal.ofReal (Cg0 + Ctop)
                * (ENNReal.ofReal 5 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                    * Work.CR.Flat.holderNorm 1 α v P)) :=
                mul_le_mul_of_nonneg_left hsum0 bot_le
          _ = ENNReal.ofReal (5 * (Cg0 + Ctop))
                * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                    * Work.CR.Flat.holderNorm 1 α v P) := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith [hCg0pos.le, hCtpos.le])]
                congr 1
                ring
          _ = (ENNReal.ofReal (5 * (Cg0 + Ctop))
                * (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ))
                * Work.CR.Flat.holderNorm 1 α v P := by rw [mul_assoc]
          _ ≤ (ENNReal.ofReal (5 * (Ctop + Cg0) + 1)
                * (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ))
                * Work.CR.Flat.holderNorm 1 α v P := by
                refine mul_le_mul_of_nonneg_right ?_ bot_le
                exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) bot_le
      calc Work.CR.Flat.holderNorm 0 α (Work.CR.Flat.Cauchy.bmPotential g) P
            + (Work.CR.Flat.iterDerivNorm 1 (Work.CR.Flat.Cauchy.bmPotential g) P
                + Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential g) P)
          ≤ ENNReal.ofReal Cg0 * ∑ l, Work.CR.Flat.holderNorm 0 α (g l) Set.univ
            + ENNReal.ofReal Ctop * ∑ l, Work.CR.Flat.holderNorm 0 α (g l) Set.univ :=
            add_le_add hlow0 htop0
        _ ≤ _ := hstep
        _ ≤ _ := by
            refine le_add_of_nonneg_right bot_le
    exact hfinal1
  · -- ## the case `2 ≤ L`
    have hm1eq : ((L - 1 - 1) + 1 : ℕ) = L - 1 := by omega
    have hm2eq : ((L - 2 + 1) : ℕ) = L - 1 := by omega
    have hLeq : ((L - 1) + 1 : ℕ) = L := by omega
    have hsumL1 := hsum (L - 1) (le_refl (L - 1))
    have hsumL2 := hsum (L - 2) (by omega)
    have hG1 : ∑ l, Work.CR.Flat.holderNorm (L - 1) α (g l) Set.univ
        ≤ ENNReal.ofReal (3 * S0c * VLc + Cp (L - 1) * Bs * VL1c) := by
      have h1 : (∑ l, Work.CR.Flat.holderNorm (L - 1) α (g l) Set.univ)
          ≤ ENNReal.ofReal 3 * (ENNReal.ofReal S0c * ENNReal.ofReal VLc)
            + ENNReal.ofReal (Cp (L - 1)) * (ENNReal.ofReal Bs * ENNReal.ofReal VL1c) := by
        simpa [hLeq, hm1eq, hS0e, hVLe, hVL1e, hBseq] using hsumL1
      refine h1.trans ?_
      rw [show ENNReal.ofReal 3 * (ENNReal.ofReal S0c * ENNReal.ofReal VLc)
            = ENNReal.ofReal (3 * S0c * VLc) from by
          rw [← ENNReal.ofReal_mul hS0c0, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
          congr 1
          ring,
        show ENNReal.ofReal (Cp (L - 1)) * (ENNReal.ofReal Bs * ENNReal.ofReal VL1c)
            = ENNReal.ofReal (Cp (L - 1) * Bs * VL1c) from by
          rw [← ENNReal.ofReal_mul hBsz, ← ENNReal.ofReal_mul (hCpnn (L - 1))]
          congr 1
          ring,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    have hG2 : ∑ l, Work.CR.Flat.holderNorm (L - 2) α (g l) Set.univ
        ≤ ENNReal.ofReal (3 * S0c * VL1c + Cp (L - 2) * Bs * VL1c) := by
      have h1 : (∑ l, Work.CR.Flat.holderNorm (L - 2) α (g l) Set.univ)
          ≤ ENNReal.ofReal 3 * (ENNReal.ofReal S0c * ENNReal.ofReal VL1c)
            + ENNReal.ofReal (Cp (L - 2))
              * (ENNReal.ofReal Bs * Work.CR.Flat.holderNorm ((L - 2 - 1) + 1) α v P) := by
        simpa [hm2eq, hS0e, hVL1e, hBseq] using hsumL2
      have hmono2 : Work.CR.Flat.holderNorm ((L - 2 - 1) + 1) α v P
          ≤ ENNReal.ofReal VL1c := by
        refine le_trans (Work.CR.Flat.holderNorm_mono_k
          (show (L - 2 - 1) + 1 ≤ L - 1 by omega) α v P) ?_
        rw [hVL1e]
      have h2' : (∑ l, Work.CR.Flat.holderNorm (L - 2) α (g l) Set.univ)
          ≤ ENNReal.ofReal 3 * (ENNReal.ofReal S0c * ENNReal.ofReal VL1c)
            + ENNReal.ofReal (Cp (L - 2)) * (ENNReal.ofReal Bs * ENNReal.ofReal VL1c) := by
        refine h1.trans ?_
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmono2 bot_le) bot_le)
      refine h2'.trans ?_
      rw [show ENNReal.ofReal 3 * (ENNReal.ofReal S0c * ENNReal.ofReal VL1c)
            = ENNReal.ofReal (3 * S0c * VL1c) from by
          rw [← ENNReal.ofReal_mul hS0c0, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
          congr 1
          ring,
        show ENNReal.ofReal (Cp (L - 2)) * (ENNReal.ofReal Bs * ENNReal.ofReal VL1c)
            = ENNReal.ofReal (Cp (L - 2) * Bs * VL1c) from by
          rw [← ENNReal.ofReal_mul hBsz, ← ENNReal.ofReal_mul (hCpnn (L - 2))]
          congr 1
          ring,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    have hcoef2 : Ctop * Cp (L - 1) * Bs + 3 * CgL * S0c + CgL * Cp (L - 2) * Bs
        ≤ (Ctop * Cp (L - 1) + 3 * CgL + CgL * Cp (L - 2)) * (Bs + 1) + 1 := by
      have h1 := hCpnn (L - 1)
      have h2 := hCpnn (L - 2)
      have hb1 : 0 ≤ Ctop * Cp (L - 1) := mul_nonneg hCtpos.le h1
      have hb2 : 0 ≤ CgL * Cp (L - 2) := mul_nonneg hCgL0 h2
      have hp1 : Ctop * Cp (L - 1) * Bs ≤ (Ctop * Cp (L - 1)) * (Bs + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hb1
      have hp2 : 3 * CgL * S0c ≤ (3 * CgL) * (Bs + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [hS0cBs]) (by linarith [hCgL0])
      have hp3 : CgL * Cp (L - 2) * Bs ≤ (CgL * Cp (L - 2)) * (Bs + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hb2
      nlinarith [hp1, hp2, hp3, hb1, hb2, hCgL0, hBsz]
    have hreal : CgL * (3 * S0c * VL1c + Cp (L - 2) * Bs * VL1c)
          + Ctop * (3 * S0c * VLc + Cp (L - 1) * Bs * VL1c)
        ≤ (5 * (Ctop + Cg0) + 1) * S0c * VLc
          + ((Ctop * Cp (L - 1) + 3 * CgL + CgL * Cp (L - 2)) * (Bs + 1) + 1) * VL1c := by
      have hcoef1 : 3 * Ctop ≤ 5 * (Ctop + Cg0) + 1 := by linarith [hCtpos.le, hCg0pos.le]
      have hkey : 3 * Ctop * S0c * VLc ≤ (5 * (Ctop + Cg0) + 1) * S0c * VLc := by
        refine mul_le_mul_of_nonneg_right ?_ hVLc0
        exact mul_le_mul_of_nonneg_right hcoef1 hS0c0
      have hkey2 : (Ctop * Cp (L - 1) * Bs + 3 * CgL * S0c + CgL * Cp (L - 2) * Bs) * VL1c
          ≤ ((Ctop * Cp (L - 1) + 3 * CgL + CgL * Cp (L - 2)) * (Bs + 1) + 1) * VL1c :=
        mul_le_mul_of_nonneg_right hcoef2 hVL1c0
      have hCgLpos : 0 ≤ CgL := hCgL0
      calc CgL * (3 * S0c * VL1c + Cp (L - 2) * Bs * VL1c)
            + Ctop * (3 * S0c * VLc + Cp (L - 1) * Bs * VL1c)
          = 3 * Ctop * S0c * VLc
            + (Ctop * Cp (L - 1) * Bs + 3 * CgL * S0c + CgL * Cp (L - 2) * Bs) * VL1c := by
            ring
        _ ≤ _ := add_le_add hkey hkey2
    have hbig : Work.CR.Flat.holderNorm (L - 1) α (Work.CR.Flat.Cauchy.bmPotential g) P
          + (Work.CR.Flat.iterDerivNorm L (Work.CR.Flat.Cauchy.bmPotential g) P
              + Work.CR.Flat.holderSeminorm L α (Work.CR.Flat.Cauchy.bmPotential g) P)
        ≤ ENNReal.ofReal (CgL * (3 * S0c * VL1c + Cp (L - 2) * Bs * VL1c)
              + Ctop * (3 * S0c * VLc + Cp (L - 1) * Bs * VL1c)) := by
      refine (add_le_add hlow htop).trans ?_
      refine (add_le_add (mul_le_mul_of_nonneg_left hG2 bot_le)
        (mul_le_mul_of_nonneg_left hG1 bot_le)).trans ?_
      rw [← ENNReal.ofReal_mul hCgL0, ← ENNReal.ofReal_mul hCtpos.le]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    have hconv : ENNReal.ofReal (CgL * (3 * S0c * VL1c + Cp (L - 2) * Bs * VL1c)
              + Ctop * (3 * S0c * VLc + Cp (L - 1) * Bs * VL1c))
        ≤ ENNReal.ofReal (5 * (Ctop + Cg0) + 1)
            * (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
            * Work.CR.Flat.holderNorm L α v P
          + ENNReal.ofReal ((Ctop * Cp (L - 1) + 3 * CgL + CgL * Cp (L - 2)) * (Bs + 1) + 1)
            * Work.CR.Flat.holderNorm (L - 1) α v P := by
      refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
      rw [ENNReal.ofReal_add (by positivity) (by positivity), hS0e, hVLe, hVL1e]
      rw [show ENNReal.ofReal ((5 * (Ctop + Cg0) + 1) * S0c * VLc)
            = ENNReal.ofReal (5 * (Ctop + Cg0) + 1) * ENNReal.ofReal S0c
              * ENNReal.ofReal VLc from by
          rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 5 * (Ctop + Cg0) + 1),
            ← ENNReal.ofReal_mul (mul_nonneg (by positivity : (0:ℝ) ≤ 5 * (Ctop + Cg0) + 1) hS0c0)],
        show ENNReal.ofReal (((Ctop * Cp (L - 1) + 3 * CgL + CgL * Cp (L - 2)) * (Bs + 1) + 1)
              * VL1c)
            = ENNReal.ofReal ((Ctop * Cp (L - 1) + 3 * CgL + CgL * Cp (L - 2)) * (Bs + 1) + 1)
              * ENNReal.ofReal VL1c from by
          rw [ENNReal.ofReal_mul (by positivity)]]
    exact hbig.trans hconv

/-! ## The level-`1` datum bound and the level-`1` contraction -/

/-- The Beltrami datum `Σ_j b l j ∂_j v` at level `1` of `v`: it is globally continuous and
compactly supported, vanishes off the polydisc, and its total `C^{0,α}`-norm is bounded by
`3 (Σ_{l,j}‖b l j‖_{0,α}) ‖v‖_{1,α}`. -/
private lemma beltramiDatum_zero {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∀ (b : Fin n → Fin n → (Fin n → ℂ) → ℂ) (v : (Fin n → ℂ) → ℂ),
      (∀ l j, ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (b l j)) →
      (∀ l j, HasCompactSupport (b l j)) →
      (∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
      ContDiffOn ℝ (1 : ℕ∞) v (Work.CR.Flat.polydisc 0 ρ) →
      Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ) < ⊤ →
      (∀ l, ContDiff ℝ (((0 : ℕ)) : ℕ∞)
              (fun y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y)) ∧
      (∀ l, HasCompactSupport (fun y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y)) ∧
      (∀ l z, (∃ i, ρ i ≤ ‖z i‖) → (∑ j, b l j z * Work.CR.Flat.dCoord j v z) = 0) ∧
      (∑ l, Work.CR.Flat.holderNorm 0 α
            (fun y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y) Set.univ)
        ≤ ENNReal.ofReal 3 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
            * Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ)) := by
  intro b v hbsm hbcs hbsupp hv hvfin
  set P : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 ρ with hP
  have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hvan2 : ∀ (l j : Fin n) (z : Fin n → ℂ), (∃ i, ρ i ≤ ‖z i‖) → b l j z = 0 := by
    intro l j z hz
    by_contra hc
    obtain ⟨i, hi⟩ := hz
    have hmem := (Work.CR.Flat.mem_polydisc.mp (hbsupp l j z hc)) i
    simp only [Pi.zero_apply, sub_zero] at hmem
    exact absurd hmem (not_lt.mpr hi)
  have hdD : ∀ j : Fin n, ContDiffOn ℝ (((0 : ℕ)) : ℕ∞)
      (fun z => Work.CR.Flat.dCoord j v z) P := by
    intro j
    exact Work.NN.Core.dCoord_contDiffOn (N := 0) (by simpa using hv) j
  have hdDfin : ∀ j : Fin n,
      Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P < ⊤ := by
    intro j
    refine lt_of_le_of_lt (le_trans (holderNorm_dCoord_le_one hPopen (m := 0)
      (by simpa using hv) j) (Work.CR.Flat.holderNorm_mono_k (by norm_num) α v P)) hvfin
  have hprod_sm : ∀ l j : Fin n,
      ContDiff ℝ (((0 : ℕ)) : ℕ∞) (fun z => b l j z * Work.CR.Flat.dCoord j v z) := by
    intro l j
    exact Work.NN.Core.contDiff_flatMul_of_smooth_sharp (n := n) hρ (hbsm l j) (hvan2 l j)
      (hdD j) (ne_of_lt (hdDfin j))
  have hg_sm : ∀ l : Fin n, ContDiff ℝ (((0 : ℕ)) : ℕ∞)
      (fun y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y) := by
    intro l
    have h := ContDiff.sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun j : Fin n => fun z => b l j z * Work.CR.Flat.dCoord j v z)
      (fun j _ => hprod_sm l j)
    simpa using h
  have hg_cs : ∀ l : Fin n,
      HasCompactSupport (fun y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y) := by
    intro l
    refine Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0)
      (r := fun j => 2 * ρ j) (fun j => by linarith [hρ j]) (fun z hz => ?_)
    obtain ⟨k, hk⟩ := hz
    have hk' : ρ k ≤ ‖z k‖ := by
      have h2 : (2 * ρ k) / 2 = ρ k := by ring
      rw [h2] at hk
      simpa using hk
    exact Work.NN.Core.beltramiDatum_vanishing (ρ := ρ) hbsupp l v z ⟨k, hk'⟩
  have hg_van : ∀ l : Fin n, ∀ z : Fin n → ℂ,
      (∃ i, ρ i ≤ ‖z i‖) → (∑ j, b l j z * Work.CR.Flat.dCoord j v z) = 0 :=
    fun l z hz => Work.NN.Core.beltramiDatum_vanishing (ρ := ρ) hbsupp l v z hz
  refine ⟨hg_sm, hg_cs, hg_van, ?_⟩
  have hstep1 : (∑ l, Work.CR.Flat.holderNorm 0 α
        (fun y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y) Set.univ)
      ≤ ∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α
          (fun z => b l j z * Work.CR.Flat.dCoord j v z) Set.univ := by
    refine Finset.sum_le_sum fun l _ => ?_
    have h := Work.CR.Flat.Holder.holderNorm_sum_le (Finset.univ : Finset (Fin n))
      (g := fun j z => b l j z * Work.CR.Flat.dCoord j v z)
      (k := 0) (α := α) (fun j _ => (hprod_sm l j).contDiffOn) uniqueDiffOn_univ
    simpa using h
  have hstep2 : ∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α
        (fun z => b l j z * Work.CR.Flat.dCoord j v z) Set.univ
      ≤ ∑ l, ∑ j, (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
            * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P
          + ENNReal.ofReal 2 * (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
              * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P)) := by
    refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ => ?_
    refine (flatMul_two_le hα0 hα1 hρ 0 (b l j) (fun z => Work.CR.Flat.dCoord j v z)
      (hbsm l j) (hvan2 l j) (hdD j) (hdDfin j) (hprod_sm l j)).trans ?_
    have h01 : ((0 : ℕ) - 1) = 0 := by omega
    rw [h01]
    refine add_le_add le_rfl ?_
    refine mul_le_mul_of_nonneg_right ?_ bot_le
    norm_num
  have hw1 : ∀ j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => Work.CR.Flat.dCoord j v z) P ≤ Work.CR.Flat.holderNorm 1 α v P :=
    fun j => holderNorm_dCoord_le_one hPopen (m := 0) (by simpa using hv) j
  have hstep3 : ∑ l, ∑ j, (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
          * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P
        + ENNReal.ofReal 2 * (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
            * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P))
      ≤ ENNReal.ofReal 3 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
          * Work.CR.Flat.holderNorm 1 α v P) := by
    have h1 : ∑ l, ∑ j, (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
          * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P)
        ≤ (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
            * Work.CR.Flat.holderNorm 1 α v P := by
      calc ∑ l, ∑ j, (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
            * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P)
          ≤ ∑ l, (∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm 1 α v P :=
              Finset.sum_le_sum fun l _ =>
                enat_sum_mul_le Finset.univ (fun j => Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                  (fun j => Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P)
                  (Work.CR.Flat.holderNorm 1 α v P) (fun j _ => hw1 j)
        _ = (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm 1 α v P := by rw [← Finset.sum_mul]
    have h2 : ∑ l, ∑ j, (ENNReal.ofReal 2 * (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
            * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P))
        ≤ ENNReal.ofReal 2 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
            * Work.CR.Flat.holderNorm 1 α v P) := by
      calc ∑ l, ∑ j, (ENNReal.ofReal 2 * (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
            * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P))
          ≤ ∑ l, ∑ j, (ENNReal.ofReal 2 * (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
              * Work.CR.Flat.holderNorm 1 α v P)) := by
              refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ => ?_
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hw1 j) bot_le) bot_le
        _ = ENNReal.ofReal 2 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm 1 α v P) := by
              rw [Finset.sum_congr rfl (fun l _ =>
                    enat_sum_const_mul Finset.univ
                      (fun j => Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                      (ENNReal.ofReal 2) (Work.CR.Flat.holderNorm 1 α v P))]
              exact enat_sum_const_mul Finset.univ
                (fun l => ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                (ENNReal.ofReal 2) (Work.CR.Flat.holderNorm 1 α v P)
    calc ∑ l, ∑ j, (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
          * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P
        + ENNReal.ofReal 2 * (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
            * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P))
        = (∑ l, ∑ j, (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
              * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P))
          + ∑ l, ∑ j, (ENNReal.ofReal 2 * (Work.CR.Flat.holderNorm 0 α (b l j) Set.univ
              * Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord j v z) P)) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [← Finset.sum_add_distrib]
      _ ≤ (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm 1 α v P
          + ENNReal.ofReal 2 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm 1 α v P) := add_le_add h1 h2
      _ = ENNReal.ofReal 3 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm 1 α v P) := by
            have hone : (1 : ℝ≥0∞) + ENNReal.ofReal 2 = ENNReal.ofReal 3 := by
              rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
              norm_num
            rw [show (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                  * Work.CR.Flat.holderNorm 1 α v P
                + ENNReal.ofReal 2 * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                  * Work.CR.Flat.holderNorm 1 α v P)
                = (1 + ENNReal.ofReal 2) * ((∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                  * Work.CR.Flat.holderNorm 1 α v P) from by rw [add_mul, one_mul],
              hone]
  exact hstep1.trans (hstep2.trans hstep3)

/-- The level-`1` contraction for the Beltrami operator: for `v` of class `C^{1,α}` on the polydisc,
`T(b∂v)` is `C^{1,α}` with norm bounded by `3 C₀ (Σ_{l,j}‖b l j‖_{0,α}) ‖v‖_{1,α}`. -/
private lemma beltramiOp_one_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hn : 0 < n) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ (b : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ l j, ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (b l j)) →
      (∀ l j, HasCompactSupport (b l j)) →
      (∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
      ∀ (v : (Fin n → ℂ) → ℂ),
        ContDiffOn ℝ (1 : ℕ∞) v (Work.CR.Flat.polydisc 0 ρ) →
        Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ) < ⊤ →
        ContDiffOn ℝ (1 : ℕ∞) (beltramiOp b v) (Work.CR.Flat.polydisc 0 ρ) ∧
        Work.CR.Flat.holderNorm 1 α (beltramiOp b v) (Work.CR.Flat.polydisc 0 ρ)
          ≤ ENNReal.ofReal C1 * (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ) := by
  obtain ⟨Cg0, hCg0pos, hCg0⟩ := bmPotential_gain (n := n) hn (α := α) hα0 hα1 hρ 0
  refine ⟨3 * Cg0, by positivity, ?_⟩
  intro b hbsm hbcs hbsupp v hv hvfin
  obtain ⟨hsm, hcs, hvan, hsum0⟩ := beltramiDatum_zero (n := n) hα0 hα1 hρ b v
    hbsm hbcs hbsupp hv hvfin
  have hbfin : (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ) < ⊤ :=
    ENNReal.sum_lt_top.mpr fun l _ => ENNReal.sum_lt_top.mpr fun j _ =>
      lt_top_iff_ne_top.mpr (Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport'
        hα0.le hα1.le ((hbsm l j).of_le (WithTop.coe_le_coe.mpr le_top)) (hbcs l j))
  obtain ⟨hcd, hbd⟩ := hCg0 (fun l y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y)
    hsm hcs (fun l => lt_of_le_of_lt
      (Finset.single_le_sum (f := fun l => Work.CR.Flat.holderNorm 0 α
        (fun y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y) Set.univ)
        (fun l _ => bot_le) (Finset.mem_univ l))
      (lt_of_le_of_lt hsum0 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top hbfin hvfin)))) hvan
  refine ⟨?_, ?_⟩
  · show ContDiffOn ℝ (1 : ℕ∞) (fun z => Work.CR.Flat.Cauchy.bmPotential
      (fun l y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y) z)
      (Work.CR.Flat.polydisc 0 ρ)
    exact hcd
  have := hsum0
  calc Work.CR.Flat.holderNorm 1 α (beltramiOp b v) (Work.CR.Flat.polydisc 0 ρ)
      ≤ ENNReal.ofReal Cg0 * ∑ l, Work.CR.Flat.holderNorm 0 α
          (fun y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y) Set.univ := hbd
    _ ≤ ENNReal.ofReal Cg0 * (ENNReal.ofReal 3 * ((∑ l, ∑ j,
            Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
            * Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ))) :=
          mul_le_mul_of_nonneg_left this bot_le
    _ = ENNReal.ofReal (3 * Cg0) * (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
          * Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCg0pos.le, mul_assoc]
          congr 1
          ring_nf


/-! ## Continuity of the Beltrami datum and (sub)additivity of the Beltrami operator
(for *smooth*, not analytic, coefficients) -/

private lemma continuous_beltramiDatum_smooth {α : ℝ} (hα0 : 0 < α)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {b : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hb : ∀ l j, ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (b l j))
    (hbsupp : ∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {v : (Fin n → ℂ) → ℂ} (hv : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ))
    (hvf : Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ) < ⊤) (l : Fin n) :
    Continuous (fun y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y) := by
  obtain ⟨M, hM0, hM⟩ := Work.NN.Core.dCoord_bound_on_polydisc (n := n) hρ hα0 hv hvf
  have hbcont : ∀ j, Continuous (b l j) := fun j => (hb l j).continuous
  have hbound : ∀ y, ‖∑ j, b l j y * Work.CR.Flat.dCoord j v y‖ ≤ (∑ j, ‖b l j y‖) * M := by
    intro y
    by_cases hy : y ∈ Work.CR.Flat.polydisc 0 ρ
    · calc ‖∑ j, b l j y * Work.CR.Flat.dCoord j v y‖
          ≤ ∑ j, ‖b l j y * Work.CR.Flat.dCoord j v y‖ := norm_sum_le _ _
        _ = ∑ j, ‖b l j y‖ * ‖Work.CR.Flat.dCoord j v y‖ := by
            exact Finset.sum_congr rfl fun j _ => norm_mul _ _
        _ ≤ ∑ j, ‖b l j y‖ * M :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hM j y hy) (norm_nonneg _)
        _ = (∑ j, ‖b l j y‖) * M := by rw [Finset.sum_mul]
    · have hzero : ∀ j, b l j y = 0 := fun j => by
        by_contra hc
        exact hy (hbsupp l j y hc)
      simp only [hzero, zero_mul, Finset.sum_const_zero, norm_zero]
      positivity
  rw [continuous_iff_continuousAt]
  intro y₀
  by_cases hy₀ : y₀ ∈ Work.CR.Flat.polydisc 0 ρ
  · have hcontOn : ContinuousOn (fun y => ∑ j, b l j y * Work.CR.Flat.dCoord j v y)
        (Work.CR.Flat.polydisc 0 ρ) := by
      refine continuousOn_finsetSum _ fun j _ => ?_
      exact (hbcont j).continuousOn.mul
        (Work.NN.Core.dCoord_contDiffOn (N := 0) (by simpa using hv) j).continuousOn
    exact hcontOn.continuousAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hy₀)
  · have hb0 : ∀ j, b l j y₀ = 0 := fun j => by
      by_contra hc
      exact hy₀ (hbsupp l j y₀ hc)
    have hlim : Filter.Tendsto (fun y => (∑ j, ‖b l j y‖) * M) (𝓝 y₀) (𝓝 0) := by
      have h1 : Filter.Tendsto (fun y => ∑ j, ‖b l j y‖) (𝓝 y₀) (𝓝 (∑ j, ‖b l j y₀‖)) :=
        tendsto_finsetSum _ fun j _ => ((hbcont j).continuousAt).norm
      have hconst : Filter.Tendsto (fun _ : Fin n → ℂ => M) (𝓝 y₀) (𝓝 M) := tendsto_const_nhds
      have h2 := h1.mul hconst
      have h3 : (∑ j, ‖b l j y₀‖) = 0 := by simp [hb0]
      simpa [h3] using h2
    have hzero : (∑ j, b l j y₀ * Work.CR.Flat.dCoord j v y₀) = 0 := by simp [hb0]
    rw [ContinuousAt, hzero]
    exact squeeze_zero_norm' (Filter.Eventually.of_forall hbound) hlim

private lemma beltramiOp_add_smooth {α : ℝ} (hα0 : 0 < α) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hn : 0 < n)
    {b : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hb : ∀ l j, ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (b l j))
    (hbsupp : ∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {v w : (Fin n → ℂ) → ℂ}
    (hv : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ))
    (hw : ContDiffOn ℝ 1 w (Work.CR.Flat.polydisc 0 ρ))
    (hvf : Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ) < ⊤)
    (hwf : Work.CR.Flat.holderNorm 1 α w (Work.CR.Flat.polydisc 0 ρ) < ⊤) :
    beltramiOp b (v + w) = beltramiOp b v + beltramiOp b w := by
  funext z
  have hdat := Work.NN.Core.beltramiDatum_add (n := n) hρ hbsupp hv hw
  have hcs : ∀ m, HasCompactSupport (fun y => ∑ j, b m j y * Work.CR.Flat.dCoord j v y) :=
    fun m => Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0)
      (r := fun j => 2 * ρ j) (fun j => by linarith [hρ j]) (fun z hz => by
        obtain ⟨k, hk⟩ := hz
        have hk' : ρ k ≤ ‖z k‖ := by
          have h2 : (2 * ρ k) / 2 = ρ k := by ring
          rw [h2] at hk
          simpa using hk
        exact Work.NN.Core.beltramiDatum_vanishing (ρ := ρ) hbsupp m v z ⟨k, hk'⟩)
  have hcs' : ∀ m, HasCompactSupport (fun y => ∑ j, b m j y * Work.CR.Flat.dCoord j w y) :=
    fun m => Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0)
      (r := fun j => 2 * ρ j) (fun j => by linarith [hρ j]) (fun z hz => by
        obtain ⟨k, hk⟩ := hz
        have hk' : ρ k ≤ ‖z k‖ := by
          have h2 : (2 * ρ k) / 2 = ρ k := by ring
          rw [h2] at hk
          simpa using hk
        exact Work.NN.Core.beltramiDatum_vanishing (ρ := ρ) hbsupp m w z ⟨k, hk'⟩)
  have hcontv : ∀ m, Continuous (fun y => ∑ j, b m j y * Work.CR.Flat.dCoord j v y) :=
    fun m => continuous_beltramiDatum_smooth hα0 hρ hb hbsupp hv hvf m
  have hcontw : ∀ m, Continuous (fun y => ∑ j, b m j y * Work.CR.Flat.dCoord j w y) :=
    fun m => continuous_beltramiDatum_smooth hα0 hρ hb hbsupp hw hwf m
  simp only [Work.NN.Core.beltramiOp, Pi.add_apply]
  rw [hdat]
  exact Work.NN.Core.bmPotential_add_of_cont_apply hn hcontv hcontw hcs hcs' z

private lemma beltramiOp_sub_smooth {α : ℝ} (hα0 : 0 < α) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hn : 0 < n)
    {b : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hb : ∀ l j, ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (b l j))
    (hbsupp : ∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {v w : (Fin n → ℂ) → ℂ}
    (hv : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ))
    (hw : ContDiffOn ℝ 1 w (Work.CR.Flat.polydisc 0 ρ))
    (hvf : Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ) < ⊤)
    (hwf : Work.CR.Flat.holderNorm 1 α w (Work.CR.Flat.polydisc 0 ρ) < ⊤) :
    beltramiOp b (v - w) = beltramiOp b v - beltramiOp b w := by
  funext z
  have hdat := Work.NN.Core.beltramiDatum_sub (n := n) hρ hbsupp hv hw
  have hcs : ∀ m, HasCompactSupport (fun y => ∑ j, b m j y * Work.CR.Flat.dCoord j v y) :=
    fun m => Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0)
      (r := fun j => 2 * ρ j) (fun j => by linarith [hρ j]) (fun z hz => by
        obtain ⟨k, hk⟩ := hz
        have hk' : ρ k ≤ ‖z k‖ := by
          have h2 : (2 * ρ k) / 2 = ρ k := by ring
          rw [h2] at hk
          simpa using hk
        exact Work.NN.Core.beltramiDatum_vanishing (ρ := ρ) hbsupp m v z ⟨k, hk'⟩)
  have hcs' : ∀ m, HasCompactSupport (fun y => ∑ j, b m j y * Work.CR.Flat.dCoord j w y) :=
    fun m => Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0)
      (r := fun j => 2 * ρ j) (fun j => by linarith [hρ j]) (fun z hz => by
        obtain ⟨k, hk⟩ := hz
        have hk' : ρ k ≤ ‖z k‖ := by
          have h2 : (2 * ρ k) / 2 = ρ k := by ring
          rw [h2] at hk
          simpa using hk
        exact Work.NN.Core.beltramiDatum_vanishing (ρ := ρ) hbsupp m w z ⟨k, hk'⟩)
  have hcontv : ∀ m, Continuous (fun y => ∑ j, b m j y * Work.CR.Flat.dCoord j v y) :=
    fun m => continuous_beltramiDatum_smooth hα0 hρ hb hbsupp hv hvf m
  have hcontw : ∀ m, Continuous (fun y => ∑ j, b m j y * Work.CR.Flat.dCoord j w y) :=
    fun m => continuous_beltramiDatum_smooth hα0 hρ hb hbsupp hw hwf m
  simp only [Work.NN.Core.beltramiOp, Pi.sub_apply]
  rw [hdat]
  exact Work.NN.Core.bmPotential_sub_of_cont_apply hn hcontv hcontw hcs hcs' z

/-! ## The main theorem -/

/-- The small-coefficient interior Schauder/bootstrap engine for the Beltrami system, with the
smallness imposed **only at level 0**, a threshold **uniform in the level `k` and in `ρ'`**, and
the coefficient `b` smooth in the *finite-order* sense (not analytic `ω`).

If `b` is `C^∞` (finite orders), compactly supported, supported in the open polydisc
`polydisc 0 ρ` and `C^{0,α}`-small there (by the fixed threshold `δ`, depending only on `ρ`), if
`F` is `C^k` with finite `C^{k,α}`-norm on `polydisc 0 ρ`, and `u` is `C¹` with finite
`C^{1,α}`-norm on `polydisc 0 ρ` satisfying `u = T(b ∂u) + F` there (`T = bmPotential`), then `u`
is `C^k` with finite `C^{k,α}`-norm on every strictly smaller polydisc `polydisc 0 ρ'`.

The point of the level-0 hypothesis is that it is *scale invariant* (a smallness hypothesis at
level `k` has a threshold that necessarily decays with `k`), while `δ` is independent of both `k`
and `ρ'`: this is what makes a bootstrap in which the coefficient is *not* cut off work.  The
proof is the Neumann series `Σ_m (T ∘ b∂)^m F`: the top-order term is bounded by
`K·‖b‖_{0,α}·‖w‖_{k,α}` with `K` **independent of `k`** (because `∂` commutes with `T`,
`Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv`), and the lower-order terms (carrying derivatives
of `b`) are absorbed using the Gagliardo–Nirenberg interpolation `holderNorm_interp_le` together
with the geometric decay of `‖w_m‖_{0,α}`; the limit is taken with `holderNorm_le_of_tendsto`. -/
private theorem contDiffOn_of_beltrami_fixedPoint_c0_smooth {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {ρ' : Fin n → ℝ}, (∀ j, 0 < ρ' j) → (∀ j, ρ' j < ρ j) →
      ∀ (k : ℕ), 1 ≤ k → ∀ (b : Fin n → Fin n → (Fin n → ℂ) → ℂ) (F u : (Fin n → ℂ) → ℂ),
        (∀ l j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b l j)) →
        (∀ l j, HasCompactSupport (b l j)) →
        (∀ l j z, b l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        (∀ l j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ ≤ ENNReal.ofReal δ) →
        ContDiffOn ℝ (k : ℕ∞) F (Work.CR.Flat.polydisc 0 ρ) →
        Work.CR.Flat.holderNorm k α F (Work.CR.Flat.polydisc 0 ρ) < ⊤ →
        ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
        Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc 0 ρ) < ⊤ →
        (∀ z ∈ Work.CR.Flat.polydisc 0 ρ,
          u z = Work.CR.Flat.Cauchy.bmPotential
                  (fun l y => ∑ j, b l j y * Work.CR.Flat.dCoord j u y) z + F z) →
        ContDiffOn ℝ (k : ℕ∞) u (Work.CR.Flat.polydisc 0 ρ') ∧
          Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ') < ⊤ := by
  classical
  obtain ⟨Cstar, hCstarpos, hstep⟩ := beltramiOp_step_le (n := n) hα0 hα1 hρ hn
  obtain ⟨C1, hC1pos, hone⟩ := beltramiOp_one_le (n := n) hα0 hα1 hρ hn
  set W : ℝ := C1 * ((n : ℝ) * (n : ℝ)) + Cstar * ((n : ℝ) * (n : ℝ)) + 1 with hWdef
  have hnn : 0 ≤ (n : ℝ) * (n : ℝ) := mul_self_nonneg _
  have hWpos : 0 < W := by
    rw [hWdef]
    have h1 : 0 ≤ C1 * ((n : ℝ) * (n : ℝ)) := mul_nonneg hC1pos.le hnn
    have h2 : 0 ≤ Cstar * ((n : ℝ) * (n : ℝ)) := mul_nonneg hCstarpos.le hnn
    linarith
  refine ⟨1 / (2 * W), by positivity, ?_⟩
  intro ρ' hρ' hρ'ρ k hk b F u hbsm hbcs hbsupp hbδ hF hFf hu huf heq
  set P : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 ρ with hPdef
  set P' : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 ρ' with hP'def
  have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hP'open : IsOpen P' := Work.CR.Flat.isOpen_polydisc 0 ρ'
  have hP'sub : P' ⊆ P := Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρ'ρ j))
  have hδ0 : 0 ≤ 1 / (2 * W) := by positivity
  have hBsmem : (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
      ≤ ENNReal.ofReal ((n : ℝ) * (n : ℝ) * (1 / (2 * W))) :=
    Work.NN.Core.sum_sum_holderNorm_le hδ0 (le_refl 0) hbδ
  have hδC1 : C1 * ((n : ℝ) * (n : ℝ) * (1 / (2 * W))) ≤ 1 / 2 := by
    have hle : C1 * ((n : ℝ) * (n : ℝ)) ≤ W := by
      rw [hWdef]
      have h2 : 0 ≤ Cstar * ((n : ℝ) * (n : ℝ)) := mul_nonneg hCstarpos.le hnn
      linarith
    calc C1 * ((n : ℝ) * (n : ℝ) * (1 / (2 * W)))
        = (C1 * ((n : ℝ) * (n : ℝ))) * (1 / (2 * W)) := by ring
      _ ≤ W * (1 / (2 * W)) := mul_le_mul_of_nonneg_right hle (by positivity)
      _ = 1 / 2 := by field_simp
  have hδCs : Cstar * ((n : ℝ) * (n : ℝ) * (1 / (2 * W))) ≤ 1 / 2 := by
    have hle : Cstar * ((n : ℝ) * (n : ℝ)) ≤ W := by
      rw [hWdef]
      have h2 : 0 ≤ C1 * ((n : ℝ) * (n : ℝ)) := mul_nonneg hC1pos.le hnn
      linarith
    calc Cstar * ((n : ℝ) * (n : ℝ) * (1 / (2 * W)))
        = (Cstar * ((n : ℝ) * (n : ℝ))) * (1 / (2 * W)) := by ring
      _ ≤ W * (1 / (2 * W)) := mul_le_mul_of_nonneg_right hle (by positivity)
      _ = 1 / 2 := by field_simp
  -- ## the level-`1` geometric decay of the iterates
  have hdecay : ∀ (v : (Fin n → ℂ) → ℂ), ContDiffOn ℝ 1 v P →
      Work.CR.Flat.holderNorm 1 α v P < ⊤ →
      ∀ m, ContDiffOn ℝ 1 ((beltramiOp b)^[m] v) P ∧
        Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[m] v) P
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m) * Work.CR.Flat.holderNorm 1 α v P := by
    intro v hv hvfin m
    induction m with
    | zero =>
      refine ⟨by simpa using hv, ?_⟩
      rw [Function.iterate_zero_apply, pow_zero, ENNReal.ofReal_one, one_mul]
    | succ m ih =>
      obtain ⟨hcd, hbd⟩ := ih
      have hfin : Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[m] v) P < ⊤ :=
        lt_of_le_of_lt hbd (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvfin)
      obtain ⟨hcd', hbd'⟩ := hone b hbsm hbcs hbsupp ((beltramiOp b)^[m] v) hcd hfin
      refine ⟨by rwa [Function.iterate_succ_apply'], ?_⟩
      rw [Function.iterate_succ_apply']
      calc Work.CR.Flat.holderNorm 1 α (beltramiOp b ((beltramiOp b)^[m] v)) P
          ≤ ENNReal.ofReal C1 * (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
              * Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[m] v) P := hbd'
        _ ≤ ENNReal.ofReal C1 * ENNReal.ofReal ((n : ℝ) * (n : ℝ) * (1 / (2 * W)))
              * (ENNReal.ofReal ((1 / 2 : ℝ) ^ m) * Work.CR.Flat.holderNorm 1 α v P) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hBsmem bot_le) hbd bot_le bot_le
        _ = ENNReal.ofReal (C1 * ((n : ℝ) * (n : ℝ) * (1 / (2 * W))))
              * ENNReal.ofReal ((1 / 2 : ℝ) ^ m) * Work.CR.Flat.holderNorm 1 α v P := by
              rw [show ENNReal.ofReal C1
                    * ENNReal.ofReal ((n : ℝ) * (n : ℝ) * (1 / (2 * W)))
                  = ENNReal.ofReal (C1 * ((n : ℝ) * (n : ℝ) * (1 / (2 * W)))) from
                    (ENNReal.ofReal_mul hC1pos.le).symm]
              simp only [mul_assoc]
        _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (m + 1)) * Work.CR.Flat.holderNorm 1 α v P := by
              have hcoef : ENNReal.ofReal (C1 * ((n : ℝ) * (n : ℝ) * (1 / (2 * W))))
                    * ENNReal.ofReal ((1 / 2 : ℝ) ^ m)
                  ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (m + 1)) := by
                rw [← ENNReal.ofReal_mul (by positivity :
                  (0 : ℝ) ≤ C1 * ((n : ℝ) * (n : ℝ) * (1 / (2 * W))))]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [pow_succ, mul_comm (((1 / 2 : ℝ)) ^ m) (1 / 2)]
                exact mul_le_mul_of_nonneg_right hδC1 (pow_nonneg (by norm_num) m)
              exact mul_le_mul_of_nonneg_right hcoef bot_le
  -- ## the induction on the level
  have hInv : ∀ L, 1 ≤ L → L ≤ k →
      (∀ m, ContDiffOn ℝ ((L : ℕ) : ℕ∞) ((beltramiOp b)^[m] F) P) ∧
      (∀ m, Work.CR.Flat.holderNorm L α ((beltramiOp b)^[m] F) P < ⊤) ∧
      Summable (fun m => (Work.CR.Flat.holderNorm L α ((beltramiOp b)^[m] F) P).toReal) := by
    have main : ∀ m, m + 1 ≤ k →
        (∀ j, ContDiffOn ℝ (((m + 1 : ℕ)) : ℕ∞) ((beltramiOp b)^[j] F) P) ∧
        (∀ j, Work.CR.Flat.holderNorm (m + 1) α ((beltramiOp b)^[j] F) P < ⊤) ∧
        Summable (fun j =>
          (Work.CR.Flat.holderNorm (m + 1) α ((beltramiOp b)^[j] F) P).toReal) := by
      intro m
      induction m with
      | zero =>
        intro hm
        have hF1 : ContDiffOn ℝ (1 : ℕ∞) F P := hF.of_le (by exact_mod_cast hm)
        have hF1fin : Work.CR.Flat.holderNorm 1 α F P < ⊤ :=
          lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_k hm α F P) hFf
        have hdec := hdecay F hF1 hF1fin
        refine ⟨fun j => (hdec j).1, fun j => ?_, ?_⟩
        · exact lt_of_le_of_lt (hdec j).2
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF1fin)
        · have hdom : ∀ j, (Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[j] F) P).toReal
              ≤ (1 / 2 : ℝ) ^ j * (Work.CR.Flat.holderNorm 1 α F P).toReal := by
            intro j
            have h1 : (Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[j] F) P).toReal
                ≤ (ENNReal.ofReal ((1 / 2 : ℝ) ^ j)
                    * Work.CR.Flat.holderNorm 1 α F P).toReal :=
              ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hF1fin))
                (hdec j).2
            rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by norm_num) j)] at h1
          exact Summable.of_nonneg_of_le (fun j => ENNReal.toReal_nonneg)
            hdom ((summable_geometric_of_lt_one (r := 1/2) (by norm_num) (by norm_num)).mul_right _)
      | succ m ih =>
        intro hm
        obtain ⟨ihcd, ihfin, ihsum⟩ := ih (by omega)
        obtain ⟨M_L, hM_L0, hstepL⟩ := hstep (m + 2) (by omega) b hbsm hbcs hbsupp
        have hsub : m + 2 - 1 = m + 1 := by omega
        have hmk : m + 2 ≤ k := hm
        have hcf : ∀ j, ContDiffOn ℝ (((m + 2 : ℕ)) : ℕ∞) ((beltramiOp b)^[j] F) P ∧
            Work.CR.Flat.holderNorm (m + 2) α ((beltramiOp b)^[j] F) P < ⊤ := by
          intro j
          induction j with
          | zero =>
            exact ⟨hF.of_le (by exact_mod_cast hmk),
              lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_k hmk α F P) hFf⟩
          | succ j ihj =>
            obtain ⟨hcdj, hfinj⟩ := ihj
            obtain ⟨hcd', hbd'⟩ := hstepL ((beltramiOp b)^[j] F) hcdj hfinj
            rw [hsub] at hbd'
            refine ⟨by rwa [Function.iterate_succ_apply'], ?_⟩
            rw [Function.iterate_succ_apply']
            refine lt_of_le_of_lt hbd' ?_
            refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
            · exact ENNReal.mul_lt_top
                (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
                  (lt_of_le_of_lt hBsmem ENNReal.ofReal_lt_top)) hfinj
            · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ihfin j)
        have hrec : ∀ j, (Work.CR.Flat.holderNorm (m + 2) α ((beltramiOp b)^[j + 1] F) P).toReal
            ≤ (1 / 2) * (Work.CR.Flat.holderNorm (m + 2) α ((beltramiOp b)^[j] F) P).toReal
              + M_L * (Work.CR.Flat.holderNorm (m + 1) α ((beltramiOp b)^[j] F) P).toReal := by
          intro j
          obtain ⟨hcdj, hfinj⟩ := hcf j
          obtain ⟨-, hbnd⟩ := hstepL ((beltramiOp b)^[j] F) hcdj hfinj
          rw [hsub] at hbnd
          have hbnd' : Work.CR.Flat.holderNorm (m + 2) α ((beltramiOp b)^[j + 1] F) P
              ≤ ENNReal.ofReal (1 / 2)
                  * Work.CR.Flat.holderNorm (m + 2) α ((beltramiOp b)^[j] F) P
                + ENNReal.ofReal M_L * Work.CR.Flat.holderNorm (m + 1) α ((beltramiOp b)^[j] F) P := by
            rw [Function.iterate_succ_apply']
            refine hbnd.trans ?_
            have h1 : ENNReal.ofReal Cstar
                  * (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                ≤ ENNReal.ofReal (1 / 2) := by
              calc ENNReal.ofReal Cstar
                    * (∑ l, ∑ j, Work.CR.Flat.holderNorm 0 α (b l j) Set.univ)
                  ≤ ENNReal.ofReal Cstar
                    * ENNReal.ofReal ((n : ℝ) * (n : ℝ) * (1 / (2 * W))) :=
                      mul_le_mul_of_nonneg_left hBsmem bot_le
                _ = ENNReal.ofReal (Cstar * ((n : ℝ) * (n : ℝ) * (1 / (2 * W)))) :=
                      (ENNReal.ofReal_mul hCstarpos.le).symm
                _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hδCs
            exact add_le_add (mul_le_mul_of_nonneg_right h1 bot_le) le_rfl
          have hf1 : (ENNReal.ofReal (1 / 2)
                * Work.CR.Flat.holderNorm (m + 2) α ((beltramiOp b)^[j] F) P
              + ENNReal.ofReal M_L * Work.CR.Flat.holderNorm (m + 1) α ((beltramiOp b)^[j] F) P)
              ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨
                ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hfinj),
                ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (ihfin j))⟩
          have hgoal := ENNReal.toReal_mono hf1 hbnd'
          rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hfinj))
                (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (ihfin j))),
              ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
              ENNReal.toReal_ofReal hM_L0] at hgoal
        have hmain := summable_of_linear_recursion (x := fun j =>
            (Work.CR.Flat.holderNorm (m + 2) α ((beltramiOp b)^[j] F) P).toReal)
          (y := fun j => (Work.CR.Flat.holderNorm (m + 1) α ((beltramiOp b)^[j] F) P).toReal)
          (θ := 1 / 2) (K := M_L)
          (fun j => ENNReal.toReal_nonneg) (fun j => ENNReal.toReal_nonneg)
          (by norm_num) (by norm_num) hM_L0 hrec ihsum
        exact ⟨fun j => (hcf j).1, fun j => (hcf j).2, hmain.1⟩
    intro L hL1 hLk
    have h := main (L - 1) (by omega)
    rwa [Nat.sub_add_cancel hL1] at h
  -- ## the limit
  obtain ⟨hkcd, hkfin, hksum⟩ := hInv k hk le_rfl
  set A : ℕ → (Fin n → ℂ) → ℂ :=
    fun M z => ∑ i ∈ Finset.range M, ((beltramiOp b)^[i] F) z with hAdef
  have hAapp : ∀ (M : ℕ) (z : Fin n → ℂ),
      A M z = ∑ i ∈ Finset.range M, ((beltramiOp b)^[i] F) z := fun M z => rfl
  set Cfin : ℝ := ∑' m, (Work.CR.Flat.holderNorm k α ((beltramiOp b)^[m] F) P).toReal
    with hCfindef
  have hCfin0 : 0 ≤ Cfin := tsum_nonneg fun m => ENNReal.toReal_nonneg
  have hF1fin : Work.CR.Flat.holderNorm 1 α F P < ⊤ :=
    lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_k hk α F P) hFf
  have hdecF : ∀ m, ContDiffOn ℝ 1 ((beltramiOp b)^[m] F) P :=
    fun m => hdecay F (hF.of_le (by exact_mod_cast hk)) hF1fin m |>.1
  have hdecFin : ∀ m, Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[m] F) P < ⊤ :=
    fun m => lt_of_le_of_lt (hdecay F (hF.of_le (by exact_mod_cast hk)) hF1fin m).2
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF1fin)
  have hdecU : ∀ m, ContDiffOn ℝ 1 ((beltramiOp b)^[m] u) P :=
    fun m => (hdecay u hu huf m).1
  have hdecUfin : ∀ m, Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[m] u) P < ⊤ :=
    fun m => lt_of_le_of_lt (hdecay u hu huf m).2
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top huf)
  -- the resolvent identity for the iterates
  have hid : ∀ M, Set.EqOn ((beltramiOp b)^[M] u)
      (fun z => (beltramiOp b)^[M] F z + ((beltramiOp b)^[M + 1]) u z) P := by
    intro M
    induction M with
    | zero =>
      intro z hz
      dsimp only
      have hzx := heq z hz
      have hopu : (beltramiOp b) u z = Work.CR.Flat.Cauchy.bmPotential
          (fun l y => ∑ j, b l j y * Work.CR.Flat.dCoord j u y) z := rfl
      have e0 : (beltramiOp b)^[0] u z = u z := rfl
      have e1 : (beltramiOp b)^[0] F z = F z := rfl
      have e2 : (beltramiOp b)^[0 + 1] u z = (beltramiOp b) u z := rfl
      rw [e0, e1, e2, hopu, add_comm]
      exact hzx
    | succ M ih =>
      intro z hz
      dsimp only
      have h1 : (beltramiOp b) ((beltramiOp b)^[M] u) z
          = (beltramiOp b) ((beltramiOp b)^[M] F + (beltramiOp b)^[M + 1] u) z :=
        congrFun (Work.NN.Core.beltramiOp_congr hbsupp ih) z
      have h2 : (beltramiOp b) ((beltramiOp b)^[M] F + (beltramiOp b)^[M + 1] u) z
          = (beltramiOp b) ((beltramiOp b)^[M] F) z
            + (beltramiOp b) ((beltramiOp b)^[M + 1] u) z := by
        rw [beltramiOp_add_smooth hα0 hρ hn hbsm hbsupp
          (hdecF M) (hdecU (M + 1)) (hdecFin M) (hdecUfin (M + 1))]
        rfl
      have key := h1.trans h2
      rw [show (beltramiOp b)^[M + 1] u z = (beltramiOp b) ((beltramiOp b)^[M] u) z from by
            rw [Function.iterate_succ_apply']]
      rw [show (beltramiOp b)^[M + 1] F z = (beltramiOp b) ((beltramiOp b)^[M] F) z from by
            rw [Function.iterate_succ_apply']]
      rw [show (beltramiOp b)^[M + 2] u z
            = (beltramiOp b) ((beltramiOp b)^[M + 1] u) z from by
            rw [Function.iterate_succ_apply']]
      exact key
  have hident : ∀ M, Set.EqOn u (fun z => A M z + ((beltramiOp b)^[M]) u z) P := by
    intro M
    induction M with
    | zero =>
      intro z hz
      dsimp only
      rw [Function.iterate_zero_apply, hAapp]
      simp
    | succ M ih =>
      intro z hz
      dsimp only
      have h1 := hid M hz
      dsimp only at h1
      have e1 : (beltramiOp b)^[M + 1] u z = (beltramiOp b) ((beltramiOp b)^[M] u) z := by
        rw [Function.iterate_succ_apply']
      rw [e1] at h1 ⊢
      have h4 := ih hz
      dsimp only at h4
      have h5 : A (M + 1) z = A M z + (beltramiOp b)^[M] F z := by
        rw [hAapp, hAapp, Finset.sum_range_succ]
      rw [h5]
      rw [h4, h1]
      ring
  -- pointwise convergence
  have hconv : ∀ z ∈ P', Tendsto (fun M => A M z) atTop (nhds (u z)) := by
    intro z hz
    have hzP : z ∈ P := hP'sub hz
    have hrem : Tendsto (fun M => ((beltramiOp b)^[M]) u z) atTop (nhds 0) := by
      have hbd : ∀ M, ‖((beltramiOp b)^[M]) u z‖
          ≤ ((1 / 2 : ℝ) ^ M) * (Work.CR.Flat.holderNorm 1 α u P).toReal := by
        intro M
        have hfin : Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[M] u) P < ⊤ := hdecUfin M
        have h1 : ENNReal.ofReal ‖((beltramiOp b)^[M]) u z‖
            ≤ Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[M] u) P := by
          refine le_trans ?_ (Work.CR.Flat.iterDerivNorm_le_holderNorm 1 α
            ((beltramiOp b)^[M] u) P (Nat.zero_le 1))
          simp only [Work.CR.Flat.iterDerivNorm, norm_iteratedFDerivWithin_zero]
          exact le_iSup₂_of_le z hzP le_rfl
        have h3 : ENNReal.ofReal ‖((beltramiOp b)^[M]) u z‖
            ≤ ENNReal.ofReal (Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[M] u) P).toReal := by
          rw [ENNReal.ofReal_toReal (ne_of_lt hfin)]
          exact h1
        have h2 : ‖((beltramiOp b)^[M]) u z‖
            ≤ (Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[M] u) P).toReal :=
          (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h3
        calc ‖((beltramiOp b)^[M]) u z‖
            ≤ (Work.CR.Flat.holderNorm 1 α ((beltramiOp b)^[M] u) P).toReal := h2
          _ ≤ (ENNReal.ofReal ((1 / 2 : ℝ) ^ M)
                * Work.CR.Flat.holderNorm 1 α u P).toReal :=
              ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt huf))
                (hdecay u hu huf M).2
          _ = (1 / 2 : ℝ) ^ M * (Work.CR.Flat.holderNorm 1 α u P).toReal := by
              rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by norm_num) M)]
      refine squeeze_zero_norm' (Filter.Eventually.of_forall hbd) ?_
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).mul_const
          (Work.CR.Flat.holderNorm 1 α u P).toReal
    have hsub : ∀ M, A M z = u z - ((beltramiOp b)^[M]) u z := by
      intro M
      have h := hident M hzP
      dsimp only at h
      rw [h]
      ring
    have hlim : Tendsto (fun M => u z - ((beltramiOp b)^[M]) u z) atTop (nhds (u z)) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => u z) atTop (nhds (u z))).sub hrem
    refine hlim.congr' ?_
    filter_upwards with M
    exact (hsub M).symm
  -- the uniform bound
  have hbound : ∀ M, Work.CR.Flat.holderNorm k α (A M) P' ≤ ENNReal.ofReal Cfin := by
    intro M
    have h2 : A M = fun z => ∑ i ∈ Finset.range M, ((beltramiOp b)^[i] F) z :=
      funext fun z => hAapp M z
    rw [h2]
    refine (Work.CR.Flat.holderNorm_mono_set hPopen hP'open hP'sub k α _).trans ?_
    refine (Work.CR.Flat.Holder.holderNorm_sum_le (Finset.range M)
      (fun i _ => (hkcd i)) hPopen.uniqueDiffOn).trans ?_
    calc ∑ i ∈ Finset.range M, Work.CR.Flat.holderNorm k α ((beltramiOp b)^[i] F) P
        ≤ ∑ i ∈ Finset.range M,
            ENNReal.ofReal ((Work.CR.Flat.holderNorm k α ((beltramiOp b)^[i] F) P).toReal) :=
          Finset.sum_le_sum fun i _ => by
            rw [ENNReal.ofReal_toReal (ne_of_lt (hkfin i))]
      _ = ENNReal.ofReal (∑ i ∈ Finset.range M,
            (Work.CR.Flat.holderNorm k α ((beltramiOp b)^[i] F) P).toReal) :=
          (ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)).symm
      _ ≤ ENNReal.ofReal Cfin :=
          ENNReal.ofReal_le_ofReal (hksum.sum_le_tsum (Finset.range M)
            (fun i _ => ENNReal.toReal_nonneg))
  -- the Cauchy condition
  have hcau : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m m' : ℕ, M ≤ m → M ≤ m' →
      Work.CR.Flat.holderNorm k α (A m - A m') P' ≤ ENNReal.ofReal ε := by
    intro ε hε
    have htsum_fin : (∑' m, Work.CR.Flat.holderNorm k α ((beltramiOp b)^[m] F) P) ≠ ⊤ := by
      have h2 : (∑' m, Work.CR.Flat.holderNorm k α ((beltramiOp b)^[m] F) P)
          = ∑' m, ENNReal.ofReal
              (Work.CR.Flat.holderNorm k α ((beltramiOp b)^[m] F) P).toReal :=
        tsum_congr fun m => (ENNReal.ofReal_toReal (ne_of_lt (hkfin m))).symm
      have h3 : (∑' m, ENNReal.ofReal
              (Work.CR.Flat.holderNorm k α ((beltramiOp b)^[m] F) P).toReal)
          = ENNReal.ofReal Cfin := by
        rw [hCfindef, ENNReal.ofReal_tsum_of_nonneg (fun m => ENNReal.toReal_nonneg) hksum]
      rw [h2, h3]
      exact ENNReal.ofReal_ne_top
    have htend := ENNReal.tendsto_sum_nat_add
      (fun m => Work.CR.Flat.holderNorm k α ((beltramiOp b)^[m] F) P) htsum_fin
    have hev : ∀ᶠ i in atTop,
        (∑' l, Work.CR.Flat.holderNorm k α ((beltramiOp b)^[l + i] F) P)
          < ENNReal.ofReal ε :=
      (tendsto_order.1 htend).2 _ (ENNReal.ofReal_pos.mpr hε)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N, ?_⟩
    intro m m' hm hm'
    rcases le_total m m' with hle | hle
    · have hfun : A m - A m' = fun z => -∑ i ∈ Finset.Ico m m', ((beltramiOp b)^[i] F) z := by
        funext z
        rw [Pi.sub_apply, hAapp, hAapp, Finset.sum_Ico_eq_sub _ hle]
        ring
      rw [hfun]
      rw [show (fun z => -∑ i ∈ Finset.Ico m m', ((beltramiOp b)^[i]) F z)
            = -(fun z => ∑ i ∈ Finset.Ico m m', ((beltramiOp b)^[i]) F z) from by
          funext z; rfl]
      rw [Work.CR.Flat.Holder.holderNorm_neg
        (ContDiffOn.sum (s := Finset.Ico m m') (f := fun i => ((beltramiOp b)^[i]) F)
          (fun i _ => (hkcd i).mono hP'sub)) hP'open.uniqueDiffOn]
      refine (Work.CR.Flat.Holder.holderNorm_sum_le (Finset.Ico m m')
        (fun i _ => (hkcd i).mono hP'sub) hP'open.uniqueDiffOn).trans ?_
      refine (Finset.sum_le_sum fun i _ =>
        Work.CR.Flat.holderNorm_mono_set hPopen hP'open hP'sub k α _).trans ?_
      rw [Finset.sum_Ico_eq_sum_range]
      refine (ENNReal.sum_le_tsum (Finset.range (m' - m))).trans ?_
      have heq : (∑' i, Work.CR.Flat.holderNorm k α ((beltramiOp b)^[m + i] F) P)
          = (∑' i, Work.CR.Flat.holderNorm k α ((beltramiOp b)^[i + m] F) P) :=
        tsum_congr fun i => by rw [Nat.add_comm]
      rw [heq]
      exact le_of_lt (hN m hm)
    · have hfun : A m - A m' = fun z => ∑ i ∈ Finset.Ico m' m, ((beltramiOp b)^[i] F) z := by
        funext z
        rw [Pi.sub_apply, hAapp, hAapp, Finset.sum_Ico_eq_sub _ hle]
      rw [hfun]
      refine (Work.CR.Flat.Holder.holderNorm_sum_le (Finset.Ico m' m)
        (fun i _ => (hkcd i).mono hP'sub) hP'open.uniqueDiffOn).trans ?_
      refine (Finset.sum_le_sum fun i _ =>
        Work.CR.Flat.holderNorm_mono_set hPopen hP'open hP'sub k α _).trans ?_
      rw [Finset.sum_Ico_eq_sum_range]
      refine (ENNReal.sum_le_tsum (Finset.range (m - m'))).trans ?_
      have heq : (∑' i, Work.CR.Flat.holderNorm k α ((beltramiOp b)^[m' + i] F) P)
          = (∑' i, Work.CR.Flat.holderNorm k α ((beltramiOp b)^[i + m'] F) P) :=
        tsum_congr fun i => by rw [Nat.add_comm]
      rw [heq]
      exact le_of_lt (hN m' hm')
  obtain ⟨hle, hcd⟩ := holderNorm_le_of_tendsto (k := k) (α := α) (P := P') hP'open hCfin0
    (fun M => by
      have h2 : A M = fun z => ∑ i ∈ Finset.range M, ((beltramiOp b)^[i] F) z :=
        funext fun z => hAapp M z
      rw [h2]
      exact ContDiffOn.sum (s := Finset.range M) (f := fun i => ((beltramiOp b)^[i]) F)
        (fun i _ => (hkcd i).mono hP'sub))
    hbound hconv hcau
  exact ⟨hcd, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩

end
end Work.NN.Core


set_option maxHeartbeats 800000

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

noncomputable section

variable {n : ℕ}

/-! ## Auxiliary lemmas for the bootstrap -/

/-- The closed polydisc `{z | ∀ j, ‖z j - c j‖ ≤ r j}`. -/
private def closedPolydisc {n : ℕ} (c : Cn n) (r : Fin n → ℝ) : Set (Cn n) := {z | ∀ j, ‖z j - c j‖ ≤ r j}

private lemma closedPolydisc_subset {n : ℕ} {c : Cn n} {r r' : Fin n → ℝ}
    (h : ∀ j, r j < r' j) : closedPolydisc c r ⊆ Work.CR.Flat.polydisc c r' :=
  fun _ hz j => lt_of_le_of_lt (hz j) (h j)

private lemma isCompact_closedPolydisc {n : ℕ} (c : Cn n) (r : Fin n → ℝ) :
    IsCompact (closedPolydisc c r) := by
  have hbdd : closedPolydisc c r ⊆ Metric.closedBall c (∑ j, max (r j) 0) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => le_max_right _ _)).mpr
      fun j => ?_
    calc ‖(z - c) j‖ = ‖z j - c j‖ := by simp
      _ ≤ max (r j) 0 := le_max_of_le_left (hz j)
      _ ≤ ∑ i, max (r i) 0 := Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ j)
  have hclosed : IsClosed (closedPolydisc c r) := by
    have h : closedPolydisc c r = ⋂ j, {z : Cn n | ‖z j - c j‖ ≤ r j} := by
      ext z; simp [closedPolydisc]
    rw [h]
    exact isClosed_iInter fun j =>
      isClosed_le ((continuous_apply j).sub continuous_const).norm continuous_const
  exact IsCompact.of_isClosed_subset (isCompact_closedBall c (∑ j, max (r j) 0)) hclosed hbdd

/-- `C^∞` (finite orders) implies `C^k` for every natural `k`. -/
private lemma contDiff_natCast_of_smooth {n : ℕ} {m : ℕ} {g : Cn n → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ m g :=
  hg.of_le (WithTop.coe_le_coe.mpr le_top)

/-- The comparison `1 ≤ ∞` of the `ContDiff` order. -/
private lemma one_le_smooth : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

/-- `dCoord` of a smooth function is smooth. -/
private lemma contDiff_dCoord {u : Cn n → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (j : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Work.CR.Flat.dCoord j u z) := by
  have h : (fun z => Work.CR.Flat.dCoord j u z) = fun z => dCoordLin j (fderiv ℝ u z) :=
    funext fun z => congrFun (dCoord_eq_comp j u) z
  rw [h]
  exact (dCoordLin j).contDiff.comp (hu.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl)

/-- `dbarCoord` of a smooth function is smooth. -/
private lemma contDiff_dbarCoord_fin {u : Cn n → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (j : Fin n) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => Work.CR.Flat.dbarCoord j u z) := by
  have h : (fun z => Work.CR.Flat.dbarCoord j u z)
      = fun z => Work.CR.Flat.Polydisc.dbarCoordPhi j (fderiv ℝ u z) :=
    funext fun z => congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp j u) z
  rw [h]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi j).contDiff.comp
    (hu.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl)

/-- A smooth function supported inside an open set, times a function which is `C¹` on that open
set, is globally `C¹`. -/
private lemma contDiff_one_mul_of_contDiffOn {χ h : Cn n → ℂ} {U : Set (Cn n)} (hU : IsOpen U)
    (hχ : ContDiff ℝ 1 χ) (hsub : tsupport χ ⊆ U)
    (hh : ContDiffOn ℝ 1 h U) : ContDiff ℝ 1 (fun z => χ z * h z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hh.contDiffAt (hU.mem_nhds (hsub hz)))
  · have hzo : ∀ᶠ w in 𝓝 z, χ w = 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with w hw
      exact image_eq_zero_of_notMem_tsupport hw
    have hev : (fun w => χ w * h w) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
      hzo.mono fun w hw => by simp [hw]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev

/-- A function which vanishes off the topological support of a compactly supported function has
compact support. -/
private lemma hasCompactSupport_of_notMem_tsupport {f χ : Cn n → ℂ} (hχ : HasCompactSupport χ)
    (h : ∀ z, z ∉ tsupport χ → f z = 0) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset hχ (isClosed_tsupport f) (by
    rw [tsupport]
    refine closure_minimal (fun z hz => ?_) (isClosed_tsupport χ)
    simp only [Function.mem_support] at hz
    by_contra hc
    exact hz (h z hc))

/-- A finite sum of compactly supported functions is compactly supported. -/
private lemma hasCompactSupport_finsetSum {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommMonoid Y] {s : Finset ι} {f : ι → X → Y} (h : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h0 : (fun x : X => ∑ i ∈ (∅ : Finset ι), f i x) = fun _ => (0 : Y) := by
      funext x; simp
    rw [h0]
    exact hasCompactSupport_iff_eventuallyEq.mpr (Eventually.of_forall fun x => by simp)
  | insert a s ha ih =>
    have h1 : (fun x : X => ∑ i ∈ insert a s, f i x)
        = (fun x : X => f a x + ∑ i ∈ s, f i x) := by
      funext x; rw [Finset.sum_insert ha]
    rw [h1]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The topological support of `dCoord l χ` is contained in that of `χ`. -/
private lemma tsupport_dCoord_subset {χ : Cn n → ℂ} (l : Fin n) :
    tsupport (fun z => Work.CR.Flat.dCoord l χ z) ⊆ tsupport χ := by
  rw [tsupport]
  refine closure_minimal (fun z hz => ?_) (isClosed_tsupport χ)
  simp only [Function.mem_support] at hz
  by_contra hc
  exact hz (dCoord_eq_zero_of_fderiv_eq_zero (fderiv_eq_zero_of_notMem_tsupport hc) l)

/-- A smooth function whose topological support is contained in a polydisc is compactly
supported. -/
private lemma hasCompactSupport_of_tsupport_subset_polydisc {ψ : Cn n → ℂ} {ρψ : Fin n → ℝ}
    (hψts : tsupport ψ ⊆ Work.CR.Flat.polydisc 0 ρψ) : HasCompactSupport ψ := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Cn n) (∑ j, max (ρψ j) 0))
    (isClosed_tsupport ψ) ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => le_max_right _ _)).mpr fun j => ?_
  have h1 : ‖(z - 0) j‖ = ‖z j‖ := by simp
  rw [h1]
  calc ‖z j‖ ≤ max (ρψ j) 0 :=
        le_max_of_le_left (le_of_lt (by simpa using (Work.CR.Flat.mem_polydisc.mp (hψts hz)) j))
    _ ≤ ∑ i, max (ρψ i) 0 := Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ j)

/-- **The cutoff identity.**  If `χ` is smooth, supported in the open set `U`, if `h` is `C¹` on
`U` and satisfies the Beltrami equation `∂̄_l h = Σ_j c l j ∂_j h` at every point of
`tsupport χ`, then the product `χ h` satisfies the same equation with the error term
`(∂̄_l χ - Σ_j c l j ∂_j χ) h`. -/
private lemma dbarCoord_cutoff_eq {χ h : Cn n → ℂ} {U : Set (Cn n)} (hU : IsOpen U)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hsub : tsupport χ ⊆ U)
    (hh : ContDiffOn ℝ 1 h U) (c : Fin n → Fin n → Cn n → ℂ)
    (heq : ∀ l z, z ∈ tsupport χ → Work.CR.Flat.dbarCoord l h z
      = ∑ j, c l j z * Work.CR.Flat.dCoord j h z) :
    ∀ l z, Work.CR.Flat.dbarCoord l (fun w => χ w * h w) z
      = (∑ j, c l j z * Work.CR.Flat.dCoord j (fun w => χ w * h w) z)
        + (Work.CR.Flat.dbarCoord l χ z - ∑ j, c l j z * Work.CR.Flat.dCoord j χ z) * h z := by
  intro l z
  by_cases hz : z ∈ tsupport χ
  · have hdh : DifferentiableAt ℝ h z :=
      (hh.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt (by norm_num)
    have hdχ : DifferentiableAt ℝ χ z := (hχ.of_le one_le_smooth).contDiffAt.differentiableAt (by norm_num)
    have hfun : (fun w => χ w * h w) = χ * h := by funext w; rfl
    have hml : Work.CR.Flat.dbarCoord l (fun w => χ w * h w) z
        = Work.CR.Flat.dbarCoord l χ z * h z
          + χ z * (∑ j, c l j z * Work.CR.Flat.dCoord j h z) := by
      rw [Work.CR.Flat.Polydisc.dbarCoord_mul l χ h z hdχ hdh, heq l z hz]
    have hdm : ∀ j, Work.CR.Flat.dCoord j (fun w => χ w * h w) z
        = Work.CR.Flat.dCoord j χ z * h z + χ z * Work.CR.Flat.dCoord j h z :=
      fun j => by rw [hfun]; exact dCoord_mul j χ h z hdχ hdh
    have hsum : (∑ j, c l j z * Work.CR.Flat.dCoord j (fun w => χ w * h w) z)
        = (∑ j, c l j z * (Work.CR.Flat.dCoord j χ z * h z))
          + χ z * (∑ j, c l j z * Work.CR.Flat.dCoord j h z) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hdm j]; ring
    have hfirst : (∑ j, c l j z * (Work.CR.Flat.dCoord j χ z * h z))
        = (∑ j, c l j z * Work.CR.Flat.dCoord j χ z) * h z := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hml, hsum, hfirst]; ring
  · have hzo : ∀ᶠ w in 𝓝 z, χ w = 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with w hw
      exact image_eq_zero_of_notMem_tsupport hw
    have hev : (fun w => χ w * h w) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := hzo.mono (fun w hw => by simp [hw])
    have hdW : fderiv ℝ (fun w => χ w * h w) z = 0 := by rw [hev.fderiv_eq]; simp
    have hdχ : fderiv ℝ χ z = 0 := fderiv_eq_zero_of_notMem_tsupport hz
    have h1 : (∑ j, c l j z * Work.CR.Flat.dCoord j (fun w => χ w * h w) z) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [dCoord_eq_zero_of_fderiv_eq_zero hdW j, mul_zero]
    have h2 : Work.CR.Flat.dbarCoord l χ z = 0 := dbarCoord_eq_zero_of_fderiv_eq_zero hdχ l
    have h3 : (∑ j, c l j z * Work.CR.Flat.dCoord j χ z) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [dCoord_eq_zero_of_fderiv_eq_zero hdχ j, mul_zero]
    rw [dbarCoord_eq_zero_of_fderiv_eq_zero hdW l, h1, h2, h3]
    ring

/-- **The cutoff identity for the perturbed operator.**  If `χ` is smooth, supported in the open
set `U`, `h` is `C¹` on `U`, and `h` satisfies the perturbed `∂̄`-equation at every point of
`tsupport χ`, then the perturbed `∂̄` of the product `χ h` is the smooth coefficient
`∂̄_l χ + Lcoef A χ l` times `h`. -/
private lemma dbarCn_cutoff_eq {χ h : Cn n → ℂ} {U : Set (Cn n)} (hU : IsOpen U)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hsub : tsupport χ ⊆ U)
    (hh : ContDiffOn ℝ 1 h U) (A : Cn n → Cn n →L[ℝ] Cn n)
    (heq : ∀ l z, z ∈ tsupport χ →
      dbarCn (JstdCn n + A) h z (Pi.single l 1) = 0) :
    ∀ l z, dbarCn (JstdCn n + A) (fun w => χ w * h w) z (Pi.single l 1)
      = (Work.CR.Flat.dbarCoord l χ z + Lcoef A χ l z) * h z := by
  intro l z
  by_cases hz : z ∈ tsupport χ
  · have hdh : DifferentiableAt ℝ h z :=
      (hh.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt (by norm_num)
    have hdχ : DifferentiableAt ℝ χ z := (hχ.of_le one_le_smooth).contDiffAt.differentiableAt (by norm_num)
    rw [dbarCoef_lin, Work.CR.Flat.Polydisc.dbarCoord_mul l χ h z hdχ hdh]
    have hL : Lcoef A (fun w => χ w * h w) l z = Lcoef A χ l z * h z + χ z * Lcoef A h l z := by
      have hf : (fun w => χ w * h w) = χ * h := by funext w; rfl
      rw [show Lcoef A (fun w => χ w * h w) l z
          = (Complex.I / 2) * fderiv ℝ (χ * h) z (A z (Pi.single l 1)) by
        rw [← hf]; rfl]
      simp only [Lcoef, fderiv_mul hdχ hdh, add_apply, smul_apply, smul_eq_mul]
      ring
    have hkey : Work.CR.Flat.dbarCoord l h z + Lcoef A h l z = 0 := by
      have h := heq l z hz
      rwa [dbarCoef_lin] at h
    rw [hL]
    linear_combination χ z * hkey
  · have hzo : ∀ᶠ w in 𝓝 z, χ w = 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with w hw
      exact image_eq_zero_of_notMem_tsupport hw
    have hdχ : fderiv ℝ χ z = 0 := fderiv_eq_zero_of_notMem_tsupport hz
    have hev : (fun w => χ w * h w) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := hzo.mono (fun w hw => by simp [hw])
    have hdW : fderiv ℝ (fun w => χ w * h w) z = 0 := by rw [hev.fderiv_eq]; simp
    have hLHS : dbarCn (JstdCn n + A) (fun w => χ w * h w) z (Pi.single l 1) = 0 := by
      simp [dbarCn, hdW]
    have hRHS : (Work.CR.Flat.dbarCoord l χ z + Lcoef A χ l z) * h z = 0 := by
      have h1 : Work.CR.Flat.dbarCoord l χ z = 0 := dbarCoord_eq_zero_of_fderiv_eq_zero hdχ l
      have h2 : Lcoef A χ l z = 0 := by simp [Lcoef, hdχ]
      rw [h1, h2, zero_add, zero_mul]
    rw [hLHS, hRHS]

/-- Homogeneity of the Bochner--Martinelli potential in its datum. -/
private lemma bmPotential_const_mul (a : ℂ) (f : Fin n → Cn n → ℂ) :
    Work.CR.Flat.Cauchy.bmPotential (fun j z => a * f j z)
      = fun z => a * Work.CR.Flat.Cauchy.bmPotential f z := by
  funext z
  simp only [Work.CR.Flat.Cauchy.bmPotential, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * (a * f j ζ))
      = ∫ ζ, a * (Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * f j ζ) from
        MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => by ring),
    MeasureTheory.integral_const_mul]

/-- A smooth function whose topological support lies in the polydisc `polydisc 0 ρψ`, times a
function which is `C^m` on that polydisc with finite `C^{m,α}`-norm, is globally `C^m` with finite
`C^{m,α}`-norm. -/
private lemma contDiff_mul_of_smooth_supported {ψ h : Cn n → ℂ} {ρψ : Fin n → ℝ} {m : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hρψ : ∀ j, 0 < ρψ j)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψts : tsupport ψ ⊆ Work.CR.Flat.polydisc 0 ρψ)
    (hh : ContDiffOn ℝ (m : ℕ∞) h (Work.CR.Flat.polydisc 0 ρψ))
    (hhfin : Work.CR.Flat.holderNorm m α h (Work.CR.Flat.polydisc 0 ρψ) < ⊤) :
    ContDiff ℝ m (fun z => ψ z * h z) ∧
      Work.CR.Flat.holderNorm m α (fun z => ψ z * h z) Set.univ < ⊤ := by
  have hPopen : IsOpen (Work.CR.Flat.polydisc 0 ρψ) := Work.CR.Flat.isOpen_polydisc 0 ρψ
  have hψcs : HasCompactSupport ψ := hasCompactSupport_of_tsupport_subset_polydisc hψts
  have hψvan : ∀ z, (∃ j, ρψ j ≤ ‖z j‖) → ψ z = 0 := by
    intro z hz
    by_contra hc
    have hmem : z ∈ tsupport ψ := subset_closure (by simpa [Function.mem_support] using hc)
    obtain ⟨j, hj⟩ := hz
    exact absurd (by simpa using (Work.CR.Flat.mem_polydisc.mp (hψts hmem)) j) (not_lt.mpr hj)
  have hdiff : ContDiff ℝ m (fun z => ψ z * h z) :=
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport hPopen hψ hψts hh
  have hpol : Work.CR.Flat.holderNorm m α (fun z => ψ z * h z)
      (Work.CR.Flat.polydisc 0 ρψ) < ⊤ := by
    obtain ⟨C, _hCpos, hC⟩ := Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
      (Ω := Work.CR.Flat.polydisc 0 ρψ) hPopen.uniqueDiffOn hα0.le (le_of_lt hα1)
      (contDiff_natCast_of_smooth hψ) hψcs
    refine lt_of_le_of_lt (hC h hh) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hhfin
  refine ⟨hdiff, ?_⟩
  refine lt_of_le_of_lt (Work.NN.Core.holderNorm_univ_le_holderNorm_polydisc_of_contDiff_vanishing
    hα0 hρψ hdiff (fun z hz => by rw [hψvan z hz, zero_mul])) hpol

/-- Hypoellipticity of the perturbed `∂̄`-operator for small perturbations: if `A` is smooth and
componentwise `C^{0,α}`-small on the polydisc `polydisc 0 ρ`, `J = JstdCn n + A` is almost complex,
and `h` is a `C¹` solution of `∂̄_J h = 0` on `polydisc 0 ρ`, then `h` is `C^k` on every smaller
polydisc `polydisc 0 ρ'` (`ρ' < ρ`) for every `k`. -/
private theorem dbarCn_smooth_of_small_pert {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hρ'ρ : ∀ j, ρ' j < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiff ℝ m A) → ∀ {ε : ℝ}, ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
          (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
        (∀ z v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        ∀ h : Work.NN.Core.Cn n → ℂ,
          ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ) →
          (∀ j, ∀ z ∈ Work.CR.Flat.polydisc 0 ρ,
            Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) h z (Pi.single j 1) = 0) →
          ∀ k : ℕ, ContDiffOn ℝ k h (Work.CR.Flat.polydisc 0 ρ') := by
  classical
  -- ## geometric data
  set ρ₁ : Fin n → ℝ := fun j => ρ' j + (ρ j - ρ' j) * (3 / 4) with hρ₁def
  have hρ₁pos : ∀ j, 0 < ρ₁ j := fun j => by
    rw [hρ₁def]; nlinarith [hρ' j, hρ'ρ j]
  have hρ₁ρ : ∀ j, ρ₁ j < ρ j := fun j => by
    rw [hρ₁def]; nlinarith [hρ' j, hρ'ρ j]
  have hρ₁ρle : ∀ j, ρ₁ j ≤ ρ j := fun j => le_of_lt (hρ₁ρ j)
  set R : ℕ → Fin n → ℝ := fun k j => ρ' j + (ρ j - ρ' j) / ((k : ℝ) + 1) with hRdef
  have hRpos : ∀ k j, 0 < R k j := fun k j => by
    rw [hRdef]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : 0 < (ρ j - ρ' j) / ((k : ℝ) + 1) := div_pos (by linarith [hρ'ρ j]) h1
    linarith [hρ' j]
  have hRltρ : ∀ k, 1 ≤ k → ∀ j, R k j < ρ j := fun k hk j => by
    rw [hRdef]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (ρ j - ρ' j) / ((k : ℝ) + 1) < ρ j - ρ' j := by
      rw [div_lt_iff₀ h1]
      have hk1 : (1 : ℝ) < (k : ℝ) + 1 := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith
      nlinarith [hρ'ρ j]
    linarith [h2]
  have hRmono : ∀ k j, R (k + 1) j < R k j := fun k j => by
    rw [hRdef]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h3 : (ρ j - ρ' j) / ((k : ℝ) + 1 + 1) < (ρ j - ρ' j) / ((k : ℝ) + 1) := by
      refine div_lt_div_of_pos_left (by linarith [hρ'ρ j]) (by positivity) ?_
      push_cast; linarith
    push_cast
    linarith
  have hR1ρ₁ : ∀ j, R 1 j < ρ₁ j := fun j => by
    rw [hRdef, hρ₁def]; norm_num; nlinarith [hρ'ρ j]
  have hρ'R : ∀ k j, ρ' j < R k j := fun k j => by
    rw [hRdef]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : 0 < (ρ j - ρ' j) / ((k : ℝ) + 1) := div_pos (by linarith [hρ'ρ j]) h1
    linarith
  -- ## the auxiliary polydisc `Q` (support of the base cutoff)
  set Q : Fin n → ℝ := fun j => ρ' j + (ρ j - ρ' j) * (5 / 8) with hQdef
  have hQpos : ∀ j, 0 < Q j := fun j => by rw [hQdef]; nlinarith [hρ' j, hρ'ρ j]
  have hQρ : ∀ j, Q j < ρ j := fun j => by rw [hQdef]; nlinarith [hρ' j, hρ'ρ j]
  have hR1Q : ∀ j, R 1 j < Q j := fun j => by
    rw [hRdef, hQdef]; norm_num; nlinarith [hρ'ρ j]
  have hQρ₁ : ∀ j, Q j < ρ₁ j := fun j => by
    rw [hQdef, hρ₁def]; norm_num; nlinarith [hρ'ρ j]
  -- ## the thresholds
  obtain ⟨εD, hεDpos, CD, hCDpos, hbelt⟩ :=
    exists_beltramiCoef_small_smooth hn hα0 hα1 hρ hρ₁pos hρ₁ρ
  obtain ⟨δe, hδepos, heng⟩ := contDiffOn_of_beltrami_fixedPoint_c0_smooth hn hα0 hα1 hρ
  obtain ⟨δ0, hδ0pos, hbase0⟩ :=
    dbarCoord_finite_of_perturbed_data (n := n) hn hα0 hα1 hρ hQpos hQρ
  set γ : ℂ := Work.CR.Flat.Cauchy.bmGamma n with hγdef
  have hγne : γ ≠ 0 := by
    rw [hγdef]
    exact Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
  set K : ℝ := (‖γ⁻¹‖ + 1) * (CD + 1) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hKCD : ‖γ⁻¹‖ * CD ≤ K := by rw [hKdef]; nlinarith [norm_nonneg γ⁻¹, hCDpos]
  refine ⟨min (min εD δ0) (δe / (2 * K)), ?_, ?_⟩
  · exact lt_min (lt_min hεDpos hδ0pos) (by positivity)
  intro A hA ε hε hsmall hJ h hh1 heq
  have hρ₁mem : ∀ {z : Cn n}, z ∈ Work.CR.Flat.polydisc 0 ρ₁ → z ∈ Work.CR.Flat.polydisc 0 ρ :=
    fun hz => Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρ₁ρ j)) hz
  have hρmem : ∀ {z : Cn n}, z ∈ Work.CR.Flat.polydisc 0 ρ → z ∈ Work.CR.Flat.polydisc 0 ρ :=
    fun hz => hz
  -- replace `ε` by `ε' = max ε 0`
  set ε' : ℝ := max ε 0 with hε'def
  have hε'0 : 0 ≤ ε' := le_max_right _ _
  have hε'εD : ε' ≤ εD := by
    rcases le_total ε 0 with hh | hh
    · rw [hε'def, max_eq_right hh]; exact hεDpos.le
    · rw [hε'def, max_eq_left hh]
      exact le_trans hε (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε'δ0 : ε' ≤ δ0 := by
    rcases le_total ε 0 with hh | hh
    · rw [hε'def, max_eq_right hh]; exact hδ0pos.le
    · rw [hε'def, max_eq_left hh]
      exact le_trans hε (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε'δe : ε' ≤ δe / (2 * K) := by
    rcases le_total ε 0 with hh | hh
    · rw [hε'def, max_eq_right hh]; positivity
    · rw [hε'def, max_eq_left hh]; exact le_trans hε (min_le_right _ _)
  have hsmall' : ∀ i j, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
      (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε' :=
    fun i j => (hsmall i j).trans (ENNReal.ofReal_le_ofReal (le_max_left ε 0))
  -- the Beltrami coefficient of `A`
  obtain ⟨c, hcsm, hccs, hcsupp, hcnorm, hceq⟩ := hbelt A ε' hε'0 hε'εD hA hsmall'
  -- the engine's coefficient `b = γ⁻¹ • c`
  set bb : Fin n → Fin n → Cn n → ℂ := fun l j z => γ⁻¹ * c l j z with hbbdef
  have hbbsm : ∀ l j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bb l j) := fun l j =>
    contDiff_const.mul (hcsm l j)
  have hbbcs : ∀ l j, HasCompactSupport (bb l j) := fun l j => (hccs l j).mul_left
  have hbbsupp : ∀ l j z, bb l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ := by
    intro l j z hz
    refine hcsupp l j z (fun h0 => hz ?_)
    simp [hbbdef, h0]
  have hbbnorm : ∀ l j, Work.CR.Flat.holderNorm 0 α (bb l j) Set.univ ≤ ENNReal.ofReal δe := by
    intro l j
    have h1 : Work.CR.Flat.holderNorm 0 α (bb l j) Set.univ
        ≤ ENNReal.ofReal ‖γ⁻¹‖ * Work.CR.Flat.holderNorm 0 α (c l j) Set.univ := by
      rw [hbbdef]
      exact Work.NN.Core.holderNorm_const_mul_le uniqueDiffOn_univ γ⁻¹ (c l j)
    have h2 : ENNReal.ofReal ‖γ⁻¹‖ * Work.CR.Flat.holderNorm 0 α (c l j) Set.univ
        ≤ ENNReal.ofReal ‖γ⁻¹‖ * ENNReal.ofReal (CD * ε') :=
      mul_le_mul_of_nonneg_left (hcnorm l j) bot_le
    have h3 : ENNReal.ofReal ‖γ⁻¹‖ * ENNReal.ofReal (CD * ε')
        = ENNReal.ofReal (‖γ⁻¹‖ * (CD * ε')) := (ENNReal.ofReal_mul (norm_nonneg γ⁻¹)).symm
    have h4 : ‖γ⁻¹‖ * (CD * ε') ≤ δe := by
      calc ‖γ⁻¹‖ * (CD * ε') = (‖γ⁻¹‖ * CD) * ε' := by ring
        _ ≤ K * (δe / (2 * K)) := mul_le_mul hKCD hε'δe hε'0 (le_of_lt hKpos)
        _ = δe / 2 := by field_simp
        _ ≤ δe := by linarith [hδepos]
    calc Work.CR.Flat.holderNorm 0 α (bb l j) Set.univ
        ≤ ENNReal.ofReal ‖γ⁻¹‖ * Work.CR.Flat.holderNorm 0 α (c l j) Set.univ := h1
      _ ≤ ENNReal.ofReal ‖γ⁻¹‖ * ENNReal.ofReal (CD * ε') := h2
      _ = ENNReal.ofReal (‖γ⁻¹‖ * (CD * ε')) := h3
      _ ≤ ENNReal.ofReal δe := ENNReal.ofReal_le_ofReal h4
  -- ## base case: `h` is `C^{1,α}` on `polydisc 0 (R 1)`
  obtain ⟨χ₀, V₀, hχ₀sm, hχ₀cs, hχ₀supp, hV₀open, hKV₀, hχ₀one⟩ :=
    exists_contDiff_bump_of_isCompact_subset (K := closedPolydisc (0 : Cn n) (R 1))
      (U := Work.CR.Flat.polydisc 0 Q) (isCompact_closedPolydisc _ _)
      (Work.CR.Flat.isOpen_polydisc 0 Q) (closedPolydisc_subset hR1Q)
  have hχ₀suppρ : tsupport χ₀ ⊆ Work.CR.Flat.polydisc 0 ρ :=
    fun z hz => Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hQρ j)) (hχ₀supp hz)
  have hχ₀suppρ₁ : tsupport χ₀ ⊆ Work.CR.Flat.polydisc 0 ρ₁ :=
    fun z hz => Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hQρ₁ j)) (hχ₀supp hz)
  have hχ₀one1 : ∀ z, z ∈ Work.CR.Flat.polydisc 0 (R 1) → χ₀ z = 1 :=
    fun z hz => hχ₀one z (hKV₀ fun j => le_of_lt (hz j))
  have hχ₀van : ∀ z, z ∉ Work.CR.Flat.polydisc 0 Q → χ₀ z = 0 := by
    intro z hz
    rw [Work.CR.Flat.mem_polydisc] at hz
    push Not at hz
    obtain ⟨i, hi⟩ := hz
    by_contra hc
    exact absurd ((Work.CR.Flat.mem_polydisc.mp (hχ₀supp (subset_closure
      (by simpa [Function.mem_support] using hc)))) i) (not_lt.mpr (by simpa using hi))
  set coef : Fin n → Cn n → ℂ := fun m z => Work.CR.Flat.dbarCoord m χ₀ z + Lcoef A χ₀ m z
    with hcoefdef
  have hcoefsm : ∀ m, ContDiff ℝ 1 (coef m) := by
    intro m
    rw [hcoefdef]
    refine ((contDiff_dbarCoord_fin hχ₀sm m).of_le one_le_smooth).add ?_
    have h1 : ContDiff ℝ 1 (fun z : Cn n =>
        fderiv ℝ χ₀ z (A z (Pi.single m (1 : ℂ)))) :=
      ((hχ₀sm.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl).of_le one_le_smooth).clm_apply
        ((hA 1).clm_apply contDiff_const)
    exact contDiff_const.mul h1
  have hcoefts : ∀ m, tsupport (coef m) ⊆ Work.CR.Flat.polydisc 0 ρ := by
    intro m
    have hsub : tsupport (coef m) ⊆ tsupport χ₀ := by
      rw [tsupport]
      refine closure_minimal (fun z hz => ?_) (isClosed_tsupport χ₀)
      simp only [Function.mem_support] at hz
      by_contra hc
      have hfd : fderiv ℝ χ₀ z = 0 := fderiv_eq_zero_of_notMem_tsupport hc
      refine hz ?_
      have h1 : Work.CR.Flat.dbarCoord m χ₀ z = 0 := dbarCoord_eq_zero_of_fderiv_eq_zero hfd m
      have h2 : Lcoef A χ₀ m z = 0 := by simp [Lcoef, hfd]
      show coef m z = 0
      rw [hcoefdef]
      simp only [Pi.add_apply]
      rw [h1, h2, add_zero]
    exact hsub.trans hχ₀suppρ
  have hbase1 : Work.CR.Flat.holderNorm 1 α h (Work.CR.Flat.polydisc 0 (R 1)) < ⊤ := by
    have hW1 : ContDiff ℝ 1 (fun w => χ₀ w * h w) :=
      contDiff_one_mul_of_contDiffOn (Work.CR.Flat.isOpen_polydisc 0 ρ) (hχ₀sm.of_le one_le_smooth)
        hχ₀suppρ hh1
    have hWcs : HasCompactSupport (fun w => χ₀ w * h w) := hχ₀cs.mul_right
    have hdata : ∀ m, Work.CR.Flat.holderNorm 0 α (fun z => dbarCn (JstdCn n + A)
        (fun w => χ₀ w * h w) z (Pi.single m 1)) Set.univ < ⊤ := by
      intro m
      have hid : (fun z => dbarCn (JstdCn n + A) (fun w => χ₀ w * h w) z (Pi.single m 1))
          = fun z => coef m z * h z := by
        funext z
        exact dbarCn_cutoff_eq (Work.CR.Flat.isOpen_polydisc 0 ρ) hχ₀sm hχ₀suppρ hh1 A
          (fun l z hz => heq l z (hρ₁mem (hχ₀suppρ₁ hz))) m z
      rw [hid]
      exact lt_top_iff_ne_top.mpr
        (Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport' (X := Cn n)
          hα0.le (le_of_lt hα1)
          (contDiff_one_mul_of_contDiffOn (Work.CR.Flat.isOpen_polydisc 0 ρ) (hcoefsm m)
            (hcoefts m) hh1)
          ((hasCompactSupport_of_tsupport_subset_polydisc (hcoefts m)).mul_right))
    have hflat := hbase0 hε'0 hε'δ0 hsmall' (fun w => χ₀ w * h w) hW1 hWcs
      (fun z hz => by
        show χ₀ z * h z = 0
        have hzQ : z ∉ Work.CR.Flat.polydisc 0 Q := fun h =>
          hz.elim fun i hi => absurd (h i) (not_lt.mpr (by simpa using hi))
        rw [hχ₀van z hzQ, zero_mul]) hdata
    have hflatfin : ∀ l, Work.CR.Flat.holderNorm 0 α
        (fun z => Work.CR.Flat.dbarCoord l (fun w => χ₀ w * h w) z) Set.univ < ⊤ := hflat
    have hdc : ∀ l, ContDiff ℝ 0 (fun z => Work.CR.Flat.dbarCoord l (fun w => χ₀ w * h w) z) := by
      intro l
      have hfd : Continuous (fderiv ℝ (fun w => χ₀ w * h w)) :=
        hW1.continuous_fderiv (by norm_num)
      have h : (fun z => Work.CR.Flat.dbarCoord l (fun w => χ₀ w * h w) z)
          = fun z => Work.CR.Flat.Polydisc.dbarCoordPhi l (fderiv ℝ (fun w => χ₀ w * h w) z) :=
        funext fun z => congrFun
          (Work.CR.Flat.Polydisc.dbarCoord_eq_comp l (fun w => χ₀ w * h w)) z
      rw [h]
      exact contDiff_zero.mpr ((Work.CR.Flat.Polydisc.dbarCoordPhi l).continuous.comp hfd)
    have hdcs : ∀ l, HasCompactSupport (fun z => Work.CR.Flat.dbarCoord l (fun w => χ₀ w * h w) z) := by
      intro l
      refine hasCompactSupport_of_notMem_tsupport hWcs (fun z hz => ?_)
      exact dbarCoord_eq_zero_of_fderiv_eq_zero (fderiv_eq_zero_of_notMem_tsupport hz) l
    have hdcvan : ∀ l z, (∃ i, Q i ≤ ‖z i‖) →
        Work.CR.Flat.dbarCoord l (fun w => χ₀ w * h w) z = 0 := by
      intro l z hz
      have hzQ : z ∉ Work.CR.Flat.polydisc 0 Q := fun h =>
        hz.elim fun i hi => absurd (h i) (not_lt.mpr (by simpa using hi))
      by_cases hzt : z ∈ tsupport χ₀
      · exact absurd (hχ₀supp hzt) hzQ
      · have hzo : χ₀ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hzt
        have hev : (fun w => χ₀ w * h w) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
          hzo.mono (fun w hw => by simp [hw])
        exact dbarCoord_eq_zero_of_fderiv_eq_zero (by rw [hev.fderiv_eq]; simp) l
    obtain ⟨_Cp, _hCppos, hpot⟩ := bmPotential_gain (n := n) hn hα0 hα1 hQpos 0
    have hpotfin : Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential
        (fun l z => Work.CR.Flat.dbarCoord l (fun w => χ₀ w * h w) z))
        (Work.CR.Flat.polydisc 0 Q) < ⊤ := by
      refine lt_of_le_of_lt (hpot (fun l z => Work.CR.Flat.dbarCoord l (fun w => χ₀ w * h w) z)
        (fun l => hdc l) hdcs hflatfin hdcvan).2 ?_
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun l _ => hflatfin l)
    have hEqOn : ∀ z ∈ Work.CR.Flat.polydisc 0 Q, (fun w => χ₀ w * h w) z
        = (γ)⁻¹ * Work.CR.Flat.Cauchy.bmPotential
            (fun l y => Work.CR.Flat.dbarCoord l (fun w => χ₀ w * h w) y) z := by
      intro z _
      have hh := Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul (n := n) hn hW1 hWcs z
      rw [← hh, ← mul_assoc, inv_mul_cancel₀ hγne, one_mul]
    have hWfin : Work.CR.Flat.holderNorm 1 α (fun w => χ₀ w * h w)
        (Work.CR.Flat.polydisc 0 Q) < ⊤ := by
      rw [Work.NN.Core.holderNorm_congr hEqOn]
      refine lt_of_le_of_lt (Work.NN.Core.holderNorm_const_mul_le
        (Work.CR.Flat.isOpen_polydisc 0 Q).uniqueDiffOn (γ)⁻¹ _) ?_
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpotfin
    refine lt_of_le_of_lt ?_ hWfin
    rw [Work.NN.Core.holderNorm_congr (k := 1) (α := α) (f := h)
      (g := fun w => χ₀ w * h w) (Ω := Work.CR.Flat.polydisc 0 (R 1))
      (fun z hz => by rw [hχ₀one1 z hz, one_mul])]
    exact Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 Q)
      (Work.CR.Flat.isOpen_polydisc 0 (R 1)) (Work.CR.Flat.polydisc_mono fun j => le_of_lt (hR1Q j))
      1 α (fun w => χ₀ w * h w)
  -- ## the tower
  have key : ∀ m : ℕ, 1 ≤ m →
      ContDiffOn ℝ (m : ℕ∞) h (Work.CR.Flat.polydisc 0 (R m)) ∧
        Work.CR.Flat.holderNorm m α h (Work.CR.Flat.polydisc 0 (R m)) < ⊤ := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        exact ⟨hh1.mono (Work.CR.Flat.polydisc_mono fun j => le_of_lt (hRltρ 1 le_rfl j)), hbase1⟩
      · obtain ⟨hsm_m, hfin_m⟩ := ih hmpos
        -- the cutoff of this step
        obtain ⟨χ, V, hχsm, hχcs, hχsupp, hVopen, hKV, hχone⟩ :=
          exists_contDiff_bump_of_isCompact_subset
            (K := closedPolydisc (0 : Cn n) (R (m + 1)))
            (U := Work.CR.Flat.polydisc 0 (R m))
            (isCompact_closedPolydisc _ _) (Work.CR.Flat.isOpen_polydisc 0 (R m))
            (closedPolydisc_subset fun j => hRmono m j)
        have hχsuppρ : tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρ :=
          fun z hz => Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hRltρ m hmpos j)) (hχsupp hz)
        have hχsuppρ₁ : tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρ₁ := by
          refine fun z hz => Work.CR.Flat.polydisc_mono (fun j => ?_) (hχsupp hz)
          have h1 : R m j < ρ₁ j := by
            rw [hRdef, hρ₁def]
            have h2 : (ρ j - ρ' j) / ((m : ℝ) + 1) ≤ (ρ j - ρ' j) / 2 := by
              refine div_le_div_of_nonneg_left (by linarith [hρ'ρ j]) (by norm_num) ?_
              have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
              linarith
            nlinarith [h2, hρ'ρ j]
          exact le_of_lt h1
        have hχone' : ∀ z, z ∈ Work.CR.Flat.polydisc 0 (R (m + 1)) → χ z = 1 :=
          fun z hz => hχone z (hKV fun j => le_of_lt (hz j))
        -- the error coefficient `ψ` and the datum `G = ψ h`
        set ψ : Fin n → Cn n → ℂ := fun l z => Work.CR.Flat.dbarCoord l χ z
            - ∑ j, c l j z * Work.CR.Flat.dCoord j χ z with hψdef
        set G : Fin n → Cn n → ℂ := fun l z => ψ l z * h z with hGdef
        have hψsm : ∀ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ l) := by
          intro l
          rw [hψdef]
          refine (contDiff_dbarCoord_fin hχsm l).sub ?_
          exact ContDiff.sum fun j _ => (hcsm l j).mul (contDiff_dCoord hχsm j)
        have hψts : ∀ l, tsupport (ψ l) ⊆ Work.CR.Flat.polydisc 0 (R m) := by
          intro l
          have hsub : tsupport (ψ l) ⊆ tsupport χ := by
            rw [tsupport]
            refine closure_minimal (fun z hz => ?_) (isClosed_tsupport χ)
            simp only [Function.mem_support] at hz
            by_contra hc
            have hfd : fderiv ℝ χ z = 0 := fderiv_eq_zero_of_notMem_tsupport hc
            refine hz ?_
            rw [hψdef]
            simp only [Pi.sub_apply, Finset.sum_apply]
            rw [dbarCoord_eq_zero_of_fderiv_eq_zero hfd l,
              Finset.sum_eq_zero (fun j _ => by rw [dCoord_eq_zero_of_fderiv_eq_zero hfd j, mul_zero])]
            simp
          exact hsub.trans hχsupp
        have hGsm : ∀ l, ContDiff ℝ m (G l) := fun l =>
          (contDiff_mul_of_smooth_supported (n := n) hα0 hα1 (hRpos m) (hψsm l) (hψts l)
            hsm_m hfin_m).1
        have hGfin : ∀ l, Work.CR.Flat.holderNorm m α (G l) Set.univ < ⊤ := fun l =>
          (contDiff_mul_of_smooth_supported (n := n) hα0 hα1 (hRpos m) (hψsm l) (hψts l)
            hsm_m hfin_m).2
        have hGcs : ∀ l, HasCompactSupport (G l) := fun l =>
          (hasCompactSupport_of_tsupport_subset_polydisc (hψts l)).mul_right
        have hGvan : ∀ l z, (∃ i, ρ i ≤ ‖z i‖) → G l z = 0 := by
          intro l z hz
          show ψ l z * h z = 0
          have h1 : z ∉ Work.CR.Flat.polydisc 0 (R m) := fun h => hz.elim fun i hi =>
            absurd (h i) (not_lt.mpr (by simpa using le_trans (le_of_lt (hRltρ m hmpos i)) hi))
          have h2 : z ∉ tsupport (ψ l) := fun hc => h1 (hψts l hc)
          rw [image_eq_zero_of_notMem_tsupport h2, zero_mul]
        -- `F = γ⁻¹ T(G)`
        set F : Cn n → ℂ := fun z => (γ)⁻¹ * Work.CR.Flat.Cauchy.bmPotential G z with hFdef
        obtain ⟨Cp, _hCppos, hpotG⟩ := bmPotential_gain (n := n) hn hα0 hα1 hρ m
        have hpG := hpotG G hGsm hGcs hGfin hGvan
        have hFsm : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞) F (Work.CR.Flat.polydisc 0 ρ) := by
          rw [hFdef]
          simpa only [smul_eq_mul] using hpG.1.const_smul ((γ)⁻¹ : ℂ)
        have hFfin : Work.CR.Flat.holderNorm (m + 1) α F (Work.CR.Flat.polydisc 0 ρ) < ⊤ := by
          rw [hFdef]
          refine lt_of_le_of_lt (Work.NN.Core.holderNorm_const_mul_le
            (Work.CR.Flat.isOpen_polydisc 0 ρ).uniqueDiffOn (γ)⁻¹ _) ?_
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
          have hb := lt_of_le_of_lt hpG.2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.sum_lt_top.mpr fun l _ => hGfin l))
          simpa only [Pi.zero_apply] using hb
        -- the cutoff identity
        have hcut : ∀ l z, Work.CR.Flat.dbarCoord l (fun w => χ w * h w) z
            = (∑ j, c l j z * Work.CR.Flat.dCoord j (fun w => χ w * h w) z) + G l z := by
          intro l z
          have h := dbarCoord_cutoff_eq (Work.CR.Flat.isOpen_polydisc 0 ρ) hχsm hχsuppρ hh1 c
            (fun l z hz => hceq h z (hχsuppρ₁ hz)
              (fun k => heq k z (hρ₁mem (hχsuppρ₁ hz))) l) l z
          rw [h, hGdef, hψdef]
        -- the fixed point equation
        have hWu1 : ContDiff ℝ 1 (fun w => χ w * h w) :=
          contDiff_one_mul_of_contDiffOn (Work.CR.Flat.isOpen_polydisc 0 ρ) (hχsm.of_le one_le_smooth)
            hχsuppρ hh1
        have hWcs : HasCompactSupport (fun w => χ w * h w) := hχcs.mul_right
        have hWufin : Work.CR.Flat.holderNorm 1 α (fun w => χ w * h w)
            (Work.CR.Flat.polydisc 0 ρ) < ⊤ := by
          have hbig : Work.CR.Flat.holderNorm m α (fun w => χ w * h w) Set.univ < ⊤ :=
            (contDiff_mul_of_smooth_supported (n := n) hα0 hα1 (hRpos m) hχsm hχsupp hsm_m
              hfin_m).2
          exact lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_set isOpen_univ
            (Work.CR.Flat.isOpen_polydisc 0 ρ) (fun x _ => trivial) 1 α _)
            (lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_k hmpos α _ Set.univ) hbig)
        have hWeq : ∀ z ∈ Work.CR.Flat.polydisc 0 ρ, (fun w => χ w * h w) z
            = Work.CR.Flat.Cauchy.bmPotential (fun l y => ∑ j, bb l j y
                * Work.CR.Flat.dCoord j (fun w => χ w * h w) y) z + F z := by
          intro z _
          set fdat : Fin n → Cn n → ℂ := fun l y => ∑ j, c l j y
              * Work.CR.Flat.dCoord j (fun w => χ w * h w) y with hfdatdef
          set f2 : Fin n → Cn n → ℂ := fun l y => ∑ j, bb l j y
              * Work.CR.Flat.dCoord j (fun w => χ w * h w) y with hf2def
          have hPom := Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul (n := n) hn hWu1 hWcs z
          have hfdc : Continuous (fderiv ℝ (fun w => χ w * h w)) :=
            hWu1.continuous_fderiv (by norm_num)
          have hdcj : ∀ j, Continuous (fun y => Work.CR.Flat.dCoord j (fun w => χ w * h w) y) := by
            intro j
            have h1 : (fun y => Work.CR.Flat.dCoord j (fun w => χ w * h w) y)
                = fun y => dCoordLin j (fderiv ℝ (fun w => χ w * h w) y) :=
              funext fun y => congrFun (dCoord_eq_comp j (fun w => χ w * h w)) y
            rw [h1]
            exact (dCoordLin j).continuous.comp hfdc
          have hcont1 : ∀ l, Continuous (fdat l) := fun l =>
            continuous_finsetSum _ fun j _ => (hcsm l j).continuous.mul (hdcj j)
          have hcontG : ∀ l, Continuous (G l) := fun l => (hGsm l).continuous
          have hcs1 : ∀ l, HasCompactSupport (fdat l) := fun l =>
            hasCompactSupport_finsetSum fun j _ => (hccs l j).mul_right
          have hcsG : ∀ l, HasCompactSupport (G l) := hGcs
          have hAB : (fun l y => Work.CR.Flat.dbarCoord l (fun w => χ w * h w) y)
              = fdat + G := by
            funext l y; exact hcut l y
          have hsplit : Work.CR.Flat.Cauchy.bmGamma n * (fun w => χ w * h w) z
              = Work.CR.Flat.Cauchy.bmPotential fdat z
                + Work.CR.Flat.Cauchy.bmPotential G z := by
            rw [hPom, hAB,
              Work.NN.Core.bmPotential_add_of_cont (n := n) hn hcont1 hcontG hcs1 hcsG]
            rfl
          have hGfac : Work.CR.Flat.Cauchy.bmPotential G z = γ * F z := by
            show Work.CR.Flat.Cauchy.bmPotential G z
              = γ * (γ⁻¹ * Work.CR.Flat.Cauchy.bmPotential G z)
            rw [mul_inv_cancel_left₀ hγne]
          have hcbb : ∀ l j y, c l j y = γ * bb l j y := by
            intro l j y
            rw [hbbdef]
            exact (mul_inv_cancel_left₀ hγne (c l j y)).symm
          have hffac : Work.CR.Flat.Cauchy.bmPotential fdat z
              = γ * Work.CR.Flat.Cauchy.bmPotential f2 z := by
            have hfdef2 : fdat = fun l y => γ * (∑ j, bb l j y
                * Work.CR.Flat.dCoord j (fun w => χ w * h w) y) := by
              funext l y
              rw [hfdatdef]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hcbb l j y]; ring
            rw [hfdef2]
            exact congrFun (Work.NN.Core.bmPotential_const_mul (n := n) γ f2) z
          have hPom2 : Work.CR.Flat.Cauchy.bmGamma n * (fun w => χ w * h w) z
              = γ * (Work.CR.Flat.Cauchy.bmPotential f2 z + F z) := by
            rw [hsplit, hffac, hGfac]
            ring_nf
          exact mul_left_cancel₀ hγne hPom2

        -- the engine
        obtain ⟨hWsm, hWfin⟩ := heng (hRpos (m + 1)) (fun j => hRltρ (m + 1) (by omega) j) (m + 1)
          (by omega) bb F (fun w => χ w * h w) hbbsm hbbcs hbbsupp hbbnorm hFsm hFfin hWu1.contDiffOn hWufin hWeq
        refine ⟨?_, ?_⟩
        · exact hWsm.congr (fun z hz => by rw [hχone' z hz, one_mul])
        · rw [Work.NN.Core.holderNorm_congr (k := m + 1) (α := α) (f := h)
            (g := fun w => χ w * h w) (Ω := Work.CR.Flat.polydisc 0 (R (m + 1)))
            (fun z hz => by rw [hχone' z hz, one_mul])]
          exact hWfin
  -- ## conclusion
  intro k
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact contDiffOn_zero.mpr ((hh1.mono (Work.CR.Flat.polydisc_mono fun j =>
      le_of_lt (hρ'ρ j))).continuousOn)
  · exact (key k hkpos).1.mono (Work.CR.Flat.polydisc_mono fun j => le_of_lt (hρ'R k j))

end

end Work.NN.Core


/-!
# The cutoff identity for the Beltrami system with a source term

...
-/

namespace Work.NN.Final

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

noncomputable section

/-- **The cutoff identity with a source.**  If `χ` is smooth and supported in the open set `U`,
`h` is `C¹` on `U`, and at every point of `tsupport χ` the Beltrami system with source
`∂̄_l h = Σ_j c l j ∂_j h + S_l` holds, then the product `χ h` satisfies the same system with the
extra term `(∂̄_l χ - Σ_j c l j ∂_j χ) h` and the source multiplied by `χ`. -/
private lemma dbarCoord_cutoff_eq_source {n : ℕ} {χ h : Work.NN.Core.Cn n → ℂ}
    {U : Set (Work.NN.Core.Cn n)} (hU : IsOpen U)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hsub : tsupport χ ⊆ U)
    (hh : ContDiffOn ℝ 1 h U) (c : Fin n → Fin n → Work.NN.Core.Cn n → ℂ)
    (S : Fin n → Work.NN.Core.Cn n → ℂ)
    (heq : ∀ l z, z ∈ tsupport χ → Work.CR.Flat.dbarCoord l h z
      = (∑ j, c l j z * Work.CR.Flat.dCoord j h z) + S l z) :
    ∀ l z, Work.CR.Flat.dbarCoord l (fun w => χ w * h w) z
      = (∑ j, c l j z * Work.CR.Flat.dCoord j (fun w => χ w * h w) z)
        + (Work.CR.Flat.dbarCoord l χ z - ∑ j, c l j z * Work.CR.Flat.dCoord j χ z) * h z
        + χ z * S l z := by
  intro l z
  by_cases hz : z ∈ tsupport χ
  · have hdh : DifferentiableAt ℝ h z :=
      (hh.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt (by norm_num)
    have hdχ : DifferentiableAt ℝ χ z :=
      (hχ.of_le Work.NN.Core.one_le_smooth).contDiffAt.differentiableAt (by norm_num)
    have hfun : (fun w => χ w * h w) = χ * h := by funext w; rfl
    have hml : Work.CR.Flat.dbarCoord l (fun w => χ w * h w) z
        = Work.CR.Flat.dbarCoord l χ z * h z
          + χ z * ((∑ j, c l j z * Work.CR.Flat.dCoord j h z) + S l z) := by
      rw [Work.CR.Flat.Polydisc.dbarCoord_mul l χ h z hdχ hdh, heq l z hz]
    have hdm : ∀ j, Work.CR.Flat.dCoord j (fun w => χ w * h w) z
        = Work.CR.Flat.dCoord j χ z * h z + χ z * Work.CR.Flat.dCoord j h z :=
      fun j => by rw [hfun]; exact Work.NN.Core.dCoord_mul j χ h z hdχ hdh
    have hsum : (∑ j, c l j z * Work.CR.Flat.dCoord j (fun w => χ w * h w) z)
        = (∑ j, c l j z * (Work.CR.Flat.dCoord j χ z * h z))
          + χ z * (∑ j, c l j z * Work.CR.Flat.dCoord j h z) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hdm j]; ring
    have hfirst : (∑ j, c l j z * (Work.CR.Flat.dCoord j χ z * h z))
        = (∑ j, c l j z * Work.CR.Flat.dCoord j χ z) * h z := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hml, hsum, hfirst]; ring
  · have hzo : ∀ᶠ w in 𝓝 z, χ w = 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with w hw
      exact image_eq_zero_of_notMem_tsupport hw
    have hev : (fun w => χ w * h w) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
      hzo.mono (fun w hw => by simp [hw])
    have hdW : fderiv ℝ (fun w => χ w * h w) z = 0 := by rw [hev.fderiv_eq]; simp
    have hdχ : fderiv ℝ χ z = 0 := Work.NN.Core.fderiv_eq_zero_of_notMem_tsupport hz
    have h1 : (∑ j, c l j z * Work.CR.Flat.dCoord j (fun w => χ w * h w) z) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [Work.NN.Core.dCoord_eq_zero_of_fderiv_eq_zero hdW j, mul_zero]
    have h2 : Work.CR.Flat.dbarCoord l χ z = 0 := Work.NN.Core.dbarCoord_eq_zero_of_fderiv_eq_zero hdχ l
    have h3 : (∑ j, c l j z * Work.CR.Flat.dCoord j χ z) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [Work.NN.Core.dCoord_eq_zero_of_fderiv_eq_zero hdχ j, mul_zero]
    have h4 : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
    rw [Work.NN.Core.dbarCoord_eq_zero_of_fderiv_eq_zero hdW l, h1, h2, h3, h4]
    ring

end

end Work.NN.Final


/-!
# The smoothness tower for the Beltrami system with a source

Adaptation of the tower in `Work.NN.Core.dbarCn_smooth_of_small_pert` to the inhomogeneous
(decoupled) Beltrami system `∂̄_l h = Σ_j c l j ∂_j h + S_l`.
-/

namespace Work.NN.Final

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

noncomputable section

/-- **The `C^{k}`-tower for the Beltrami system with a source.**  If `c` is smooth, compactly
supported in `polydisc 0 ρ` and `C^{0,α}`-small, if `S` is smooth, and if `h ∈ C¹` with finite
`C^{1,α}`-norm on `polydisc 0 ρ` solves `∂̄_l h = Σ_j c l j ∂_j h + S_l` there, then `h` is `C^k`
on every strictly smaller polydisc `polydisc 0 ρ'`. -/
private theorem beltrami_tower_source {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρs ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hρ'ρs : ∀ j, ρ' j < ρs j)
    (hρsρ : ∀ j, ρs j ≤ ρ j) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (c : Fin n → Fin n → Work.NN.Core.Cn n → ℂ) (S : Fin n → Work.NN.Core.Cn n → ℂ)
        (h : Work.NN.Core.Cn n → ℂ),
        (∀ l j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c l j)) →
        (∀ l j, HasCompactSupport (c l j)) →
        (∀ l j z, c l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        (∀ l j, Work.CR.Flat.holderNorm 0 α (c l j) Set.univ ≤ ENNReal.ofReal δ) →
        (∀ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (S l)) →
        ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ) →
        Work.CR.Flat.holderNorm 1 α h (Work.CR.Flat.polydisc 0 ρ) < ⊤ →
        (∀ l z, z ∈ Work.CR.Flat.polydisc 0 ρs →
          Work.CR.Flat.dbarCoord l h z = (∑ j, c l j z * Work.CR.Flat.dCoord j h z) + S l z) →
        ∀ k : ℕ, ContDiffOn ℝ k h (Work.CR.Flat.polydisc 0 ρ') := by
  classical
  -- ## the descending chain of polydiscs
  set R : ℕ → Fin n → ℝ := fun k j => ρ' j + (ρs j - ρ' j) / ((k : ℝ) + 1) with hRdef
  have hRpos : ∀ k j, 0 < R k j := fun k j => by
    rw [hRdef]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : 0 < (ρs j - ρ' j) / ((k : ℝ) + 1) := div_pos (by linarith [hρ'ρs j]) h1
    linarith [hρ' j]
  have hRltρs : ∀ k, 1 ≤ k → ∀ j, R k j < ρs j := fun k hk j => by
    rw [hRdef]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (ρs j - ρ' j) / ((k : ℝ) + 1) < ρs j - ρ' j := by
      rw [div_lt_iff₀ h1]
      have hk1 : (1 : ℝ) < (k : ℝ) + 1 := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith
      nlinarith [hρ'ρs j]
    linarith [h2]
  have hRmono : ∀ k j, R (k + 1) j < R k j := fun k j => by
    rw [hRdef]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h3 : (ρs j - ρ' j) / ((k : ℝ) + 1 + 1) < (ρs j - ρ' j) / ((k : ℝ) + 1) := by
      refine div_lt_div_of_pos_left (by linarith [hρ'ρs j]) (by positivity) ?_
      push_cast; linarith
    push_cast
    linarith
  have hρ'R : ∀ k j, ρ' j < R k j := fun k j => by
    rw [hRdef]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : 0 < (ρs j - ρ' j) / ((k : ℝ) + 1) := div_pos (by linarith [hρ'ρs j]) h1
    linarith [hρ' j]
  -- ## the engine
  obtain ⟨δe, hδepos, heng⟩ :=
    Work.NN.Core.contDiffOn_of_beltrami_fixedPoint_c0_smooth (n := n) hn hα0 hα1 hρ
  set γ : ℂ := Work.CR.Flat.Cauchy.bmGamma n with hγdef
  have hγne : γ ≠ 0 := by
    rw [hγdef]
    exact Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
  set δ : ℝ := δe / (‖γ⁻¹‖ + 1) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  refine ⟨δ, hδpos, ?_⟩
  intro c S h hcsm hccs hcsupp hcnorm hSsm hh1 hhfin heq
  -- ## the coefficient `bb = γ⁻¹ • c`
  set bb : Fin n → Fin n → Work.NN.Core.Cn n → ℂ := fun l j z => γ⁻¹ * c l j z with hbbdef
  have hbbsm : ∀ l j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bb l j) :=
    fun l j => contDiff_const.mul (hcsm l j)
  have hbbcs : ∀ l j, HasCompactSupport (bb l j) := fun l j => (hccs l j).mul_left
  have hbbsupp : ∀ l j z, bb l j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ := by
    intro l j z hz
    refine hcsupp l j z (fun h0 => hz ?_)
    simp [hbbdef, h0]
  have hbbnorm : ∀ l j, Work.CR.Flat.holderNorm 0 α (bb l j) Set.univ ≤ ENNReal.ofReal δe := by
    intro l j
    have h1 : Work.CR.Flat.holderNorm 0 α (bb l j) Set.univ
        ≤ ENNReal.ofReal ‖γ⁻¹‖ * Work.CR.Flat.holderNorm 0 α (c l j) Set.univ := by
      rw [hbbdef]
      exact Work.NN.Core.holderNorm_const_mul_le uniqueDiffOn_univ γ⁻¹ (c l j)
    have h2 : ENNReal.ofReal ‖γ⁻¹‖ * Work.CR.Flat.holderNorm 0 α (c l j) Set.univ
        ≤ ENNReal.ofReal ‖γ⁻¹‖ * ENNReal.ofReal δ :=
      mul_le_mul_of_nonneg_left (hcnorm l j) bot_le
    have h3 : ENNReal.ofReal ‖γ⁻¹‖ * ENNReal.ofReal δ = ENNReal.ofReal (‖γ⁻¹‖ * δ) :=
      (ENNReal.ofReal_mul (norm_nonneg γ⁻¹)).symm
    have h4 : ‖γ⁻¹‖ * δ ≤ δe := by
      rw [hδdef]
      have hL : 0 ≤ ‖γ⁻¹‖ := norm_nonneg _
      have hL1 : 0 < ‖γ⁻¹‖ + 1 := by positivity
      rw [show ‖γ⁻¹‖ * (δe / (‖γ⁻¹‖ + 1)) = (‖γ⁻¹‖ * δe) / (‖γ⁻¹‖ + 1) by ring]
      rw [div_le_iff₀ hL1]
      nlinarith [hL, hδepos]
    calc Work.CR.Flat.holderNorm 0 α (bb l j) Set.univ
        ≤ ENNReal.ofReal ‖γ⁻¹‖ * Work.CR.Flat.holderNorm 0 α (c l j) Set.univ := h1
      _ ≤ ENNReal.ofReal ‖γ⁻¹‖ * ENNReal.ofReal δ := h2
      _ = ENNReal.ofReal (‖γ⁻¹‖ * δ) := h3
      _ ≤ ENNReal.ofReal δe := ENNReal.ofReal_le_ofReal h4
  -- ## the induction
  have key : ∀ m : ℕ, 1 ≤ m →
      ContDiffOn ℝ (m : ℕ∞) h (Work.CR.Flat.polydisc 0 (R m)) ∧
        Work.CR.Flat.holderNorm m α h (Work.CR.Flat.polydisc 0 (R m)) < ⊤ := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        refine ⟨hh1.mono (Work.CR.Flat.polydisc_mono fun j =>
          le_trans (le_of_lt (hRltρs 1 le_rfl j)) (hρsρ j)), ?_⟩
        exact lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 ρ)
          (Work.CR.Flat.isOpen_polydisc 0 (R 1))
          (Work.CR.Flat.polydisc_mono fun j =>
            le_trans (le_of_lt (hRltρs 1 le_rfl j)) (hρsρ j)) 1 α h) hhfin
      · obtain ⟨hsm_m, hfin_m⟩ := ih hmpos
        -- the cutoff of this step
        obtain ⟨χ, V, hχsm, hχcs, hχsupp, hVopen, hKV, hχone⟩ :=
          Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
            (n := n) (K := Work.NN.Core.closedPolydisc (0 : Work.NN.Core.Cn n) (R (m + 1)))
            (U := Work.CR.Flat.polydisc 0 (R m))
            (Work.NN.Core.isCompact_closedPolydisc _ _) (Work.CR.Flat.isOpen_polydisc 0 (R m))
            (Work.NN.Core.closedPolydisc_subset fun j => hRmono m j)
        have hRmρ : Work.CR.Flat.polydisc 0 (R m) ⊆ Work.CR.Flat.polydisc 0 ρ :=
          Work.CR.Flat.polydisc_mono (fun j =>
            le_trans (le_of_lt (hRltρs m hmpos j)) (hρsρ j))
        have hRmρs : Work.CR.Flat.polydisc 0 (R m) ⊆ Work.CR.Flat.polydisc 0 ρs :=
          Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hRltρs m hmpos j))
        have hχsuppρ : tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρ := fun z hz => hRmρ (hχsupp hz)
        have hχsuppρs : tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρs := fun z hz => hRmρs (hχsupp hz)
        have hχone' : ∀ z, z ∈ Work.CR.Flat.polydisc 0 (R (m + 1)) → χ z = 1 :=
          fun z hz => hχone z (hKV fun j => le_of_lt (hz j))
        -- the error coefficient `ψ` and the datum `G = ψ h + χ S`
        set ψ : Fin n → Work.NN.Core.Cn n → ℂ := fun l z => Work.CR.Flat.dbarCoord l χ z
            - ∑ j, c l j z * Work.CR.Flat.dCoord j χ z with hψdef
        set G : Fin n → Work.NN.Core.Cn n → ℂ := fun l z => ψ l z * h z + χ z * S l z with hGdef
        have hψsm : ∀ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ l) := by
          intro l
          rw [hψdef]
          refine (Work.NN.Core.contDiff_dbarCoord_fin hχsm l).sub ?_
          exact ContDiff.sum fun j _ => (hcsm l j).mul (Work.NN.Core.contDiff_dCoord hχsm j)
        have hψts : ∀ l, tsupport (ψ l) ⊆ Work.CR.Flat.polydisc 0 (R m) := by
          intro l
          have hsub : tsupport (ψ l) ⊆ tsupport χ := by
            rw [tsupport]
            refine closure_minimal (fun z hz => ?_) (isClosed_tsupport χ)
            simp only [Function.mem_support] at hz
            by_contra hc
            have hfd : fderiv ℝ χ z = 0 := Work.NN.Core.fderiv_eq_zero_of_notMem_tsupport hc
            refine hz ?_
            rw [hψdef]
            simp only [Pi.sub_apply, Finset.sum_apply]
            rw [Work.NN.Core.dbarCoord_eq_zero_of_fderiv_eq_zero hfd l,
              Finset.sum_eq_zero (fun j _ => by
                rw [Work.NN.Core.dCoord_eq_zero_of_fderiv_eq_zero hfd j, mul_zero])]
            simp
          exact hsub.trans hχsupp
        have h1Gsm : ∀ l, ContDiff ℝ m (fun z => ψ l z * h z) := fun l =>
          (Work.NN.Core.contDiff_mul_of_smooth_supported (n := n) hα0 hα1 (hRpos m) (hψsm l)
            (hψts l) hsm_m hfin_m).1
        have h1Gfin : ∀ l, Work.CR.Flat.holderNorm m α (fun z => ψ l z * h z) Set.univ < ⊤ :=
          fun l => (Work.NN.Core.contDiff_mul_of_smooth_supported (n := n) hα0 hα1 (hRpos m)
            (hψsm l) (hψts l) hsm_m hfin_m).2
        have h2Gsm : ∀ l, ContDiff ℝ m (fun z => χ z * S l z) := fun l =>
          ((hχsm.of_le (WithTop.coe_le_coe.mpr le_top)).mul (hSsm l)).of_le
            (WithTop.coe_le_coe.mpr le_top)
        have h2Gfin : ∀ l, Work.CR.Flat.holderNorm m α (fun z => χ z * S l z) Set.univ < ⊤ :=
          fun l => by
            rw [lt_top_iff_ne_top]
            refine Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport'
              (X := Work.NN.Core.Cn n) hα0.le (le_of_lt hα1) ?_ (hχcs.mul_right)
            exact ((hχsm.of_le (WithTop.coe_le_coe.mpr le_top)).mul (hSsm l)).of_le
              (WithTop.coe_le_coe.mpr le_top)
        have hGsm : ∀ l, ContDiff ℝ m (G l) := fun l => (h1Gsm l).add (h2Gsm l)
        have hGfin : ∀ l, Work.CR.Flat.holderNorm m α (G l) Set.univ < ⊤ := fun l => by
          rw [lt_top_iff_ne_top]
          exact Work.CR.Flat.Holder.holderNorm_add_ne_top (k := m) (α := α)
            ((h1Gsm l).contDiffOn) ((h2Gsm l).contDiffOn) uniqueDiffOn_univ
            (lt_top_iff_ne_top.mp (h1Gfin l)) (lt_top_iff_ne_top.mp (h2Gfin l))
        have hGcs : ∀ l, HasCompactSupport (G l) := fun l =>
          ((Work.NN.Core.hasCompactSupport_of_tsupport_subset_polydisc (hψts l)).mul_right).add
            (hχcs.mul_right)
        have hGvan : ∀ l z, (∃ i, ρ i ≤ ‖z i‖) → G l z = 0 := by
          intro l z hz
          have hzρ : z ∉ Work.CR.Flat.polydisc 0 ρ := fun h => hz.elim fun i hi =>
            absurd (h i) (not_lt.mpr (by simpa using hi))
          have h1 : z ∉ tsupport (ψ l) := fun hc => hzρ (hRmρ (hψts l hc))
          have h2 : z ∉ tsupport χ := fun hc => hzρ (hχsuppρ hc)
          rw [hGdef]
          simp only [Pi.add_apply]
          rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2,
            zero_mul, zero_mul, add_zero]
        -- `F = γ⁻¹ T(G)`
        set F : Work.NN.Core.Cn n → ℂ := fun z => γ⁻¹ * Work.CR.Flat.Cauchy.bmPotential G z
          with hFdef
        obtain ⟨Cp, _hCppos, hpotG⟩ :=
          Work.NN.Core.bmPotential_gain (n := n) hn hα0 hα1 hρ m
        have hpG := hpotG G hGsm hGcs hGfin hGvan
        have hFsm : ContDiffOn ℝ (((m + 1 : ℕ)) : ℕ∞) F (Work.CR.Flat.polydisc 0 ρ) := by
          rw [hFdef]
          simpa only [smul_eq_mul] using hpG.1.const_smul ((γ)⁻¹ : ℂ)
        have hFfin : Work.CR.Flat.holderNorm (m + 1) α F (Work.CR.Flat.polydisc 0 ρ) < ⊤ := by
          rw [hFdef]
          refine lt_of_le_of_lt (Work.NN.Core.holderNorm_const_mul_le
            (Work.CR.Flat.isOpen_polydisc 0 ρ).uniqueDiffOn (γ)⁻¹ _) ?_
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
          have hb := lt_of_le_of_lt hpG.2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.sum_lt_top.mpr fun l _ => hGfin l))
          simpa only [Pi.zero_apply] using hb
        -- the cutoff identity
        have hcut : ∀ l z, Work.CR.Flat.dbarCoord l (fun w => χ w * h w) z
            = (∑ j, c l j z * Work.CR.Flat.dCoord j (fun w => χ w * h w) z) + G l z := by
          intro l z
          have h := dbarCoord_cutoff_eq_source (n := n) (U := Work.CR.Flat.polydisc 0 ρ)
            (Work.CR.Flat.isOpen_polydisc 0 ρ) hχsm hχsuppρ hh1 c S
            (fun l z hz => heq l z (hχsuppρs hz)) l z
          rw [h, hGdef, hψdef]
          ring
        -- the product `W = χ h`
        have hWu1 : ContDiff ℝ 1 (fun w => χ w * h w) :=
          Work.NN.Core.contDiff_one_mul_of_contDiffOn (Work.CR.Flat.isOpen_polydisc 0 ρ)
            (hχsm.of_le Work.NN.Core.one_le_smooth) hχsuppρ hh1
        have hWcs : HasCompactSupport (fun w => χ w * h w) := hχcs.mul_right
        have hWufin : Work.CR.Flat.holderNorm 1 α (fun w => χ w * h w)
            (Work.CR.Flat.polydisc 0 ρ) < ⊤ := by
          have hbig : Work.CR.Flat.holderNorm m α (fun w => χ w * h w) Set.univ < ⊤ :=
            (Work.NN.Core.contDiff_mul_of_smooth_supported (n := n) hα0 hα1 (hRpos m) hχsm
              hχsupp hsm_m hfin_m).2
          exact lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_set isOpen_univ
            (Work.CR.Flat.isOpen_polydisc 0 ρ) (fun x _ => trivial) 1 α _)
            (lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_k hmpos α _ Set.univ) hbig)
        -- the fixed point equation
        have hWeq : ∀ z ∈ Work.CR.Flat.polydisc 0 ρ, (fun w => χ w * h w) z
            = Work.CR.Flat.Cauchy.bmPotential (fun l y => ∑ j, bb l j y
                * Work.CR.Flat.dCoord j (fun w => χ w * h w) y) z + F z := by
          intro z _
          set fdat : Fin n → Work.NN.Core.Cn n → ℂ := fun l y => ∑ j, c l j y
              * Work.CR.Flat.dCoord j (fun w => χ w * h w) y with hfdatdef
          set f2 : Fin n → Work.NN.Core.Cn n → ℂ := fun l y => ∑ j, bb l j y
              * Work.CR.Flat.dCoord j (fun w => χ w * h w) y with hf2def
          have hPom := Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul (n := n) hn hWu1 hWcs z
          have hfdc : Continuous (fderiv ℝ (fun w => χ w * h w)) :=
            hWu1.continuous_fderiv (by norm_num)
          have hdcj : ∀ j, Continuous (fun y => Work.CR.Flat.dCoord j (fun w => χ w * h w) y) := by
            intro j
            have h1 : (fun y => Work.CR.Flat.dCoord j (fun w => χ w * h w) y)
                = fun y => Work.NN.Core.dCoordLin j (fderiv ℝ (fun w => χ w * h w) y) :=
              funext fun y => congrFun (Work.NN.Core.dCoord_eq_comp j
                (fun w => χ w * h w)) y
            rw [h1]
            exact (Work.NN.Core.dCoordLin j).continuous.comp hfdc
          have hcont1 : ∀ l, Continuous (fdat l) := fun l =>
            continuous_finsetSum _ fun j _ => (hcsm l j).continuous.mul (hdcj j)
          have hcontG : ∀ l, Continuous (G l) := fun l => (hGsm l).continuous
          have hcs1 : ∀ l, HasCompactSupport (fdat l) := fun l =>
            Work.NN.Core.hasCompactSupport_finsetSum fun j _ => (hccs l j).mul_right
          have hcsG : ∀ l, HasCompactSupport (G l) := hGcs
          have hAB : (fun l y => Work.CR.Flat.dbarCoord l (fun w => χ w * h w) y) = fdat + G := by
            funext l y; exact hcut l y
          have hsplit : Work.CR.Flat.Cauchy.bmGamma n * (fun w => χ w * h w) z
              = Work.CR.Flat.Cauchy.bmPotential fdat z
                + Work.CR.Flat.Cauchy.bmPotential G z := by
            rw [hPom, hAB,
              Work.NN.Core.bmPotential_add_of_cont (n := n) hn hcont1 hcontG hcs1 hcsG]
            rfl
          have hGfac : Work.CR.Flat.Cauchy.bmPotential G z = γ * F z := by
            show Work.CR.Flat.Cauchy.bmPotential G z
              = γ * (γ⁻¹ * Work.CR.Flat.Cauchy.bmPotential G z)
            rw [mul_inv_cancel_left₀ hγne]
          have hcbb : ∀ l j y, c l j y = γ * bb l j y := by
            intro l j y
            rw [hbbdef]
            exact (mul_inv_cancel_left₀ hγne (c l j y)).symm
          have hffac : Work.CR.Flat.Cauchy.bmPotential fdat z
              = γ * Work.CR.Flat.Cauchy.bmPotential f2 z := by
            have hfdef2 : fdat = fun l y => γ * (∑ j, bb l j y
                * Work.CR.Flat.dCoord j (fun w => χ w * h w) y) := by
              funext l y
              rw [hfdatdef]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hcbb l j y]; ring
            rw [hfdef2]
            exact congrFun (Work.NN.Core.bmPotential_const_mul (n := n) γ f2) z
          have hPom2 : Work.CR.Flat.Cauchy.bmGamma n * (fun w => χ w * h w) z
              = γ * (Work.CR.Flat.Cauchy.bmPotential f2 z + F z) := by
            rw [hsplit, hffac, hGfac]
            ring_nf
          exact mul_left_cancel₀ hγne hPom2
        -- the engine
        obtain ⟨hWsm, hWfin⟩ := heng (hRpos (m + 1)) (fun j =>
            lt_of_lt_of_le (hRltρs (m + 1) (by omega) j) (hρsρ j)) (m + 1)
          (by omega) bb F (fun w => χ w * h w) hbbsm hbbcs hbbsupp hbbnorm hFsm hFfin
          hWu1.contDiffOn hWufin hWeq
        refine ⟨?_, ?_⟩
        · exact hWsm.congr (fun z hz => by rw [hχone' z hz, one_mul])
        · rw [Work.NN.Core.holderNorm_congr (k := m + 1) (α := α) (f := h)
            (g := fun w => χ w * h w) (Ω := Work.CR.Flat.polydisc 0 (R (m + 1)))
            (fun z hz => by rw [hχone' z hz, one_mul])]
          exact hWfin
  -- ## conclusion
  intro k
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact contDiffOn_zero.mpr ((hh1.mono (Work.CR.Flat.polydisc_mono fun j =>
      le_trans (le_of_lt (hρ'ρs j)) (hρsρ j))).continuousOn)
  · exact (key k hkpos).1.mono (Work.CR.Flat.polydisc_mono fun j => le_of_lt (hρ'R k j))

end

end Work.NN.Final


/-!
# Hypoellipticity of `∂̄_J` with an inhomogeneous (smooth) datum

...

-/

namespace Work.NN.Final

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

noncomputable section

end

/-! ## The Beltrami system of the inhomogeneous equation, with a smooth source -/

/-- A `C^∞` (finite-order) compactly supported real function has a bounded Fréchet derivative. -/
private lemma nn_fderiv_bound_of_contDiff_hasCompactSupport {n : ℕ} {φ : Work.NN.Core.Cn n → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖fderiv ℝ φ z‖ ≤ M := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hcont : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hc.fderiv ℝ)
  exact ⟨max C 0, le_max_right _ _, fun z => le_trans (hC z) (le_max_left _ _)⟩

/-- **The Beltrami form of the inhomogeneous perturbed `∂̄`-equation, with a source.**

There is a threshold `ε₀ > 0` and a constant `C > 0` such that for every perturbation `A` of the
standard structure which is `C^∞` and componentwise `C^{0,α}`-small (of size `ε ≤ ε₀`) on the
polydisc `polydisc 0 ρ`, and every `C^∞` datum `f`, one can find a smooth compactly supported
coefficient `c` (supported in `polydisc 0 ρ`, of `C^{0,α}`-norm at most `C ε`) and a smooth source
`S` such that every solution `u` of

`∂̄_{Jstd + A} u = f`  (in every coordinate direction `e_k`)

satisfies the *decoupled* system `∂̄_k u = Σ_j c k j ∂_j u + S_k` on the smaller polydisc
`polydisc 0 ρ₁`. -/
private theorem exists_beltramiCoefSource_small_smooth {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {ρ ρ₁ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ₁ : ∀ j, 0 < ρ₁ j)
    (hρ₁ρ : ∀ j, ρ₁ j < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
        (f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ) (ε : ℝ),
        0 ≤ ε → ε ≤ ε₀ →
        (∀ m : ℕ, ContDiff ℝ m A) → (∀ m : ℕ, ContDiff ℝ m f) →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
          (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
        ∃ (c : Fin n → Fin n → Work.NN.Core.Cn n → ℂ) (S : Fin n → Work.NN.Core.Cn n → ℂ),
          (∀ k j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c k j)) ∧
          (∀ k j, HasCompactSupport (c k j)) ∧
          (∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) ∧
          (∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ ≤ ENNReal.ofReal (C * ε)) ∧
          (∀ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (S l)) ∧
          ∀ (u : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n),
            z ∈ Work.CR.Flat.polydisc 0 ρ₁ →
            (∀ k : Fin n, Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z
              (Pi.single k 1) = f z (Pi.single k 1)) →
            ∀ k, Work.CR.Flat.dbarCoord k u z
              = (∑ j, c k j z * Work.CR.Flat.dCoord j u z) + S k z := by
  classical
  -- ## a smooth cutoff of the perturbation, equal to `1` on the smaller polydisc
  obtain ⟨χ, V, hχsm, hχcs, hχtsupp, hVopen, hKV, hχone, hχ01⟩ :=
    Work.NN.Core.JFPre.jf_exists_cutoff_polydisc (n := n) (σ := ρ₁) (ρ := ρ) hρ₁ρ
  obtain ⟨M, hM0, hMbd⟩ := nn_fderiv_bound_of_contDiff_hasCompactSupport hχsm hχcs
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Work.NN.Core.beltramiCoefSmallZero_c1 (n := n) hn hα0 hα1 hρ M hM0
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  refine ⟨1 / (2 * (n : ℝ)), by positivity, C₀ * (1 + M), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 1 + M := by linarith
    exact mul_pos hC₀pos h1
  intro A f ε hε0 hεε₀ hA hf hsmall
  -- ## the cut-off perturbation
  set D : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n :=
    fun z => χ z • A z with hDdef
  have hDsm : ∀ m : ℕ, ContDiff ℝ m D := by
    intro m
    rw [hDdef]
    exact (hχsm.of_le (WithTop.coe_le_coe.mpr le_top)).smul (hA m)
  have hχsupp : ∀ z, χ z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ :=
    fun z hz => hχtsupp (subset_closure (by simpa [Function.mem_support] using hz))
  have hχabs : ∀ z, |χ z| ≤ 1 := by
    intro z
    rw [abs_of_nonneg (hχ01 z).1]
    exact (hχ01 z).2
  -- ## the smallness of the cut-off perturbation
  have hentry : ∀ (i j : Fin n) (z : Work.NN.Core.Cn n), z ∈ Work.CR.Flat.polydisc 0 ρ →
      ‖A z (Pi.single i 1) j‖ ≤ ε := by
    intro i j z hz
    have h1 := Work.CR.Flat.norm_apply_le_holderNorm 0 α
      (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) hz
    exact (ENNReal.ofReal_le_ofReal_iff hε0).mp (le_trans h1 (hsmall i j))
  have hbetasup : ∀ (k' j' : Fin n) (z : Work.NN.Core.Cn n),
      ‖Work.NN.Core.betaCoef D k' j' z‖ ≤ ε / 2 := by
    intro k' j' z
    rw [hDdef, Work.NN.Core.betaCoef_smul]
    have h : |χ z| * ‖A z (Pi.single k' 1) j'‖ ≤ ε := by
      by_cases hz : χ z = 0
      · simp only [hz, abs_zero, zero_mul]
        exact hε0
      · calc |χ z| * ‖A z (Pi.single k' 1) j'‖ ≤ 1 * ε :=
              mul_le_mul (hχabs z) (hentry k' j' z (hχsupp z hz)) (norm_nonneg _) zero_le_one
          _ = ε := one_mul ε
    calc ‖-(Complex.I / 2) * (χ z * A z (Pi.single k' 1) j')‖
        = ‖(Complex.I / 2 : ℂ)‖ * ‖χ z * A z (Pi.single k' 1) j'‖ := by rw [norm_mul, norm_neg]
      _ = (1 / 2) * (|χ z| * ‖A z (Pi.single k' 1) j'‖) := by
          rw [norm_div, Complex.norm_I, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          norm_num
      _ ≤ (1 / 2) * ε := by linarith
      _ = ε / 2 := by ring
  have hq : ∀ z, ‖Work.NN.Core.BopBar D z‖ ≤ 1 / 4 := by
    intro z
    change ‖ContinuousLinearMap.pi (fun k : Fin n => ∑ j : Fin n,
      ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Work.NN.Core.Cn n →L[ℝ] ℂ)
        (starRingEnd ℂ (Work.NN.Core.betaCoef D k j z)))‖ ≤ 1 / 4
    refine le_trans (Work.NN.Core.opNorm_pi_sum_smulRight_le _
      (by positivity : (0:ℝ) ≤ ε / 2) (fun k j => ?_)) ?_
    · rw [starRingEnd_apply, norm_star]
      exact hbetasup k j z
    · have h1 : (n : ℝ) * ε ≤ 1 / 2 := by
        calc (n : ℝ) * ε ≤ (n : ℝ) * (1 / (2 * (n : ℝ))) := by gcongr
          _ = 1 / 2 := by field_simp
      calc (n : ℝ) * (ε / 2) = (n : ℝ) * ε / 2 := by ring
        _ ≤ (1 / 2) / 2 := by linarith
        _ = 1 / 4 := by norm_num
  -- ## the coefficient and the source
  have heqD : ∀ (u : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n),
      z ∈ Work.CR.Flat.polydisc 0 ρ₁ → (∀ k : Fin n,
        Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single k 1)
          = f z (Pi.single k 1)) →
      ∀ k, Work.CR.Flat.dbarCoord k u z
        = (∑ j, Work.NN.Core.beltramiCoef D k j z * Work.CR.Flat.dCoord j u z)
          + beltramiSource D f z k := by
    intro u z hz hz'
    have hDz : D z = A z := by
      rw [hDdef]
      show χ z • A z = A z
      rw [hχone z (by
        -- χ = 1 on the closed box of radii ρ₁, and polydisc 0 ρ₁ is contained in it
        refine hKV fun j => le_of_lt (by simpa using (Work.CR.Flat.mem_polydisc.mp hz) j))]
      exact one_smul ℝ (A z)
    have hstr : (Work.NN.Core.JstdCn n + D) z = (Work.NN.Core.JstdCn n + A) z := by
      ext v
      simp only [Pi.add_apply]
      rw [hDz]
    have hz'' : ∀ k : Fin n,
        Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + D) u z (Pi.single k 1)
          = f z (Pi.single k 1) := by
      intro k
      have hEq : Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + D) u z
          = Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z := by
        unfold Work.NN.Core.dbarCn
        rw [hstr]
      rw [hEq]
      exact hz' k
    exact dbarCoord_eq_beltramiCoeff_source_pointwise D f u z (hq z) hz''
  -- ## the support of the coefficient
  have hcsupp : ∀ (k j : Fin n) (z : Work.NN.Core.Cn n),
      Work.NN.Core.beltramiCoef D k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ := by
    intro k j z hz
    by_contra hzρ
    have hχz : χ z = 0 := by
      by_contra hc
      exact hzρ (hχsupp z hc)
    have hDz : D z = 0 := by
      rw [hDdef]
      show χ z • A z = 0
      rw [hχz]
      exact zero_smul ℝ (A z)
    have h0 : Work.NN.Core.beltramiCoeff D z = 0 :=
      Work.NN.Core.beltramiCoeff_eq_zero_of_betaCoef_eq_zero D z
        (fun k' j' => by simp [Work.NN.Core.betaCoef, hDz])
    exact hz (by simp [Work.NN.Core.beltramiCoef, h0])
  refine ⟨fun k j z => Work.NN.Core.beltramiCoef D k j z,
    fun l z => beltramiSource D f z l, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k j
    exact Work.NN.Core.beltramiCoef_contDiff_infty D hDsm hq k j
  · intro k j
    refine Work.NN.Core.hasCompactSupport_of_tsupport_subset_polydisc
      (ρψ := fun j => 2 * ρ j) ?_
    have hsub : tsupport (fun z => Work.NN.Core.beltramiCoef D k j z)
        ⊆ Work.NN.Core.closedPolydisc (0 : Work.NN.Core.Cn n) ρ := by
      rw [tsupport]
      refine closure_minimal (fun z hz => ?_)
        (Work.NN.Core.isCompact_closedPolydisc (0 : Work.NN.Core.Cn n) ρ).isClosed
      rw [Work.NN.Core.closedPolydisc]
      intro j'
      have := Work.CR.Flat.mem_polydisc.mp (hcsupp k j z hz) j'
      simpa using le_of_lt this
    exact fun z hz => Work.NN.Core.closedPolydisc_subset
      (fun j => by linarith [hρ j]) (hsub hz)
  · exact hcsupp
  · intro k j
    have hχ1 : ContDiff ℝ 1 χ := hχsm.of_le (WithTop.coe_le_coe.mpr le_top)
    have h := hC₀ (A := A) hA χ hχ1 hχcs hχsupp hχ01 hMbd hε0 hεε₀ hsmall k j
    refine h.trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  · intro l
    exact beltramiSource_contDiff D hDsm hq f hf l
  · exact heqD

/-! ## The product rule for the perturbed `∂̄`-operator -/

/-- The product rule for `∂̄_{Jstd + A}`: the perturbation is a derivation. -/
private lemma dbarCn_mul_eq {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (χ h : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n) (l : Fin n)
    (hdχ : DifferentiableAt ℝ χ z) (hdh : DifferentiableAt ℝ h z) :
    Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) (fun w => χ w * h w) z (Pi.single l 1)
      = χ z * Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) h z (Pi.single l 1)
        + (Work.CR.Flat.dbarCoord l χ z + Work.NN.Core.Lcoef A χ l z) * h z := by
  have hL : Work.NN.Core.Lcoef A (fun w => χ w * h w) l z
      = Work.NN.Core.Lcoef A χ l z * h z + χ z * Work.NN.Core.Lcoef A h l z := by
    have hf : (fun w => χ w * h w) = χ * h := by funext w; rfl
    rw [show Work.NN.Core.Lcoef A (fun w => χ w * h w) l z
        = (Complex.I / 2) * fderiv ℝ (χ * h) z (A z (Pi.single l (1 : ℂ))) by
      rw [← hf]; rfl]
    simp only [Work.NN.Core.Lcoef, fderiv_mul hdχ hdh, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [Work.NN.Core.dbarCoef_lin, Work.CR.Flat.Polydisc.dbarCoord_mul l χ h z hdχ hdh, hL,
    Work.NN.Core.dbarCoef_lin]
  ring

/-! ## The core: inhomogeneous hypoellipticity with globally defined data -/

/-- **Hypoellipticity of `∂̄_{Jstd + A}` for an inhomogeneous datum**, in the global setting:
`A` is globally `C^∞`, componentwise `C^{0,α}`-small on `polydisc 0 ρb`, `J = Jstd + A` is almost
complex everywhere, `f` is globally `C^∞`, and `h ∈ C¹` solves `∂̄_J h = f` on `polydisc 0 ρb`.
Then `h` is `C^k` on `polydisc 0 ρ'` for every `k`, whenever `ρ' < ρb` componentwise. -/
private theorem dbarCn_smooth_inhom_global {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρb ρ' : Fin n → ℝ} (hρb : ∀ j, 0 < ρb j) (hρ' : ∀ j, 0 < ρ' j)
    (hρ'ρb : ∀ j, ρ' j < ρb j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiff ℝ m A) → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
          (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρb) ≤ ENNReal.ofReal ε) →
        (∀ z v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        ∀ (f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ),
          (∀ m : ℕ, ContDiff ℝ m f) →
          ∀ h : Work.NN.Core.Cn n → ℂ,
            ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρb) →
            (∀ z, z ∈ Work.CR.Flat.polydisc 0 ρb → ∀ V : Work.NN.Core.Cn n,
              Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) h z V = f z V) →
            ∀ k : ℕ, ContDiffOn ℝ k h (Work.CR.Flat.polydisc 0 ρ') := by
  classical
  -- ## the chain of radii `ρ' < ρ₁ < ρc < Q < ρb`
  set ρc : Fin n → ℝ := fun j => ρ' j + (ρb j - ρ' j) / 4 with hρcdef
  set Q : Fin n → ℝ := fun j => ρ' j + (ρb j - ρ' j) / 2 with hQdef
  set ρ₁ : Fin n → ℝ := fun j => ρ' j + (ρb j - ρ' j) / 8 with hρ₁def
  have hδ0 : ∀ j, 0 < ρb j - ρ' j := fun j => by linarith [hρ'ρb j]
  have hρcpos : ∀ j, 0 < ρc j := fun j => by
    rw [hρcdef]; have h := div_pos (hδ0 j) (by norm_num : (0:ℝ) < 4); linarith [hρ' j]
  have hQpos : ∀ j, 0 < Q j := fun j => by
    rw [hQdef]; have h := div_pos (hδ0 j) (by norm_num : (0:ℝ) < 2); linarith [hρ' j]
  have hρ₁pos : ∀ j, 0 < ρ₁ j := fun j => by
    rw [hρ₁def]; have h := div_pos (hδ0 j) (by norm_num : (0:ℝ) < 8); linarith [hρ' j]
  have hρ'ρ₁ : ∀ j, ρ' j < ρ₁ j := fun j => by
    rw [hρ₁def]; have h := div_pos (hδ0 j) (by norm_num : (0:ℝ) < 8); linarith
  have hρ₁ρc : ∀ j, ρ₁ j < ρc j := fun j => by
    rw [hρ₁def, hρcdef]; nlinarith [hδ0 j]
  have hρcQ : ∀ j, ρc j < Q j := fun j => by
    rw [hρcdef, hQdef]; nlinarith [hδ0 j]
  have hQρb : ∀ j, Q j < ρb j := fun j => by
    rw [hQdef]; nlinarith [hδ0 j]
  have hρ₁ρb : ∀ j, ρ₁ j < ρb j := fun j => by
    rw [hρ₁def]; nlinarith [hδ0 j]
  have hρcρb : ∀ j, ρc j < ρb j := fun j => by
    rw [hρcdef]; nlinarith [hδ0 j]
  -- ## the three constants
  obtain ⟨δb, hδb, hbase0⟩ :=
    Work.NN.Core.dbarCoord_finite_of_perturbed_data (n := n) hn hα0 hα1 hρb hQpos hQρb
  obtain ⟨δt, hδt, htower⟩ :=
    beltrami_tower_source (n := n) hn hα0 hα1 (ρ := ρc) (ρs := ρ₁) (ρ' := ρ')
      hρcpos hρ' hρ'ρ₁ (fun j => le_of_lt (hρ₁ρc j))
  obtain ⟨εc, hεc, C, hCpos, hcs⟩ :=
    exists_beltramiCoefSource_small_smooth (n := n) hn hα0 hα1 hρcpos hρ₁pos hρ₁ρc
  refine ⟨min δb (min εc (δt / C)), lt_min hδb (lt_min hεc (div_pos hδt hCpos)), ?_⟩
  intro A hA ε hε0 hεε₀ hsmall hJ f hf h hh1 heq
  have hεδb : ε ≤ δb := le_trans hεε₀ (min_le_left _ _)
  have hεεc : ε ≤ εc := le_trans hεε₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεδt : C * ε ≤ δt := by
    have h : ε ≤ δt / C := le_trans hεε₀ (le_trans (min_le_right _ _) (min_le_right _ _))
    calc C * ε ≤ C * (δt / C) := by gcongr
      _ = δt := by field_simp
  -- ## STEP 1: the base case `h ∈ C^{1,α}(polydisc 0 ρc)`
  have hbase : Work.CR.Flat.holderNorm 1 α h (Work.CR.Flat.polydisc 0 ρc) < ⊤ := by
    obtain ⟨χ₀, V₀, hχ₀sm, hχ₀cs, hχ₀supp, hV₀open, hKV₀, hχ₀one⟩ :=
      Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
        (n := n) (K := Work.NN.Core.closedPolydisc (0 : Work.NN.Core.Cn n) ρc)
        (U := Work.CR.Flat.polydisc 0 Q)
        (Work.NN.Core.isCompact_closedPolydisc _ _) (Work.CR.Flat.isOpen_polydisc 0 Q)
        (Work.NN.Core.closedPolydisc_subset hρcQ)
    have hχ₀one1 : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρc → χ₀ z = 1 :=
      fun z hz => hχ₀one z (hKV₀ fun j => le_of_lt (hz j))
    have hχ₀van : ∀ z, z ∉ Work.CR.Flat.polydisc 0 Q → χ₀ z = 0 := by
      intro z hz
      rw [Work.CR.Flat.mem_polydisc] at hz
      push Not at hz
      obtain ⟨i, hi⟩ := hz
      by_contra hc
      exact absurd ((Work.CR.Flat.mem_polydisc.mp (hχ₀supp (subset_closure
        (by simpa [Function.mem_support] using hc)))) i) (not_lt.mpr (by simpa using hi))
    set coef : Fin n → Work.NN.Core.Cn n → ℂ := fun m z =>
      Work.CR.Flat.dbarCoord m χ₀ z + Work.NN.Core.Lcoef A χ₀ m z with hcoefdef
    have hcoefsm : ∀ m, ContDiff ℝ 1 (coef m) := by
      intro m
      rw [hcoefdef]
      refine ((Work.NN.Core.contDiff_dbarCoord_fin hχ₀sm m).of_le Work.NN.Core.one_le_smooth).add ?_
      have h1 : ContDiff ℝ 1 (fun z : Work.NN.Core.Cn n =>
          fderiv ℝ χ₀ z (A z (Pi.single m (1 : ℂ)))) :=
        ((hχ₀sm.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl).of_le
          Work.NN.Core.one_le_smooth).clm_apply ((hA 1).clm_apply contDiff_const)
      exact contDiff_const.mul h1
    have hcoefts : ∀ m, tsupport (coef m) ⊆ Work.CR.Flat.polydisc 0 Q := by
      intro m
      have hsub : tsupport (coef m) ⊆ tsupport χ₀ := by
        rw [tsupport]
        refine closure_minimal (fun z hz => ?_) (isClosed_tsupport χ₀)
        simp only [Function.mem_support] at hz
        by_contra hc
        have hfd : fderiv ℝ χ₀ z = 0 := Work.NN.Core.fderiv_eq_zero_of_notMem_tsupport hc
        refine hz ?_
        have h1 : Work.CR.Flat.dbarCoord m χ₀ z = 0 :=
          Work.NN.Core.dbarCoord_eq_zero_of_fderiv_eq_zero hfd m
        have h2 : Work.NN.Core.Lcoef A χ₀ m z = 0 := by simp [Work.NN.Core.Lcoef, hfd]
        show coef m z = 0
        rw [hcoefdef]
        simp only [Pi.add_apply]
        rw [h1, h2, add_zero]
      exact hsub.trans hχ₀supp
    have hW1 : ContDiff ℝ 1 (fun w => χ₀ w * h w) :=
      Work.NN.Core.contDiff_one_mul_of_contDiffOn (Work.CR.Flat.isOpen_polydisc 0 Q)
        (hχ₀sm.of_le Work.NN.Core.one_le_smooth) hχ₀supp
        (hh1.mono (Work.CR.Flat.polydisc_mono fun j => le_of_lt (hQρb j)))
    have hWcs : HasCompactSupport (fun w => χ₀ w * h w) := hχ₀cs.mul_right
    have hWvan : ∀ z, (∃ i, Q i ≤ ‖z i‖) → (fun w => χ₀ w * h w) z = 0 := by
      intro z hz
      have hzQ : z ∉ Work.CR.Flat.polydisc 0 Q := fun h => hz.elim fun i hi =>
        absurd (h i) (not_lt.mpr (by simpa using hi))
      show χ₀ z * h z = 0
      rw [hχ₀van z hzQ, zero_mul]
    -- the perturbed datum of the cutoff function
    have hdat : ∀ m, Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A)
          (fun w => χ₀ w * h w) z (Pi.single m 1)) Set.univ < ⊤ := by
      intro m
      have hid : (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A)
          (fun w => χ₀ w * h w) z (Pi.single m 1))
          = fun z => χ₀ z * f z (Pi.single m 1) + coef m z * h z := by
        funext z
        by_cases hz : z ∈ Work.CR.Flat.polydisc 0 ρb
        · have hdχ : DifferentiableAt ℝ χ₀ z :=
            (hχ₀sm.of_le Work.NN.Core.one_le_smooth).contDiffAt.differentiableAt (by norm_num)
          have hdh : DifferentiableAt ℝ h z :=
            (hh1.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρb).mem_nhds hz)).differentiableAt
              (by norm_num)
          rw [dbarCn_mul_eq A χ₀ h z m hdχ hdh, heq z hz (Pi.single m 1)]
        · have hzQ : z ∉ Work.CR.Flat.polydisc 0 Q := fun hc =>
            hz (Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hQρb j)) hc)
          have hχ₀z : χ₀ z = 0 := hχ₀van z hzQ
          have hcoefz : coef m z = 0 := by
            by_contra hc
            exact hzQ (hcoefts m (subset_closure (by simpa [Function.mem_support] using hc)))
          have hnot : z ∉ tsupport χ₀ := fun hc => hzQ (hχ₀supp hc)
          have hzo : ∀ᶠ w in 𝓝 z, χ₀ w = 0 := by
            filter_upwards [(isClosed_tsupport χ₀).isOpen_compl.mem_nhds hnot] with w hw
            exact image_eq_zero_of_notMem_tsupport hw
          have hev : (fun w => χ₀ w * h w) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
            hzo.mono (fun w hw => by simp [hw])
          have hfd : fderiv ℝ (fun w => χ₀ w * h w) z = 0 := by rw [hev.fderiv_eq]; simp
          rw [hχ₀z, hcoefz]
          simp only [zero_mul, add_zero]
          unfold Work.NN.Core.dbarCn
          rw [hfd]
          simp
      rw [hid]
      rw [lt_top_iff_ne_top]
      have hf1m : ContDiff ℝ 1 (fun z : Work.NN.Core.Cn n => χ₀ z * f z (Pi.single m 1)) :=
        (hχ₀sm.of_le Work.NN.Core.one_le_smooth).mul ((hf 1).clm_apply contDiff_const)
      have hf1cs : HasCompactSupport (fun z : Work.NN.Core.Cn n => χ₀ z * f z (Pi.single m 1)) :=
        hχ₀cs.mul_right
      have hf2m : ContDiff ℝ 1 (fun z : Work.NN.Core.Cn n => coef m z * h z) :=
        Work.NN.Core.contDiff_one_mul_of_contDiffOn (Work.CR.Flat.isOpen_polydisc 0 Q)
          (hcoefsm m) (hcoefts m)
          (hh1.mono (Work.CR.Flat.polydisc_mono fun j => le_of_lt (hQρb j)))
      have hf2cs : HasCompactSupport (fun z : Work.NN.Core.Cn n => coef m z * h z) :=
        (Work.NN.Core.hasCompactSupport_of_tsupport_subset_polydisc (hcoefts m)).mul_right
      exact Work.CR.Flat.Holder.holderNorm_add_ne_top (k := 0) (α := α)
        (f := fun z : Work.NN.Core.Cn n => χ₀ z * f z (Pi.single m 1))
        (g := fun z : Work.NN.Core.Cn n => coef m z * h z) (Ω := Set.univ)
        (contDiffOn_zero.mpr hf1m.continuous.continuousOn)
        (contDiffOn_zero.mpr hf2m.continuous.continuousOn) uniqueDiffOn_univ
        (Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport'
          (X := Work.NN.Core.Cn n) hα0.le (le_of_lt hα1) hf1m hf1cs)
        (Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport'
          (X := Work.NN.Core.Cn n) hα0.le (le_of_lt hα1) hf2m hf2cs)
    -- the flat data of the cutoff function is `C^{0,α}`
    have hflat := hbase0 (A := A) hε0 hεδb hsmall (fun w => χ₀ w * h w) hW1 hWcs hWvan hdat
    -- the Bochner--Martinelli representation and the gain of one derivative
    have hdc : ∀ l, ContDiff ℝ 0 (fun z => Work.CR.Flat.dbarCoord l
        (fun w => χ₀ w * h w) z) := by
      intro l
      have hfd : Continuous (fderiv ℝ (fun w => χ₀ w * h w)) := hW1.continuous_fderiv (by norm_num)
      have h : (fun z => Work.CR.Flat.dbarCoord l (fun w => χ₀ w * h w) z)
          = fun z => Work.CR.Flat.Polydisc.dbarCoordPhi l
              (fderiv ℝ (fun w => χ₀ w * h w) z) :=
        funext fun z => congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp l
          (fun w => χ₀ w * h w)) z
      rw [h]
      exact contDiff_zero.mpr ((Work.CR.Flat.Polydisc.dbarCoordPhi l).continuous.comp hfd)
    have hdcs : ∀ l, HasCompactSupport (fun z => Work.CR.Flat.dbarCoord l
        (fun w => χ₀ w * h w) z) := by
      intro l
      refine Work.NN.Core.hasCompactSupport_of_notMem_tsupport hWcs (fun z hz => ?_)
      exact Work.NN.Core.dbarCoord_eq_zero_of_fderiv_eq_zero
        (Work.NN.Core.fderiv_eq_zero_of_notMem_tsupport hz) l
    have hdcvan : ∀ l z, (∃ i, Q i ≤ ‖z i‖) → Work.CR.Flat.dbarCoord l
        (fun w => χ₀ w * h w) z = 0 := by
      intro l z hz
      have hzQ : z ∉ Work.CR.Flat.polydisc 0 Q := fun h => hz.elim fun i hi =>
        absurd (h i) (not_lt.mpr (by simpa using hi))
      by_cases hzt : z ∈ tsupport χ₀
      · exact absurd (hχ₀supp hzt) hzQ
      · have hzo : χ₀ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hzt
        have hev : (fun w => χ₀ w * h w) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
          hzo.mono (fun w hw => by simp [hw])
        exact Work.NN.Core.dbarCoord_eq_zero_of_fderiv_eq_zero
          (by rw [hev.fderiv_eq]; simp) l
    obtain ⟨_Cp, _hCppos, hpot⟩ :=
      Work.NN.Core.bmPotential_gain (n := n) hn hα0 hα1 hQpos 0
    have hpotfin : Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential
        (fun l z => Work.CR.Flat.dbarCoord l (fun w => χ₀ w * h w) z))
        (Work.CR.Flat.polydisc 0 Q) < ⊤ := by
      refine lt_of_le_of_lt (hpot (fun l z => Work.CR.Flat.dbarCoord l
        (fun w => χ₀ w * h w) z) (fun l => hdc l) hdcs hflat hdcvan).2 ?_
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.sum_lt_top.mpr fun l _ => hflat l)
    have hγ : Work.CR.Flat.Cauchy.bmGamma n ≠ 0 :=
      Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
    have hEqOn : ∀ z ∈ Work.CR.Flat.polydisc 0 Q, (fun w => χ₀ w * h w) z
        = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPotential
            (fun l y => Work.CR.Flat.dbarCoord l (fun w => χ₀ w * h w) y) z := by
      intro z _
      have hh := Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul (n := n) hn hW1 hWcs z
      rw [← hh, ← mul_assoc, inv_mul_cancel₀ hγ, one_mul]
    have hWfin : Work.CR.Flat.holderNorm 1 α (fun w => χ₀ w * h w)
        (Work.CR.Flat.polydisc 0 Q) < ⊤ := by
      rw [Work.NN.Core.holderNorm_congr hEqOn]
      refine lt_of_le_of_lt (Work.NN.Core.holderNorm_const_mul_le
        (Work.CR.Flat.isOpen_polydisc 0 Q).uniqueDiffOn (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ _) ?_
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpotfin
    refine lt_of_le_of_lt ?_ hWfin
    rw [Work.NN.Core.holderNorm_congr (k := 1) (α := α) (f := h)
      (g := fun w => χ₀ w * h w) (Ω := Work.CR.Flat.polydisc 0 ρc)
      (fun z hz => by rw [hχ₀one1 z hz, one_mul])]
    exact Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 Q)
      (Work.CR.Flat.isOpen_polydisc 0 ρc)
      (Work.CR.Flat.polydisc_mono fun j => le_of_lt (hρcQ j)) 1 α
      (fun w => χ₀ w * h w)
  -- ## STEP 2: the tower
  obtain ⟨c, S, hcsm, hccs, hcsupp, hcnorm, hSsm, heqsrc⟩ :=
    hcs A f ε hε0 hεεc hA hf (fun i j => (Work.CR.Flat.holderNorm_mono_set
      (Work.CR.Flat.isOpen_polydisc 0 ρb) (Work.CR.Flat.isOpen_polydisc 0 ρc)
      (Work.CR.Flat.polydisc_mono fun j => le_of_lt (hρcρb j)) 0 α
      (fun z => A z (Pi.single i 1) j)).trans (hsmall i j))
  exact fun k => htower c S h hcsm hccs hcsupp
    (fun l j => hcnorm l j |>.trans (ENNReal.ofReal_le_ofReal hεδt))
    hSsm (hh1.mono (Work.CR.Flat.polydisc_mono fun j => le_of_lt (hρcρb j)))
    hbase
    (fun l z hz => heqsrc h z hz (fun kk => heq z
      (Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρ₁ρb j)) hz) (Pi.single kk 1)) l) k

private theorem dbarCn_smooth_local_of_smooth_datum {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiffOn ℝ m A (Work.NN.Final.pd n ρ 4)) → ∀ {ε : ℝ}, ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => A z (Pi.single i 1) j) (Work.NN.Final.pd n ρ 4) ≤ ENNReal.ofReal ε) →
        (∀ z, z ∈ Work.NN.Final.pd n ρ 4 → ∀ v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        ∀ (f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ),
          (∀ m : ℕ, ContDiffOn ℝ m (fun z => f z) (Work.NN.Final.pd n ρ 2)) →
          ∀ h : Work.NN.Core.Cn n → ℂ,
            ContDiffOn ℝ 1 h (Work.NN.Final.pd n ρ 2) →
            (∀ z, z ∈ Work.NN.Final.pd n ρ 2 → ∀ V : Work.NN.Core.Cn n,
              Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) h z V = f z V) →
            ∀ k : ℕ, ContDiffOn ℝ k h (Work.NN.Final.pd n ρ 1) := by
  classical
  -- ## the intermediate polydisc `ρb = (3/2)ρ`
  set ρb : Fin n → ℝ := fun j => (3 / 2) * ρ j with hρbdef
  have hρbpos : ∀ j, 0 < ρb j := fun j => by rw [hρbdef]; linarith [hρ j]
  have hρρb : ∀ j, ρ j < ρb j := fun j => by rw [hρbdef]; linarith [hρ j]
  have hpd3 : Work.NN.Final.pd n ρ (3 / 2) = Work.CR.Flat.polydisc 0 ρb := by
    rw [hρbdef]; rfl
  have hpd1 : Work.NN.Final.pd n ρ 1 = Work.CR.Flat.polydisc 0 ρ := by
    rw [Work.NN.Final.pd]
    congr 1
    funext j
    rw [one_mul]
  have hpd3sub : Work.NN.Final.pd n ρ (3 / 2) ⊆ Work.NN.Final.pd n ρ 2 :=
    Work.NN.Final.pd_mono hρ (by norm_num)
  have hρbsub2 : Work.CR.Flat.polydisc 0 ρb ⊆ Work.NN.Final.pd n ρ 2 := by
    rw [← hpd3]
    exact Work.NN.Final.pd_mono hρ (by norm_num)
  have hρbsub4 : Work.CR.Flat.polydisc 0 ρb ⊆ Work.NN.Final.pd n ρ 4 := by
    rw [← hpd3]
    exact Work.NN.Final.pd_mono hρ (by norm_num : (3 / 2 : ℝ) ≤ 4)
  -- ## the core theorem
  obtain ⟨ε₀, hε₀, hcore⟩ :=
    dbarCn_smooth_inhom_global (n := n) hn hα0 hα1 (ρb := ρb) (ρ' := ρ) hρbpos hρ hρρb
  refine ⟨ε₀, hε₀, ?_⟩
  intro A hAsm ε hε hsmall hJ f hf h hh1 heq
  -- ## replace `ε` by `ε' = max ε 0`
  set ε' : ℝ := max ε 0 with hε'def
  have hε'0 : 0 ≤ ε' := le_max_right _ _
  have hε'ε : ε ≤ ε' := le_max_left _ _
  have hε'ε₀ : ε' ≤ ε₀ := by
    rcases le_total ε 0 with hh | hh
    · rw [hε'def, max_eq_right hh]; exact hε₀.le
    · rw [hε'def, max_eq_left hh]; exact hε
  -- ## a smooth retraction of `ℂⁿ` into `pd n ρ 4`
  obtain ⟨χA, VA, hχAsm, hχAcs, hχAts, hVAopen, hKVA, hχAone, hχA01⟩ :=
    Work.NN.Core.JFPre.jf_exists_cutoff_polydisc (n := n)
      (σ := fun j => 3 * ρ j) (ρ := fun j => 4 * ρ j) (fun j => by linarith [hρ j])
  set rA : Work.NN.Core.Cn n → Work.NN.Core.Cn n := fun z => χA z • z with hrAdef
  have hrAsm : ∀ m : ℕ, ContDiff ℝ m rA := by
    intro m
    rw [hrAdef]
    have h := (hχAsm.of_le (WithTop.coe_le_coe.mpr le_top)).smul
      (contDiff_id : ContDiff ℝ m (id : Work.NN.Core.Cn n → Work.NN.Core.Cn n))
    convert h using 1
    funext z; rfl
  have hrAim : ∀ z, rA z ∈ Work.NN.Final.pd n ρ 4 := by
    intro z
    have h4 : Work.NN.Final.pd n ρ 4 = Work.CR.Flat.polydisc 0 (fun j => 4 * ρ j) := rfl
    rw [h4, hrAdef, Work.CR.Flat.mem_polydisc]
    intro j
    simp only [Pi.smul_apply, Pi.zero_apply, sub_zero]
    by_cases hz : z ∈ Work.CR.Flat.polydisc 0 (fun j => 4 * ρ j)
    · have hzj : ‖z j‖ < 4 * ρ j := by simpa using (Work.CR.Flat.mem_polydisc.mp hz) j
      have hχle : χA z ≤ 1 := (hχA01 z).2
      have hχ0 : 0 ≤ χA z := (hχA01 z).1
      rw [norm_smul, Real.norm_of_nonneg hχ0]
      calc χA z * ‖z j‖ ≤ 1 * ‖z j‖ := mul_le_mul_of_nonneg_right hχle (norm_nonneg _)
        _ = ‖z j‖ := one_mul _
        _ < 4 * ρ j := hzj
    · have hz0 : χA z = 0 := by
        by_contra hc
        exact hz (hχAts (subset_closure (by simpa [Function.mem_support] using hc)))
      rw [hz0, zero_smul, norm_zero]
      linarith [hρ j]
  have hrAfix : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρb → rA z = z := by
    intro z hz
    have hzj : ∀ j, ‖z j‖ ≤ 3 * ρ j := fun j => by
      have h1 : ‖z j‖ < ρb j := by simpa using (Work.CR.Flat.mem_polydisc.mp hz) j
      have h2 : ρb j = (3 / 2) * ρ j := by simp [hρbdef]
      rw [h2] at h1
      linarith [hρ j]
    have hzV : z ∈ VA := hKVA hzj
    rw [hrAdef]
    show χA z • z = z
    rw [hχAone z hzV, one_smul]
  -- ## the globality of `A₀ = A ∘ rA`
  set A₀ : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n :=
    fun z => A (rA z) with hA₀def
  have hA₀sm : ∀ m : ℕ, ContDiff ℝ m A₀ := by
    intro m
    rw [hA₀def, contDiff_iff_contDiffAt]
    intro z
    have h1 : ContDiffAt ℝ m A (rA z) :=
      (hAsm m).contDiffAt ((Work.NN.Final.isOpen_pd ρ 4).mem_nhds (hrAim z))
    exact h1.comp z ((hrAsm m).contDiffAt)
  have hA₀fix : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρb → A₀ z = A z := by
    intro z hz
    show A (rA z) = A z
    rw [hrAfix z hz]
  have hJ₀ : ∀ z v : Work.NN.Core.Cn n,
      (Work.NN.Core.JstdCn n + A₀) z ((Work.NN.Core.JstdCn n + A₀) z v) = -v := by
    intro z v
    have hEq : (Work.NN.Core.JstdCn n + A₀) z = (Work.NN.Core.JstdCn n + A) (rA z) := by
      ext w
      simp only [Pi.add_apply, hA₀def]
      rfl
    rw [hEq]
    exact hJ (rA z) (hrAim z) v
  -- ## a smooth extension of `f`
  obtain ⟨χf, Vf, hχfsm, hχfcs, hχfts, hVfopen, hKVf, hχfone, hχf01⟩ :=
    Work.NN.Core.JFPre.jf_exists_cutoff_polydisc (n := n)
      (σ := ρb) (ρ := fun j => 2 * ρ j) (fun j => by rw [hρbdef]; linarith [hρ j])
  set rf : Work.NN.Core.Cn n → Work.NN.Core.Cn n := fun z => χf z • z with hrfdef
  have hrfsm : ∀ m : ℕ, ContDiff ℝ m rf := by
    intro m
    rw [hrfdef]
    have h := (hχfsm.of_le (WithTop.coe_le_coe.mpr le_top)).smul
      (contDiff_id : ContDiff ℝ m (id : Work.NN.Core.Cn n → Work.NN.Core.Cn n))
    convert h using 1
    funext z; rfl
  have hrfim : ∀ z, rf z ∈ Work.NN.Final.pd n ρ 2 := by
    intro z
    have h2 : Work.NN.Final.pd n ρ 2 = Work.CR.Flat.polydisc 0 (fun j => 2 * ρ j) := rfl
    rw [h2, hrfdef, Work.CR.Flat.mem_polydisc]
    intro j
    simp only [Pi.smul_apply, Pi.zero_apply, sub_zero]
    by_cases hz : z ∈ Work.CR.Flat.polydisc 0 (fun j => 2 * ρ j)
    · have hzj : ‖z j‖ < 2 * ρ j := by simpa using (Work.CR.Flat.mem_polydisc.mp hz) j
      have hχle : χf z ≤ 1 := (hχf01 z).2
      have hχ0 : 0 ≤ χf z := (hχf01 z).1
      rw [norm_smul, Real.norm_of_nonneg hχ0]
      calc χf z * ‖z j‖ ≤ 1 * ‖z j‖ := mul_le_mul_of_nonneg_right hχle (norm_nonneg _)
        _ = ‖z j‖ := one_mul _
        _ < 2 * ρ j := hzj
    · have hz0 : χf z = 0 := by
        by_contra hc
        exact hz (hχfts (subset_closure (by simpa [Function.mem_support] using hc)))
      rw [hz0, zero_smul, norm_zero]
      linarith [hρ j]
  have hrffix : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρb → rf z = z := by
    intro z hz
    have hzj : ∀ j, ‖z j‖ ≤ ρb j := fun j => le_of_lt (by
      simpa using (Work.CR.Flat.mem_polydisc.mp hz) j)
    have hzV : z ∈ Vf := hKVf hzj
    rw [hrfdef]
    show χf z • z = z
    rw [hχfone z hzV, one_smul]
  set f₀ : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ := fun z => f (rf z) with hf₀def
  have hf₀sm : ∀ m : ℕ, ContDiff ℝ m f₀ := by
    intro m
    rw [hf₀def, contDiff_iff_contDiffAt]
    intro z
    have h1 : ContDiffAt ℝ m (fun z => f z) (rf z) :=
      (hf m).contDiffAt ((Work.NN.Final.isOpen_pd ρ 2).mem_nhds (hrfim z))
    exact h1.comp z ((hrfsm m).contDiffAt)
  have hf₀fix : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρb → f₀ z = f z := by
    intro z hz
    show f (rf z) = f z
    rw [hrffix z hz]
  -- ## the smallness of `A₀` on `polydisc 0 ρb`
  have hsmall₀ : ∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => A₀ z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρb) ≤ ENNReal.ofReal ε' := by
    intro i j
    have hcongr : Work.CR.Flat.holderNorm 0 α (fun z => A₀ z (Pi.single i 1) j)
        (Work.CR.Flat.polydisc 0 ρb)
        = Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
          (Work.CR.Flat.polydisc 0 ρb) :=
      Work.NN.Core.holderNorm_congr (fun z hz => by rw [hA₀fix z hz])
    rw [hcongr]
    refine (Work.CR.Flat.holderNorm_mono_set (Work.NN.Final.isOpen_pd ρ 4)
      (Work.CR.Flat.isOpen_polydisc 0 ρb) ?_ 0 α _).trans
      ((hsmall i j).trans (ENNReal.ofReal_le_ofReal hε'ε))
    intro z hz
    exact hρbsub4 hz
  -- ## the equation with the globalised data
  have heq₀ : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρb → ∀ V : Work.NN.Core.Cn n,
      Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A₀) h z V = f₀ z V := by
    intro z hz V
    have hz2 : z ∈ Work.NN.Final.pd n ρ 2 := hρbsub2 hz
    have hstr : (Work.NN.Core.JstdCn n + A₀) z = (Work.NN.Core.JstdCn n + A) z := by
      ext v
      simp only [Pi.add_apply, ContinuousLinearMap.add_apply]
      rw [hA₀fix z hz]
    have hd : Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A₀) h z
        = Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) h z := by
      unfold Work.NN.Core.dbarCn
      rw [hstr]
    rw [hd, heq z hz2 V, hf₀fix z hz]
  -- ## apply the core theorem
  intro k
  have hk := hcore (A := A₀) hA₀sm hε'0 hε'ε₀ hsmall₀ hJ₀ f₀ hf₀sm h
    (hh1.mono hρbsub2) heq₀ k
  exact hpd1 ▸ hk

end Work.NN.Final


/-!
# Hypoellipticity of the perturbed `∂̄`-operator, local form with a smooth inhomogeneous datum

`Work.NN.Final.dbarCn_smooth_inhom_global` (in `dbarCn_smooth_local_of_smooth_datum.lean`) proves
the interior regularity statement `C¹` solution of `∂̄_{Jstd + A} h = f` with `A`, `f` *globally*
`C^∞`, `Jstd + A` almost complex *globally*, and the equation posed on `polydisc 0 ρb`:
then `h` is `C^k` on `polydisc 0 ρ'` for every `k`, whenever `ρ' < ρb`.

The application only knows `A`, `f` and the almost-complexity of `Jstd + A` on the polydisc
`polydisc 0 ρ` on which the equation is posed, and the conclusion is asked on a strictly smaller
polydisc `polydisc 0 ρ'`.  This module removes the global hypotheses, by the standard device:
choose an intermediate radius `ρs` with `ρ' < ρs < ρ`, a smooth bump `χ` equal to `1` on the closed
polydisc of radii `ρs` and supported in `polydisc 0 ρ`, and let `r z = χ z • z` be the resulting
smooth retraction of `ℂⁿ` into `polydisc 0 ρ`, the identity on `polydisc 0 ρs`.  Then
`A₀ = A ∘ r`, `f₀ = f ∘ r` are globally `C^∞`, agree with `A`, `f` on `polydisc 0 ρs`, and
`Jstd + A₀` is almost complex everywhere (because `r` takes its values in `polydisc 0 ρ`), so the
global theorem applies to `A₀`, `f₀` with the base radius `ρs`.
-/

namespace Work.NN.Final

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

noncomputable section

theorem dbarCn_smooth_local_flex {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hρ'ρ : ∀ j, ρ' j < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiffOn ℝ m A (Work.CR.Flat.polydisc 0 ρ)) → ∀ {ε : ℝ}, ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
          (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
        (∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ → ∀ v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        ∀ (f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ),
          (∀ m : ℕ, ContDiffOn ℝ m (fun z => f z) (Work.CR.Flat.polydisc 0 ρ)) →
          ∀ h : Work.NN.Core.Cn n → ℂ,
            ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ) →
            (∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ → ∀ V : Work.NN.Core.Cn n,
              Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) h z V = f z V) →
            ∀ k : ℕ, ContDiffOn ℝ k h (Work.CR.Flat.polydisc 0 ρ') := by
  classical
  -- ## an intermediate radius `ρ' < ρs < ρ`
  set ρs : Fin n → ℝ := fun j => (ρ j + ρ' j) / 2 with hρsdef
  have hρspos : ∀ j, 0 < ρs j := fun j => by rw [hρsdef]; linarith [hρ j, hρ' j]
  have hρ'ρs : ∀ j, ρ' j < ρs j := fun j => by rw [hρsdef]; linarith [hρ'ρ j]
  have hρsρ : ∀ j, ρs j < ρ j := fun j => by rw [hρsdef]; linarith [hρ'ρ j]
  -- ## the global theorem, with base radius `ρs`
  obtain ⟨ε₀, hε₀, hcore⟩ :=
    dbarCn_smooth_inhom_global (n := n) hn hα0 hα1 (ρb := ρs) (ρ' := ρ') hρspos hρ' hρ'ρs
  refine ⟨ε₀, hε₀, ?_⟩
  intro A hA ε hε hsmall hJ f hf h hh1 heq
  -- ## replace `ε` by `ε' = max ε 0` (the global theorem asks for `0 ≤ ε`)
  set ε' : ℝ := max ε 0 with hε'def
  have hε'0 : 0 ≤ ε' := le_max_right _ _
  have hε'ε : ε ≤ ε' := le_max_left _ _
  have hε'ε₀ : ε' ≤ ε₀ := by
    rcases le_total ε 0 with hh | hh
    · rw [hε'def, max_eq_right hh]; exact hε₀.le
    · rw [hε'def, max_eq_left hh]; exact hε
  have hsmall' : ∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε' :=
    fun i j => (hsmall i j).trans (ENNReal.ofReal_le_ofReal hε'ε)
  -- ## a smooth retraction into `polydisc 0 ρ`, the identity on `polydisc 0 ρs`
  obtain ⟨χ, V, hχsm, _hχcs, hχts, _hVopen, hKV, hχone, hχ01⟩ :=
    Work.NN.Core.JFPre.jf_exists_cutoff_polydisc (n := n) (σ := ρs) (ρ := ρ) hρsρ
  set r : Work.NN.Core.Cn n → Work.NN.Core.Cn n := fun z => χ z • z with hrdef
  have hrsm : ∀ m : ℕ, ContDiff ℝ m r := by
    intro m
    rw [hrdef]
    have hχm : ContDiff ℝ m χ := hχsm.of_le (WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤))
    have h := hχm.smul (contDiff_id : ContDiff ℝ m (id : Work.NN.Core.Cn n → Work.NN.Core.Cn n))
    convert h using 1
    funext z; rfl
  have hrim : ∀ z, r z ∈ Work.CR.Flat.polydisc 0 ρ := by
    intro z
    rw [hrdef, Work.CR.Flat.mem_polydisc]
    intro j
    simp only [Pi.smul_apply, Pi.zero_apply, sub_zero]
    by_cases hz : z ∈ Work.CR.Flat.polydisc 0 ρ
    · have hzj : ‖z j‖ < ρ j := by simpa using (Work.CR.Flat.mem_polydisc.mp hz) j
      have hχle : χ z ≤ 1 := (hχ01 z).2
      have hχ0 : 0 ≤ χ z := (hχ01 z).1
      rw [norm_smul, Real.norm_of_nonneg hχ0]
      calc χ z * ‖z j‖ ≤ 1 * ‖z j‖ := mul_le_mul_of_nonneg_right hχle (norm_nonneg _)
        _ = ‖z j‖ := one_mul _
        _ < ρ j := hzj
    · have hz0 : χ z = 0 := by
        by_contra hc
        exact hz (hχts (subset_closure (by simpa [Function.mem_support] using hc)))
      rw [hz0, zero_smul, norm_zero]
      exact hρ j
  have hrifix : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρs → r z = z := by
    intro z hz
    have hzj : ∀ j : Fin n, ‖z j‖ ≤ ρs j :=
      fun j => le_of_lt (by simpa using (Work.CR.Flat.mem_polydisc.mp hz) j)
    have hzV : z ∈ V := hKV hzj
    rw [hrdef]
    show χ z • z = z
    rw [hχone z hzV, one_smul]
  -- ## the globalised perturbation and datum `A₀ = A ∘ r`, `f₀ = f ∘ r`
  set A₀ : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n := fun z => A (r z)
    with hA₀def
  have hA₀sm : ∀ m : ℕ, ContDiff ℝ m A₀ := by
    intro m
    rw [hA₀def, contDiff_iff_contDiffAt]
    intro z
    have h1 : ContDiffAt ℝ m A (r z) :=
      (hA m).contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds (hrim z))
    exact h1.comp z ((hrsm m).contDiffAt)
  have hA₀fix : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρs → A₀ z = A z := by
    intro z hz
    show A (r z) = A z
    rw [hrifix z hz]
  set f₀ : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ := fun z => f (r z) with hf₀def
  have hf₀sm : ∀ m : ℕ, ContDiff ℝ m f₀ := by
    intro m
    rw [hf₀def, contDiff_iff_contDiffAt]
    intro z
    have h1 : ContDiffAt ℝ m (fun z => f z) (r z) :=
      (hf m).contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds (hrim z))
    exact h1.comp z ((hrsm m).contDiffAt)
  have hf₀fix : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρs → f₀ z = f z := by
    intro z hz
    show f (r z) = f z
    rw [hrifix z hz]
  -- ## the smallness of `A₀` on `polydisc 0 ρs`
  have hsmall₀ : ∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => A₀ z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρs) ≤ ENNReal.ofReal ε' := by
    intro i j
    have hcongr : Work.CR.Flat.holderNorm 0 α (fun z => A₀ z (Pi.single i 1) j)
        (Work.CR.Flat.polydisc 0 ρs)
        = Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
          (Work.CR.Flat.polydisc 0 ρs) :=
      Work.NN.Core.holderNorm_congr (fun z hz => by rw [hA₀fix z hz])
    rw [hcongr]
    exact (Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 ρ)
      (Work.CR.Flat.isOpen_polydisc 0 ρs)
      (Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρsρ j))) 0 α _).trans (hsmall' i j)
  -- ## the global almost-complexity of `Jstd + A₀`
  have hJ₀ : ∀ z v : Work.NN.Core.Cn n,
      (Work.NN.Core.JstdCn n + A₀) z ((Work.NN.Core.JstdCn n + A₀) z v) = -v := by
    intro z v
    have hEq : (Work.NN.Core.JstdCn n + A₀) z = (Work.NN.Core.JstdCn n + A) (r z) := by
      ext w
      simp only [Pi.add_apply, hA₀def]
      rfl
    rw [hEq]
    exact hJ (r z) (hrim z) v
  -- ## the equation with the globalised data on `polydisc 0 ρs`
  have heq₀ : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρs → ∀ V : Work.NN.Core.Cn n,
      Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A₀) h z V = f₀ z V := by
    intro z hz V
    have hzρ : z ∈ Work.CR.Flat.polydisc 0 ρ :=
      Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρsρ j)) hz
    have hstr : (Work.NN.Core.JstdCn n + A₀) z = (Work.NN.Core.JstdCn n + A) z := by
      ext v
      simp only [Pi.add_apply, ContinuousLinearMap.add_apply]
      rw [hA₀fix z hz]
    have hd : Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A₀) h z
        = Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) h z := by
      unfold Work.NN.Core.dbarCn
      rw [hstr]
    rw [hd, heq z hzρ V, hf₀fix z hz]
  -- ## apply the global theorem
  intro k
  exact hcore (A := A₀) hA₀sm hε'0 hε'ε₀ hsmall₀ hJ₀ f₀ hf₀sm h
    (hh1.mono (Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρsρ j)))) heq₀ k

end

end Work.NN.Final

