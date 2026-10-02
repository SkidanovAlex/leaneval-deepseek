/-
# Smooth compactly supported approximations of an admissible coefficient

An admissible Beltrami coefficient `μ` (measurable, `‖μ‖ ≤ k < 1` a.e., bounded support) is
approximated a.e. by the mollifications `μ_n = μ ⋆ ρ_n`, where `ρ_n` is a smooth bump at `0` with
`∫ ρ_n = 1` and support shrinking to `{0}`.  The approximants are smooth, compactly supported,
keep the *same* pointwise bound `k`, stay inside a *fixed* ball, and converge to `μ` a.e.

Contents:

* `mollify_bump_*` — the properties of the bump kernels `ρ_n = (Work.MRMT.Weyl.bump n).normed volume`;
* `mollify_admissible_bound`, `mollify_admissible_ball`, `mollify_admissible_integrable`,
  `mollify_admissible_locallyIntegrable` — extraction of the constants and integrability from
  `Admissible μ`;
* `mollify_support_moll_subset` — the support of `ρ ⋆ μ` is contained in `support ρ + support μ`;
* `mollify_norm_moll_le` — a mollification of a function bounded by `k` a.e. is bounded by `k`;
* `mollify_tendsto_integral_norm_moll` — global `L¹` convergence of the mollifications;
* `mollify_ae_tendsto_of_tendsto_integral_norm` — `L¹` convergence implies a.e. convergence along
  a subsequence;
* `mollify_admissible` — the main statement.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Weyl.moll_L1_aux
import Submission.Work.MRMT.Weyl.moll_tendsto_L1_loc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal Convolution Pointwise

namespace Work.MRMT.Found

open Work.MRMT

/-! ## The bump kernels -/

theorem mollify_bump_mass (m : ℕ) :
    ∫ y, (Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ) y = 1 :=
  (Work.MRMT.Weyl.bump m).integral_normed (μ := (volume : Measure ℂ))

theorem mollify_bump_nonneg (m : ℕ) (y : ℂ) :
    0 ≤ (Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ) y :=
  (Work.MRMT.Weyl.bump m).nonneg_normed (μ := (volume : Measure ℂ)) y

theorem mollify_bump_continuous (m : ℕ) :
    Continuous ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) :=
  ((Work.MRMT.Weyl.bump m).contDiff_normed (μ := (volume : Measure ℂ)) (n := ⊤)).continuous

theorem mollify_bump_compactSupport (m : ℕ) :
    HasCompactSupport ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) :=
  (Work.MRMT.Weyl.bump m).hasCompactSupport_normed (μ := (volume : Measure ℂ))

theorem mollify_bump_contDiff (m : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) :=
  (Work.MRMT.Weyl.bump m).contDiff_normed (μ := (volume : Measure ℂ)) (n := ⊤)

theorem mollify_bump_rOut_le_one (m : ℕ) : (Work.MRMT.Weyl.bump m).rOut ≤ 1 := by
  simp only [Work.MRMT.Weyl.bump]
  rw [div_le_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem mollify_bump_support_subset (m : ℕ) :
    Function.support ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) ⊆
      Metric.closedBall 0 1 := by
  intro y hy
  have hyt : y ∈ tsupport ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) :=
    subset_closure hy
  rw [ContDiffBump.tsupport_normed_eq] at hyt
  rw [Metric.mem_closedBall] at hyt ⊢
  exact hyt.trans (mollify_bump_rOut_le_one m)

/-! ## Extracting the constants from an admissible coefficient -/

theorem mollify_admissible_bound {μ : ℂ → ℂ} (hμ : Admissible μ) :
    ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := by
  obtain ⟨k₀, hk₀, hb⟩ := hμ.bound
  refine ⟨max k₀ 0, le_max_right _ _, max_lt_iff.mpr ⟨hk₀, one_pos⟩, ?_⟩
  filter_upwards [hb] with z hz
  exact hz.trans (le_max_left _ _)

theorem mollify_admissible_ball {μ : ℂ → ℂ} (hμ : Admissible μ) :
    ∃ R : ℝ, 0 ≤ R ∧ Function.support μ ⊆ Metric.closedBall 0 R := by
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hμ.bdd
  refine ⟨|R₀|, abs_nonneg _, fun z hz => ?_⟩
  have h₁ : ‖z‖ ≤ R₀ := by
    have := hR₀ hz
    simpa [Metric.mem_closedBall] using this
  rw [Metric.mem_closedBall]
  simpa using h₁.trans (le_abs_self R₀)

theorem mollify_admissible_compactSupport {μ : ℂ → ℂ} (hμ : Admissible μ) :
    HasCompactSupport μ := by
  have := hμ.bdd.isCompact_closure
  simpa [HasCompactSupport, tsupport] using this

theorem mollify_admissible_integrable {μ : ℂ → ℂ} (hμ : Admissible μ) :
    Integrable μ (volume : Measure ℂ) := by
  obtain ⟨k₀, _, hb⟩ := hμ.bound
  exact memLp_one_iff_integrable.mp
    ((mollify_admissible_compactSupport hμ).memLp_of_bound hμ.meas k₀ hb)

theorem mollify_admissible_locallyIntegrable {μ : ℂ → ℂ} (hμ : Admissible μ) :
    LocallyIntegrable μ (volume : Measure ℂ) :=
  (mollify_admissible_integrable hμ).locallyIntegrable

/-! ## The support of a mollification -/

theorem mollify_support_moll_subset {μ : ℂ → ℂ} {ρ : ℂ → ℝ} {r R : ℝ}
    (hρ : Function.support ρ ⊆ Metric.closedBall 0 r)
    (hμ : Function.support μ ⊆ Metric.closedBall 0 R) :
    Function.support (Work.MRMT.Weyl.moll ρ μ) ⊆ Metric.closedBall 0 (r + R) := by
  intro x hx
  have hx' : x ∈ Function.support ρ + Function.support μ := by
    have h := MeasureTheory.support_convolution_subset (f := ρ) (g := μ)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure ℂ)) hx
    simpa [Work.MRMT.Weyl.moll] using h
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  rw [Metric.mem_closedBall, dist_zero_right]
  have ha' : ‖a‖ ≤ r := by
    have h := hρ ha
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have hb' : ‖b‖ ≤ R := by
    have h := hμ hb
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
    _ ≤ r + R := add_le_add ha' hb'

/-! ## Pointwise bound of a mollification -/

theorem mollify_norm_moll_le {μ : ℂ → ℂ} {ρ : ℂ → ℝ} {k : ℝ}
    (hρc : Continuous ρ) (hρcs : HasCompactSupport ρ)
    (hρ1 : ∫ y, ρ y = 1) (hρnn : ∀ y, 0 ≤ ρ y) (_hk : 0 ≤ k)
    (hμli : LocallyIntegrable μ (volume : Measure ℂ))
    (hμb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) (z : ℂ) :
    ‖Work.MRMT.Weyl.moll ρ μ z‖ ≤ k := by
  have hρint : Integrable ρ (volume : Measure ℂ) := hρc.integrable_of_hasCompactSupport hρcs
  have hint : Integrable (fun y : ℂ => (ρ y : ℂ) * μ (z - y)) (volume : Measure ℂ) := by
    have h := hρcs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hρc hμli z
    simpa [MeasureTheory.ConvolutionExistsAt, Work.MRMT.Weyl.moll_apply,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h
  have hbound_ae : ∀ᵐ y ∂(volume : Measure ℂ), ‖μ (z - y)‖ ≤ k := by
    rw [MeasureTheory.ae_iff]
    have hnull : (volume : Measure ℂ) {w : ℂ | ¬ (‖μ w‖ ≤ k)} = 0 := by
      rw [← MeasureTheory.ae_iff]
      exact hμb
    exact (MeasureTheory.Measure.measurePreserving_sub_left (volume : Measure ℂ) z).preimage_null
      hnull
  have hpt : ∀ y : ℂ, ‖(ρ y : ℂ) * μ (z - y)‖ = ρ y * ‖μ (z - y)‖ := fun y => by
    rw [norm_mul]
    congr 1
    exact (RCLike.norm_ofReal (K := ℂ) (ρ y)).trans (abs_of_nonneg (hρnn y))
  have hint_norm : Integrable (fun y : ℂ => ρ y * ‖μ (z - y)‖) (volume : Measure ℂ) :=
    hint.norm.congr (Filter.Eventually.of_forall hpt)
  rw [Work.MRMT.Weyl.moll_apply]
  calc ‖∫ y, (ρ y : ℂ) * μ (z - y)‖
      ≤ ∫ y, ‖(ρ y : ℂ) * μ (z - y)‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y, ρ y * ‖μ (z - y)‖ :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ ≤ ∫ y, ρ y * k := by
        refine MeasureTheory.integral_mono_ae hint_norm (hρint.mul_const k) ?_
        filter_upwards [hbound_ae] with y hy
        exact mul_le_mul_of_nonneg_left hy (hρnn y)
    _ = k := by
        rw [MeasureTheory.integral_mul_const, hρ1, one_mul]

/-! ## Global `L¹` convergence of the mollifications -/

theorem mollify_tendsto_integral_norm_moll {μ : ℂ → ℂ}
    (hμli : LocallyIntegrable μ (volume : Measure ℂ)) {R : ℝ}
    (hμ : Function.support μ ⊆ Metric.closedBall 0 R) :
    Filter.Tendsto
      (fun n : ℕ => ∫ z,
        ‖Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump n).normed (volume : Measure ℂ)) μ z - μ z‖)
      Filter.atTop (nhds 0) := by
  have hsupp_moll : ∀ m : ℕ, Function.support
      (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ) ⊆
      Metric.closedBall 0 (1 + R) := fun m =>
    mollify_support_moll_subset (mollify_bump_support_subset m) hμ
  have hmain : Filter.Tendsto
      (fun n : ℕ => ∫ z in Metric.closedBall (0 : ℂ) (R + 1),
        ‖Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump n).normed (volume : Measure ℂ)) μ z - μ z‖)
      Filter.atTop (nhds 0) :=
    Work.MRMT.Weyl.moll_tendsto_L1_loc hμli Work.MRMT.Weyl.bump Work.MRMT.Weyl.tendsto_rOut_bump
      (isCompact_closedBall (0 : ℂ) (R + 1))
  refine hmain.congr' (Filter.Eventually.of_forall fun n => ?_)
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Metric.closedBall (0 : ℂ) (R + 1))
    (f := fun z => ‖Work.MRMT.Weyl.moll
      ((Work.MRMT.Weyl.bump n).normed (volume : Measure ℂ)) μ z - μ z‖) ?_
  intro z hz
  have hz' : R + 1 < ‖z‖ := by
    have h := hz
    simp only [Metric.mem_closedBall, dist_zero_right] at h
    linarith
  have hμz : μ z = 0 := by
    by_contra hne
    have h2 := hμ hne
    simp only [Metric.mem_closedBall, dist_zero_right] at h2
    linarith
  have hmz : Work.MRMT.Weyl.moll
      ((Work.MRMT.Weyl.bump n).normed (volume : Measure ℂ)) μ z = 0 := by
    by_contra hne
    have h3 := hsupp_moll n hne
    simp only [Metric.mem_closedBall, dist_zero_right] at h3
    linarith
  rw [hμz, hmz, sub_zero, norm_zero]

/-! ## `L¹` convergence implies a.e. convergence along a subsequence -/

theorem mollify_ae_tendsto_of_tendsto_integral_norm {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ n, Integrable (f n) (volume : Measure ℂ))
    (hg : Integrable g (volume : Measure ℂ))
    (h : Filter.Tendsto (fun n => ∫ z, ‖f n z - g z‖) Filter.atTop (nhds 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂(volume : Measure ℂ),
        Filter.Tendsto (fun n => f (ns n) z) Filter.atTop (nhds (g z)) := by
  have hint : ∀ n, Integrable (fun z => f n z - g z) (volume : Measure ℂ) :=
    fun n => (hf n).sub hg
  have heLp : Filter.Tendsto (fun n => eLpNorm (fun z => f n z - g z) 1 (volume : Measure ℂ))
      Filter.atTop (nhds 0) := by
    have h1 : ∀ n, eLpNorm (fun z => f n z - g z) 1 (volume : Measure ℂ)
        = ENNReal.ofReal (∫ z, ‖f n z - g z‖) := by
      intro n
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hint n).aestronglyMeasurable,
        ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    have h2 : Filter.Tendsto (fun n => ENNReal.ofReal (∫ z, ‖f n z - g z‖))
        Filter.atTop (nhds (ENNReal.ofReal 0)) :=
      ENNReal.continuous_ofReal.tendsto 0 |>.comp h
    rw [ENNReal.ofReal_zero] at h2
    exact h2.congr' (Filter.Eventually.of_forall fun n => (h1 n).symm)
  have hTIM : MeasureTheory.TendstoInMeasure (volume : Measure ℂ) (fun n => f n) Filter.atTop g :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (p := 1) one_ne_zero
      ENNReal.one_ne_top heLp
  exact MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae hTIM

/-! ## The main statement -/

theorem mollify_admissible {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ) :
    ∃ (k M : ℝ) (μn : ℕ → ℂ → ℂ),
      0 ≤ k ∧ k < 1 ∧ 0 ≤ M ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) ∧
      (∀ z : ℂ, μ z ≠ 0 → ‖z‖ ≤ M) ∧
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n)) ∧
      (∀ n, HasCompactSupport (μn n)) ∧
      (∀ n z, ‖μn n z‖ ≤ k) ∧
      (∀ n z, μn n z ≠ 0 → ‖z‖ ≤ M) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
        Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds (μ z))) := by
  obtain ⟨k, hk0, hk1, hμb⟩ := mollify_admissible_bound hμ
  obtain ⟨R, hR0, hsupp⟩ := mollify_admissible_ball hμ
  have hli : LocallyIntegrable μ (volume : Measure ℂ) := mollify_admissible_locallyIntegrable hμ
  have hintμ : Integrable μ (volume : Measure ℂ) := mollify_admissible_integrable hμ
  have hcd : ∀ m : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ) := by
    intro m
    exact Work.MRMT.Weyl.contDiff_moll (mollify_bump_contDiff m)
      (mollify_bump_compactSupport m) hli
  have hcs_moll : ∀ m : ℕ, HasCompactSupport
      (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ) := by
    intro m
    have hsub : Function.support
        (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ) ⊆
        Metric.closedBall 0 (1 + R) :=
      mollify_support_moll_subset (mollify_bump_support_subset m) hsupp
    have hb : Bornology.IsBounded (Function.support
        (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ)) :=
      Metric.isBounded_closedBall.subset hsub
    have hcomp := hb.isCompact_closure
    simpa [HasCompactSupport, tsupport] using hcomp
  have hnorm_moll : ∀ m : ℕ, ∀ z : ℂ,
      ‖Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ z‖ ≤ k := by
    intro m z
    exact mollify_norm_moll_le (mollify_bump_continuous m) (mollify_bump_compactSupport m)
      (mollify_bump_mass m) (mollify_bump_nonneg m) hk0 hli hμb z
  have hsupp_moll : ∀ m : ℕ, ∀ z : ℂ,
      Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ z ≠ 0 →
        ‖z‖ ≤ R + 1 := by
    intro m z hz
    have h1 : z ∈ Metric.closedBall 0 (1 + R) :=
      mollify_support_moll_subset (mollify_bump_support_subset m) hsupp hz
    simp only [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  have hint_moll : ∀ m : ℕ, Integrable
      (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ)
      (volume : Measure ℂ) := fun m =>
    (hcd m).continuous.integrable_of_hasCompactSupport (hcs_moll m)
  have hL1 := mollify_tendsto_integral_norm_moll hli hsupp
  obtain ⟨ns, hns, hae⟩ := mollify_ae_tendsto_of_tendsto_integral_norm hint_moll hintμ hL1
  refine ⟨k, R + 1, fun m =>
    Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump (ns m)).normed (volume : Measure ℂ)) μ,
    hk0, hk1, by linarith, hμb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h1 : z ∈ Metric.closedBall 0 R := hsupp hz
    simp only [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  · intro m
    exact hcd (ns m)
  · intro m
    exact hcs_moll (ns m)
  · intro m z
    exact hnorm_moll (ns m) z
  · intro m z hz
    exact hsupp_moll (ns m) z hz
  · exact hae

end Work.MRMT.Found
