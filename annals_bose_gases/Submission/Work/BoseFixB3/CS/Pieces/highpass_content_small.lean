import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Fourier.Notation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.cubInd_kinFT_l2
import Submission.Work.BoseFixB3.CS.Pieces.highpass_difference
import Submission.Work.BoseFixB3.CS.Pieces.highpass_shell_l2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.highpass_content_small`

The high-pass content of a smooth bump inside the box is super-polynomially small:

`|∫_{Λ(ℓ)}(ψ − f_L(√−Δ)ψ)| ≤ C·M·ℓ³/(ℓκ)^40`

for every `ψ ∈ C^∞` supported in the ball of radius `ℓ/2` whose derivatives up to order `40`
obey `‖D^jψ‖ ≤ M/ℓ^j` (`f_L` is the free-space low-momentum multiplier `lowMult` of the
corpus, the cube is `acube ℓ`).

Route: the two momentum representations (the multiplier pairing `highpass_difference` and the
Plancherel mass `cubInd_kinFT_l2`) turn the difference into the boundary-layer pairing
`(2π)⁻³∫_p (1 − f(‖p‖/κ))·conj(kinFT 1_Λ p)·kinFT ψ p`; the weight vanishes for `‖p‖ ≤ κ`,
so Cauchy–Schwarz against the two `L²` masses — the shell bound `highpass_shell_l2`
(`κ^{-40}` decay from the order-`40` derivative) and the box indicator's mass `(2π)³ℓ³` —
gives the claim.
-/

noncomputable section
open MeasureTheory Filter Metric
open scoped Real Topology BigOperators FourierTransform

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000


/-! ### Elementary facts about the cut-off -/

private lemma fc_nonneg (fc : Work.BoseBoxFix.LowCut) (s : ℝ) : 0 ≤ fc.f s := by
  rcases le_total s 2 with h | h
  · have := fc.anti h
    rw [fc.zero 2 le_rfl] at this
    exact this
  · rw [fc.zero s h]

private lemma fc_le_one (fc : Work.BoseBoxFix.LowCut) (s : ℝ) : fc.f s ≤ 1 := by
  rcases le_total s 1 with h | h
  · rw [fc.one s h]
  · have := fc.anti h
    rw [fc.one 1 le_rfl] at this
    exact this

private lemma fc_eq_one_of_norm_le (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ)
    {p : E3} (hp : ‖p‖ ≤ κ) : fc.f (‖p‖ / κ) = 1 := by
  refine fc.one _ ?_
  rw [div_le_one hκ]
  exact hp

private lemma hasCompactSupport_cut (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (fun p : E3 => fc.f (‖p‖ / κ)) := by
  refine HasCompactSupport.intro (K := Metric.closedBall 0 (2 * κ))
    (isCompact_closedBall 0 (2 * κ)) ?_
  intro p hp
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hp
  refine fc.zero _ ?_
  rw [le_div_iff₀ hκ]
  linarith [not_le.mp hp]

/-! ### Support of a function vanishing in the exterior ball -/

private lemma norm_le_of_support {ψ : E3 → ℝ} {ℓ : ℝ}
    (hsupp : ∀ y : E3, ℓ / 2 ≤ ‖y‖ → ψ y = 0) :
    ∀ y ∈ Function.support ψ, ‖y‖ ≤ ℓ / 2 := by
  intro y hy
  by_contra hcon
  exact hy (hsupp y (le_of_lt (lt_of_not_ge hcon)))

private lemma support_subset_acube {ψ : E3 → ℝ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hsupp : ∀ y : E3, ℓ / 2 ≤ ‖y‖ → ψ y = 0) :
    Function.support ψ ⊆ Submission.BoseGases.acube ℓ :=
  fun y hy => Submission.BoseGases.mem_acube_of_norm_le hℓ (norm_le_of_support hsupp y hy)

private lemma indicator_acube_eq {ψ : E3 → ℝ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hsupp : ∀ y : E3, ℓ / 2 ≤ ‖y‖ → ψ y = 0) :
    (Submission.BoseGases.acube ℓ).indicator ψ = ψ := by
  funext y
  by_cases hy : y ∈ Submission.BoseGases.acube ℓ
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy]
    exact (hsupp y (le_of_lt (lt_of_not_ge (fun hle =>
      hy (Submission.BoseGases.mem_acube_of_norm_le hℓ hle))))).symm

private lemma hasCompactSupport_of_hsupp {ψ : E3 → ℝ} {ℓ : ℝ} (_hℓ : 0 < ℓ)
    (hsupp : ∀ y : E3, ℓ / 2 ≤ ‖y‖ → ψ y = 0) : HasCompactSupport ψ :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (ℓ / 2))
    (fun y hy => by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact norm_le_of_support hsupp y hy)

private lemma cubInd_eq_indicator (ℓ : ℝ) :
    (fun z : E3 =>
        (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ))
      = (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℂ)) := by
  funext z
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]; norm_num
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]; norm_num

theorem highpass_content_small :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ), 0 < κ → 0 < ℓ →
      ∀ (ψ : EuclideanSpace ℝ (Fin 3) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∀ y, ℓ / 2 ≤ ‖y‖ → ψ y = 0) →
      (∀ M : ℝ, 0 ≤ M → (∀ y, |ψ y| ≤ M) →
        (∀ (j : ℕ), j ≤ 40 → ∀ y, ‖iteratedFDeriv ℝ j ψ y‖ ≤ M / ℓ ^ j) →
        |∫ y in Submission.BoseGases.acube ℓ,
            (ψ y - Work.BoseBoxFix.lowMult fc κ ℓ ψ y)| ≤ C * M * ℓ ^ 3 / (ℓ * κ) ^ 40) := by
  obtain ⟨C₁, hC₁, hshell⟩ := highpass_shell_l2
  refine ⟨C₁ + 1, by linarith, ?_⟩
  intro fc κ ℓ hκ hℓ ψ hψ hsupp M hM hψM hder
  have hℓ0 : (0 : ℝ) ≤ ℓ := le_of_lt hℓ
  have hcs : HasCompactSupport ψ := hasCompactSupport_of_hsupp hℓ hsupp
  set Ψ : E3 → ℂ := fun z => (ψ z : ℂ) with hΨeq
  set Θ : E3 → ℂ := fun z =>
    (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ) with hΘeq
  set shell : Set E3 := {p : E3 | κ ≤ ‖p‖} with hshell_eq
  have hshell_meas : MeasurableSet shell := by
    rw [hshell_eq]
    exact (isClosed_le continuous_const continuous_norm).measurableSet
  -- the L² facts for the two `kinFT` transforms
  have hΘkin : MemLp (Submission.BoseGases.kinFT Θ) 2 (volume : Measure E3) := by
    rw [hΘeq, cubInd_eq_indicator ℓ]
    exact Work.BoseKinLoc.Momentum.memLp_kinFT
      (memLp_one_iff_integrable.mp (memLp_indicator_const (μ := (volume : Measure E3)) (E := ℂ) 1
        (Submission.BoseGases.acube_measurable ℓ) (1 : ℂ)
        (Or.inr (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ0)))))
      (memLp_indicator_const (μ := (volume : Measure E3)) (E := ℂ) 2
        (Submission.BoseGases.acube_measurable ℓ) (1 : ℂ)
        (Or.inr (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ0))))
  have hΘmem : MemLp (fun p : E3 => ‖Submission.BoseGases.kinFT Θ p‖) 2 (volume : Measure E3) :=
    hΘkin.norm
  have hΘint2 : Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT Θ p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hΘkin.aestronglyMeasurable).mp hΘkin
  have hψint : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hcs
  have hcspow : HasCompactSupport (fun x : E3 => ψ x ^ 2) := by
    have h := hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    simpa [Function.comp_def] using h
  have hψsq : Integrable (fun x : E3 => ψ x ^ 2) :=
    (hψ.continuous.pow 2).integrable_of_hasCompactSupport hcspow
  have hψL2 : MemLp ψ 2 (volume : Measure E3) :=
    (memLp_two_iff_integrable_sq hψ.continuous.aestronglyMeasurable).mpr hψsq
  have hΨkin : MemLp (Submission.BoseGases.kinFT Ψ) 2 (volume : Measure E3) := by
    rw [hΨeq]
    exact Work.BoseKinLoc.Momentum.memLp_kinFT hψint.ofReal hψL2.ofReal
  have hΨmem : MemLp (fun p : E3 => ‖Submission.BoseGases.kinFT Ψ p‖) 2 (volume : Measure E3) :=
    hΨkin.norm
  have hΨint2 : Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT Ψ p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hΨkin.aestronglyMeasurable).mp hΨkin
  -- the high-pass pair
  set F : E3 → ℝ := shell.indicator (fun p : E3 => ‖Submission.BoseGases.kinFT Θ p‖) with hFeq
  set G : E3 → ℝ := shell.indicator (fun p : E3 => ‖Submission.BoseGases.kinFT Ψ p‖) with hGeq
  have hFmem : MemLp F 2 (volume : Measure E3) := by
    rw [hFeq]; exact hΘmem.indicator hshell_meas
  have hGmem : MemLp G 2 (volume : Measure E3) := by
    rw [hGeq]; exact hΨmem.indicator hshell_meas
  -- (2) pointwise bound by the shell pairing
  have hpt : ∀ p : E3,
      |(1 - fc.f (‖p‖ / κ)) * ((starRingEnd ℂ) (Submission.BoseGases.kinFT Θ p)
          * Submission.BoseGases.kinFT Ψ p).re| ≤ F p * G p := by
    intro p
    have hre : |((starRingEnd ℂ) (Submission.BoseGases.kinFT Θ p)
        * Submission.BoseGases.kinFT Ψ p).re|
        ≤ ‖Submission.BoseGases.kinFT Θ p‖ * ‖Submission.BoseGases.kinFT Ψ p‖ :=
      (Complex.abs_re_le_norm _).trans (le_of_eq (by rw [norm_mul, Complex.norm_conj]))
    by_cases hp : p ∈ shell
    · have hf0 : 0 ≤ fc.f (‖p‖ / κ) := fc_nonneg fc _
      have hf1 : fc.f (‖p‖ / κ) ≤ 1 := fc_le_one fc _
      have h1 : |1 - fc.f (‖p‖ / κ)| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith, by linarith⟩
      have hFp : F p = ‖Submission.BoseGases.kinFT Θ p‖ := by
        rw [hFeq]; exact Set.indicator_of_mem hp _
      have hGp : G p = ‖Submission.BoseGases.kinFT Ψ p‖ := by
        rw [hGeq]; exact Set.indicator_of_mem hp _
      rw [hFp, hGp, abs_mul]
      calc |1 - fc.f (‖p‖ / κ)| * |((starRingEnd ℂ) (Submission.BoseGases.kinFT Θ p)
              * Submission.BoseGases.kinFT Ψ p).re|
          ≤ 1 * (‖Submission.BoseGases.kinFT Θ p‖ * ‖Submission.BoseGases.kinFT Ψ p‖) :=
            mul_le_mul h1 hre (abs_nonneg _) zero_le_one
        _ = ‖Submission.BoseGases.kinFT Θ p‖ * ‖Submission.BoseGases.kinFT Ψ p‖ := one_mul _
    · have hlt : ‖p‖ < κ := lt_of_not_ge (fun h => hp (by rw [hshell_eq]; exact h))
      have hf1 : fc.f (‖p‖ / κ) = 1 := fc_eq_one_of_norm_le fc hκ (le_of_lt hlt)
      have hFp : F p = 0 := by rw [hFeq]; exact Set.indicator_of_notMem hp _
      have hGp : G p = 0 := by rw [hGeq]; exact Set.indicator_of_notMem hp _
      rw [hFp, hGp, mul_zero]
      simp [hf1]
  -- (3) the integral bound
  have h_int_le : |∫ p : E3, (1 - fc.f (‖p‖ / κ)) *
        ((starRingEnd ℂ) (Submission.BoseGases.kinFT Θ p) * Submission.BoseGases.kinFT Ψ p).re|
      ≤ ∫ p : E3, F p * G p :=
    abs_integral_le_integral_abs.trans
      (integral_mono_of_nonneg (Eventually.of_forall fun p => abs_nonneg _)
        (MemLp.integrable_mul hFmem hGmem) (Eventually.of_forall hpt))
  -- (4) Cauchy–Schwarz
  have hF2nn : 0 ≤ ∫ p : E3, F p ^ 2 := integral_nonneg fun p => sq_nonneg _
  have hG2nn : 0 ≤ ∫ p : E3, G p ^ 2 := integral_nonneg fun p => sq_nonneg _
  have hCS := Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt hFmem hGmem
  have hFG2 : (∫ p : E3, F p * G p) ^ 2
      ≤ (∫ p : E3, F p ^ 2) * (∫ p : E3, G p ^ 2) := by
    calc (∫ p : E3, F p * G p) ^ 2
        = |∫ p : E3, F p * G p| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt (∫ p : E3, F p ^ 2) * Real.sqrt (∫ p : E3, G p ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hCS 2
      _ = (∫ p : E3, F p ^ 2) * (∫ p : E3, G p ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hF2nn, Real.sq_sqrt hG2nn]
  -- (5) the two masses
  have hFsq_eq : (∫ p : E3, F p ^ 2) = ∫ p in shell, ‖Submission.BoseGases.kinFT Θ p‖ ^ 2 := by
    rw [hFeq]
    rw [show (fun p : E3 => (shell.indicator (fun p : E3 => ‖Submission.BoseGases.kinFT Θ p‖)) p ^ 2)
        = shell.indicator (fun p : E3 => ‖Submission.BoseGases.kinFT Θ p‖ ^ 2) from by
          funext p
          by_cases hp : p ∈ shell
          · simp [Set.indicator_of_mem hp]
          · simp [Set.indicator_of_notMem hp]]
    rw [integral_indicator hshell_meas]
  have hFA : (∫ p : E3, F p ^ 2) ≤ (2 * Real.pi) ^ 3 * ℓ ^ 3 := by
    rw [hFsq_eq]
    refine (setIntegral_le_integral hΘint2 (Eventually.of_forall fun p => sq_nonneg _)).trans
      (le_of_eq ?_)
    rw [hΘeq]
    exact cubInd_kinFT_l2 ℓ hℓ0
  have hGsq_eq : (∫ p : E3, G p ^ 2) = ∫ p in shell, ‖Submission.BoseGases.kinFT Ψ p‖ ^ 2 := by
    rw [hGeq]
    rw [show (fun p : E3 => (shell.indicator (fun p : E3 => ‖Submission.BoseGases.kinFT Ψ p‖)) p ^ 2)
        = shell.indicator (fun p : E3 => ‖Submission.BoseGases.kinFT Ψ p‖ ^ 2) from by
          funext p
          by_cases hp : p ∈ shell
          · simp [Set.indicator_of_mem hp]
          · simp [Set.indicator_of_notMem hp]]
    rw [integral_indicator hshell_meas]
  have hGB : (∫ p : E3, G p ^ 2)
      ≤ C₁ * (κ ^ 80)⁻¹ * ∫ x : E3, ‖iteratedFDeriv ℝ 40 ψ x‖ ^ 2 := by
    rw [hGsq_eq]
    have h3 := hshell ψ κ hκ hψ hcs
    rwa [← hshell_eq, ← hΨeq] at h3
  -- (6) the order-40 derivative bound
  have hsupp_norm : ∀ x ∈ tsupport ψ, ‖x‖ ≤ ℓ / 2 := by
    intro x hx
    have h := closure_minimal (fun y hy => by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact norm_le_of_support hsupp y hy) Metric.isClosed_closedBall hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using h
  have hsupp40 : Function.support (iteratedFDeriv ℝ 40 ψ) ⊆ Submission.BoseGases.acube ℓ :=
    fun x hx => Submission.BoseGases.mem_acube_of_norm_le hℓ0
      (hsupp_norm x (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := ψ) 40 hx))
  have hz40 : ∀ x ∉ Submission.BoseGases.acube ℓ, ‖iteratedFDeriv ℝ 40 ψ x‖ ^ 2 = 0 := by
    intro x hx
    have hx' : iteratedFDeriv ℝ 40 ψ x = 0 := by
      by_contra hcon
      exact hx (hsupp40 (Function.mem_support.mpr hcon))
    rw [hx', norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hD : ∫ x : E3, ‖iteratedFDeriv ℝ 40 ψ x‖ ^ 2 ≤ M ^ 2 * (ℓ ^ 80)⁻¹ * ℓ ^ 3 := by
    have h40 : ∀ x : E3, ‖iteratedFDeriv ℝ 40 ψ x‖ ≤ M * (ℓ ^ 40)⁻¹ := by
      intro x
      have h := hder 40 le_rfl x
      rwa [div_eq_mul_inv] at h
    have hptD : ∀ x : E3, ‖iteratedFDeriv ℝ 40 ψ x‖ ^ 2 ≤
        (M * (ℓ ^ 40)⁻¹) ^ 2 * (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) x := by
      intro x
      by_cases hx : x ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem hx, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) (h40 x) 2
      · rw [Set.indicator_of_notMem hx, mul_zero, hz40 x hx]
    have hgint : Integrable (fun x : E3 => (M * (ℓ ^ 40)⁻¹) ^ 2 *
        (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) x) :=
      (memLp_one_iff_integrable.mp (memLp_indicator_const (μ := (volume : Measure E3)) (E := ℝ) 1
        (Submission.BoseGases.acube_measurable ℓ) (1 : ℝ)
        (Or.inr (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ0))))).const_mul _
    calc ∫ x : E3, ‖iteratedFDeriv ℝ 40 ψ x‖ ^ 2
        ≤ ∫ x : E3, (M * (ℓ ^ 40)⁻¹) ^ 2 *
            (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) x :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hgint
            (Eventually.of_forall hptD)
      _ = (M * (ℓ ^ 40)⁻¹) ^ 2 * ℓ ^ 3 := by
          rw [integral_const_mul, integral_indicator_const (1 : ℝ)
            (Submission.BoseGases.acube_measurable ℓ), smul_eq_mul, mul_one, Measure.real,
            Submission.BoseGases.acube_volume ℓ hℓ0, ENNReal.toReal_ofReal (by positivity)]
      _ = M ^ 2 * (ℓ ^ 80)⁻¹ * ℓ ^ 3 := by
          rw [mul_pow, inv_pow, ← pow_mul, show (40 : ℕ) * 2 = 80 from by norm_num]
  -- (7) assembly
  set I : ℝ := ∫ y in Submission.BoseGases.acube ℓ, (ψ y - Work.BoseBoxFix.lowMult fc κ ℓ ψ y)
    with hIeq
  set J : ℝ := ∫ p : E3, (1 - fc.f (‖p‖ / κ)) *
    ((starRingEnd ℂ) (Submission.BoseGases.kinFT Θ p) * Submission.BoseGases.kinFT Ψ p).re
    with hJeq
  have hIJ : I = ((2 * Real.pi) ^ 3)⁻¹ * J := by
    rw [hIeq, hJeq, hΘeq, hΨeq]
    exact highpass_difference hκ hℓ hψ.continuous hcs hsupp
  have hJabs : |J| ≤ ∫ p : E3, F p * G p := by
    rw [hJeq]; exact h_int_le
  have hJs : J ^ 2 ≤ (∫ p : E3, F p * G p) ^ 2 := by
    rw [← sq_abs J]
    exact pow_le_pow_left₀ (abs_nonneg _) hJabs 2
  have hI2 : |I| ^ 2 ≤ C₁ * ((2 * Real.pi) ^ 3)⁻¹ *
      (M ^ 2 * ℓ ^ 6 * (ℓ ^ 80)⁻¹ * (κ ^ 80)⁻¹) := by
    have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
    have h1 : |I| ^ 2 = (((2 * Real.pi) ^ 3)⁻¹) ^ 2 * J ^ 2 := by
      rw [hIJ, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹),
        mul_pow, sq_abs]
    rw [h1]
    calc (((2 * Real.pi) ^ 3)⁻¹) ^ 2 * J ^ 2
        ≤ (((2 * Real.pi) ^ 3)⁻¹) ^ 2 * (∫ p : E3, F p * G p) ^ 2 :=
          mul_le_mul_of_nonneg_left hJs (by positivity)
      _ ≤ (((2 * Real.pi) ^ 3)⁻¹) ^ 2 * ((∫ p : E3, F p ^ 2) * (∫ p : E3, G p ^ 2)) :=
          mul_le_mul_of_nonneg_left hFG2 (by positivity)
      _ ≤ (((2 * Real.pi) ^ 3)⁻¹) ^ 2 *
            (((2 * Real.pi) ^ 3 * ℓ ^ 3) *
              (C₁ * (κ ^ 80)⁻¹ * (M ^ 2 * (ℓ ^ 80)⁻¹ * ℓ ^ 3))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hFA (hGB.trans (mul_le_mul_of_nonneg_left hD (by positivity)))
            (by positivity) (by positivity)
      _ = C₁ * ((2 * Real.pi) ^ 3)⁻¹ * (M ^ 2 * ℓ ^ 6 * (ℓ ^ 80)⁻¹ * (κ ^ 80)⁻¹) := by
          have hπ3 : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
          have h1 : (ℓ ^ 80 : ℝ) ≠ 0 := pow_ne_zero _ (ne_of_gt hℓ)
          have h2 : (κ ^ 80 : ℝ) ≠ 0 := pow_ne_zero _ (ne_of_gt hκ)
          field_simp
          try ring
  have hK : C₁ * ((2 * Real.pi) ^ 3)⁻¹ ≤ (C₁ + 1) ^ 2 := by
    have h1 : ((2 * Real.pi) ^ 3)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      calc (1 : ℝ) = 1 ^ 3 := by norm_num
        _ ≤ (2 * Real.pi) ^ 3 :=
            pow_le_pow_left₀ zero_le_one (by linarith [Real.pi_gt_three]) 3
    nlinarith [hC₁, h1]
  have hP : 0 ≤ M ^ 2 * ℓ ^ 6 * (ℓ ^ 80)⁻¹ * (κ ^ 80)⁻¹ := by positivity
  have hfin : |I| ^ 2 ≤ ((C₁ + 1) * M * ℓ ^ 3 / (ℓ * κ) ^ 40) ^ 2 := by
    have hT2 : ((C₁ + 1) * M * ℓ ^ 3 / (ℓ * κ) ^ 40) ^ 2
        = (C₁ + 1) ^ 2 * (M ^ 2 * ℓ ^ 6 * (ℓ ^ 80)⁻¹ * (κ ^ 80)⁻¹) := by
      have h1 : (ℓ ^ 80 : ℝ) ≠ 0 := pow_ne_zero _ (ne_of_gt hℓ)
      have h2 : (κ ^ 80 : ℝ) ≠ 0 := pow_ne_zero _ (ne_of_gt hκ)
      have h3 : ((ℓ * κ) ^ 40 : ℝ) ≠ 0 :=
        pow_ne_zero _ (mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hκ))
      field_simp
      try ring
    rw [hT2]
    exact hI2.trans (mul_le_mul_of_nonneg_right hK hP)
  have hgoal : |I| ≤ (C₁ + 1) * M * ℓ ^ 3 / (ℓ * κ) ^ 40 := by
    have h := sq_le_sq.mp hfin
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by linarith [hC₁]) hM)
      (pow_nonneg (le_of_lt hℓ) 3))
      (pow_nonneg (mul_nonneg (le_of_lt hℓ) (le_of_lt hκ)) 40))] at h
    simpa using h
  exact hgoal

end Work.BoseFixB3.CS.Pieces
