import Submission.FUP.HormanderExact
import Submission.Commons.MeasureTheory.Integral.exists_approximate_identity_complex_ae
import Submission.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_locallyL2Bounded
import Submission.FUP.DbarMollifyWt
import Submission.FUP.DbarLocalize
import Submission.FUP.PSHMollify
import Submission.Commons.MeasureTheory.Integral.tendsto_convolution_le
import Submission.Commons.MeasureTheory.Integral.exists_approximate_identity_complex

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Hörmander's `∂̄`-theorem for a plurisubharmonic weight: the approximation layer

`Submission/FUP/HormanderExact.lean` proves Hörmander's theorem for a **smooth** (`C^∞`) weight
`φ` with a *pointwise* Hermitian Hessian bound (`HessBound φ κ`) and **exact** data `η = ∂̄h`.
This module starts the passage to an arbitrary **upper semicontinuous, locally bounded** weight,
which is the form needed by §5 of Cohen's paper (where the weight `section5Phi ρ u u₀` is built
from a merely u.s.c. plurisubharmonic `u`).

The strategy (see `ROADMAP.md`, session 45) is:

* mollify the *weight*: `ψ_n := mollWt (K n) φ`, `κ_n := mollWt (K n) κ` for an approximate
  identity `K n`; `DbarDbarPos.mollify` (`Submission/FUP/DbarMollifyWt.lean`) transfers the
  distributional positivity, and since `ψ_n` is smooth this gives `HessBound ψ_n κ_n`;
* apply the smooth-weight theorem to get `g_n` with `∂̄g_n = ∂̄h` and
  `∫⁻|g_n|²e^{-ψ_n} ≤ T_n := ∫⁻|∂̄h|²e^{-ψ_n}/κ_n`;
* `H_n := g_n - h` is holomorphic; local `L²`-bounds plus **Montel** give a subsequence converging
  locally uniformly to a holomorphic `H`;
* **Fatou** gives `∫|H+h|²e^{-φ} ≤ liminf T_n = T` (using only `limsup ψ_n ≤ φ`, i.e. upper
  semicontinuity).

This file contains the elementary layer: local integrability of a u.s.c. locally bounded weight,
the positivity and smoothness of the mollified weights, the Hessian bound, and one-sided
convergence of the mollifications.
-/

namespace Submission.FUP

variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-- **Hörmander's `∂̄`-theorem for an upper semicontinuous locally bounded weight and exact data.**

This is the provable form of `HormanderStatement` (`Submission/FUP/Hormander.lean`): the data is
`η = ∂̄h` for a smooth compactly supported `h` — the only case used by §5 — and the weight only has
to be upper semicontinuous and locally bounded (in addition to the distributional positivity
`DbarDbarPos φ κ`). -/
def HormanderStatementExact : Prop :=
  ∀ (φ : ℂᵈ → ℝ) (κ : ℂᵈ → ℝ), UpperSemicontinuous φ →
    LocallyIntegrable φ (volume : Measure (ℂᵈ)) →
    DbarDbarPos φ κ → (∀ z, 0 < κ z) → Continuous κ →
    ∀ (h : ℂᵈ → ℂ), ContDiff ℝ ∞ h → HasCompactSupport h →
      (∃ M : ℝ, ∀ z : ℂᵈ, (∃ w ∈ tsupport (formNormSq (dbarFun h)), ‖z - w‖ ≤ 1 / 3)
        → -M ≤ φ z) →
      (∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z) < ⊤) →
      ∃ g : ℂᵈ → ℂ, ContDiff ℝ ∞ g ∧
        (∀ j : Fin d, (fun z => partialZbar j g z) = fun z => dbarFun h z j) ∧
        (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(φ z)))
          ≤ ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z))

/-- An upper semicontinuous, locally bounded function on `ℂᵈ` is locally integrable. -/
theorem locallyIntegrable_of_upperSemicontinuous {φ : ℂᵈ → ℝ}
    (husc : UpperSemicontinuous φ)
    (hbdd : ∀ R : ℝ, ∃ M : ℝ, ∀ z : ℂᵈ, ‖z‖ ≤ R → |φ z| ≤ M) :
    LocallyIntegrable φ (volume : Measure (ℂᵈ)) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂᵈ)
  obtain ⟨M, hM⟩ := hbdd R
  rw [IntegrableOn]
  haveI : IsFiniteMeasure ((volume : Measure (ℂᵈ)).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  refine Integrable.of_bound
    (husc.measurable.aestronglyMeasurable.mono_measure Measure.restrict_le_self) (max M 0) ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  have hzR : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hz
  rw [Real.norm_eq_abs]
  exact le_trans (hM z hzR) (le_max_left _ _)

/-- **The pointwise Hermitian Hessian bound for the mollified weight.**

Since the mollified weight is smooth, the distributional positivity `DbarDbarPos φ κ` transfers,
through `DbarDbarPos.mollify`, into the pointwise bound of the Kohn--Morrey estimate. -/
theorem hessBound_mollify {φ κ : ℂᵈ → ℝ} {K : ℂᵈ → ℝ}
    (hKc : ContDiff ℝ ∞ K) (hKs : HasCompactSupport K) (hKnn : ∀ t, 0 ≤ K t)
    (hφm : LocallyIntegrable φ (volume : Measure (ℂᵈ)))
    (hκm : LocallyIntegrable κ (volume : Measure (ℂᵈ)))
    (h : DbarDbarPos φ κ) :
    HessBound (mollWt K φ) (mollWt K κ) :=
  pointwise_bound_of_dbarDbarPos
    ((contDiff_mollWt hKc hKs hφm).of_le (WithTop.coe_le_coe.mpr le_top))
    (contDiff_mollWt hKc hKs hκm).continuous
    (DbarDbarPos.mollify hKc hKs hKnn hφm hκm h)

/-- The mollification of a strictly positive continuous function against a nonnegative kernel of
mass `1` is strictly positive. -/
theorem mollWt_pos {κ : ℂᵈ → ℝ} {K : ℂᵈ → ℝ} (hKc : Continuous K) (hKs : HasCompactSupport K)
    (hKnn : ∀ t, 0 ≤ K t) (hK1 : ∫ t, K t = 1) (hκc : Continuous κ)
    (hκpos : ∀ z, 0 < κ z) (z : ℂᵈ) : 0 < mollWt K κ z := by
  rw [mollWt]
  have hne : K ≠ 0 := by
    intro hzero
    rw [hzero] at hK1
    simpa using hK1
  obtain ⟨s, hs⟩ : ∃ s : ℂᵈ, 0 < K s := by
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hne
    exact ⟨s, lt_of_le_of_ne (hKnn s) (Ne.symm hs)⟩
  have hcont : Continuous (fun t : ℂᵈ => K (z - t) * κ t) :=
    (hKc.comp (continuous_const.sub continuous_id)).mul hκc
  have hcs1 : HasCompactSupport (fun t : ℂᵈ => K (z - t)) := by
    have h := hKs.comp_homeomorph (Homeomorph.subLeft z)
    simpa only [Function.comp_def, Homeomorph.subLeft_apply] using h
  have hInt : Integrable (fun t : ℂᵈ => K (z - t) * κ t) volume :=
    hcont.integrable_of_hasCompactSupport (hcs1.mul_right (f' := κ))
  have hnn : 0 ≤ᵐ[volume] (fun t : ℂᵈ => K (z - t) * κ t) :=
    Eventually.of_forall fun t => mul_nonneg (hKnn _) (hκpos t).le
  rw [integral_pos_iff_support_of_nonneg_ae hnn hInt]
  have hUo : IsOpen {t : ℂᵈ | 0 < K (z - t) * κ t} := isOpen_lt continuous_const hcont
  have hUne : {t : ℂᵈ | 0 < K (z - t) * κ t}.Nonempty :=
    ⟨z - s, by
      rw [Set.mem_ofPred_eq, sub_sub_cancel]
      exact mul_pos hs (hκpos _)⟩
  have hsub : {t : ℂᵈ | 0 < K (z - t) * κ t}
      ⊆ Function.support (fun t : ℂᵈ => K (z - t) * κ t) :=
    fun t ht => Function.mem_support.mpr (ne_of_gt ht)
  exact lt_of_lt_of_le (hUo.measure_pos volume hUne) (measure_mono hsub)

/-- **One-sided convergence of the mollified weight**: for a u.s.c. locally bounded `φ` the
mollification eventually satisfies `mollWt (K n) φ z ≤ φ z + ε`.  (Only this direction is needed;
the opposite inequality is *false* for a general u.s.c. function.) -/
theorem tendsto_mollWt_le {φ : ℂᵈ → ℝ} {K : ℕ → ℂᵈ → ℝ}
    (husc : UpperSemicontinuous φ)
    (hbdd : ∀ R : ℝ, ∃ M : ℝ, ∀ z : ℂᵈ, ‖z‖ ≤ R → |φ z| ≤ M)
    (hKnn : ∀ (n : ℕ) (s : ℂᵈ), 0 ≤ K n s)
    (hKmass : ∀ n : ℕ, ∫ s : ℂᵈ, K n s = 1)
    (hKsupp : ∀ n : ℕ, Function.support (K n) ⊆ Metric.closedBall 0 (1 / (n + 1)))
    (z : ℂᵈ) : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, mollWt (K n) φ z ≤ φ z + ε := by
  intro ε hε
  refine (Commons.MeasureTheory.Integral.tendsto_convolution_le husc hbdd hKnn hKmass hKsupp z
    ε hε).mono fun n hn => ?_
  rwa [mollWt_eq (K n) φ z]

/-! ## Elementary bounds for the mollification of a weight -/

/-- **An upper semicontinuous function is bounded above on every ball.** -/
lemma locallyBoundedAbove_of_upperSemicontinuous {φ : ℂᵈ → ℝ} (h : UpperSemicontinuous φ) :
    ∀ R : ℝ, ∃ M : ℝ, ∀ z : ℂᵈ, ‖z‖ ≤ R → φ z ≤ M := by
  intro R
  obtain ⟨M, hM⟩ := UpperSemicontinuousOn.bddAbove_of_isCompact
    (isCompact_closedBall (0 : ℂᵈ) R) (h.upperSemicontinuousOn (s := Metric.closedBall (0 : ℂᵈ) R))
  exact ⟨M, fun z hz => hM ⟨z, Metric.mem_closedBall.mpr (by simpa using hz), rfl⟩⟩

/-- Translation preserves local integrability. -/
lemma locallyIntegrable_comp_sub_left {f : ℂᵈ → ℝ}
    (hf : LocallyIntegrable f (volume : Measure (ℂᵈ))) (z : ℂᵈ) :
    LocallyIntegrable (fun t : ℂᵈ => f (z - t)) (volume : Measure (ℂᵈ)) := by
  rw [locallyIntegrable_iff] at hf ⊢
  intro K hK
  have hcomp : IsCompact ((fun t : ℂᵈ => z - t) '' K) :=
    hK.image (continuous_const.sub continuous_id)
  have h2 := (Measure.measurePreserving_sub_left volume z).integrableOn_comp_preimage
    (MeasurableEquiv.subLeft z).measurableEmbedding (f := f)
    (s := (fun t : ℂᵈ => z - t) '' K)
  have h3 : IntegrableOn (fun a : ℂᵈ => f (z - a))
      ((fun t : ℂᵈ => z - t) ⁻¹' ((fun t : ℂᵈ => z - t) '' K)) volume :=
    h2.mpr (hf _ hcomp)
  rwa [Set.preimage_image_eq _ (fun a b h => by simpa using h)] at h3

/-- The kernel times a translate of a locally integrable function is integrable. -/
lemma integrable_kernel_mul_comp_sub {f K : ℂᵈ → ℝ}
    (hfi : LocallyIntegrable f (volume : Measure (ℂᵈ))) (hKc : Continuous K)
    (hKs : HasCompactSupport K) (z : ℂᵈ) :
    Integrable (fun t : ℂᵈ => K t * f (z - t)) (volume : Measure (ℂᵈ)) := by
  have h1 : Integrable (fun t : ℂᵈ => K t • f (z - t)) (volume : Measure (ℂᵈ)) :=
    (locallyIntegrable_comp_sub_left hfi z).integrable_smul_left_of_hasCompactSupport hKc hKs
  simpa [smul_eq_mul] using h1

/-- **Lower bound for a mollification**: if `f (z - t) ≥ m` on the support of the nonnegative
kernel `K` of mass `1`, then `m ≤ (K * f) z`. -/
lemma mollWt_ge_of_le {f K : ℂᵈ → ℝ} {z : ℂᵈ} {m : ℝ}
    (hfi : LocallyIntegrable f (volume : Measure (ℂᵈ))) (hKc : Continuous K)
    (hKs : HasCompactSupport K) (hKnn : ∀ t, 0 ≤ K t) (hK1 : ∫ t, K t = 1)
    (hle : ∀ t ∈ tsupport K, m ≤ f (z - t)) : m ≤ mollWt K f z := by
  rw [mollWt_eq]
  have hI1 := integrable_kernel_mul_comp_sub hfi hKc hKs z
  have hKint : Integrable K (volume : Measure (ℂᵈ)) := hKc.integrable_of_hasCompactSupport hKs
  have hI2 : Integrable (fun t : ℂᵈ => K t * m) (volume : Measure (ℂᵈ)) := hKint.mul_const m
  have hmono := integral_mono_ae hI2 hI1 (Eventually.of_forall fun t => by
    change K t * m ≤ K t * f (z - t)
    by_cases ht : t ∈ tsupport K
    · exact mul_le_mul_of_nonneg_left (hle t ht) (hKnn t)
    · rw [image_eq_zero_of_notMem_tsupport ht]; simp)
  have hconst : ∫ t : ℂᵈ, K t * m = m := by
    rw [show (fun t : ℂᵈ => K t * m) = fun t : ℂᵈ => m * K t by funext t; ring]
    rw [integral_const_mul, hK1, mul_one]
  linarith

/-- **Upper bound for a mollification**: if `f (z - t) ≤ M` on the support of the nonnegative
kernel `K` of mass `1`, then `(K * f) z ≤ M`. -/
lemma mollWt_le_of_le {f K : ℂᵈ → ℝ} {z : ℂᵈ} {M : ℝ}
    (hfi : LocallyIntegrable f (volume : Measure (ℂᵈ))) (hKc : Continuous K)
    (hKs : HasCompactSupport K) (hKnn : ∀ t, 0 ≤ K t) (hK1 : ∫ t, K t = 1)
    (hle : ∀ t ∈ tsupport K, f (z - t) ≤ M) : mollWt K f z ≤ M := by
  rw [mollWt_eq]
  have hI1 := integrable_kernel_mul_comp_sub hfi hKc hKs z
  have hKint : Integrable K (volume : Measure (ℂᵈ)) := hKc.integrable_of_hasCompactSupport hKs
  have hI2 : Integrable (fun t : ℂᵈ => K t * M) (volume : Measure (ℂᵈ)) := hKint.mul_const M
  have hmono := integral_mono_ae hI1 hI2 (Eventually.of_forall fun t => by
    change K t * f (z - t) ≤ K t * M
    by_cases ht : t ∈ tsupport K
    · exact mul_le_mul_of_nonneg_left (hle t ht) (hKnn t)
    · rw [image_eq_zero_of_notMem_tsupport ht]; simp)
  have hconst : ∫ t : ℂᵈ, K t * M = M := by
    rw [show (fun t : ℂᵈ => K t * M) = fun t : ℂᵈ => M * K t by funext t; ring]
    rw [integral_const_mul, hK1, mul_one]
  linarith

/-- A continuous positive function is bounded below by a positive constant on a closed ball. -/
lemma exists_pos_le_on_closedBall {κ : ℂᵈ → ℝ} (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z)
    (R : ℝ) : ∃ c : ℝ, 0 < c ∧ ∀ z ∈ Metric.closedBall (0 : ℂᵈ) R, c ≤ κ z := by
  by_cases hR : R < 0
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    exact absurd (Metric.mem_closedBall.mp hz)
      (not_le.mpr (lt_of_lt_of_le hR dist_nonneg))
  · push_neg at hR
    obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall (0 : ℂᵈ) R).exists_isMinOn
      ⟨0, Metric.mem_closedBall_self hR⟩ hκc.continuousOn
    exact ⟨κ x, hκpos x, fun z hz => (isMinOn_iff.mp hmin) z hz⟩

/-- **Pointwise domination for the mollified weight.**

If `φ` is bounded below by `-M` on the `1/3`-neighbourhood of the support of `W`, `κ` is continuous
and positive, `K` a nonnegative kernel of mass `1` supported in the ball of radius `1/3`, and `W`
is continuous, compactly supported and nonnegative, then there is `C > 0` with
`W z e^{-K*φ}/(K*κ) ≤ C W z` for every `z`. -/
theorem mollified_pointwise_le {φ κ W : ℂᵈ → ℝ} (hWc : Continuous W)
    (hWs : HasCompactSupport W) (hWnn : ∀ z, 0 ≤ W z)
    (hφli : LocallyIntegrable φ (volume : Measure (ℂᵈ)))
    {M : ℝ} (hlb : ∀ z : ℂᵈ, (∃ w ∈ tsupport W, ‖z - w‖ ≤ 1 / 3) → -M ≤ φ z)
    {K : ℂᵈ → ℝ} (hKc : Continuous K) (hKs : HasCompactSupport K) (hKnn : ∀ t, 0 ≤ K t)
    (hK1 : ∫ t, K t = 1) (hKsub : tsupport K ⊆ Metric.closedBall 0 (1 / 3))
    (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z) :
    ∃ C : ℝ, 0 < C ∧ ∀ z,
      W z * Real.exp (-(mollWt K φ z)) / mollWt K κ z ≤ C * W z := by
  obtain ⟨R₀, hR₀⟩ := hWs.isCompact.isBounded.exists_norm_le
  set R : ℝ := max R₀ 0 + 1 with hRdef
  obtain ⟨c, hcpos, hc⟩ := exists_pos_le_on_closedBall hκc hκpos R
  have ht1 : ∀ t ∈ tsupport K, ‖t‖ ≤ 1 / 3 := by
    intro t ht
    have h := hKsub ht
    simpa [Metric.mem_closedBall, dist_eq_norm] using h
  have hcth : ∀ z ∈ tsupport W, ∀ t ∈ tsupport K,
      ∃ w ∈ tsupport W, ‖(z - t) - w‖ ≤ 1 / 3 := by
    intro z hz t ht
    refine ⟨z, hz, ?_⟩
    calc ‖(z - t) - z‖ = ‖-t‖ := by ring_nf
      _ = ‖t‖ := norm_neg t
      _ ≤ 1 / 3 := ht1 t ht
  have hsubR : ∀ z ∈ tsupport W, ∀ t ∈ tsupport K, ‖z - t‖ ≤ R := by
    intro z hz t ht
    have hzR : ‖z‖ ≤ R₀ := hR₀ z hz
    calc ‖z - t‖ ≤ ‖z‖ + ‖t‖ := norm_sub_le z t
      _ ≤ R₀ + 1 := by have := ht1 t ht; linarith
      _ ≤ R := by rw [hRdef]; linarith [le_max_left R₀ 0]
  have hpoint : ∀ z, W z * Real.exp (-(mollWt K φ z)) / mollWt K κ z
      ≤ (Real.exp M / c) * W z := by
    intro z
    by_cases hz : z ∈ tsupport W
    · have hge : -M ≤ mollWt K φ z :=
        mollWt_ge_of_le hφli hKc hKs hKnn hK1 fun t ht => hlb (z - t) (hcth z hz t ht)
      have hgeκ : c ≤ mollWt K κ z :=
        mollWt_ge_of_le hκc.locallyIntegrable hKc hKs hKnn hK1 fun t ht =>
          hc (z - t) (Metric.mem_closedBall.mpr (by simpa using hsubR z hz t ht))
      have h1 : Real.exp (-(mollWt K φ z)) ≤ Real.exp M := Real.exp_le_exp.mpr (by linarith)
      have h2 : (mollWt K κ z)⁻¹ ≤ c⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hcpos hgeκ
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left h1 (hWnn z)) h2
        (inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le hcpos hgeκ)))
        (mul_nonneg (hWnn z) (Real.exp_nonneg M))) (le_of_eq ?_)
      ring
    · have hz0 : W z = 0 := image_eq_zero_of_notMem_tsupport hz
      rw [hz0]; simp
  exact ⟨Real.exp M / c, div_pos (Real.exp_pos M) hcpos, hpoint⟩

/-- **Uniform bound for the weighted integral of the mollified test form.** -/
theorem lintegral_mollified_le {φ κ W : ℂᵈ → ℝ} (hWc : Continuous W)
    (hWs : HasCompactSupport W) (hWnn : ∀ z, 0 ≤ W z)
    (hφli : LocallyIntegrable φ (volume : Measure (ℂᵈ)))
    {M : ℝ} (hlb : ∀ z : ℂᵈ, (∃ w ∈ tsupport W, ‖z - w‖ ≤ 1 / 3) → -M ≤ φ z)
    {K : ℂᵈ → ℝ} (hKc : Continuous K) (hKs : HasCompactSupport K) (hKnn : ∀ t, 0 ≤ K t)
    (hK1 : ∫ t, K t = 1) (hKsub : tsupport K ⊆ Metric.closedBall 0 (1 / 3))
    (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z) :
    ∃ C : ℝ, 0 < C ∧
      (∫⁻ z, ENNReal.ofReal (W z * Real.exp (-(mollWt K φ z)) / mollWt K κ z)
        ≤ ENNReal.ofReal (C * ∫ z, W z)) := by
  obtain ⟨C, hCpos, hpoint⟩ := mollified_pointwise_le hWc hWs hWnn hφli hlb hKc hKs hKnn hK1
    hKsub hκc hκpos
  refine ⟨C, hCpos, ?_⟩
  have hWint : Integrable W (volume : Measure (ℂᵈ)) := hWc.integrable_of_hasCompactSupport hWs
  have hCnn : (0 : ℝ) ≤ C := le_of_lt hCpos
  have hstep : (fun z => ENNReal.ofReal (C * W z))
      = (fun z => ENNReal.ofReal C * ENNReal.ofReal (W z)) :=
    funext fun z => ENNReal.ofReal_mul hCnn
  refine le_trans (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hpoint z)) ?_
  rw [hstep, lintegral_const_mul]
  · rw [← ofReal_integral_eq_lintegral_ofReal hWint (Eventually.of_forall hWnn),
      ← ENNReal.ofReal_mul hCnn]
  · exact hWc.measurable.ennreal_ofReal

/-- **Uniform bounds for a whole family of mollified weights.** -/
theorem mollified_family_le {φ κ W : ℂᵈ → ℝ} (hWc : Continuous W)
    (hWs : HasCompactSupport W) (hWnn : ∀ z, 0 ≤ W z)
    (hφli : LocallyIntegrable φ (volume : Measure (ℂᵈ)))
    {M : ℝ} (hlb : ∀ z : ℂᵈ, (∃ w ∈ tsupport W, ‖z - w‖ ≤ 1 / 3) → -M ≤ φ z)
    {K : ℕ → ℂᵈ → ℝ} (hKc : ∀ n, Continuous (K n)) (hKs : ∀ n, HasCompactSupport (K n))
    (hKnn : ∀ n t, 0 ≤ K n t) (hK1 : ∀ n, ∫ t, K n t = 1)
    (hKsub : ∀ n, tsupport (K n) ⊆ Metric.closedBall 0 (1 / 3))
    (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n z, W z * Real.exp (-(mollWt (K n) φ z)) / mollWt (K n) κ z ≤ C * W z) ∧
      (∀ n, ∫⁻ z, ENNReal.ofReal (W z * Real.exp (-(mollWt (K n) φ z)) / mollWt (K n) κ z)
        ≤ ENNReal.ofReal (C * ∫ z, W z)) := by
  obtain ⟨R₀, hR₀⟩ := hWs.isCompact.isBounded.exists_norm_le
  set R : ℝ := max R₀ 0 + 1 with hRdef
  obtain ⟨c, hcpos, hc⟩ := exists_pos_le_on_closedBall hκc hκpos R
  have ht1 : ∀ n t, t ∈ tsupport (K n) → ‖t‖ ≤ 1 / 3 := by
    intro n t ht
    have h := hKsub n ht
    simpa [Metric.mem_closedBall, dist_eq_norm] using h
  have hcth : ∀ (n : ℕ) z, z ∈ tsupport W → ∀ t ∈ tsupport (K n),
      ∃ w ∈ tsupport W, ‖(z - t) - w‖ ≤ 1 / 3 := by
    intro n z hz t ht
    refine ⟨z, hz, ?_⟩
    calc ‖(z - t) - z‖ = ‖-t‖ := by ring_nf
      _ = ‖t‖ := norm_neg t
      _ ≤ 1 / 3 := ht1 n t ht
  have hsubR : ∀ (n : ℕ) z, z ∈ tsupport W → ∀ t ∈ tsupport (K n), ‖z - t‖ ≤ R := by
    intro n z hz t ht
    have hzR : ‖z‖ ≤ R₀ := hR₀ z hz
    calc ‖z - t‖ ≤ ‖z‖ + ‖t‖ := norm_sub_le z t
      _ ≤ R₀ + 1 := by have := ht1 n t ht; linarith
      _ ≤ R := by rw [hRdef]; linarith [le_max_left R₀ 0]
  have hb₃ : ∀ n z, W z * Real.exp (-(mollWt (K n) φ z)) / mollWt (K n) κ z
      ≤ (Real.exp M / c) * W z := by
    intro n z
    by_cases hz : z ∈ tsupport W
    · have hge : -M ≤ mollWt (K n) φ z :=
        mollWt_ge_of_le hφli (hKc n) (hKs n) (hKnn n) (hK1 n) fun t ht =>
          hlb (z - t) (hcth n z hz t ht)
      have hgeκ : c ≤ mollWt (K n) κ z :=
        mollWt_ge_of_le hκc.locallyIntegrable (hKc n) (hKs n) (hKnn n) (hK1 n) fun t ht =>
          hc (z - t) (Metric.mem_closedBall.mpr (by simpa using hsubR n z hz t ht))
      have h1 : Real.exp (-(mollWt (K n) φ z)) ≤ Real.exp M := Real.exp_le_exp.mpr (by linarith)
      have h2 : (mollWt (K n) κ z)⁻¹ ≤ c⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hcpos hgeκ
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left h1 (hWnn z)) h2
        (inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le hcpos hgeκ)))
        (mul_nonneg (hWnn z) (Real.exp_nonneg M))) (le_of_eq ?_)
      ring
    · have hz0 : W z = 0 := image_eq_zero_of_notMem_tsupport hz
      rw [hz0]; simp
  refine ⟨Real.exp M / c, div_pos (Real.exp_pos M) hcpos, hb₃, ?_⟩
  intro n
  have hWint : Integrable W (volume : Measure (ℂᵈ)) := hWc.integrable_of_hasCompactSupport hWs
  have hCnn : (0 : ℝ) ≤ Real.exp M / c := le_of_lt (div_pos (Real.exp_pos M) hcpos)
  have hstep : (fun z => ENNReal.ofReal ((Real.exp M / c) * W z))
      = (fun z => ENNReal.ofReal (Real.exp M / c) * ENNReal.ofReal (W z)) :=
    funext fun z => ENNReal.ofReal_mul hCnn
  refine le_trans (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hb₃ n z)) ?_
  rw [hstep, lintegral_const_mul]
  · rw [← ofReal_integral_eq_lintegral_ofReal hWint (Eventually.of_forall hWnn),
      ← ENNReal.ofReal_mul hCnn]
  · exact hWc.measurable.ennreal_ofReal

/-- **Finiteness of the weighted integral of the mollified test form.** -/
theorem hint_mollified_lt_top {φ κ W : ℂᵈ → ℝ} (hWc : Continuous W)
    (hWs : HasCompactSupport W) (hWnn : ∀ z, 0 ≤ W z)
    (hφli : LocallyIntegrable φ (volume : Measure (ℂᵈ)))
    {M : ℝ} (hlb : ∀ z : ℂᵈ, (∃ w ∈ tsupport W, ‖z - w‖ ≤ 1 / 3) → -M ≤ φ z)
    {K : ℂᵈ → ℝ} (hKc : Continuous K) (hKs : HasCompactSupport K) (hKnn : ∀ t, 0 ≤ K t)
    (hK1 : ∫ t, K t = 1) (hKsub : tsupport K ⊆ Metric.closedBall 0 (1 / 3))
    (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z) :
    ∫⁻ z, ENNReal.ofReal (W z * Real.exp (-(mollWt K φ z)) / mollWt K κ z) < ⊤ := by
  obtain ⟨C, hC, hle⟩ := lintegral_mollified_le hWc hWs hWnn hφli hlb hKc hKs hKnn hK1 hKsub
    hκc hκpos
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

/-- **The smooth solution for a mollified weight.** -/
theorem exists_smooth_solution_mollified {φ κ : ℂᵈ → ℝ} (hd : 1 ≤ d)
    (hφli : LocallyIntegrable φ (volume : Measure (ℂᵈ)))
    (hdd : DbarDbarPos φ κ) (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z)
    {K : ℕ → ℂᵈ → ℝ} (hKc : ∀ n, ContDiff ℝ ∞ (K n)) (hKs : ∀ n, HasCompactSupport (K n))
    (hKnn : ∀ n t, 0 ≤ K n t) (hK1 : ∀ n, ∫ t, K n t = 1)
    (hKsub : ∀ n, tsupport (K n) ⊆ Metric.closedBall 0 (1 / 3))
    {h : ℂᵈ → ℂ} (hh : ContDiff ℝ ∞ h) (hhs : HasCompactSupport h)
    {M : ℝ} (hlb : ∀ z : ℂᵈ, (∃ w ∈ tsupport (formNormSq (dbarFun h)), ‖z - w‖ ≤ 1 / 3)
        → -M ≤ φ z) (n : ℕ) :
    ∃ g : ℂᵈ → ℂ, ContDiff ℝ ∞ g ∧
      (∀ j : Fin d, (fun z => partialZbar j g z) = fun z => dbarFun h z j) ∧
      (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(mollWt (K n) φ z)))
        ≤ ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z
            * Real.exp (-(mollWt (K n) φ z)) / mollWt (K n) κ z)) := by
  have hκm : LocallyIntegrable κ (volume : Measure (ℂᵈ)) := hκc.locallyIntegrable
  have hηc : ∀ j : Fin d, Continuous (fun z => dbarFun h z j) := fun j =>
    (contDiff_pi.mp (contDiff_dbarFun hh) j).continuous
  have hWc : Continuous (formNormSq (dbarFun h)) := continuous_formNormSq (continuous_pi hηc)
  have hWs : HasCompactSupport (formNormSq (dbarFun h)) :=
    hasCompactSupport_formNormSq (hasCompactSupport_pi fun j =>
      hhs.mono' (fun z hz => by
        by_contra hzc
        have hd0 : fderiv ℝ h z = 0 := (HasFDerivAt.of_notMem_tsupport ℝ hzc).fderiv
        exact hz (by simp [dbarFun, partialZbar, hd0])))
  have hint := hint_mollified_lt_top hWc hWs (formNormSq_nonneg _) hφli hlb (hKc n).continuous
    (hKs n) (hKnn n) (hK1 n) (hKsub n) hκc hκpos
  exact exists_smooth_solution_of_dbar_exact
    (contDiff_mollWt (hKc n) (hKs n) hφli) hd
    (contDiff_mollWt (hKc n) (hKs n) hκm).continuous
    (mollWt_pos (hKc n).continuous (hKs n) (hKnn n) (hK1 n) hκc hκpos)
    (hessBound_mollify (hKc n) (hKs n) (hKnn n) hφli hκm hdd) hh hhs hint

/-- A real-differentiable function whose `\bar\partial`-derivatives all vanish is holomorphic. -/
lemma differentiable_complex_of_partialZbar_zero {f : ℂᵈ → ℂ} (hf : Differentiable ℝ f)
    (h : ∀ (j : Fin d) (z : ℂᵈ), partialZbar j f z = 0) : Differentiable ℂ f := by
  refine Commons.Analysis.Complex.differentiable_complex_of_dbar_eq_zero hf fun j z => ?_
  have hz := h j z
  rw [partialZbar] at hz
  rcases div_eq_zero_iff.mp hz with h' | h'
  · exact h'
  · exact absurd h' (by norm_num)

/-- A nonnegative real function is bounded by the `toReal` of its `ofReal`-lintegral. -/
lemma integral_le_toReal_lintegral {μ : Measure (ℂᵈ)} {f : ℂᵈ → ℝ} (hf : ∀ z, 0 ≤ f z) :
    ∫ z, f z ∂μ ≤ (∫⁻ z, ENNReal.ofReal (f z) ∂μ).toReal := by
  by_cases h : Integrable f μ
  · rw [← ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hf),
      ENNReal.toReal_ofReal (integral_nonneg hf)]
  · rw [integral_undef h]
    exact ENNReal.toReal_nonneg

/-- `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
lemma sq_norm_sub_le' {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith [norm_sub_le a b, norm_nonneg (a - b), norm_nonneg a, norm_nonneg b]
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b, h1]

/-- **The weighted `L²` bound on a compact set.**  If `ψ ≤ M'` on the compact set `B` and the
weighted `L²` integral of `G` is at most `C`, then `∫_B ‖G‖² ≤ e^{M'} C`. -/
lemma setIntegral_sq_le {G : ℂᵈ → ℂ} (hGc : Continuous G) {ψ : ℂᵈ → ℝ} (hψc : Continuous ψ)
    {B : Set ℂᵈ} (hBc : IsCompact B) {M' C : ℝ} (hC : 0 ≤ C) (hψle : ∀ w ∈ B, ψ w ≤ M')
    (hbd : ∫⁻ w, ENNReal.ofReal (‖G w‖ ^ 2 * Real.exp (-(ψ w))) ≤ ENNReal.ofReal C) :
    ∫ w in B, ‖G w‖ ^ 2 ≤ Real.exp M' * C := by
  have hGint : IntegrableOn (fun w : ℂᵈ => ‖G w‖ ^ 2) B volume :=
    ((hGc.norm.pow 2).continuousOn).integrableOn_compact hBc
  have hTint : IntegrableOn (fun w : ℂᵈ => Real.exp M' * (‖G w‖ ^ 2 * Real.exp (-(ψ w))))
      B volume :=
    ((continuous_const.mul ((hGc.norm.pow 2).mul
      (Real.continuous_exp.comp hψc.neg))).continuousOn).integrableOn_compact hBc
  have h1 : ∫ w in B, ‖G w‖ ^ 2
      ≤ ∫ w in B, Real.exp M' * (‖G w‖ ^ 2 * Real.exp (-(ψ w))) := by
    refine setIntegral_mono_on hGint hTint hBc.measurableSet fun w hw => ?_
    have h2 : (1 : ℝ) ≤ Real.exp M' * Real.exp (-(ψ w)) := by
      rw [← Real.exp_add, show (1 : ℝ) = Real.exp 0 by simp, Real.exp_le_exp]
      linarith [hψle w hw]
    calc ‖G w‖ ^ 2 = ‖G w‖ ^ 2 * 1 := by ring
      _ ≤ ‖G w‖ ^ 2 * (Real.exp M' * Real.exp (-(ψ w))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.exp M' * (‖G w‖ ^ 2 * Real.exp (-(ψ w))) := by ring
  have h2 : ∫ w in B, Real.exp M' * (‖G w‖ ^ 2 * Real.exp (-(ψ w)))
      = Real.exp M' * ∫ w in B, ‖G w‖ ^ 2 * Real.exp (-(ψ w)) := integral_const_mul _ _
  have h3 : ∫ w in B, ‖G w‖ ^ 2 * Real.exp (-(ψ w))
      ≤ (∫⁻ w in B, ENNReal.ofReal (‖G w‖ ^ 2 * Real.exp (-(ψ w)))).toReal :=
    integral_le_toReal_lintegral (μ := volume.restrict B) fun w => by positivity
  have h4 : (∫⁻ w in B, ENNReal.ofReal (‖G w‖ ^ 2 * Real.exp (-(ψ w)))).toReal
      ≤ C := by
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (le_trans (setLIntegral_le_lintegral B _) hbd)) ?_
    rw [ENNReal.toReal_ofReal hC]
  calc ∫ w in B, ‖G w‖ ^ 2
      ≤ Real.exp M' * ∫ w in B, ‖G w‖ ^ 2 * Real.exp (-(ψ w)) := by rw [← h2]; exact h1
    _ ≤ Real.exp M' * C := by
        refine mul_le_mul_of_nonneg_left (le_trans h3 h4) (Real.exp_nonneg M')

/-- **Hörmander's `∂̄` theorem for an upper semicontinuous weight: the limit argument.**

Given a sequence `K n` of nonnegative kernels of mass `1` supported in the unit ball whose
mollifications converge a.e. to the function (`hae`), the smooth solutions for the mollified
weights pass to the limit: Montel's theorem produces a holomorphic limit of `G n - h`, and Fatou's
lemma transfers the weighted `L²` estimate. -/
theorem exists_solution_of_hormanderPsh {φ κ : ℂᵈ → ℝ} (hd : 1 ≤ d)
    (hφusc : UpperSemicontinuous φ) (hφli : LocallyIntegrable φ (volume : Measure (ℂᵈ)))
    (hdd : DbarDbarPos φ κ) (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z)
    {K : ℕ → ℂᵈ → ℝ} (hKc : ∀ n, ContDiff ℝ ∞ (K n)) (hKs : ∀ n, HasCompactSupport (K n))
    (hKnn : ∀ n t, 0 ≤ K n t) (hK1 : ∀ n, ∫ t, K n t = 1)
    (hKsub : ∀ n, tsupport (K n) ⊆ Metric.closedBall 0 (1 / 3))
    (hae : ∀ (g : ℂᵈ → ℝ), LocallyIntegrable g (volume : Measure (ℂᵈ)) →
        ∀ᵐ z ∂(volume : Measure (ℂᵈ)),
          Tendsto (fun n => ∫ s, K n s * g (z - s)) atTop (𝓝 (g z)))
    {h : ℂᵈ → ℂ} (hh : ContDiff ℝ ∞ h) (hhs : HasCompactSupport h)
    {Mφ : ℝ} (hlb : ∀ z : ℂᵈ, (∃ w ∈ tsupport (formNormSq (dbarFun h)), ‖z - w‖ ≤ 1 / 3)
      → -Mφ ≤ φ z)
    (hint : ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z) < ⊤) :
    ∃ g : ℂᵈ → ℂ, ContDiff ℝ ∞ g ∧
      (∀ j : Fin d, (fun z => partialZbar j g z) = fun z => dbarFun h z j) ∧
      (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(φ z)))
        ≤ ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z)) := by
  have hκm : LocallyIntegrable κ (volume : Measure (ℂᵈ)) := hκc.locallyIntegrable
  have hψcont : ∀ n, Continuous (fun z => mollWt (K n) φ z) := fun n =>
    (contDiff_mollWt (hKc n) (hKs n) hφli).continuous
  have hηc : ∀ j : Fin d, Continuous (fun z => dbarFun h z j) := fun j =>
    (contDiff_pi.mp (contDiff_dbarFun hh) j).continuous
  have hWc : Continuous (formNormSq (dbarFun h)) := continuous_formNormSq (continuous_pi hηc)
  have hWs : HasCompactSupport (formNormSq (dbarFun h)) :=
    hasCompactSupport_formNormSq (hasCompactSupport_pi fun j =>
      hhs.mono' (fun z hz => by
        by_contra hzc
        have hd0 : fderiv ℝ h z = 0 := (HasFDerivAt.of_notMem_tsupport ℝ hzc).fderiv
        exact hz (by simp [dbarFun, partialZbar, hd0])))
  have hWnn : ∀ z, 0 ≤ formNormSq (dbarFun h) z := formNormSq_nonneg _
  have hWint : Integrable (formNormSq (dbarFun h)) (volume : Measure (ℂᵈ)) :=
    hWc.integrable_of_hasCompactSupport hWs
  obtain ⟨C₀, hC₀pos, hpt₀, hTbd⟩ :=
    mollified_family_le hWc hWs hWnn hφli hlb (fun n => (hKc n).continuous) hKs hKnn hK1 hKsub
      hκc hκpos
  -- the sequence of smooth solutions for the mollified weights
  have hex : ∀ n, ∃ g : ℂᵈ → ℂ, ContDiff ℝ ∞ g ∧
      (∀ j : Fin d, (fun z => partialZbar j g z) = fun z => dbarFun h z j) ∧
      (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(mollWt (K n) φ z)))
        ≤ ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z
            * Real.exp (-(mollWt (K n) φ z)) / mollWt (K n) κ z)) := fun n =>
    exists_smooth_solution_mollified hd hφli hdd hκc hκpos hKc hKs hKnn hK1 hKsub hh hhs hlb n
  let G : ℕ → ℂᵈ → ℂ := fun n => Classical.choose (hex n)
  have hGsm : ∀ n, ContDiff ℝ ∞ (G n) := fun n => (Classical.choose_spec (hex n)).1
  have hGpart : ∀ n j, (fun z => partialZbar j (G n) z) = fun z => dbarFun h z j :=
    fun n j => (Classical.choose_spec (hex n)).2.1 j
  have hGbd : ∀ n, ∫⁻ z, ENNReal.ofReal (‖G n z‖ ^ 2 * Real.exp (-(mollWt (K n) φ z)))
      ≤ ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z
          * Real.exp (-(mollWt (K n) φ z)) / mollWt (K n) κ z) :=
    fun n => (Classical.choose_spec (hex n)).2.2
  -- `G n - h` is holomorphic
  have hHdiff : ∀ n, Differentiable ℂ (fun z => G n z - h z) := by
    intro n
    refine differentiable_complex_of_partialZbar_zero
      (((hGsm n).differentiable (by simp)).sub (hh.differentiable (by simp))) fun j z => ?_
    have h1 : partialZbar j (fun z => G n z - h z) z
        = partialZbar j (G n) z - partialZbar j h z := by
      have h2 : fderiv ℝ (fun z => G n z - h z) z = fderiv ℝ (G n) z - fderiv ℝ h z :=
        fderiv_sub (((hGsm n).differentiable (by simp)) z) ((hh.differentiable (by simp)) z)
      simp only [partialZbar, h2, sub_apply]
      ring
    rw [h1, show partialZbar j (G n) z = dbarFun h z j from congrFun (hGpart n j) z]
    simp only [dbarFun, sub_self]
  -- local `L²` bounds for `G n - h`
  have hMontel : ∀ (z : ℂᵈ) (R : ℝ), ∃ C : ℝ,
      ∀ n, ∫ w in Metric.closedBall z R, ‖G n w - h w‖ ^ 2 ≤ C := by
    intro z R
    obtain ⟨M', hM'⟩ := locallyBoundedAbove_of_upperSemicontinuous hφusc (‖z‖ + R + 1)
    have hψle : ∀ n, ∀ w ∈ Metric.closedBall z R, mollWt (K n) φ w ≤ M' := by
      intro n w hw
      refine mollWt_le_of_le hφli (hKc n).continuous (hKs n) (hKnn n) (hK1 n) ?_
      intro t ht
      have ht1 : ‖t‖ ≤ 1 / 3 := by
        have h := hKsub n ht
        simpa [Metric.mem_closedBall, dist_eq_norm] using h
      have hwz : ‖w‖ ≤ ‖z‖ + R := by
        have h := Metric.mem_closedBall.mp hw
        rw [dist_eq_norm] at h
        calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
          _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
          _ ≤ ‖z‖ + R := by linarith
      have hwt : ‖w - t‖ ≤ ‖z‖ + R + 1 := by
        calc ‖w - t‖ ≤ ‖w‖ + ‖t‖ := norm_sub_le w t
          _ ≤ ‖z‖ + R + 1 := by linarith
      exact hM' (w - t) hwt
    have hGB : ∀ n, ∫ w in Metric.closedBall z R, ‖G n w‖ ^ 2
        ≤ Real.exp M' * (C₀ * ∫ z, formNormSq (dbarFun h) z) := by
      intro n
      refine setIntegral_sq_le (hGsm n).continuous (hψcont n) (isCompact_closedBall z R)
        (mul_nonneg (le_of_lt hC₀pos) (integral_nonneg hWnn)) (hψle n) ?_
      refine le_trans (hGbd n) (hTbd n)
    have hThInt : Integrable (fun w : ℂᵈ => ‖h w‖ ^ 2) (volume : Measure (ℂᵈ)) := by
      have hcs : HasCompactSupport (fun w : ℂᵈ => ‖h w‖ ^ 2) := by
        have := hhs.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
        simpa [Function.comp_def] using this
      exact (hh.continuous.norm.pow 2).integrable_of_hasCompactSupport hcs
    have hLHSint : ∀ n, IntegrableOn (fun w : ℂᵈ => ‖G n w - h w‖ ^ 2)
        (Metric.closedBall z R) volume := fun n =>
      ((((hGsm n).continuous.sub hh.continuous).norm.pow 2)).continuousOn.integrableOn_compact
        (isCompact_closedBall z R)
    have hSUMint : ∀ n, IntegrableOn (fun w : ℂᵈ => 2 * ‖G n w‖ ^ 2 + 2 * ‖h w‖ ^ 2)
        (Metric.closedBall z R) volume := fun n =>
      (((continuous_const.mul ((hGsm n).continuous.norm.pow 2)).add
        (continuous_const.mul (hh.continuous.norm.pow 2)))).continuousOn.integrableOn_compact
        (isCompact_closedBall z R)
    refine ⟨2 * (Real.exp M' * (C₀ * ∫ z, formNormSq (dbarFun h) z)) + 2 * ∫ w, ‖h w‖ ^ 2,
      fun n => ?_⟩
    have h1 : ∫ w in Metric.closedBall z R, ‖G n w - h w‖ ^ 2
        ≤ ∫ w in Metric.closedBall z R, (2 * ‖G n w‖ ^ 2 + 2 * ‖h w‖ ^ 2) :=
      setIntegral_mono_on (hLHSint n) (hSUMint n) measurableSet_closedBall
        fun w _ => sq_norm_sub_le' _ _
    have h2 : ∫ w in Metric.closedBall z R, (2 * ‖G n w‖ ^ 2 + 2 * ‖h w‖ ^ 2)
        = 2 * (∫ w in Metric.closedBall z R, ‖G n w‖ ^ 2)
          + 2 * (∫ w in Metric.closedBall z R, ‖h w‖ ^ 2) := by
      have h2a : ∫ w in Metric.closedBall z R, (2 * ‖G n w‖ ^ 2 + 2 * ‖h w‖ ^ 2)
          = (∫ w in Metric.closedBall z R, 2 * ‖G n w‖ ^ 2)
            + ∫ w in Metric.closedBall z R, 2 * ‖h w‖ ^ 2 :=
        integral_add
          (((continuous_const.mul ((hGsm n).continuous.norm.pow 2)).continuousOn).integrableOn_compact
            (isCompact_closedBall z R))
          (((continuous_const.mul (hh.continuous.norm.pow 2)).continuousOn).integrableOn_compact
            (isCompact_closedBall z R))
      rw [h2a, integral_const_mul, integral_const_mul]
    have h3 : ∫ w in Metric.closedBall z R, ‖h w‖ ^ 2 ≤ ∫ w, ‖h w‖ ^ 2 :=
      setIntegral_le_integral hThInt (Eventually.of_forall fun w => by positivity)
    calc ∫ w in Metric.closedBall z R, ‖G n w - h w‖ ^ 2
        ≤ 2 * (∫ w in Metric.closedBall z R, ‖G n w‖ ^ 2)
          + 2 * (∫ w in Metric.closedBall z R, ‖h w‖ ^ 2) := h1.trans_eq h2
      _ ≤ 2 * (Real.exp M' * (C₀ * ∫ z, formNormSq (dbarFun h) z)) + 2 * ∫ w, ‖h w‖ ^ 2 := by
          have := hGB n
          linarith [h3]
  -- Montel
  obtain ⟨φs, G', hφsmono, hconv, hG'diff⟩ :=
    Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_locallyL2Bounded
      (f := fun n w => G n w - h w) hHdiff hMontel
  have hG'sm : ContDiff ℝ ∞ G' := contDiff_of_differentiable_complex hG'diff
  have hG'lim : ∀ w, Tendsto (fun k => G (φs k) w - h w) atTop (𝓝 (G' w)) := fun w =>
    hconv.tendsto_at (Set.mem_univ w)
  -- a.e. convergence of the mollified weights
  have hψae : ∀ᵐ z ∂(volume : Measure (ℂᵈ)),
      Tendsto (fun n => mollWt (K n) φ z) atTop (𝓝 (φ z)) :=
    (hae φ hφli).mono fun z hz =>
      hz.congr' (Eventually.of_forall fun n => (mollWt_eq (K n) φ z).symm)
  have hκae : ∀ᵐ z ∂(volume : Measure (ℂᵈ)),
      Tendsto (fun n => mollWt (K n) κ z) atTop (𝓝 (κ z)) :=
    (hae κ hκm).mono fun z hz =>
      hz.congr' (Eventually.of_forall fun n => (mollWt_eq (K n) κ z).symm)
  -- dominated convergence for `T n`
  have hTmeas : ∀ n, Measurable (fun z => ENNReal.ofReal (formNormSq (dbarFun h) z
      * Real.exp (-(mollWt (K n) φ z)) / mollWt (K n) κ z)) := fun n =>
    ENNReal.measurable_ofReal.comp
      (((hWc.mul (Real.continuous_exp.comp (hψcont n).neg)).div
        ((contDiff_mollWt (hKc n) (hKs n) hκm).continuous)
        (fun z => ne_of_gt (mollWt_pos (hKc n).continuous (hKs n) (hKnn n) (hK1 n) hκc hκpos z)))
        |>.measurable)
  have hTendsto : Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z
      * Real.exp (-(mollWt (K n) φ z)) / mollWt (K n) κ z)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z))) := by
    have hbound : ∀ n, (fun z => ENNReal.ofReal (formNormSq (dbarFun h) z
        * Real.exp (-(mollWt (K n) φ z)) / mollWt (K n) κ z))
        ≤ᵐ[(volume : Measure (ℂᵈ))] fun z => ENNReal.ofReal (C₀ * formNormSq (dbarFun h) z) :=
      fun n => Eventually.of_forall fun z => ENNReal.ofReal_le_ofReal (hpt₀ n z)
    have hfin : ∫⁻ z, ENNReal.ofReal (C₀ * formNormSq (dbarFun h) z) ≠ ⊤ := by
      have hstep : (fun z => ENNReal.ofReal (C₀ * formNormSq (dbarFun h) z))
          = fun z => ENNReal.ofReal C₀ * ENNReal.ofReal (formNormSq (dbarFun h) z) :=
        funext fun z => ENNReal.ofReal_mul hC₀pos.le
      rw [hstep, lintegral_const_mul]
      · rw [← ofReal_integral_eq_lintegral_ofReal hWint (Eventually.of_forall hWnn)]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      · exact hWc.measurable.ennreal_ofReal
    have hlim : ∀ᵐ z ∂(volume : Measure (ℂᵈ)), Tendsto (fun n => ENNReal.ofReal
        (formNormSq (dbarFun h) z * Real.exp (-(mollWt (K n) φ z)) / mollWt (K n) κ z)) atTop
        (𝓝 (ENNReal.ofReal (formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z))) := by
      filter_upwards [hψae, hκae] with z hψ hκ
      have h1 : Tendsto (fun n => formNormSq (dbarFun h) z * Real.exp (-(mollWt (K n) φ z)))
          atTop (𝓝 (formNormSq (dbarFun h) z * Real.exp (-(φ z)))) :=
        tendsto_const_nhds.mul ((Real.continuous_exp.tendsto _).comp hψ.neg)
      have h2 : Tendsto (fun n =>
          (formNormSq (dbarFun h) z * Real.exp (-(mollWt (K n) φ z))) / mollWt (K n) κ z)
          atTop (𝓝 ((formNormSq (dbarFun h) z * Real.exp (-(φ z))) / κ z)) :=
        h1.div hκ (hκpos z).ne'
      exact (ENNReal.continuous_ofReal.tendsto _).comp h2
    exact tendsto_lintegral_of_dominated_convergence _ hTmeas hbound hfin hlim
  -- the Fatou argument
  have hFmeas : ∀ k, Measurable (fun z => ENNReal.ofReal (‖G (φs k) z‖ ^ 2
      * Real.exp (-(mollWt (K (φs k)) φ z)))) := fun k =>
    ENNReal.measurable_ofReal.comp
      (((hGsm (φs k)).continuous.norm.pow 2).mul
        (Real.continuous_exp.comp (hψcont (φs k)).neg)).measurable
  have hlimF : ∀ᵐ z ∂(volume : Measure (ℂᵈ)), Tendsto (fun k => ENNReal.ofReal
      (‖G (φs k) z‖ ^ 2 * Real.exp (-(mollWt (K (φs k)) φ z)))) atTop
      (𝓝 (ENNReal.ofReal (‖G' z + h z‖ ^ 2 * Real.exp (-(φ z))))) := by
    filter_upwards [hψae.mono (fun z hz => hz.comp hφsmono.tendsto_atTop)] with z hψ
    have hB : Tendsto (fun k => G (φs k) z) atTop (𝓝 (G' z + h z)) := by
      have h := (hG'lim z).add (tendsto_const_nhds (x := h z))
      simpa using h
    have hC : Tendsto (fun k => ‖G (φs k) z‖ ^ 2) atTop (𝓝 (‖G' z + h z‖ ^ 2)) := hB.norm.pow 2
    have hD : Tendsto (fun k => Real.exp (-(mollWt (K (φs k)) φ z))) atTop
        (𝓝 (Real.exp (-(φ z)))) := (Real.continuous_exp.tendsto _).comp hψ.neg
    exact (ENNReal.continuous_ofReal.tendsto _).comp (hC.mul hD)
  have hFatou1 : ∫⁻ z, liminf (fun k => ENNReal.ofReal (‖G (φs k) z‖ ^ 2
      * Real.exp (-(mollWt (K (φs k)) φ z)))) atTop
      ≤ liminf (fun k => ∫⁻ z, ENNReal.ofReal (‖G (φs k) z‖ ^ 2
        * Real.exp (-(mollWt (K (φs k)) φ z)))) atTop :=
    lintegral_liminf_le hFmeas
  have hFatou2 : liminf (fun k => ∫⁻ z, ENNReal.ofReal (‖G (φs k) z‖ ^ 2
        * Real.exp (-(mollWt (K (φs k)) φ z)))) atTop
      ≤ ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z) := by
    have h3 : Tendsto (fun k => ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z
        * Real.exp (-(mollWt (K (φs k)) φ z)) / mollWt (K (φs k)) κ z)) atTop
        (𝓝 (∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z
          * Real.exp (-(φ z)) / κ z))) := hTendsto.comp hφsmono.tendsto_atTop
    refine le_trans (liminf_le_liminf (Eventually.of_forall fun k => hGbd (φs k))) ?_
    rw [h3.liminf_eq]
  have hFatouEq : ∫⁻ z, liminf (fun k => ENNReal.ofReal (‖G (φs k) z‖ ^ 2
      * Real.exp (-(mollWt (K (φs k)) φ z)))) atTop
      = ∫⁻ z, ENNReal.ofReal (‖G' z + h z‖ ^ 2 * Real.exp (-(φ z))) :=
    lintegral_congr_ae (hlimF.mono fun z hz => hz.liminf_eq)
  -- conclusion
  refine ⟨fun z => G' z + h z, hG'sm.add hh, ?_, ?_⟩
  · intro j
    funext z
    rw [partialZbar_add j ((hG'diff z).restrictScalars ℝ) ((hh.differentiable (by simp)) z),
      congrFun (partialZbar_eq_zero_of_differentiable_complex hG'diff j) z]
    simp [dbarFun]
  · rw [← hFatouEq]
    exact le_trans hFatou1 hFatou2

/-- **Hörmander's `∂̄` theorem for upper semicontinuous locally bounded weights and exact data.**

This proves the `Prop` `HormanderStatementExact` declared above, by instantiating the limit
argument `exists_solution_of_hormanderPsh` with the approximate identity of
`Commons.MeasureTheory.Integral.exists_approximate_identity_complex_ae`. -/
theorem hormanderStatementExact (d : ℕ) : HormanderStatementExact (d := d) := by
  intro φ κ hφusc hφli hdd hκpos hκc h hh hhs hlb hint
  obtain ⟨K, hKnn, hK1, hKc, hKs, hKsupp, haeE⟩ :=
    Commons.MeasureTheory.Integral.exists_approximate_identity_complex_ae d
  -- shift the approximate identity so that its support has radius at most `1/3`
  let K' : ℕ → (Fin d → ℂ) → ℝ := fun n => K (n + 2)
  have hK'c : ∀ n, ContDiff ℝ ∞ (K' n) := fun n => hKc (n + 2)
  have hK's : ∀ n, HasCompactSupport (K' n) := fun n => hKs (n + 2)
  have hK'nn : ∀ n t, 0 ≤ K' n t := fun n t => hKnn (n + 2) t
  have hK'1 : ∀ n, ∫ t, K' n t = 1 := fun n => hK1 (n + 2)
  have hK'sub : ∀ n, tsupport (K' n) ⊆ Metric.closedBall (0 : Fin d → ℂ) (1 / 3) := by
    intro n
    have h1 : tsupport (K (n + 2)) ⊆
        Metric.closedBall (0 : Fin d → ℂ) (1 / (↑(n + 2) + 1)) :=
      closure_minimal (hKsupp (n + 2)) Metric.isClosed_closedBall
    intro z hz
    have hz' := h1 hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz' ⊢
    refine le_trans hz' ?_
    have h3 : (3 : ℝ) ≤ ↑(n + 2) + 1 := by
      have : (3 : ℕ) ≤ (n + 2) + 1 := by omega
      push_cast
      exact_mod_cast this
    exact one_div_le_one_div_of_le (show (0 : ℝ) < 3 by norm_num) h3
  have hae' : ∀ (g : (Fin d → ℂ) → ℝ), MeasureTheory.LocallyIntegrable g MeasureTheory.volume →
      ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)),
        Filter.Tendsto (fun n => ∫ s, K' n s * g (z - s)) Filter.atTop (nhds (g z)) := by
    intro g hg
    have hshift : Filter.Tendsto (fun n : ℕ => n + 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b, fun a ha => by omega⟩
    filter_upwards [(haeE ℝ g hg).mono (fun z hz => hz.comp hshift)] with z hz
    simpa [K', Function.comp_def, smul_eq_mul] using hz
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    refine ⟨fun _ => 0, contDiff_const, fun j => j.elim0, ?_⟩
    simp [formNormSq]
  · obtain ⟨M, hlb'⟩ := hlb
    exact exists_solution_of_hormanderPsh hd hφusc hφli hdd hκc hκpos hK'c hK's hK'nn hK'1
      hK'sub hae' hh hhs hlb' hint

end Submission.FUP
