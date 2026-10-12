import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseBoxFock.frameSampling_latBox
import Submission.Work.BoseBoxFock.latBox_ae_eq_latCell
import Submission.Work.BoseBoxFock.latChar_orthogonal
import Submission.Work.BoseBoxFock.latPer_fourierCoeff
import Submission.Work.BoseBoxFock.latTiling_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latFourier_tendsto_periodisation`

The `L²` convergence of the truncated lattice Fourier series of a bounded, compactly supported
weight `W` to its periodisation (see the target statement below).

## Structure of the proof

* `Work.BoseBoxFock.latTiling_integral` (the tiling identity of `ℝ³` by the translates of the
  half-open cell `latCell ℓ`) gives the Fourier coefficient
  `∫_{latCell ℓ} latPer ℓ W z e^{-i⟪k_n,z⟫}dz = Ŵ(k_n)`
  (`Work.BoseBoxFock.latPer_fourierCoeff`);
* `Work.BoseBoxFock.frameSampling_latBox` (the `L²` frame identity for weights supported in the
  closed cube) applied to the *difference* `Q_Λ - ℓ³·latPer` converts the `L²` distance into a
  lattice sum `Σ_n ‖kinFT G(k_n)‖²`, whose terms are evaluated with the orthogonality of the
  characters on the cell (`Work.BoseBoxFock.latChar_orthogonal`);
* the resulting lattice tail `Σ_{n : ‖k_n‖ > Λ}‖Ŵ(k_n)‖²` tends to `0` by the corpus's
  `Work.BoseBoxFock.kinFT_lattice_tail_sq_lt`.

The main estimate `latFourier_main` below is proved from these four inputs as hypotheses, and the
target `latFourier_tendsto_periodisation` instantiates them.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open LatFourier
open Submission.BoseGases

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Elementary facts -/

private lemma norm_exp_I_ofReal (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm Complex.I (x : ℂ)]
  exact Complex.norm_exp_ofReal_mul_I x

private lemma norm_exp_neg_I_ofReal (x : ℝ) :
    ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (-x)

private lemma exp_neg_mul_exp_pos (a b : ℝ) :
    Complex.exp (-(Complex.I * (a : ℂ))) * Complex.exp (Complex.I * (b : ℂ))
      = Complex.exp (Complex.I * ((b - a : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma kmomInt_sub (ℓ : ℝ) (m n : Fin 3 → ℤ) :
    kmomInt ℓ (m - n) = kmomInt ℓ m - kmomInt ℓ n := by
  have h := kmomInt_add ℓ (m - n) n
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-- The volume of the closed cube. -/
private lemma volume_latBox_eq {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    volume (latBox ℓ) = ENNReal.ofReal (ℓ ^ 3) := by
  have hpre : (WithLp.toLp 2 : (Fin 3 → ℝ) → E3) ⁻¹' (latBox ℓ)
      = Set.Icc (fun _ : Fin 3 => (0 : ℝ)) (fun _ => ℓ) := by
    ext x
    simp only [latBox, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def]
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩
  have hmp := PiLp.volume_preserving_toLp (Fin 3)
  rw [← MeasureTheory.MeasurePreserving.measure_preimage hmp
      (measurableSet_latBox ℓ).nullMeasurableSet, hpre, Real.volume_Icc_pi]
  simp [Finset.prod_const, ENNReal.ofReal_pow hℓ]

/-- A complex function on the cube that is bounded there and a.e. strongly measurable is
integrable on the cube. -/
private lemma integrableOn_latBox_of_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℂ}
    (haesm : AEStronglyMeasurable f (volume.restrict (latBox ℓ)))
    (hb : ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ latBox ℓ, ‖f z‖ ≤ D) :
    Integrable f (volume.restrict (latBox ℓ)) := by
  obtain ⟨D, hD0, hD⟩ := hb
  haveI : IsFiniteMeasure (volume.restrict (latBox ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_latBox_eq hℓ.le]; exact ENNReal.ofReal_lt_top⟩
  refine MemLp.integrable (q := 2) (by norm_num) (MemLp.of_bound haesm D ?_)
  rw [MeasureTheory.ae_restrict_iff' (measurableSet_latBox ℓ)]
  exact Eventually.of_forall fun z hz => hD z hz

/-! ## 2. The finite momentum ball and the partial sum -/

private lemma mom_le_iff {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (n : Fin 3 → ℤ) :
    ‖kmomInt ℓ n‖ ≤ Λ ↔ ‖latVec n‖ ≤ Λ * ℓ / (2 * Real.pi) := by
  have h2 : (0 : ℝ) < 2 * Real.pi / ℓ := by positivity
  have h3 : ‖kmomInt ℓ n‖ = (2 * Real.pi / ℓ) * ‖latVec n‖ := by
    rw [kmomInt_eq_smul_latVec, norm_smul, Real.norm_of_nonneg h2.le]
  have h4 : Λ * ℓ / (2 * Real.pi) = Λ / (2 * Real.pi / ℓ) := by
    field_simp
  rw [h3, h4, le_div_iff₀ h2, mul_comm (2 * Real.pi / ℓ) ‖latVec n‖]

private noncomputable def momFinset (ℓ Λ : ℝ) : Finset (Fin 3 → ℤ) :=
  latBall (Λ * ℓ / (2 * Real.pi))

private lemma mem_momFinset_of {ℓ Λ : ℝ} (hℓ : 0 < ℓ) {n : Fin 3 → ℤ}
    (hn : ‖kmomInt ℓ n‖ ≤ Λ) : n ∈ momFinset ℓ Λ :=
  mem_latBall.mpr ((mom_le_iff hℓ n).mp hn)

private lemma notMem_momFinset_of {ℓ Λ : ℝ} (hℓ : 0 < ℓ) {n : Fin 3 → ℤ}
    (hn : ¬ ‖kmomInt ℓ n‖ ≤ Λ) : n ∉ momFinset ℓ Λ :=
  fun h => hn ((mom_le_iff hℓ n).mpr (mem_latBall.mp h))

/-- The truncated lattice Fourier series of `W`. -/
private noncomputable def latPartial (ℓ : ℝ) (W : E3 → ℝ) (Λ : ℝ) (z : E3) : ℂ :=
  ∑' n : Fin 3 → ℤ, if ‖kmomInt ℓ n‖ ≤ Λ then
    latFt ℓ W n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) else 0

private lemma latPartial_eq_sum {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (z : E3) :
    latPartial ℓ W Λ z = ∑ n ∈ momFinset ℓ Λ,
      latFt ℓ W n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) := by
  have h : (∑' n : Fin 3 → ℤ, (if ‖kmomInt ℓ n‖ ≤ Λ then
      latFt ℓ W n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) else 0))
      = ∑ n ∈ momFinset ℓ Λ, (if ‖kmomInt ℓ n‖ ≤ Λ then
        latFt ℓ W n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) else 0) :=
    tsum_eq_sum (L := SummationFilter.unconditional (Fin 3 → ℤ)) (s := momFinset ℓ Λ)
      (f := fun n : Fin 3 → ℤ => if ‖kmomInt ℓ n‖ ≤ Λ then
        latFt ℓ W n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) else 0)
      (fun n hn => by
        rw [if_neg]
        intro hc
        exact hn (mem_momFinset_of hℓ hc))
  rw [latPartial, h]
  exact Finset.sum_congr rfl fun m hm => by
    rw [if_pos ((mom_le_iff hℓ m).mpr (mem_latBall.mp hm))]

private lemma latPartial_bdd {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z, ‖latPartial ℓ W Λ z‖ ≤ D := by
  refine ⟨∑ n ∈ momFinset ℓ Λ, ‖latFt ℓ W n‖, by positivity, fun z => ?_⟩
  rw [latPartial_eq_sum hℓ]
  calc ‖∑ n ∈ momFinset ℓ Λ,
        latFt ℓ W n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))‖
      ≤ ∑ n ∈ momFinset ℓ Λ,
          ‖latFt ℓ W n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ momFinset ℓ Λ, ‖latFt ℓ W n‖ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [norm_mul, norm_exp_I_ofReal, mul_one]

private lemma latPartial_aesm {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    AEStronglyMeasurable (latPartial ℓ W Λ) volume := by
  rw [show latPartial ℓ W Λ = fun z => ∑ n ∈ momFinset ℓ Λ,
      latFt ℓ W n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) from
    funext (latPartial_eq_sum hℓ W)]
  have h := Finset.aestronglyMeasurable_sum (μ := volume) (momFinset ℓ Λ) fun n _ =>
    (by fun_prop : Continuous fun z : E3 =>
      latFt ℓ W n * Complex.exp
        (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))).aestronglyMeasurable
  have h2 : (∑ n ∈ momFinset ℓ Λ, fun z : E3 =>
        latFt ℓ W n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
      = fun z : E3 => ∑ n ∈ momFinset ℓ Λ,
        latFt ℓ W n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) := by
    funext z
    rw [Finset.sum_apply]
  rwa [h2] at h

/-! ## 3. The main estimate -/

private theorem latFourier_main {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWm : AEStronglyMeasurable W volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, R < ‖x‖ → W x = 0)
    (hframe : ∀ {g : E3 → ℂ}, MemLp g 2 volume → tsupport g ⊆ latBox ℓ →
      HasSum (fun n : Fin 3 → ℤ => ‖kinFT g (kmomInt ℓ n)‖ ^ 2)
        (ℓ ^ 3 * ∫ x : E3, ‖g x‖ ^ 2))
    (horth : ∀ j : Fin 3 → ℤ,
      ∫ z in latCell ℓ, Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ j) z : ℝ) : ℂ))
        = if j = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0)
    (hfour : ∀ n : Fin 3 → ℤ,
      ∫ z in latCell ℓ, latPer ℓ W z
          * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
        = latFt ℓ W n)
    (hbox : latBox ℓ =ᵐ[volume] latCell ℓ) :
    Tendsto (fun Λ : ℝ => ∫ z in latBox ℓ,
        ‖latPartial ℓ W Λ z - ((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z‖ ^ 2) atTop (nhds 0) := by
  classical
  set c : ℂ := ((ℓ ^ 3 : ℝ) : ℂ) with hc
  have hcnorm : ‖c‖ = ℓ ^ 3 := by
    rw [hc]
    have hsq : ‖(((ℓ ^ 3 : ℝ) : ℂ))‖ ^ 2 = (ℓ ^ 3) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
    have h3 : (0 : ℝ) < ℓ ^ 3 := by positivity
    nlinarith [norm_nonneg (((ℓ ^ 3 : ℝ) : ℂ)), h3]
  have hbox_int : ∀ (f : E3 → ℂ), ∫ z in latBox ℓ, f z = ∫ z in latCell ℓ, f z :=
    fun f => by rw [Measure.restrict_congr_set hbox]
  have horth_box : ∀ j : Fin 3 → ℤ,
      ∫ z in latBox ℓ, Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ j) z : ℝ) : ℂ))
        = if j = 0 then c else 0 := by
    intro j; rw [hbox_int, horth j, hc]
  obtain ⟨D, hD0, hD⟩ := latPer_bdd (R := R) hℓ hWb hWs
  have hPerAesm : AEStronglyMeasurable (latPer ℓ W) (volume.restrict (latBox ℓ)) :=
    ((latPerCut_aestronglyMeasurable hℓ hWm hWs).restrict (s := latBox ℓ)).congr
      ((MeasureTheory.ae_restrict_iff' (s := latBox ℓ) (measurableSet_latBox ℓ)).mpr
        (Eventually.of_forall fun z hz => by rw [latPerCut, Set.indicator_of_mem hz]))
  have hcut_tsup : tsupport (latPerCut ℓ W) ⊆ latBox ℓ := by
    refine closure_minimal ?_ (isClosed_latBox ℓ)
    intro z hz
    by_contra hzc
    exact hz (by rw [latPerCut, Set.indicator_of_notMem hzc])
  have hcut_frame := hframe (latPerCut_memLp hℓ hWb hWm hWs) hcut_tsup
  have hcut_coeff : ∀ n : Fin 3 → ℤ, kinFT (latPerCut ℓ W) (kmomInt ℓ n) = latFt ℓ W n := by
    intro n
    have h1 : kinFT (latPerCut ℓ W) (kmomInt ℓ n)
        = ∫ z in latBox ℓ, latPer ℓ W z
            * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) := by
      rw [kinFT, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := latBox ℓ)
        (f := fun y => Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))
          * latPerCut ℓ W y)
        (fun y hy => by rw [latPerCut, Set.indicator_of_notMem hy, mul_zero])]
      refine setIntegral_congr_fun (measurableSet_latBox ℓ) fun y hy => ?_
      rw [latPerCut, Set.indicator_of_mem hy, mul_comm]
    rw [h1, hbox_int, hfour n]
  have hsumm : Summable (fun n : Fin 3 → ℤ => ‖latFt ℓ W n‖ ^ 2) :=
    hcut_frame.summable.congr fun n => by rw [hcut_coeff n]
  have key : ∀ Λ : ℝ, (∫ z in latBox ℓ, ‖latPartial ℓ W Λ z - c * latPer ℓ W z‖ ^ 2)
      = ℓ ^ 3 * ∑' n : Fin 3 → ℤ,
          (if ‖kmomInt ℓ n‖ ≤ Λ then 0 else ‖latFt ℓ W n‖ ^ 2) := by
    intro Λ
    set F : E3 → ℂ := fun z => latPartial ℓ W Λ z - c * latPer ℓ W z with hF
    set G : E3 → ℂ := (latBox ℓ).indicator F with hG
    obtain ⟨D₁, hD₁0, hD₁⟩ := latPartial_bdd (ℓ := ℓ) (Λ := Λ) hℓ W
    have hFbd : ∀ u ∈ latBox ℓ, ‖F u‖ ≤ D₁ + ‖c‖ * D := by
      intro u hu
      have h2 := hD u hu
      have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg c)
      have h4 := hD₁ u
      rw [hF]
      calc ‖latPartial ℓ W Λ u - c * latPer ℓ W u‖
          ≤ ‖latPartial ℓ W Λ u‖ + ‖c * latPer ℓ W u‖ := norm_sub_le _ _
        _ ≤ D₁ + ‖c‖ * D := by rw [norm_mul]; linarith
    have hGbd : ∀ u, ‖G u‖ ≤ D₁ + ‖c‖ * D := by
      intro u
      by_cases hu : u ∈ latBox ℓ
      · rw [hG, Set.indicator_of_mem hu]; exact hFbd u hu
      · rw [hG, Set.indicator_of_notMem hu, norm_zero]
        exact add_nonneg hD₁0 (mul_nonneg (norm_nonneg c) hD0)
    have hGaesm : AEStronglyMeasurable G volume := by
      have h1 : AEStronglyMeasurable ((latBox ℓ).indicator (latPartial ℓ W Λ)) volume :=
        (latPartial_aesm hℓ W).indicator (measurableSet_latBox ℓ)
      have h2 : AEStronglyMeasurable (latPerCut ℓ W) volume :=
        latPerCut_aestronglyMeasurable hℓ hWm hWs
      have h3 : G = fun u => (latBox ℓ).indicator (latPartial ℓ W Λ) u
          - c * latPerCut ℓ W u := by
        funext u
        by_cases hu : u ∈ latBox ℓ
        · rw [hG, Set.indicator_of_mem hu, Set.indicator_of_mem hu, hF, latPerCut,
            Set.indicator_of_mem hu]
        · rw [hG, Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, latPerCut,
            Set.indicator_of_notMem hu]
          ring
      rw [h3]
      exact h1.sub (h2.const_mul c)
    have hGmemLp : MemLp G 2 volume :=
      memLp_of_bdd_of_latBox hℓ hGaesm ⟨_, hGbd⟩ fun u hu => by
        rw [hG, Set.indicator_of_notMem hu]
    have hGtsup : tsupport G ⊆ latBox ℓ := by
      refine closure_minimal ?_ (isClosed_latBox ℓ)
      intro z hz
      by_contra hzc
      exact hz (by rw [hG, Set.indicator_of_notMem hzc])
    have hGframe := hframe hGmemLp hGtsup
    have hGint : ∫ u : E3, ‖G u‖ ^ 2 = ∫ z in latBox ℓ, ‖F z‖ ^ 2 := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := latBox ℓ)
        (f := fun u => ‖G u‖ ^ 2) (fun u hu => by
          rw [hG, Set.indicator_of_notMem hu, norm_zero,
            zero_pow (by norm_num : (2 : ℕ) ≠ 0)])]
      refine setIntegral_congr_fun (measurableSet_latBox ℓ) fun u hu => ?_
      rw [hG, Set.indicator_of_mem hu]
    have hGcoeff : ∀ n : Fin 3 → ℤ, kinFT G (kmomInt ℓ n)
        = (if ‖kmomInt ℓ n‖ ≤ Λ then 0 else -c * latFt ℓ W n) := by
      intro n
      have h1 : kinFT G (kmomInt ℓ n) = ∫ z in latBox ℓ,
          Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) * F z := by
        rw [kinFT, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := latBox ℓ)
          (f := fun y => Complex.exp
            (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ))) * G y)
          (fun y hy => by rw [hG, Set.indicator_of_notMem hy, mul_zero])]
        refine setIntegral_congr_fun (measurableSet_latBox ℓ) fun y hy => ?_
        rw [hG, Set.indicator_of_mem hy]
      have hI1 : Integrable (fun z : E3 =>
          Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
            * latPartial ℓ W Λ z) (volume.restrict (latBox ℓ)) :=
        integrableOn_latBox_of_bdd hℓ
          (((by fun_prop : Continuous fun z : E3 => Complex.exp
            (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))).aestronglyMeasurable.restrict
              (s := latBox ℓ)).mul ((latPartial_aesm hℓ W).restrict (s := latBox ℓ)))
          ⟨D₁, hD₁0, fun z _ => by
            rw [norm_mul, norm_exp_neg_I_ofReal, one_mul]; exact hD₁ z⟩
      have hI2 : Integrable (fun z : E3 =>
          Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
            * latPer ℓ W z) (volume.restrict (latBox ℓ)) :=
        integrableOn_latBox_of_bdd hℓ
          (((by fun_prop : Continuous fun z : E3 => Complex.exp
            (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))).aestronglyMeasurable.restrict
              (s := latBox ℓ)).mul hPerAesm)
          ⟨D, hD0, fun z hz => by
            rw [norm_mul, norm_exp_neg_I_ofReal, one_mul]; exact hD z hz⟩
      have hpt : ∀ z : E3, Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) * F z
          = Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
              * latPartial ℓ W Λ z
            - c * (Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
              * latPer ℓ W z) := by
        intro z
        rw [hF]; ring
      have hsplit : (∫ z in latBox ℓ, Complex.exp
            (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) * F z)
          = (∫ z in latBox ℓ, Complex.exp
                (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
                * latPartial ℓ W Λ z)
            - c * (∫ z in latBox ℓ, Complex.exp
                (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) * latPer ℓ W z) := by
        rw [show (∫ z in latBox ℓ, Complex.exp
              (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) * F z)
            = ∫ z in latBox ℓ, (Complex.exp
                (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
                * latPartial ℓ W Λ z
              - c * (Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
                * latPer ℓ W z)) from
          setIntegral_congr_fun (measurableSet_latBox ℓ) fun z _ => hpt z]
        rw [integral_sub hI1 (hI2.const_mul c), integral_const_mul]
      have hfirst : (∫ z in latBox ℓ, Complex.exp
            (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) * latPartial ℓ W Λ z)
          = (if ‖kmomInt ℓ n‖ ≤ Λ then c * latFt ℓ W n else 0) := by
        have hpt2 : ∀ z : E3, Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
              * latPartial ℓ W Λ z
            = ∑ m ∈ momFinset ℓ Λ,
                (latFt ℓ W m * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ m) z : ℝ) : ℂ)))
                  * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) := by
          intro z
          rw [latPartial_eq_sum hℓ W z, Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
        rw [show (∫ z in latBox ℓ, Complex.exp
              (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) * latPartial ℓ W Λ z)
            = ∫ z in latBox ℓ, ∑ m ∈ momFinset ℓ Λ,
                (latFt ℓ W m * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ m) z : ℝ) : ℂ)))
                  * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) from
          setIntegral_congr_fun (measurableSet_latBox ℓ) fun z _ => hpt2 z]
        have hsum := integral_finsetSum (μ := volume.restrict (latBox ℓ))
          (s := momFinset ℓ Λ)
          (f := fun m z => (latFt ℓ W m
              * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ m) z : ℝ) : ℂ)))
                * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))))
          (fun m _ => integrableOn_latBox_of_bdd hℓ
            (((by fun_prop : Continuous fun z : E3 =>
              (latFt ℓ W m * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ m) z : ℝ) : ℂ)))
                * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))).aestronglyMeasurable).restrict
              (s := latBox ℓ))
            ⟨‖latFt ℓ W m‖, norm_nonneg _, fun z _ => by
              rw [norm_mul, norm_mul, norm_exp_I_ofReal, norm_exp_neg_I_ofReal, mul_one,
                mul_one]⟩)
        rw [hsum]
        rw [show (∑ m ∈ momFinset ℓ Λ, ∫ z in latBox ℓ,
              (latFt ℓ W m * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ m) z : ℝ) : ℂ)))
                * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))))
            = ∑ m ∈ momFinset ℓ Λ, latFt ℓ W m * (∫ z in latBox ℓ,
                Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ (m - n)) z : ℝ) : ℂ))) from
          Finset.sum_congr rfl fun m _ => by
            rw [show (∫ z in latBox ℓ, latFt ℓ W m
                  * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ m) z : ℝ) : ℂ))
                  * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))))
                = ∫ z in latBox ℓ, latFt ℓ W m
                    * (Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ m) z : ℝ) : ℂ))
                      * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))) from
              setIntegral_congr_fun (measurableSet_latBox ℓ) fun z _ => by ring]
            rw [integral_const_mul]
            congr 1
            refine setIntegral_congr_fun (measurableSet_latBox ℓ) fun z _ => ?_
            rw [mul_comm
                (Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ m) z : ℝ) : ℂ)))
                (Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))),
              exp_neg_mul_exp_pos (inner ℝ (kmomInt ℓ n) z) (inner ℝ (kmomInt ℓ m) z)]
            rw [kmomInt_sub, inner_sub_left]]
        rw [show (∑ m ∈ momFinset ℓ Λ, latFt ℓ W m * (∫ z in latBox ℓ,
                Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ (m - n)) z : ℝ) : ℂ))))
            = ∑ m ∈ momFinset ℓ Λ, latFt ℓ W m * (if m = n then c else 0) from
          Finset.sum_congr rfl fun m _ => by
            rw [horth_box (m - n)]
            by_cases h : m - n = 0
            · rw [if_pos h, if_pos (sub_eq_zero.mp h)]
            · rw [if_neg h, if_neg (fun hmn => h (sub_eq_zero.mpr hmn))]]
        rw [show (∑ m ∈ momFinset ℓ Λ, latFt ℓ W m * (if m = n then c else 0))
            = ∑ m ∈ momFinset ℓ Λ, (if m = n then latFt ℓ W m * c else 0) from
          Finset.sum_congr rfl fun m _ => by by_cases h : m = n <;> simp [h]]
        rw [Finset.sum_ite_eq']
        by_cases hn : ‖kmomInt ℓ n‖ ≤ Λ
        · rw [if_pos hn, if_pos (mem_momFinset_of hℓ hn)]
          try ring_nf
        · rw [if_neg hn, if_neg (notMem_momFinset_of hℓ hn)]
          try ring_nf
      have hsecond : (∫ z in latBox ℓ, Complex.exp
            (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) * latPer ℓ W z)
          = latFt ℓ W n := by
        rw [show (∫ z in latBox ℓ, Complex.exp
              (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) * latPer ℓ W z)
            = ∫ z in latBox ℓ, latPer ℓ W z
                * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) from
          setIntegral_congr_fun (measurableSet_latBox ℓ) fun z _ => mul_comm _ _]
        rw [hbox_int, hfour n]
      rw [h1, hsplit, hfirst, hsecond]
      by_cases hn : ‖kmomInt ℓ n‖ ≤ Λ
      · rw [if_pos hn, if_pos hn]
        ring
      · rw [if_neg hn, if_neg hn]
        ring
    have h6 : ∑' n : Fin 3 → ℤ, ‖kinFT G (kmomInt ℓ n)‖ ^ 2
        = ℓ ^ 6 * ∑' n : Fin 3 → ℤ,
            (if ‖kmomInt ℓ n‖ ≤ Λ then 0 else ‖latFt ℓ W n‖ ^ 2) := by
      have hpt : ∀ n : Fin 3 → ℤ, ‖kinFT G (kmomInt ℓ n)‖ ^ 2
          = ℓ ^ 6 * (if ‖kmomInt ℓ n‖ ≤ Λ then 0 else ‖latFt ℓ W n‖ ^ 2) := by
        intro n
        rw [hGcoeff n]
        by_cases hn : ‖kmomInt ℓ n‖ ≤ Λ
        · rw [if_pos hn, if_pos hn, norm_zero]
          ring
        · rw [if_neg hn, if_neg hn, norm_mul, norm_neg, hcnorm]
          ring_nf
      rw [tsum_congr hpt, tsum_mul_left]
    have h7 : ℓ ^ 3 * (∫ u : E3, ‖G u‖ ^ 2)
        = ℓ ^ 6 * ∑' n : Fin 3 → ℤ,
            (if ‖kmomInt ℓ n‖ ≤ Λ then 0 else ‖latFt ℓ W n‖ ^ 2) := by
      rw [← hGframe.tsum_eq, h6]
    have h8 : ∫ u : E3, ‖G u‖ ^ 2
        = ℓ ^ 3 * ∑' n : Fin 3 → ℤ,
            (if ‖kmomInt ℓ n‖ ≤ Λ then 0 else ‖latFt ℓ W n‖ ^ 2) := by
      calc ∫ u : E3, ‖G u‖ ^ 2
          = (ℓ ^ 3)⁻¹ * (ℓ ^ 3 * ∫ u : E3, ‖G u‖ ^ 2) := by field_simp
        _ = (ℓ ^ 3)⁻¹ * (ℓ ^ 6 * ∑' n : Fin 3 → ℤ,
              (if ‖kmomInt ℓ n‖ ≤ Λ then 0 else ‖latFt ℓ W n‖ ^ 2)) := by rw [h7]
        _ = ℓ ^ 3 * ∑' n : Fin 3 → ℤ,
              (if ‖kmomInt ℓ n‖ ≤ Λ then 0 else ‖latFt ℓ W n‖ ^ 2) := by
            field_simp
            try ring
    rw [← hGint, h8]
  -- conclusion
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨Λ₀, hΛ₀⟩ := kinFT_lattice_tail_sq_lt (ℓ := ℓ) (R := R) hℓ hWb hWs
    (ε / (2 * ℓ ^ 3)) (by positivity)
  refine ⟨Λ₀, fun Λ hΛ => ?_⟩
  have hbound : ∫ z in latBox ℓ,
      ‖latPartial ℓ W Λ z - c * latPer ℓ W z‖ ^ 2 < ε := by
    rw [key Λ]
    have h1 : (∑' n : Fin 3 → ℤ, (if ‖kmomInt ℓ n‖ ≤ Λ then 0 else ‖latFt ℓ W n‖ ^ 2))
        = ∑' n : Fin 3 → ℤ, (if Λ < ‖kmomInt ℓ n‖ then ‖latFt ℓ W n‖ ^ 2 else 0) := by
      refine tsum_congr fun n => ?_
      by_cases hn : ‖kmomInt ℓ n‖ ≤ Λ
      · rw [if_pos hn, if_neg (not_lt.mpr hn)]
      · rw [if_neg hn, if_pos (not_le.mp hn)]
    rw [h1]
    have h2 : (∑' n : Fin 3 → ℤ, (if Λ < ‖kmomInt ℓ n‖ then ‖latFt ℓ W n‖ ^ 2 else 0))
        ≤ ∑' n : Fin 3 → ℤ,
            (if Λ₀ ≤ ‖kmomInt ℓ n‖ then ‖latFt ℓ W n‖ ^ 2 else 0) := by
      refine Summable.tsum_le_tsum (fun n => ?_) (hsumm.indicator _) (hsumm.indicator _)
      by_cases hn : Λ < ‖kmomInt ℓ n‖
      · rw [if_pos hn, if_pos (le_trans hΛ hn.le)]
      · rw [if_neg hn]; positivity
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 (by positivity)) ?_
    have h3 := hΛ₀ Λ₀ le_rfl
    have h3' : (∑' n : Fin 3 → ℤ,
        (if Λ₀ ≤ ‖kmomInt ℓ n‖ then ‖latFt ℓ W n‖ ^ 2 else 0)) ≤ ε / (2 * ℓ ^ 3) := h3
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left h3' (by positivity)) ?_
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ℓ ^ 3)]
    have hpos : (0 : ℝ) < ℓ ^ 3 * ε := by positivity
    linarith
  have hnn : 0 ≤ ∫ z in latBox ℓ,
      ‖latPartial ℓ W Λ z - c * latPer ℓ W z‖ ^ 2 := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  exact hbound

/-- The truncated lattice Fourier series of a bounded compactly supported weight converges in `L²`
of the torus `(ℝ/ℓℤ)³` to its periodisation: for `W` a.e.-strongly-measurable, bounded, with
`W x = 0` for `‖x‖ > R`, the cube-partial sums `Σ_{‖k_n‖ ≤ Λ} Ŵ(k_n)e^{i⟪k_n,z⟫}`
(`k_n = kmomInt ℓ n = (2π/ℓ)n`) converge in `L²([0,ℓ]³)` to `ℓ³Σ_m W(z + ℓ•latVec m)`.  This is
the classical `L²` Fourier-series convergence for the `ℓ`-periodisation of `W` (whose Fourier
coefficients are exactly `Ŵ(k_n)`), and it is the *valid* replacement of the pointwise Poisson
identity `Work.BoseBoxFock.latticePoisson_kernel` (which holds only for smooth `W`). -/
theorem latFourier_tendsto_periodisation {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    Filter.Tendsto
      (fun Λ : ℝ => ∫ z in {z : EuclideanSpace ℝ (Fin 3) | ∀ i : Fin 3, z i ∈ Set.Icc (0 : ℝ) ℓ},
        ‖(∑' n : Fin 3 → ℤ, if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ Λ then
              (Submission.BoseGases.kinFT (fun y => (W y : ℂ))
                  (Work.BoseBoxFock.kmomInt ℓ n))
                * Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℝ) : ℂ))
            else 0)
          - ((ℓ ^ 3 : ℝ) : ℂ)
              * (∑' m : Fin 3 → ℤ, (W (z + ℓ • Work.BoseBoxFock.latVec m) : ℂ))‖ ^ 2)
      Filter.atTop (nhds (0 : ℝ)) := by
  refine latFourier_main hℓ hWm hWb hWs (fun {g} hg hsupp => frameSampling_latBox hℓ hg hsupp)
    (fun j => latChar_orthogonal hℓ j)
    (fun n => latPer_fourierCoeff (R := R) hℓ hWm hWb hWs
      (fun f hf => latTiling_integral hℓ f hf) n)
    (latBox_ae_eq_latCell hℓ.le)

end Work.BoseBoxFock
