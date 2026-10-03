import Mathlib
import Submission.Work.KMTAreas.A7.FiberOpWideCutEqSelf
import Submission.Work.KMTAreas.A7Hi.fourierCoeff_eq_zero_ae

/-!
# `periodize m ∈ L^∞(ℝ/ℤ)` when the integer Fourier coefficients of `m` are absolutely summable

If `m ∈ L¹(ℝ)` has absolutely summable Fourier transform at the integers,
`∑_j ‖cw m j‖ < ∞` where `cw m j = ∫ θ, m θ · e(-jθ) dθ`, then the periodisation
`periodize m ξ = ∑_k m (x + k)` (`x ∈ [0,1)` the representative of `ξ`) is essentially bounded.

The proof identifies the periodisation with the (uniformly convergent, hence continuous) Fourier
series `g ξ = ∑_j cw m j · fourier j ξ`:

* `Work.KMTPlan.A6.IntegrablePeriodize` gives `periodize m ∈ L¹(ℝ/ℤ)`;
* `fourierCoeff (periodize m) j = cw m j` (`Work.KMTAreas.A7.fourierCoeff_periodize_eq_cw`);
* the Fourier coefficients of `g` are computed with the dominated-convergence theorem for series
  (`hasSum_integral_of_summable_integral_norm`) and the orthogonality of the characters;
* uniqueness of Fourier coefficients for `L¹` functions
  (`Work.KMTAreas.A7Hi.fourierCoeff_eq_zero_ae`) then gives `periodize m = g` a.e., and `g` is
  bounded because `‖fourier j ξ‖ = 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Hi

open MeasureTheory Filter
open scoped Topology BigOperators NNReal ENNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

theorem periodizeMemLpTop {m : ℝ → ℂ} (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖)) :
    MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize m) ⊤
      Work.Analysis.IonescuWainger.circleMeasure := by
  set g : Circ → ℂ := fun ξ => ∑' j : ℤ, Work.KMTAreas.A7.cw m j * fourier (T := 1) j ξ with hgdef
  have hnorm_fourier : ∀ (j : ℤ) (ξ : Circ), ‖fourier (T := 1) j ξ‖ = 1 := by
    intro j ξ
    rw [fourier_apply]
    exact Circle.norm_coe _
  have hterm : ∀ j : ℤ, Continuous (fun ξ : Circ =>
      Work.KMTAreas.A7.cw m j * fourier (T := 1) j ξ) :=
    fun j => continuous_const.mul (fourier (T := 1) j).continuous
  have hbound : ∀ (j : ℤ) (ξ : Circ),
      ‖Work.KMTAreas.A7.cw m j * fourier (T := 1) j ξ‖ ≤ ‖Work.KMTAreas.A7.cw m j‖ := by
    intro j ξ
    rw [norm_mul, hnorm_fourier j ξ, mul_one]
  have hgcont : Continuous g := continuous_tsum hterm hmsum hbound
  have hgbd : ∀ ξ : Circ, ‖g ξ‖ ≤ ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ := by
    intro ξ
    have hs : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j * fourier (T := 1) j ξ‖) :=
      hmsum.congr (fun j => by rw [norm_mul, hnorm_fourier j ξ, mul_one])
    have hs2 := norm_tsum_le_tsum_norm hs
    have hcongr : (∑' i : ℤ, ‖Work.KMTAreas.A7.cw m i * fourier (T := 1) i ξ‖)
        = ∑' i : ℤ, ‖Work.KMTAreas.A7.cw m i‖ :=
      tsum_congr (fun i => by rw [norm_mul, hnorm_fourier i ξ, mul_one])
    rw [hcongr] at hs2
    simpa only [hgdef] using hs2
  have hg_mem : MemLp g ⊤ Work.Analysis.IonescuWainger.circleMeasure :=
    MemLp.mono' (memLp_top_const (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖))
      hgcont.aestronglyMeasurable (Eventually.of_forall hgbd)
  have hg_int : Integrable g Work.Analysis.IonescuWainger.circleMeasure := hg_mem.integrable le_top
  have hper_int : Integrable (Work.Analysis.IonescuWainger.periodize m)
      Work.Analysis.IonescuWainger.circleMeasure := Work.KMTPlan.A6.IntegrablePeriodize hm
  -- the Fourier coefficients of `g`
  have hgfc : ∀ n : ℤ, fourierCoeff g n = Work.KMTAreas.A7.cw m n := by
    intro n
    have hcont_i : ∀ i : ℤ, Continuous (fun ξ : Circ =>
        fourier (T := 1) (-n) ξ * (Work.KMTAreas.A7.cw m i * fourier (T := 1) i ξ)) := fun i =>
      (fourier (T := 1) (-n)).continuous.mul (continuous_const.mul (fourier (T := 1) i).continuous)
    have hle_i : ∀ (i : ℤ) (ξ : Circ),
        ‖fourier (T := 1) (-n) ξ * (Work.KMTAreas.A7.cw m i * fourier (T := 1) i ξ)‖
        ≤ ‖Work.KMTAreas.A7.cw m i‖ := by
      intro i ξ
      rw [norm_mul, norm_mul, hnorm_fourier (-n) ξ, hnorm_fourier i ξ]; norm_num
    have hFint : ∀ i : ℤ, Integrable (fun ξ : Circ =>
        fourier (T := 1) (-n) ξ * (Work.KMTAreas.A7.cw m i * fourier (T := 1) i ξ))
        Work.Analysis.IonescuWainger.circleMeasure := fun i =>
      Integrable.of_bound (hcont_i i).aestronglyMeasurable ‖Work.KMTAreas.A7.cw m i‖
        (Eventually.of_forall (hle_i i))
    have hFsum : Summable (fun i : ℤ => ∫ ξ : Circ,
        ‖fourier (T := 1) (-n) ξ * (Work.KMTAreas.A7.cw m i * fourier (T := 1) i ξ)‖
        ∂Work.Analysis.IonescuWainger.circleMeasure) := by
      refine hmsum.congr (fun i => ?_)
      have hval : (fun ξ : Circ => ‖fourier (T := 1) (-n) ξ * (Work.KMTAreas.A7.cw m i * fourier (T := 1) i ξ)‖)
          = fun _ => ‖Work.KMTAreas.A7.cw m i‖ := by
        funext ξ
        rw [norm_mul, norm_mul, hnorm_fourier (-n) ξ, hnorm_fourier i ξ]; norm_num
      rw [hval]; simp
    have hleft : ∀ i : ℤ, ∫ ξ : Circ, fourier (T := 1) (-n) ξ * (Work.KMTAreas.A7.cw m i * fourier (T := 1) i ξ)
        ∂Work.Analysis.IonescuWainger.circleMeasure
        = Work.KMTAreas.A7.cw m i * (if n = i then 1 else 0) := by
      intro i
      rw [show (fun ξ : Circ => fourier (T := 1) (-n) ξ * (Work.KMTAreas.A7.cw m i * fourier (T := 1) i ξ))
          = fun ξ => Work.KMTAreas.A7.cw m i * (fourier (T := 1) (-n) ξ * fourier (T := 1) i ξ) from
            funext (fun ξ => by ring)]
      rw [integral_const_mul]
      congr 1
      have heq : (fun ξ : Circ => fourier (T := 1) (-n) ξ * fourier (T := 1) i ξ)
          = fun ξ : Circ => fourier (T := 1) (-n) ξ • (fourier (T := 1) i) ξ := by
        funext ξ; rw [smul_eq_mul]
      rw [heq, ← fourierCoeff, fourierCoeff_fourier]
      simp [Pi.single_apply]
    have hHasSum := hasSum_integral_of_summable_integral_norm hFint hFsum
    have hsumeq : (∑' i : ℤ, ∫ ξ : Circ, fourier (T := 1) (-n) ξ * (Work.KMTAreas.A7.cw m i * fourier (T := 1) i ξ)
        ∂Work.Analysis.IonescuWainger.circleMeasure) = Work.KMTAreas.A7.cw m n := by
      rw [funext hleft, tsum_eq_single n]
      · simp
      · intro i hi; rw [if_neg (Ne.symm hi), mul_zero]
    have hcongr : fourierCoeff g n = ∫ ξ : Circ, ∑' i : ℤ,
        fourier (T := 1) (-n) ξ * (Work.KMTAreas.A7.cw m i * fourier (T := 1) i ξ)
        ∂Work.Analysis.IonescuWainger.circleMeasure := by
      rw [fourierCoeff]
      refine integral_congr_ae (Eventually.of_forall (fun ξ => ?_))
      show fourier (T := 1) (-n) ξ • g ξ
        = ∑' i : ℤ, fourier (T := 1) (-n) ξ * (Work.KMTAreas.A7.cw m i * fourier (T := 1) i ξ)
      have hstep : fourier (T := 1) (-n) ξ • g ξ
          = fourier (T := 1) (-n) ξ * (∑' j : ℤ, Work.KMTAreas.A7.cw m j * fourier (T := 1) j ξ) := by
        simp only [hgdef, smul_eq_mul]
      rw [hstep, ← tsum_mul_left]
    rw [hcongr, hHasSum.tsum_eq.symm, hsumeq]
  -- the difference has vanishing Fourier coefficients
  have hffc : ∀ n : ℤ, fourierCoeff (fun ξ : Circ => Work.Analysis.IonescuWainger.periodize m ξ - g ξ) n = 0 := by
    intro n
    have h1 : Integrable (fun ξ : Circ => fourier (T := 1) (-n) ξ * Work.Analysis.IonescuWainger.periodize m ξ)
        Work.Analysis.IonescuWainger.circleMeasure :=
      hper_int.bdd_mul (c := 1) (fourier (T := 1) (-n)).continuous.aestronglyMeasurable
        (Eventually.of_forall (fun ξ => by
          rw [fourier_apply]; exact le_of_eq (Circle.norm_coe _)))
    have h2 : Integrable (fun ξ : Circ => fourier (T := 1) (-n) ξ * g ξ)
        Work.Analysis.IonescuWainger.circleMeasure :=
      Integrable.of_bound ((fourier (T := 1) (-n)).continuous.mul hgcont).aestronglyMeasurable
        (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖) (Eventually.of_forall (fun ξ => by
          rw [norm_mul, hnorm_fourier (-n) ξ, one_mul]; exact hgbd ξ))
    have hsub : fourierCoeff (fun ξ : Circ => Work.Analysis.IonescuWainger.periodize m ξ - g ξ) n
        = fourierCoeff (Work.Analysis.IonescuWainger.periodize m) n - fourierCoeff g n := by
      rw [fourierCoeff, fourierCoeff, fourierCoeff]
      simp only [smul_eq_mul]
      rw [show (fun ξ : Circ => fourier (T := 1) (-n) ξ * (Work.Analysis.IonescuWainger.periodize m ξ - g ξ))
          = fun ξ => fourier (T := 1) (-n) ξ * Work.Analysis.IonescuWainger.periodize m ξ
              - fourier (T := 1) (-n) ξ * g ξ from funext (fun ξ => mul_sub _ _ _)]
      rw [integral_sub h1 h2]
    rw [hsub, Work.KMTAreas.A7.fourierCoeff_periodize_eq_cw hm n, hgfc n, sub_self]
  have hInt_u : Integrable (fun ξ : Circ => Work.Analysis.IonescuWainger.periodize m ξ - g ξ)
      Work.Analysis.IonescuWainger.circleMeasure := hper_int.sub hg_int
  have huae := fourierCoeff_eq_zero_ae hInt_u hffc
  have hge : g =ᵐ[Work.Analysis.IonescuWainger.circleMeasure] Work.Analysis.IonescuWainger.periodize m :=
    huae.mono (fun ξ h => by
      have h0 : Work.Analysis.IonescuWainger.periodize m ξ - g ξ = 0 := h
      exact (sub_eq_zero.mp h0).symm)
  exact hg_mem.ae_eq hge

end

end Work.KMTAreas.A7Hi
