/-
# `bound_Z7`: the estimate for the projector-derivative term `Z₇`

The paper (Elgindi, Annals 194 (3) 2021, §"`L²` coercivity for `𝓛_Γ^T` with one
`z`-derivative") expands `D_z(𝓛_Γ^T f)` into seven terms `I₁,…,I₇` and estimates each.
This file treats the seventh one,

  `Z7 α f z θ = (Γ(θ)/c) · C₀(f) · 2z²(2-z)/(1+z)⁴`,  `C₀(f) = L₁₂(Transport f)(0)`,

proving `IntegrableOn` of its pairing with `D_z f` against the weight `w² sin(2θ)^{-η}` and
the lower bound `≥ -(1/32) EDz f - 10⁷ Ef f`, using the hypothesis `(C₀ f)² ≤ 32 Ef f`.

The argument is a pointwise AM-GM `|Z₇ D_z f| W ≤ (1/32)(D_z f)² W + 8 Z₇² W` together
with the tensor bound `∫∫ Z₇² W = (C₀ f)² · (∫_θ (Γ/c)² sin^{-η}) · (∫_z g² w²)`, where
`g(z) = 2z²(2-z)/(1+z)⁴`.  The two one-dimensional factors are computed:

* `∫_z g² w² = 4` (elementary antiderivative `-4(z²-z+1)/(1+z)³`);
* `∫_θ (Γ/c)² sin(2θ)^{-η} ≤ 25 · 189`, from `∫ sin(2θ)^{-η} ≤ 189` (`etaWeight_integral_le`)
  and `c α ≥ 1/5` (an explicit lower bound for the normalisation constant).

Since `(C₀f)² ≤ 32 Ef f`, this gives `8 ∫∫ Z₇² W ≤ 8·(18900·32) Ef f ≤ 10⁷ Ef f`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.EDz_eq_wip
import Submission.Work.Coercivity.f_sq_w_sq_integrable
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.Coercivity.zero_set_deriv_countable
import Submission.Work.Coercivity.integral_sin_two_neg_rpow_le
import Submission.Work.Coercivity.L2CoercivityTransportEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The product measure and the a.e. algebra of `f` and `D_z f` -/

private abbrev Pz7 : Measure (ℝ × ℝ) :=
  (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)

private lemma w_ne_zero_of_pos7 {z : ℝ} (hz : 0 < z) : Spaces.w z ≠ 0 := by
  have h1 : (1 + z) ≠ 0 := by linarith
  simp only [Spaces.w]
  exact div_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 (ne_of_gt hz))

private lemma measurable_w7 : Measurable (fun z : ℝ => Spaces.w z) := by
  show Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
  fun_prop

private lemma ae_w_ne_zero7 : ∀ᵐ z ∂(volume.restrict Spaces.Iz), Spaces.w z ≠ 0 := by
  have hsub : {z : ℝ | Spaces.w z = 0} ∩ Set.Ici 0 ⊆ ({0} : Set ℝ) := by
    intro z hz
    obtain ⟨hz0, hzI⟩ := hz
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact w_ne_zero_of_pos7 (lt_of_le_of_ne hzI (Ne.symm hne)) hz0
  rw [MeasureTheory.ae_iff]
  rw [show {z : ℝ | ¬ Spaces.w z ≠ 0} = {z : ℝ | Spaces.w z = 0} by ext z; simp]
  change (volume.restrict (Set.Ici 0)) {z : ℝ | Spaces.w z = 0} = 0
  rw [MeasureTheory.Measure.restrict_apply
    (show MeasurableSet {z : ℝ | Spaces.w z = 0} from
      measurable_w7 (measurableSet_singleton 0))]
  exact measure_mono_null hsub (measure_singleton 0)

private lemma ae_w_ne_zero_prod7 : ∀ᵐ p ∂Pz7, Spaces.w p.1 ≠ 0 := by
  have hset : MeasurableSet {p : ℝ × ℝ | Spaces.w p.1 ≠ 0} :=
    (measurable_w7.comp measurable_fst) (measurableSet_singleton 0).compl
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
    (p := fun p : ℝ × ℝ => Spaces.w p.1 ≠ 0) hset]
  filter_upwards [ae_w_ne_zero7] with z hz
  exact Filter.Eventually.of_forall fun _ => hz

private lemma aesm_f_sq7 (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 ^ 2) Pz7 := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) = Pz7 := by
    rw [Pz7, MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  have h1 : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) Pz7 := by
    rw [← hvol]
    exact f_sq_w_sq_integrable α f hi
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.w p.1 ^ 2)⁻¹) Pz7 := by
    apply Measurable.aestronglyMeasurable
    show Measurable (fun p : ℝ × ℝ => (((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2)⁻¹)
    fun_prop
  have h3 := h1.aestronglyMeasurable.mul h2
  refine h3.congr ?_
  filter_upwards [ae_w_ne_zero_prod7] with p hp
  rw [Pi.mul_apply]
  have hw2 : Spaces.w p.1 ^ 2 ≠ 0 := pow_ne_zero 2 hp
  field_simp

private lemma nullMeasurableSet_f_eq_zero7 (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    NullMeasurableSet {p : ℝ × ℝ | f p.1 p.2 = 0} Pz7 := by
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 ^ 2) Pz7 := aesm_f_sq7 α f hi
  have h2 : NullMeasurableSet {p : ℝ × ℝ | f p.1 p.2 ^ 2 = 0} Pz7 :=
    h1.nullMeasurableSet_eq_fun aestronglyMeasurable_const
  refine h2.congr ?_
  filter_upwards with p
  exact propext (by rw [pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)])

private lemma ae_snd_mem_Iθ7 : ∀ᵐ p ∂Pz7, p.2 ∈ Spaces.Iθ := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => p.2 ∈ Spaces.Iθ)
    (measurableSet_Icc.preimage measurable_snd)]
  filter_upwards with x
  exact MeasureTheory.ae_restrict_mem measurableSet_Icc

private lemma ae_sin_ne_zero7 : ∀ᵐ p ∂Pz7, Real.sin (2 * p.2) ≠ 0 :=
  MeasureTheory.ae_mono (by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self
      MeasureTheory.Measure.restrict_le_self) ae_sin_two_ne_zero

private lemma ae_sin_pos7 : ∀ᵐ p ∂Pz7, 0 < Real.sin (2 * p.2) := by
  filter_upwards [ae_snd_mem_Iθ7, ae_sin_ne_zero7] with p hp hne
  exact lt_of_le_of_ne
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hp.1], by linarith [hp.2, Real.pi_pos]⟩)
    (Ne.symm hne)

private lemma integrable_Dz_sq_Weta7 (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    Integrable (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 ^ 2 * Weta p.1 p.2) Pz7 := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) = Pz7 := by
    rw [Pz7, MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  rw [← hvol]
  refine hi.intDz.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.uncurry, Weta]
  ring

private lemma integrable_Dz_sq_w_sq7 (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    Integrable (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 ^ 2 * Spaces.w p.1 ^ 2) Pz7 := by
  have hW := integrable_Dz_sq_Weta7 α f hi
  have hsin : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Spaces.eta)) := by fun_prop
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 ^ 2 * Spaces.w p.1 ^ 2) Pz7 := by
    refine (hW.aestronglyMeasurable.mul hsin.aestronglyMeasurable).congr ?_
    filter_upwards [ae_sin_pos7] with p hp
    have hs : (Real.sin (2 * p.2)) ^ (-Spaces.eta) * (Real.sin (2 * p.2)) ^ (Spaces.eta) = 1 := by
      rw [← Real.rpow_add hp, neg_add_cancel, Real.rpow_zero]
    have hs' : (Real.sin (2 * p.2)) ^ (Spaces.eta)
        = ((Real.sin (2 * p.2)) ^ (-Spaces.eta))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hp), inv_inv]
    simp only [Pi.mul_apply, Weta, hs']
    have hne : (Real.sin (2 * p.2)) ^ (-Spaces.eta) ≠ 0 := by positivity
    field_simp
  refine hW.mono' haesm ?_
  filter_upwards [ae_sin_pos7] with p hp
  have h1 : (1 : ℝ) ≤ (Real.sin (2 * p.2)) ^ (-Spaces.eta) := by
    rw [Real.rpow_neg (le_of_lt hp)]
    exact (one_le_inv₀ (Real.rpow_pos_of_pos hp _)).mpr
      (Real.rpow_le_one (le_of_lt hp) (Real.sin_le_one _) (by norm_num [Spaces.eta]))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  simp only [Weta]
  calc Spaces.Dz f p.1 p.2 ^ 2 * Spaces.w p.1 ^ 2
      = Spaces.Dz f p.1 p.2 ^ 2 * Spaces.w p.1 ^ 2 * 1 := (mul_one _).symm
    _ ≤ Spaces.Dz f p.1 p.2 ^ 2 * Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = Spaces.Dz f p.1 p.2 ^ 2
          * (Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) := by ring

private lemma aesm_Dz_sq7 (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 ^ 2) Pz7 := by
  have h1 := (integrable_Dz_sq_w_sq7 α f hi).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.w p.1 ^ 2)⁻¹) Pz7 := by
    apply Measurable.aestronglyMeasurable
    show Measurable (fun p : ℝ × ℝ => (((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2)⁻¹)
    fun_prop
  refine (h1.mul h2).congr ?_
  filter_upwards [ae_w_ne_zero_prod7] with p hp
  rw [Pi.mul_apply]
  have hw2 : Spaces.w p.1 ^ 2 ≠ 0 := pow_ne_zero 2 hp
  field_simp

private def Z7Ppsi (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ENNReal :=
  fun p => ENNReal.ofReal (Spaces.Dz f p.1 p.2 ^ 2)
    * Set.indicator {q : ℝ × ℝ | f q.1 q.2 = 0} (fun _ => (1 : ENNReal)) p

/-- Under `CoerciveData`, `D_z f` vanishes almost everywhere on the zero set of `f`. -/
private lemma Dz_zero_ae_on_zero_set7 (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    ∀ᵐ p ∂Pz7, f p.1 p.2 = 0 → Spaces.Dz f p.1 p.2 = 0 := by
  have hψ : AEMeasurable (Z7Ppsi f) Pz7 := by
    have hA : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Spaces.Dz f p.1 p.2 ^ 2)) Pz7 :=
      ENNReal.measurable_ofReal.comp_aemeasurable (aesm_Dz_sq7 α f hi).aemeasurable
    have hB : AEMeasurable (fun p : ℝ × ℝ =>
        Set.indicator {q : ℝ × ℝ | f q.1 q.2 = 0} (fun _ => (1 : ENNReal)) p) Pz7 :=
      AEMeasurable.indicator₀ (f := fun _ : ℝ × ℝ => (1 : ENNReal))
        (s := {q : ℝ × ℝ | f q.1 q.2 = 0}) aemeasurable_const
        (nullMeasurableSet_f_eq_zero7 α f hi)
    exact hA.mul hB
  have hslice : ∀ θ : ℝ, ∫⁻ z, Z7Ppsi f (z, θ) ∂(volume.restrict Spaces.Iz) = 0 := by
    intro θ
    have hsub : {z : ℝ | Z7Ppsi f (z, θ) ≠ 0}
        ⊆ {z : ℝ | f z θ = 0 ∧ deriv (fun u => f u θ) z ≠ 0} := by
      intro z hz
      simp only [Set.mem_setOf_eq]
      have h1 : ENNReal.ofReal (Spaces.Dz f z θ ^ 2) ≠ 0 := by
        intro hc
        exact hz (by simp only [Z7Ppsi, hc, zero_mul])
      have h2 : Set.indicator {q : ℝ × ℝ | f q.1 q.2 = 0}
          (fun _ => (1 : ENNReal)) (z, θ) ≠ 0 := by
        intro hc
        exact hz (by simp only [Z7Ppsi, hc, mul_zero])
      have h3 : (z, θ) ∈ {q : ℝ × ℝ | f q.1 q.2 = 0} := by
        by_contra hc
        rw [Set.indicator_of_notMem hc] at h2
        exact h2 rfl
      refine ⟨h3, fun hd => ?_⟩
      have hDz : Spaces.Dz f z θ ≠ 0 := fun hc => h1 (by rw [hc]; simp)
      exact hDz (by rw [Spaces.Dz, Spaces.pz, hd, mul_zero])
    have hcount : ({z : ℝ | f z θ = 0 ∧ deriv (fun u => f u θ) z ≠ 0}).Countable :=
      zero_set_deriv_countable (fun u => f u θ)
    have h0 : (volume.restrict Spaces.Iz) {z : ℝ | Z7Ppsi f (z, θ) ≠ 0} = 0 :=
      measure_mono_null hsub (Set.Countable.measure_zero hcount _)
    rw [MeasureTheory.lintegral_congr_ae ((MeasureTheory.ae_iff).mpr h0),
      MeasureTheory.lintegral_zero]
  have hsum : ∫⁻ p, Z7Ppsi f p ∂Pz7 = 0 := by
    rw [MeasureTheory.lintegral_prod_symm (Z7Ppsi f) hψ]
    rw [show (∫⁻ θ, ∫⁻ z, Z7Ppsi f (z, θ) ∂(volume.restrict Spaces.Iz)
          ∂(volume.restrict Spaces.Iθ))
        = ∫⁻ _θ, (0 : ENNReal) ∂(volume.restrict Spaces.Iθ) from
      MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun θ => hslice θ),
      MeasureTheory.lintegral_zero]
  have hz0 : Z7Ppsi f =ᵐ[Pz7] 0 := (MeasureTheory.lintegral_eq_zero_iff' hψ).mp hsum
  filter_upwards [hz0] with p hp hf
  have h1 : ENNReal.ofReal (Spaces.Dz f p.1 p.2 ^ 2)
      * Set.indicator {q : ℝ × ℝ | f q.1 q.2 = 0} (fun _ => (1 : ENNReal)) p = 0 := by
    simpa only [Z7Ppsi, Pi.zero_apply] using hp
  rw [Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | f q.1 q.2 = 0} from hf), mul_one] at h1
  exact sq_eq_zero_iff.mp
    (le_antisymm (ENNReal.ofReal_eq_zero.mp h1) (sq_nonneg _))


/-! ## The angular and radial one-dimensional bounds -/

private lemma Gam_le_one7 (α : ℝ) (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    Spaces.Gam α θ ≤ 1 := by
  rw [Spaces.Gam]
  refine Real.rpow_le_one (mul_nonneg ?_ (sq_nonneg _)) (sin_mul_cos_sq_le_one hθ) (by positivity)
  exact Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩

private lemma Weta_nonneg7 {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) (z : ℝ) : 0 ≤ Weta z θ := by
  rw [Weta]
  refine mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ _)
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- `c α ≥ 1/5`: on `[π/6, π/3]` the integrand `ΓK = 3 (sinθ cos²θ)^{1+α/3}` is at least
`3^{5/3}/16` and the interval has length `π/6`, while `3^{5/3} π ≥ 6.2 · 3.1415 ≥ 96/5`. -/
private lemma c_ge_fifth7 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) : (1 : ℝ) / 5 ≤ Spaces.c α := by
  have hlb : ∀ θ ∈ Set.Icc (π / 6) (π / 3),
      (3 : ℝ) ^ ((5 : ℝ) / 3) / 16 ≤ Spaces.Gam α θ * Spaces.K θ := by
    intro θ hθ
    have hs_ge : (1 : ℝ) / 2 ≤ Real.sin θ := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := π / 6) (y := θ)
        (by linarith [Real.pi_pos]) (by linarith [hθ.2, Real.pi_pos]) hθ.1
      rwa [Real.sin_pi_div_six] at h
    have hs_le : Real.sin θ ≤ Real.sqrt 3 / 2 := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := θ) (y := π / 3)
        (by linarith [hθ.1, Real.pi_pos]) (by linarith [Real.pi_pos]) hθ.2
      rwa [Real.sin_pi_div_three] at h
    set s : ℝ := Real.sin θ with hs
    have hs0 : 0 ≤ s := by linarith
    have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsq : (1 : ℝ) / 4 ≤ s ^ 2 := by nlinarith [hs_ge, sq_nonneg (s - 1 / 2)]
    have hfac : 0 ≤ (Real.sqrt 3 / 2 - s) * (8 * s ^ 2 + 4 * Real.sqrt 3 * s - 2) := by
      refine mul_nonneg (by linarith) ?_
      nlinarith [hsq, hs_ge, Real.sqrt_nonneg 3]
    have hkey : (Real.sqrt 3 / 2 - s) * (8 * s ^ 2 + 4 * Real.sqrt 3 * s - 2)
        = 8 * (s * (1 - s ^ 2)) - Real.sqrt 3 := by
      nlinarith [hs3]
    have h8u : Real.sqrt 3 ≤ 8 * (s * (1 - s ^ 2)) := by linarith
    have hu : Real.sin θ * Real.cos θ ^ 2 = s * (1 - s ^ 2) := by
      have h := Real.sin_sq_add_cos_sq θ
      rw [← hs] at h
      nlinarith [h]
    have hsin_nn : 0 ≤ Real.sin θ := by rw [← hs]; exact hs0
    have hu_le1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
      have hc2 : Real.cos θ ^ 2 ≤ 1 := by
        have h := mul_nonneg (by linarith [Real.cos_le_one θ] : (0 : ℝ) ≤ 1 - Real.cos θ)
          (by linarith [Real.neg_one_le_cos θ] : (0 : ℝ) ≤ 1 + Real.cos θ)
        nlinarith [h]
      nlinarith [Real.sin_le_one θ, hc2, sq_nonneg (Real.cos θ), hsin_nn]
    have hu_ge : Real.sqrt 3 / 8 ≤ Real.sin θ * Real.cos θ ^ 2 := by
      rw [hu]; linarith
    have hprod : Spaces.Gam α θ * Spaces.K θ
        = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 + 1) := by
      rw [Spaces.Gam, Spaces.K,
        Real.rpow_add' (mul_nonneg hsin_nn (sq_nonneg _)) (by positivity), Real.rpow_one]
      ring
    have hexp : (Real.sin θ * Real.cos θ ^ 2) ^ ((4 : ℝ) / 3)
        ≤ (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 + 1) :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith) hu_le1 (by linarith)
    have hbase : ((Real.sqrt 3) / 8) ^ ((4 : ℝ) / 3)
        ≤ (Real.sin θ * Real.cos θ ^ 2) ^ ((4 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hu_ge (by norm_num)
    have hu4 : ((Real.sqrt 3) / 8) ^ ((4 : ℝ) / 3) = (3 : ℝ) ^ ((2 : ℝ) / 3) / 16 := by
      rw [Real.sqrt_eq_rpow, show (8 : ℝ) = 2 ^ 3 by norm_num,
        Real.div_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_natCast (2 : ℝ) 3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        show ((1 : ℝ) / 2) * ((4 : ℝ) / 3) = 2 / 3 by norm_num,
        show ((3 : ℕ) : ℝ) * (4 / 3) = 4 by norm_num]
      norm_num
    have hval : (3 : ℝ) * ((Real.sqrt 3) / 8) ^ ((4 : ℝ) / 3)
        = (3 : ℝ) ^ ((5 : ℝ) / 3) / 16 := by
      have h32 : (3 : ℝ) * (3 : ℝ) ^ ((2 : ℝ) / 3) = (3 : ℝ) ^ ((5 : ℝ) / 3) := by
        conv_rhs => rw [show ((5 : ℝ) / 3) = 1 + 2 / 3 by norm_num,
          Real.rpow_add (by norm_num : (0 : ℝ) < 3), Real.rpow_one]
      rw [hu4, ← mul_div_assoc, h32]
    rw [hprod]
    linarith [hexp, hbase, hval]
  have hint : IntegrableOn (fun θ : ℝ => Spaces.Gam α θ * Spaces.K θ) Spaces.Iθ :=
    Spaces.CAux.integrableOn_GamK α hα
  have hsub : Set.Icc (π / 6) (π / 3) ⊆ Spaces.Iθ := fun θ hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hIntOn : IntegrableOn (fun θ : ℝ => Spaces.Gam α θ * Spaces.K θ)
      (Set.Icc (π / 6) (π / 3)) := hint.mono_set hsub
  have hfin : volume (Set.Icc (π / 6) (π / 3)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hge : (3 : ℝ) ^ ((5 : ℝ) / 3) / 16 * volume.real (Set.Icc (π / 6) (π / 3))
      ≤ ∫ θ in Set.Icc (π / 6) (π / 3), Spaces.Gam α θ * Spaces.K θ :=
    MeasureTheory.setIntegral_ge_of_const_le_real measurableSet_Icc hfin hlb hIntOn
  have hvol : volume.real (Set.Icc (π / 6) (π / 3)) = π / 6 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hge' : (3 : ℝ) ^ ((5 : ℝ) / 3) / 16 * (π / 6)
      ≤ ∫ θ in Set.Icc (π / 6) (π / 3), Spaces.Gam α θ * Spaces.K θ := by
    calc (3 : ℝ) ^ ((5 : ℝ) / 3) / 16 * (π / 6)
        = (3 : ℝ) ^ ((5 : ℝ) / 3) / 16 * volume.real (Set.Icc (π / 6) (π / 3)) := by
          rw [hvol]
      _ ≤ _ := hge
  have hle : ∫ θ in Set.Icc (π / 6) (π / 3), Spaces.Gam α θ * Spaces.K θ ≤ Spaces.c α := by
    have hnn : 0 ≤ᵐ[volume.restrict Spaces.Iθ] (fun θ => Spaces.Gam α θ * Spaces.K θ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact (Spaces.gamK_bounds α θ hα hθ).1
    have hst : Set.Icc (π / 6) (π / 3) ≤ᵐ[volume] Spaces.Iθ := by
      filter_upwards with θ hθ; exact hsub hθ
    have := MeasureTheory.setIntegral_mono_set hint hnn hst
    simpa [Spaces.c] using this
  have hnum : (1 : ℝ) / 5 ≤ (3 : ℝ) ^ ((5 : ℝ) / 3) / 16 * (π / 6) := by
    have h3 : (31 : ℝ) / 5 ≤ (3 : ℝ) ^ ((5 : ℝ) / 3) := by
      have hiff := Real.rpow_le_rpow_iff (x := (31 : ℝ) / 5)
        (y := (3 : ℝ) ^ ((5 : ℝ) / 3)) (z := (3 : ℝ))
        (by norm_num) (by positivity) (by norm_num)
      rw [← hiff]
      have hcube : ((3 : ℝ) ^ ((5 : ℝ) / 3)) ^ (3 : ℝ) = (243 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
          show ((5 : ℝ) / 3) * (3 : ℝ) = 5 by norm_num]
        rw [show (5 : ℝ) = (((5 : ℕ) : ℝ)) from by norm_num, Real.rpow_natCast]
        norm_num
      rw [hcube, show ((3 : ℝ)) = (((3 : ℕ) : ℝ)) from by norm_num, Real.rpow_natCast]
      norm_num
    nlinarith [h3, Real.pi_gt_d4, Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) ((5 : ℝ) / 3)]
  linarith [hge', hle, hnum]

private lemma ang_int7 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Integrable (fun θ : ℝ =>
        (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        (volume.restrict Spaces.Iθ)
      ∧ (∫ θ in Spaces.Iθ,
          (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) ≤ 4725 := by
  have hc5 : (1 : ℝ) / 5 ≤ Spaces.c α := c_ge_fifth7 α hα hα1
  have hcpos : 0 < Spaces.c α := lt_of_lt_of_le (by norm_num) hc5
  have hbase : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ :=
    (integral_sin_two_neg_rpow_le Spaces.eta (by norm_num [Spaces.eta])
      (by norm_num [Spaces.eta])).1
  have hdom : Integrable (fun θ : ℝ => 25 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (volume.restrict Spaces.Iθ) := hbase.const_mul 25
  have hpt : ∀ θ ∈ Spaces.Iθ,
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
        ≤ 25 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    intro θ hθ
    have hG := Gam_le_one7 α hα hθ
    have hG0 : 0 ≤ Spaces.Gam α θ := by
      rw [Spaces.Gam]
      exact Real.rpow_nonneg (mul_nonneg
        (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)) _
    have hs0 : 0 ≤ (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _
    have hsq : (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 25 := by
      rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (Spaces.c α) ^ 2)]
      have h1 : (Spaces.Gam α θ) ^ 2 ≤ 1 := by nlinarith [hG0, hG]
      have h2 : (1 : ℝ) ≤ 25 * (Spaces.c α) ^ 2 := by nlinarith [hc5, hcpos]
      nlinarith
    exact mul_le_mul_of_nonneg_right hsq hs0
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (volume.restrict Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    unfold Spaces.Gam
    fun_prop
  have hnn : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      0 ≤ (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' hdom hmeas ?_
    filter_upwards [hnn, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ hθI
    rw [Real.norm_of_nonneg hθ]
    exact hpt θ hθI
  · have hmono : (∫ θ in Spaces.Iθ,
        (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        ≤ ∫ θ in Spaces.Iθ, 25 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
      refine integral_mono_of_nonneg hnn hdom ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hpt θ hθ
    calc (∫ θ in Spaces.Iθ,
          (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        ≤ ∫ θ in Spaces.Iθ, 25 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := hmono
      _ = 25 * ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ 25 * 189 := by linarith [etaWeight_integral_le]
      _ = 4725 := by norm_num

/-- `∫_0^∞ (2z²(2-z)/(1+z)⁴)² w(z)² dz = 4`, with antiderivative
`-12(1+z)^{-1} + 12(1+z)^{-2} - 4(1+z)^{-3}`. -/
private lemma gprof_aux7 :
    Integrable (fun z : ℝ => (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4) ^ 2 * (Spaces.w z) ^ 2)
        (volume.restrict Spaces.Iz)
    ∧ (∫ z in Spaces.Iz, (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4) ^ 2 * (Spaces.w z) ^ 2) = 4 := by
  set f' : ℝ → ℝ := fun z => 4 * (2 - z) ^ 2 / (1 + z) ^ 4 with hf'
  set F : ℝ → ℝ := fun z => -12 * ((1 + z)⁻¹) ^ 3 + 12 * ((1 + z)⁻¹) ^ 2 - 4 * ((1 + z)⁻¹)
    with hF
  have hderiv : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt F (f' z) z := by
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    have hzne : (1 : ℝ) + z ≠ 0 := by positivity
    have hGz := ((hasDerivAt_id z).const_add (1 : ℝ)).inv hzne
    have h := ((((hGz).pow 3).const_mul (-12)).add (((hGz).pow 2).const_mul 12)).sub
      ((hGz).const_mul 4)
    refine h.congr_deriv ?_
    rw [hf']
    simp only [id_eq, Pi.inv_apply]
    simp only [div_eq_mul_inv, neg_mul, one_mul, inv_pow]
    field_simp
    ring
  have hpos : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ f' z := by
    intro z _
    rw [hf']; positivity
  have hlim : Tendsto F atTop (nhds 0) := by
    have hlin : Tendsto (fun z : ℝ => 1 + z) atTop atTop :=
      Filter.tendsto_atTop.mpr fun a => Filter.eventually_atTop.mpr ⟨a, fun b hb => by linarith⟩
    have hinv : Tendsto (fun z : ℝ => (1 + z)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hlin
    have h := (((hinv.pow 3).const_mul (-12)).add ((hinv.pow 2).const_mul 12)).sub
      (hinv.const_mul 4)
    simpa [hF] using h
  have hF0 : F 0 = -4 := by rw [hF]; norm_num
  have hint : IntegrableOn f' (Set.Ioi 0) :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have hval : ∫ z in Set.Ioi 0, f' z = 4 := by
    have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
    rw [hF0] at h
    linarith
  have hae' : (fun z : ℝ => (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4) ^ 2 * (Spaces.w z) ^ 2)
      =ᵐ[volume.restrict (Set.Ioi 0)] f' := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
    rw [hf', Spaces.w]
    have hz' : (0 : ℝ) < z := hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    field_simp
    ring
  have h2 : volume.restrict Spaces.Iz = volume.restrict (Set.Ioi 0) := by
    rw [Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
  have h' : IntegrableOn (fun z : ℝ => (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4) ^ 2
      * (Spaces.w z) ^ 2) (Set.Ioi 0) := hint.congr hae'.symm
  refine ⟨?_, ?_⟩
  · rw [h2]; exact h'
  · rw [h2, MeasureTheory.integral_congr_ae hae']
    exact hval

/-! ## The pointwise AM-GM bound -/

private lemma Z7_pointwise (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    |Z7 α f z θ * Spaces.Dz f z θ * Weta z θ|
      ≤ (1 / 32) * ((Spaces.Dz f z θ) ^ 2 * Weta z θ)
        + 8 * ((Z7 α f z θ) ^ 2 * Weta z θ) := by
  have hW : 0 ≤ Weta z θ := Weta_nonneg7 hθ z
  have h1 : |Z7 α f z θ * Spaces.Dz f z θ * Weta z θ|
      = |Z7 α f z θ| * |Spaces.Dz f z θ| * Weta z θ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hW]
  rw [h1]
  have ha : (Spaces.Dz f z θ) ^ 2 = |Spaces.Dz f z θ| ^ 2 := by rw [sq_abs]
  have hb : (Z7 α f z θ) ^ 2 = |Z7 α f z θ| ^ 2 := by rw [sq_abs]
  rw [ha, hb]
  nlinarith [mul_nonneg hW (sq_nonneg (|Spaces.Dz f z θ| - 16 * |Z7 α f z θ|))]

/-! ## The main theorem -/

theorem bound_Z7 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hi : CoerciveData α f) (hC0 : (C0 f) ^ 2 ≤ 32 * Ef f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Z7 α f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)
    ∧ wip Weta (Z7 α f) (Spaces.Dz f) ≥ -((1 / 32) * EDz f + 10 ^ 7 * Ef f) := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) = Pz7 := by
    rw [Pz7, MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  -- ## The two one-dimensional integrals of `Z₇²·Weta`
  have hA2int := gprof_aux7.1
  have hA2val := gprof_aux7.2
  have hB2int := (ang_int7 α hα hα1).1
  have hB2val := (ang_int7 α hα hα1).2
  have hProd : Integrable (fun p : ℝ × ℝ =>
      ((2 * p.1 ^ 2 * (2 - p.1) / (1 + p.1) ^ 4) ^ 2 * (Spaces.w p.1) ^ 2)
        * ((Spaces.Gam α p.2 / Spaces.c α) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))) Pz7 :=
    hA2int.mul_prod hB2int
  have hZ72 : Integrable (fun p : ℝ × ℝ => (Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2) Pz7 := by
    refine (hProd.const_mul ((C0 f) ^ 2)).congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Pi.mul_apply]
    rw [Z7, Weta]
    ring
  have hZ72val : (∫ p, (Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pz7)
      = (C0 f) ^ 2 * (∫ θ in Spaces.Iθ,
            (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          * (∫ z in Spaces.Iz, (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4) ^ 2 * (Spaces.w z) ^ 2) := by
    have hcongr : (∫ p, (Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pz7)
        = ∫ p, (C0 f) ^ 2 * (((2 * p.1 ^ 2 * (2 - p.1) / (1 + p.1) ^ 4) ^ 2
              * (Spaces.w p.1) ^ 2)
            * ((Spaces.Gam α p.2 / Spaces.c α) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)))
            ∂Pz7 :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by
        simp only [Z7, Weta]; ring))
    rw [hcongr, MeasureTheory.integral_const_mul, MeasureTheory.integral_prod _ hProd]
    have hinner : ∀ z : ℝ, (∫ θ, ((2 * z ^ 2 * (2 - z) / (1 + z) ^ 4) ^ 2 * (Spaces.w z) ^ 2)
          * ((Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          ∂(volume.restrict Spaces.Iθ))
        = ((2 * z ^ 2 * (2 - z) / (1 + z) ^ 4) ^ 2 * (Spaces.w z) ^ 2)
          * (∫ θ in Spaces.Iθ,
              (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
      intro z
      rw [MeasureTheory.integral_const_mul]
    simp_rw [hinner]
    rw [show (∫ z, ((2 * z ^ 2 * (2 - z) / (1 + z) ^ 4) ^ 2 * (Spaces.w z) ^ 2)
          * (∫ θ in Spaces.Iθ,
              (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          ∂(volume.restrict Spaces.Iz))
        = (∫ θ in Spaces.Iθ,
              (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          * (∫ z, (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4) ^ 2 * (Spaces.w z) ^ 2
              ∂(volume.restrict Spaces.Iz)) from by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))]
    ring
  -- ## A.e. strong measurability of the integrand
  have hae1 : ∀ᵐ p ∂Pz7, p.1 ∈ Spaces.Iz := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => p.1 ∈ Spaces.Iz)
      (measurableSet_Ici.preimage measurable_fst)]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact Filter.Eventually.of_forall (fun _ => hz)
  have hLf : Integrable (fun p : ℝ × ℝ => L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) Pz7 := by
    rw [← hvol]; exact hi.intL
  have hF2 : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) Pz7 := by
    rw [← hvol]; exact f_sq_w_sq_integrable α f hi
  have hnum : AEStronglyMeasurable
      (fun p : ℝ × ℝ => f p.1 p.2 * Spaces.Dz f p.1 p.2 * Spaces.w p.1 ^ 2) Pz7 := by
    have h3 : Measurable (fun p : ℝ × ℝ => 1 - 2 / (1 + p.1)) := by fun_prop
    have h4 := h3.aestronglyMeasurable.mul hF2.aestronglyMeasurable
    refine (hLf.aestronglyMeasurable.sub h4).congr (Filter.Eventually.of_forall (fun p => ?_))
    show L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
        - (1 - 2 / (1 + p.1)) * (f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2)
      = f p.1 p.2 * Spaces.Dz f p.1 p.2 * Spaces.w p.1 ^ 2
    simp only [L]
    ring
  have hZW : AEStronglyMeasurable (fun p : ℝ × ℝ => Z7 α f p.1 p.2 * Weta p.1 p.2) Pz7 := by
    have h1 : Measurable (fun p : ℝ × ℝ => (Spaces.Gam α p.2 / Spaces.c α) * C0 f
        * (2 * p.1 ^ 2 * (2 - p.1) / (1 + p.1) ^ 4)) := by
      unfold Spaces.Gam; fun_prop
    have h2 : Measurable (fun p : ℝ × ℝ => Weta p.1 p.2) := by
      unfold Weta Spaces.w; fun_prop
    refine (h1.aestronglyMeasurable.mul h2.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Pi.mul_apply, Z7]
  have hFmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Z7 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) Pz7 := by
    by_cases hC0z : C0 f = 0
    · have hzero : (fun p : ℝ × ℝ =>
          Z7 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) = fun _ => (0 : ℝ) := by
        funext p
        simp only [Z7]
        rw [hC0z]
        ring
      rw [hzero]
      exact aestronglyMeasurable_const
    · have hmeasGam : Measurable (fun θ : ℝ => Spaces.Gam α θ) := by
        unfold Spaces.Gam; fun_prop
      have haeGam : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), Spaces.Gam α θ ≠ 0 := by
        have hnull : (volume : Measure ℝ) ({0, π / 2} : Set ℝ) = 0 := by
          rw [show ({0, π / 2} : Set ℝ) = {0} ∪ {π / 2} by ext x; simp [or_comm]]
          exact measure_union_null (measure_singleton 0) (measure_singleton (π / 2))
        have hsub : {θ : ℝ | Spaces.Gam α θ = 0} ∩ Spaces.Iθ ⊆ ({0, π / 2} : Set ℝ) := by
          intro θ hθ
          obtain ⟨hGam, hI⟩ := hθ
          by_contra hne
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
          obtain ⟨hne0, hne2⟩ := hne
          have hlt : 0 < θ := lt_of_le_of_ne hI.1 (Ne.symm hne0)
          have hlt2 : θ < π / 2 := lt_of_le_of_ne hI.2 hne2
          have hs : 0 < Real.sin θ :=
            Real.sin_pos_of_pos_of_lt_pi hlt (by linarith [hlt2, Real.pi_pos])
          have hc : 0 < Real.cos θ :=
            Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt2⟩
          unfold Spaces.Gam at hGam
          exact absurd hGam (ne_of_gt (Real.rpow_pos_of_pos (mul_pos hs (pow_pos hc 2)) _))
        rw [MeasureTheory.ae_iff]
        rw [show {θ : ℝ | ¬ Spaces.Gam α θ ≠ 0} = {θ : ℝ | Spaces.Gam α θ = 0} by
          ext θ; simp]
        rw [MeasureTheory.Measure.restrict_apply (by measurability)]
        exact measure_mono_null (fun x hx => hsub hx) hnull
      have haeZ : ∀ᵐ p ∂Pz7, Spaces.Gam α p.2 / Spaces.c α ≠ 0 := by
        have hset : MeasurableSet {p : ℝ × ℝ | Spaces.Gam α p.2 / Spaces.c α ≠ 0} :=
          ((hmeasGam.comp measurable_snd).div_const (Spaces.c α))
            (measurableSet_singleton 0).compl
        rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
          (p := fun p : ℝ × ℝ => Spaces.Gam α p.2 / Spaces.c α ≠ 0) hset]
        filter_upwards with z
        filter_upwards [haeGam] with θ hθ
        exact div_ne_zero hθ (c_ne_zero hα hα1)
      have haez1 : ∀ᵐ z ∂(volume.restrict Spaces.Iz), 2 * z ^ 2 / (1 + z) ^ 3 ≠ 0 := by
        filter_upwards [ae_w_ne_zero7, MeasureTheory.ae_restrict_mem measurableSet_Ici]
          with z hz hzI
        have hzI' : (0 : ℝ) ≤ z := hzI
        have hz0 : z ≠ 0 := fun h => hz (by rw [h]; simp [Spaces.w])
        have h1 : 0 < (1 : ℝ) + z := by linarith
        exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz0))
          (pow_ne_zero 3 (ne_of_gt h1))
      have haez : ∀ᵐ p ∂Pz7, 2 * p.1 ^ 2 / (1 + p.1) ^ 3 ≠ 0 := by
        have hset : MeasurableSet {p : ℝ × ℝ | 2 * p.1 ^ 2 / (1 + p.1) ^ 3 ≠ 0} :=
          (by fun_prop : Measurable (fun p : ℝ × ℝ => 2 * p.1 ^ 2 / (1 + p.1) ^ 3))
            (measurableSet_singleton 0).compl
        rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
          (p := fun p : ℝ × ℝ => 2 * p.1 ^ 2 / (1 + p.1) ^ 3 ≠ 0) hset]
        filter_upwards [haez1] with z hz
        exact Filter.Eventually.of_forall (fun θ => hz)
      have haeCoef : ∀ᵐ p ∂Pz7,
          (Spaces.Gam α p.2 / Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * C0 f ≠ 0 := by
        filter_upwards [haeZ, haez] with p h1 h2
        exact mul_ne_zero (mul_ne_zero h1 h2) hC0z
      -- `f * w²` is a.e. strongly measurable, via `intT` and `intP`
      have hT : Integrable (fun p : ℝ × ℝ =>
          Transport f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) Pz7 := by
        rw [← hvol]; exact hi.intT
      have hP : Integrable (fun p : ℝ × ℝ =>
          Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) Pz7 := by
        rw [← hvol]; exact hi.intP
      have hdiff : Integrable (fun p : ℝ × ℝ =>
          (Spaces.Gam α p.2 / Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * C0 f
            * (f p.1 p.2 * Spaces.w p.1 ^ 2)) Pz7 := by
        refine (hT.sub hP).congr (Filter.Eventually.of_forall (fun p => ?_))
        simp only [Pi.sub_apply, Proj, C0, Transport]
        ring
      have hfw2 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 * Spaces.w p.1 ^ 2) Pz7 := by
        have hcoef : Measurable (fun p : ℝ × ℝ =>
            ((Spaces.Gam α p.2 / Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * C0 f)⁻¹) := by
          refine Measurable.inv ?_
          unfold Spaces.Gam; fun_prop
        refine (hdiff.aestronglyMeasurable.mul hcoef.aestronglyMeasurable).congr ?_
        filter_upwards [haeCoef] with p hp
        simp only [Pi.mul_apply]
        calc (Spaces.Gam α p.2 / Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * C0 f
              * (f p.1 p.2 * Spaces.w p.1 ^ 2)
              * ((Spaces.Gam α p.2 / Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * C0 f)⁻¹
            = (f p.1 p.2 * Spaces.w p.1 ^ 2)
              * (((Spaces.Gam α p.2 / Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * C0 f)
                * ((Spaces.Gam α p.2 / Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * C0 f)⁻¹) := by
              ring_nf
          _ = (f p.1 p.2 * Spaces.w p.1 ^ 2) * 1 := by rw [mul_inv_cancel₀ hp]
          _ = f p.1 p.2 * Spaces.w p.1 ^ 2 := by rw [mul_one]
      have hinv_meas : Measurable (fun x : ℝ => x⁻¹) := Measurable.inv measurable_id
      have hDz0 := Dz_zero_ae_on_zero_set7 α f hi
      have hDz : AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2) Pz7 := by
        have hfw2inv : AEStronglyMeasurable (fun p : ℝ × ℝ =>
            (f p.1 p.2 * Spaces.w p.1 ^ 2)⁻¹) Pz7 :=
          (hinv_meas.comp_aemeasurable hfw2.aemeasurable).aestronglyMeasurable
        have hH : AEStronglyMeasurable (fun p : ℝ × ℝ =>
            (f p.1 p.2 * Spaces.Dz f p.1 p.2 * Spaces.w p.1 ^ 2)
              * (f p.1 p.2 * Spaces.w p.1 ^ 2)⁻¹) Pz7 := hnum.mul hfw2inv
        refine hH.congr ?_
        filter_upwards [hDz0, hae1] with p hp hz
        by_cases hd : f p.1 p.2 * Spaces.w p.1 ^ 2 = 0
        · rw [hd, inv_zero, mul_zero]
          rcases mul_eq_zero.mp hd with hf0 | hw0
          · exact (hp hf0).symm
          · have hz0 : p.1 = 0 := by
              by_contra hne
              exact (pow_ne_zero 2 (w_ne_zero_of_pos7 (lt_of_le_of_ne hz (Ne.symm hne)))) hw0
            rw [hz0]; simp [Spaces.Dz]
        · rw [show f p.1 p.2 * Spaces.Dz f p.1 p.2 * Spaces.w p.1 ^ 2
              = (f p.1 p.2 * Spaces.w p.1 ^ 2) * Spaces.Dz f p.1 p.2 from by ring]
          calc (f p.1 p.2 * Spaces.w p.1 ^ 2) * Spaces.Dz f p.1 p.2
                * (f p.1 p.2 * Spaces.w p.1 ^ 2)⁻¹
              = Spaces.Dz f p.1 p.2 * ((f p.1 p.2 * Spaces.w p.1 ^ 2)
                  * (f p.1 p.2 * Spaces.w p.1 ^ 2)⁻¹) := by ring_nf
            _ = Spaces.Dz f p.1 p.2 * 1 := by rw [mul_inv_cancel₀ hd]
            _ = Spaces.Dz f p.1 p.2 := by rw [mul_one]
      exact (hZW.mul hDz).congr (Filter.Eventually.of_forall (fun p => by
        simp only [Pi.mul_apply]; ring))
  -- ## Integrability and the lower bound
  have hDz2 : Integrable (fun p : ℝ × ℝ => (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) Pz7 :=
    integrable_Dz_sq_Weta7 α f hi
  have hdom : Integrable (fun p : ℝ × ℝ =>
      (1 / 32) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2)
        + 8 * ((Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2)) Pz7 :=
    (hDz2.const_mul (1 / 32)).add (hZ72.const_mul 8)
  have hFint : Integrable
      (fun p : ℝ × ℝ => Z7 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) Pz7 := by
    refine hdom.mono' hFmeas ?_
    filter_upwards [ae_snd_mem_Iθ7] with p hp
    rw [Real.norm_eq_abs]
    exact Z7_pointwise α f hp
  have hneg : Integrable (fun p : ℝ × ℝ =>
      -((1 / 32) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2))
        - 8 * ((Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2)) Pz7 :=
    (((hDz2.const_mul (1 / 32)).add (hZ72.const_mul 8)).neg).congr
      (Filter.Eventually.of_forall (fun p => by
        simp only [Pi.add_apply, Pi.neg_apply]; ring))
  have hbound : ∀ᵐ p ∂Pz7,
      -((1 / 32) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2))
        - 8 * ((Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2)
      ≤ Z7 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 := by
    filter_upwards [ae_snd_mem_Iθ7] with p hp
    have h := Z7_pointwise α f hp (z := p.1)
    have h2 := (abs_le.mp h).1
    linarith [h2]
  have hmono : (∫ p, -((1 / 32) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2))
        - 8 * ((Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2) ∂Pz7)
      ≤ ∫ p, Z7 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂Pz7 :=
    integral_mono_ae hneg hFint hbound
  have hval_neg : (∫ p, -((1 / 32) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2))
        - 8 * ((Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2) ∂Pz7)
      = -((1 / 32) * ∫ p, (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pz7)
        - 8 * ∫ p, (Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pz7 := by
    rw [show (∫ p, -((1 / 32) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2))
          - 8 * ((Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2) ∂Pz7)
        = ∫ p, -(((1 / 32) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2))
          + 8 * ((Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2)) ∂Pz7 from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))]
    rw [MeasureTheory.integral_neg,
      MeasureTheory.integral_add (hDz2.const_mul (1 / 32)) (hZ72.const_mul 8),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    ring
  have hEDzP : (∫ p, (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pz7) = EDz f := by
    have hOn2 : IntegrableOn (Function.uncurry (fun z θ =>
        Spaces.Dz f z θ * Spaces.Dz f z θ * Weta z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) := by
      rw [IntegrableOn, hvol]
      exact hDz2.congr (Filter.Eventually.of_forall (fun p => by
        show Spaces.Dz f p.1 p.2 ^ 2 * Weta p.1 p.2
            = Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2
        ring))
    have hwip : wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        (Spaces.Dz f) (Spaces.Dz f)
        = ∫ p, Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂Pz7 :=
      wip_eq_integral_prod Weta (Spaces.Dz f) (Spaces.Dz f) hOn2
    rw [EDz_eq_wip f, hwip]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))
  have hZ7P : (∫ p, (Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pz7) ≤ 18900 * (C0 f) ^ 2 := by
    rw [hZ72val, hA2val]
    calc (C0 f) ^ 2 * (∫ θ in Spaces.Iθ,
            (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) * 4
        = (C0 f) ^ 2 * 4 * (∫ θ in Spaces.Iθ,
            (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by ring
      _ ≤ (C0 f) ^ 2 * 4 * 4725 := by
          refine mul_le_mul_of_nonneg_left hB2val ?_
          positivity
      _ = 18900 * (C0 f) ^ 2 := by ring
  have hOn : IntegrableOn
      (Function.uncurry (fun z θ => Z7 α f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [IntegrableOn, hvol]
    exact hFint
  refine ⟨hOn, ?_⟩
  rw [wip_eq_integral_prod Weta (Z7 α f) (Spaces.Dz f) hOn]
  have hkey : 8 * (∫ p, (Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pz7) ≤ 10 ^ 7 * Ef f := by
    nlinarith [hZ7P, hC0]
  calc -((1 / 32) * EDz f + 10 ^ 7 * Ef f)
      = -((1 / 32) * EDz f) - 10 ^ 7 * Ef f := by ring
    _ ≤ -((1 / 32) * ∫ p, (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pz7)
          - 8 * ∫ p, (Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pz7 := by
        rw [hEDzP]; linarith [hkey]
    _ = (∫ p, -((1 / 32) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2))
          - 8 * ((Z7 α f p.1 p.2) ^ 2 * Weta p.1 p.2) ∂Pz7) := hval_neg.symm
    _ ≤ ∫ p, Z7 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂Pz7 := hmono

end Work.Coercivity
