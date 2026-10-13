/-
# A self-contained, namespaced copy of the `Z₃` bound of `zZ3.lean`

`Submission/Work/Coercivity/zZ3.lean` proves the `Z₃`-bound

  `(Z₃ f, D_z f)_{w²sin^{-η}} ≥ -((1/32)·E_{z}(f) + 10⁶·|fw|²)`

used by the `D_z`-coercivity estimate of `𝓛_Γ^T`.  That file cannot be imported here:

* it does not even build on its own, because it imports `L2CoercivityTransportEta`, which
  declares `Work.Coercivity.aesm_L12f`, a name `zZ3.lean` re-declares; and
* its helper names `Pzθ` and `measurable_w` collide with the ones declared in
  `bound_Z5.lean` and `T4aux.lean`, which the `D_z`-estimate needs as well.

This file is a verbatim copy of `zZ3.lean` placed inside the fresh namespace
`Work.Coercivity.Z3Clean`, which resolves both problems: the locally declared
`aesm_L12f`, `Pzθ`, `measurable_w` and every other helper now live under
`Work.Coercivity.Z3Clean`, while all references to the surrounding theory (`Z3`, `Weta`,
`wip`, `Ef`, `EDz`, …) still resolve to the shared `Work.Coercivity` names.  The result is
used, as `Z3Clean.Z3_bound`, in `FirstDerivativeCoercivity.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.angular_avg_w_sq_le
import Submission.Work.Coercivity.f_sq_w_sq_integrable
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.Coercivity.EDz_eq_wip
import Submission.Work.Coercivity.zero_set_deriv_countable
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.c_bounds
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

namespace Z3Clean

set_option autoImplicit false

abbrev Pzθ : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)

/-- The radial weight `w` does not vanish at any `z > 0`. -/
lemma w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Spaces.w z ≠ 0 := by
  have h1 : (1 + z) ≠ 0 := by linarith
  simp only [Spaces.w]
  exact div_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 (ne_of_gt hz))

/-- The radial weight `w` is measurable. -/
lemma measurable_w : Measurable (fun z : ℝ => Spaces.w z) := by
  show Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
  fun_prop

/-- On `Iz` the radial weight `w` vanishes only at `z = 0`, hence almost everywhere. -/
lemma ae_w_ne_zero : ∀ᵐ z ∂(volume.restrict Spaces.Iz), Spaces.w z ≠ 0 := by
  have hsub : {z : ℝ | Spaces.w z = 0} ∩ Set.Ici 0 ⊆ ({0} : Set ℝ) := by
    intro z hz
    obtain ⟨hz0, hzI⟩ := hz
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact w_ne_zero_of_pos (lt_of_le_of_ne hzI (Ne.symm hne)) hz0
  rw [MeasureTheory.ae_iff]
  rw [show {z : ℝ | ¬ Spaces.w z ≠ 0} = {z : ℝ | Spaces.w z = 0} by ext z; simp]
  change (volume.restrict (Set.Ici 0)) {z : ℝ | Spaces.w z = 0} = 0
  rw [MeasureTheory.Measure.restrict_apply
    (show MeasurableSet {z : ℝ | Spaces.w z = 0} from
      measurable_w (measurableSet_singleton 0))]
  exact measure_mono_null hsub (measure_singleton 0)

/-- The radial weight does not vanish almost everywhere on the quadrant. -/
lemma ae_w_ne_zero_prod : ∀ᵐ p ∂Pzθ, Spaces.w p.1 ≠ 0 := by
  have hset : MeasurableSet {p : ℝ × ℝ | Spaces.w p.1 ≠ 0} :=
    (measurable_w.comp measurable_fst) (measurableSet_singleton 0).compl
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
    (p := fun p : ℝ × ℝ => Spaces.w p.1 ≠ 0) hset]
  filter_upwards [ae_w_ne_zero] with z hz
  exact Filter.Eventually.of_forall fun _ => hz

/-- `f²` is a.e. strongly measurable on the quadrant, under `CoerciveData`. -/
lemma aesm_f_sq_Z3 (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 ^ 2) Pzθ := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) = Pzθ := by
    rw [Pzθ, MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  have h1 : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) Pzθ := by
    rw [← hvol]
    exact f_sq_w_sq_integrable α f hi
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.w p.1 ^ 2)⁻¹) Pzθ := by
    apply Measurable.aestronglyMeasurable
    show Measurable (fun p : ℝ × ℝ => (((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2)⁻¹)
    fun_prop
  have h3 := h1.aestronglyMeasurable.mul h2
  refine h3.congr ?_
  filter_upwards [ae_w_ne_zero_prod] with p hp
  rw [Pi.mul_apply]
  have hw2 : Spaces.w p.1 ^ 2 ≠ 0 := pow_ne_zero 2 hp
  field_simp

/-- `{p | f p.1 p.2 = 0}` is null measurable on the quadrant, under `CoerciveData`. -/
lemma nullMeasurableSet_f_eq_zero (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    NullMeasurableSet {p : ℝ × ℝ | f p.1 p.2 = 0} Pzθ := by
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 ^ 2) Pzθ := aesm_f_sq_Z3 α f hi
  have h2 : NullMeasurableSet {p : ℝ × ℝ | f p.1 p.2 ^ 2 = 0} Pzθ :=
    h1.nullMeasurableSet_eq_fun aestronglyMeasurable_const
  refine h2.congr ?_
  filter_upwards with p
  exact propext (by rw [pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)])

/-- Almost every point of the quadrant has its second coordinate in `Iθ`. -/
lemma ae_snd_mem_Iθ : ∀ᵐ p ∂Pzθ, p.2 ∈ Spaces.Iθ := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => p.2 ∈ Spaces.Iθ)
    (measurableSet_Icc.preimage measurable_snd)]
  filter_upwards with x
  exact MeasureTheory.ae_restrict_mem measurableSet_Icc

/-- Almost every point of the quadrant has `sin (2 p.2) ≠ 0`. -/
lemma ae_sin_ne_zero_Pzθ : ∀ᵐ p ∂Pzθ, Real.sin (2 * p.2) ≠ 0 :=
  MeasureTheory.ae_mono (by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self
      MeasureTheory.Measure.restrict_le_self) ae_sin_two_ne_zero

/-- Almost every point of the quadrant has `sin (2 p.2) > 0`. -/
lemma ae_sin_pos_Pzθ : ∀ᵐ p ∂Pzθ, 0 < Real.sin (2 * p.2) := by
  filter_upwards [ae_snd_mem_Iθ, ae_sin_ne_zero_Pzθ] with p hp hne
  exact lt_of_le_of_ne
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hp.1], by linarith [hp.2, Real.pi_pos]⟩)
    (Ne.symm hne)

/-- `(Dz f)² * Weta` is integrable on the quadrant (this is `intDz` up to rewriting). -/
lemma integrable_Dz_sq_Weta (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    Integrable (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 ^ 2 * Weta p.1 p.2) Pzθ := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) = Pzθ := by
    rw [Pzθ, MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  rw [← hvol]
  refine hi.intDz.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.uncurry, Weta]
  ring

/-- `(Dz f)² * w²` is integrable on the quadrant. -/
lemma integrable_Dz_sq_w_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    Integrable (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 ^ 2 * Spaces.w p.1 ^ 2) Pzθ := by
  have hW := integrable_Dz_sq_Weta α f hi
  have hsin : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Spaces.eta)) := by fun_prop
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 ^ 2 * Spaces.w p.1 ^ 2) Pzθ := by
    refine (hW.aestronglyMeasurable.mul hsin.aestronglyMeasurable).congr ?_
    filter_upwards [ae_sin_pos_Pzθ] with p hp
    have hs : (Real.sin (2 * p.2)) ^ (-Spaces.eta) * (Real.sin (2 * p.2)) ^ (Spaces.eta) = 1 := by
      rw [← Real.rpow_add hp, neg_add_cancel, Real.rpow_zero]
    have hs' : (Real.sin (2 * p.2)) ^ (Spaces.eta)
        = ((Real.sin (2 * p.2)) ^ (-Spaces.eta))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hp), inv_inv]
    simp only [Pi.mul_apply, Weta, hs']
    have hne : (Real.sin (2 * p.2)) ^ (-Spaces.eta) ≠ 0 := by positivity
    field_simp
  refine hW.mono' haesm ?_
  filter_upwards [ae_sin_pos_Pzθ] with p hp
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

/-- `(Dz f)²` is a.e. strongly measurable on the quadrant. -/
lemma aesm_Dz_sq_Z3 (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 ^ 2) Pzθ := by
  have h1 := (integrable_Dz_sq_w_sq α f hi).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.w p.1 ^ 2)⁻¹) Pzθ := by
    apply Measurable.aestronglyMeasurable
    show Measurable (fun p : ℝ × ℝ => (((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2)⁻¹)
    fun_prop
  refine (h1.mul h2).congr ?_
  filter_upwards [ae_w_ne_zero_prod] with p hp
  rw [Pi.mul_apply]
  have hw2 : Spaces.w p.1 ^ 2 ≠ 0 := pow_ne_zero 2 hp
  field_simp

/-- The auxiliary function whose vanishing encodes that `Dz f` vanishes where `f` does. -/
private def Z3Ppsi (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ENNReal :=
  fun p => ENNReal.ofReal (Spaces.Dz f p.1 p.2 ^ 2)
    * Set.indicator {q : ℝ × ℝ | f q.1 q.2 = 0} (fun _ => (1 : ENNReal)) p

/-- Under `CoerciveData`, `Dz f` vanishes almost everywhere on the zero set of `f`. -/
lemma Dz_zero_ae_on_zero_set (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    ∀ᵐ p ∂Pzθ, f p.1 p.2 = 0 → Spaces.Dz f p.1 p.2 = 0 := by
  have hψ : AEMeasurable (Z3Ppsi f) Pzθ := by
    have hA : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Spaces.Dz f p.1 p.2 ^ 2)) Pzθ :=
      ENNReal.measurable_ofReal.comp_aemeasurable (aesm_Dz_sq_Z3 α f hi).aemeasurable
    have hB : AEMeasurable (fun p : ℝ × ℝ =>
        Set.indicator {q : ℝ × ℝ | f q.1 q.2 = 0} (fun _ => (1 : ENNReal)) p) Pzθ :=
      AEMeasurable.indicator₀ (f := fun _ : ℝ × ℝ => (1 : ENNReal))
        (s := {q : ℝ × ℝ | f q.1 q.2 = 0}) aemeasurable_const
        (nullMeasurableSet_f_eq_zero α f hi)
    exact hA.mul hB
  have hslice : ∀ θ : ℝ, ∫⁻ z, Z3Ppsi f (z, θ) ∂(volume.restrict Spaces.Iz) = 0 := by
    intro θ
    have hsub : {z : ℝ | Z3Ppsi f (z, θ) ≠ 0}
        ⊆ {z : ℝ | f z θ = 0 ∧ deriv (fun u => f u θ) z ≠ 0} := by
      intro z hz
      simp only [Set.mem_ofPred_eq]
      have h1 : ENNReal.ofReal (Spaces.Dz f z θ ^ 2) ≠ 0 := by
        intro hc
        exact hz (by simp only [Z3Ppsi, hc, zero_mul])
      have h2 : Set.indicator {q : ℝ × ℝ | f q.1 q.2 = 0}
          (fun _ => (1 : ENNReal)) (z, θ) ≠ 0 := by
        intro hc
        exact hz (by simp only [Z3Ppsi, hc, mul_zero])
      have h3 : (z, θ) ∈ {q : ℝ × ℝ | f q.1 q.2 = 0} := by
        by_contra hc
        rw [Set.indicator_of_notMem hc] at h2
        exact h2 rfl
      refine ⟨h3, fun hd => ?_⟩
      have hDz : Spaces.Dz f z θ ≠ 0 := fun hc => h1 (by rw [hc]; simp)
      exact hDz (by rw [Spaces.Dz, Spaces.pz, hd, mul_zero])
    have hcount : ({z : ℝ | f z θ = 0 ∧ deriv (fun u => f u θ) z ≠ 0}).Countable :=
      zero_set_deriv_countable (fun u => f u θ)
    have h0 : (volume.restrict Spaces.Iz) {z : ℝ | Z3Ppsi f (z, θ) ≠ 0} = 0 :=
      measure_mono_null hsub (Set.Countable.measure_zero hcount _)
    rw [MeasureTheory.lintegral_congr_ae ((MeasureTheory.ae_iff).mpr h0),
      MeasureTheory.lintegral_zero]
  have hsum : ∫⁻ p, Z3Ppsi f p ∂Pzθ = 0 := by
    rw [MeasureTheory.lintegral_prod_symm (Z3Ppsi f) hψ]
    rw [show (∫⁻ θ, ∫⁻ z, Z3Ppsi f (z, θ) ∂(volume.restrict Spaces.Iz)
          ∂(volume.restrict Spaces.Iθ))
        = ∫⁻ _θ, (0 : ENNReal) ∂(volume.restrict Spaces.Iθ) from
      MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun θ => hslice θ),
      MeasureTheory.lintegral_zero]
  have hz0 : Z3Ppsi f =ᵐ[Pzθ] 0 := (MeasureTheory.lintegral_eq_zero_iff' hψ).mp hsum
  filter_upwards [hz0] with p hp hf
  have h1 : ENNReal.ofReal (Spaces.Dz f p.1 p.2 ^ 2)
      * Set.indicator {q : ℝ × ℝ | f q.1 q.2 = 0} (fun _ => (1 : ENNReal)) p = 0 := by
    simpa only [Z3Ppsi, Pi.zero_apply] using hp
  rw [Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | f q.1 q.2 = 0} from hf), mul_one] at h1
  exact sq_eq_zero_iff.mp
    (le_antisymm (ENNReal.ofReal_eq_zero.mp h1) (sq_nonneg _))

/-- The radial coefficient `(w/z) L₁₂(f)` multiplying the angular weight `K` in `intK`. -/
private def zcoef (f : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z => Spaces.w z / z * L12f f z

/-- Almost everywhere strong measurability transfers from `(0,∞)` to `Iz`. -/
lemma aesm_of_continuousOn_Ioi {g : ℝ → ℝ} (h : ContinuousOn g (Set.Ioi 0)) :
    AEStronglyMeasurable g (volume.restrict Spaces.Iz) := by
  have h1 : AEStronglyMeasurable g (volume.restrict (Set.Ioi 0)) :=
    h.aestronglyMeasurable measurableSet_Ioi
  rw [show Spaces.Iz = Set.Ici 0 from rfl,
    ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  exact h1

/-- Quotients of real-valued a.e. strongly measurable functions are a.e. strongly measurable. -/
lemma aesm_div {g₁ g₂ : ℝ × ℝ → ℝ} (h₁ : AEStronglyMeasurable g₁ Pzθ)
    (h₂ : AEStronglyMeasurable g₂ Pzθ) :
    AEStronglyMeasurable (fun p => g₁ p / g₂ p) Pzθ := by
  rw [aestronglyMeasurable_iff_aemeasurable] at h₁ h₂ ⊢
  have h := h₁.mul h₂.inv
  have heq : (fun p => g₁ p / g₂ p) = g₁ * g₂⁻¹ := by
    funext p
    rw [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
  rw [heq]
  exact h

/-- `L₁₂(f)` is differentiable (hence continuous) on `(0,∞)`. -/
lemma hasDerivAt_L12f (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (L12f f) (-(FM.L12dens Spaces.K f z)) z :=
  FM.hasDerivAt_L12 (K := Spaces.K) (f := f) (a := 0) (ρ := z)
    hfH.hint (hfH.hcont z hz) hz

/-- `L₁₂(f)` is a.e. strongly measurable on `Iz`. -/
lemma aesm_L12f (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    AEStronglyMeasurable (fun z => L12f f z) (volume.restrict Spaces.Iz) :=
  aesm_of_continuousOn_Ioi fun z hz => (hasDerivAt_L12f f hfH hz).continuousAt.continuousWithinAt

/-- `z ↦ (w z / z) L₁₂(f)(z)` is a.e. strongly measurable on `Iz`. -/
lemma aesm_zcoef (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    AEStronglyMeasurable (zcoef f) (volume.restrict Spaces.Iz) := by
  have hw : AEStronglyMeasurable (fun z : ℝ => Spaces.w z / z) (volume.restrict Spaces.Iz) := by
    apply aesm_of_continuousOn_Ioi
    have h : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2 / z) (Set.Ioi 0) := by
      apply ContinuousOn.div
      · exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
          (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
      · exact continuousOn_id
      · intro z hz; exact ne_of_gt hz
    simpa only [Spaces.w] using h
  exact hw.mul (aesm_L12f f hfH)

/-- The angular average `z ↦ ∫ θ, K θ f z θ` is a.e. strongly measurable on `Iz`. -/
lemma aesm_Kavg (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    AEStronglyMeasurable (fun z => Kavg f z) (volume.restrict Spaces.Iz) := by
  have hcont : ContinuousOn (fun z : ℝ => FM.L12dens Spaces.K f z) (Set.Ioi 0) :=
    fun z hz => (hfH.hcont z hz).continuousWithinAt
  have h1 : ContinuousOn (fun z : ℝ => z * FM.L12dens Spaces.K f z) (Set.Ioi 0) :=
    continuousOn_id.mul hcont
  refine aesm_of_continuousOn_Ioi (h1.congr ?_)
  intro z hz
  exact integral_K_mul_eq_mul_L12dens f hz

/-- On `(0,∞)`, `Kavg f z = -z ∂_z L₁₂(f)(z)`. -/
lemma Kavg_eq (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) {z : ℝ} (hz : 0 < z) :
    Kavg f z = -(z * deriv (L12f f) z) := by
  have h1 : Kavg f z = z * FM.L12dens Spaces.K f z := integral_K_mul_eq_mul_L12dens f hz
  rw [h1, (hasDerivAt_L12f f hfH hz).deriv]
  ring

/-- A.e. on `Iz`, if `(w/z) L₁₂(f)(z) = 0` then `Kavg f z = 0`. -/
lemma Kavg_zero_ae_of_zcoef_zero (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    ∀ᵐ z ∂(volume.restrict Spaces.Iz), zcoef f z = 0 → Kavg f z = 0 := by
  have hcount : ({z : ℝ | L12f f z = 0 ∧ deriv (L12f f) z ≠ 0}).Countable :=
    zero_set_deriv_countable (L12f f)
  have h0 : (volume.restrict Spaces.Iz) {z : ℝ | L12f f z = 0 ∧ deriv (L12f f) z ≠ 0} = 0 :=
    Set.Countable.measure_zero hcount _
  have hderivae : ∀ᵐ z ∂(volume.restrict Spaces.Iz),
      ¬(L12f f z = 0 ∧ deriv (L12f f) z ≠ 0) := by
    rw [MeasureTheory.ae_iff]; simpa using h0
  filter_upwards [ae_w_ne_zero, hderivae,
    MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hw hderiv hzI hzcoef
  have hzpos : 0 < z := lt_of_le_of_ne hzI (by rintro rfl; simp [Spaces.w] at hw)
  have hL : L12f f z = 0 := by
    rcases mul_eq_zero.mp hzcoef with h | h
    · exact absurd h (div_ne_zero hw (ne_of_gt hzpos))
    · exact h
  have hd : deriv (L12f f) z = 0 := by
    by_contra hc; exact hderiv ⟨hL, hc⟩
  rw [Kavg_eq f hfH hzpos, hd, mul_zero, neg_zero]

/-- The `intL` integrand is integrable for the product measure. -/
lemma integrable_L_f_w_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    Integrable (fun p : ℝ × ℝ => L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) Pzθ := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) = Pzθ := by
    rw [Pzθ, MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  rw [← hvol]
  exact hi.intL

/-- `p ↦ f p.1 p.2 * 1_{zcoef f p.1 * K p.2 ≠ 0}(p)` is a.e. strongly measurable. -/
lemma aesm_f_ind (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) (hfH : HardyHyp f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      f p.1 p.2 * Set.indicator {q : ℝ × ℝ | zcoef f q.1 * Spaces.K q.2 ≠ 0}
        (fun _ => (1 : ℝ)) p) Pzθ := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) = Pzθ := by
    rw [Pzθ, MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  have hK : Integrable (fun p : ℝ × ℝ => zcoef f p.1 * (Spaces.K p.2 * f p.1 p.2)) Pzθ := by
    rw [← hvol]
    refine hi.intK.congr (Filter.Eventually.of_forall fun p => ?_)
    show Spaces.w p.1 / p.1 * L12f f p.1 * (Spaces.K p.2 * f p.1 p.2)
      = zcoef f p.1 * (Spaces.K p.2 * f p.1 p.2)
    rw [zcoef]
  have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ => zcoef f p.1 * Spaces.K p.2) Pzθ :=
    (aesm_zcoef f hfH).comp_fst.mul
      ((K_facts_continuous.measurable.comp measurable_snd).aestronglyMeasurable)
  have hdiv : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (zcoef f p.1 * Spaces.K p.2)⁻¹) Pzθ := by
    have h := aesm_div (g₁ := fun _ : ℝ × ℝ => (1 : ℝ)) (g₂ := fun p : ℝ × ℝ =>
      zcoef f p.1 * Spaces.K p.2) aestronglyMeasurable_const hprod
    simpa only [Pi.div_apply, one_div] using h
  refine (hK.aestronglyMeasurable.mul hdiv).congr ?_
  filter_upwards with p
  by_cases h : zcoef f p.1 * Spaces.K p.2 = 0
  · have hmem : p ∉ {q : ℝ × ℝ | zcoef f q.1 * Spaces.K q.2 ≠ 0} := by
      intro hh; exact hh h
    rw [Pi.mul_apply, Set.indicator_of_notMem hmem, mul_zero]
    rw [show zcoef f p.1 * (Spaces.K p.2 * f p.1 p.2)
        * (zcoef f p.1 * Spaces.K p.2)⁻¹ = 0 from by
      rw [← mul_assoc, h, zero_mul, zero_mul]]
  · have hmem : p ∈ {q : ℝ × ℝ | zcoef f q.1 * Spaces.K q.2 ≠ 0} := h
    rw [Pi.mul_apply, Set.indicator_of_mem hmem, mul_one]
    rw [show zcoef f p.1 * (Spaces.K p.2 * f p.1 p.2)
        * (zcoef f p.1 * Spaces.K p.2)⁻¹
        = f p.1 p.2 * ((zcoef f p.1 * Spaces.K p.2) * (zcoef f p.1 * Spaces.K p.2)⁻¹) from by
          ring,
      mul_inv_cancel₀ h, mul_one]


/-- The auxiliary `g = L f · w²`, divided by the (a.e. nonvanishing) `f · w²`. -/
lemma aesm_g (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) (hfH : HardyHyp f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2)
        / (f p.1 p.2 * Set.indicator {q : ℝ × ℝ | zcoef f q.1 * Spaces.K q.2 ≠ 0}
            (fun _ => (1 : ℝ)) p * Spaces.w p.1 ^ 2)) Pzθ :=
  aesm_div (integrable_L_f_w_sq α f hi).aestronglyMeasurable
    ((aesm_f_ind α f hi hfH).mul (by
      apply Measurable.aestronglyMeasurable
      show Measurable (fun p : ℝ × ℝ => (((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2))
      fun_prop))

/-- The angular integral of `sin(2θ)^{-η}` over `Iθ` is at most `189`. -/
lemma theta_rpow_integral_bound :
    (∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta)) ≤ 189 :=
  etaWeight_integral_le

/-- The integrand `(Kavg f z)² w z²` is integrable and bounded by `3 Ef f`. -/
lemma Kavg_sq_w_bound (α : ℝ) (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f)
    (hi : CoerciveData α f) :
    IntegrableOn (fun z => Kavg f z ^ 2 * Spaces.w z ^ 2) Spaces.Iz ∧
      (∫ z in Spaces.Iz, Kavg f z ^ 2 * Spaces.w z ^ 2) ≤ 3 * Ef f := by
  have hfw : IntegrableOn (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine (f_sq_w_sq_integrable α f hi).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry]; ring
  obtain ⟨hint, hle⟩ := angular_avg_w_sq_le f hfH hfw
  refine ⟨hint, hle.trans (le_of_eq ?_)⟩
  congr 1
  have h3 := (prod_slice_facts f hfw).2.2
  rw [Ef_eq]
  simp only [Spaces.L2Sq]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => (h3 z).symm

/-! ## The assembly of the `Z₃` bound -/

/-- Fubini for a separated integrand against `Pzθ`. -/
private lemma integral_prod_mul_Pzθ (g₁ g₂ : ℝ → ℝ) :
    ∫ p : ℝ × ℝ, g₁ p.1 * g₂ p.2 ∂Pzθ
      = (∫ z in Spaces.Iz, g₁ z) * (∫ θ in Spaces.Iθ, g₂ θ) :=
  MeasureTheory.integral_prod_mul g₁ g₂

/-- The radial part `(2z/(c(1+z)²))·(K,f)_{L²_θ}` of `Z₃`. -/
private def Z3phi (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => 2 * z / (Spaces.c α * (1 + z) ^ 2) * Kavg f z

/-- The set on which `(w/z)L₁₂(f) · K` does not vanish. -/
private def Z3S (f : ℝ → ℝ → ℝ) : Set (ℝ × ℝ) := {q | zcoef f q.1 * Spaces.K q.2 ≠ 0}

/-- `f` cut off by `Z3S`. -/
private def Z3f0 (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2 * Set.indicator (Z3S f) (fun _ => (1 : ℝ)) p

/-- `L f · w²` divided by `f · w²` (an a.e. safe representative of `L f · w²`). -/
private def Z3g (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => (L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) / (Z3f0 f p * Spaces.w p.1 ^ 2)

/-- An a.e. measurable representative of the integrand `Z₃ · D_z f · Weta`. -/
private def Z3T (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Z3phi α f p.1 * Spaces.Gam α p.2 * Spaces.w p.1 ^ 2
    * (Real.sin (2 * p.2)) ^ (-Spaces.eta)
    * Set.indicator (Z3S f) (fun _ => (1 : ℝ)) p
    * (Z3g f p - Z3f0 f p + 2 * Z3f0 f p / (1 + p.1))

private lemma Z3_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Z3 α f z θ = Z3phi α f z * Spaces.Gam α θ := by
  rw [Z3, Z3phi]; ring

private lemma nullMeasurableSet_Z3S (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    NullMeasurableSet (Z3S f) Pzθ := by
  have hprod : AEMeasurable (fun p : ℝ × ℝ => zcoef f p.1 * Spaces.K p.2) Pzθ :=
    ((aesm_zcoef f hfH).comp_fst.mul
      ((K_facts_continuous.measurable.comp measurable_snd).aestronglyMeasurable)).aemeasurable
  have h := hprod.nullMeasurableSet_preimage (s := {x : ℝ | x ≠ 0})
    (by rw [show {x : ℝ | x ≠ 0} = {0}ᶜ by ext x; simp]
        exact (measurableSet_singleton 0).compl)
  have h' : NullMeasurableSet {p : ℝ × ℝ | zcoef f p.1 * Spaces.K p.2 ≠ 0} Pzθ := h
  exact show NullMeasurableSet (Z3S f) Pzθ from h'

private lemma ae_fst_mem_Iz : ∀ᵐ p ∂Pzθ, p.1 ∈ Spaces.Iz := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => p.1 ∈ Spaces.Iz)
    (by rw [show {p : ℝ × ℝ | p.1 ∈ Spaces.Iz} = Set.Ici (0 : ℝ) ×ˢ Set.univ by
          ext p; simp [Spaces.Iz]]
        exact measurableSet_Ici.prod MeasurableSet.univ)]
  filter_upwards [MeasureTheory.ae_restrict_mem (s := Spaces.Iz)
    (show MeasurableSet (Set.Ici (0 : ℝ)) from measurableSet_Ici)] with x hx
  exact Filter.Eventually.of_forall fun _ => hx

private lemma Kavg_zero_ae_prod (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    ∀ᵐ p ∂Pzθ, zcoef f p.1 = 0 → Kavg f p.1 = 0 := by
  have hS : (volume.restrict Spaces.Iz) {z : ℝ | zcoef f z = 0 ∧ Kavg f z ≠ 0} = 0 := by
    have h := (MeasureTheory.ae_iff).mp (Kavg_zero_ae_of_zcoef_zero f hfH)
    simpa only [not_imp, ne_eq, Set.setOf_and] using h
  rw [MeasureTheory.ae_iff]
  have hset : {p : ℝ × ℝ | ¬(zcoef f p.1 = 0 → Kavg f p.1 = 0)}
      = {z : ℝ | zcoef f z = 0 ∧ Kavg f z ≠ 0} ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true, not_imp, ne_eq]
  rw [hset, MeasureTheory.Measure.prod_prod, hS, zero_mul]

private lemma five_mul_le (u v : ℝ) : 5 * u * v ≤ 400 * u ^ 2 + (1 / 64) * v ^ 2 := by
  nlinarith [sq_nonneg (20 * u - v / 8)]

private lemma sin_rpow_neg_eta_eq_sq {θ : ℝ} (h : 0 < Real.sin (2 * θ)) :
    (Real.sin (2 * θ)) ^ (-Spaces.eta) = ((Real.sin (2 * θ)) ^ (-Spaces.eta / 2)) ^ 2 := by
  rw [sq, ← Real.rpow_add h]
  norm_num

private lemma aesm_Z3T (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) (hfH : HardyHyp f) :
    AEStronglyMeasurable (Z3T α f) Pzθ := by
  have hφ : AEStronglyMeasurable (fun p : ℝ × ℝ => Z3phi α f p.1) Pzθ := by
    have h1 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => 2 * p.1 / (Spaces.c α * (1 + p.1) ^ 2)) Pzθ := by
      apply Measurable.aestronglyMeasurable; fun_prop
    exact h1.mul (aesm_Kavg f hfH).comp_fst
  have hΓ : AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.Gam α p.2) Pzθ := by
    apply Measurable.aestronglyMeasurable
    unfold Spaces.Gam; fun_prop
  have hw2 : AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.w p.1 ^ 2) Pzθ := by
    apply Measurable.aestronglyMeasurable
    show Measurable (fun p : ℝ × ℝ => (((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2))
    fun_prop
  have hsin : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Spaces.eta)) Pzθ := by
    apply Measurable.aestronglyMeasurable; fun_prop
  have hind : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Set.indicator (Z3S f) (fun _ => (1 : ℝ)) p) Pzθ :=
    (aemeasurable_const.indicator₀ (nullMeasurableSet_Z3S f hfH)).aestronglyMeasurable
  have hf0 : AEStronglyMeasurable (Z3f0 f) Pzθ := aesm_f_ind α f hi hfH
  have hg : AEStronglyMeasurable (Z3g f) Pzθ := aesm_g α f hi hfH
  have hbr : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Z3g f p - Z3f0 f p + 2 * Z3f0 f p / (1 + p.1)) Pzθ := by
    refine (hg.sub hf0).add ?_
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => 2 / (1 + p.1)) Pzθ := by
      apply Measurable.aestronglyMeasurable; fun_prop
    refine (hf0.mul h2).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring_nf
  exact ((((hφ.mul hΓ).mul hw2).mul hsin).mul hind).mul hbr

private lemma Z3T_eq_target_ae (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f)
    (hi : CoerciveData α f) :
    ∀ᵐ p ∂Pzθ,
      Z3T α f p = Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 := by
  filter_upwards [ae_fst_mem_Iz, ae_snd_mem_Iθ, Kavg_zero_ae_prod f hfH,
    Dz_zero_ae_on_zero_set α f hi, ae_w_ne_zero_prod] with p hpz hpθ hK hpD hw
  by_cases hS : zcoef f p.1 * Spaces.K p.2 = 0
  · have hind : Set.indicator (Z3S f) (fun _ => (1 : ℝ)) p = 0 := by
      rw [Set.indicator_of_notMem]
      intro hc; exact hc hS
    rw [Z3T, hind, mul_zero]
    rcases mul_eq_zero.mp hS with hz | hK0
    · have hφ0 : Z3phi α f p.1 = 0 := by rw [Z3phi, hK hz, mul_zero]
      rw [zero_mul, Z3_eq, hφ0]
      ring
    · have hΓ0 : Spaces.Gam α p.2 = 0 := by
        have h1 : Real.sin p.2 * Real.cos p.2 ^ 2 = 0 := by
          have hK0' : 3 * Real.sin p.2 * Real.cos p.2 ^ 2 = 0 := by
            simpa only [Spaces.K] using hK0
          rcases mul_eq_zero.mp hK0' with h | h
          · rw [mul_eq_zero] at h
            rcases h with h | h
            · exact absurd h (by norm_num)
            · rw [h, zero_mul]
          · rw [h, mul_zero]
        rw [Spaces.Gam, h1, Real.zero_rpow (ne_of_gt (by linarith : (0 : ℝ) < α / 3))]
      rw [zero_mul, Z3_eq, hΓ0]
      ring
  · have hind : Set.indicator (Z3S f) (fun _ => (1 : ℝ)) p = 1 := by
      rw [Set.indicator_of_mem]; exact hS
    rw [Z3T, hind, mul_one]
    by_cases hf : f p.1 p.2 = 0
    · have hf0 : Z3f0 f p = 0 := by rw [Z3f0, Set.indicator_of_mem hS, mul_one, hf]
      have hg0 : Z3g f p = 0 := by rw [Z3g, hf0]; simp
      rw [hg0, hf0, hpD hf]
      ring
    · have hf0 : Z3f0 f p = f p.1 p.2 := by rw [Z3f0, Set.indicator_of_mem hS, mul_one]
      have hg : Z3g f p = L f p.1 p.2 := by
        rw [Z3g, hf0, div_eq_iff (mul_ne_zero hf (pow_ne_zero 2 hw))]
        ring
      have hL : L f p.1 p.2 - f p.1 p.2 + 2 * f p.1 p.2 / (1 + p.1)
          = Spaces.Dz f p.1 p.2 := by
        rw [L]; ring
      rw [hg, hf0, hL, Z3_eq, Weta]
      ring_nf

theorem Z3_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hfH : HardyHyp f) (hi : CoerciveData α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Z3 α f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)
    ∧ wip Weta (Z3 α f) (Spaces.Dz f) ≥ -((1 / 32) * EDz f + 10 ^ 6 * Ef f) := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) = Pzθ := by
    rw [Pzθ, MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  -- ## The pointwise bound for `Z₃`
  have hZ3bd : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |Z3 α f z θ| ≤ 5 * |Kavg f z| := by
    intro z hz θ hθ
    have hΓ1 : |Spaces.Gam α θ| ≤ 1 := by
      rw [abs_of_nonneg (Spaces.Gam_bounds α θ hα hθ).1]
      exact (Spaces.Gam_bounds α θ hα hθ).2
    have hc : (1 : ℝ) / 10 ≤ Spaces.c α := (Spaces.c_bounds α hα hα1).1
    have hcp : 0 < Spaces.c α := lt_of_lt_of_le (by norm_num) hc
    have hφ : |Z3phi α f z| ≤ 5 * |Kavg f z| := by
      rw [Z3phi, abs_mul]
      have hz0 : 0 ≤ z := hz
      have hden : 0 < Spaces.c α * (1 + z) ^ 2 :=
        mul_pos hcp (pow_pos (by linarith) 2)
      have h2 : |2 * z / (Spaces.c α * (1 + z) ^ 2)| ≤ 5 := by
        rw [abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hden))]
        rw [div_le_iff₀ hden]
        nlinarith [sq_nonneg (1 - z), sq_nonneg (1 + z), hcp, hc]
      calc |2 * z / (Spaces.c α * (1 + z) ^ 2)| * |Kavg f z| ≤ 5 * |Kavg f z| :=
            mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ = 5 * |Kavg f z| := rfl
    calc |Z3 α f z θ| = |Z3phi α f z| * |Spaces.Gam α θ| := by rw [Z3_eq, abs_mul]
      _ ≤ (5 * |Kavg f z|) * 1 :=
          mul_le_mul hφ hΓ1 (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = 5 * |Kavg f z| := by ring
  -- ## The dominator
  set G : ℝ × ℝ → ℝ := fun p => 400 * (Kavg f p.1) ^ 2 * Spaces.w p.1 ^ 2
      * (Real.sin (2 * p.2)) ^ (-Spaces.eta)
      + (1 / 64) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 with hGdef
  have hBint : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (volume.restrict Spaces.Iθ) :=
    (Work.Spaces.sin_two_rpow (-Spaces.eta) (by rw [Spaces.eta]; norm_num)
      (by rw [Spaces.eta]; norm_num)).1
  have hG1 : Integrable (fun p : ℝ × ℝ => 400 * (Kavg f p.1) ^ 2 * Spaces.w p.1 ^ 2
      * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) Pzθ := by
    have hA : Integrable (fun z : ℝ => 400 * ((Kavg f z) ^ 2 * Spaces.w z ^ 2))
        (volume.restrict Spaces.Iz) :=
      (Kavg_sq_w_bound α f hfH hi).1.const_mul 400
    refine (Integrable.mul_prod hA hBint).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  have hG2 : Integrable (fun p : ℝ × ℝ => (1 / 64) * (Spaces.Dz f p.1 p.2) ^ 2
      * Weta p.1 p.2) Pzθ := by
    refine ((integrable_Dz_sq_Weta α f hi).const_mul (1 / 64)).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  have hGint : Integrable G Pzθ := by
    rw [hGdef]
    exact hG1.add hG2
  -- ## Pointwise domination
  have hdom : ∀ᵐ p ∂Pzθ,
      ‖Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2‖ ≤ G p := by
    filter_upwards [ae_fst_mem_Iz, ae_snd_mem_Iθ, ae_sin_pos_Pzθ] with p hpz hpθ hsp
    obtain ⟨z, θ⟩ := p
    simp only [Prod.fst, Prod.snd] at hpz hpθ hsp ⊢
    have hwz0 : 0 ≤ Spaces.w z := by rw [Spaces.w]; positivity
    have hs0 : 0 ≤ (Real.sin (2 * θ)) ^ (-Spaces.eta / 2) := Real.rpow_nonneg (le_of_lt hsp) _
    have hWnn : 0 ≤ Weta z θ := by
      rw [Weta]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hsp) _)
    have hsq : ((Real.sin (2 * θ)) ^ (-Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (-Spaces.eta) := (sin_rpow_neg_eta_eq_sq hsp).symm
    set u : ℝ := |Kavg f z| * Spaces.w z * (Real.sin (2 * θ)) ^ (-Spaces.eta / 2) with hu
    set v : ℝ := |Spaces.Dz f z θ| * Spaces.w z * (Real.sin (2 * θ)) ^ (-Spaces.eta / 2)
      with hv
    have hu0 : 0 ≤ u := by rw [hu]; positivity
    have hv0 : 0 ≤ v := by rw [hv]; positivity
    have h2 : |Z3 α f z θ| * |Spaces.Dz f z θ| * Weta z θ ≤ 5 * u * v := by
      have h1 := hZ3bd z hpz θ hpθ
      have hstep : |Z3 α f z θ| * |Spaces.Dz f z θ| * Weta z θ
          ≤ (5 * |Kavg f z|) * |Spaces.Dz f z θ| * Weta z θ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) hWnn
      calc |Z3 α f z θ| * |Spaces.Dz f z θ| * Weta z θ
          ≤ (5 * |Kavg f z|) * |Spaces.Dz f z θ| * Weta z θ := hstep
        _ = 5 * u * v := by rw [hu, hv, Weta, ← hsq]; ring
    have h3 : 400 * u ^ 2 + (1 / 64) * v ^ 2
        = 400 * (Kavg f z) ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
          + 1 / 64 * (Spaces.Dz f z θ) ^ 2 * Weta z θ := by
      rw [hu, hv, Weta, ← hsq]
      simp only [mul_pow, sq_abs]
      ring
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hWnn, hGdef]
    simp only [Prod.fst, Prod.snd]
    calc |Z3 α f z θ| * |Spaces.Dz f z θ| * Weta z θ ≤ 5 * u * v := h2
      _ ≤ 400 * u ^ 2 + (1 / 64) * v ^ 2 := five_mul_le u v
      _ = 400 * (Kavg f z) ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
            + 1 / 64 * (Spaces.Dz f z θ) ^ 2 * Weta z θ := h3
  -- ## An a.e. strongly measurable representative
  have hT := Z3T_eq_target_ae α hα f hfH hi
  have hTaesm := aesm_Z3T α f hi hfH
  have hAESM : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) Pzθ :=
    hTaesm.congr hT
  have hInt : Integrable
      (fun p : ℝ × ℝ => Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) Pzθ :=
    Integrable.mono' hGint hAESM hdom
  have hIntOn : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Z3 α f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [IntegrableOn, hvol]
    exact hInt
  refine ⟨hIntOn, ?_⟩
  -- ## The weighted integral of `(Dz f)²`
  have hEDzG : ∫ p : ℝ × ℝ, Spaces.Dz f p.1 p.2 ^ 2 * Weta p.1 p.2 ∂Pzθ = EDz f := by
    rw [EDz_eq_wip]
    have hIntW : IntegrableOn (Function.uncurry (fun z θ => Spaces.Dz f z θ * Spaces.Dz f z θ
        * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))))
        (Spaces.Iz ×ˢ Spaces.Iθ) := by
      rw [IntegrableOn, hvol]
      refine (integrable_Dz_sq_Weta α f hi).congr
        (Filter.Eventually.of_forall fun p => ?_)
      show Spaces.Dz f p.1 p.2 ^ 2 * Weta p.1 p.2
        = Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2
          * (Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))
      rw [Weta]
      ring
    rw [wip_eq_integral_prod _ _ _ hIntW]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [Weta]; ring)
  have hEf0 : 0 ≤ Ef f := by
    rw [Ef_eq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEDz0 : 0 ≤ EDz f := by
    simp only [EDz, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hA0 : 0 ≤ ∫ z in Spaces.Iz, Kavg f z ^ 2 * Spaces.w z ^ 2 :=
    integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hB0 : 0 ≤ ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
    MeasureTheory.integral_nonneg_of_ae (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  -- ## The value of the dominator
  have hGval : ∫ p, G p ∂Pzθ ≤ 226800 * Ef f + (1 / 64) * EDz f := by
    have hI1 : ∫ p : ℝ × ℝ, 400 * (Kavg f p.1) ^ 2 * Spaces.w p.1 ^ 2
        * (Real.sin (2 * p.2)) ^ (-Spaces.eta) ∂Pzθ
        = 400 * (∫ z in Spaces.Iz, Kavg f z ^ 2 * Spaces.w z ^ 2)
          * (∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
      have h1 : ∫ p : ℝ × ℝ, 400 * (Kavg f p.1) ^ 2 * Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta) ∂Pzθ
          = ∫ p : ℝ × ℝ, (fun z : ℝ => 400 * ((Kavg f z) ^ 2 * Spaces.w z ^ 2)) p.1
              * (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta)) p.2 ∂Pzθ :=
        integral_congr_ae (Filter.Eventually.of_forall fun p => by
          simp only; ring)
      rw [h1, integral_prod_mul_Pzθ
        (fun z : ℝ => 400 * ((Kavg f z) ^ 2 * Spaces.w z ^ 2))
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta)),
        MeasureTheory.integral_const_mul]
    have hI2 : ∫ p : ℝ × ℝ, (1 / 64) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pzθ
        = (1 / 64) * EDz f := by
      rw [show (fun p : ℝ × ℝ => (1 / 64) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2)
          = fun p : ℝ × ℝ => (1 / 64)
            * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) from by funext p; ring]
      rw [MeasureTheory.integral_const_mul, hEDzG]
    rw [hGdef, MeasureTheory.integral_add hG1 hG2, hI1, hI2]
    have hA := (Kavg_sq_w_bound α f hfH hi).2
    have hB := theta_rpow_integral_bound
    have hmain : 400 * (∫ z in Spaces.Iz, Kavg f z ^ 2 * Spaces.w z ^ 2)
        * (∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta)) ≤ 226800 * Ef f := by
      have h3 : 400 * (∫ z in Spaces.Iz, Kavg f z ^ 2 * Spaces.w z ^ 2)
          * (∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta))
          ≤ 400 * (3 * Ef f) * (∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num)) hB0
      have h4 : 400 * (3 * Ef f) * (∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta))
          ≤ 400 * (3 * Ef f) * 189 :=
        mul_le_mul_of_nonneg_left hB (by linarith)
      calc 400 * (∫ z in Spaces.Iz, Kavg f z ^ 2 * Spaces.w z ^ 2)
          * (∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta))
          ≤ 400 * (3 * Ef f)
              * (∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta)) := h3
        _ ≤ 400 * (3 * Ef f) * 189 := h4
        _ = 226800 * Ef f := by ring
    exact add_le_add hmain (le_refl _)
  -- ## The final comparison
  have habs : ∫ p, ‖Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2‖ ∂Pzθ
      ≤ ∫ p, G p ∂Pzθ := integral_mono_ae hInt.norm hGint hdom
  have h1 : -(∫ p, ‖Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2‖ ∂Pzθ)
      ≤ ∫ p, Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂Pzθ := by
    have h := MeasureTheory.abs_integral_le_integral_abs (μ := Pzθ)
      (f := fun p : ℝ × ℝ => Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2)
    have h2 : (∫ p, |Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2| ∂Pzθ)
        = ∫ p, ‖Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2‖ ∂Pzθ :=
      integral_congr_ae (Filter.Eventually.of_forall fun p => by
        show |Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2|
          = ‖Z3 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2‖
        rw [Real.norm_eq_abs])
    rw [h2] at h
    exact (abs_le.mp h).1
  rw [wip_eq_integral_prod Weta (Z3 α f) (Spaces.Dz f) hIntOn]
  linarith [h1, habs, hGval, hEf0, hEDz0]

end Z3Clean

end Work.Coercivity
