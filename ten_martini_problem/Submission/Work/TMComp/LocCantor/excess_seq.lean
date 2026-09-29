import Mathlib
import Submission.Work.TMComp.Kotani.hasDerivAt_ell
import Submission.Work.TMComp.Kotani.ell_div_antitoneOn
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.ell_defect_le
import Submission.Work.TMComp.Kotani.two_ell
import Submission.Work.TMComp.RedC8.ell_harmonicOnNhd

/-!
# C17 (`P_LocCantor`) — the excess sequence of the Kotani step (L8)

With `ℓ(E) = ell α lam E = ∫₀¹ log ‖m(E,y)‖ dy` (`Kotani.ell`) and
`defect E y = m(E,y) - 1/m(E,α-y)` (`Kotani.defect`), put

* `ratioE α lam E ε = ℓ(E+iε)/ε`,
* `dIntE α lam E ε = ∫₀¹ im(-1/defect(E+iε,y)) dy = ∂_ε ℓ(E+iε)`  (`hasDerivAt_ell`),
* `excessE α lam E ε = ratioE α lam E ε - dIntE α lam E ε ≥ 0`.

For fixed `E` the function `ε ↦ ratioE α lam E ε` is differentiable on `(0,∞)` with derivative
`-excessE(E,ε)/ε`; consequently (fundamental theorem of calculus)

  `∫_a^b excessE(E,ε)/ε dε = ratioE(E,a) - ratioE(E,b)`,

and under the hypothesis `ℓ(E+iε) ≤ C ε` (for `E ∈ K`, `ε ∈ (0,1]`) this is at most `C`
(since `ratioE ≥ 0`).  Tonelli on `K × (a,1)` then gives
`∫₀¹ (1/ε)(∫_K excessE(E,ε) dE) dε ≤ C |K| < ∞`, so for every `n` there is `ε ∈ (0,1/n)` with
`∫_K excessE(E,ε) dE < 1/n`.  This is the sequence `e` of the statement.
-/

set_option maxHeartbeats 1000000

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace Work.TMComp.LocCantor

open Work.TMComp.Kotani

/-! ## The objects -/

/-- `ratioE α lam E ε = ℓ(E+iε)/ε`. -/
def ratioE (α lam : ℝ) (E ε : ℝ) : ℝ := ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I) / ε

/-- `dIntE α lam E ε = ∫₀¹ im(-1/defect(E+iε,y)) dy`. -/
def dIntE (α lam : ℝ) (E ε : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, (-1 / defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y).im

/-- The excess `excessE α lam E ε = ratioE α lam E ε - dIntE α lam E ε`. -/
def excessE (α lam : ℝ) (E ε : ℝ) : ℝ := ratioE α lam E ε - dIntE α lam E ε

/-! ## Nonnegativity -/

/-- `ℓ ≥ 0` on the upper half plane (from (L2), since `Im p > 0`). -/
theorem ell_nonneg (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) : 0 ≤ ell α lam E := by
  have h2 := two_ell α lam E hE
  have hpinv : ∀ x : ℝ, 0 < (pSec α lam E x).im := by
    intro x
    rw [pSec_im α lam E hE x]
    have h1 : 0 < (mfun α lam E x).im := MfunProbs.mfun_im_pos α lam hE x
    have h2 : 0 < ‖mfun α lam E x‖ ^ 2 := by
      refine pow_pos ?_ 2
      exact norm_pos_iff.mpr fun h => by
        have := MfunProbs.mfun_im_pos α lam hE x
        rw [h] at this; simp at this
    exact div_pos h1 h2
  have hnonneg : 0 ≤ ∫ x in (0 : ℝ)..1, Real.log (1 + E.im / (pSec α lam E x).im) :=
    intervalIntegral.integral_nonneg_of_forall zero_le_one fun x => by
      apply Real.log_nonneg
      have hx : 0 < E.im / (pSec α lam E x).im := div_pos hE (hpinv x)
      linarith
  linarith

/-- The excess is nonnegative: `∫₀¹ im(-1/defect) ≤ ℓ/ε` (`ell_defect_le`). -/
theorem excessE_nonneg (α lam : ℝ) (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ excessE α lam E ε := by
  have hEim : 0 < (((E : ℂ) + (ε : ℂ) * Complex.I)).im := by simpa using hε
  have h := ell_defect_le α lam (((E : ℂ) + (ε : ℂ) * Complex.I)) hEim
  have h2 : (((E : ℂ) + (ε : ℂ) * Complex.I)).im = ε := by simp
  rw [h2] at h
  simp only [excessE, ratioE, dIntE]
  linarith

/-! ## Continuity of the parametrized objects -/

/-- `ℓ` is continuous on the upper half plane (it is harmonic there). -/
theorem continuousOn_ell (α lam : ℝ) :
    ContinuousOn (fun z : ℂ => ell α lam z) {z : ℂ | 0 < z.im} :=
  InnerProductSpace.HarmonicOnNhd.continuousOn (Work.TMComp.RedC8.ell_harmonicOnNhd α lam)

/-- The parametrized integrand `(z,y) ↦ im(-1/defect(z,y))` is continuous on `ℍ × ℝ`. -/
theorem continuousOn_defect_im (α lam : ℝ) :
    ContinuousOn (fun p : ℂ × ℝ => (-1 / defect α lam p.1 p.2).im)
      {p : ℂ × ℝ | 0 < p.1.im} := by
  have hm1 : ContinuousOn (fun p : ℂ × ℝ => mfun α lam p.1 p.2)
      {p : ℂ × ℝ | 0 < p.1.im} := MfunProbs.mfun_continuousOn α lam
  have hm2 : ContinuousOn (fun p : ℂ × ℝ => mfun α lam p.1 (α - p.2))
      {p : ℂ × ℝ | 0 < p.1.im} := by
    have hmap : ContinuousOn (fun p : ℂ × ℝ => (p.1, α - p.2)) {p : ℂ × ℝ | 0 < p.1.im} :=
      (continuous_fst.prodMk (continuous_const.sub continuous_snd)).continuousOn
    have hcomp := (MfunProbs.mfun_continuousOn α lam).comp hmap
      (fun p (hp : p ∈ {p : ℂ × ℝ | 0 < p.1.im}) => hp)
    have hfun : ((fun q : ℂ × ℝ => mfun α lam q.1 q.2) ∘ fun p : ℂ × ℝ => (p.1, α - p.2))
        = (fun p : ℂ × ℝ => mfun α lam p.1 (α - p.2)) := by
      funext p; rfl
    rwa [hfun] at hcomp
  have hm2n : ∀ p : ℂ × ℝ, p ∈ {p : ℂ × ℝ | 0 < p.1.im} →
      mfun α lam p.1 (α - p.2) ≠ 0 := fun p hp =>
    ne_of_apply_ne Complex.im (ne_of_gt (MfunProbs.mfun_im_pos α lam hp (α - p.2)))
  have hdef : ContinuousOn (fun p : ℂ × ℝ => defect α lam p.1 p.2)
      {p : ℂ × ℝ | 0 < p.1.im} := by
    have hfun : (fun p : ℂ × ℝ => defect α lam p.1 p.2)
        = (fun p : ℂ × ℝ => mfun α lam p.1 p.2 - 1 / mfun α lam p.1 (α - p.2)) := by
      funext p
      rw [defect, sSec]
    rw [hfun]
    have hnum : ContinuousOn (fun _ : ℂ × ℝ => (1 : ℂ)) {p : ℂ × ℝ | 0 < p.1.im} :=
      continuous_const.continuousOn
    exact hm1.sub (hnum.div hm2 hm2n)
  have hne : ∀ p : ℂ × ℝ, p ∈ {p : ℂ × ℝ | 0 < p.1.im} → defect α lam p.1 p.2 ≠ 0 :=
    fun p hp => defect_ne_zero α lam hp p.2
  have h3 : ContinuousOn (fun p : ℂ × ℝ => -1 / defect α lam p.1 p.2)
      {p : ℂ × ℝ | 0 < p.1.im} := by
    have hnum : ContinuousOn (fun _ : ℂ × ℝ => (-1 : ℂ)) {p : ℂ × ℝ | 0 < p.1.im} :=
      continuous_const.continuousOn
    exact hnum.div hdef hne
  exact Complex.continuous_im.comp_continuousOn h3

/-- Continuity of `z ↦ ∫₀¹ im(-1/defect(z,y)) dy` on the upper half plane. -/
theorem defect_integral_continuous (α lam : ℝ) :
    ContinuousOn (fun z : ℂ => ∫ y in (0 : ℝ)..1, (-1 / defect α lam z y).im)
      {z : ℂ | 0 < z.im} := by
  rw [(isOpen_lt continuous_const Complex.continuous_im).continuousOn_iff]
  intro z₀ hz₀
  have hz₀pos : 0 < z₀.im := hz₀
  set δ : ℝ := z₀.im / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδlt : δ < z₀.im := by rw [hδdef]; linarith
  have hminpos : 0 < min δ 1 := lt_min hδpos one_pos
  have hnbhd : {z : ℂ | δ ≤ z.im} ∈ 𝓝 z₀ :=
    Filter.mem_of_superset
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hδlt)
      (fun z (hz : δ < z.im) => le_of_lt hz)
  refine intervalIntegral.continuousAt_of_dominated_interval
    (F := fun (z : ℂ) (y : ℝ) => (-1 / defect α lam z y).im)
    (x₀ := z₀) (a := 0) (b := 1) (bound := fun _ => 1 / min δ 1) ?_ ?_ ?_ ?_
  · filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz₀pos] with z hz
    exact (Complex.continuous_im.comp (continuous_const.div
      (continuous_defect_phase α lam hz)
      (fun y => defect_ne_zero α lam hz y))).aestronglyMeasurable
  · filter_upwards [hnbhd] with z hz
    filter_upwards with y _
    have hzpos : 0 < z.im := lt_of_lt_of_le hδpos hz
    have hlow : min δ 1 ≤ (mfun α lam z y).im := by
      refine mfun_im_ge α lam (h := min δ 1) hminpos (min_le_right _ _) ?_ y
      exact le_trans (min_le_left _ _) hz
    have hdefge : min δ 1 ≤ (defect α lam z y).im :=
      le_trans hlow (mfun_im_le_defect_im α lam hzpos y)
    have hnorm : min δ 1 ≤ ‖defect α lam z y‖ := le_trans hdefge (Complex.im_le_norm _)
    have h1 : |(-1 / defect α lam z y).im| ≤ 1 / ‖defect α lam z y‖ := by
      have h1' := Complex.abs_im_le_norm ((-1 : ℂ) / defect α lam z y)
      rwa [norm_div, norm_neg, norm_one] at h1'
    rw [Real.norm_eq_abs]
    exact le_trans h1 (one_div_le_one_div_of_le hminpos hnorm)
  · exact continuous_const.intervalIntegrable 0 1
  · filter_upwards with y _
    have hcont_z : ContinuousOn (fun z : ℂ => (-1 / defect α lam z y).im)
        {z : ℂ | 0 < z.im} := by
      have hmap : ContinuousOn (fun z : ℂ => (z, y)) {z : ℂ | 0 < z.im} :=
        (continuous_id.prodMk continuous_const).continuousOn
      have hcomp := (continuousOn_defect_im α lam).comp hmap
        (fun z (hz : z ∈ {z : ℂ | 0 < z.im}) => by simpa using hz)
      have hfun : ((fun p : ℂ × ℝ => (-1 / defect α lam p.1 p.2).im) ∘ fun z : ℂ => (z, y))
          = (fun z : ℂ => (-1 / defect α lam z y).im) := by
        funext z; rfl
      rwa [hfun] at hcomp
    exact hcont_z.continuousAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz₀pos)

/-! ## Continuity in `(E,ε)`, and the derivative -/

/-- Continuity of the pair `(E,ε) ↦ ratioE α lam E ε` for `ε > 0`. -/
theorem continuousOn_pair_ratioE (α lam : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => ratioE α lam p.1 p.2) {p : ℝ × ℝ | 0 < p.2} := by
  have hmap : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have h1 : ContinuousOn (fun p : ℝ × ℝ => ell α lam ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))
      {p : ℝ × ℝ | 0 < p.2} :=
    (continuousOn_ell α lam).comp hmap.continuousOn (fun p hp => by simpa using hp)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => p.2) {p : ℝ × ℝ | 0 < p.2} :=
    continuous_snd.continuousOn
  have hfun : (fun p : ℝ × ℝ => ratioE α lam p.1 p.2)
      = (fun p : ℝ × ℝ => ell α lam ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) / p.2) := by
    funext p; rw [ratioE]
  rw [hfun]
  exact h1.div h2 (fun p hp => ne_of_gt hp)

/-- Continuity of the pair `(E,ε) ↦ dIntE α lam E ε` for `ε > 0`. -/
theorem continuousOn_pair_dIntE (α lam : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => dIntE α lam p.1 p.2) {p : ℝ × ℝ | 0 < p.2} := by
  have hmap : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have h1 : ContinuousOn (fun p : ℝ × ℝ => ∫ y in (0 : ℝ)..1,
      (-1 / defect α lam ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) y).im)
      {p : ℝ × ℝ | 0 < p.2} :=
    (defect_integral_continuous α lam).comp hmap.continuousOn (fun p hp => by simpa using hp)
  have hfun : (fun p : ℝ × ℝ => dIntE α lam p.1 p.2)
      = (fun p : ℝ × ℝ => ∫ y in (0 : ℝ)..1,
          (-1 / defect α lam ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) y).im) := by
    funext p; rw [dIntE]
  rw [hfun]
  exact h1

/-- Continuity of the pair `(E,ε) ↦ excessE α lam E ε` for `ε > 0`. -/
theorem continuousOn_pair_excessE (α lam : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => excessE α lam p.1 p.2) {p : ℝ × ℝ | 0 < p.2} := by
  have hfun : (fun p : ℝ × ℝ => excessE α lam p.1 p.2)
      = (fun p : ℝ × ℝ => ratioE α lam p.1 p.2 - dIntE α lam p.1 p.2) := by
    funext p; rw [excessE]
  rw [hfun]
  exact (continuousOn_pair_ratioE α lam).sub (continuousOn_pair_dIntE α lam)

/-- Continuity of the pair `(E,ε) ↦ excessE α lam E ε / ε` for `ε > 0`. -/
theorem continuousOn_pair_excessE_div (α lam : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => excessE α lam p.1 p.2 / p.2) {p : ℝ × ℝ | 0 < p.2} := by
  have hfun : (fun p : ℝ × ℝ => excessE α lam p.1 p.2 / p.2)
      = (fun p : ℝ × ℝ => excessE α lam p.1 p.2) / (fun p : ℝ × ℝ => p.2) := by
    funext p
    simp only [Pi.div_apply]
  rw [hfun]
  exact (continuousOn_pair_excessE α lam).div continuous_snd.continuousOn
    (fun p hp => ne_of_gt hp)

/-- The one-variable slice `ε ↦ excessE α lam E ε / ε` is continuous on `(0,∞)`. -/
theorem continuousOn_slice_excessE_div (α lam : ℝ) (E : ℝ) :
    ContinuousOn (fun ε : ℝ => excessE α lam E ε / ε) {ε : ℝ | 0 < ε} := by
  have h1 := continuousOn_pair_excessE_div α lam
  have h2 : ContinuousOn (fun ε : ℝ => (E, ε)) {ε : ℝ | 0 < ε} :=
    (continuous_const.prodMk continuous_id).continuousOn
  have h3 := h1.comp h2 (fun ε hε => hε)
  have hfun : ((fun p : ℝ × ℝ => excessE α lam p.1 p.2 / p.2) ∘ fun ε : ℝ => (E, ε))
      = (fun ε : ℝ => excessE α lam E ε / ε) := by
    funext ε; rfl
  rwa [hfun] at h3

/-- `∂_ε [ℓ(E+iε)/ε] = -excessE(E,ε)/ε`. -/
theorem hasDerivAt_ratioE (α lam : ℝ) (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    HasDerivAt (fun t : ℝ => ratioE α lam E t) (-(excessE α lam E ε) / ε) ε := by
  have h := (hasDerivAt_ell α lam E ε hε).div (hasDerivAt_id ε) (ne_of_gt hε)
  have hval : ((∫ y in (0 : ℝ)..1,
        (-1 / defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y).im) * ε
      - ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I) * 1) / ε ^ 2
      = -(excessE α lam E ε) / ε := by
    simp only [excessE, ratioE, dIntE]
    field_simp
    ring
  refine (h.congr_deriv hval).congr_of_eventuallyEq ?_
  filter_upwards with t
  simp only [Pi.div_apply, id_eq, ratioE]

/-- **Fundamental theorem of calculus.** `∫_a^b excessE(E,ε)/ε dε = ratioE(E,a) - ratioE(E,b)`. -/
theorem integral_excessE_div (α lam : ℝ) (E : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ ε in a..b, excessE α lam E ε / ε = ratioE α lam E a - ratioE α lam E b := by
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => ratioE α lam E t)
      (-(excessE α lam E x) / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_ratioE α lam E (lt_of_lt_of_le ha hx.1)
  have hcont : ContinuousOn (fun x : ℝ => excessE α lam E x / x) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact (continuousOn_slice_excessE_div α lam E).mono (fun x hx => lt_of_lt_of_le ha hx.1)
  have hint : IntervalIntegrable (fun x : ℝ => -(excessE α lam E x) / x) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine hcont.neg.congr (fun x _ => ?_)
    show -(excessE α lam E x) / x = -(excessE α lam E x / x)
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h2 : ∫ x in a..b, -(excessE α lam E x) / x
      = -(∫ x in a..b, excessE α lam E x / x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    show -(excessE α lam E x) / x = -(excessE α lam E x / x)
    ring
  rw [h2] at h
  linarith

/-! ## The ENNReal selection lemma -/

/-- If `∫⁻ ε in (a,1), ε⁻¹ * H ε ≤ B` for every `a ∈ (0,1)` then `H` is small at points
arbitrarily close to `0`. -/
theorem small_of_lintegral_le (H : ℝ → ENNReal) (B : ENNReal) (hB : B < ⊤)
    (h : ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∫⁻ ε in Set.Ioc a 1, (ENNReal.ofReal ε⁻¹ * H ε) ≤ B) :
    ∀ n : ℕ, 1 ≤ n → ∃ ε ∈ Set.Ioo (0 : ℝ) ((n : ℝ)⁻¹),
      H ε < ENNReal.ofReal ((n : ℝ)⁻¹) := by
  intro n hn
  by_contra hcon
  push_neg at hcon
  set δ : ℝ := (n : ℝ)⁻¹ with hδdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle : δ ≤ 1 := by
    rw [hδdef]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)
  set σ : ℝ := (n : ℝ) * (B.toReal + 1) with hσdef
  have hσpos : 0 < σ := by
    rw [hσdef]
    have : (0 : ℝ) ≤ B.toReal := ENNReal.toReal_nonneg
    nlinarith
  set a : ℝ := δ * Real.exp (-σ) with hadef
  have hapos : 0 < a := by rw [hadef]; positivity
  have ha_lt : a < δ := by
    rw [hadef]
    have hexp : Real.exp (-σ) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    exact mul_lt_of_lt_one_right hδpos hexp
  have hmem : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨hapos, lt_of_lt_of_le ha_lt hδle⟩
  have hδa : a ≤ δ := le_of_lt ha_lt
  -- the a.e. statement `ε ≠ δ`
  have hδae : ∀ᵐ ε ∂(volume : Measure ℝ), ε ≠ δ := by
    rw [MeasureTheory.ae_iff]
    simpa using (Real.volume_singleton (a := δ))
  -- lower bound
  have hlow1 : ENNReal.ofReal (B.toReal + 1)
      ≤ ∫⁻ ε in Set.Ioc a δ, (ENNReal.ofReal ε⁻¹ * H ε) := by
    have hstep : ∫⁻ ε in Set.Ioc a δ, (ENNReal.ofReal ε⁻¹ * ENNReal.ofReal δ)
        ≤ ∫⁻ ε in Set.Ioc a δ, (ENNReal.ofReal ε⁻¹ * H ε) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      have hne : ∀ᵐ ε ∂(volume.restrict (Set.Ioc a δ)), ε ≠ δ := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hδae] with ε h1 _
        exact h1
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc, hne] with ε hε hεne
      have hεmem : ε ∈ Set.Ioo (0 : ℝ) δ :=
        ⟨lt_trans hapos hε.1, lt_of_le_of_ne hε.2 hεne⟩
      exact mul_le_mul_of_nonneg_left (hcon ε hεmem) (by positivity)
    have hval : ∫⁻ ε in Set.Ioc a δ, (ENNReal.ofReal ε⁻¹ * ENNReal.ofReal δ)
        = ENNReal.ofReal (B.toReal + 1) := by
      rw [MeasureTheory.lintegral_mul_const' (ENNReal.ofReal δ) (fun ε : ℝ => ENNReal.ofReal ε⁻¹)
        ENNReal.ofReal_ne_top]
      have hI : IntegrableOn (fun ε : ℝ => ε⁻¹) (Set.Ioc a δ) := by
        refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set
          Set.Ioc_subset_Icc_self
        exact continuousOn_id.inv₀ (fun x hx => ne_of_gt (lt_of_lt_of_le hapos hx.1))
      have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc a δ)] (fun ε : ℝ => ε⁻¹) := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with ε hε
        exact inv_nonneg.mpr (le_of_lt (lt_trans hapos hε.1))
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI hnn]
      have hlog : ∫ ε in Set.Ioc a δ, ε⁻¹ = σ := by
        rw [(intervalIntegral.integral_of_le hδa).symm, integral_inv_of_pos hapos hδpos]
        have hratio : δ / a = Real.exp σ := by
          rw [hadef, div_eq_mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hδpos),
            one_mul, ← Real.exp_neg]
          congr 1
          rw [hσdef]
          ring
        rw [hratio, Real.log_exp]
      rw [hlog, ← ENNReal.ofReal_mul (le_of_lt hσpos)]
      congr 1
      have hval2 : σ * δ = B.toReal + 1 := by
        rw [hσdef, hδdef]
        rw [mul_assoc, mul_comm (B.toReal + 1) _, ← mul_assoc,
          mul_inv_cancel₀ (ne_of_gt hnpos), one_mul]
      exact hval2
    exact hval.ge.trans hstep
  -- upper bound
  have hup : ∫⁻ ε in Set.Ioc a δ, (ENNReal.ofReal ε⁻¹ * H ε) ≤ B :=
    le_trans (MeasureTheory.lintegral_mono_set (Set.Ioc_subset_Ioc_right hδle)) (h a hmem)
  have hle : ENNReal.ofReal (B.toReal + 1) ≤ B := le_trans hlow1 hup
  have hle' : (ENNReal.ofReal (B.toReal + 1)).toReal ≤ B.toReal :=
    ENNReal.toReal_mono hB.ne hle
  rw [ENNReal.toReal_ofReal (by linarith [ENNReal.toReal_nonneg (a := B)])] at hle'
  linarith

/-! ## The theorem -/

theorem excess_seq (α lam : ℝ) {K : Set ℝ} (hK : MeasurableSet K) (hKfin : MeasureTheory.volume K < ⊤) (hH : ∃ C : ℝ, 0 < C ∧ ∀ E ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → Work.TMComp.Kotani.ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I) ≤ C * ε) : ∃ e : ℕ → ℝ, (∀ j : ℕ, 0 < e j ∧ e j ≤ 1) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun j : ℕ => ∫ E in K, (Work.TMComp.Kotani.ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j - ∫ y in (0 : ℝ)..1, (-1 / Work.TMComp.Kotani.defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im)) Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hH⟩ := hH
  -- The Tonelli step: a bound for the `ε`-integral of the `K`-averaged excess.
  have hStep : ∀ a ∈ Set.Ioo (0 : ℝ) 1,
      ∫⁻ ε in Set.Ioc a 1, (ENNReal.ofReal ε⁻¹ *
          (∫⁻ E in K, ENNReal.ofReal (excessE α lam E ε)))
        ≤ ENNReal.ofReal C * volume K := by
    intro a ha
    obtain ⟨ha0, ha1⟩ := ha
    have hSmeas : MeasurableSet (K ×ˢ Set.Ioc a 1) := hK.prod measurableSet_Ioc
    have hcontF : ContinuousOn
        (Function.uncurry fun (E ε : ℝ) => ENNReal.ofReal (excessE α lam E ε / ε))
        (K ×ˢ Set.Ioc a 1) := by
      have h2 : ContinuousOn (fun p : ℝ × ℝ => excessE α lam p.1 p.2 / p.2)
          (K ×ˢ Set.Ioc a 1) :=
        (continuousOn_pair_excessE_div α lam).mono (fun p hp => lt_trans ha0 hp.2.1)
      exact ENNReal.continuous_ofReal.comp_continuousOn h2
    have hFaem : AEMeasurable
        (Function.uncurry fun (E ε : ℝ) => ENNReal.ofReal (excessE α lam E ε / ε))
        ((volume.restrict K).prod (volume.restrict (Set.Ioc a 1))) := by
      rw [MeasureTheory.Measure.prod_restrict]
      exact hcontF.aemeasurable hSmeas
    have hswap := MeasureTheory.lintegral_lintegral_swap (μ := volume.restrict K)
      (ν := volume.restrict (Set.Ioc a 1))
      (f := fun (E ε : ℝ) => ENNReal.ofReal (excessE α lam E ε / ε)) hFaem
    -- pointwise bound for `E ∈ K`
    have hpt : ∀ E ∈ K, ∫⁻ ε in Set.Ioc a 1, ENNReal.ofReal (excessE α lam E ε / ε)
        ≤ ENNReal.ofReal C := by
      intro E hE
      have hI : IntegrableOn (fun ε : ℝ => excessE α lam E ε / ε) (Set.Ioc a 1) := by
        refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set
          Set.Ioc_subset_Icc_self
        exact (continuousOn_slice_excessE_div α lam E).mono (fun x hx => lt_of_lt_of_le ha0 hx.1)
      have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc a 1)]
          (fun ε : ℝ => excessE α lam E ε / ε) := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with ε hε
        exact div_nonneg (excessE_nonneg α lam E (lt_trans ha0 hε.1))
          (le_of_lt (lt_trans ha0 hε.1))
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI hnn]
      apply ENNReal.ofReal_le_ofReal
      rw [(intervalIntegral.integral_of_le ha1.le).symm,
        integral_excessE_div α lam E ha0 ha1.le]
      have h3 : ratioE α lam E a ≤ C := by
        have hh := hH E hE a ha0 ha1.le
        rw [ratioE, div_le_iff₀ ha0]
        simpa using hh
      have h4 : 0 ≤ ratioE α lam E 1 := by
        rw [ratioE]
        exact div_nonneg (ell_nonneg α lam (E := ((E : ℂ) + (1 : ℂ) * Complex.I)) (by simp))
          (by norm_num)
      linarith
    have hconst : ∫⁻ E in K, ENNReal.ofReal C = ENNReal.ofReal C * volume K := by
      rw [MeasureTheory.lintegral_const]
      congr 1
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    -- assemble
    have h1 : (∫⁻ ε in Set.Ioc a 1, ENNReal.ofReal ε⁻¹ *
          (∫⁻ E in K, ENNReal.ofReal (excessE α lam E ε)))
        = ∫⁻ ε in Set.Ioc a 1, ∫⁻ E in K, ENNReal.ofReal (excessE α lam E ε / ε) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with ε hε
      have hεpos : 0 < ε := lt_trans ha0 hε.1
      have hEeq : (∫⁻ E in K, ENNReal.ofReal (excessE α lam E ε / ε))
          = ∫⁻ E in K, ENNReal.ofReal (excessE α lam E ε) * ENNReal.ofReal ε⁻¹ := by
        refine MeasureTheory.lintegral_congr (fun E => ?_)
        rw [← ENNReal.ofReal_mul (excessE_nonneg α lam E hεpos), div_eq_mul_inv]
      rw [hEeq, MeasureTheory.lintegral_mul_const' (ENNReal.ofReal ε⁻¹) _ ENNReal.ofReal_ne_top,
        mul_comm]
    rw [h1, ← hswap]
    calc ∫⁻ E in K, ∫⁻ ε in Set.Ioc a 1, ENNReal.ofReal (excessE α lam E ε / ε)
        ≤ ∫⁻ E in K, ENNReal.ofReal C := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem hK] with E hE
          exact hpt E hE
      _ = ENNReal.ofReal C * volume K := hconst
  -- apply the selection lemma
  have hsel : ∀ j : ℕ, ∃ ε ∈ Set.Ioo (0 : ℝ) (((j + 1 : ℕ) : ℝ)⁻¹),
      (∫⁻ E in K, ENNReal.ofReal (excessE α lam E ε))
        < ENNReal.ofReal (((j + 1 : ℕ) : ℝ)⁻¹) := fun j =>
    small_of_lintegral_le (fun ε => ∫⁻ E in K, ENNReal.ofReal (excessE α lam E ε))
      (ENNReal.ofReal C * volume K) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin) hStep
      (j + 1) (Nat.le_add_left 1 j)
  choose e he using hsel
  refine ⟨e, ?_, ?_, ?_⟩
  · intro j
    have hlt := (he j).1.2
    have hle : (((j + 1 : ℕ) : ℝ)⁻¹) ≤ 1 :=
      inv_le_one_of_one_le₀ (by exact_mod_cast Nat.le_add_left 1 j)
    exact ⟨(he j).1.1, le_trans (le_of_lt hlt) hle⟩
  · refine squeeze_zero (fun j => le_of_lt (he j).1.1) (fun j => le_of_lt (he j).1.2) ?_
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · have hmain : Filter.Tendsto (fun j : ℕ => ∫ E in K, excessE α lam E (e j))
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (f := fun j => ‖∫ E in K, excessE α lam E (e j)‖)
        (g := fun j => (((j + 1 : ℕ) : ℝ)⁻¹)) (fun j => norm_nonneg _) ?_ ?_
      · intro j
        have h1 := MeasureTheory.norm_integral_le_lintegral_norm (μ := volume.restrict K)
          (fun E : ℝ => excessE α lam E (e j))
        have h2 : (∫⁻ E in K, ENNReal.ofReal ‖excessE α lam E (e j)‖)
            = ∫⁻ E in K, ENNReal.ofReal (excessE α lam E (e j)) := by
          refine MeasureTheory.lintegral_congr (fun E => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (excessE_nonneg α lam E (he j).1.1)]
        rw [h2] at h1
        have h3 : (∫⁻ E in K, ENNReal.ofReal (excessE α lam E (e j))).toReal
            ≤ (((j + 1 : ℕ) : ℝ)⁻¹) := by
          have h4 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (le_of_lt (he j).2)
          rwa [ENNReal.toReal_ofReal (by positivity)] at h4
        linarith
      · simpa only [one_div, Nat.cast_add, Nat.cast_one] using
          tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [excessE, ratioE, dIntE] using hmain

end Work.TMComp.LocCantor
