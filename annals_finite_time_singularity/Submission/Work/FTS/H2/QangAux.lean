/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary vocabulary for the `z`-differentiation of the angular moments `Qang`

This is the interface module of the proof of `Work.FTS.H2.QangDiff`: the target there is

* `Qang g j` is continuous on `(0,∞)` for `j ≤ 3`;
* `∂_z (Qang g j) z = Qang g (j+1) z / z` for `j ≤ 2`, `z > 0`,

in the *interior* class `SmoothQuad g + HkMem α 4 g` (no analyticity hypothesis
`Spaces.SmoothNbhd`, which a cut-off can never satisfy).

The whole proof runs through the primitive/`Fubini` identity

  `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`

for `j ≤ 3` and `z, z₀ > 0`.  Here we collect the two elementary ingredients of that
identity which are used by several of its pieces, and which are stated in exactly the
form the consumers expect:

* `Qang_eq_intervalIntegral`, which rewrites the set integral over `Iθ = [0,π/2]`
  defining `Qang` as the interval integral over `0..π/2` (needed because
  `Fubini` for interval integrals is stated for interval integrals);
* `sq_DzIter_le_HkIntegrand_div_w_sq`: the *pointwise* domination of a pure
  `D_z`-iterate by the `H^k`-integrand, `(D_z^j g)² ≤ HkIntegrand α k g / w²`, valid on
  the whole *open* quadrant `z > 0`, `0 < θ < π/2` (`Spaces.sq_le_HkIntegrand_z` only
  controls `(D_z^j g)²·w²/sin(2θ)^η` and degenerates at the angular endpoints, where
  Lean's `sin(2θ)^(η/2)` is `0`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.DzIter_slice_FTC_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## `Qang` as an interval integral -/

/-- The angular moment `Qang g j z = ∫_θ K(θ)·(D_z^j g)(z,θ) dθ` written as the *interval*
integral over `0..π/2` (the form in which `Fubini`'s theorem for interval integrals is
stated). -/
def QangI (g : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ

/-- `Qang` is the interval integral `QangI`: `Iθ = Icc 0 (π/2)` differs from `Ioc 0 (π/2)`
by the null singleton `{0}`. -/
theorem Qang_eq_intervalIntegral (g : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Work.Elliptic.Qang g j z = QangI g j z := by
  rw [Work.Elliptic.Qang, QangI, Work.Spaces.Iθ,
    MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)).symm

/-! ## The radial weight -/

theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (by positivity) (by positivity)

/-- The radial weight `w` is antitone on `(0,∞)`: `w x ≥ w b` for `0 < x ≤ b`. -/
theorem w_ge_of_le {x b : ℝ} (hx : 0 < x) (hxb : x ≤ b) : Work.Spaces.w b ≤ Work.Spaces.w x := by
  have hb : 0 < b := lt_of_lt_of_le hx hxb
  rw [Work.Spaces.w, Work.Spaces.w, div_le_div_iff₀ (pow_pos hb 2) (pow_pos hx 2)]
  nlinarith [sq_nonneg (x - b), hx, hb, hxb]

/-! ## The pointwise domination of a pure `D_z`-iterate by the `H^k`-integrand -/

theorem sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- **A single pure `D_z` slot of the `H^k`-integrand dominates the square of the iterate,
on the open quadrant.**  From `Spaces.sq_le_HkIntegrand_z`

  `(D_z^j g · w/sin(2θ)^{η/2})² ≤ HkIntegrand α k g`

and `sin(2θ)^{η/2} ≤ 1` on `(0,π/2)`, so that the angular weight can be dropped: for
`z > 0` and `0 < θ < π/2`,

  `(D_z^j g z θ)² ≤ HkIntegrand α k g z θ / w(z)²`.

(The statement is *pointwise* on the open quadrant — the endpoints `θ = 0, π/2` are the
null set on which Lean's `sin(2θ)^{η/2} = 0` makes the weighted inequality degenerate.) -/
theorem sq_DzIter_le_HkIntegrand_div_w_sq (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (j : ℕ)
    (hj : j ≤ k) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ / (Work.Spaces.w z) ^ 2 := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hw : 0 < Work.Spaces.w z := w_pos hz
  have he : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  set s : ℝ := Real.sin (2 * θ) with hsdef
  have hsnn : 0 ≤ s := le_of_lt hs
  have hpowle : s ^ (Work.Spaces.eta / 2) ≤ 1 := by
    have h1 : s ^ (Work.Spaces.eta / 2) ≤ (1 : ℝ) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_le_rpow hsnn hs1 (by positivity)
    simpa using h1
  have hpowpos : 0 < s ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs _
  -- the weighted factor is at least `w z`
  have hfac : (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hsq : (s ^ (Work.Spaces.eta / 2)) ^ 2 ≤ 1 := pow_le_one₀ hpowpos.le hpowle
    nlinarith [hw]
  have hkey := Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hj
  have hkey' : (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
    have h2 : (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (Work.Spaces.DzIter j g z θ
            * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))) ^ 2 := by
      nlinarith [hfac, sq_nonneg (Work.Spaces.DzIter j g z θ)]
    exact le_trans h2 hkey
  rw [le_div_iff₀ (by positivity)]
  linarith [hkey']


/-! ## The interior class of `SmoothQuad` data is a `SmoothOpen` datum -/

/-- `SmoothQuad` (smoothness on `z > -1`, `0 < θ < π/2`) restricts to `SmoothOpen`
(smoothness on the open quadrant `z > 0`, `0 < θ < π/2`), which is the class of the
open-quadrant API of `Submission/Work/FTS/EllipticEst/`. -/
theorem SmoothQuad.toSmoothOpen {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.EllipticEst.SmoothOpen f :=
  ContDiffOn.mono h (by
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hz' : (-1 : ℝ) < z := by linarith
    exact ⟨hz', ⟨hθ1, hθ2⟩⟩)

/-! ## The primitive formula along a `z`-slice -/

/-- The angular weight is bounded by `3`. -/
theorem abs_Ktheta_le_three (θ : ℝ) : |Work.Elliptic.Ktheta θ| ≤ 3 := by
  have hsin : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hcos2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hcos, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  rw [Work.Elliptic.Ktheta, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have hsin' : 0 ≤ |Real.sin θ| := abs_nonneg _
  have hcos2' : 0 ≤ |Real.cos θ ^ 2| := abs_nonneg _
  nlinarith [hsin, hcos2, hsin', hcos2']

/-- **The primitive formula along a `z`-slice.**  For `g` of class `SmoothQuad`, every
`j : ℕ`, every `z, z₀ > 0` and every `θ ∈ (0,π/2)`,

  `D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^{z} D_z^{j+1} g x θ / x dx`. -/
theorem QangSliceFTC {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) (j : ℕ)
    {z z₀ θ : ℝ} (hz : 0 < z) (hz₀ : 0 < z₀) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ
      = ∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x := by
  have hO : Work.FTS.EllipticEst.SmoothOpen g := SmoothQuad.toSmoothOpen hsm
  -- the derivative of the `θ`-slice of `D_z^j g`, in divided form
  have hderiv : ∀ r : ℝ, r ∈ Set.uIcc z₀ z →
      Work.Spaces.pz (Work.Spaces.DzIter j g) r θ
        = Work.Spaces.DzIter (j + 1) g r θ / r := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le (lt_min hz₀ hz) hr.1
    have h1 : Work.Spaces.DzIter (j + 1) g r θ
        = r * Work.Spaces.pz (Work.Spaces.DzIter j g) r θ := rfl
    rw [h1, mul_comm r, mul_div_cancel_right₀ _ (ne_of_gt hrpos)]
  rcases le_total z₀ z with hle | hle
  · have hF := Work.FTS.EllipticEst.DzIter_slice_FTC_open hO j hz₀ hle hθ
    rw [hF]
    refine intervalIntegral.integral_congr (a := z₀) (b := z)
      (f := fun r => Work.Spaces.pz (Work.Spaces.DzIter j g) r θ)
      (g := fun r => Work.Spaces.DzIter (j + 1) g r θ / r) (fun r hr => hderiv r hr)
  · have hF := Work.FTS.EllipticEst.DzIter_slice_FTC_open hO j hz hle hθ
    have hF' : Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ
        = -∫ r in z..z₀, Work.Spaces.pz (Work.Spaces.DzIter j g) r θ := by
      linarith [hF]
    rw [hF']
    rw [intervalIntegral.integral_congr (a := z) (b := z₀)
      (f := fun r => Work.Spaces.pz (Work.Spaces.DzIter j g) r θ)
      (g := fun r => Work.Spaces.DzIter (j + 1) g r θ / r)
      (fun r hr => hderiv r (by rwa [Set.uIcc_comm]))]
    rw [intervalIntegral.integral_symm, neg_neg]

/-! ## Integrability of the angular slice of `Ktheta · D_z^j g` -/

/-- The pair `(z,θ) ↦ Ktheta θ · D_z^j g z θ` is continuous on the open quadrant. -/
theorem continuousOn_Ktheta_DzIter {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
      * Work.Spaces.DzIter j g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hO : Work.FTS.EllipticEst.SmoothOpen g := SmoothQuad.toSmoothOpen hsm
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hO.DzIter j).continuousOn
  refine (hD.mul hK).congr (fun p hp => ?_)
  exact mul_comm _ _

/-- **The angular slice `θ ↦ Ktheta θ · D_z^j g z θ` is integrable on `Iθ`** for `z > 0` and
`j ≤ 4`, in the interior class `SmoothQuad g + HkMem α 4 g`. -/
theorem QangSliceIntegrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
      Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_Ktheta_DzIter hsm j) hz
  have hmaj : MeasureTheory.Integrable (fun θ : ℝ =>
      3 * (Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.Integrable (fun θ : ℝ =>
        Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hmem.1 z (Set.mem_Ici.mpr hz.le)).div_const _
    have h2 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ)) (by
        rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    exact (h1.add h2).const_mul 3
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  rw [show (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) from by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hKh := abs_Ktheta_le_three θ
  have hDh := sq_DzIter_le_HkIntegrand_div_w_sq α 4 g j hj hz hθ
  have hsq : |Work.Spaces.DzIter j g z θ| ≤ (Work.Spaces.DzIter j g z θ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|Work.Spaces.DzIter j g z θ| - 1),
      sq_abs (Work.Spaces.DzIter j g z θ), abs_nonneg (Work.Spaces.DzIter j g z θ)]
  have hDnn : 0 ≤ |Work.Spaces.DzIter j g z θ| := abs_nonneg _
  have hDh' : |Work.Spaces.DzIter j g z θ|
      ≤ Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1 :=
    le_trans hsq (by linarith)
  calc |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ|
      ≤ 3 * |Work.Spaces.DzIter j g z θ| := mul_le_mul_of_nonneg_right hKh hDnn
    _ ≤ 3 * (Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left hDh' (by norm_num)

/-! ## An almost-everywhere statement on the interval integral over `0..π/2` -/

/-- A property which holds on the open interval `(0,π/2)` holds almost everywhere on
`uIoc 0 (π/2)` (the two endpoints form a null set). -/
theorem ae_imp_uIoc {p : ℝ → Prop} (h : ∀ θ : ℝ, 0 < θ → θ < π / 2 → p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume), θ ∈ Set.uIoc 0 (π / 2) → p θ := by
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({π / 2} : Set ℝ)) ?_
    (MeasureTheory.measure_singleton (π / 2))
  intro θ hθ
  simp only [Set.mem_setOf_eq, not_imp] at hθ
  obtain ⟨hin, hp⟩ := hθ
  rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2)] at hin
  simp only [Set.mem_Ioc] at hin
  by_contra hc
  simp only [Set.mem_singleton_iff] at hc
  exact hp (h θ hin.1 (lt_of_le_of_ne hin.2 hc))

end Work.FTS.H2
