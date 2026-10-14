import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.PkgJets.thetaBound
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

/-!
# Auxiliary lemmas for the per-slice bound of `Θ α g / cos θ`

The target `ProducerH.thetaDivCos_slice` is

`∫_θ HkIntegrand α 0 (Θ α g / cos θ) z θ ≤ C (1 + 1/z) (Xn6 α g)²`  (`z > 0`),

which combines two independent estimates:

* the **angular** estimate `theta_slice_le`: the slice is at most
  `((1/(4α))²·4·∫_θ sin(2θ)^{-η}) · ((L₁₂ g z)²w(z)²)`, via the pointwise bound
  `PkgJets.HkIntegrand_zero_le` and the integrability of `sin(2θ)^{-η}` on `Iθ`;
* the **radial** estimate `L12_w_sq_pointwise_aux`: `(L₁₂ g z)²w(z)² ≤ 2000·BK²·HkSq α 4 g / z`
  for `ClassC` data, by the mean value estimate of `Work.Analysis.WeightedPoincare` applied to
  `t ↦ L₁₂ g t · w t` on `[z/2,z]`.

The elementary pointwise arithmetic behind the second one (the estimate of `|R·R'|` by the
weighted squares of `L₁₂ g` and `FK g`) is isolated as `two_mul_abs_RR_le`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The pointwise mean-value arithmetic.**  For `L = L₁₂ g t`, `F = FK g t`, `w = w(t)`,
`R = L·w` and `R' = -(F/t)·w + L·(-(2(1+t)/t³))` (the logarithmic derivative of `w`), one has

  `2|R·R'| ≤ (10/z)·((L·w)² + (F·w)²)`  for `t ≥ z/2 > 0`.

Indeed `|R'| ≤ |F|w/t + |L|·2(1+t)/t³`, so `|R·R'| ≤ |L|w·|F|w/t + (Lw)²·(2/t)` (the second
term because `2(1+t)/t³ ≤ (2/t)w`), and `|L|w·|F|w ≤ ((Lw)² + (Fw)²)/2` by AM–GM; collecting,
`2|R R'| ≤ 5((Lw)² + (Fw)²)/t`, and `1/t ≤ 2/z` since `t ≥ z/2`. -/
theorem two_mul_abs_RR_le (L F t z : ℝ) (ht : 0 < t) (hz : 0 < z) (hzt : z ≤ 2 * t) :
    2 * |(L * Work.Spaces.w t) * (-(F / t) * Work.Spaces.w t + L * (-(2 * (1 + t) / t ^ 3)))|
      ≤ (10 / z) * ((L * Work.Spaces.w t) ^ 2 + (F * Work.Spaces.w t) ^ 2) := by
  change 2 * |(L * ((1 + t) ^ 2 / t ^ 2))
        * (-(F / t) * ((1 + t) ^ 2 / t ^ 2) + L * (-(2 * (1 + t) / t ^ 3)))|
      ≤ (10 / z) * ((L * ((1 + t) ^ 2 / t ^ 2)) ^ 2 + (F * ((1 + t) ^ 2 / t ^ 2)) ^ 2)
  set w : ℝ := (1 + t) ^ 2 / t ^ 2 with hw
  set c : ℝ := 2 * (1 + t) / t ^ 3 with hc
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hwpos : 0 < w := by rw [hw]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hcw : c * t ≤ 2 * w := by
    rw [hc, hw]; field_simp; nlinarith [ht.le]
  have hcw2 : c / w ≤ 2 / t := by
    rw [div_le_div_iff₀ hwpos ht]; linarith [hcw]
  set A : ℝ := |L| * w with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hAe : A ^ 2 = (L * w) ^ 2 := by
    rw [hA, ← sq_abs (L * w), show |L * w| = |L| * w from by rw [abs_mul, abs_of_nonneg hw0]]
  have hVe : (|F| * w) ^ 2 = (F * w) ^ 2 := by
    rw [← sq_abs (F * w), show |F * w| = |F| * w from by rw [abs_mul, abs_of_nonneg hw0]]
  have hY : |(-(F / t) * w + L * (-c))| ≤ |F| * w / t + |L| * c := by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul, abs_neg, abs_neg, abs_of_nonneg hw0, abs_of_nonneg hc0,
      abs_div, abs_of_pos ht]
    have he : |F| / t * w = |F| * w / t := by ring
    rw [he]
  have hX : |(L * w) * (-(F / t) * w + L * (-c))| ≤ A * (|F| * w / t + |L| * c) := by
    rw [abs_mul, show |L * w| = A from by rw [hA, abs_mul, abs_of_nonneg hw0]]
    exact mul_le_mul_of_nonneg_left hY hA0
  have hterm : A * (|F| * w / t + |L| * c) ≤ A * (|F| * w) / t + (2 / t) * A ^ 2 := by
    rw [mul_add]
    have e : A * (|F| * w / t) = A * (|F| * w) / t := by ring
    rw [e]
    refine add_le_add le_rfl ?_
    have h1 : A * (|L| * c) = A ^ 2 * (c / w) := by
      rw [hA]; field_simp; try ring
    calc A * (|L| * c) = A ^ 2 * (c / w) := h1
      _ ≤ A ^ 2 * (2 / t) := mul_le_mul_of_nonneg_left hcw2 (sq_nonneg A)
      _ = (2 / t) * A ^ 2 := by ring
  have hamgm : A * (|F| * w) ≤ (A ^ 2 + (|F| * w) ^ 2) / 2 := by
    nlinarith [sq_nonneg (A - |F| * w)]
  have hb1 : A * (|F| * w) / t ≤ ((A ^ 2 + (|F| * w) ^ 2) / 2) / t :=
    div_le_div_of_nonneg_right hamgm (le_of_lt ht)
  have hstep : 2 * |(L * w) * (-(F / t) * w + L * (-c))| ≤ 5 * (A ^ 2 + (|F| * w) ^ 2) / t := by
    have h23 : |(L * w) * (-(F / t) * w + L * (-c))|
        ≤ ((A ^ 2 + (|F| * w) ^ 2) / 2) / t + (2 / t) * A ^ 2 :=
      le_trans hX (le_trans hterm (add_le_add hb1 le_rfl))
    have hmul := mul_le_mul_of_nonneg_left h23 (by norm_num : (0:ℝ) ≤ 2)
    have heq : 2 * (((A ^ 2 + (|F| * w) ^ 2) / 2) / t + (2 / t) * A ^ 2)
        = (5 * A ^ 2 + (|F| * w) ^ 2) / t := by
      field_simp; ring
    rw [heq] at hmul
    refine le_trans hmul ?_
    rw [div_le_div_iff_of_pos_right ht]
    nlinarith [sq_nonneg (|F| * w)]
  have hlast : 5 * (A ^ 2 + (|F| * w) ^ 2) / t ≤ (10 / z) * (A ^ 2 + (|F| * w) ^ 2) := by
    have h5' : (5:ℝ) / t ≤ 10 / z := by
      rw [div_le_div_iff₀ ht hz]; linarith
    have h0 : 0 ≤ A ^ 2 + (|F| * w) ^ 2 := by positivity
    calc 5 * (A ^ 2 + (|F| * w) ^ 2) / t = (5 / t) * (A ^ 2 + (|F| * w) ^ 2) := by ring
      _ ≤ (10 / z) * (A ^ 2 + (|F| * w) ^ 2) := mul_le_mul_of_nonneg_right h5' h0
  calc 2 * |(L * ((1 + t) ^ 2 / t ^ 2))
        * (-(F / t) * ((1 + t) ^ 2 / t ^ 2) + L * (-(2 * (1 + t) / t ^ 3)))|
      = 2 * |(L * w) * (-(F / t) * w + L * (-c))| := by rw [hw, hc]
    _ ≤ 5 * (A ^ 2 + (|F| * w) ^ 2) / t := hstep
    _ ≤ (10 / z) * (A ^ 2 + (|F| * w) ^ 2) := hlast
    _ = (10 / z) * ((L * w) ^ 2 + (F * w) ^ 2) := by rw [hAe, hVe]
    _ = (10 / z) * ((L * ((1 + t) ^ 2 / t ^ 2)) ^ 2 + (F * ((1 + t) ^ 2 / t ^ 2)) ^ 2) := by rw [hw]

/-! ## The angular (slice) estimate -/

/-- `∫_θ HkIntegrand α 0 (Θ α g / cos θ) z θ ≤ ((1/(4α))²·4·Jη)·((L₁₂ g z)²w(z)²)` where
`Jη = ∫_θ sin(2θ)^{-η}`: integrate the pointwise bound `PkgJets.HkIntegrand_zero_le` against the
integrable weight `sin(2θ)^{-η}` (`Work.Spaces.sin_two_rpow`). -/
theorem theta_slice_le {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
      (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) z θ)
      ≤ ((1 / (4 * α)) ^ 2 * 4
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  set J : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hJ
  have hsinEta : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hmaj : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (1 / (4 * α)) ^ 2 * 4 * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) *
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    hsinEta.const_mul _
  have hmono : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
        (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (1 / (4 * α)) ^ 2 * 4 * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) *
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ))
      hmaj
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => Work.FTS_EllLimOK.PkgJets.HkIntegrand_zero_le hα g z θ hθ))
  have hval : (∫ θ in Work.Spaces.Iθ,
          (1 / (4 * α)) ^ 2 * 4 * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) *
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = ((1 / (4 * α)) ^ 2 * 4 * J) * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [MeasureTheory.integral_const_mul, ← hJ]
    ring
  exact le_trans hmono (le_of_eq hval)

/-! ## The radial (mean value) estimate -/

/-- **Pointwise-in-`z` bound for the weighted `L₁₂`-transform.**
For `g` of class `C` and every `z > 0`, `(L₁₂ g z)² w(z)² ≤ 2000·BK²·HkSq α 4 g / z`.

The mean value lemma `Work.Analysis.WeightedPoincare.sq_le_two_div_mul_integral_sq_add_integral_abs_mul`
applied to `R = L₁₂ g · w` on `[z/2,z]` (with `R'` the product-rule derivative, computed from
`PkgJets.L12_classC_facts` and `Work.Coercivity.hasDerivAt_w`) gives
`R z² ≤ (2/z)∫_{z/2}^z R² + ∫_{z/2}^z 2|R R'|`; the first integral is at most
`H = ∫_{Iz}(L₁₂ g)²w²`, and the second is at most `(10/z)(H + K)` by `two_mul_abs_RR_le`,
`K = ∫_{Iz}(FK g)²w²`.  Then `H ≤ 107·BK²·HkSq α 4 g` and `K ≤ BK²·HkSq α 4 g`. -/
theorem L12_w_sq_pointwise_aux {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.ClassC.ClassC α g) :
    ∀ z : ℝ, 0 < z →
      (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ 2000 * Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g / z := by
  intro z hz
  obtain ⟨-, hderivL, hcont01, htend⟩ := Work.FTS_EllLimOK.PkgJets.L12_classC_facts hg
  obtain ⟨hQint, hFKbd⟩ := Work.FTS_EllLimOK.PkgJets.FK_w_sq_bound hg
  obtain ⟨hL12int, hL12bd⟩ :=
    Work.FTS_EllLimOK.PkgJets.L12_w_sq_bound hderivL hcont01 htend hg.l12 hQint
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS_EllLimOK.PkgJets.HkMem_mono_le hg.reg (by norm_num) hg.mem
  set S : ℝ := Work.Spaces.HkSq α 4 g with hS
  set B : ℝ := Work.FTS.GalBasis.cc.BK with hB
  have hS0 : 0 ≤ S := Work.Spaces.HkSq_nonneg α 4 g
  set H : ℝ := ∫ t in Work.Spaces.Iz, (Work.Construction.L12 g t) ^ 2 * (Work.Spaces.w t) ^ 2 with hH
  set K : ℝ := ∫ t in Work.Spaces.Iz, (Work.Construction.FK g t) ^ 2 * (Work.Spaces.w t) ^ 2 with hK
  have hHle : H ≤ 107 * K := by rw [hH, hK]; exact hL12bd
  have hKle : K ≤ B ^ 2 * S := by rw [hK, hB, hS]; exact hFKbd
  set R : ℝ → ℝ := fun t => Work.Construction.L12 g t * Work.Spaces.w t with hR
  set R' : ℝ → ℝ := fun t => -(Work.Construction.L12dens g t) * Work.Spaces.w t
      + Work.Construction.L12 g t * (-(2 * (1 + t) / t ^ 3)) with hR'
  have hle : z / 2 ≤ z := by linarith
  have hz2 : (0 : ℝ) < z / 2 := by linarith
  have hL12_cont : ContinuousOn (fun t : ℝ => Work.Construction.L12 g t) (Set.Icc (z / 2) z) :=
    fun t ht => (hderivL t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hL12dens_cont : ContinuousOn (Work.Construction.L12dens g) (Set.Icc (z / 2) z) :=
    fun t ht => (Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk hg.reg hmem4
      (by linarith [ht.1])).continuousWithinAt
  have hw_cont : ContinuousOn Work.Spaces.w (Set.Icc (z / 2) z) := by
    change ContinuousOn (fun t : ℝ => (1 + t) ^ 2 / t ^ 2) (Set.Icc (z / 2) z)
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · exact continuousOn_id.pow 2
    · intro t ht; exact pow_ne_zero 2 (by linarith [ht.1] : t ≠ 0)
  have hrat_cont : ContinuousOn (fun t : ℝ => -(2 * (1 + t) / t ^ 3)) (Set.Icc (z / 2) z) := by
    refine ContinuousOn.neg ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_const.mul (continuousOn_const.add continuousOn_id)
    · exact continuousOn_id.pow 3
    · intro t ht; exact pow_ne_zero 3 (by linarith [ht.1] : t ≠ 0)
  have hRcont : ContinuousOn R (Set.Icc (z / 2) z) := by
    rw [hR]; exact hL12_cont.mul hw_cont
  have hR'cont : ContinuousOn R' (Set.Icc (z / 2) z) := by
    rw [hR']
    exact ((hL12dens_cont.neg).mul hw_cont).add (hL12_cont.mul hrat_cont)
  have hder : ∀ t ∈ Set.Ioo (z / 2) z, HasDerivAt R (R' t) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h1 : HasDerivAt (fun t : ℝ => Work.Construction.L12 g t)
        (-(Work.Construction.L12dens g t)) t := hderivL t (by linarith [ht.1])
    have h2 : HasDerivAt Work.Spaces.w (-(2 * (1 + t) / t ^ 3)) t :=
      (Work.Coercivity.hasDerivAt_w ht0).congr_deriv (by ring)
    rw [hR, hR']
    exact h1.mul h2
  have hRcont_u : ContinuousOn R (Set.uIcc (z / 2) z) := by
    rw [Set.uIcc_of_le hle]; exact hRcont
  have hR'cont_u : ContinuousOn R' (Set.uIcc (z / 2) z) := by
    rw [Set.uIcc_of_le hle]; exact hR'cont
  have hint1 : IntervalIntegrable (fun t => 2 * R t * R' t) MeasureTheory.volume (z / 2) z :=
    ((continuousOn_const (c := (2:ℝ))).mul hRcont_u |>.mul hR'cont_u).intervalIntegrable
  have hintabs : IntervalIntegrable (fun t => 2 * |R t * R' t|) MeasureTheory.volume (z / 2) z :=
    ((continuousOn_const (c := (2:ℝ))).mul (hRcont_u.mul hR'cont_u |>.abs)).intervalIntegrable
  have hintsq : IntervalIntegrable (fun t => R t ^ 2) MeasureTheory.volume (z / 2) z :=
    (hRcont_u.pow 2).intervalIntegrable
  have hkey := Work.Analysis.WeightedPoincare.sq_le_two_div_mul_integral_sq_add_integral_abs_mul
    hz hRcont hder hint1 hintabs hintsq
  have hRz : R z ^ 2 = (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    rw [hR]; ring
  rw [hRz] at hkey
  have hA : (∫ t in (z / 2)..z, R t ^ 2) ≤ H := by
    rw [intervalIntegral.integral_of_le hle, hH]
    have hfun : (fun t : ℝ => R t ^ 2)
        = fun t : ℝ => (Work.Construction.L12 g t) ^ 2 * (Work.Spaces.w t) ^ 2 := by
      funext t; rw [hR]; ring
    rw [hfun]
    refine MeasureTheory.setIntegral_mono_set hL12int ?_ ?_
    · exact Filter.Eventually.of_forall fun t => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact Filter.Eventually.of_forall fun t ht => le_of_lt (lt_trans hz2 ht.1)
  have hk_cont : ContinuousOn (fun t : ℝ =>
      (Work.Construction.FK g t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Icc (z / 2) z) := by
    have hFK : ContinuousOn (fun t : ℝ => Work.Construction.FK g t) (Set.Icc (z / 2) z) :=
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fk_cont_FK hg.reg hmem4).mono
        (fun t ht => lt_of_lt_of_le hz2 ht.1)
    exact (hFK.pow 2).mul (hw_cont.pow 2)
  have hki : IntervalIntegrable (fun t => (Work.Construction.FK g t) ^ 2
      * (Work.Spaces.w t) ^ 2) MeasureTheory.volume (z / 2) z := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]; exact hk_cont
  have hC : (∫ t in (z / 2)..z, (Work.Construction.FK g t) ^ 2 * (Work.Spaces.w t) ^ 2) ≤ K := by
    rw [intervalIntegral.integral_of_le hle, hK]
    refine MeasureTheory.setIntegral_mono_set hQint ?_ ?_
    · exact Filter.Eventually.of_forall fun t => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact Filter.Eventually.of_forall fun t ht => le_of_lt (lt_trans hz2 ht.1)
  have hpt : ∀ t ∈ Set.Icc (z / 2) z, 2 * |R t * R' t|
      ≤ (10 / z) * (R t ^ 2 + (Work.Construction.FK g t) ^ 2 * (Work.Spaces.w t) ^ 2) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hz2 ht.1
    have hzt : z ≤ 2 * t := by linarith [ht.1]
    have hR2 : R t ^ 2 = (Work.Construction.L12 g t * Work.Spaces.w t) ^ 2 := by rw [hR]
    have hF2 : (Work.Construction.FK g t) ^ 2 * (Work.Spaces.w t) ^ 2
        = (Work.Construction.FK g t * Work.Spaces.w t) ^ 2 := (mul_pow _ _ 2).symm
    rw [hR2, hF2]
    have key := two_mul_abs_RR_le (Work.Construction.L12 g t) (Work.Construction.FK g t) t z ht0 hz hzt
    refine le_trans (le_of_eq ?_) key
    simp only [hR, hR', Work.FTS_EllLimOK.PkgJets.L12dens_eq_FK_div g t]
  have hInt2 : IntervalIntegrable (fun t => (10 / z) * (R t ^ 2
      + (Work.Construction.FK g t) ^ 2 * (Work.Spaces.w t) ^ 2)) MeasureTheory.volume (z / 2) z := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    exact ((hRcont.pow 2).add hk_cont).const_mul (10 / z)
  have hB : (∫ t in (z / 2)..z, 2 * |R t * R' t|) ≤ (10 / z) * (H + K) := by
    have hmono := intervalIntegral.integral_mono_on hle hintabs hInt2 hpt
    have hcm : (∫ u in (z / 2)..z, (10 / z) * (R u ^ 2
        + (Work.Construction.FK g u) ^ 2 * (Work.Spaces.w u) ^ 2))
        = (10 / z) * ∫ u in (z / 2)..z, (R u ^ 2
          + (Work.Construction.FK g u) ^ 2 * (Work.Spaces.w u) ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    have hadd : (∫ u in (z / 2)..z, (R u ^ 2
        + (Work.Construction.FK g u) ^ 2 * (Work.Spaces.w u) ^ 2))
        = (∫ u in (z / 2)..z, R u ^ 2)
          + ∫ u in (z / 2)..z, (Work.Construction.FK g u) ^ 2 * (Work.Spaces.w u) ^ 2 :=
      intervalIntegral.integral_add hintsq hki
    rw [hcm, hadd] at hmono
    exact le_trans hmono (mul_le_mul_of_nonneg_left (add_le_add hA hC) (by positivity))
  have hfinal : (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (12 * H + 10 * K) / z := by
    have h1 : (2 / z) * (∫ t in (z / 2)..z, R t ^ 2) ≤ (2 / z) * H :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    have h3 : (2 / z) * H + (10 / z) * (H + K) = (12 * H + 10 * K) / z := by
      field_simp; ring
    calc (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (2 / z) * (∫ t in (z / 2)..z, R t ^ 2) + ∫ t in (z / 2)..z, 2 * |R t * R' t| := hkey
      _ ≤ (2 / z) * H + (10 / z) * (H + K) := add_le_add h1 hB
      _ = (12 * H + 10 * K) / z := h3
  have hsum3 : 12 * H + 10 * K ≤ 2000 * (B ^ 2 * S) := by
    have hH' : H ≤ 107 * (B ^ 2 * S) := le_trans hHle (mul_le_mul_of_nonneg_left hKle (by norm_num))
    have hB2nn : 0 ≤ B ^ 2 * S := mul_nonneg (sq_nonneg B) hS0
    nlinarith [hH', hKle, hB2nn]
  calc (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (12 * H + 10 * K) / z := hfinal
    _ ≤ (2000 * (B ^ 2 * S)) / z := div_le_div_of_nonneg_right hsum3 (le_of_lt hz)
    _ = 2000 * B ^ 2 * S / z := by ring

end

end Work.FTS_EllLimOK.ProducerH
