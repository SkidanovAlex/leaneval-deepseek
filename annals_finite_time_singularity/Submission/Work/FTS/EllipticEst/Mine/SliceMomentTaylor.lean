import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Blocks.IMC.cs_integral_mul_le
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# The slice moment/Taylor estimate `∫_{Iθ} |g| sinθcos²θ ≤ 3|g(π/4)| + 9|g'(π/4)| + 9√(∫|g''|²sin(2θ)^{-η})`

For `g` of class `C²` on the open angular interval `(0, π/2)` whose weighted second
derivative `g'' · sin(2θ)^{-η/2}` is square integrable on `Iθ = [0, π/2]`
(`η = 99/100`), the slice `g` is integrable against the solvability weight
`sin θ cos²θ`, and

`∫_{Iθ} |g θ| sinθcos²θ ≤ 3 |g(π/4)| + 9 |g'(π/4)| + 9 √(∫_{Iθ} g''(θ)² sin(2θ)^{-η})`.

## Route

* **Taylor with integral remainder** (`TaylorRemainderIoo`): for `g` of class `C²` on an open
  interval and `a, θ` in it, `g θ = g a + (θ-a)g'(a) + ∫_a^θ (θ-s) g''(s) ds` (FTC applied to
  `s ↦ (θ-s)g'(s) + g(s)`, whose derivative is `(θ-s)g''(s)`; no orientation split is needed
  because Mathlib's interval integral is oriented).
* **Weighted Cauchy–Schwarz** (`abs_intervalIntegral_mul_le`): on a compact subinterval
  `[c,d] ⊆ (0,π/2)` where `sin(2s) > 0`, split `(θ-s)h(s)` as
  `(|θ-s| sin(2s)^{η/2}) · (|h(s)| sin(2s)^{-η/2})` and apply Cauchy–Schwarz
  (`Work.Blocks.IMC.cs_integral_mul_le`) over `Icc c d`; monotonicity of the set integral
  (`setIntegral_mono_set`) replaces `Icc c d` by `Iθ` in both factors.
* **Kernel bound** (`integral_sq_mul_sin_two_rpow_le_eight`): since `|θ - s| ≤ π/2` and
  `sin(2s)^η ≤ 1` on `Iθ`,
  `∫_{Iθ} (θ-s)² sin(2s)^η ≤ (π/2)² · (π/2) = (π/2)³ ≤ 8` (using `π < 4`).
* **Assembly**: `|g θ| ≤ M := |g(π/4)| + (π/2)|g'(π/4)| + √8·√N` on `(0,π/2)`, where
  `N = ∫_{Iθ} g''² sin(2θ)^{-η}`; multiplying by `sinθcos²θ ≥ 0` and integrating gives
  `∫|g| sinθcos²θ ≤ M/3 ≤ 3|g(π/4)| + 9|g'(π/4)| + 9√N` (the constants `3, 9, 9` are extremely
  loose).  Integrability of `g · sinθcos²θ` follows by dominated convergence against the
  integrable majorant `M · sinθcos²θ`, the a.e. statements being transferred from the open
  interval via `Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo`.
-/


noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §1 Taylor's formula with integral remainder on an open interval -/

private theorem TaylorRemainderIoo {g : ℝ → ℝ} {l u a θ : ℝ}
    (hg : ContDiffOn ℝ 2 g (Set.Ioo l u)) (ha : a ∈ Set.Ioo l u) (hθ : θ ∈ Set.Ioo l u) :
    g θ = g a + (θ - a) * deriv g a + ∫ s in a..θ, (θ - s) * deriv (deriv g) s := by
  have hsub : Set.uIcc a θ ⊆ Set.Ioo l u := ordConnected_Ioo.uIcc_subset ha hθ
  have hca : ∀ s ∈ Set.uIcc a θ, ContDiffAt ℝ 2 g s := fun s hs =>
    hg.contDiffAt (isOpen_Ioo.mem_nhds (hsub hs))
  have hH : ∀ s ∈ Set.uIcc a θ,
      HasDerivAt (fun s : ℝ => (θ - s) * deriv g s + g s)
        ((θ - s) * deriv (deriv g) s) s := by
    intro s hs
    have h2 : ContDiffAt ℝ 2 g s := hca s hs
    have h1 : ContDiffAt ℝ 1 (deriv g) s := h2.derivWithin (m := 1) (by norm_num)
    have hd2 : HasDerivAt (deriv g) (deriv (deriv g) s) s :=
      (h1.hasStrictDerivAt (by norm_num)).hasDerivAt
    have hd0 : HasDerivAt g (deriv g s) s := (h2.differentiableAt (by norm_num)).hasDerivAt
    have hd1 : HasDerivAt (fun s : ℝ => θ - s) (-1) s := by
      have h : HasDerivAt (fun s : ℝ => θ - s) (0 - 1) s :=
        (hasDerivAt_const s θ).sub (hasDerivAt_id s)
      simpa using h
    have h := (hd1.mul hd2).add hd0
    have hA : (-1 * deriv g s + (θ - s) * deriv (deriv g) s + deriv g s)
        = (θ - s) * deriv (deriv g) s := by ring
    rw [hA] at h
    exact h
  have hint : IntervalIntegrable (fun s : ℝ => (θ - s) * deriv (deriv g) s)
      MeasureTheory.volume a θ := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have h2 : ContDiffAt ℝ 2 g s := hca s hs
    have h1 : ContDiffAt ℝ 1 (deriv g) s := h2.derivWithin (m := 1) (by norm_num)
    have h0 : ContinuousAt (deriv (deriv g)) s :=
      (h1.derivWithin (m := 0) (by norm_num)).continuousAt
    exact ((continuous_const.sub continuous_id).continuousAt.mul h0).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hH hint
  have hz : (∫ s in a..θ, (θ - s) * deriv (deriv g) s)
      = ((θ - θ) * deriv g θ + g θ) - ((θ - a) * deriv g a + g a) := hFTC
  rw [hz]
  ring

/-! ## §2 Elementary angular facts -/

private lemma eta_pos : 0 < Work.Spaces.eta := by norm_num [Work.Spaces.eta]

private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma cont_sin_two_rpow :
    ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ := by
  refine ContinuousOn.rpow_const ?_ (fun x _ => Or.inr (le_of_lt eta_pos))
  exact Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)

private lemma integrableOn_sin_two_rpow :
    MeasureTheory.IntegrableOn (fun s : ℝ => (Real.sin (2 * s)) ^ (Work.Spaces.eta))
      Work.Spaces.Iθ :=
  ContinuousOn.integrableOn_compact isCompact_Icc cont_sin_two_rpow

private lemma integral_sin_two_rpow_le :
    (∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (Work.Spaces.eta)) ≤ Real.pi / 2 := by
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (C := (1 : ℝ)) (ne_of_lt isCompact_Icc.measure_lt_top)
  calc (∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (Work.Spaces.eta))
      ≤ ∫ s in Work.Spaces.Iθ, (1 : ℝ) :=
        setIntegral_mono_on integrableOn_sin_two_rpow hone measurableSet_Icc
          (fun s hs => Real.rpow_le_one (sin_two_nonneg_Iθ hs) (Real.sin_le_one _)
            (le_of_lt eta_pos))
    _ = Real.pi / 2 := by
        rw [MeasureTheory.setIntegral_const]
        simp [Work.Spaces.Iθ,
          Real.volume_real_Icc_of_le (le_of_lt (by positivity : (0 : ℝ) < Real.pi / 2))]

private lemma integrableOn_sq_mul_sin_two_rpow {θ : ℝ} :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ :=
  ContinuousOn.integrableOn_compact isCompact_Icc
    (((show Continuous fun s : ℝ => (θ - s) ^ 2 by fun_prop).continuousOn).mul cont_sin_two_rpow)

private lemma integral_sq_mul_sin_two_rpow_le_eight {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta)) ≤ 8 := by
  have hpi4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
  have hmaj : MeasureTheory.IntegrableOn
      (fun s : ℝ => (Real.pi / 2) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
      Work.Spaces.Iθ :=
    integrableOn_sin_two_rpow.const_mul _
  have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hθ
  calc (∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
      ≤ ∫ s in Work.Spaces.Iθ, (Real.pi / 2) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta) := by
        refine setIntegral_mono_on integrableOn_sq_mul_sin_two_rpow hmaj measurableSet_Icc
          (fun s hs => ?_)
        have hs' : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hs
        have h1 : -(Real.pi / 2) ≤ θ - s := by linarith [hs'.2, hθ'.1]
        have h2 : θ - s ≤ Real.pi / 2 := by linarith [hθ'.2, hs'.1]
        have h3 : (θ - s) ^ 2 ≤ (Real.pi / 2) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (sin_two_nonneg_Iθ hs) _)
    _ = (Real.pi / 2) ^ 2 * (∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (Work.Spaces.eta)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (Real.pi / 2) ^ 2 * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left integral_sin_two_rpow_le (by positivity)
    _ ≤ 8 := by
        have h2 : Real.pi / 2 ≤ 2 := by linarith
        have h3 : (Real.pi / 2) ^ 3 ≤ 8 := by
          calc (Real.pi / 2) ^ 3 ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
            _ = 8 := by norm_num
        nlinarith [h3]

/-! ## §3 The two Cauchy–Schwarz factors -/

private def facA (θ s : ℝ) : ℝ := |θ - s| * (Real.sin (2 * s)) ^ (Work.Spaces.eta / 2)

private def facB (h : ℝ → ℝ) (s : ℝ) : ℝ := |h s| * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta / 2))

private lemma rpow_half_mul_self {x : ℝ} (hx : 0 < x) :
    x ^ (Work.Spaces.eta / 2) * x ^ (Work.Spaces.eta / 2) = x ^ Work.Spaces.eta := by
  rw [← Real.rpow_add hx, show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta by ring]

private lemma rpow_neg_half_mul_self {x : ℝ} (hx : 0 < x) :
    x ^ (-(Work.Spaces.eta / 2)) * x ^ (-(Work.Spaces.eta / 2)) = x ^ (-(Work.Spaces.eta)) := by
  rw [← Real.rpow_add hx,
    show -(Work.Spaces.eta / 2) + -(Work.Spaces.eta / 2) = -(Work.Spaces.eta) by ring]

private lemma rpow_half_sq {x : ℝ} (hx : 0 < x) :
    (x ^ (Work.Spaces.eta / 2)) ^ 2 = x ^ Work.Spaces.eta := by
  rw [sq, rpow_half_mul_self hx]

private lemma rpow_neg_half_sq {x : ℝ} (hx : 0 < x) :
    (x ^ (-(Work.Spaces.eta / 2))) ^ 2 = x ^ (-(Work.Spaces.eta)) := by
  rw [sq, rpow_neg_half_mul_self hx]

private lemma facA_mul_facB {h : ℝ → ℝ} {θ s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) :
    facA θ s * facB h s = |(θ - s) * h s| := by
  have hsp : 0 < Real.sin (2 * s) := sin_two_pos_of_Ioo hs
  have hrp : (Real.sin (2 * s)) ^ (Work.Spaces.eta / 2)
      * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta / 2)) = 1 := by
    rw [← Real.rpow_add hsp, show Work.Spaces.eta / 2 + -(Work.Spaces.eta / 2) = 0 by ring,
      Real.rpow_zero]
  rw [facA, facB, abs_mul]
  calc |θ - s| * (Real.sin (2 * s)) ^ (Work.Spaces.eta / 2)
        * (|h s| * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta / 2)))
      = |θ - s| * |h s|
        * ((Real.sin (2 * s)) ^ (Work.Spaces.eta / 2)
          * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta / 2))) := by ring
    _ = |θ - s| * |h s| := by rw [hrp, mul_one]

private lemma facA_sq {θ s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) :
    (facA θ s) ^ 2 = (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta) := by
  have hsp : 0 < Real.sin (2 * s) := sin_two_pos_of_Ioo hs
  rw [facA, mul_pow, sq_abs, rpow_half_sq hsp]

private lemma facB_sq {h : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) :
    (facB h s) ^ 2 = (h s) ^ 2 * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) := by
  have hsp : 0 < Real.sin (2 * s) := sin_two_pos_of_Ioo hs
  rw [facB, mul_pow, sq_abs, rpow_neg_half_sq hsp]

private lemma contOn_sin_two_rpow_half {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ (Work.Spaces.eta / 2)) (Set.Icc c d) := by
  refine ContinuousOn.rpow_const ?_ (fun x hx => Or.inl ?_)
  · exact Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  · exact ne_of_gt (sin_two_pos_of_Ioo ⟨lt_of_lt_of_le hc hx.1, lt_of_le_of_lt hx.2 hd⟩)

private lemma contOn_sin_two_rpow_neg_half {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ (-(Work.Spaces.eta / 2))) (Set.Icc c d) := by
  refine ContinuousOn.rpow_const ?_ (fun x hx => Or.inl ?_)
  · exact Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  · exact ne_of_gt (sin_two_pos_of_Ioo ⟨lt_of_lt_of_le hc hx.1, lt_of_le_of_lt hx.2 hd⟩)

private lemma contOn_facA {θ c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (facA θ) (Set.Icc c d) := by
  have h1 : Continuous (fun s : ℝ => |θ - s|) := by fun_prop
  exact h1.continuousOn.mul (contOn_sin_two_rpow_half hc hd)

private lemma contOn_facB {h : ℝ → ℝ} {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2)
    (hcont : ContinuousOn h (Set.Icc c d)) :
    ContinuousOn (facB h) (Set.Icc c d) :=
  hcont.abs.mul (contOn_sin_two_rpow_neg_half hc hd)

/-! ## §4 Cauchy–Schwarz on a compact subinterval of the open angular interval -/

private lemma abs_intervalIntegral_mul_le {h : ℝ → ℝ} {θ c d : ℝ} (hcd : c ≤ d)
    (hc : 0 < c) (hd : d < Real.pi / 2) (hcont : ContinuousOn h (Set.Icc c d))
    (hint : MeasureTheory.IntegrableOn (fun s => (h s) ^ 2
        * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    |∫ s in c..d, (θ - s) * h s|
      ≤ Real.sqrt (∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
        * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
            * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) := by
  have hsub : Set.Icc c d ⊆ Work.Spaces.Iθ :=
    fun s hs => ⟨le_trans (le_of_lt hc) hs.1, le_trans hs.2 (le_of_lt hd)⟩
  have hsuboo : Set.Icc c d ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun s hs => ⟨lt_of_lt_of_le hc hs.1, lt_of_le_of_lt hs.2 hd⟩
  have hmIcc : MeasurableSet (Set.Icc c d) := measurableSet_Icc
  have hnnA : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta) :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun s hs =>
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ ⟨le_of_lt hs.1, le_of_lt hs.2⟩) _))
  have hnnB : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (h s) ^ 2 * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun s hs =>
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ ⟨le_of_lt hs.1, le_of_lt hs.2⟩) _))
  have h1 : |∫ s in c..d, (θ - s) * h s| ≤ ∫ s in c..d, |(θ - s) * h s| := by
    simpa only [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_integral_norm (f := fun s : ℝ => (θ - s) * h s) hcd
  have h2 : (∫ s in c..d, |(θ - s) * h s|)
      = ∫ s in Set.Icc c d, facA θ s * facB h s := by
    rw [intervalIntegral.integral_of_le hcd, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun hmIcc (fun s hs => ?_)
    rw [facA_mul_facB (h := h) (θ := θ) (hsuboo hs)]
  have hFaesm : AEStronglyMeasurable (facA θ) (volume.restrict (Set.Icc c d)) :=
    (contOn_facA (θ := θ) hc hd).aestronglyMeasurable hmIcc
  have hGaesm : AEStronglyMeasurable (facB h) (volume.restrict (Set.Icc c d)) :=
    (contOn_facB hc hd hcont).aestronglyMeasurable hmIcc
  have hF2 : Integrable (fun s => (facA θ s) ^ 2) (volume.restrict (Set.Icc c d)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc ((contOn_facA (θ := θ) hc hd).pow 2)
  have hG2 : Integrable (fun s => (facB h s) ^ 2) (volume.restrict (Set.Icc c d)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc ((contOn_facB hc hd hcont).pow 2)
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Set.Icc c d))
    hFaesm hGaesm hF2 hG2
  have hF2' : (∫ s in Set.Icc c d, (facA θ s) ^ 2)
      = ∫ s in Set.Icc c d, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta) :=
    setIntegral_congr_fun hmIcc (fun s hs => facA_sq (hsuboo hs))
  have hG2' : (∫ s in Set.Icc c d, (facB h s) ^ 2)
      = ∫ s in Set.Icc c d, (h s) ^ 2 * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) :=
    setIntegral_congr_fun hmIcc (fun s hs => facB_sq (hsuboo hs))
  have hF2le : (∫ s in Set.Icc c d, (facA θ s) ^ 2)
      ≤ ∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta) := by
    rw [hF2']
    exact setIntegral_mono_set integrableOn_sq_mul_sin_two_rpow hnnA
      (Eventually.of_forall (fun s hs => hsub hs))
  have hG2le : (∫ s in Set.Icc c d, (facB h s) ^ 2)
      ≤ ∫ s in Work.Spaces.Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) := by
    rw [hG2']
    exact setIntegral_mono_set hint hnnB (Eventually.of_forall (fun s hs => hsub hs))
  have hFGnn : 0 ≤ ∫ s in Set.Icc c d, facA θ s * facB h s :=
    setIntegral_nonneg hmIcc (fun s hs => by
      rw [facA_mul_facB (h := h) (θ := θ) (hsuboo hs)]; exact abs_nonneg _)
  have h3 : (∫ s in Set.Icc c d, facA θ s * facB h s)
      ≤ Real.sqrt (∫ s in Set.Icc c d, (facA θ s) ^ 2)
        * Real.sqrt (∫ s in Set.Icc c d, (facB h s) ^ 2) := by
    calc (∫ s in Set.Icc c d, facA θ s * facB h s)
        = |∫ s in Set.Icc c d, facA θ s * facB h s| := (abs_of_nonneg hFGnn).symm
      _ ≤ _ := hcs
  have h4 : Real.sqrt (∫ s in Set.Icc c d, (facA θ s) ^ 2)
      * Real.sqrt (∫ s in Set.Icc c d, (facB h s) ^ 2)
      ≤ Real.sqrt (∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
        * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
            * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) :=
    mul_le_mul (Real.sqrt_le_sqrt hF2le) (Real.sqrt_le_sqrt hG2le)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc |∫ s in c..d, (θ - s) * h s| ≤ ∫ s in c..d, |(θ - s) * h s| := h1
    _ = ∫ s in Set.Icc c d, facA θ s * facB h s := h2
    _ ≤ _ := h3
    _ ≤ _ := h4

/-! ## §5 The Taylor remainder at `π/4` -/

private theorem intervalRemainder_le {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hh : MeasureTheory.IntegrableOn (fun s => (h s) ^ 2
        * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |∫ s in (Real.pi / 4)..θ, (θ - s) * h s|
      ≤ Real.sqrt 8 * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
          * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) := by
  have h4pos : (0 : ℝ) < Real.pi / 4 := by positivity
  have h4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hC : Real.sqrt (∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
      ≤ Real.sqrt 8 :=
    Real.sqrt_le_sqrt (integral_sq_mul_sin_two_rpow_le_eight ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hNN : 0 ≤ Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
      * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) := Real.sqrt_nonneg _
  rcases le_total (Real.pi / 4) θ with hle | hle
  · have hc1 : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro s hs
      exact ⟨lt_of_lt_of_le h4pos hs.1, lt_of_le_of_lt hs.2 hθ.2⟩
    have hkey := abs_intervalIntegral_mul_le (h := h) (θ := θ) hle h4pos hθ.2
      (hcont.mono hc1) hh
    calc |∫ s in (Real.pi / 4)..θ, (θ - s) * h s|
        ≤ Real.sqrt (∫ s in Work.Spaces.Iθ,
              (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
          * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
              * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) := hkey
      _ ≤ Real.sqrt 8 * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
              * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_right hC hNN
  · have hsym : (∫ s in (Real.pi / 4)..θ, (θ - s) * h s)
        = -(∫ s in θ..(Real.pi / 4), (θ - s) * h s) :=
      intervalIntegral.integral_symm θ (Real.pi / 4)
    have hc1 : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro s hs
      exact ⟨lt_of_lt_of_le hθ.1 hs.1, lt_of_le_of_lt hs.2 h4lt⟩
    have hkey := abs_intervalIntegral_mul_le (h := h) (θ := θ) hle hθ.1 h4lt
      (hcont.mono hc1) hh
    rw [hsym, abs_neg]
    calc |∫ s in θ..(Real.pi / 4), (θ - s) * h s|
        ≤ Real.sqrt (∫ s in Work.Spaces.Iθ,
              (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
          * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
              * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) := hkey
      _ ≤ Real.sqrt 8 * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
              * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_right hC hNN

/-! ## §6 The angular weight `sinθcos²θ` -/

private lemma continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

private lemma sinCos2_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos, hθ.1]) hθ.2
  positivity

private lemma integrableOn_sinCos2 :
    MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
  ContinuousOn.integrableOn_compact isCompact_Icc continuous_sinCos2.continuousOn

private lemma integral_Iθ_sinCos2 :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ) = 1 / 3 := by
  have hderiv : ∀ θ : ℝ,
      HasDerivAt (fun θ : ℝ => -(Real.cos θ) ^ 3 / 3) (Work.Elliptic.sinCos2 θ) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => Real.cos θ) (-Real.sin θ) θ := Real.hasDerivAt_cos θ
    have h3 := h1.pow 3
    have h4 := h3.neg.div_const 3
    refine h4.congr_deriv ?_
    simp only [Work.Elliptic.sinCos2]
    ring
  have hint : IntervalIntegrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ) volume 0 (π / 2) :=
    continuous_sinCos2.intervalIntegrable 0 (π / 2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := π / 2)
    (fun θ _ => hderiv θ) hint
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
  rw [h]
  simp [Real.cos_pi_div_two, Real.cos_zero]
  norm_num

private lemma aesm_of_contDiffOn_Ioo {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)) := hg.continuousOn
  have h1 : AEStronglyMeasurable g (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hms : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))
  rwa [hms] at h1

/-! ## §7 The main estimate -/

theorem SliceMomentTaylor {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => g θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, |g θ| * Work.Elliptic.sinCos2 θ
        ≤ 3 * |g (Real.pi / 4)| + 9 * |deriv g (Real.pi / 4)|
          + 9 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have h4mem : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hder1 : ContDiffOn ℝ 1 (deriv g) (Set.Ioo 0 (Real.pi / 2)) :=
    hg.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont2 : ContinuousOn (deriv (deriv g)) (Set.Ioo 0 (Real.pi / 2)) :=
    (hder1.deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)).continuousOn
  set NN : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hNNdef
  set M : ℝ := |g (Real.pi / 4)| + (Real.pi / 2) * |deriv g (Real.pi / 4)|
      + Real.sqrt 8 * Real.sqrt NN with hMdef
  -- the pointwise bound on the open interval
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |g θ| ≤ M := by
    intro θ hθ
    have hT := TaylorRemainderIoo hg h4mem hθ
    have hb := intervalRemainder_le hcont2 hint hθ
    have hθa : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hθb : |θ - Real.pi / 4| * |deriv g (Real.pi / 4)|
        ≤ (Real.pi / 2) * |deriv g (Real.pi / 4)| :=
      mul_le_mul_of_nonneg_right hθa (abs_nonneg _)
    rw [hMdef]
    calc |g θ| = |g (Real.pi / 4) + (θ - Real.pi / 4) * deriv g (Real.pi / 4)
            + ∫ s in (Real.pi / 4)..θ, (θ - s) * deriv (deriv g) s| := by rw [hT]
      _ ≤ |g (Real.pi / 4)| + |(θ - Real.pi / 4) * deriv g (Real.pi / 4)|
            + |∫ s in (Real.pi / 4)..θ, (θ - s) * deriv (deriv g) s| := abs_add_three ..
      _ = |g (Real.pi / 4)| + |θ - Real.pi / 4| * |deriv g (Real.pi / 4)|
            + |∫ s in (Real.pi / 4)..θ, (θ - s) * deriv (deriv g) s| := by rw [abs_mul]
      _ ≤ |g (Real.pi / 4)| + (Real.pi / 2) * |deriv g (Real.pi / 4)|
            + Real.sqrt 8 * Real.sqrt NN := by
          have := hb
          rw [← hNNdef] at this
          linarith [hθb, this]
  -- integrability of the majorant
  have hMsc : Integrable (fun θ => M * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sinCos2.const_mul M
  have hscnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ Work.Elliptic.sinCos2 θ :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ =>
      sinCos2_nonneg_of_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have haebound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |g θ| * Work.Elliptic.sinCos2 θ ≤ M * Work.Elliptic.sinCos2 θ :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ =>
      mul_le_mul_of_nonneg_right (hpt θ hθ)
        (sinCos2_nonneg_of_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
  have haesm : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ) :=
    aesm_of_contDiffOn_Ioo hg
  have hscaesm : AEStronglyMeasurable (fun θ => Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) :=
    continuous_sinCos2.continuousOn.aestronglyMeasurable measurableSet_Icc
  have hIntAbs : Integrable (fun θ => |g θ| * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have haesmA : AEStronglyMeasurable (fun θ => |g θ| * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
      fun_prop
    refine Integrable.mono' hMsc haesmA ?_
    filter_upwards [haebound, hscnn] with θ h hnn
    rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hnn)]
  have hIntG : Integrable (fun θ => g θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have haesmG : AEStronglyMeasurable (fun θ => g θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
      fun_prop
    refine Integrable.mono' hMsc haesmG ?_
    filter_upwards [haebound, hscnn] with θ h hnn
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    exact h
  refine ⟨hIntG, ?_⟩
  calc (∫ θ in Work.Spaces.Iθ, |g θ| * Work.Elliptic.sinCos2 θ)
      ≤ ∫ θ in Work.Spaces.Iθ, M * Work.Elliptic.sinCos2 θ :=
        integral_mono_ae hIntAbs hMsc haebound
    _ = M * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ) := by
        rw [MeasureTheory.integral_const_mul]
    _ = M * (1 / 3) := by rw [integral_Iθ_sinCos2]
    _ ≤ 3 * |g (Real.pi / 4)| + 9 * |deriv g (Real.pi / 4)| + 9 * Real.sqrt NN := by
        rw [hMdef]
        have h8 : Real.sqrt 8 ≤ 27 := by
          have h : Real.sqrt 8 ≤ Real.sqrt (27 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
          rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 27)] at h
        have hp : Real.pi ≤ 54 := by linarith [Real.pi_lt_four]
        nlinarith [abs_nonneg (g (Real.pi / 4)), abs_nonneg (deriv g (Real.pi / 4)),
          Real.sqrt_nonneg NN]

end Work.FTS.EllipticEst.Mine
