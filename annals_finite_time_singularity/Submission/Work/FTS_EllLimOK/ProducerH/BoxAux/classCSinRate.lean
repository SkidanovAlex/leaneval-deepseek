import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongPersist.N6.sliceAng_le6
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS_RegExport.THL.integral_sin_two_rpow_le
import Submission.Work.Spaces.HardyZ
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `BoxAux.classCSinRate` — the angular vanishing rate of a class-`C` profile

For `0 < α ≤ 1` there is a constant `C = C(α) > 0` such that **every** class-`C` profile
`f` (`Work.FTS.ClassC.ClassC α f`) obeys, uniformly in `z > 0` and `θ ∈ (0,π/2)`,

  `|f z θ| ≤ C · Xn6 α f · (min θ (π/2 - θ)) ^ ((γ-1)/2)`,   `γ = gam α = 1 + α/10`,

i.e. `f` vanishes at both angular endpoints at least at the rate `sin(2θ)^((γ-1)/2)`.

**Route.**  A class-`C` profile has honest traces (`ClassC.tr`): `f z θ → 0` as `θ → 0⁺` and as
`θ → (π/2)⁻` for every `z > 0` (`Work.FTS.H2.HQ.BdryTraces.tendsto_theta_*`).  Hence `f z θ` is the
integral of its `θ`-derivative down to the endpoint, and the weighted Cauchy–Schwarz inequality

  `|f z θ - f z t| ≤ (∫_θ^t g'² sin^{2-γ})^{1/2} · (∫_θ^t sin^{γ-2})^{1/2}`

combined with `∫_θ^t sin(2σ)^{γ-2} ≤ 2(π/4)^{2-γ}/(γ-1)·(t-θ)^{γ-1}`
(`THL.integral_sin_two_rpow_le`) produces the exponent `(γ-1)/2` at *both* endpoints.

The remaining input is the `z`-uniform angular slice bound: for `1 ≤ a` and `a + b ≤ 5`,
`∫_θ (D_z^bD_θ^a f z θ)² sin(2θ)^{-γ} ≤ C · HkSq α 6 f` (`StrongPersist.N6.sliceAng_le6`), applied
at the slot `(b,a) = (0,1)` (`D_θ f = sin(2θ)·∂_θ f`).  The sub-interval form used here is
obtained from the full-`Iθ` form by monotonicity of the set integral, the integrability of the
integrand on `Iθ` being `StrongEps.integrableOn_mixed_sq_rpow6`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary angular facts -/

/-- `sin(2θ) > 0` on the open angular interval. -/
private lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `(s ^ a) ^ 2 = s ^ (2 * a)` for `s ≥ 0`. -/
private lemma rpow_sq {s a : ℝ} (hs : 0 ≤ s) : (s ^ a) ^ 2 = s ^ (2 * a) := by
  rw [← Real.rpow_two (s ^ a), ← Real.rpow_mul hs a 2,
    show a * 2 = 2 * a by ring]

/-- `s ^ 2 · s ^ (-γ) = s ^ (2 - γ)` for `s > 0`. -/
private lemma sq_mul_rpow_neg {s γ : ℝ} (hs : 0 < s) : s ^ 2 * s ^ (-γ) = s ^ (2 - γ) := by
  rw [← Real.rpow_two, ← Real.rpow_add hs,
    show (2 : ℝ) + -γ = 2 - γ by ring]

/-- `(s·a) ^ 2 · s ^ (-γ) = a ^ 2 · s ^ (2 - γ)` for `s > 0`. -/
private lemma mul_sq_mul_rpow_neg {s a γ : ℝ} (hs : 0 < s) :
    (s * a) ^ 2 * s ^ (-γ) = a ^ 2 * s ^ (2 - γ) := by
  rw [mul_pow, ← sq_mul_rpow_neg hs]
  ring

/-! ## The one-dimensional Cauchy–Schwarz rate lemma -/

/-- **The endpoint rate from the weighted angular `L²` bound.**  If `g` is differentiable on
`(0, π/2)` with derivative `g'`, continuous on `[a,b] ⊂ (0,π/2)`, and
`∫_a^b g'² sin(2·)^{2-γ} ≤ M` with `1 < γ ≤ 2`, then

  `|g b - g a| ≤ √M · √(2(π/4)^{2-γ}/(γ-1)) · (b-a)^{(γ-1)/2}`. -/
private theorem cs_rate {γ M a b : ℝ} (hγ1 : 1 < γ) (hγ2 : γ ≤ 2) (hM : 0 ≤ M)
    {g g' : ℝ → ℝ}
    (hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' x) x)
    (hcont : ContinuousOn g' (Set.uIcc a b))
    (ha : 0 < a) (hab : a < b) (hb : b < Real.pi / 2)
    (hint : ∫ x in a..b, (g' x) ^ 2 * (Real.sin (2 * x)) ^ (2 - γ) ≤ M) :
    |g b - g a| ≤ Real.sqrt M * Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1))
      * (b - a) ^ ((γ - 1) / 2) := by
  have hγm1 : 0 < γ - 1 := by linarith
  have hsin : ∀ x ∈ Set.uIcc a b, 0 < Real.sin (2 * x) := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [Real.pi_pos, hx.2])
  -- the fundamental theorem of calculus on `[a,b]`
  have hder' : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    exact hder x ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hFTC : ∫ x in a..b, g' x = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder' hcont.intervalIntegrable
  -- the two Cauchy–Schwarz factors
  set A₁ : ℝ → ℝ := fun x => g' x * (Real.sin (2 * x)) ^ ((2 - γ) / 2) with hA₁
  set A₂ : ℝ → ℝ := fun x => (Real.sin (2 * x)) ^ ((γ - 2) / 2) with hA₂
  have hsincont : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.uIcc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcont₁ : ContinuousOn A₁ (Set.uIcc a b) :=
    hcont.mul (hsincont.rpow_const (fun x hx => Or.inl (ne_of_gt (hsin x hx))))
  have hcont₂ : ContinuousOn A₂ (Set.uIcc a b) :=
    hsincont.rpow_const (fun x hx => Or.inl (ne_of_gt (hsin x hx)))
  have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab.le hcont₁ hcont₂
  -- pointwise identities
  have hprod : ∀ x ∈ Set.uIcc a b, A₁ x * A₂ x = g' x := by
    intro x hx
    have hs := hsin x hx
    have h1 : (Real.sin (2 * x)) ^ ((2 - γ) / 2) * (Real.sin (2 * x)) ^ ((γ - 2) / 2) = 1 := by
      rw [← Real.rpow_add hs, show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero]
    simp only [hA₁, hA₂]
    rw [mul_assoc, h1, mul_one]
  have hsq₁ : ∀ x ∈ Set.uIcc a b, (A₁ x) ^ 2 = (g' x) ^ 2 * (Real.sin (2 * x)) ^ (2 - γ) := by
    intro x hx
    have hs := hsin x hx
    simp only [hA₁]
    rw [mul_pow, rpow_sq hs.le, show 2 * ((2 - γ) / 2) = 2 - γ by ring]
  have hsq₂ : ∀ x ∈ Set.uIcc a b, (A₂ x) ^ 2 = (Real.sin (2 * x)) ^ (γ - 2) := by
    intro x hx
    have hs := hsin x hx
    simp only [hA₂]
    rw [rpow_sq hs.le, show 2 * ((γ - 2) / 2) = γ - 2 by ring]
  have hprodI : ∫ x in a..b, A₁ x * A₂ x = ∫ x in a..b, g' x :=
    intervalIntegral.integral_congr hprod
  have hsq₁I : ∫ x in a..b, (A₁ x) ^ 2
      = ∫ x in a..b, (g' x) ^ 2 * (Real.sin (2 * x)) ^ (2 - γ) :=
    intervalIntegral.integral_congr hsq₁
  have hsq₂I : ∫ x in a..b, (A₂ x) ^ 2 = ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2) :=
    intervalIntegral.integral_congr hsq₂
  -- the `sin^{γ-2}` integral
  have hKnn : 0 ≤ 2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1) :=
    div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [Real.pi_pos]) _)) hγm1.le
  have hsinInt : ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2)
      ≤ 2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1) * (b - a) ^ (γ - 1) := by
    have h := Work.FTS_RegExport.THL.integral_sin_two_rpow_le (p := γ - 1)
      (by linarith) (by linarith) ha hab.le hb
    rwa [show γ - 1 - 1 = γ - 2 by ring, show 1 - (γ - 1) = 2 - γ by ring] at h
  have hsqrt₂ : Real.sqrt (∫ x in a..b, (A₂ x) ^ 2)
      ≤ Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1)) * (b - a) ^ ((γ - 1) / 2) := by
    have hA2le : ∫ x in a..b, (A₂ x) ^ 2
        ≤ 2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1) * (b - a) ^ (γ - 1) := by
      rw [hsq₂I]; exact hsinInt
    have h1 : Real.sqrt (∫ x in a..b, (A₂ x) ^ 2)
        ≤ Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1) * (b - a) ^ (γ - 1)) :=
      Real.sqrt_le_sqrt hA2le
    have h2 : Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1) * (b - a) ^ (γ - 1))
        = Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1)) * (b - a) ^ ((γ - 1) / 2) := by
      rw [Real.sqrt_mul hKnn]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ b - a),
        show (γ - 1) * (1 / 2) = (γ - 1) / 2 by ring]
    rw [h2] at h1; exact h1
  have hsqrt₁ : Real.sqrt (∫ x in a..b, (A₁ x) ^ 2) ≤ Real.sqrt M := by
    refine Real.sqrt_le_sqrt ?_
    rw [hsq₁I]; exact hint
  calc |g b - g a| = |∫ x in a..b, g' x| := by rw [hFTC]
    _ = |∫ x in a..b, A₁ x * A₂ x| := by rw [hprodI]
    _ ≤ Real.sqrt (∫ x in a..b, (A₁ x) ^ 2) * Real.sqrt (∫ x in a..b, (A₂ x) ^ 2) := hcs
    _ ≤ Real.sqrt M * (Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1))
          * (b - a) ^ ((γ - 1) / 2)) :=
        mul_le_mul hsqrt₁ hsqrt₂ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt M * Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1))
          * (b - a) ^ ((γ - 1) / 2) := by ring

/-! ## The target -/

theorem classCSinRate {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |f z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α f
          * (min θ (Real.pi / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2) := by
  obtain ⟨Csl, hCslpos, hsl⟩ := Work.FTS.StrongPersist.N6.sliceAng_le6
  have hγ1 : 1 < Work.Spaces.gam α := by
    have h := Work.Spaces.gam_sub_one α; linarith
  have hγ2 : Work.Spaces.gam α ≤ 2 := by
    have h := Work.Spaces.gam_sub_one α; linarith
  have hp : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one α]; linarith
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hKpos : 0 < 2 * (Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (Work.Spaces.gam α - 1) :=
    div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hpi4 _)) hp
  refine ⟨Real.sqrt Csl * Real.sqrt
      (2 * (Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (Work.Spaces.gam α - 1)),
    mul_pos (Real.sqrt_pos.mpr hCslpos) (Real.sqrt_pos.mpr hKpos), ?_⟩
  intro f hf z hz θ hθ
  have hF : Work.FTS.EllipticEst.SmoothOpen f := hf.reg
  have h6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf.reg 6 (by norm_num) hf.mem
  -- ## the slice derivative and its continuity
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun y : ℝ => f z y) (Work.Spaces.pth f z x) x := by
    intro x hx
    have hc0 : ContDiffOn ℝ Work.Stability.smoothOrder (fun y : ℝ => f z y)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hF.curry_θ hz
    have hc : ContDiffOn ℝ 1 (fun y : ℝ => f z y) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hc0.of_le (WithTop.coe_le_coe.mpr le_top)
    have hd1 : DifferentiableOn ℝ (fun y : ℝ => f z y) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hc.differentiableOn one_ne_zero
    have hdiff : DifferentiableAt ℝ (fun y : ℝ => f z y) x :=
      hd1.differentiableAt (isOpen_Ioo.mem_nhds hx)
    simpa only [Work.Spaces.pth] using hdiff.hasDerivAt
  have hcont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < Real.pi / 2 →
      ContinuousOn (fun x : ℝ => Work.Spaces.pth f z x) (Set.uIcc a b) := by
    intro a b ha hab hb
    have hc0 : ContDiffOn ℝ Work.Stability.smoothOrder (fun y : ℝ => Work.Spaces.pth f z y)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hF.pth.curry_θ hz
    refine hc0.continuousOn.mono ?_
    rw [Set.uIcc_of_le hab]
    exact fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  -- ## the `z`-uniform angular slice bound, on sub-intervals
  have hslice : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < Real.pi / 2 →
      ∫ x in a..b, (Work.Spaces.pth f z x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α)
        ≤ Csl * Work.Spaces.HkSq α 6 f := by
    intro a b ha hab hb
    have hint : IntegrableOn (fun x : ℝ => (Work.Spaces.mixed 0 1 f z x) ^ 2
        * (Real.sin (2 * x)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
      Work.FTS.StrongEps.integrableOn_mixed_sq_rpow6 hF h6 0 1 (by norm_num) (by norm_num) hz
    have hcongr : ∫ x in a..b, (Work.Spaces.pth f z x) ^ 2
          * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α)
        = ∫ x in a..b, (Work.Spaces.mixed 0 1 f z x) ^ 2
          * (Real.sin (2 * x)) ^ (-(Work.Spaces.gam α)) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hab] at hx
      have hs : 0 < Real.sin (2 * x) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
          (by linarith [Real.pi_pos, hx.2])
      have hmix : Work.Spaces.mixed 0 1 f z x
          = Real.sin (2 * x) * Work.Spaces.pth f z x := rfl
      rw [hmix, Work.Spaces.pth]
      exact (mul_sq_mul_rpow_neg (a := deriv (fun y : ℝ => f z y) x)
        (γ := Work.Spaces.gam α) hs).symm
    rw [hcongr, intervalIntegral.integral_of_le hab]
    refine le_trans (setIntegral_mono_set hint
      (ae_restrict_of_forall_mem measurableSet_Icc fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
          (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
            (by linarith [Real.pi_pos, hx.2])) _))
      (Eventually.of_forall fun x hx =>
        ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩)) ?_
    exact hsl α f 0 1 hα hα1 hF h6 (by norm_num) (by norm_num) z hz
  -- ## the angular endpoint traces
  have htr0 : Tendsto (fun y : ℝ => f z y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := Work.FTS.H2.HQ.BdryTraces.tendsto_theta_zero (α := α) hα (k := 6) hf.tr
      (a := 0) (b := 0) (by norm_num) (z := z) hz
    simpa using h
  have htrpi : Tendsto (fun y : ℝ => f z y) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have h := Work.FTS.H2.HQ.BdryTraces.tendsto_theta_pi (α := α) hα (k := 6) hf.tr
      (a := 0) (b := 0) (by norm_num) (z := z) hz
    simpa using h
  -- ## the one-step estimate
  set B : ℝ := Real.sqrt (Csl * Work.Spaces.HkSq α 6 f)
    * Real.sqrt (2 * (Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (Work.Spaces.gam α - 1))
    with hBdef
  have hBnn : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hstep : ∀ {a b : ℝ}, 0 < a → a < b → b < Real.pi / 2 →
      |f z b - f z a| ≤ B * (b - a) ^ ((Work.Spaces.gam α - 1) / 2) := by
    intro a b ha hab hb
    have hM : 0 ≤ Csl * Work.Spaces.HkSq α 6 f :=
      mul_nonneg hCslpos.le (Work.Spaces.HkSq_nonneg α 6 f)
    have h1 := cs_rate hγ1 hγ2 hM hder (hcont ha hab.le hb) ha hab hb (hslice ha hab.le hb)
    rw [hBdef]
    exact h1
  -- ## the two endpoint rates
  have hR : |f z θ| ≤ B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2) := by
    have htend : Tendsto (fun t : ℝ => B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2)
        + |f z t|) (𝓝[<] (Real.pi / 2))
        (𝓝 (B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2))) := by
      have h := (tendsto_const_nhds (x := B * (Real.pi / 2 - θ)
        ^ ((Work.Spaces.gam α - 1) / 2))).add htrpi.abs
      simpa using h
    have hev : ∀ᶠ t in 𝓝[<] (Real.pi / 2),
        |f z θ| ≤ B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2) + |f z t| := by
      filter_upwards [Ioo_mem_nhdsLT hθ.2] with t ht
      have h1 : |f z t - f z θ| ≤ B * (t - θ) ^ ((Work.Spaces.gam α - 1) / 2) :=
        hstep hθ.1 ht.1 ht.2
      have h2 : (t - θ) ^ ((Work.Spaces.gam α - 1) / 2)
          ≤ (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2) :=
        Real.rpow_le_rpow (le_of_lt (sub_pos.mpr ht.1)) (sub_le_sub_right ht.2.le θ)
          (div_nonneg hp.le (by norm_num))
      have h3 : B * (t - θ) ^ ((Work.Spaces.gam α - 1) / 2)
          ≤ B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2) :=
        mul_le_mul_of_nonneg_left h2 hBnn
      calc |f z θ| = |f z θ - f z t + f z t| := by ring_nf
        _ ≤ |f z θ - f z t| + |f z t| := abs_add_le _ _
        _ = |f z t - f z θ| + |f z t| := by rw [abs_sub_comm]
        _ ≤ B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2) + |f z t| := by linarith
    exact ge_of_tendsto htend hev
  have hL : |f z θ| ≤ B * θ ^ ((Work.Spaces.gam α - 1) / 2) := by
    have htend : Tendsto (fun t : ℝ => B * θ ^ ((Work.Spaces.gam α - 1) / 2) + |f z t|)
        (𝓝[>] (0 : ℝ)) (𝓝 (B * θ ^ ((Work.Spaces.gam α - 1) / 2))) := by
      have h := (tendsto_const_nhds (x := B * θ ^ ((Work.Spaces.gam α - 1) / 2))).add htr0.abs
      simpa using h
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        |f z θ| ≤ B * θ ^ ((Work.Spaces.gam α - 1) / 2) + |f z t| := by
      filter_upwards [Ioo_mem_nhdsGT hθ.1] with t ht
      have h1 : |f z θ - f z t| ≤ B * (θ - t) ^ ((Work.Spaces.gam α - 1) / 2) :=
        hstep ht.1 ht.2 hθ.2
      have h2 : (θ - t) ^ ((Work.Spaces.gam α - 1) / 2)
          ≤ θ ^ ((Work.Spaces.gam α - 1) / 2) :=
        Real.rpow_le_rpow (le_of_lt (sub_pos.mpr ht.2)) (sub_le_self θ ht.1.le)
          (div_nonneg hp.le (by norm_num))
      have h3 : B * (θ - t) ^ ((Work.Spaces.gam α - 1) / 2)
          ≤ B * θ ^ ((Work.Spaces.gam α - 1) / 2) :=
        mul_le_mul_of_nonneg_left h2 hBnn
      calc |f z θ| = |f z θ - f z t + f z t| := by ring_nf
        _ ≤ |f z θ - f z t| + |f z t| := abs_add_le _ _
        _ ≤ B * θ ^ ((Work.Spaces.gam α - 1) / 2) + |f z t| := by linarith
    exact ge_of_tendsto htend hev
  -- ## assembly
  have hB : B = Real.sqrt Csl * Real.sqrt
      (2 * (Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (Work.Spaces.gam α - 1))
      * Work.FTS.StrongGlobal.Xn6 α f := by
    rw [hBdef, Work.FTS.StrongGlobal.Xn6, Work.Spaces.HkNorm,
      Real.sqrt_mul hCslpos.le (Work.Spaces.HkSq α 6 f)]
    ring
  rw [hB] at hL hR
  rcases le_total θ (Real.pi / 2 - θ) with h | h
  · rw [min_eq_left h]; exact hL
  · rw [min_eq_right h]; exact hR

end Work.FTS_EllLimOK.ProducerH.BoxAux
