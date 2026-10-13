/-
# `|L₁₂ f z - L₁₂ g z| ≤ C · |f - g|_{ℋ⁴} / √(1+z)`

The Lipschitz (in `f`) decay bound for the zero mode `L₁₂` of the fundamental model, at the
honest `ℋ⁴`-order, *uniformly in `α`* and with the **bounded** decay profile `1/√(1+z)`
(whereas `Work.FTS.StrongEps.L12AbsLe` gives the sharp `1/√z`, which blows up at `z = 0`).

With `L₁₂ f z = ∫_{s>z} ∫_{θ∈Iθ} K(θ)·f(s,θ)/s dθ ds` (`K(θ) = 3 sin θ cos²θ`) and
`Wlam s = 1/(s·w s) = s/(1+s)²`, the route is the Cauchy–Schwarz one of
`Work.FTS.GalBasis.cc.abs_L12_le_HkNorm`, with two modifications:

* **order `4`** instead of order `0`: the pointwise bound on the density is the already
  proved `Work.FTS.GalBasis.cc.abs_L12dens_le`
  (`|L12dens h s| ≤ Wlam s · BK · √(∫_θ HkIntegrand α 4 h s θ)`), so the norm on the right
  is exactly `Xn α h = HkNorm α 4 h = √(HkSq α 4 h)`;
* **the weight bound `∫_{s>z} Wlam² ≤ 1/(1+z)`** instead of `1/z`: since
  `Wlam s² = s²/(1+s)⁴ ≤ 1/(1+s)²` for `s ≥ 0` (because `s ≤ 1+s`), and
  `∫_{s>z} (1+s)^{-2} ds = 1/(1+z)` by the FTC on `x ↦ -(1+x)^{-1}`, whose derivative
  `-(1+x)^{-2} ≤ 0` is automatically integrable
  (`MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos`).  This is what makes the bound
  valid down to `z = 0` (where it reads `C·|h|_{ℋ⁴}`).

Finally `L₁₂ f z - L₁₂ g z = L₁₂ (f - g) z` for `z ≥ 0` by the proved
`Work.FTS.StrongEps.EComparison.L12_sub_HkMem`, so the Lipschitz statement reduces to the
estimate for the difference datum.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false

/-! ## The two elementary inputs: a pointwise comparison and a tail integral -/

/-- `Wlam s² = s²/(1+s)⁴ ≤ 1/(1+s)²` for `s ≥ 0`: since `s ≤ 1+s`, the numerator `s²` is at
most `(1+s)²`, so the quotient is at most `(1+s)²/(1+s)⁴ = 1/(1+s)²`. -/
lemma Wlam_sq_le_inv_sq (s : ℝ) (hs : 0 ≤ s) :
    Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ 1 / (1 + s) ^ 2 := by
  have hle : s ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
  have hpos : 0 < (1 + s) ^ 2 := by positivity
  rw [Work.FTS.GalBasis.cc.Wlam, div_pow, show ((1 + s) ^ 2) ^ 2 = (1 + s) ^ 4 by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc s ^ 2 * (1 + s) ^ 2 ≤ (1 + s) ^ 2 * (1 + s) ^ 2 :=
        mul_le_mul_of_nonneg_right hle hpos.le
    _ = 1 * (1 + s) ^ 4 := by ring

/-- The integrand of the tail integral: `x ↦ 1/(1+x)²` is the derivative of
`x ↦ (1+x)^{-1}`, which is positive and decreasing to `0` at `+∞`, so its derivative
(negated) is automatically integrable on `(a,∞)` by
`MeasureTheory.integrableOn_Ioi_deriv_of_nonpos`. -/
private lemma integrableOn_Ioi_one_add_sq_inv_aux (a : ℝ) (_ha : 0 ≤ a) :
    MeasureTheory.IntegrableOn (fun x : ℝ => 1 / (1 + x) ^ 2) (Set.Ioi a) ∧
      ∫ x in Set.Ioi a, 1 / (1 + x) ^ 2 = 1 / (1 + a) := by
  have hg'neg : ∀ x ∈ Set.Ioi a, -(1 / (1 + x) ^ 2) ≤ 0 := by
    intro x _
    have h : 0 ≤ 1 / (1 + x) ^ 2 := by positivity
    linarith
  have hcont : ContinuousWithinAt (fun x : ℝ => (1 + x)⁻¹) (Set.Ici a) a := by
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.inv₀ ?_ ?_
    · fun_prop
    · linarith
  have hlim : Tendsto (fun x : ℝ => (1 + x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_const_nhds.add_atTop tendsto_id)
  have hderiv : ∀ x ∈ Set.Ioi a,
      HasDerivAt (fun x : ℝ => (1 + x)⁻¹) (-(1 / (1 + x) ^ 2)) x := by
    intro x hx
    have hx0 : (1 + x) ≠ 0 := by
      simp only [Set.mem_Ioi] at hx
      linarith
    have h := (hasDerivAt_inv hx0).comp x ((hasDerivAt_id x).const_add 1)
    convert h using 1
    funext y
    simp only [Function.comp_apply]
    ring_nf
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => -(1 / (1 + x) ^ 2)) (Set.Ioi a) :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonpos hcont hderiv hg'neg hlim
  refine ⟨by simpa using hint.neg, ?_⟩
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hg'neg hlim
  rw [MeasureTheory.integral_neg, zero_sub] at h
  rw [one_div]
  linarith [h]

/-- `x ↦ 1/(1+x)²` is integrable on `(a,∞)` for `a ≥ 0`. -/
lemma integrableOn_Ioi_one_add_sq_inv (a : ℝ) (ha : 0 ≤ a) :
    MeasureTheory.IntegrableOn (fun x : ℝ => 1 / (1 + x) ^ 2) (Set.Ioi a) :=
  (integrableOn_Ioi_one_add_sq_inv_aux a ha).1

/-- **The tail integral**: `∫_{x>a} (1+x)^{-2} dx = 1/(1+a)` for `a ≥ 0`.  (FTC on
`x ↦ -(1+x)^{-1}`, whose derivative is `(1+x)^{-2}` and which tends to `0` at `+∞`.) -/
lemma integral_Ioi_one_add_sq_inv (a : ℝ) (ha : 0 ≤ a) :
    ∫ x in Set.Ioi a, 1 / (1 + x) ^ 2 = 1 / (1 + a) :=
  (integrableOn_Ioi_one_add_sq_inv_aux a ha).2

/-! ## Cauchy–Schwarz in the radial variable with the sharp weight bound `1/(1+z)` -/

/-- Cauchy–Schwarz in the radial variable with the weight bound `∫_{s>z} Wlam² ≤ 1/(1+z)`,
valid for `z ≥ 0`.  No measurability of `A` is assumed: the argument uses the measurable
surrogate `B = √(A²)`, which agrees with `A` on `(z,∞)` because `A ≥ 0` there. -/
lemma Wlam_mul_le_sqrt_one_add {A : ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (hnn : ∀ s ∈ Set.Ioi z, 0 ≤ A s)
    (hint : MeasureTheory.IntegrableOn (fun s => A s ^ 2) (Set.Ioi z)) :
    ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Real.sqrt (1 / (1 + z)) * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) := by
  -- the measurable surrogate `B = √(A²)`, equal to `A` on `(z,∞)`
  set B : ℝ → ℝ := fun s => Real.sqrt (A s ^ 2) with hB
  have hBnn : ∀ s, 0 ≤ B s := fun s => Real.sqrt_nonneg _
  have hBeq : B =ᵐ[volume.restrict (Set.Ioi z)] A := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [hB]
    exact Real.sqrt_sq (hnn s hs)
  have hBsq : ∀ s, B s ^ 2 = A s ^ 2 := fun s => by
    change Real.sqrt (A s ^ 2) ^ 2 = A s ^ 2
    exact Real.sq_sqrt (sq_nonneg (A s))
  have hB_aesm : AEStronglyMeasurable B (volume.restrict (Set.Ioi z)) := by
    change AEStronglyMeasurable (fun s => Real.sqrt (A s ^ 2)) (volume.restrict (Set.Ioi z))
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hB_int : MeasureTheory.IntegrableOn (fun s => B s ^ 2) (Set.Ioi z) :=
    hint.congr_fun (fun s _ => (hBsq s).symm) measurableSet_Ioi
  have hB_memLp : MemLp B 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hB_aesm).mpr hB_int
  -- the radial weight
  have hWlam_aesm : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi z)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi z))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi z) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using
      Work.Elliptic.psi_sq_integrable_aux.mono_set (fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢
        linarith)
  have hWlam_memLp : MemLp Work.FTS.GalBasis.cc.Wlam 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hWlam_aesm).mpr hWlam_sq_int
  -- the sharp weight bound `∫_{s>z} Wlam² ≤ 1/(1+z)`
  have hWlam_sq_le : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ 1 / (1 + z) := by
    have h1 : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2
        ≤ ∫ s in Set.Ioi z, 1 / (1 + s) ^ 2 :=
      MeasureTheory.setIntegral_mono_on hWlam_sq_int (integrableOn_Ioi_one_add_sq_inv z hz)
        measurableSet_Ioi (fun s hs =>
          Wlam_sq_le_inv_sq s (le_of_lt (lt_of_le_of_lt hz hs)))
    rw [integral_Ioi_one_add_sq_inv z hz] at h1
    exact h1
  -- Cauchy–Schwarz for the two measurable factors
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
    (u := Work.FTS.GalBasis.cc.Wlam) (v := B) (s := Set.Ioi z) hWlam_memLp hB_memLp
  have hprod : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s
      = |∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s| := by
    rw [abs_of_nonneg]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_of_le_of_lt hz hs)))
      (hBnn s)
  calc ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      = ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hBeq] with s hs
        rw [hs]
    _ = |∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s| := hprod
    _ ≤ Real.sqrt (∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2)
          * Real.sqrt (∫ s in Set.Ioi z, B s ^ 2) := hcs
    _ = Real.sqrt (∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2)
          * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) := by
        rw [MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun s => hBsq s)]
    _ ≤ Real.sqrt (1 / (1 + z)) * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hWlam_sq_le) (Real.sqrt_nonneg _)

/-! ## The integrated bound on the tail `(z,∞)` -/

/-- **The main estimate**, at order `4` and for `z ≥ 0`:
`∫_{s>z} |L₁₂-density h s| ds ≤ BK · √(1/(1+z)) · √(HkSq α 4 h)`. -/
lemma tail_abs_L12dens_le {α : ℝ} {h : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 h)
    {z : ℝ} (hz : 0 ≤ z) :
    ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / (1 + z))
        * Real.sqrt (Work.Spaces.HkSq α 4 h) := by
  -- the angular marginal `H` and its square root `A`
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 h s θ
  have hAnn : ∀ s, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  -- integrability of `H` on `[0,∞)` and hence on `(z,∞)`
  have hH_int_Iz : MeasureTheory.IntegrableOn H Work.Spaces.Iz := by
    simpa only [hH] using hmem.2
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := by
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith
  have hH_int : MeasureTheory.IntegrableOn H (Set.Ioi z) := hH_int_Iz.mono_set hsub
  have hA2_int : MeasureTheory.IntegrableOn (fun s => A s ^ 2) (Set.Ioi z) := by
    refine hH_int.congr_fun (fun s _ => ?_) measurableSet_Ioi
    rw [hA]
    exact (Real.sq_sqrt (hHnn s)).symm
  -- `∫_{s>z} A² ≤ HkSq α 4 h`
  have hA2_le : ∫ s in Set.Ioi z, A s ^ 2 ≤ Work.Spaces.HkSq α 4 h := by
    have h1 : ∫ s in Set.Ioi z, A s ^ 2 = ∫ s in Set.Ioi z, H s :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]
        exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi z, H s ≤ ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_mono_set hH_int_Iz (Filter.Eventually.of_forall hHnn)
        (Filter.Eventually.of_forall fun x hx => hsub hx)
    have h3 : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α 4 h := by
      rw [hH]
      rfl
    linarith
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Real.sqrt (1 / (1 + z)) * Real.sqrt (Work.Spaces.HkSq α 4 h) :=
    le_trans (Wlam_mul_le_sqrt_one_add hz (fun s _ => hAnn s) hA2_int)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA2_le) (Real.sqrt_nonneg _))
  -- the pointwise bound on the density
  have hbd : ∀ s ∈ Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * A s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hz hs
    have hb := Work.FTS.GalBasis.cc.abs_L12dens_le α h hmem hs0
    simpa only [hA, hH] using hb
  -- the majorant is integrable (AM–GM) and the bound passes to the integral
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi z)) := by
    rw [hA]
    exact (hH_int.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hWlam_aesm : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi z)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi z))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi z) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using
      Work.Elliptic.psi_sq_integrable_aux.mono_set (fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢
        linarith)
  have hAMGM : ∀ s ∈ Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Work.FTS.GalBasis.cc.Wlam s ^ 2 + A s ^ 2 := by
    intro s _
    nlinarith [sq_nonneg (Work.FTS.GalBasis.cc.Wlam s - A s)]
  have hsum_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2 + A s ^ 2) (Set.Ioi z) :=
    hWlam_sq_int.add hA2_int
  have hdom_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s))
      (Set.Ioi z) := by
    refine MeasureTheory.Integrable.mono' (hsum_int.const_mul Work.FTS.GalBasis.cc.BK) ?_ ?_
    · exact (hWlam_aesm.mul hA_aesm).const_mul Work.FTS.GalBasis.cc.BK
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hnn : 0 ≤ Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) :=
        mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg
          (mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_of_le_of_lt hz hs)))
            (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) Work.FTS.GalBasis.cc.BK_nonneg
  have h2 : ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      |Work.Construction.L12dens h s|
        ≤ Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun s hs => ?_
    calc |Work.Construction.L12dens h s|
        ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * A s) := hbd s hs
      _ = Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by ring
  have h3 : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s)
      = Work.FTS.GalBasis.cc.BK * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s :=
    MeasureTheory.integral_const_mul Work.FTS.GalBasis.cc.BK _
  calc ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := h2
    _ = Work.FTS.GalBasis.cc.BK * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s := h3
    _ ≤ Work.FTS.GalBasis.cc.BK * (Real.sqrt (1 / (1 + z)) * Real.sqrt (Work.Spaces.HkSq α 4 h)) :=
        mul_le_mul_of_nonneg_left hCS Work.FTS.GalBasis.cc.BK_nonneg
    _ = Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / (1 + z)) * Real.sqrt (Work.Spaces.HkSq α 4 h) := by
        ring

/-! ## The Lipschitz statement -/

theorem L12_z_lipschitz : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ f g : Work.FTS.Galerkin.Fn,
    Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
    Work.FTS.VocabO.HQo α 4 (fun z θ => f z θ - g z θ) →
    ∀ z : ℝ, 0 ≤ z →
      |Work.Construction.L12 f z - Work.Construction.L12 g z|
        ≤ C / Real.sqrt (1 + z) * Work.FTS.Nonlin.Xn α (fun z θ => f z θ - g z θ) := by
  refine ⟨Work.FTS.GalBasis.cc.BK + 1, by linarith [Work.FTS.GalBasis.cc.BK_nonneg], ?_⟩
  intro α _ f g hf hg hfg z hz
  -- the difference datum
  set h : ℝ → ℝ → ℝ := fun z θ => f z θ - g z θ with hh
  have hmemh : Work.Spaces.HkMem α 4 h := hfg.2
  -- additivity of `L₁₂` in the first argument, for `z ≥ 0`
  have hsub : Work.Construction.L12 f z - Work.Construction.L12 g z
      = Work.Construction.L12 h z := by
    refine (Work.FTS.StrongEps.EComparison.L12_sub_HkMem hf.1 hg.1 hf.2 hg.2 z ?_).symm
    simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
  have h1 : |Work.Construction.L12 h z|
      ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens h s| := by
    have hL12 : Work.Construction.L12 h z
        = ∫ s in Set.Ioi z, Work.Construction.L12dens h s := rfl
    rw [hL12]
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi z))
        (f := fun s => Work.Construction.L12dens h s))
  have h2 : ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / (1 + z))
        * Real.sqrt (Work.Spaces.HkSq α 4 h) :=
    tail_abs_L12dens_le hmemh hz
  have h3 : Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / (1 + z))
        * Real.sqrt (Work.Spaces.HkSq α 4 h)
      = Work.FTS.GalBasis.cc.BK * Real.sqrt (Work.Spaces.HkSq α 4 h)
        / Real.sqrt (1 + z) := by
    rw [Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num), Real.sqrt_one]
    ring
  have h4 : Work.FTS.GalBasis.cc.BK * Real.sqrt (Work.Spaces.HkSq α 4 h)
        / Real.sqrt (1 + z)
      ≤ (Work.FTS.GalBasis.cc.BK + 1) * Real.sqrt (Work.Spaces.HkSq α 4 h)
        / Real.sqrt (1 + z) := by
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hXn : Work.FTS.Nonlin.Xn α h = Real.sqrt (Work.Spaces.HkSq α 4 h) := rfl
  have hmain : |Work.Construction.L12 f z - Work.Construction.L12 g z|
      ≤ (Work.FTS.GalBasis.cc.BK + 1) / Real.sqrt (1 + z)
        * Work.FTS.Nonlin.Xn α h := by
    calc |Work.Construction.L12 f z - Work.Construction.L12 g z|
        = |Work.Construction.L12 h z| := by rw [hsub]
      _ ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens h s| := h1
      _ ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / (1 + z))
            * Real.sqrt (Work.Spaces.HkSq α 4 h) := h2
      _ = Work.FTS.GalBasis.cc.BK * Real.sqrt (Work.Spaces.HkSq α 4 h)
            / Real.sqrt (1 + z) := h3
      _ ≤ (Work.FTS.GalBasis.cc.BK + 1) * Real.sqrt (Work.Spaces.HkSq α 4 h)
            / Real.sqrt (1 + z) := h4
      _ = (Work.FTS.GalBasis.cc.BK + 1) / Real.sqrt (1 + z) * Work.FTS.Nonlin.Xn α h := by
          rw [hXn]
          ring
  simpa only [hh] using hmain

end Work.FTS.StrongEps.L12
