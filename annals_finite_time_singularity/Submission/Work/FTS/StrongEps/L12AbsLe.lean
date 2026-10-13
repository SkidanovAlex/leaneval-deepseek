/-
# The decay bound `|L₁₂ f z| ≤ C √(ℋ⁰-norm f)/√z`

This file proves `Work.FTS.StrongEps.L12AbsLe`:

`∃ C > 0, ∀ f, HkMem α 0 f → ∀ z > 0, |L₁₂ f z| ≤ C · √(HkSq α 0 f)/√z`.

With `L₁₂ f z = ∫_{s>z} ∫_{θ∈Iθ} K(θ)·f(s,θ)/s dθ ds` (`K(θ) = 3 sin θ cos²θ`), the proof is
the `k = 0`, arbitrary-`z` version of the Cauchy–Schwarz route already used for
`Work.FTS.GalBasis.cc.abs_L12_le_HkNorm` (`z = 0`, `k = 4`):

writing `Sw θ = sin(2θ)^{η/2}`, `Gaz f s θ = f s θ · (w s / Sw θ)` and
`Wlam s = 1/(s·w s) = s/(1+s)²`, the density integrand factorises as

  `K θ · f s θ/s = Wlam s · (K θ · Sw θ · Gaz f s θ)`

(both sides vanish at `θ = 0, π/2`, where `Sw` and `K` vanish).  Then

* angular Cauchy–Schwarz
  (`Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen`, order `k = 0`):
  `|∫_θ K·Sw·Gaz| ≤ BK·√(∫_θ HkIntegrand α 0 f s θ)`, with
  `BK = √(∫_θ (K·Sw)²)` (finite, `α`-free);
* radial Cauchy–Schwarz against `Wlam` restricted to `(z,∞)`, with the **sharp** weight
  bound `∫_{s>z} Wlam² ≤ ∫_{s>z} s^{-2} = 1/z` (valid because `Wlam s² ≤ s^{-2}` for `s > 0`);
  this is what produces the `1/√z` decay (the global bound `∫_{(0,∞)} Wlam² = W2` of
  `Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi` would only give a `z`-independent
  constant);
* `∫_{s>z} ∫_θ HkIntegrand α 0 f s θ ≤ HkSq α 0 f`, because `(z,∞) ⊆ Iz = [0,∞)`
  (`HkMem α 0 f` provides the integrability of the marginal).

At order `k = 0` the `α`-dependent part of `HkIntegrand` is empty, so the constant is
absolute (independent of `α`).  Measurability of the datum is never assumed: the only
functions whose measurability is used are the continuous weight `Wlam` and the square root
`√(∫_θ HkIntegrand)`, which is measurable because the marginal is integrable; where the
Bochner integral is the junk value `0`, the estimate holds trivially.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.Construction.Defs
import Submission.Work.FM.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-! ## The pointwise bound on the density -/

/-- The `L₁₂`-density at order `0`: angular Cauchy–Schwarz
(`Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen` with `k = 0`) combined with the
factorisation `L12dens f s = Wlam s · ∫_θ K·Sw·Gaz f s ·` of
`Work.FTS.GalBasis.cc.L12dens_eq_weighted`. -/
lemma abs_L12dens_le_zero (α : ℝ) (f : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s)
    (hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 f s θ)
      Work.Spaces.Iθ) :
    |Work.Construction.L12dens f s|
      ≤ Work.FTS.GalBasis.cc.Wlam s
        * (Work.FTS.GalBasis.cc.BK * Real.sqrt
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f s θ)) := by
  rw [Work.FTS.GalBasis.cc.L12dens_eq_weighted f hs, abs_mul,
    abs_of_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le)]
  exact mul_le_mul_of_nonneg_left
    (Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen α 0 f hint)
    (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le)

/-! ## The sharp radial Cauchy–Schwarz bound -/

/-- The pointwise comparison behind the sharp radial weight bound:
`Wlam s² = s²/(1+s)⁴ ≤ s^{-2}` for `s > 0`. -/
lemma Wlam_sq_le_rpow (s : ℝ) (hs : 0 < s) :
    Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ s ^ (-2 : ℝ) := by
  have h4 : s ^ 4 ≤ (1 + s) ^ 4 := pow_le_pow_left₀ hs.le (by linarith) 4
  have hid : ((1 + s) ^ 2) ^ 2 = (1 + s) ^ 4 := by ring
  have hmain : s ^ 2 / ((1 + s) ^ 2) ^ 2 ≤ 1 / s ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), hid]
    nlinarith [h4]
  have hred : s ^ (-2 : ℝ) = 1 / s ^ 2 := by
    rw [Real.rpow_neg hs.le, Real.rpow_two, inv_eq_one_div]
  rw [Work.FTS.GalBasis.cc.Wlam, div_pow, hred]
  exact hmain

/-- Cauchy–Schwarz in the radial variable, with the sharp weight bound
`∫_{s>z} Wlam² ≤ 1/z`.  No measurability of `A` is assumed: the argument uses the
measurable surrogate `B = √(A²)`, which agrees with `A` on `(z,∞)` because `A ≥ 0` there. -/
lemma Wlam_mul_le_sqrt {A : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hnn : ∀ s ∈ Set.Ioi z, 0 ≤ A s)
    (hint : MeasureTheory.IntegrableOn (fun s => A s ^ 2) (Set.Ioi z)) :
    ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) := by
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
  -- the sharp weight bound
  have hWlam_sq_le : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ 1 / z := by
    have h1 : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2
        ≤ ∫ s in Set.Ioi z, s ^ (-2 : ℝ) :=
      MeasureTheory.setIntegral_mono_of_nonneg (fun s _ => sq_nonneg _)
        (fun s hs => Wlam_sq_le_rpow s (lt_trans hz hs))
        (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hz)
    have h2 : ∫ s in Set.Ioi z, s ^ (-2 : ℝ) = 1 / z := by
      rw [integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hz,
        show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      ring
    linarith
  -- Cauchy–Schwarz for the two measurable factors
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
    (u := Work.FTS.GalBasis.cc.Wlam) (v := B) (s := Set.Ioi z) hWlam_memLp hB_memLp
  have hprod : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s
      = |∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s| := by
    rw [abs_of_nonneg]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_trans hz hs))) (hBnn s)
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
    _ ≤ Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hWlam_sq_le) (Real.sqrt_nonneg _)

/-! ## The integrated bound on the tail `(z,∞)` -/

/-- **The main estimate.**  For `f` with `HkMem α 0 f` and `z > 0`,
`∫_{s>z} |L₁₂-density f s| ds ≤ BK · √(1/z) · √(HkSq α 0 f)`. -/
lemma tail_abs_L12dens_le (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 0 f)
    {z : ℝ} (hz : 0 < z) :
    ∫ s in Set.Ioi z, |Work.Construction.L12dens f s|
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / z)
        * Real.sqrt (Work.Spaces.HkSq α 0 f) := by
  -- the angular marginal `H` and its square root `A`
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 f s θ
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
  -- `∫_{s>z} A² ≤ HkSq α 0 f`
  have hA2_le : ∫ s in Set.Ioi z, A s ^ 2 ≤ Work.Spaces.HkSq α 0 f := by
    have h1 : ∫ s in Set.Ioi z, A s ^ 2 = ∫ s in Set.Ioi z, H s :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]
        exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi z, H s ≤ ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_mono_set hH_int_Iz (Filter.Eventually.of_forall hHnn)
        (Filter.Eventually.of_forall fun x hx => hsub hx)
    have h3 : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α 0 f := by
      rw [hH]
      rfl
    linarith
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Real.sqrt (1 / z) * Real.sqrt (Work.Spaces.HkSq α 0 f) :=
    le_trans (Wlam_mul_le_sqrt hz (fun s _ => hAnn s) hA2_int)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA2_le) (Real.sqrt_nonneg _))
  -- the pointwise bound on the density
  have hbd : ∀ s ∈ Set.Ioi z, |Work.Construction.L12dens f s|
      ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * A s) := by
    intro s hs
    have hs0 : 0 < s := lt_trans hz hs
    have hb := abs_L12dens_le_zero α f hs0 (hmem.1 s (hsub hs))
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
          (mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_trans hz hs)))
            (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) Work.FTS.GalBasis.cc.BK_nonneg
  have h2 : ∫ s in Set.Ioi z, |Work.Construction.L12dens f s|
      ≤ ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      |Work.Construction.L12dens f s|
        ≤ Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun s hs => ?_
    calc |Work.Construction.L12dens f s|
        ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * A s) := hbd s hs
      _ = Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by ring
  have h3 : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s)
      = Work.FTS.GalBasis.cc.BK * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s :=
    MeasureTheory.integral_const_mul Work.FTS.GalBasis.cc.BK _
  calc ∫ s in Set.Ioi z, |Work.Construction.L12dens f s|
      ≤ ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := h2
    _ = Work.FTS.GalBasis.cc.BK * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s := h3
    _ ≤ Work.FTS.GalBasis.cc.BK * (Real.sqrt (1 / z) * Real.sqrt (Work.Spaces.HkSq α 0 f)) :=
        mul_le_mul_of_nonneg_left hCS Work.FTS.GalBasis.cc.BK_nonneg
    _ = Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / z) * Real.sqrt (Work.Spaces.HkSq α 0 f) := by
        ring

/-! ## The theorem -/

theorem L12AbsLe (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.Spaces.HkMem α 0 f → ∀ z : ℝ, 0 < z →
      |Work.Construction.L12 f z| ≤ C * Real.sqrt (Work.Spaces.HkSq α 0 f) / Real.sqrt z := by
  refine ⟨Work.FTS.GalBasis.cc.BK + 1,
    by linarith [Work.FTS.GalBasis.cc.BK_nonneg], ?_⟩
  intro f hmem z hz
  have h1 : |Work.Construction.L12 f z|
      ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens f s| := by
    have hL12 : Work.Construction.L12 f z
        = ∫ s in Set.Ioi z, Work.Construction.L12dens f s := rfl
    rw [hL12]
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi z))
        (f := fun s => Work.Construction.L12dens f s))
  have h2 := tail_abs_L12dens_le α f hmem hz
  have h3 : Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / z) * Real.sqrt (Work.Spaces.HkSq α 0 f)
      = Work.FTS.GalBasis.cc.BK * Real.sqrt (Work.Spaces.HkSq α 0 f) / Real.sqrt z := by
    rw [Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num), Real.sqrt_one]
    ring
  have h4 : Work.FTS.GalBasis.cc.BK * Real.sqrt (Work.Spaces.HkSq α 0 f) / Real.sqrt z
      ≤ (Work.FTS.GalBasis.cc.BK + 1) * Real.sqrt (Work.Spaces.HkSq α 0 f)
          / Real.sqrt z := by
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg z)
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  calc |Work.Construction.L12 f z|
      ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens f s| := h1
    _ ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / z) * Real.sqrt (Work.Spaces.HkSq α 0 f) := h2
    _ = Work.FTS.GalBasis.cc.BK * Real.sqrt (Work.Spaces.HkSq α 0 f) / Real.sqrt z := h3
    _ ≤ (Work.FTS.GalBasis.cc.BK + 1) * Real.sqrt (Work.Spaces.HkSq α 0 f)
          / Real.sqrt z := h4

end Work.FTS.StrongEps
