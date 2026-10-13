/-
Copyright: work module for the Elgindi finite-time singularity project.

# `r ↦ F_*(F)(r)/r` is integrable on `(0,∞)` for an elliptic solution in `ℋ^k`

The angular moment of the solvability condition,

  `F_*(F)(z) = ∫_θ F(z,θ) sin θ cos²θ dθ`   (`Work.Elliptic.Fstar`),

controls the singular part `G_* = -(1/(4α))L₁₂(F)` of the elliptic estimates through the
radial integral `L₁₂(F)(z) = 3 ∫_z^∞ F_*(F)(r)/r dr` (`Work.Elliptic.L12rad`).  This file
proves that the integrand of that radial integral *is* `L¹` on the whole half-line:

  `IntegrableOn (fun r ↦ F_*(F)(r)/r) (Ioi 0)`,

for every source `F` which agrees on the open quadrant with `bslOp α Ψ`, where `Ψ` is a
solution of the elliptic problem in the sense of `Work.Elliptic.IsBslSol` and is smooth on
a neighbourhood of the closed quadrant (`Work.Spaces.SmoothNbhd`), and such that `F` is
honestly in `ℋ^k` (`Work.Spaces.HkMem α k F`).

## The argument

1. **Pointwise Cauchy–Schwarz (`Fstar_div_sq_le`).**  `F_*(F)(z)` is the pairing of
   `θ ↦ F(z,θ)·w(z)/sin(2θ)^{η/2}` with `θ ↦ sin(2θ)^{η/2} sin θ cos²θ`, divided by
   `w(z) = (1+z)²/z²`.  Cauchy–Schwarz in `θ` (available in the workspace as
   `PsiInt_sq_mul_w_le_open`, packaged for the moment `F_*` as
   `FstarDzIter_sq_mul_w_le_open` with `D_z^0 = id`) gives

     `F_*(F)(z)² · w(z)² ≤ (π/2) · ∫_θ HkIntegrand α 0 F z θ ≤ (π/2) · ∫_θ HkIntegrand α k F z θ`,

   because the `ℋ⁰`-integrand is the `i = 0` term of the `ℋ^k`-integrand.  Since
   `w(z)²z² = (1+z)⁴/z²` this is `(F_*(F)(z)/z)² ≤ (π/2)·A(z)·(z/(1+z)²)²` with
   `A(z) = ∫_θ HkIntegrand α k F z θ`.

2. **Integrability of the majorant (`aux_integrableOn_sq_div_one_add_sq`,
   `aux_integrableOn_sqrt_mul_of_integrableOn`).**  Taking square roots,

     `|F_*(F)(z)/z| ≤ √(π/2)·√(A(z))·z/(1+z)²`,

   and `L¹·L² ⟹ L¹` (AM–GM: `2√(A z)·|B z| ≤ A z + B z²`) reduces this to the
   integrability of `A` on `(0,∞)` — which is `hmem.2`, restricted from `[0,∞)` — and of
   the explicit function `(z/(1+z)²)²`, which decays like `z^{-2}`.

3. **Measurability (`aesm_Fstar_div`).**  The estimates are stated for sources which are
   *only* known to be `C^∞` on the open quadrant, and `ℋ^k`-membership alone does **not**
   make `F_*(F)` measurable (multiplying `F` by a non-measurable `{±1}`-valued radial
   factor leaves `HkIntegrand α 0` unchanged).  Here the elliptic law `bslOp α Ψ = F` on
   the open quadrant is what saves measurability: on `Iθ` the two functions agree except
   on the null set `{0,π/2}`, so `F_*(F)(z) = ∫_θ bslOp α Ψ z θ · sinθcos²θ dθ` for every
   `z > 0`, and the angular integral of a function which is continuous on the open quadrant
   is a.e. strongly measurable (`aestronglyMeasurable_integral_Itheta_Q0`).

The theorem is then `Integrable.mono'` against the integrable majorant
`√(π/2)·(√(A z)·z/(1+z)²)`, with `AEStronglyMeasurable` from step 3.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Fstar_sq_le
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.FstarSmooth

/-! ## Placeholders for the two delegated lemmas (exactly as requested) -/

private theorem aux_integrableOn_sq_div_one_add_sq :
    MeasureTheory.IntegrableOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2) (Set.Ioi 0) := by
  have hcont_Ioc : ContinuousOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2) (Set.Ioc (0:ℝ) 1) := by
    refine ContinuousOn.pow (ContinuousOn.div continuousOn_id
      ((continuousOn_const.add continuousOn_id).pow 2) ?_) 2
    intro z hz
    have hz' : (0 : ℝ) < 1 + z := by linarith [hz.1]
    exact pow_ne_zero 2 (ne_of_gt hz')
  have hle_Ioc : ∀ z ∈ Set.Ioc (0:ℝ) 1, ‖(z / (1 + z) ^ 2) ^ 2‖ ≤ (1 : ℝ) := by
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := le_of_lt hz.1
    have hdiv0 : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz0 (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hdiv0 2)]
    have hle : z / (1 + z) ^ 2 ≤ 1 := by
      have hpos : (0 : ℝ) < (1 + z) ^ 2 := by nlinarith [hz0]
      rw [div_le_one hpos]
      nlinarith [hz0, hz.2]
    exact pow_le_one₀ hdiv0 hle
  have hA : MeasureTheory.IntegrableOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2) (Set.Ioc (0:ℝ) 1) := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (s := Set.Ioc (0:ℝ) 1) (C := (1 : ℝ))
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) ?_ ?_
    · exact hcont_Ioc.aestronglyMeasurable measurableSet_Ioc
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hle_Ioc
  have hcont_Ioi : ContinuousOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2) (Set.Ioi (1:ℝ)) := by
    refine ContinuousOn.pow (ContinuousOn.div continuousOn_id
      ((continuousOn_const.add continuousOn_id).pow 2) ?_) 2
    intro z hz
    have hz1 : (1 : ℝ) < z := Set.mem_Ioi.mp hz
    have hz' : (0 : ℝ) < 1 + z := by linarith
    exact pow_ne_zero 2 (ne_of_gt hz')
  have hle_Ioi : ∀ z ∈ Set.Ioi (1:ℝ),
      ‖(z / (1 + z) ^ 2) ^ 2‖ ≤ z ^ (-2 : ℝ) := by
    intro z hz
    have hz1 : (0 : ℝ) < z := lt_trans zero_lt_one hz
    have hz0 : (0 : ℝ) ≤ z := le_of_lt hz1
    have hdiv0 : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz0 (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hdiv0 2)]
    have hstep : z / (1 + z) ^ 2 ≤ z / z ^ 2 := by
      refine div_le_div_of_nonneg_left hz0 (by positivity) ?_
      exact pow_le_pow_left₀ hz0 (by linarith) 2
    calc (z / (1 + z) ^ 2) ^ 2 ≤ (z / z ^ 2) ^ 2 :=
          pow_le_pow_left₀ hdiv0 hstep 2
      _ = z ^ (-2 : ℝ) := by
          rw [Real.rpow_neg hz0, Real.rpow_two]
          field_simp
  have hB : MeasureTheory.IntegrableOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2) (Set.Ioi (1:ℝ)) := by
    refine MeasureTheory.Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := (1 : ℝ))
        (by norm_num) (by norm_num)) ?_ ?_
    · exact hcont_Ioi.aestronglyMeasurable measurableSet_Ioi
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hle_Ioi
  have hunion := hA.union hB
  rw [Set.Ioc_union_Ioi (a := (0:ℝ)) (b := 1) (c := 1) (by norm_num),
    min_eq_left (by norm_num : (0:ℝ) ≤ 1)] at hunion
  exact hunion

private theorem aux_integrableOn_sqrt_mul_of_integrableOn {A B : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A (Set.Ioi 0))
    (hAnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), 0 ≤ A z)
    (hB : MeasureTheory.IntegrableOn (fun z : ℝ => (B z) ^ 2) (Set.Ioi 0))
    (hBm : MeasureTheory.AEStronglyMeasurable B (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.IntegrableOn (fun z : ℝ => Real.sqrt (A z) * B z) (Set.Ioi 0) := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun z : ℝ => (1 / 2) * (A z + (B z) ^ 2)) (Set.Ioi 0) :=
    (hA.add hB).const_mul (1 / 2)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Real.sqrt (A z) * B z) (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable).mul hBm
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  filter_upwards [hAnn, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hAznn _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (A z))]
  have h := sq_nonneg (Real.sqrt (A z) - |B z|)
  rw [sub_sq, Real.sq_sqrt hAznn, sq_abs] at h
  linarith

/-! ## The source is `C^∞` on the open quadrant -/

theorem smoothOpen_of_bslSol (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hsol : Work.Elliptic.IsBslSol α F Ψ) : Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp α Ψ hsm)
    (fun z θ hz hθ0 hθ1 => hsol.1 z hz θ hθ0 hθ1)

/-! ## The `ℋ⁰`-integrand and its domination by the `ℋ^k`-integrand -/

theorem HkIntegrand_zero_apply (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

theorem HkIntegrand_zero_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [HkIntegrand_zero_apply, Work.Spaces.HkIntegrand]
  have hmixed : 0 ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs with hc
      · exact sq_nonneg _
      · exact le_refl 0
  have hsingle : (Work.Spaces.DzIter 0 f z θ * (Work.Spaces.w z
        / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    Finset.single_le_sum
      (s := Finset.range (k + 1))
      (f := fun i => (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.succ_pos k))
  exact le_trans (by simpa only [Work.Spaces.DzIter_zero] using hsingle)
    (le_add_of_nonneg_right hmixed)

theorem integral_HkIntegrand_zero_le (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hmem : Work.Spaces.HkMem α k F) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
  MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 F z θ)
    (hmem.1 z hz)
    (Eventually.of_forall fun θ => HkIntegrand_zero_le α k F z θ)

/-! ## `F_*` as an angular integral of `bslOp α Ψ` -/

theorem Fstar_eq_integral_bslOp (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hsol : Work.Elliptic.IsBslSol α F Ψ) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Fstar F z
      = ∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.Fstar]
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  by_cases hmid : 0 < θ ∧ θ < π / 2
  · rw [hsol.1 z hz θ hmid.1 hmid.2]
  · have hzero : θ = 0 ∨ θ = π / 2 := by
      obtain ⟨h0, h2⟩ := hθ
      by_cases hpos : 0 < θ
      · right
        by_contra hne
        exact hmid ⟨hpos, lt_of_le_of_ne h2 hne⟩
      · left; linarith
    rcases hzero with rfl | rfl <;>
      simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two]

/-! ## The pointwise bound -/

theorem Fstar_div_sq_le (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    (Work.Elliptic.Fstar F z / z) ^ 2
      ≤ (π / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
          * (z / (1 + z) ^ 2) ^ 2 := by
  have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
  have hIθ : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hcs := Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open α k F hF hmem 0 (Nat.zero_le k) hz
  simp only [Work.Spaces.DzIter_zero] at hcs
  have hA0 : (∫ θ in Work.Spaces.Iθ,
        (F z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ :=
    setIntegral_congr_fun hIθ fun θ _ => (HkIntegrand_zero_apply α F z θ).symm
  have hmono := integral_HkIntegrand_zero_le α k F hzI hmem
  have hle : (Work.Elliptic.Fstar F z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (π / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    calc (Work.Elliptic.Fstar F z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ,
            (F z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := hcs
      _ = (π / 2) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ := by rw [hA0]
      _ ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
  have halg : (Work.Elliptic.Fstar F z / z) ^ 2
      = (Work.Elliptic.Fstar F z) ^ 2 * (Work.Spaces.w z) ^ 2 * (z / (1 + z) ^ 2) ^ 2 := by
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 + z) ≠ 0 := by positivity
    rw [Work.Spaces.w]
    field_simp
  rw [halg]
  calc (Work.Elliptic.Fstar F z) ^ 2 * (Work.Spaces.w z) ^ 2 * (z / (1 + z) ^ 2) ^ 2
      ≤ ((π / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ))
          * (z / (1 + z) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ = (π / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
          * (z / (1 + z) ^ 2) ^ 2 := by ring

theorem abs_Fstar_div_le (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    |Work.Elliptic.Fstar F z / z|
      ≤ Real.sqrt (π / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
          * (z / (1 + z) ^ 2) := by
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
  have hRHS : 0 ≤ Real.sqrt (π / 2)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
      * (z / (1 + z) ^ 2) := by positivity
  have hkey : (Real.sqrt (π / 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
        * (z / (1 + z) ^ 2)) ^ 2
      = (π / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
          * (z / (1 + z) ^ 2) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hA]
  calc |Work.Elliptic.Fstar F z / z|
      = Real.sqrt ((Work.Elliptic.Fstar F z / z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Real.sqrt (π / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
          * (z / (1 + z) ^ 2)) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [hkey]
        exact Fstar_div_sq_le α k F hz hF hmem
    _ = Real.sqrt (π / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
          * (z / (1 + z) ^ 2) := Real.sqrt_sq hRHS

/-! ## A.e. strong measurability of `F_*(F)/·` -/

theorem aesm_Fstar_div (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hbsl : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp α Ψ hsm
  have hsc : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  have hQ0 : ContinuousOn
      (Function.uncurry fun z θ : ℝ => Work.Elliptic.bslOp α Ψ z θ / z)
      Work.FTS.EllipticEst.Q0 := by
    refine hbsl.continuousOn.div continuousOn_fst ?_
    intro p hp
    obtain ⟨hz, -, -⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt hz
  have h := Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0
    (fun z θ : ℝ => Work.Elliptic.bslOp α Ψ z θ / z) hQ0 Work.Elliptic.sinCos2 hsc
  refine h.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : (0 : ℝ) < r := Set.mem_Ioi.mp hr
  rw [Fstar_eq_integral_bslOp α F Ψ hsol hr0, ← MeasureTheory.integral_div]
  exact setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring

/-! ## The main theorem -/

theorem Fstar_div_integrable_of_sol_Hk (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ)
    (hmem : Work.Spaces.HkMem α k F) :
    MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_of_bslSol α F Ψ hsm hsol
  have hsub : Set.Ioi (0 : ℝ) ⊆ Work.Spaces.Iz := by
    intro z hz
    exact le_of_lt (Set.mem_Ioi.mp hz)
  have hAint : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) (Set.Ioi 0) :=
    hmem.2.mono_set hsub
  have hAnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
    Eventually.of_forall fun z =>
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
  have hsq : MeasureTheory.IntegrableOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2) (Set.Ioi 0) :=
    aux_integrableOn_sq_div_one_add_sq
  have hBm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => z / (1 + z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi 0) := by
      refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2) ?_
      intro z hz
      have hz' : (0 : ℝ) < z := Set.mem_Ioi.mp hz
      positivity
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hmaj : MeasureTheory.IntegrableOn
      (fun z : ℝ => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
        * (z / (1 + z) ^ 2)) (Set.Ioi 0) :=
    aux_integrableOn_sqrt_mul_of_integrableOn hAint hAnn hsq hBm
  have hmaj' : MeasureTheory.IntegrableOn
      (fun z : ℝ => Real.sqrt (π / 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
            * (z / (1 + z) ^ 2))) (Set.Ioi 0) :=
    MeasureTheory.Integrable.const_mul hmaj _
  refine MeasureTheory.Integrable.mono' hmaj' (aesm_Fstar_div α F Ψ hsm hsol) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  rw [Real.norm_eq_abs]
  calc |Work.Elliptic.Fstar F z / z|
      ≤ Real.sqrt (π / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
          * (z / (1 + z) ^ 2) := abs_Fstar_div_le α k F hz hF hmem
    _ = Real.sqrt (π / 2)
          * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
            * (z / (1 + z) ^ 2)) := by ring

end Work.FTS.EllipticEst.Cert.FstarSmooth
