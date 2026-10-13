/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EqcProduct`: the product of a cutoff with a function smooth near its support

Support module for `Sobolev/equicontinuous_deriv4_of_uniform_Hk6.lean`: a `C²` cutoff `χ`
vanishing off a closed set `s`, multiplied by a function `g` which is analytic on an open set
`U ⊇ s`, is `C²` with compact support whenever `χ` has compact support; and the `L²`-norms of
`v = χ·g` and of its second derivative are estimated in terms of those of `g` and of `‖fderiv g‖`
and `‖fderiv (fderiv g)‖`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongLWP.Sobolev.EqcBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Sobolev

set_option maxHeartbeats 1000000

set_option autoImplicit false

/-- The product of a `C²` cutoff `χ`, vanishing off a closed set `s`, with a function `g` which
is analytic (`ContDiffOn ℝ ⊤`) on an open set `U ⊇ s`, is `C²`. -/
lemma eqc_contDiff_two_mul_of_forall_notMem_eq_zero {χ g : ℝ × ℝ → ℝ} {s U : Set (ℝ × ℝ)}
    (hsc : IsClosed s) (hsU : s ⊆ U) (hU : IsOpen U) (hχ : ContDiff ℝ 2 χ)
    (hχ0 : ∀ x ∉ s, χ x = 0) (hg : ContDiffOn ℝ ⊤ g U) :
    ContDiff ℝ 2 (fun x => χ x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · have hxR : x ∈ s := by
      have hsub : tsupport χ ⊆ s :=
        hsc.closure_subset_iff.mpr (Function.support_subset_iff'.mpr hχ0)
      exact hsub hx
    exact hχ.contDiffAt.mul ((hg.contDiffAt (hU.mem_nhds (hsU hxR))).of_le le_top)
  · have hev : (fun y => χ y * g y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- A product with a compactly supported cutoff has compact support. -/
lemma eqc_hasCompactSupport_mul {χ g : ℝ × ℝ → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport (fun x => χ x * g x) :=
  hχ.mono fun x hx => by
    simp only [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by rw [h0, zero_mul])

/-- **The second derivative of a product.**  If `χ` and `g` are twice differentiable on a
neighbourhood of `x`, then
`‖D²(χ·g)(x)‖ ≤ |χ x|·‖D²g(x)‖ + 2‖Dχ(x)‖‖Dg(x)‖ + ‖D²χ(x)‖·|g x|`.

The bound is proved by evaluating the second derivative at an arbitrary vector, which keeps the
scalar multiplications at the (single) level of `(ℝ × ℝ) →L[ℝ] ℝ`; going through the operator
norm of the second derivative directly runs into the missing `IsBoundedSMul`/`NormSMulClass`
instance on `(ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)` in this Mathlib pin. -/
lemma eqc_norm_fderiv_fderiv_mul_le {χ g : ℝ × ℝ → ℝ} {M0 M1 M2 : ℝ} {x : ℝ × ℝ}
    (hχ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ χ y ∧ DifferentiableAt ℝ (fderiv ℝ χ) y)
    (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ (fderiv ℝ g) y)
    (hM0 : |χ x| ≤ M0) (hM1 : ‖fderiv ℝ χ x‖ ≤ M1) (hM2 : ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M2) :
    ‖fderiv ℝ (fderiv ℝ (fun y => χ y * g y)) x‖ ≤
      M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * |g x| := by
  have hχx := hχ.self_of_nhds
  have hgx := hg.self_of_nhds
  have hfg : fderiv ℝ (fun y => χ y * g y)
      =ᶠ[𝓝 x] (fun y => χ y • fderiv ℝ g y + g y • fderiv ℝ χ y) := by
    filter_upwards [hχ, hg] with y hy hgy
    exact fderiv_fun_mul hy.1 hgy.1
  have hd1 : DifferentiableAt ℝ (fun y => χ y • fderiv ℝ g y) x := hχx.1.smul hgx.2
  have hd2 : DifferentiableAt ℝ (fun y => g y • fderiv ℝ χ y) x := hgx.1.smul hχx.2
  have e1 : fderiv ℝ (fderiv ℝ (fun y => χ y * g y)) x
      = fderiv ℝ (fun y => χ y • fderiv ℝ g y) x
        + fderiv ℝ (fun y => g y • fderiv ℝ χ y) x := by
    rw [hfg.fderiv_eq]
    exact fderiv_add hd1 hd2
  have e2 : fderiv ℝ (fun y => χ y • fderiv ℝ g y) x
      = χ x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ χ x).smulRight (fderiv ℝ g x) :=
    fderiv_smul hχx.1 hgx.2
  have e3 : fderiv ℝ (fun y => g y • fderiv ℝ χ y) x
      = g x • fderiv ℝ (fderiv ℝ χ) x + (fderiv ℝ g x).smulRight (fderiv ℝ χ x) :=
    fderiv_smul hgx.1 hχx.2
  have hM0nn : 0 ≤ M0 := le_trans (abs_nonneg (χ x)) hM0
  have hM1nn : 0 ≤ M1 := le_trans (norm_nonneg (fderiv ℝ χ x)) hM1
  have hM2nn : 0 ≤ M2 := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ χ) x)) hM2
  have hbound : 0 ≤ M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * |g x| := by
    have h1 : 0 ≤ M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ :=
      mul_nonneg hM0nn (norm_nonneg (fderiv ℝ (fderiv ℝ g) x))
    have h2 : 0 ≤ 2 * M1 * ‖fderiv ℝ g x‖ := by positivity
    have h3 : 0 ≤ M2 * |g x| := mul_nonneg hM2nn (abs_nonneg (g x))
    linarith
  rw [ContinuousLinearMap.opNorm_le_iff hbound]
  intro h
  rw [e1, e2, e3]
  have hA : ‖χ x • ((fderiv ℝ (fderiv ℝ g) x) h)‖
      ≤ (M0 * ‖fderiv ℝ (fderiv ℝ g) x‖) * ‖h‖ := by
    calc ‖χ x • ((fderiv ℝ (fderiv ℝ g) x) h)‖
        ≤ ‖χ x‖ * ‖(fderiv ℝ (fderiv ℝ g) x) h‖ :=
          norm_smul_le (χ x) ((fderiv ℝ (fderiv ℝ g) x) h)
      _ ≤ ‖χ x‖ * (‖fderiv ℝ (fderiv ℝ g) x‖ * ‖h‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ h)
            (norm_nonneg (χ x))
      _ = (‖χ x‖ * ‖fderiv ℝ (fderiv ℝ g) x‖) * ‖h‖ := by ring
      _ ≤ (M0 * ‖fderiv ℝ (fderiv ℝ g) x‖) * ‖h‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg h)
          rw [Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right hM0 (norm_nonneg (fderiv ℝ (fderiv ℝ g) x))
  have hB : ‖(fderiv ℝ χ x h) • (fderiv ℝ g x)‖
      ≤ (M1 * ‖h‖) * ‖fderiv ℝ g x‖ := by
    calc ‖(fderiv ℝ χ x h) • (fderiv ℝ g x)‖
        ≤ ‖fderiv ℝ χ x h‖ * ‖fderiv ℝ g x‖ :=
          norm_smul_le (fderiv ℝ χ x h) (fderiv ℝ g x)
      _ ≤ (‖fderiv ℝ χ x‖ * ‖h‖) * ‖fderiv ℝ g x‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ h)
            (norm_nonneg (fderiv ℝ g x))
      _ ≤ (M1 * ‖h‖) * ‖fderiv ℝ g x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM1 (norm_nonneg h))
            (norm_nonneg (fderiv ℝ g x))
  have hC : ‖g x • ((fderiv ℝ (fderiv ℝ χ) x) h)‖ ≤ (M2 * ‖h‖) * |g x| := by
    calc ‖g x • ((fderiv ℝ (fderiv ℝ χ) x) h)‖
        ≤ ‖g x‖ * ‖(fderiv ℝ (fderiv ℝ χ) x) h‖ :=
          norm_smul_le (g x) ((fderiv ℝ (fderiv ℝ χ) x) h)
      _ ≤ ‖g x‖ * (‖fderiv ℝ (fderiv ℝ χ) x‖ * ‖h‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ h) (norm_nonneg (g x))
      _ = ‖g x‖ * (‖h‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖) := by ring
      _ ≤ |g x| * (‖h‖ * M2) := by
          refine mul_le_mul (by rw [Real.norm_eq_abs]) ?_ (by positivity)
            (abs_nonneg (g x))
          exact mul_le_mul_of_nonneg_left hM2 (norm_nonneg h)
      _ = (M2 * ‖h‖) * |g x| := by ring
  have hD : ‖(fderiv ℝ g x h) • (fderiv ℝ χ x)‖
      ≤ (M1 * ‖fderiv ℝ g x‖) * ‖h‖ := by
    calc ‖(fderiv ℝ g x h) • (fderiv ℝ χ x)‖
        ≤ ‖fderiv ℝ g x h‖ * ‖fderiv ℝ χ x‖ :=
          norm_smul_le (fderiv ℝ g x h) (fderiv ℝ χ x)
      _ ≤ (‖fderiv ℝ g x‖ * ‖h‖) * M1 :=
          mul_le_mul (ContinuousLinearMap.le_opNorm (fderiv ℝ g x) h) hM1
            (norm_nonneg (fderiv ℝ χ x))
            (mul_nonneg (norm_nonneg (fderiv ℝ g x)) (norm_nonneg h))
      _ = (M1 * ‖fderiv ℝ g x‖) * ‖h‖ := by ring
  calc ‖χ x • ((fderiv ℝ (fderiv ℝ g) x) h) + (fderiv ℝ χ x h) • (fderiv ℝ g x)
        + (g x • ((fderiv ℝ (fderiv ℝ χ) x) h) + (fderiv ℝ g x h) • (fderiv ℝ χ x))‖
      ≤ (‖χ x • ((fderiv ℝ (fderiv ℝ g) x) h)‖ + ‖(fderiv ℝ χ x h) • (fderiv ℝ g x)‖)
        + (‖g x • ((fderiv ℝ (fderiv ℝ χ) x) h)‖ + ‖(fderiv ℝ g x h) • (fderiv ℝ χ x)‖) := by
        refine le_trans (norm_add_le _ _)
          (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ ((M0 * ‖fderiv ℝ (fderiv ℝ g) x‖) * ‖h‖ + (M1 * ‖h‖) * ‖fderiv ℝ g x‖)
        + ((M2 * ‖h‖) * |g x| + (M1 * ‖fderiv ℝ g x‖) * ‖h‖) :=
        add_le_add (add_le_add hA hB) (add_le_add hC hD)
    _ = (M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * |g x|) * ‖h‖ := by
        ring

/-- On a set where `χ` vanishes (and outside which the integrand vanishes), the `L²`-norm of
`χ·g` is dominated by that of `g`. -/
lemma eqc_integral_mul_sq_le {χ g : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hχ0 : ∀ x ∉ s, χ x = 0) (hχle1 : ∀ x, χ x ≤ 1) (hχnn : ∀ x, 0 ≤ χ x)
    (hs : MeasurableSet s) (hgi : IntegrableOn (fun x => (g x) ^ 2) s) :
    ∫ x : ℝ × ℝ, (χ x * g x) ^ 2 ≤ ∫ x in s, (g x) ^ 2 := by
  have hzero : ∀ x ∉ s, (χ x * g x) ^ 2 = 0 := fun x hx => by rw [hχ0 x hx, zero_mul]; simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hgi ?_
  filter_upwards [ae_restrict_mem hs] with x hx
  have h1 : (χ x) ^ 2 ≤ 1 := by nlinarith [hχnn x, hχle1 x]
  calc (χ x * g x) ^ 2 = (χ x) ^ 2 * (g x) ^ 2 := by ring
    _ ≤ 1 * (g x) ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = (g x) ^ 2 := one_mul _

/-- The second-derivative product bound, integrated.  `χ` is a `C²` cutoff vanishing off the
closed set `s`; `g` is twice differentiable on the open set `U ⊇ s`; and `E` dominates
`‖fderiv (fderiv g)‖` on `s` and is square-integrable there (in the applications `E` is the sum
of the absolute values of the four basis entries of the second derivative, which keeps the
statement free of the `Norm`-instance diamonds of `E →L[ℝ] (E →L[ℝ] ℝ)`). -/
lemma eqc_integral_fderiv_fderiv_mul_sq_le {χ g : ℝ × ℝ → ℝ} {s U : Set (ℝ × ℝ)}
    {M0 M1 M2 : ℝ} {E : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (hsc : IsClosed s)
    (hχ0 : ∀ x ∉ s, χ x = 0)
    (hM0 : ∀ x, ‖χ x‖ ≤ M0) (hM1 : ∀ x, ‖fderiv ℝ χ x‖ ≤ M1)
    (hM2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M2)
    (hU : IsOpen U) (hsU : s ⊆ U) (hgd : ∀ y ∈ U, DifferentiableAt ℝ g y)
    (hgd2 : ∀ y ∈ U, DifferentiableAt ℝ (fderiv ℝ g) y)
    (hE : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ E x)
    (hI0 : IntegrableOn (fun x => (g x) ^ 2) s)
    (hI1 : IntegrableOn (fun x => ‖fderiv ℝ g x‖ ^ 2) s)
    (hI2 : IntegrableOn (fun x => (E x) ^ 2) s) :
    ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun y => χ y * g y)) x‖ ^ 2
      ≤ 3 * (M0 ^ 2 * (∫ x in s, (E x) ^ 2)
        + (2 * M1) ^ 2 * (∫ x in s, ‖fderiv ℝ g x‖ ^ 2)
        + M2 ^ 2 * (∫ x in s, (g x) ^ 2)) := by
  have hχd : ∀ x, DifferentiableAt ℝ χ x :=
    fun x => (hχ.differentiable (by norm_num)).differentiableAt
  have hχd2 : ∀ x, DifferentiableAt ℝ (fderiv ℝ χ) x := fun x =>
    ((hχ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
  set v : ℝ × ℝ → ℝ := fun y => χ y * g y with hvdef
  have hpt : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2
      ≤ 3 * (M0 ^ 2 * (E x) ^ 2 + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2) := by
    intro x hx
    have hχev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ χ y ∧ DifferentiableAt ℝ (fderiv ℝ χ) y :=
      Eventually.of_forall fun y => ⟨hχd y, hχd2 y⟩
    have hgev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ (fderiv ℝ g) y := by
      filter_upwards [hU.mem_nhds (hsU hx)] with y hy
      exact ⟨hgd y hy, hgd2 y hy⟩
    have hb := eqc_norm_fderiv_fderiv_mul_le (χ := χ) (g := g) (x := x) hχev hgev
      (hM0 x) (hM1 x) (hM2 x)
    have hb' : ‖fderiv ℝ (fderiv ℝ v) x‖
        ≤ M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * ‖g x‖ := hb
    have hM0nn : 0 ≤ M0 := le_trans (abs_nonneg (χ x)) (hM0 x)
    have hM1nn : 0 ≤ M1 := le_trans (norm_nonneg (fderiv ℝ χ x)) (hM1 x)
    have hM2nn : 0 ≤ M2 := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ χ) x)) (hM2 x)
    have hstep : M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * ‖g x‖
        ≤ M0 * E x + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * ‖g x‖ :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hE x hx) hM0nn) le_rfl) le_rfl
    have hnn1 : 0 ≤ M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * ‖g x‖ := by
      positivity
    have hsq := pow_le_pow_left₀ hnn1 hstep 2
    have hsq2 := pow_le_pow_left₀ (norm_nonneg (fderiv ℝ (fderiv ℝ v) x)) hb' 2
    refine (hsq2.trans hsq).trans ?_
    calc (M0 * E x + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * ‖g x‖) ^ 2
        ≤ 3 * ((M0 * E x) ^ 2 + (2 * M1 * ‖fderiv ℝ g x‖) ^ 2 + (M2 * ‖g x‖) ^ 2) :=
          eqc_sq_add3_le _ _ _
      _ = 3 * (M0 ^ 2 * (E x) ^ 2 + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2) := by
          simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  have hvzero : ∀ x ∉ s, fderiv ℝ (fderiv ℝ v) x = 0 := fun x hx =>
    (eqc_fderiv_fderiv_eq_zero_of_open hsc.isOpen_compl (fun y hy => by
      simp only [hvdef]; rw [hχ0 y hy, zero_mul]) hx).2
  have hmain : ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2
      = ∫ x in s, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hvzero x hx, ContinuousLinearMap.opNorm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)])).symm
  rw [hmain]
  have hFA : IntegrableOn (fun x => M0 ^ 2 * (E x) ^ 2) s := hI2.const_mul _
  have hFB : IntegrableOn (fun x => (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2) s := hI1.const_mul _
  have hFC : IntegrableOn (fun x => M2 ^ 2 * (g x) ^ 2) s := hI0.const_mul _
  have hIntBig : IntegrableOn (fun x => 3 * (M0 ^ 2 * (E x) ^ 2
      + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2)) s :=
    (hFA.add hFB).add hFC |>.const_mul 3
  have h1 : (∫ x in s, M0 ^ 2 * (E x) ^ 2
        + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2)
      = (∫ x in s, M0 ^ 2 * (E x) ^ 2 + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2)
        + (∫ x in s, M2 ^ 2 * (g x) ^ 2) :=
    integral_add (hFA.add hFB) hFC
  have h2 : (∫ x in s, M0 ^ 2 * (E x) ^ 2 + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2)
      = (∫ x in s, M0 ^ 2 * (E x) ^ 2)
        + (∫ x in s, (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2) :=
    integral_add hFA hFB
  have h3 : (∫ x in s, M0 ^ 2 * (E x) ^ 2) = M0 ^ 2 * (∫ x in s, (E x) ^ 2) :=
    integral_const_mul _ _
  have h4 : (∫ x in s, (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2)
      = (2 * M1) ^ 2 * (∫ x in s, ‖fderiv ℝ g x‖ ^ 2) := integral_const_mul _ _
  have h5 : (∫ x in s, M2 ^ 2 * (g x) ^ 2) = M2 ^ 2 * (∫ x in s, (g x) ^ 2) :=
    integral_const_mul _ _
  have hsplit : (∫ x in s, M0 ^ 2 * (E x) ^ 2
        + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2)
      = M0 ^ 2 * (∫ x in s, (E x) ^ 2)
        + (2 * M1) ^ 2 * (∫ x in s, ‖fderiv ℝ g x‖ ^ 2)
        + M2 ^ 2 * (∫ x in s, (g x) ^ 2) := by
    rw [h1, h2, h3, h4, h5]
  calc ∫ x in s, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2
      ≤ ∫ x in s, 3 * (M0 ^ 2 * (E x) ^ 2
          + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hIntBig
          (ae_restrict_of_forall_mem hsc.measurableSet hpt)
    _ = 3 * (M0 ^ 2 * (∫ x in s, (E x) ^ 2)
          + (2 * M1) ^ 2 * (∫ x in s, ‖fderiv ℝ g x‖ ^ 2)
          + M2 ^ 2 * (∫ x in s, (g x) ^ 2)) := by
        rw [integral_const_mul, hsplit]

end Work.FTS.StrongLWP.Sobolev
