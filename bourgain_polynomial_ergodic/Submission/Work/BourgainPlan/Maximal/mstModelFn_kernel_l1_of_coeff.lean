import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mstKernel_helpers
import Submission.Work.BourgainPlan.IonescuWainger.fourierCoeff_arcTranslate

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open Work.BourgainPlan.IonescuWainger
open scoped ENNReal BigOperators

set_option autoImplicit false

local notation "Circle" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haar" => (AddCircle.haarAddCircle (T := 1))
local notation "circleLift" => Work.BourgainPlan.Thm52.circleLift

/-- **From the per-term kernel bound to the kernel bound for a whole model symbol.**

Suppose the *untranslated* profile-times-bump `h_{N,s} = star (mstProf P N ·) * mstEta d χ η s` has
summable Fourier coefficients of total mass at most `K`, uniformly in the profile scale `N ≥ 1` and
the level `s` (the analytic hypothesis `hterm`, e.g. the conclusion of
`Submission.Work.BourgainPlan.Maximal.mstProfBumpS_coeff`).  Then for every `N ≥ 1`, every `s` and
every finite set `Es` of circle points, the `ℓ¹` coefficient kernel of the model symbol
`mstModelFn (star ∘ mstG P) (star ∘ mstProf P N) (mstEta d χ η s) Es` is summable with total mass at
most `K * #Es`.

Route (elementary geometry of the translation plus the triangle inequality):

* `mstModelFn_apply` expands the model symbol as `Σ_{β ∈ Es} star (mstG P β) * arcTranslate β h_{N,s}`
  and `‖star (mstG P β)‖ ≤ 1` (`mstG_norm_le_one`);
* the `p`-th Fourier coefficient of `arcTranslate β h` is `star (fourier p β)` times that of `h`
  (Haar-translation invariance `MeasureTheory.integral_add_right_eq_self` and
  `fourier p (ζ + β) = fourier p ζ * fourier p β`; the ready-made form is
  `Work.BourgainPlan.IonescuWainger.fourierCoeff_arcTranslate`, with `fourier_add_arg`);
* a finite sum of integrable functions has the sum of the integrals
  (`MeasureTheory.integral_finsetSum`), and each term is integrable: `‖mstProf P N ·‖ ≤ 1`
  (`norm_polyProfile_le_one`), `‖mstEta d χ η s ·‖` is a.e. bounded (derivable from
  `hη2`/`hcd`/`hd`, see the companion module
  `Submission.Work.BourgainPlan.Maximal.mstKernel_helpers` — it is `sorry`-free and contains
  `mstEta_eq_mstC`, the `MemLp` facts for the level bumps, `star_fourier_eq_exp`,
  `star_fourier_add_right` and `iwRep_coe_of_mem`), and `‖star (fourier p ·)‖ = 1`
  (`norm_fourier_apply'`); then `Integrable.mul_bdd` applies;
* summing `‖·‖` over `p ∈ ℤ` and then over `β ∈ Es` (Tonelli / `Summable.of_nonneg_of_le`,
  `Summable.tsum_finsetSum`, `Summable.tsum_le_tsum`, `Finset.sum_mul`) gives `#Es * K`.
  In fact the `Es`-dependence factors out completely: the `p`-th coefficient of the model symbol is
  `(Σ_{β ∈ Es} star (mstG P β) * star (fourier p β)) * A_p` with `A_p` the `p`-th coefficient of
  `h_{N,s}` (the reviewer's observation), so only one scalar identity plus the triangle inequality
  is needed.

Note the hypothesis `hterm` is only assumed for `N ≥ 1` (which is what the analytic companion gives)
and the conclusion is likewise restricted to `N ≥ 1`; no hypothesis on `N = 0` is needed.

Import `Submission.Work.BourgainPlan.Maximal.mst_major_defs` and
`Submission.Work.BourgainPlan.IonescuWainger.fourierCoeff_arcTranslate` (and optionally the helper
module `Submission.Work.BourgainPlan.Maximal.mstKernel_helpers`).  Work in namespace
`Work.BourgainPlan.Maximal`. -/
theorem mstModelFn_kernel_l1_of_coeff (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hd : 1 ≤ d) (hχ0 : 0 ≤ χ) (hχd : χ ≤ (d : ℝ))
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hcd : ∀ s : ℕ, ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η s)))
    {K : ℝ}
    (hterm : ∀ (N s : ℕ), 1 ≤ N →
      Summable (fun m : ℤ => ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖)
      ∧ (∑' m : ℤ, ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖) ≤ K) :
    ∀ (N s : ℕ), 1 ≤ N → ∀ (Es : Finset Work.BourgainPlan.IonescuWainger.Circle),
      Summable (fun p : ℤ => ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          mstModelFn (fun β => star (mstG P β)) (fun ζ => star (mstProf P N ζ))
            (mstEta d χ η s) Es ξ * star (fourier p ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖)
      ∧ (∑' p : ℤ, ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          mstModelFn (fun β => star (mstG P β)) (fun ζ => star (mstProf P N ζ))
            (mstEta d χ η s) Es ξ * star (fourier p ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖) ≤ K * (Es.card : ℝ) := by
  intro N s hN Es
  have hcont : Continuous (circleLift (mstEta d χ η 0)) := (hcd 0).continuous
  have hEta : MemLp (mstEta d χ η s) ⊤ haar := memLp_mstEta d χ η hη2 hcont hd hχ0 hχd s
  -- The untranslated profile-times-bump `h_{N,s}` whose coefficients `hterm` controls.
  set h : Circle → ℂ := fun ζ => star (mstProf P N ζ) * mstEta d χ η s ζ with hh
  have hMemLp : MemLp h ⊤ haar := by
    rw [hh]
    have hProf' : MemLp (fun ζ : Circle => star (mstProf P N ζ)) ⊤ haar :=
      (memLp_comp_iwRep (memLp_restrict_Ioc_of_continuous (continuous_polyProfile P N))).star
    refine MemLp.of_le hEta (hProf'.aestronglyMeasurable.mul hEta.aestronglyMeasurable) ?_
    filter_upwards with ζ
    rw [norm_mul, norm_star, mstProf_apply]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_polyProfile_le_one P N (iwRep ζ))
  obtain ⟨hsum, hsumle⟩ := hterm N s hN
  have hsumB : Summable (fun p : ℤ => ‖∫ ξ : Circle, h ξ * star (fourier p ξ) ∂haar‖) := by
    simpa only [hh] using hsum
  have hsumBle : (∑' p : ℤ, ‖∫ ξ : Circle, h ξ * star (fourier p ξ) ∂haar‖) ≤ K := by
    simpa only [hh] using hsumle
  -- **The `p`-th coefficient of the model symbol factors through that of `h`.**
  have key : ∀ p : ℤ,
      (∫ ξ : Circle, mstModelFn (fun β => star (mstG P β)) (fun ζ => star (mstProf P N ζ))
          (mstEta d χ η s) Es ξ * star (fourier p ξ) ∂haar)
      = (∑ β ∈ Es, star (mstG P β) * star (fourier p β))
          * (∫ ξ : Circle, h ξ * star (fourier p ξ) ∂haar) := by
    intro p
    have hdecomp : (fun ξ : Circle => mstModelFn (fun β => star (mstG P β))
          (fun ζ => star (mstProf P N ζ)) (mstEta d χ η s) Es ξ * star (fourier p ξ))
        = fun ξ : Circle => ∑ β ∈ Es, star (mstG P β) * (h (ξ - β) * star (fourier p ξ)) := by
      funext ξ
      rw [mstModelFn_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      rw [hh]
      ring
    have hsumint : (∫ ξ : Circle, ∑ β ∈ Es,
          star (mstG P β) * (h (ξ - β) * star (fourier p ξ)) ∂haar)
        = ∑ β ∈ Es, ∫ ξ : Circle, star (mstG P β) * (h (ξ - β) * star (fourier p ξ)) ∂haar := by
      refine MeasureTheory.integral_finsetSum Es (fun β _ => ?_)
      have hArc : MemLp (arcTranslate β h) ⊤ haar := memLp_arcTranslate hMemLp β
      have hfour : MemLp (fun ξ : Circle => star (fourier p ξ)) ⊤ haar :=
        MemLp.of_bound ((fourier p).continuous.aestronglyMeasurable.star) 1 (by
          filter_upwards with ξ
          rw [norm_star, norm_fourier_apply' p ξ])
      have hmem : MemLp (fun ξ : Circle => arcTranslate β h ξ * star (fourier p ξ)) ⊤ haar :=
        MemLp.of_le hArc (hArc.aestronglyMeasurable.mul hfour.aestronglyMeasurable) (by
          filter_upwards with ξ
          rw [norm_mul, norm_star, norm_fourier_apply' p ξ, mul_one])
      exact ((hmem.mono_exponent le_top).integrable le_rfl).const_mul _
    rw [hdecomp, hsumint, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    have htr : ∫ ξ : Circle, h (ξ - β) * star (fourier p ξ) ∂haar
        = star (fourier p β) * ∫ ξ : Circle, h ξ * star (fourier p ξ) ∂haar :=
      Work.BourgainPlan.IonescuWainger.fourierCoeff_arcTranslate h hMemLp β p
    rw [MeasureTheory.integral_const_mul, htr]
    ring
  -- **Domination of the `p`-th coefficient by `#Es * ‖B_p‖`.**
  have hbound : ∀ p : ℤ, ‖∫ ξ : Circle, mstModelFn (fun β => star (mstG P β))
          (fun ζ => star (mstProf P N ζ)) (mstEta d χ η s) Es ξ * star (fourier p ξ) ∂haar‖
      ≤ (Es.card : ℝ) * ‖∫ ξ : Circle, h ξ * star (fourier p ξ) ∂haar‖ := by
    intro p
    rw [key p, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖∑ β ∈ Es, star (mstG P β) * star (fourier p β)‖
        ≤ ∑ β ∈ Es, ‖star (mstG P β) * star (fourier p β)‖ := norm_sum_le _ _
      _ = ∑ β ∈ Es, ‖mstG P β‖ := by
            refine Finset.sum_congr rfl (fun β _ => ?_)
            rw [norm_mul, norm_star, norm_star, norm_fourier_apply' p β, mul_one]
      _ ≤ ∑ β ∈ Es, (1 : ℝ) := by
            exact Finset.sum_le_sum (fun β _ => mstG_norm_le_one P β)
      _ = (Es.card : ℝ) := by simp
  have hcomp : Summable (fun p : ℤ =>
      (Es.card : ℝ) * ‖∫ ξ : Circle, h ξ * star (fourier p ξ) ∂haar‖) :=
    Summable.mul_left _ hsumB
  have hsumX : Summable (fun p : ℤ => ‖∫ ξ : Circle, mstModelFn (fun β => star (mstG P β))
        (fun ζ => star (mstProf P N ζ)) (mstEta d χ η s) Es ξ * star (fourier p ξ) ∂haar‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound hcomp
  refine ⟨hsumX, ?_⟩
  calc ∑' p : ℤ, ‖∫ ξ : Circle, mstModelFn (fun β => star (mstG P β))
          (fun ζ => star (mstProf P N ζ)) (mstEta d χ η s) Es ξ * star (fourier p ξ) ∂haar‖
      ≤ ∑' p : ℤ, (Es.card : ℝ) * ‖∫ ξ : Circle, h ξ * star (fourier p ξ) ∂haar‖ :=
        Summable.tsum_le_tsum hbound hsumX hcomp
    _ = (Es.card : ℝ) * ∑' p : ℤ, ‖∫ ξ : Circle, h ξ * star (fourier p ξ) ∂haar‖ :=
        Summable.tsum_mul_left _ hsumB
    _ ≤ (Es.card : ℝ) * K := mul_le_mul_of_nonneg_left hsumBle (Nat.cast_nonneg _)
    _ = K * (Es.card : ℝ) := mul_comm _ _

end Work.BourgainPlan.Maximal
