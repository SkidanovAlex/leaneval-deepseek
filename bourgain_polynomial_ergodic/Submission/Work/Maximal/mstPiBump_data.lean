import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.contDiff_polyProfile
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation
import Submission.Work.BourgainPlan.Maximal.mstKernel_helpers
import Submission.Work.BourgainPlan.Maximal.memLp_scaled_bump
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.iw_superset

namespace Work.Maximal

open Filter
open Work.BourgainPlan.Maximal

set_option maxHeartbeats 2000000

/-! ## Elementary tools for the pointwise Mikhlin bounds of a product

The three lemmas below are what turns the pointwise bounds of the two factors into the pointwise
bounds of their product; they are stated for arbitrary functions `u v : ℝ → ℂ` so that the main
theorem can be phrased in terms of them. -/

/-- A function which is eventually `0` near `x` has derivative `0` at `x`. -/
private lemma deriv_eq_zero_of_eventuallyEq_zero {w : ℝ → ℂ} {x : ℝ}
    (hw : w =ᶠ[nhds x] 0) : deriv w x = 0 := by
  rw [Filter.EventuallyEq.deriv_eq hw]; simp

/-- The second Leibniz rule, expanded: `(uv)'' = u'' v + 2 u' v' + u v''`. -/
private lemma iteratedDeriv_two_mul {f g : ℝ → ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (f * g) x
      = iteratedDeriv 2 f x * g x + 2 * deriv f x * deriv g x
        + f x * iteratedDeriv 2 g x := by
  rw [iteratedDeriv_mul hf hg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_self,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.reduceSub, Nat.reduceAdd, iteratedDeriv_zero,
    iteratedDeriv_one]
  norm_num
  ring

/-- A function which is eventually `0` near `x` has second derivative `0` at `x`. -/
private lemma iteratedDeriv_two_eq_zero_of_eventuallyEq_zero {w : ℝ → ℂ} {x : ℝ}
    (hw : w =ᶠ[nhds x] 0) : iteratedDeriv 2 w x = 0 := by
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [Filter.EventuallyEq.deriv_eq (hw.deriv)]
  simp

/-- **The level dilation factor is `≥ 1`.**  For `P` of degree `≥ 2` and `χ < 1/10` the exponent
`s (deg P − χ)` of `mstC P.natDegree χ s = 2^{s (deg P − χ)}` is nonnegative. -/
private lemma one_le_mstC' (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {χ : ℝ} (hχ : χ < 1/10)
    (s : ℕ) : 1 ≤ mstC P.natDegree χ s := by
  rw [mstC]
  apply Real.one_le_rpow (by norm_num)
  apply mul_nonneg (by positivity)
  have hd2 : (2:ℝ) ≤ (P.natDegree:ℝ) := by exact_mod_cast hd
  linarith

/-- **Mikhlin data for a product.**  Let `u` be `C²`, unit-bounded, with bounds `C1`, `C2` for its
first two derivatives on `[-1/2, 1/2]`; let `v` be `C²` with `‖v‖ ≤ M`, `|·|‖v'‖ ≤ M`,
`|·|²‖v''‖ ≤ M` and `v` vanishing for `|x| > 1/2`.  Then the product obeys the three pointwise
Mikhlin bounds with the single constant
`max M (max (C1 M / 2 + M) (C2 M / 4 + C1 M + M))`.

The only place where the support of `v` enters is the region `|x| > 1/2`, where the product is
*eventually* `0` (the set `{|x| > 1/2}` is open), so all its derivatives vanish. -/
private lemma prod_mikhlin {u v : ℝ → ℂ} {M C1 C2 : ℝ}
    (hM : 0 ≤ M) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hu0 : ∀ x, ‖u x‖ ≤ 1)
    (hu1 : ∀ x ∈ Set.Icc (-(1/2:ℝ)) (1/2), ‖deriv u x‖ ≤ C1)
    (hu2 : ∀ x ∈ Set.Icc (-(1/2:ℝ)) (1/2), ‖iteratedDeriv 2 u x‖ ≤ C2)
    (hv0 : ∀ x, ‖v x‖ ≤ M)
    (hv1 : ∀ x, |x| * ‖deriv v x‖ ≤ M)
    (hv2 : ∀ x, |x|^2 * ‖iteratedDeriv 2 v x‖ ≤ M)
    (hvsupp : ∀ x, 1/2 < |x| → v x = 0) :
    ContDiff ℝ 2 (u * v) ∧
    (∀ x, ‖(u*v) x‖ ≤ max M (max ((1/2)*C1*M + M) ((1/4)*C2*M + C1*M + M))) ∧
    (∀ x, |x| * ‖deriv (u*v) x‖ ≤ max M (max ((1/2)*C1*M + M) ((1/4)*C2*M + C1*M + M))) ∧
    (∀ x, |x|^2 * ‖iteratedDeriv 2 (u*v) x‖
        ≤ max M (max ((1/2)*C1*M + M) ((1/4)*C2*M + C1*M + M))) := by
  have hA0 : 0 ≤ max M (max ((1/2)*C1*M + M) ((1/4)*C2*M + C1*M + M)) :=
    le_trans hM (le_max_left _ _)
  have hvsupp_ev : ∀ x, 1/2 < |x| → (u * v) =ᶠ[nhds x] 0 := by
    intro x hx
    have hUop : IsOpen {y : ℝ | 1/2 < |y|} := isOpen_lt continuous_const continuous_abs
    have hmem : {y : ℝ | 1/2 < |y|} ∈ nhds x := hUop.mem_nhds hx
    have hv_ev : v =ᶠ[nhds x] 0 := Filter.mem_of_superset hmem (fun y hy => hvsupp y hy)
    exact Filter.Eventually.mono hv_ev (fun y hy => by simp [hy])
  refine ⟨hu.mul hv, ?_, ?_, ?_⟩
  · intro x
    calc ‖(u*v) x‖ = ‖u x‖ * ‖v x‖ := norm_mul _ _
      _ ≤ 1 * M := mul_le_mul (hu0 x) (hv0 x) (norm_nonneg _) (by norm_num)
      _ = M := one_mul M
      _ ≤ _ := le_max_left _ _
  · intro x
    by_cases hx : |x| ≤ 1/2
    · have hxI : x ∈ Set.Icc (-(1/2:ℝ)) (1/2) := by
        rw [Set.mem_Icc]; exact abs_le.mp hx
      rw [deriv_mul (hu.contDiffAt.differentiableAt (by norm_num))
            (hv.contDiffAt.differentiableAt (by norm_num))]
      have h1a : |x| * ‖deriv u x‖ ≤ (1/2)*C1 :=
        mul_le_mul hx (hu1 x hxI) (norm_nonneg _) (by norm_num)
      have h1 : |x| * ‖deriv u x‖ * ‖v x‖ ≤ (1/2)*C1*M :=
        mul_le_mul h1a (hv0 x) (norm_nonneg _) (mul_nonneg (by norm_num) hC1)
      have h2 : |x| * ‖u x‖ * ‖deriv v x‖ ≤ M := by
        have hre : |x| * ‖u x‖ * ‖deriv v x‖ = ‖u x‖ * (|x| * ‖deriv v x‖) := by ring
        rw [hre]
        calc ‖u x‖ * (|x| * ‖deriv v x‖) ≤ 1 * M :=
              mul_le_mul (hu0 x) (hv1 x) (by positivity) (by norm_num)
          _ = M := one_mul M
      calc |x| * ‖deriv u x * v x + u x * deriv v x‖
          ≤ |x| * (‖deriv u x * v x‖ + ‖u x * deriv v x‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg x)
        _ = |x| * ‖deriv u x‖ * ‖v x‖ + |x| * ‖u x‖ * ‖deriv v x‖ := by
            rw [norm_mul, norm_mul]; ring
        _ ≤ (1/2)*C1*M + M := add_le_add h1 h2
        _ ≤ _ := le_trans (le_max_left _ _) (le_max_right _ _)
    · have hx' : 1/2 < |x| := not_le.mp hx
      rw [deriv_eq_zero_of_eventuallyEq_zero (hvsupp_ev x hx')]
      simp only [norm_zero, mul_zero]
      exact hA0
  · intro x
    by_cases hx : |x| ≤ 1/2
    · have hxI : x ∈ Set.Icc (-(1/2:ℝ)) (1/2) := by
        rw [Set.mem_Icc]; exact abs_le.mp hx
      rw [iteratedDeriv_two_mul hu.contDiffAt hv.contDiffAt]
      have hx2 : |x|^2 ≤ 1/4 := by nlinarith [abs_nonneg x, hx]
      have s1a : |x|^2 * ‖iteratedDeriv 2 u x‖ ≤ (1/4)*C2 := by
        have h1 := mul_le_mul_of_nonneg_right hx2 (norm_nonneg (iteratedDeriv 2 u x))
        have h2 := mul_le_mul_of_nonneg_left (hu2 x hxI) (by norm_num : (0:ℝ) ≤ 1/4)
        linarith [h1, h2]
      have s1 : |x|^2 * ‖iteratedDeriv 2 u x * v x‖ ≤ (1/4)*C2*M := by
        rw [norm_mul, show |x|^2 * (‖iteratedDeriv 2 u x‖ * ‖v x‖)
            = (|x|^2 * ‖iteratedDeriv 2 u x‖) * ‖v x‖ by ring]
        exact mul_le_mul s1a (hv0 x) (norm_nonneg _) (mul_nonneg (by norm_num) hC2)
      have hdv : |x|^2 * ‖deriv v x‖ ≤ (1/2) * M := by
        have hre : |x|^2 * ‖deriv v x‖ = |x| * (|x| * ‖deriv v x‖) := by ring
        rw [hre]
        calc |x| * (|x| * ‖deriv v x‖) ≤ |x| * M :=
              mul_le_mul_of_nonneg_left (hv1 x) (abs_nonneg x)
          _ ≤ (1/2) * M := mul_le_mul hx le_rfl hM (by norm_num)
      have s2a : 2 * ‖deriv u x‖ ≤ 2 * C1 := by linarith [hu1 x hxI]
      have s2 : |x|^2 * ‖2 * deriv u x * deriv v x‖ ≤ C1*M := by
        rw [show ‖(2:ℂ) * deriv u x * deriv v x‖ = 2 * ‖deriv u x‖ * ‖deriv v x‖ by
              rw [norm_mul, norm_mul]; norm_num,
            show |x|^2 * (2 * ‖deriv u x‖ * ‖deriv v x‖)
              = 2 * ‖deriv u x‖ * (|x|^2 * ‖deriv v x‖) by ring]
        calc 2 * ‖deriv u x‖ * (|x|^2 * ‖deriv v x‖) ≤ 2 * C1 * ((1/2) * M) :=
              mul_le_mul s2a hdv (by positivity) (by linarith)
          _ = C1*M := by ring
      have s3 : |x|^2 * ‖u x * iteratedDeriv 2 v x‖ ≤ M := by
        rw [norm_mul, show |x|^2 * (‖u x‖ * ‖iteratedDeriv 2 v x‖)
            = ‖u x‖ * (|x|^2 * ‖iteratedDeriv 2 v x‖) by ring]
        calc ‖u x‖ * (|x|^2 * ‖iteratedDeriv 2 v x‖) ≤ 1 * M :=
              mul_le_mul (hu0 x) (hv2 x) (by positivity) (by norm_num)
          _ = M := one_mul M
      calc |x|^2 * ‖iteratedDeriv 2 u x * v x + 2 * deriv u x * deriv v x + u x * iteratedDeriv 2 v x‖
          ≤ |x|^2 * (‖iteratedDeriv 2 u x * v x‖ + ‖2 * deriv u x * deriv v x‖
              + ‖u x * iteratedDeriv 2 v x‖) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ |x|^2)
            calc ‖iteratedDeriv 2 u x * v x + 2 * deriv u x * deriv v x + u x * iteratedDeriv 2 v x‖
                ≤ ‖iteratedDeriv 2 u x * v x + 2 * deriv u x * deriv v x‖
                  + ‖u x * iteratedDeriv 2 v x‖ := norm_add_le _ _
              _ ≤ (‖iteratedDeriv 2 u x * v x‖ + ‖2 * deriv u x * deriv v x‖)
                  + ‖u x * iteratedDeriv 2 v x‖ :=
                  add_le_add (norm_add_le _ _) le_rfl
        _ = |x|^2 * ‖iteratedDeriv 2 u x * v x‖ + |x|^2 * ‖2 * deriv u x * deriv v x‖
            + |x|^2 * ‖u x * iteratedDeriv 2 v x‖ := by ring
        _ ≤ (1/4)*C2*M + C1*M + M := by linarith [s1, s2, s3]
        _ ≤ _ := le_trans (le_max_right _ _) (le_max_right _ _)
    · have hx' : 1/2 < |x| := not_le.mp hx
      rw [iteratedDeriv_two_eq_zero_of_eventuallyEq_zero (hvsupp_ev x hx')]
      simp only [norm_zero, mul_zero]
      exact hA0

/-- **Uniform Mikhlin data for the level-`s` base symbol of MST Theorem 7.**

Let `ψ_s : 𝕋 → ℂ` be the weight-free level-`s` model symbol `ψ_s ζ = star (Φ_1 ζ) · η_s ζ`, where
`Φ_1 = mstProf P (2^0)` is the first-scale profile and `η_s = mstEta P.natDegree χ η s` the level-`s`
bump.  Then there is a single constant `A > 0`, depending only on `P`, `η` and `M` (and NOT on `s`),
such that for every `s` the fundamental-domain lift `circleLift ψ_s`
(`Submission.Work.BourgainPlan.Thm52.circleLift`) is `C²`, bounded by `A`, and satisfies the two
Mikhlin bounds `|x| ‖D (circleLift ψ_s) x‖ ≤ A`, `|x|² ‖D² (circleLift ψ_s) x‖ ≤ A`.

These are the Mikhlin hypotheses of `IWSupersetBoundLift`, so this is what lets the
Ionescu–Wainger estimate be applied with a constant uniform in `s`. -/
theorem mstPiBump_data
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {χ : ℝ} (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) {M : ℝ} (hM : 0 < M)
    (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ,
      ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift
        (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
          star (Work.BourgainPlan.Maximal.mstProf P (2 ^ 0) ζ) *
            Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ)) ∧
      (∀ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift
        (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
          star (Work.BourgainPlan.Maximal.mstProf P (2 ^ 0) ζ) *
            Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ) x‖ ≤ A) ∧
      (∀ x : ℝ, |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift
        (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
          star (Work.BourgainPlan.Maximal.mstProf P (2 ^ 0) ζ) *
            Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ)) x‖ ≤ A) ∧
      (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift
        (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
          star (Work.BourgainPlan.Maximal.mstProf P (2 ^ 0) ζ) *
            Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ)) x‖ ≤ A) := by
  have hMle : 0 ≤ M := le_of_lt hM
  -- the first-scale profile `u = polyProfile P 1` is `C^∞`, hence `C²`
  have hu : ContDiff ℝ 2 (fun x : ℝ => polyProfile P 1 x) :=
    (contDiff_polyProfile P 1).of_le (by decide)
  have hcu1 : Continuous (iteratedDeriv 1 (fun x : ℝ => polyProfile P 1 x)) :=
    (contDiff_polyProfile P 1).continuous_iteratedDeriv 1 (by decide)
  have hcu2 : Continuous (iteratedDeriv 2 (fun x : ℝ => polyProfile P 1 x)) :=
    (contDiff_polyProfile P 1).continuous_iteratedDeriv 2 (by decide)
  -- the bounds `C1`, `C2` of `u'` and `u''` on the fixed compact interval `[-1/2, 1/2]`
  obtain ⟨C1, hC1raw⟩ :=
    (isCompact_Icc (a := (-(1/2:ℝ))) (b := (1/2))).exists_bound_of_continuousOn hcu1.continuousOn
  obtain ⟨C2, hC2raw⟩ :=
    (isCompact_Icc (a := (-(1/2:ℝ))) (b := (1/2))).exists_bound_of_continuousOn hcu2.continuousOn
  have hC1 : ∀ x ∈ Set.Icc (-(1/2:ℝ)) (1/2),
      ‖deriv (fun x : ℝ => polyProfile P 1 x) x‖ ≤ C1 := fun x hx => by
    simpa only [iteratedDeriv_one] using hC1raw x hx
  have hC2 : ∀ x ∈ Set.Icc (-(1/2:ℝ)) (1/2),
      ‖iteratedDeriv 2 (fun x : ℝ => polyProfile P 1 x) x‖ ≤ C2 := hC2raw
  have hC1nn : 0 ≤ C1 := le_trans (norm_nonneg _) (hC1 0 (by norm_num))
  have hC2nn : 0 ≤ C2 := le_trans (norm_nonneg _) (hC2 0 (by norm_num))
  refine ⟨max M (max ((1/2)*C1*M + M) ((1/4)*C2*M + C1*M + M)), ?_, ?_⟩
  · exact lt_of_lt_of_le hM (le_max_left _ _)
  · intro s
    set c : ℝ := mstC P.natDegree χ s with hc
    have hc1 : 1 ≤ c := by rw [hc]; exact one_le_mstC' P hd hχ1 s
    have hcnonneg : 0 ≤ c := le_trans zero_le_one hc1
    -- the level-`s` bump `v = η(-c·)` and its Mikhlin data
    obtain ⟨hvcont, hv0, hv1, hv2⟩ :=
      scaled_bump_mikhlin_bounds (η := η) (M := M) (d := -c) hηc hηbd hder1 hder2
    have hvsupp : ∀ x : ℝ, 1/2 < |x| → η ((-c) * x) = 0 := by
      intro x hx
      apply hηsup _
      rw [abs_mul, abs_neg, abs_of_nonneg hcnonneg]
      calc (1:ℝ)/2 ≤ |x| := le_of_lt hx
        _ = 1 * |x| := (one_mul _).symm
        _ ≤ c * |x| := mul_le_mul_of_nonneg_right hc1 (abs_nonneg x)
    -- the product `u v` obeys the Mikhlin bounds
    have hpm := prod_mikhlin (u := fun x : ℝ => polyProfile P 1 x)
      (v := fun x : ℝ => η ((-c) * x)) (M := M) (C1 := C1) (C2 := C2)
      hMle hC1nn hC2nn hu hvcont (fun x => norm_polyProfile_le_one P 1 x) hC1 hC2
      hv0 hv1 hv2 hvsupp
    obtain ⟨hpmc, hpm0, hpm1, hpm2⟩ := hpm
    -- the pointwise lift identity `circleLift ψ_s = u · v`
    have hfuneq : (Work.BourgainPlan.Thm52.circleLift
          (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
            star (mstProf P (2 ^ 0) ζ) * mstEta P.natDegree χ η s ζ))
        = fun x : ℝ => polyProfile P 1 x * η ((-c) * x) := by
      funext x
      have hstarn : ∀ y : ℝ, star (polyProfile P 1 (-y)) = polyProfile P 1 y := by
        intro y
        rw [← starRingEnd_apply, star_polyProfile, polyProfile_eq_polyE]
        apply intervalIntegral.integral_congr
        intro t _
        ring_nf
      by_cases hx : x ∈ Set.Ioc (-(1/2:ℝ)) (1/2)
      · rw [Work.BourgainPlan.Thm52.circleLift_of_mem hx]
        rw [Set.mem_Ioc] at hx
        rcases lt_or_eq_of_le hx.2 with hlt | heq
        · have hneg : -x ∈ Set.Ioc (-(1/2:ℝ)) (1/2) := by
            rw [Set.mem_Ioc]; constructor <;> linarith [hx.1, hx.2]
          have hcoe : (-(x : Work.BourgainPlan.IonescuWainger.Circle))
              = ((-x : ℝ) : Work.BourgainPlan.IonescuWainger.Circle) :=
            (AddCircle.coe_neg (1:ℝ) (x := x)).symm
          rw [hcoe, mstProf_apply, mstEta_eq_mstC, iwRep_coe_of_mem hneg]
          rw [pow_zero, ← hc, show c * -x = (-c) * x by ring, hstarn x]
        · subst heq
          rw [mstProf_apply, mstEta_eq_mstC, iwRep_neg_half]
          rw [pow_zero, ← hc]
          have h1 : (1:ℝ)/2 ≤ |c * (1/2)| := by
            rw [abs_mul, abs_of_nonneg hcnonneg, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
            nlinarith [hc1]
          have h2 : (1:ℝ)/2 ≤ |(-c) * (1/2)| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hcnonneg, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
            nlinarith [hc1]
          rw [hηsup (c * (1/2)) h1, hηsup ((-c) * (1/2)) h2, mul_zero, mul_zero]
      · rw [Work.BourgainPlan.Thm52.circleLift_of_notMem hx]
        symm
        have hxor : x ≤ -(1/2) ∨ (1/2:ℝ) < x := by
          by_contra h
          rw [not_or] at h
          exact hx ⟨not_le.mp h.1, not_lt.mp h.2⟩
        have hxabs : (1:ℝ)/2 ≤ |x| := by
          rcases hxor with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have h3 : (1:ℝ)/2 ≤ |(-c) * x| := by
          rw [abs_mul, abs_neg, abs_of_nonneg hcnonneg]
          calc (1:ℝ)/2 ≤ |x| := hxabs
            _ = 1 * |x| := (one_mul _).symm
            _ ≤ c * |x| := mul_le_mul_of_nonneg_right hc1 (abs_nonneg x)
        rw [hηsup _ h3, mul_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hfuneq]; exact hpmc
    · intro x; rw [hfuneq]; exact hpm0 x
    · intro x; rw [hfuneq]; exact hpm1 x
    · intro x; rw [hfuneq]; exact hpm2 x

end Work.Maximal
