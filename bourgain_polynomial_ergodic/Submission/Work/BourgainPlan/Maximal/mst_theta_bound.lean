import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_theta_defs
import Submission.Work.BourgainPlan.Maximal.mst_theta_weighted_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.mikhlin_multiplier_lift
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.polyProfile_family_sum_le
import Submission.Work.BourgainPlan.Maximal.memLp_comp_iwRep
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Work.BourgainPlan.Maximal.mst_theta_raw
import Submission.Work.BourgainPlan.Maximal.iwMult_mul
import Submission.Work.BourgainPlan.Maximal.truncated_mikhlin_multiplier

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## Elementary preliminaries -/

/-- The support condition `η x = 0` for `|x| > 1/2` extends to `|x| ≥ 1/2` by continuity. -/
lemma eta_supp_closed {η : ℝ → ℂ} (hcont : Continuous η)
    (h : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0 := by
  intro x hx
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact h x hlt
  · have hseq : Filter.Tendsto (fun n : ℕ => x * (1 + 1 / ((n : ℝ) + 1))) Filter.atTop (nhds x) := by
      have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Filter.Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add h1
      have h3 := (tendsto_const_nhds (x := x)).mul h2
      simpa using h3
    have hval : ∀ n : ℕ, η (x * (1 + 1 / ((n : ℝ) + 1))) = 0 := by
      intro n
      apply h
      have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have habs : |x * (1 + 1 / ((n : ℝ) + 1))| = |x| * (1 + 1 / ((n : ℝ) + 1)) := by
        rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 1 + 1 / ((n:ℝ)+1))]
      rw [habs, heq]
      nlinarith
    have h2 : Filter.Tendsto (fun n : ℕ => η (x * (1 + 1 / ((n : ℝ) + 1)))) Filter.atTop
        (nhds (η x)) := (hcont.tendsto x).comp hseq
    rw [show (fun n : ℕ => η (x * (1 + 1 / ((n : ℝ) + 1)))) = fun _ : ℕ => (0:ℂ) from
      funext hval] at h2
    simpa using tendsto_nhds_unique h2 tendsto_const_nhds

/-- `IWMult` is monotone in its constant (for nonnegative constants). -/
lemma IWMult_mono {r : ℕ} {ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ} {A A' : ℝ}
    (hA : 0 ≤ A) (hAA' : A ≤ A') (h : IWMult r ψ A) : IWMult r ψ A' := by
  intro g hg
  have hq : (0:ℝ) ≤ 2 * (r : ℝ) := by positivity
  have hpow : A ^ (2 * (r : ℝ)) ≤ A' ^ (2 * (r : ℝ)) := Real.rpow_le_rpow hA hAA' hq
  have hJ0 : (0 : ℝ≥0∞) ≤ ∫⁻ (x : ℝ), ‖g x‖ₑ ^ (2 * (r : ℝ)) := by simp
  have hof0 : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (A' ^ (2 * (r : ℝ))) := by simp
  exact le_trans (h g hg) (mul_le_mul (ENNReal.ofReal_le_ofReal hpow) le_rfl hJ0 hof0)

/-! ## The level bump in the narrow regime `1 ≤ 2^{s(d−χ)}` -/

/-- **The level bump is an `IWMult` in the narrow regime** `1 ≤ 2^{s(d−χ)}`: for every `r ≥ 2`
there is `K` with `IWMult r (mstEta d χ η s) (K·Mη)` (and the conjugate version) whenever `η` has
Mikhlin data `Mη`, is `C²` and vanishes off `[-1/2,1/2]`. -/
theorem iwMult_mstEta_narrow (r : ℕ) (hr : 2 ≤ r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (Mη : ℝ), 0 < Mη →
      ContDiff ℝ 2 η → (∀ x : ℝ, ‖η x‖ ≤ Mη) →
      (∀ x : ℝ, |x| * ‖deriv η x‖ ≤ Mη) →
      (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ Mη) →
      (∀ x : ℝ, 1 / 2 < |x| → η x = 0) → ∀ s : ℕ,
        1 ≤ (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) →
        IWMult r (mstEta d χ η s) (K * Mη) ∧
        IWMult r (fun ξ => star (mstEta d χ η s ξ)) (K * Mη) := by
  have hr1 : (1 : ℝ) < 2 * (r : ℝ) := by
    have : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    linarith
  obtain ⟨C, hCpos, hC⟩ := mikhlin_multiplier_lift (2 * (r : ℝ)) hr1
  refine ⟨C, hCpos, ?_⟩
  intro d χ η Mη hMη hcd hbdd hder1 hder2 hsupp s hs
  have hMη0 : 0 ≤ Mη := hMη.le
  have hsupp' : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0 := eta_supp_closed hcd.continuous hsupp
  have hc : (1:ℝ) ≤ |(2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))| := by
    rw [abs_of_nonneg (by positivity)]; exact hs
  have hdata := mikhlin_conditions_scaled_bump (η := η) (M := Mη)
    (c := (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))) hMη0 hc hcd hbdd hder1 hder2 hsupp'
  obtain ⟨hcont, hb, hd1, hd2⟩ := hdata
  have hmain : IWMult r (mstEta d χ η s) (C * Mη) :=
    hC (mstEta d χ η s) Mη hMη0 hcont hb hd1 hd2
  refine ⟨hmain, ?_⟩
  have hcds : ContDiff ℝ 2 (fun x : ℝ => star (η x)) := Complex.conjCLE.contDiff.comp hcd
  have hbs : ∀ x : ℝ, ‖star (η x)‖ ≤ Mη := fun x => by rw [norm_star]; exact hbdd x
  have hd1s : ∀ x : ℝ, |x| * ‖deriv (fun x : ℝ => star (η x)) x‖ ≤ Mη := by
    intro x; rw [deriv.star', norm_star]; exact hder1 x
  have hd2s : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 (fun x : ℝ => star (η x)) x‖ ≤ Mη := by
    intro x
    have h2 : iteratedDeriv 2 (fun x : ℝ => star (η x)) x = star (iteratedDeriv 2 η x) := by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv.star']
    rw [h2, norm_star]; exact hder2 x
  have hss : ∀ x : ℝ, 1 / 2 < |x| → star (η x) = 0 := fun x hx => by
    rw [hsupp x hx, star_zero]
  have hss' : ∀ x : ℝ, 1 / 2 ≤ |x| → star (η x) = 0 :=
    eta_supp_closed hcds.continuous hss
  have hdata2 := mikhlin_conditions_scaled_bump (η := fun x => star (η x)) (M := Mη)
    (c := (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))) hMη0 hc hcds hbs hd1s hd2s hss'
  obtain ⟨hcont2, hb2, hd12, hd22⟩ := hdata2
  have hkey : IWMult r (fun ξ => star (η ((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) * iwRep ξ)))
      (C * Mη) := hC _ Mη hMη0 hcont2 hb2 hd12 hd22
  have hfun : (fun ξ => star (mstEta d χ η s ξ))
      = fun ξ => star (η ((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) * iwRep ξ)) := by
    funext ξ; rw [mstEta_apply]
  rw [hfun]
  exact hkey

/-! ## `MemLp ⊤` membership of the two symbols

`iwMult_mul` (the multiplicativity of the multiplier bound) is stated for `MemLp ⊤` symbols; here
are the two instances needed by the assembly: the signed profile-difference symbol `Θ_ε` read on the
circle, and the level bump `η_s`.
-/

/-- A continuous function is `MemLp ⊤` for the restricted volume on the fundamental domain
`Ioc (-1/2) (1/2]`: that restricted measure is finite and the fundamental domain is contained in the
compact interval `Icc (-1/2) (1/2)`, where `f` is bounded. -/
lemma mstTB_memLp_restrict_Ioc_of_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    MeasureTheory.MemLp f ⊤
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (-(1/2 : ℝ)) (1/2))) := by
  haveI : MeasureTheory.IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
        (Set.Ioc (-(1/2 : ℝ)) (1/2))) := by
    refine MeasureTheory.isFiniteMeasure_restrict.mpr ?_
    rw [Real.volume_Ioc]
    norm_num
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-(1/2 : ℝ)) (-(1/2) + 1)) hf.continuousOn
  refine MeasureTheory.MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall (fun x hx => hC x ⟨le_of_lt hx.1, by linarith [hx.2]⟩)

/-- `Θ_ε` read on the circle through `iwRep` is an `L^∞`-class (it is continuous on the fundamental
domain, which has finite measure). -/
lemma memLp_mstTheta (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) :
    MeasureTheory.MemLp (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
      mstThetaEps P i M ε (iwRep ξ)) ⊤ (AddCircle.haarAddCircle (T := 1)) := by
  refine memLp_comp_iwRep (g := mstThetaEps P i M ε) ?_
  refine mstTB_memLp_restrict_Ioc_of_continuous ?_
  unfold mstThetaEps
  exact continuous_finsetSum _ (fun j _ =>
    Continuous.mul continuous_const
      (((contDiff_polyProfile P (2 ^ ((j + 1) * 2 ^ i))).continuous).sub
        (contDiff_polyProfile P (2 ^ (j * 2 ^ i))).continuous))

/-- The level bump `mstEta d χ η s` is an `L^∞`-class whenever `η` is continuous and bounded. -/
lemma mstTB_memLp_mstEta {d : ℕ} {χ : ℝ} {η : ℝ → ℂ} {s : ℕ} (hcont : Continuous η) :
    MeasureTheory.MemLp (mstEta d χ η s) ⊤ (AddCircle.haarAddCircle (T := 1)) := by
  refine memLp_comp_iwRep
    (g := fun x : ℝ => η (((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))) * x)) ?_
  exact mstTB_memLp_restrict_Ioc_of_continuous (hcont.comp (continuous_const.mul continuous_id))

/-! ## The level bump in the wide regime `2^{s(d−χ)} < 1`

The lift of the level bump is the *truncated* rescaled bump
`x ↦ 1_{Ioc(-1/2,1/2)}(x) · η(-(2^{s(d−χ)} x))`.  In the wide regime the truncation is a genuine
jump (the rescaled bump reaches past the fundamental domain), so Mikhlin's theorem does not apply to
the lift itself; `truncated_mikhlin_multiplier` supplies the `L^p` bound nevertheless, with constant
`O(Mη)`.
-/

/-- The value of the level bump's fundamental-domain lift at a point `≠ 1/2`. -/
lemma circleLift_mstEta_eq (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) {x : ℝ} (hx : x ≠ 1 / 2) :
    Work.BourgainPlan.Thm52.circleLift (mstEta d χ η s) x
      = (if x ∈ Set.Ioo (-(1/2 : ℝ)) (1/2)
          then η ((-((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))) * x) else 0) := by
  by_cases hmem : x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2)
  · have hlt : x < 1 / 2 := lt_of_le_of_ne hmem.2 hx
    have hIoo : x ∈ Set.Ioo (-(1/2 : ℝ)) (1/2) := ⟨hmem.1, hlt⟩
    rw [if_pos hIoo, Work.BourgainPlan.Thm52.circleLift_of_mem hmem, mstEta_apply]
    have hcoe : -((x : ℝ) : Work.BourgainPlan.IonescuWainger.Circle)
        = ((-x : ℝ) : Work.BourgainPlan.IonescuWainger.Circle) :=
      (AddCircle.coe_neg (1 : ℝ) (x := x)).symm
    rw [hcoe]
    have hrep : iwRep ((-x : ℝ) : Work.BourgainPlan.IonescuWainger.Circle) = -x := by
      simp only [iwRep]
      exact AddCircle.liftIoc_coe_apply ⟨by linarith [hlt], by linarith [hmem.1]⟩
    rw [hrep]
    congr 1
    ring
  · have hnotIoo : x ∉ Set.Ioo (-(1/2 : ℝ)) (1/2) := fun h => hmem ⟨h.1, le_of_lt h.2⟩
    rw [if_neg hnotIoo, Work.BourgainPlan.Thm52.circleLift_of_notMem hmem]

/-- **The wide-regime transfer**: if the rescaled bump `x ↦ η (a x)` (`a = -(2^{s(d-χ)})`) satisfies
the Mikhlin conditions with constant `Mη`, then the level bump's `IWMult` has the constant `C·Mη`,
where `C` is the constant of `truncated_mikhlin_multiplier`. -/
lemma iwMult_mstEta_of_trunc {r : ℕ} {C Mη : ℝ} {d : ℕ} {χ : ℝ} {η : ℝ → ℂ} (s : ℕ)
    (hC : ∀ (m : ℝ → ℂ) (A a b : ℝ), 0 ≤ A → a < b → ContDiff ℝ 2 m →
      (∀ ξ : ℝ, ‖m ξ‖ ≤ A) → (∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ A) →
      (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A) →
      ∀ (g : ℝ → ℂ), Integrable g →
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0)
              * FourierTransform.fourier g ξ) x‖ₑ ^ (2 * (r : ℝ)) ∂(volume : Measure ℝ)
          ≤ ENNReal.ofReal ((C * A) ^ (2 * (r : ℝ)))
            * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) ∂(volume : Measure ℝ))
    (hMη : 0 ≤ Mη)
    (hcd : ContDiff ℝ 2 (fun x : ℝ => η ((-((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))) * x)))
    (hb : ∀ x : ℝ, ‖η ((-((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))) * x)‖ ≤ Mη)
    (hd1 : ∀ x : ℝ, |x| * ‖deriv (fun x : ℝ =>
      η ((-((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))) * x)) x‖ ≤ Mη)
    (hd2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 (fun x : ℝ =>
      η ((-((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))) * x)) x‖ ≤ Mη) :
    IWMult r (mstEta d χ η s) (C * Mη) := by
  intro g hg
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 / 2 := by
    rw [MeasureTheory.ae_iff]; simp
  have hfun : (fun x : ℝ => ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => Work.BourgainPlan.Thm52.circleLift (mstEta d χ η s) ξ
          * FourierTransform.fourier g ξ) x‖ₑ ^ (2 * (r : ℝ)))
      =ᵐ[volume] fun x : ℝ => ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo (-(1/2 : ℝ)) (1/2)
            then η ((-((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))) * ξ) else 0)
          * FourierTransform.fourier g ξ) x‖ₑ ^ (2 * (r : ℝ)) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hinner : FourierTransformInv.fourierInv
          (fun ξ : ℝ => Work.BourgainPlan.Thm52.circleLift (mstEta d χ η s) ξ
            * FourierTransform.fourier g ξ) x
        = FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo (-(1/2 : ℝ)) (1/2)
              then η ((-((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))) * ξ) else 0)
            * FourierTransform.fourier g ξ) x := by
      rw [Real.fourierInv_eq', Real.fourierInv_eq']
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hne] with ξ hξ
      rw [circleLift_mstEta_eq d χ η s hξ]
    show ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => Work.BourgainPlan.Thm52.circleLift (mstEta d χ η s) ξ
          * FourierTransform.fourier g ξ) x‖ₑ ^ (2 * (r : ℝ))
      = ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo (-(1/2 : ℝ)) (1/2)
            then η ((-((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))) * ξ) else 0)
          * FourierTransform.fourier g ξ) x‖ₑ ^ (2 * (r : ℝ))
    rw [hinner]
  have htrunc := hC (fun x : ℝ => η ((-((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))) * x)) Mη
    (-(1/2)) (1/2) hMη (by norm_num) hcd hb hd1 hd2
  exact le_trans (le_of_eq (MeasureTheory.lintegral_congr_ae hfun)) (htrunc g hg)

/-- **The level bump is an `IWMult` in the wide regime** `2^{s(d−χ)} < 1` (and in general, without
any restriction on the coefficient): same statement as `iwMult_mstEta_narrow`, from
`truncated_mikhlin_multiplier` and the scale invariance of the Mikhlin conditions. -/
theorem iwMult_mstEta_wide (r : ℕ) (hr : 2 ≤ r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (Mη : ℝ), 0 < Mη →
      ContDiff ℝ 2 η → (∀ x : ℝ, ‖η x‖ ≤ Mη) →
      (∀ x : ℝ, |x| * ‖deriv η x‖ ≤ Mη) →
      (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ Mη) →
      (∀ x : ℝ, 1 / 2 < |x| → η x = 0) → ∀ s : ℕ,
        IWMult r (mstEta d χ η s) (K * Mη) ∧
        IWMult r (fun ξ => star (mstEta d χ η s ξ)) (K * Mη) := by
  have hr1 : (1 : ℝ) < 2 * (r : ℝ) := by
    have : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    linarith
  obtain ⟨C, hCpos, hC⟩ := truncated_mikhlin_multiplier (2 * (r : ℝ)) hr1
  refine ⟨C, hCpos, ?_⟩
  intro d χ η Mη hMη hcd hbdd hder1 hder2 hsupp s
  have hMη0 : 0 ≤ Mη := hMη.le
  have hdata := scaled_bump_mikhlin_bounds (η := η) (M := Mη)
    (d := -((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))) hcd hbdd hder1 hder2
  obtain ⟨hmcd, hmb, hmd1, hmd2⟩ := hdata
  have hcds : ContDiff ℝ 2 (fun x : ℝ => star (η x)) := Complex.conjCLE.contDiff.comp hcd
  have hbs : ∀ x : ℝ, ‖star (η x)‖ ≤ Mη := fun x => by rw [norm_star]; exact hbdd x
  have hd1s : ∀ x : ℝ, |x| * ‖deriv (fun x : ℝ => star (η x)) x‖ ≤ Mη := by
    intro x; rw [deriv.star', norm_star]; exact hder1 x
  have hd2s : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 (fun x : ℝ => star (η x)) x‖ ≤ Mη := by
    intro x
    have h2 : iteratedDeriv 2 (fun x : ℝ => star (η x)) x = star (iteratedDeriv 2 η x) := by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv.star']
    rw [h2, norm_star]; exact hder2 x
  have hdata2 := scaled_bump_mikhlin_bounds (η := fun x => star (η x)) (M := Mη)
    (d := -((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))) hcds hbs hd1s hd2s
  obtain ⟨hmcd2, hmb2, hmd12, hmd22⟩ := hdata2
  refine ⟨iwMult_mstEta_of_trunc s hC hMη0 hmcd hmb hmd1 hmd2, ?_⟩
  have hkey : IWMult r (mstEta d χ (fun x => star (η x)) s) (C * Mη) :=
    iwMult_mstEta_of_trunc s hC hMη0 hmcd2 hmb2 hmd12 hmd22
  have hfun : (fun ξ => star (mstEta d χ η s ξ)) = mstEta d χ (fun x => star (η x)) s := by
    funext ξ
    rw [mstEta_apply, mstEta_apply]
  rw [hfun]
  exact hkey

/-! ## The two regimes combined -/

/-- **The level bump is an `IWMult` with constant `O(Mη)`** (no restriction on the level
coefficient): the narrow case `1 ≤ 2^{s(d−χ)}` is `iwMult_mstEta_narrow`, the wide case
`2^{s(d−χ)} < 1` is `iwMult_mstEta_wide`. -/
theorem iwMult_mstEta (r : ℕ) (hr : 2 ≤ r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (Mη : ℝ), 0 < Mη →
      ContDiff ℝ 2 η → (∀ x : ℝ, ‖η x‖ ≤ Mη) →
      (∀ x : ℝ, |x| * ‖deriv η x‖ ≤ Mη) →
      (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ Mη) →
      (∀ x : ℝ, 1 / 2 < |x| → η x = 0) → ∀ s : ℕ,
        IWMult r (mstEta d χ η s) (K * Mη) ∧
        IWMult r (fun ξ => star (mstEta d χ η s ξ)) (K * Mη) := by
  obtain ⟨K₁, hK₁pos, hK₁⟩ := iwMult_mstEta_narrow r hr
  obtain ⟨K₂, hK₂pos, hK₂⟩ := iwMult_mstEta_wide r hr
  refine ⟨max K₁ K₂, lt_max_of_lt_left hK₁pos, ?_⟩
  intro d χ η Mη hMη hcd hbdd hder1 hder2 hsupp s
  by_cases hc : 1 ≤ (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))
  · obtain ⟨h1, h2⟩ := hK₁ d χ η Mη hMη hcd hbdd hder1 hder2 hsupp s hc
    have hle : K₁ * Mη ≤ max K₁ K₂ * Mη :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hMη.le
    exact ⟨IWMult_mono (by positivity) hle h1, IWMult_mono (by positivity) hle h2⟩
  · push_neg at hc
    obtain ⟨h1, h2⟩ := hK₂ d χ η Mη hMη hcd hbdd hder1 hder2 hsupp s
    have hle : K₂ * Mη ≤ max K₁ K₂ * Mη :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hMη.le
    exact ⟨IWMult_mono (by positivity) hle h1, IWMult_mono (by positivity) hle h2⟩

/-! ## The assembly: MSTThetaBound -/

/-- **The conditional reduction**: MST's *raw* input `(C2)` — the unweighted signed symbols `Θ_ε`
are `IWMult`s with a constant uniform in the level, the number of terms and the signs — implies
`MSTThetaBound`.  The proof is the assembly: multiply the `Θ_ε`-bound by the level bump's bound
(`iwMult_mstEta`, both regimes) using the multiplicativity of multiplier norms
(`iwMult_mul`). -/
theorem mst_theta_bound_of_raw
    (hraw : ∀ (P : Polynomial ℤ), 2 ≤ P.natDegree → 0 < P.leadingCoeff → ∀ r : ℕ, 2 ≤ r →
      ∃ A : ℝ, 0 < A ∧ MSTThetaRawMult P r A) : MSTThetaBound := by
  intro P hdeg hlc r hr
  obtain ⟨A, hApos, hrawP⟩ := hraw P hdeg hlc r hr
  obtain ⟨K, hKpos, hbump⟩ := iwMult_mstEta r hr
  refine ⟨A * K, by positivity, ?_⟩
  intro d χ η Mη hMη hcd hbdd hder1 hder2 hsupp i M s ε hε
  obtain ⟨hb1, hb2⟩ := hbump d χ η Mη hMη hcd hbdd hder1 hder2 hsupp s
  obtain ⟨hr1, hr2⟩ := hrawP i M ε hε
  have hAK : 0 ≤ A * K := by positivity
  have hB : 0 ≤ K * Mη := by positivity
  have hmTh : MeasureTheory.MemLp (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
      mstThetaEps P i M ε (iwRep ξ)) ⊤ (AddCircle.haarAddCircle (T := 1)) :=
    memLp_mstTheta P i M ε
  have hmEta : MeasureTheory.MemLp (mstEta d χ η s) ⊤ (AddCircle.haarAddCircle (T := 1)) :=
    mstTB_memLp_mstEta hcd.continuous
  have hmEtaStar : MeasureTheory.MemLp (fun ξ => star (mstEta d χ η s ξ)) ⊤
      (AddCircle.haarAddCircle (T := 1)) :=
    MeasureTheory.MemLp.star hmEta
  have hmThStar : MeasureTheory.MemLp (fun ξ =>
      star (mstThetaEps P i M ε (iwRep ξ))) ⊤ (AddCircle.haarAddCircle (T := 1)) :=
    MeasureTheory.MemLp.star hmTh
  constructor
  · have h := iwMult_mul hApos.le hB hmTh hmEta hr1 hb1
    have hconst : A * (K * Mη) = (A * K) * Mη := by ring
    rw [hconst] at h
    exact h
  · have hmul := iwMult_mul hApos.le hB hmThStar hmEtaStar hr2 hb2
    have hconst : A * (K * Mη) = (A * K) * Mη := by ring
    have hfun : (fun ξ => star (mstThetaEps P i M ε (iwRep ξ)) * star (mstEta d χ η s ξ))
        = fun ξ => star (mstThetaSym P d χ η i M s ε ξ) := by
      funext ξ
      rw [mstThetaSym_apply, star_mul]
      exact mul_comm _ _
    rw [hconst, hfun] at hmul
    exact hmul

/-- **MST's input `(C2)`** (`MSTThetaBound`, MST Theorem 17 / the citation of the continuous singular
Radon transform theory): the signed lacunary profile-difference symbols `Θ_ε · η_s` (and their
conjugates) are `L^{2r}(ℝ)`-multipliers with norm `≤ A · Mη`, uniformly in the level, the number of
terms, the signs and the level bump.

This is `mst_theta_bound_of_raw` applied to the raw input `mst_theta_raw`, i.e. the assembly of the
delegated analytic input with the (elementary) multiplier bookkeeping of this file. -/
theorem mst_theta_bound : Work.BourgainPlan.Maximal.MSTThetaBound :=
  mst_theta_bound_of_raw (fun P hdeg hlc r hr => mst_theta_raw P hdeg hlc r hr)

end

end Work.BourgainPlan.Maximal
