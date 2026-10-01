import Mathlib
import Submission.Work.LinnikAreas.ZetaPrincipalDefs
import Submission.Work.LinnikAreas.ZetaTentPrelude
import Submission.Work.LinnikAreas.zeta_perron_tent
import Submission.Work.LinnikAreas.rectInt_logDeriv_entire_mul
import Submission.Work.LinnikAreas.rectInt_logDeriv_completedRiemannZeta
import Submission.Work.LinnikAreas.zeta_logDeriv_negHalf_bound
import Submission.Work.LinnikAreas.zeta1_goodHeight_horizontal_vanishing
import Submission.Work.LinnikAreas.zetaBallSum_strip_tendsto
import Submission.Work.LinnikAreas.completedRiemannZeta_zero_strip
import Submission.Work.LinnikAreas.tent_zeta_leftEdge_bound
import Submission.Work.LinnikAreas.logDeriv_completedRiemannZeta_eq
import Submission.Work.LinnikAreas.completedRiemannZeta_ne_zero_rectBoundary
import Submission.Work.LinnikAreas.horizontal_vanishing_completedRiemannZeta
import Submission.Work.LinnikAreas.integrable_logDeriv_completedRiemannZeta_strip

open Complex Filter MeasureTheory
open scoped Topology BigOperators

namespace Work.LinnikAreas

noncomputable section

lemma linePt_left_re (t : ℝ) : ((((-1/2 : ℝ)) : ℂ) + (t:ℂ)*Complex.I).re = -(1/2) := by
  simp
  norm_num

lemma linePt_two_re (t : ℝ) : ((2:ℂ) + (t:ℂ)*Complex.I).re = 2 := by
  simp

lemma corner_left_re (v : ℝ) : ((((-1/2 : ℝ)) : ℂ) - (v:ℂ)*Complex.I).re = -(1/2) := by
  simp
  norm_num

lemma corner_left_im (v : ℝ) : ((((-1/2 : ℝ)) : ℂ) - (v:ℂ)*Complex.I).im = -v := by
  simp

lemma corner_right_re (v : ℝ) : ((2:ℂ) + (v:ℂ)*Complex.I).re = 2 := by
  simp

lemma corner_right_im (v : ℝ) : ((2:ℂ) + (v:ℂ)*Complex.I).im = v := by
  simp

lemma half_form_bridge : ((((-1/2 : ℝ)) : ℂ)) = ((-(1/2) : ℂ)) := by norm_num

lemma linePt_left_ne_zero (t : ℝ) : ((((-1/2 : ℝ)) : ℂ) + (t:ℂ)*Complex.I) ≠ (0:ℂ) := by
  intro h
  have h2 := congrArg Complex.re h
  rw [linePt_left_re, Complex.zero_re] at h2
  norm_num at h2

lemma linePt_left_ne_one (t : ℝ) : ((((-1/2 : ℝ)) : ℂ) + (t:ℂ)*Complex.I) ≠ (1:ℂ) := by
  intro h
  have h2 := congrArg Complex.re h
  rw [linePt_left_re, Complex.one_re] at h2
  norm_num at h2

lemma linePt_left_re_gt (t : ℝ) : -(1:ℝ) < ((((-1/2 : ℝ)) : ℂ) + (t:ℂ)*Complex.I).re := by
  rw [linePt_left_re]; norm_num

lemma linePt_two_ne_zero (t : ℝ) : ((2:ℂ) + (t:ℂ)*Complex.I) ≠ (0:ℂ) := by
  intro h
  have h2 := congrArg Complex.re h
  rw [linePt_two_re, Complex.zero_re] at h2
  norm_num at h2

lemma linePt_two_ne_one (t : ℝ) : ((2:ℂ) + (t:ℂ)*Complex.I) ≠ (1:ℂ) := by
  intro h
  have h2 := congrArg Complex.re h
  rw [linePt_two_re, Complex.one_re] at h2
  norm_num at h2

lemma linePt_two_re_gt (t : ℝ) : -(1:ℝ) < ((2:ℂ) + (t:ℂ)*Complex.I).re := by
  rw [linePt_two_re]; norm_num

/-- `a + t*I ≠ b` for distinct real `a, b`. -/
lemma cplx_add_I_ne {a b : ℝ} (h : a ≠ b) (t : ℝ) : (a:ℂ) + (t:ℂ)*Complex.I ≠ (b:ℂ) := by
  intro hh
  have h2 := congrArg Complex.re hh
  simp at h2
  exact h (by simpa using h2)

/-- The tent kernel `tentPhi L K q` at the point `1` is `K ^ 2`. -/
lemma tentPhi_one (L K : ℝ) (q : ℕ) :
    Commons.NumberTheory.Linnik.tentPhi L K q 1 = (K : ℂ) ^ 2 := by
  unfold Commons.NumberTheory.Linnik.tentPhi Commons.NumberTheory.Linnik.tentK
  rw [show ((1 : ℂ) - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ) = 0 by ring]
  simp [Commons.NumberTheory.Linnik.tentH_zero]

/-- The analytic order vanishes at a point where the function does not vanish. -/
lemma analyticOrderNatAt_eq_zero_of_ne_zero {f : ℂ → ℂ} {u : ℂ} (h : f u ≠ 0) :
    analyticOrderNatAt f u = 0 := by
  rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr h)]
  rfl

/-- The tent kernel at the origin (i.e. at the pole `s = 0` of `Λ`), bounded by `q ^ (-(49/10))`. -/
lemma norm_tentPhi_zero_le (q : ℕ) (hq : 2 ≤ q) :
    ‖Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q 0‖ ≤ (q : ℝ) ^ (-(49:ℝ)/10) := by
  have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hz0 : ((Real.log (q:ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogpos.ne'
  rw [show Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q 0 =
      Commons.NumberTheory.Linnik.tentK (11/2) (3/10) ((Real.log (q:ℝ) : ℝ) : ℂ) from by
    simp [Commons.NumberTheory.Linnik.tentPhi]]
  rw [Commons.NumberTheory.Linnik.tentK_eq_closed (11/2) (3/10) _ hz0]
  rw [show ((11:ℝ)/2 - 2 * (3/10) : ℝ) = 49/10 by norm_num]
  rw [norm_mul, norm_pow, Complex.norm_exp]
  rw [show (-(((49/10:ℝ):ℂ) * ((Real.log (q:ℝ) : ℝ) : ℂ))).re = -(49/10) * Real.log (q:ℝ) by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    ring]
  rw [show Real.exp (-(49/10) * Real.log (q:ℝ)) = (q:ℝ) ^ (-(49:ℝ)/10) from by
    rw [show (-(49/10) * Real.log (q:ℝ)) = Real.log ((q:ℝ) ^ (-(49:ℝ)/10)) from by
      rw [Real.log_rpow (by positivity)]
      ring]
    rw [Real.exp_log (Real.rpow_pos_of_pos (by positivity) _)]]
  have hb : ‖(1 - Complex.exp (-(((3/10:ℝ):ℂ) * ((Real.log (q:ℝ) : ℝ) : ℂ)))) /
      ((Real.log (q:ℝ) : ℝ) : ℂ)‖ ≤ (3/10:ℝ) := by
    rw [norm_div]
    have h1 : ‖1 - Complex.exp (-(((3/10:ℝ):ℂ) * ((Real.log (q:ℝ) : ℝ) : ℂ)))‖ ≤
        ‖(((3/10:ℝ):ℂ) * ((Real.log (q:ℝ) : ℝ) : ℂ))‖ := by
      apply Commons.NumberTheory.Linnik.norm_one_sub_exp_neg_le
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      simp
      positivity
    calc ‖1 - Complex.exp (-(((3/10:ℝ):ℂ) * ((Real.log (q:ℝ) : ℝ) : ℂ)))‖ /
          ‖((Real.log (q:ℝ) : ℝ) : ℂ)‖
        ≤ ‖(((3/10:ℝ):ℂ) * ((Real.log (q:ℝ) : ℝ) : ℂ))‖ / ‖((Real.log (q:ℝ) : ℝ) : ℂ)‖ :=
          div_le_div_of_nonneg_right h1 (norm_nonneg _)
      _ = (3/10:ℝ) := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by norm_num : (0:ℝ)<3/10), abs_of_pos hlogpos]
          field_simp
  calc (q:ℝ) ^ (-(49:ℝ)/10) *
        ‖(1 - Complex.exp (-(((3/10:ℝ):ℂ) * ((Real.log (q:ℝ) : ℝ) : ℂ)))) /
          ((Real.log (q:ℝ) : ℝ) : ℂ)‖ ^ 2
      ≤ (q:ℝ) ^ (-(49:ℝ)/10) * (3/10:ℝ)^2 := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
        exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ ≤ (q:ℝ) ^ (-(49:ℝ)/10) * 1 := by
        apply mul_le_mul_of_nonneg_left (by norm_num) (Real.rpow_nonneg (by positivity) _)
    _ = (q:ℝ) ^ (-(49:ℝ)/10) := by ring

/-- **The principal-character (`ζ`) tent explicit formula.** -/
theorem zetaTentExplicit :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ Z : ℂ,
      (Filter.Tendsto (fun ρ : ℝ => Work.LinnikAreas.zetaBallSum q ρ) Filter.atTop (nhds Z)) →
      ∀ X : ℕ, (q : ℝ) ^ ((11:ℝ)/2) ≤ (X : ℝ) →
        ‖((Real.log (q : ℝ)) : ℂ)⁻¹ *
            (∑ n ∈ Finset.Icc 1 X, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
              ((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
                (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)) + Z‖
          ≤ C * ((q : ℝ) ^ (-(49:ℝ)/10) +
              (Real.log (q : ℝ))⁻¹ * ((q : ℝ) ^ (-(147:ℝ)/20)) * (1 + Real.log (q : ℝ))) := by
  obtain ⟨Cle, hClepos, hCle⟩ := tent_zeta_leftEdge_bound
  refine ⟨1 + Cle, by linarith, ?_⟩
  intro q hq Z hZ X hX
  have hq1 : 1 < q := by omega
  have hqR : (1:ℝ) < (q:ℝ) := by exact_mod_cast hq1
  have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos hqR
  -- ### the tent kernel
  set Φ : ℂ → ℂ := Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q with hΦdef
  have hΦval : ∀ u : ℂ, Φ u = Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q u :=
    fun u => by rw [hΦdef]
  have hΦdiff : Differentiable ℂ Φ := by
    rw [hΦdef]; exact Commons.NumberTheory.Linnik.tentPhi_diff (11/2) (3/10) q
  have hΦ0 : ‖Φ 0‖ ≤ (q:ℝ)^(-(49:ℝ)/10) := by rw [hΦdef]; exact norm_tentPhi_zero_le q hq
  -- ### Perron's identity
  have hper := zeta_perron_tent (L := (11/2:ℝ)) (K := (3/10:ℝ)) (by norm_num) (by norm_num)
    (q := q) hq (X := X) hX
  -- ### good heights
  obtain ⟨c, hcpos, T', hT'win, hT'sep, hVan1, hVan2⟩ :=
    zeta1_goodHeight_horizontal_vanishing (L := (11/2:ℝ)) (K := (3/10:ℝ)) (by norm_num) (by norm_num)
      (q := q) hq
  have hT'growth : ∀ T : ℝ, 1 ≤ T → T + 1 ≤ T' T := fun T hT => (hT'win T hT).1
  have hT'top : Filter.Tendsto T' Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop (max 1 (b - 1))] with T hT
    have h1 : 1 ≤ T := le_trans (le_max_left _ _) hT
    have h2 : b - 1 ≤ T := le_trans (le_max_right _ _) hT
    have h3 := hT'growth T h1
    linarith
  -- ### the ball-sum hypothesis in the strip form
  have hstrip := zetaBallSum_strip_tendsto (q := q) hq hZ
  -- ### integrability / horizontal vanishing
  obtain ⟨hintΛ2, hintΛl⟩ := integrable_logDeriv_completedRiemannZeta_strip (q := q) hq
  obtain ⟨hvanΛp, hvanΛm⟩ :=
    horizontal_vanishing_completedRiemannZeta (q := q) hq hcpos hT'growth hT'sep hVan1 hVan2
  -- ### the integrand
  set F : ℂ → ℂ := fun s => logDeriv completedRiemannZeta s * Φ s with hFdef
  have hF2 : MeasureTheory.Integrable (fun t : ℝ => F ((2:ℂ) + (t:ℂ) * Complex.I)) := by
    simpa [hFdef, hΦdef] using hintΛ2
  have hFl : MeasureTheory.Integrable (fun t : ℝ => F ((((-1/2 : ℝ))) + (t:ℂ) * Complex.I)) := by
    simpa [hFdef, hΦdef] using hintΛl
  set A2 : ℂ := ∫ t : ℝ, F ((2:ℂ) + (t:ℂ) * Complex.I) with hA2def
  set A1 : ℂ := ∫ t : ℝ, F ((((-1/2 : ℝ))) + (t:ℂ) * Complex.I) with hA1def
  -- ### the rectangle identity
  have hrect : ∀ T : ℝ, 1 ≤ T →
      Commons.NumberTheory.DirichletCharacter.rectInt (((((-1/2 : ℝ)) : ℂ) - ((T' T:ℝ):ℂ)*Complex.I))
          ((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I) F
        = 2 * (Real.pi:ℂ) * Complex.I *
            ((∑ᶠ u : ℂ, (if |u.im| < T' T then
                ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℂ) * Φ u else 0))
              - Φ 1 - Φ 0) := by
    intro T hT
    have hT'2 : 2 ≤ T' T := by have := hT'growth T hT; linarith
    have hbd : ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectBoundary
        (((((-1/2 : ℝ)) : ℂ)) - ((T' T:ℝ):ℂ)*Complex.I) ((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I),
        completedRiemannZeta s ≠ 0 ∧ s ≠ 0 ∧ s ≠ 1 :=
      fun s hs => completedRiemannZeta_ne_zero_rectBoundary (c := c) (T' := T' T) hcpos hT'2
        (fun ρ hρ => hT'sep T hT ρ hρ) hs
    have hmain := rectInt_logDeriv_completedRiemannZeta (G := Φ) hΦdiff
      (by rw [corner_left_re, corner_right_re]; norm_num)
      (by rw [corner_left_im, corner_right_im]; linarith)
      (by rw [corner_left_re]; norm_num)
      (by rw [corner_right_re]; norm_num)
      (by rw [corner_left_re]; norm_num)
      (by rw [corner_right_re]; norm_num)
      (by rw [corner_left_im]; linarith)
      (by rw [corner_right_im]; linarith)
      (fun s hs => (hbd s hs).1) (fun s hs => (hbd s hs).2)
    rw [hFdef]
    rw [hmain]
    congr 1
    rw [sub_left_inj, sub_left_inj]
    apply finsum_congr
    intro u
    rw [corner_left_re, corner_right_re, corner_left_im, corner_right_im]
    by_cases hzero : analyticOrderNatAt completedRiemannZeta u = 0
    · rw [hzero]; simp
    · have hΛu : completedRiemannZeta u = 0 := by
        by_contra hc
        exact hzero (analyticOrderNatAt_eq_zero_of_ne_zero hc)
      have hst := completedRiemannZeta_zero_strip hΛu
      by_cases hc : |u.im| < T' T
      · rw [if_pos ⟨by linarith [hst.1], by linarith [hst.2],
            (abs_lt.mp hc).1, (abs_lt.mp hc).2⟩, if_pos hc]
      · rw [if_neg (by intro hh; exact hc (abs_lt.mpr ⟨hh.2.2.1, hh.2.2.2⟩)), if_neg hc]
  -- ### the limit of the rectangle integrals
  have hlimrect : Filter.Tendsto
      (fun T : ℝ => Commons.NumberTheory.Zeta.rectInt (((((-1/2 : ℝ)) : ℂ)) - ((T' T:ℝ):ℂ)*Complex.I)
          ((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I) F) Filter.atTop
      (nhds (Complex.I * (A2 - A1))) := by
    have hnegtop : Filter.Tendsto (fun T : ℝ => -(T' T)) Filter.atTop Filter.atBot := by
      rw [Filter.tendsto_atBot]
      intro a
      filter_upwards [Filter.eventually_ge_atTop (max 1 (-a - 1))] with T hT
      have h1 : 1 ≤ T := le_trans (le_max_left _ _) hT
      have h2 : -a - 1 ≤ T := le_trans (le_max_right _ _) hT
      have h3 := hT'growth T h1
      linarith
    have hC : Filter.Tendsto
        (fun T : ℝ => ∫ y : ℝ in (-(T' T))..(T' T), F ((2:ℂ) + (y:ℂ)*Complex.I))
        Filter.atTop (nhds A2) := by
      rw [hA2def]
      exact MeasureTheory.intervalIntegral_tendsto_integral hF2 hnegtop hT'top
    have hD : Filter.Tendsto
        (fun T : ℝ => ∫ y : ℝ in (-(T' T))..(T' T), F ((((-1/2 : ℝ))) + (y:ℂ)*Complex.I))
        Filter.atTop (nhds A1) := by
      rw [hA1def]
      exact MeasureTheory.intervalIntegral_tendsto_integral hFl hnegtop hT'top
    have hcomb := ((hvanΛm.sub hvanΛp).add (hC.const_mul Complex.I)).sub (hD.const_mul Complex.I)
    have hgoal : Complex.I * (A2 - A1) = Complex.I * A2 - Complex.I * A1 := by ring
    rw [hgoal]
    simp only [sub_zero, zero_add] at hcomb
    refine hcomb.congr' ?_
    filter_upwards with T
    exact (Commons.NumberTheory.Linnik.rectInt_strip_eq (T' T) F).symm
  -- ### the strip sums converge, hence the same limit
  have hlimstate : Filter.Tendsto
      (fun T : ℝ => (∑ᶠ u : ℂ, (if |u.im| < T' T then
          ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℂ) * Φ u else 0)) - Φ 1 - Φ 0)
      Filter.atTop (nhds ((Z + Φ 1 + Φ 0) - Φ 1 - Φ 0)) :=
    ((hstrip.comp hT'top).sub tendsto_const_nhds).sub tendsto_const_nhds
  have hlim2 : Filter.Tendsto
      (fun T : ℝ => Commons.NumberTheory.Zeta.rectInt (((((-1/2 : ℝ)) : ℂ)) - ((T' T:ℝ):ℂ)*Complex.I)
          ((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I) F) Filter.atTop
      (nhds (2 * (Real.pi:ℂ) * Complex.I * ((Z + Φ 1 + Φ 0) - Φ 1 - Φ 0))) := by
    have h := hlimstate.const_mul (2 * (Real.pi:ℂ) * Complex.I)
    refine h.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with T hT
    exact (hrect T hT).symm
  have huniq := tendsto_nhds_unique hlimrect hlim2
  -- ### the key identity
  have hkey : (1/(2*(Real.pi:ℂ))) * (A2 - A1) = Z := by
    have h2 : Complex.I * (A2 - A1) = Complex.I * (2 * (Real.pi:ℂ) * Z) := by
      rw [huniq]; ring
    have h1 : (A2 - A1) = 2 * (Real.pi:ℂ) * Z := mul_left_cancel₀ Complex.I_ne_zero h2
    rw [h1]
    have hπ : (2*(Real.pi:ℂ)) ≠ 0 := by
      have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero hp
    field_simp
  -- ### the gamma factor identity
  have hEven : (1 : DirichletCharacter ℂ 1).Even := by
    rw [DirichletCharacter.Even]
    have h : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [h]; exact map_one _
  have hgf : DirichletCharacter.gammaFactor (1 : DirichletCharacter ℂ 1) = Complex.Gammaℝ :=
    funext (fun z => hEven.gammaFactor_def z)
  set G2 : ℂ := ∫ t : ℝ, logDeriv Complex.Gammaℝ ((2:ℂ)+(t:ℂ)*Complex.I) * Φ ((2:ℂ)+(t:ℂ)*Complex.I) with hG2def
  set G1 : ℂ := ∫ t : ℝ, logDeriv Complex.Gammaℝ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) *
      Φ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) with hG1def
  have hgamma : (1/(2*(Real.pi:ℂ))) * (G2 - G1) = - Φ 0 := by
    have h := Commons.NumberTheory.Linnik.gammaFactor_shift_identity (L := (11/2:ℝ)) (K := (3/10:ℝ))
      (by norm_num) (by norm_num) (χ := (1 : DirichletCharacter ℂ 1)) (Q := q) hq
    rw [hgf] at h
    rw [if_pos hEven] at h
    rw [hG2def, hG1def]
    simpa [hΦdef] using h
  -- ### splitting the two line integrals
  set Zc2 : ℂ := ∫ t : ℝ, logDeriv riemannZeta ((2:ℂ)+(t:ℂ)*Complex.I) * Φ ((2:ℂ)+(t:ℂ)*Complex.I) with hZc2def
  set Zc1 : ℂ := ∫ t : ℝ, logDeriv riemannZeta ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) *
      Φ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) with hZc1def
  have hpt2 : ∀ t : ℝ, logDeriv completedRiemannZeta ((2:ℂ)+(t:ℂ)*Complex.I) * Φ ((2:ℂ)+(t:ℂ)*Complex.I)
      = logDeriv Complex.Gammaℝ ((2:ℂ)+(t:ℂ)*Complex.I) * Φ ((2:ℂ)+(t:ℂ)*Complex.I)
        + logDeriv riemannZeta ((2:ℂ)+(t:ℂ)*Complex.I) * Φ ((2:ℂ)+(t:ℂ)*Complex.I) := by
    intro t
    have hζ : riemannZeta ((2:ℂ)+(t:ℂ)*Complex.I) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_lt_re
      rw [linePt_two_re]; norm_num
    have h := logDeriv_completedRiemannZeta_eq (s := (2:ℂ)+(t:ℂ)*Complex.I)
      (linePt_two_ne_zero t) (linePt_two_ne_one t) (linePt_two_re_gt t) hζ
    rw [h]; ring
  have hptl : ∀ t : ℝ, logDeriv completedRiemannZeta ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) *
        Φ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I)
      = logDeriv Complex.Gammaℝ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) * Φ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I)
        + logDeriv riemannZeta ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) * Φ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) := by
    intro t
    have hΛne : completedRiemannZeta ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) ≠ 0 := by
      intro h0
      have h1 := (completedRiemannZeta_zero_strip h0).1
      rw [linePt_left_re] at h1
      norm_num at h1
    have hne : riemannZeta ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) ≠ 0 := by
      intro h0
      apply hΛne
      have hfac := Commons.NumberTheory.DirichletCharacter.completedL_eq_gammaFactor_mul_L
        (1 : DirichletCharacter ℂ 1) (s := ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I))
        (linePt_left_ne_zero t) (linePt_left_re_gt t)
      rw [DirichletCharacter.completedLFunction_modOne_eq, hgf, DirichletCharacter.LFunction_modOne_eq]
        at hfac
      rw [hfac, h0, mul_zero]
    have h := logDeriv_completedRiemannZeta_eq (s := (((-1/2 : ℝ)))+(t:ℂ)*Complex.I)
      (linePt_left_ne_zero t) (linePt_left_ne_one t) (linePt_left_re_gt t) hne
    rw [h]; ring
  have hG2int : MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv Complex.Gammaℝ ((2:ℂ)+(t:ℂ)*Complex.I) * Φ ((2:ℂ)+(t:ℂ)*Complex.I)) := by
    have h := Commons.NumberTheory.Linnik.integrable_logDeriv_gammaFactor_mul_tentPhi_two
      (L := (11/2:ℝ)) (K := (3/10:ℝ)) (by norm_num) (by norm_num)
      (χ := (1 : DirichletCharacter ℂ 1)) (Q := q) hq
    rw [hgf] at h
    simpa [hΦdef] using h
  have hG1int : MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv Complex.Gammaℝ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) * Φ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I)) := by
    have h := Commons.NumberTheory.Linnik.integrable_logDeriv_gammaFactor_mul_tentPhi_left
      (L := (11/2:ℝ)) (K := (3/10:ℝ)) (by norm_num) (by norm_num)
      (χ := (1 : DirichletCharacter ℂ 1)) (Q := q) hq
    rw [hgf] at h
    simpa [hΦdef] using h
  have hZc2int : MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv riemannZeta ((2:ℂ)+(t:ℂ)*Complex.I) * Φ ((2:ℂ)+(t:ℂ)*Complex.I)) := by
    refine (hF2.sub hG2int).congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [Pi.sub_apply, hFdef]
    rw [hpt2 t]; ring
  have hZc1int : MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv riemannZeta ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) * Φ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I)) := by
    refine (hFl.sub hG1int).congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [Pi.sub_apply, hFdef]
    rw [hptl t]; ring
  have hA2split : A2 = G2 + Zc2 := by
    rw [hA2def, hG2def, hZc2def]
    have hcongr : (∫ t : ℝ, F ((2:ℂ)+(t:ℂ)*Complex.I)) = ∫ t : ℝ,
        (logDeriv Complex.Gammaℝ ((2:ℂ)+(t:ℂ)*Complex.I) * Φ ((2:ℂ)+(t:ℂ)*Complex.I)
          + logDeriv riemannZeta ((2:ℂ)+(t:ℂ)*Complex.I) * Φ ((2:ℂ)+(t:ℂ)*Complex.I)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hFdef]
      exact hpt2 t
    rw [hcongr, MeasureTheory.integral_add hG2int hZc2int]
  have hA1split : A1 = G1 + Zc1 := by
    rw [hA1def, hG1def, hZc1def]
    have hcongr : (∫ t : ℝ, F ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I)) = ∫ t : ℝ,
        (logDeriv Complex.Gammaℝ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) * Φ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I)
          + logDeriv riemannZeta ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I) * Φ ((((-1/2 : ℝ)))+(t:ℂ)*Complex.I)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hFdef]
      exact hptl t
    rw [hcongr, MeasureTheory.integral_add hG1int hZc1int]
  have hkey2 : (1/(2*(Real.pi:ℂ))) * (Zc2 - Zc1) = Z + Φ 0 := by
    have hAsplit : A2 - A1 = (G2 - G1) + (Zc2 - Zc1) := by rw [hA2split, hA1split]; ring
    calc (1/(2*(Real.pi:ℂ))) * (Zc2 - Zc1)
        = (1/(2*(Real.pi:ℂ))) * ((A2 - A1) - (G2 - G1)) := by rw [hAsplit]; ring
      _ = Z - (- Φ 0) := by rw [mul_sub, hkey, hgamma]
      _ = Z + Φ 0 := by ring
  -- ### Perron and the final inequality
  have hperΦ : ((Real.log (q:ℝ) : ℝ) : ℂ)⁻¹ *
      (∑ n ∈ Finset.Icc 1 X, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
        ((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
          (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ))
      = -(1/(2*(Real.pi:ℂ))) * Zc2 := by
    rw [← hΦdef] at hper
    rw [hZc2def]
    rw [hper]
    rw [show (∫ t : ℝ, (-logDeriv riemannZeta ((2:ℂ)+(t:ℂ)*Complex.I)) * Φ ((2:ℂ)+(t:ℂ)*Complex.I))
        = - ∫ t : ℝ, logDeriv riemannZeta ((2:ℂ)+(t:ℂ)*Complex.I) * Φ ((2:ℂ)+(t:ℂ)*Complex.I) from by
      rw [← MeasureTheory.integral_neg]
      apply integral_congr_ae
      filter_upwards with t; ring]
    ring
  have hmain_eq : ((Real.log (q:ℝ) : ℝ) : ℂ)⁻¹ *
      (∑ n ∈ Finset.Icc 1 X, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
        ((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
          (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)) + Z
      = - Φ 0 - (1/(2*(Real.pi:ℂ))) * Zc1 := by
    have hZ' : Z = (1/(2*(Real.pi:ℂ))) * (Zc2 - Zc1) - Φ 0 :=
      eq_sub_iff_add_eq.mpr hkey2.symm
    rw [hperΦ, hZ']; ring
  rw [hmain_eq]
  calc ‖- Φ 0 - (1/(2*(Real.pi:ℂ))) * Zc1‖
      ≤ ‖Φ 0‖ + ‖(1/(2*(Real.pi:ℂ))) * Zc1‖ := by
        simpa using norm_sub_le (-Φ 0) ((1/(2*(Real.pi:ℂ))) * Zc1)
    _ ≤ (q:ℝ)^(-(49:ℝ)/10) + Cle * ((Real.log (q:ℝ))⁻¹ * ((q:ℝ)^(-(147:ℝ)/20)) * (1 + Real.log (q:ℝ))) := by
        refine add_le_add hΦ0 ?_
        have h := hCle q hq
        have h' : ‖(1/(2*(Real.pi:ℂ))) * Zc1‖ ≤
            Cle * ((Real.log (q:ℝ))⁻¹ * ((q:ℝ)^(-(147:ℝ)/20)) * (1 + Real.log (q:ℝ))) := by
          rw [hZc1def]
          simp only [half_form_bridge, ← hΦdef]
          exact h
        exact h'
    _ ≤ (1 + Cle) * ((q:ℝ)^(-(49:ℝ)/10) + (Real.log (q:ℝ))⁻¹ * ((q:ℝ)^(-(147:ℝ)/20)) * (1 + Real.log (q:ℝ))) := by
        have h1 : 0 ≤ (q:ℝ)^(-(49:ℝ)/10) := Real.rpow_nonneg (by positivity) _
        have h2 : 0 ≤ (Real.log (q:ℝ))⁻¹ * ((q:ℝ)^(-(147:ℝ)/20)) * (1 + Real.log (q:ℝ)) := by
          have h5 : 0 < 1 + Real.log (q:ℝ) := by linarith
          positivity
        nlinarith [hClepos, h1, h2]

end

end Work.LinnikAreas
