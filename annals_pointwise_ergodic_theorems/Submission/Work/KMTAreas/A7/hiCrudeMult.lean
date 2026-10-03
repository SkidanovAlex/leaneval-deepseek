/-
# KMT `crude-mult`(ii) on `ℝ²`

This is the `ℝ`-case of Lemma `crude-mult`(ii) of

* B. Krause, B. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
  averages*, Annals of Math. 195 (3) 2022,

in the shape needed by `hiCrudeMult`: for a compactly supported `C⁴` symbol `ψ : ℝ² → ℂ` whose
mixed partials (up to order `2` in each variable) satisfy

  `∫_{ℝ²} ‖∂₁^{i₁}∂₂^{i₂} ψ‖ ≤ C r₁^{1-i₁} r₂^{1-i₂}`   (`0 ≤ i₁,i₂ ≤ 2`, `0 < r₁,r₂ ≤ 1`)

the Fourier coefficients `K(p) = ∫_{ℝ²} ψ(z) e(-p·z) dz` are `ℓ¹`-summable with

  `∑'_{p ∈ ℤ²} ‖K(p)‖ ≤ 100 C`.

The proof is the integration-by-parts argument of the paper, transferred from the periodic case
(`Work.KMTPlan.A6.SymToolbox_tsum_coeff2_le`, which proves the `𝔾 = ℤ` case of `crude-mult`(ii)):
each `K(p)` is `((2πip₁)^{i₁}(2πip₂)^{i₂})⁻¹` times the Fourier coefficient of `∂₁^{i₁}∂₂^{i₂}ψ`, and
one takes, for each `p`, the better of the cases `(0,0)`, `(2,0)`, `(0,2)`, `(2,2)` according to the
sizes of `r₁|p₁|` and `r₂|p₂|`.  The `ℓ¹` mass of the resulting weight is then bounded as in
`Work.KMTPlan.A6.wt_tsum_le` (mass `≤ 4` per variable).

The analytic work is the integration by parts on the (non-compact) group `ℝ²`: iterating the
one-dimensional identity `∫ F' e^{b·} = -b ∫ F e^{b·}` (valid for `F` of compact support) over the
iterated integral, with Fubini to exchange the two orders of integration.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxHiDefs
import Submission.Work.KMTPlan.A6.SymToolbox_tsum_coeff2_le

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## The Fourier coefficient of a symbol on `ℝ²` -/

/-- The `(p₁,p₂)`-th Fourier coefficient of a symbol `σ` on `ℝ²`. -/
noncomputable def kf (σ : ℝ → ℝ → ℂ) (p₁ p₂ : ℤ) : ℂ :=
  ∫ z : ℝ × ℝ, σ z.1 z.2 * ee (-((p₁ : ℝ) * z.1 + (p₂ : ℝ) * z.2))

/-- `kf` written as the iterated integral with the `y`-integration outer. -/
noncomputable def kfY (σ : ℝ → ℝ → ℂ) (p₁ p₂ : ℤ) : ℂ :=
  ∫ y : ℝ, ∫ x : ℝ, σ x y * ee (-((p₁ : ℝ) * x)) * ee (-((p₂ : ℝ) * y))

/-- `kf` written as the iterated integral with the `x`-integration outer. -/
noncomputable def kfX (σ : ℝ → ℝ → ℂ) (p₁ p₂ : ℤ) : ℂ :=
  ∫ x : ℝ, ∫ y : ℝ, σ x y * ee (-((p₁ : ℝ) * x)) * ee (-((p₂ : ℝ) * y))

/-! ## The character `ee` -/

lemma ee_eq_exp (x : ℝ) : ee x = Complex.exp (((2 * Real.pi * x : ℝ)) * Complex.I) := by
  rw [ee]; congr 1; push_cast; ring

lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  rw [ee_eq_exp, Complex.norm_exp_ofReal_mul_I]

lemma ee_neg_add (a b : ℝ) : ee (-(a + b)) = ee (-a) * ee (-b) := by
  rw [ee_eq_exp, ee_eq_exp, ee_eq_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma continuous_ee : Continuous ee := by
  rw [show ee = fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ)) * Complex.I) from
    funext ee_eq_exp]
  fun_prop

/-- The character `ee (-(a x))` is the exponential used in the one-dimensional
integration-by-parts identity. -/
lemma ee_neg_mul_eq (a x : ℝ) :
    ee (-(a * x)) = Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * (a : ℂ))) * (x : ℂ)) := by
  rw [ee_eq_exp]
  congr 1
  push_cast
  ring

/-- Multiplying an integrable function on `ℝ²` by a character preserves integrability. -/
lemma integrable_mul_ee_prod (g : ℝ × ℝ → ℂ) (h : Integrable g volume) (p₁ p₂ : ℤ) :
    Integrable (fun z : ℝ × ℝ => g z * ee (-((p₁ : ℝ) * z.1 + (p₂ : ℝ) * z.2))) volume := by
  refine h.mul_bdd (c := 1)
    ((continuous_ee.comp (by fun_prop)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [norm_ee]

/-! ## One-dimensional integration by parts -/

/-- **Integration by parts against an exponential** on all of `ℝ`: for `F` of compact support,
`∫ F' e^{b y} dy = -b ∫ F e^{b y} dy` (the boundary terms vanish). -/
lemma intIBP_step (F : ℝ → ℂ) (hd : Differentiable ℝ F) (hcont : Continuous (deriv F))
    (hc : HasCompactSupport F) (b : ℂ) :
    ∫ y : ℝ, deriv F y * Complex.exp (b * (y : ℂ))
      = -b * ∫ y : ℝ, F y * Complex.exp (b * (y : ℂ)) := by
  have hts : tsupport (fun y : ℝ => Complex.exp (b * (y : ℂ))) = Set.univ := by
    rw [tsupport, Function.support]
    have : {x : ℝ | Complex.exp (b * (x : ℂ)) ≠ 0} = Set.univ := by
      ext y; simp [Complex.exp_ne_zero]
    rw [this, closure_univ]
  have hderivF : ∀ y : ℝ, HasDerivAt F (deriv F y) y := fun y => hd.differentiableAt.hasDerivAt
  have hderivv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (b * (y : ℂ)))
      (b * Complex.exp (b * (y : ℂ))) y := by
    intro y
    have hlin : HasDerivAt (fun y : ℝ => b * (y : ℂ)) b y := by
      simpa using ((hasDerivAt_id y).ofReal_comp).const_mul b
    simpa [Function.comp_def, mul_comm] using
      (Complex.hasDerivAt_exp (b * (y : ℂ))).comp y hlin
  have hcontb : Continuous fun y : ℝ => b * Complex.exp (b * (y : ℂ)) := by fun_prop
  have h1 : Integrable (F * fun y : ℝ => b * Complex.exp (b * (y : ℂ))) :=
    (hd.continuous.mul hcontb).integrable_of_hasCompactSupport hc.mul_right
  have h2 : Integrable ((deriv F) * fun y : ℝ => Complex.exp (b * (y : ℂ))) :=
    (hcont.mul (by fun_prop)).integrable_of_hasCompactSupport hc.deriv.mul_right
  have h3 : Integrable (F * fun y : ℝ => Complex.exp (b * (y : ℂ))) :=
    (hd.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := F) (v := fun y : ℝ => Complex.exp (b * (y : ℂ))) (u' := deriv F)
      (v' := fun y : ℝ => b * Complex.exp (b * (y : ℂ)))
      (fun y _ => hderivF y) (fun y _ => hderivv y) h1 h2 h3
  have hL : (∫ y : ℝ, F y * (b * Complex.exp (b * (y : ℂ))))
      = b * ∫ y : ℝ, F y * Complex.exp (b * (y : ℂ)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  rw [hL] at hibp
  have key : ∫ y : ℝ, deriv F y * Complex.exp (b * (y : ℂ))
      = -(b * ∫ y : ℝ, F y * Complex.exp (b * (y : ℂ))) := by
    rw [hibp]; ring
  rw [key]; ring

/-- **Iterated integration by parts against an exponential**: for `F` of compact support and `C^j`,
`∫ F^{(j)} e^{b y} dy = (-b)^j ∫ F e^{b y} dy`. -/
theorem intIterIBP (F : ℝ → ℂ) (j : ℕ) (hcd : ContDiff ℝ j F) (hc : HasCompactSupport F)
    (b : ℂ) :
    ∫ y : ℝ, iteratedDeriv j F y * Complex.exp (b * (y : ℂ))
      = (-b) ^ j * ∫ y : ℝ, F y * Complex.exp (b * (y : ℂ)) := by
  have hc' : ∀ k : ℕ, HasCompactSupport (iteratedDeriv k F) := by
    intro k
    induction k with
    | zero => simpa using hc
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hder := contDiff_nat_iff_iteratedDeriv.mp hcd
  have main : ∀ k ≤ j, ∫ y : ℝ, iteratedDeriv k F y * Complex.exp (b * (y : ℂ))
      = (-b) ^ k * ∫ y : ℝ, F y * Complex.exp (b * (y : ℂ)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ n ih =>
        intro hn
        have hn' : n ≤ j := le_trans (Nat.le_succ n) hn
        rw [iteratedDeriv_succ]
        have hdiff : Differentiable ℝ (iteratedDeriv n F) := hder.2 n (Nat.lt_of_succ_le hn)
        have hcont : Continuous (deriv (iteratedDeriv n F)) := by
          rw [← iteratedDeriv_succ]; exact hder.1 (n + 1) hn
        rw [intIBP_step (iteratedDeriv n F) hdiff hcont (hc' n) b, ih hn']
        ring
  exact main j le_rfl

/-- **Iterated integration by parts**, in the form used below. -/
theorem intIterIBP_ee (F : ℝ → ℂ) (j : ℕ) (hcd : ContDiff ℝ j F) (hc : HasCompactSupport F)
    (a : ℝ) :
    ∫ y : ℝ, iteratedDeriv j F y * ee (-(a * y))
      = (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) ^ j * ∫ y : ℝ, F y * ee (-(a * y)) := by
  have h := intIterIBP F j hcd hc (-(2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)))
  have h1 : ∀ y : ℝ, Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * (a : ℂ))) * (y : ℂ))
      = ee (-(a * y)) := fun y => (ee_neg_mul_eq a y).symm
  simp only [h1] at h
  have h2 : (-(-(2 * (Real.pi : ℂ) * Complex.I * (a : ℂ))))
      = 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) := by ring
  rw [h2] at h
  exact h

/-! ## Compact support of the fibres of an iterated derivative -/

/-- If `G : ℝ² → ℂ` has compact support then so does each fibre
`x ↦ ∂₂^j G(x,y)`: the fibre vanishes identically once `x` leaves the projection of the
(topological) support of `G`. -/
theorem compSupp_iteratedDeriv_fiber (G : ℝ × ℝ → ℂ) (hc : HasCompactSupport G) (j : ℕ)
    (y : ℝ) :
    HasCompactSupport (fun x : ℝ => iteratedDeriv j (fun t : ℝ => G (x, t)) y) := by
  refine HasCompactSupport.intro' (K := Prod.fst '' tsupport G) (hc.image continuous_fst)
    (hc.image continuous_fst).isClosed ?_
  intro x hx
  have hzero : (fun t : ℝ => G (x, t)) = fun _ => (0 : ℂ) := by
    funext t
    by_contra h
    exact hx ⟨(x, t), subset_tsupport G h, rfl⟩
  rw [hzero, iteratedDeriv_const]
  split_ifs <;> rfl

/-- If `G : ℝ² → ℂ` has compact support then so does each fibre `y ↦ G(x,y)`. -/
lemma compSupp_fiber_snd (G : ℝ × ℝ → ℂ) (hc : HasCompactSupport G) (x : ℝ) :
    HasCompactSupport (fun y : ℝ => G (x, y)) := by
  refine HasCompactSupport.intro' (K := Prod.snd '' tsupport G) (hc.image continuous_snd)
    (hc.image continuous_snd).isClosed ?_
  intro y hy
  by_contra h
  exact hy ⟨(x, y), subset_tsupport G h, rfl⟩

/-! ## The topological support of the partial derivatives -/

/-- A function which vanishes in a neighbourhood of a point has all its iterated derivatives
vanishing there. -/
lemma iteratedDeriv_eq_zero_of_eventuallyEq_zero (f : ℝ → ℂ) {y : ℝ}
    (h : f =ᶠ[nhds y] (0 : ℝ → ℂ)) (j : ℕ) :
    iteratedDeriv j f y = 0 := by
  have key : ∀ j : ℕ, iteratedDeriv j f =ᶠ[nhds y] (0 : ℝ → ℂ) := by
    intro j
    induction j with
    | zero => simpa using h
    | succ k ih => rw [iteratedDeriv_succ]; simpa [deriv_zero] using ih.deriv
  exact (key j).eq_of_nhds

/-- The mixed partials of a symbol with compact support have compact support: they vanish
identically off the topological support of the symbol. -/
lemma hasCompactSupport_dp (σ : ℝ → ℝ → ℂ)
    (hc : HasCompactSupport (fun p : ℝ × ℝ => σ p.1 p.2)) (i j : ℕ) :
    HasCompactSupport (fun p : ℝ × ℝ => Work.KMTPlan.A6.dp i j σ p.1 p.2) := by
  refine HasCompactSupport.intro' (K := tsupport (fun p : ℝ × ℝ => σ p.1 p.2)) hc
    (isClosed_tsupport _) ?_
  intro p hp
  obtain ⟨ε, hε, hεsub⟩ :
      ∃ ε > 0, Metric.ball p ε ⊆ (tsupport (fun q : ℝ × ℝ => σ q.1 q.2))ᶜ :=
    Metric.mem_nhds_iff.mp ((isClosed_tsupport fun q : ℝ × ℝ => σ q.1 q.2).isOpen_compl.mem_nhds hp)
  have hzero : ∀ x : ℝ, dist x p.1 < ε → ∀ t : ℝ, dist t p.2 < ε → σ x t = 0 := by
    intro x hx t ht
    have hmem : (x, t) ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hx ht
    have hcon := hεsub hmem
    have hns : ¬ (fun q : ℝ × ℝ => σ q.1 q.2) (x, t) ≠ 0 :=
      fun h => hcon (subset_tsupport _ h)
    simpa using hns
  have h1 : (fun x : ℝ => Work.KMTPlan.A6.dp2 j σ x p.2) =ᶠ[nhds p.1] (0 : ℝ → ℂ) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds p.1 hε) ?_
    intro x hx
    show Work.KMTPlan.A6.dp2 j σ x p.2 = 0
    refine iteratedDeriv_eq_zero_of_eventuallyEq_zero (fun t : ℝ => σ x t) ?_ j
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds p.2 hε) ?_
    intro t ht
    exact hzero x hx t ht
  show Work.KMTPlan.A6.dp1 i (Work.KMTPlan.A6.dp2 j σ) p.1 p.2 = 0
  exact iteratedDeriv_eq_zero_of_eventuallyEq_zero
    (fun x : ℝ => Work.KMTPlan.A6.dp2 j σ x p.2) h1 i

/-- The mixed partials of a `C^{i+j}` compactly supported symbol are integrable. -/
lemma integrable_dp (σ : ℝ → ℝ → ℂ) (i j : ℕ)
    (hsm : ContDiff ℝ (i + j) (fun p : ℝ × ℝ => σ p.1 p.2))
    (hc : HasCompactSupport (fun p : ℝ × ℝ => σ p.1 p.2)) :
    Integrable (fun z : ℝ × ℝ => Work.KMTPlan.A6.dp i j σ z.1 z.2) volume := by
  have hsm' : ContDiff ℝ (((i + j : ℕ)) : WithTop ℕ∞) (fun p : ℝ × ℝ => σ p.1 p.2) := by
    rw [Nat.cast_add]; exact hsm
  have hJ : ContDiff ℝ (i : WithTop ℕ∞) (fun p : ℝ × ℝ => Work.KMTPlan.A6.dp2 j σ p.1 p.2) :=
    Work.KMTPlan.A6.cdp_contDiff_dp2_iter σ i j hsm'
  have hD : ContDiff ℝ (0 : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.KMTPlan.A6.dp i j σ p.1 p.2) :=
    Work.KMTPlan.A6.cdp_contDiff_dp1_iter (Work.KMTPlan.A6.dp2 j σ) 0 i (by simpa using hJ)
  exact (hD.continuous).integrable_of_hasCompactSupport (hasCompactSupport_dp σ hc i j)

/-! ## `kf` as an iterated integral (Fubini) -/

/-- Fubini: `kf` is the iterated integral with the `y`-integration outer. -/
lemma kf_eq_kfY (σ : ℝ → ℝ → ℂ) (p₁ p₂ : ℤ)
    (hInt : Integrable (fun z : ℝ × ℝ => σ z.1 z.2) volume) :
    kf σ p₁ p₂ = kfY σ p₁ p₂ := by
  have hI := integrable_mul_ee_prod (fun z : ℝ × ℝ => σ z.1 z.2) hInt p₁ p₂
  rw [kf, MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.integral_prod_symm _ hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [ee_neg_add]
  ring

/-- Fubini: `kf` is the iterated integral with the `x`-integration outer. -/
lemma kf_eq_kfX (σ : ℝ → ℝ → ℂ) (p₁ p₂ : ℤ)
    (hInt : Integrable (fun z : ℝ × ℝ => σ z.1 z.2) volume) :
    kf σ p₁ p₂ = kfX σ p₁ p₂ := by
  have hI := integrable_mul_ee_prod (fun z : ℝ × ℝ => σ z.1 z.2) hInt p₁ p₂
  rw [kf, MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.integral_prod _ hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only []
  rw [ee_neg_add]
  ring

/-- The two iterated orders agree. -/
lemma kfY_eq_kfX (σ : ℝ → ℝ → ℂ) (p₁ p₂ : ℤ)
    (hInt : Integrable (fun z : ℝ × ℝ => σ z.1 z.2) volume) :
    kfY σ p₁ p₂ = kfX σ p₁ p₂ :=
  (kf_eq_kfY σ p₁ p₂ hInt).symm.trans (kf_eq_kfX σ p₁ p₂ hInt)

/-! ## The two single-variable steps -/

/-- **Integration by parts in the first variable** of the `y`-outer iterated integral: the
`x`-integration is the inner one, so this is pointwise in `y` and needs only the fibre hypotheses. -/
theorem kfY_dp1 (h : ℝ → ℝ → ℂ) (j : ℕ) (p₁ p₂ : ℤ)
    (hfib : ∀ y : ℝ, ContDiff ℝ j (fun x : ℝ => h x y))
    (hc : ∀ y : ℝ, HasCompactSupport (fun x : ℝ => h x y)) :
    kfY (Work.KMTPlan.A6.dp1 j h) p₁ p₂
      = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ j * kfY h p₁ p₂ := by
  have hinner : ∀ y : ℝ,
      (∫ x : ℝ, Work.KMTPlan.A6.dp1 j h x y * ee (-((p₁ : ℝ) * x)) * ee (-((p₂ : ℝ) * y)))
        = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ j *
            (∫ x : ℝ, h x y * ee (-((p₁ : ℝ) * x)) * ee (-((p₂ : ℝ) * y))) := by
    intro y
    have e1 : (∫ x : ℝ,
          Work.KMTPlan.A6.dp1 j h x y * ee (-((p₁ : ℝ) * x)) * ee (-((p₂ : ℝ) * y)))
        = (∫ x : ℝ, Work.KMTPlan.A6.dp1 j h x y * ee (-((p₁ : ℝ) * x)))
            * ee (-((p₂ : ℝ) * y)) := by
      rw [← integral_mul_const]
    have e2 : (∫ x : ℝ, h x y * ee (-((p₁ : ℝ) * x)) * ee (-((p₂ : ℝ) * y)))
        = (∫ x : ℝ, h x y * ee (-((p₁ : ℝ) * x))) * ee (-((p₂ : ℝ) * y)) := by
      rw [← integral_mul_const]
    have e3 : (∫ x : ℝ, Work.KMTPlan.A6.dp1 j h x y * ee (-((p₁ : ℝ) * x)))
        = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ j *
            (∫ x : ℝ, h x y * ee (-((p₁ : ℝ) * x))) :=
      intIterIBP_ee (fun x : ℝ => h x y) j (hfib y) (hc y) (p₁ : ℝ)
    rw [e1, e2, e3]; ring
  simp only [kfY]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun y => hinner y)]
  rw [integral_const_mul]

/-- **Integration by parts in the second variable** of the `x`-outer iterated integral. -/
theorem kfX_dp2 (g : ℝ → ℝ → ℂ) (j : ℕ) (p₁ p₂ : ℤ)
    (hfib : ∀ x : ℝ, ContDiff ℝ j (fun y : ℝ => g x y))
    (hc : ∀ x : ℝ, HasCompactSupport (fun y : ℝ => g x y)) :
    kfX (Work.KMTPlan.A6.dp2 j g) p₁ p₂
      = (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ j * kfX g p₁ p₂ := by
  have hinner : ∀ x : ℝ,
      (∫ y : ℝ, Work.KMTPlan.A6.dp2 j g x y * ee (-((p₁ : ℝ) * x)) * ee (-((p₂ : ℝ) * y)))
        = (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ j *
            (∫ y : ℝ, g x y * ee (-((p₁ : ℝ) * x)) * ee (-((p₂ : ℝ) * y))) := by
    intro x
    have e1 : (∫ y : ℝ,
          Work.KMTPlan.A6.dp2 j g x y * ee (-((p₁ : ℝ) * x)) * ee (-((p₂ : ℝ) * y)))
        = ee (-((p₁ : ℝ) * x))
            * (∫ y : ℝ, Work.KMTPlan.A6.dp2 j g x y * ee (-((p₂ : ℝ) * y))) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have e2 : (∫ y : ℝ, g x y * ee (-((p₁ : ℝ) * x)) * ee (-((p₂ : ℝ) * y)))
        = ee (-((p₁ : ℝ) * x)) * (∫ y : ℝ, g x y * ee (-((p₂ : ℝ) * y))) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have e3 : (∫ y : ℝ, Work.KMTPlan.A6.dp2 j g x y * ee (-((p₂ : ℝ) * y)))
        = (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ j *
            (∫ y : ℝ, g x y * ee (-((p₂ : ℝ) * y))) :=
      intIterIBP_ee (fun y : ℝ => g x y) j (hfib x) (hc x) (p₂ : ℝ)
    rw [e1, e2, e3]; ring
  simp only [kfX]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x => hinner x)]
  rw [integral_const_mul]

/-! ## The Fourier coefficient of a mixed partial -/

/-- The integration-by-parts identity for the mixed partials: `∂₁^{j₁}∂₂^{j₂}ψ` has Fourier
coefficient `(2πip₁)^{j₁}(2πip₂)^{j₂}` times that of `ψ`. -/
theorem kf_dp (σ : ℝ → ℝ → ℂ) (j₁ j₂ : ℕ) (p₁ p₂ : ℤ)
    (hInt00 : Integrable (fun z : ℝ × ℝ => σ z.1 z.2) volume)
    (hInt0j : Integrable (fun z : ℝ × ℝ => Work.KMTPlan.A6.dp2 j₂ σ z.1 z.2) volume)
    (hIntj : Integrable (fun z : ℝ × ℝ => Work.KMTPlan.A6.dp j₁ j₂ σ z.1 z.2) volume)
    (hfib2 : ∀ x : ℝ, ContDiff ℝ j₂ (fun y : ℝ => σ x y))
    (hc2 : ∀ x : ℝ, HasCompactSupport (fun y : ℝ => σ x y))
    (hfib1 : ∀ y : ℝ, ContDiff ℝ j₁ (fun x : ℝ => Work.KMTPlan.A6.dp2 j₂ σ x y))
    (hc1 : ∀ y : ℝ, HasCompactSupport (fun x : ℝ => Work.KMTPlan.A6.dp2 j₂ σ x y)) :
    kf (Work.KMTPlan.A6.dp j₁ j₂ σ) p₁ p₂
      = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ j₁
        * (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ j₂ * kf σ p₁ p₂ := by
  rw [kf_eq_kfY (Work.KMTPlan.A6.dp j₁ j₂ σ) p₁ p₂ hIntj]
  rw [show Work.KMTPlan.A6.dp j₁ j₂ σ
        = Work.KMTPlan.A6.dp1 j₁ (Work.KMTPlan.A6.dp2 j₂ σ) from rfl]
  rw [kfY_dp1 _ _ _ _ hfib1 hc1, kfY_eq_kfX _ _ _ hInt0j,
    kfX_dp2 _ _ _ _ hfib2 hc2, ← kfY_eq_kfX _ _ _ hInt00, ← kf_eq_kfY _ _ _ hInt00]
  ring

/-! ## The bridge to `partXY` -/

/-! ## The pointwise bound for the Fourier coefficients -/

/-- **The four cases of the integration-by-parts bound.**  For `(j₁,j₂)` one of `(0,0)`, `(2,0)`,
`(0,2)`, `(2,2)`, the Fourier coefficient `kf σ p` is bounded by `C` times the corresponding
product of frequency weights. -/
lemma kf_case (σ : ℝ → ℝ → ℂ) (C r₁ r₂ : ℝ)
    (hid : ∀ i₁ i₂ : ℕ, i₁ ≤ 2 → i₂ ≤ 2 → ∀ q₁ q₂ : ℤ,
      kf (Work.KMTPlan.A6.dp i₁ i₂ σ) q₁ q₂
        = (2 * (Real.pi : ℂ) * Complex.I * (q₁ : ℂ)) ^ i₁
          * (2 * (Real.pi : ℂ) * Complex.I * (q₂ : ℂ)) ^ i₂ * kf σ q₁ q₂)
    (hbd : ∀ i₁ i₂ : ℕ, i₁ ≤ 2 → i₂ ≤ 2 →
      ∫ z : ℝ × ℝ, ‖Work.KMTPlan.A6.dp i₁ i₂ σ z.1 z.2‖ ≤
        C * r₁ ^ ((1 : ℝ) - (i₁ : ℝ)) * r₂ ^ ((1 : ℝ) - (i₂ : ℝ)))
    {j₁ j₂ : ℕ} (hj₁ : j₁ = 0 ∨ j₁ = 2) (hj₂ : j₂ = 0 ∨ j₂ = 2) (p₁ p₂ : ℤ)
    (hp₁ : j₁ = 0 ∨ p₁ ≠ 0) (hp₂ : j₂ = 0 ∨ p₂ ≠ 0) :
    ‖kf σ p₁ p₂‖ ≤ C * Work.KMTPlan.A6.rho r₁ j₁ p₁ * Work.KMTPlan.A6.rho r₂ j₂ p₂ := by
  have hj₁2 : j₁ ≤ 2 := by rcases hj₁ with h | h <;> omega
  have hj₂2 : j₂ ≤ 2 := by rcases hj₂ with h | h <;> omega
  have hd := hbd j₁ j₂ hj₁2 hj₂2
  have hid' := hid j₁ j₂ hj₁2 hj₂2 p₁ p₂
  have hnorm : ‖kf (Work.KMTPlan.A6.dp j₁ j₂ σ) p₁ p₂‖
      = (2 * Real.pi * |(p₁ : ℝ)|) ^ j₁ * (2 * Real.pi * |(p₂ : ℝ)|) ^ j₂
        * ‖kf σ p₁ p₂‖ := by
    rw [hid', norm_mul, norm_mul, Work.KMTPlan.A6.norm_two_pi_I_pow,
      Work.KMTPlan.A6.norm_two_pi_I_pow]
    try ring
  have hkey : (2 * Real.pi * |(p₁ : ℝ)|) ^ j₁ * (2 * Real.pi * |(p₂ : ℝ)|) ^ j₂
        * ‖kf σ p₁ p₂‖
      ≤ C * r₁ ^ ((1 : ℝ) - (j₁ : ℝ)) * r₂ ^ ((1 : ℝ) - (j₂ : ℝ)) := by
    rw [← hnorm]
    refine (norm_integral_le_integral_norm
      (fun z : ℝ × ℝ => Work.KMTPlan.A6.dp j₁ j₂ σ z.1 z.2
        * ee (-((p₁ : ℝ) * z.1 + (p₂ : ℝ) * z.2)))).trans ?_
    refine le_trans (le_of_eq ?_) hd
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [norm_mul, norm_ee, mul_one]
  have e1 : r₁ ^ ((1 : ℝ) - ((2 : ℕ) : ℝ)) = r₁⁻¹ := by
    rw [show (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have e1' : r₁ ^ ((1 : ℝ) - ((0 : ℕ) : ℝ)) = r₁ := by
    rw [show (1 : ℝ) - ((0 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have e2 : r₂ ^ ((1 : ℝ) - ((2 : ℕ) : ℝ)) = r₂⁻¹ := by
    rw [show (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have e2' : r₂ ^ ((1 : ℝ) - ((0 : ℕ) : ℝ)) = r₂ := by
    rw [show (1 : ℝ) - ((0 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  rcases hj₁ with rfl | rfl <;> rcases hj₂ with rfl | rfl
  · -- (0,0)
    rw [Work.KMTPlan.A6.rho_zero, Work.KMTPlan.A6.rho_zero]
    simpa only [pow_zero, mul_one, one_mul, e1', e2'] using hkey
  · -- (0,2)
    have hp₂' : p₂ ≠ 0 := hp₂.resolve_left (by norm_num : ¬ ((2 : ℕ) = 0))
    rw [Work.KMTPlan.A6.rho_zero, Work.KMTPlan.A6.rho_two]
    rw [e1', e2] at hkey
    simp only [pow_zero, mul_one, one_mul] at hkey
    have hpos : 0 < (2 * Real.pi * |(p₂ : ℝ)|) ^ 2 := by
      have h0 : 0 < 2 * Real.pi * |(p₂ : ℝ)| :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (by exact_mod_cast hp₂'))
      exact pow_pos h0 2
    have hdiv : ‖kf σ p₁ p₂‖ ≤ (C * r₁ * r₂⁻¹) / (2 * Real.pi * |(p₂ : ℝ)|) ^ 2 :=
      (le_div_iff₀ hpos).mpr (by rw [mul_comm]; exact hkey)
    exact hdiv.trans (le_of_eq (by ring))
  · -- (2,0)
    have hp₁' : p₁ ≠ 0 := hp₁.resolve_left (by norm_num : ¬ ((2 : ℕ) = 0))
    rw [Work.KMTPlan.A6.rho_two, Work.KMTPlan.A6.rho_zero]
    rw [e1, e2'] at hkey
    simp only [pow_zero, mul_one, one_mul] at hkey
    have hpos : 0 < (2 * Real.pi * |(p₁ : ℝ)|) ^ 2 := by
      have h0 : 0 < 2 * Real.pi * |(p₁ : ℝ)| :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (by exact_mod_cast hp₁'))
      exact pow_pos h0 2
    have hdiv : ‖kf σ p₁ p₂‖ ≤ (C * r₁⁻¹ * r₂) / (2 * Real.pi * |(p₁ : ℝ)|) ^ 2 :=
      (le_div_iff₀ hpos).mpr (by rw [mul_comm]; exact hkey)
    exact hdiv.trans (le_of_eq (by ring))
  · -- (2,2)
    have hp₁' : p₁ ≠ 0 := hp₁.resolve_left (by norm_num : ¬ ((2 : ℕ) = 0))
    have hp₂' : p₂ ≠ 0 := hp₂.resolve_left (by norm_num : ¬ ((2 : ℕ) = 0))
    rw [Work.KMTPlan.A6.rho_two, Work.KMTPlan.A6.rho_two]
    rw [e1, e2] at hkey
    have hpos : 0 < (2 * Real.pi * |(p₁ : ℝ)|) ^ 2 * (2 * Real.pi * |(p₂ : ℝ)|) ^ 2 := by
      have h0 : 0 < 2 * Real.pi * |(p₁ : ℝ)| :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (by exact_mod_cast hp₁'))
      have h1 : 0 < 2 * Real.pi * |(p₂ : ℝ)| :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (by exact_mod_cast hp₂'))
      exact mul_pos (pow_pos h0 2) (pow_pos h1 2)
    have hkey' : ‖kf σ p₁ p₂‖
        * ((2 * Real.pi * |(p₁ : ℝ)|) ^ 2 * (2 * Real.pi * |(p₂ : ℝ)|) ^ 2)
        ≤ C * r₁⁻¹ * r₂⁻¹ := by
      rw [mul_comm]; exact hkey
    have hdiv : ‖kf σ p₁ p₂‖
        ≤ (C * r₁⁻¹ * r₂⁻¹)
          / ((2 * Real.pi * |(p₁ : ℝ)|) ^ 2 * (2 * Real.pi * |(p₂ : ℝ)|) ^ 2) :=
      (le_div_iff₀ hpos).mpr hkey'
    exact hdiv.trans (le_of_eq (by ring))

/-- **Pointwise bound for the Fourier coefficients** by `C` times the product of the two
frequency weights `wt`. -/
lemma kf_le (σ : ℝ → ℝ → ℂ) (C r₁ r₂ : ℝ)
    (hid : ∀ i₁ i₂ : ℕ, i₁ ≤ 2 → i₂ ≤ 2 → ∀ q₁ q₂ : ℤ,
      kf (Work.KMTPlan.A6.dp i₁ i₂ σ) q₁ q₂
        = (2 * (Real.pi : ℂ) * Complex.I * (q₁ : ℂ)) ^ i₁
          * (2 * (Real.pi : ℂ) * Complex.I * (q₂ : ℂ)) ^ i₂ * kf σ q₁ q₂)
    (hbd : ∀ i₁ i₂ : ℕ, i₁ ≤ 2 → i₂ ≤ 2 →
      ∫ z : ℝ × ℝ, ‖Work.KMTPlan.A6.dp i₁ i₂ σ z.1 z.2‖ ≤
        C * r₁ ^ ((1 : ℝ) - (i₁ : ℝ)) * r₂ ^ ((1 : ℝ) - (i₂ : ℝ)))
    (p₁ p₂ : ℤ) :
    ‖kf σ p₁ p₂‖ ≤ C * (Work.KMTPlan.A6.wt r₁ p₁ * Work.KMTPlan.A6.wt r₂ p₂) := by
  have h00 := kf_case σ C r₁ r₂ hid hbd (j₁ := 0) (j₂ := 0)
    (Or.inl rfl) (Or.inl rfl) p₁ p₂ (Or.inl rfl) (Or.inl rfl)
  by_cases hp₁ : p₁ = 0
  · by_cases hp₂ : p₂ = 0
    · subst hp₁; subst hp₂
      simpa only [Work.KMTPlan.A6.wt_zero, Work.KMTPlan.A6.rho_zero, mul_assoc] using h00
    · subst hp₁
      have h02 := kf_case σ C r₁ r₂ hid hbd (j₁ := 0) (j₂ := 2)
        (Or.inl rfl) (Or.inr rfl) 0 p₂ (Or.inl rfl) (Or.inr hp₂)
      have h := Work.KMTPlan.A6.le_mul_min h00 h02
      simpa only [Work.KMTPlan.A6.wt_zero, Work.KMTPlan.A6.wt_eq_min hp₂,
        Work.KMTPlan.A6.rho_zero, mul_assoc] using h
  · by_cases hp₂ : p₂ = 0
    · subst hp₂
      have h20 := kf_case σ C r₁ r₂ hid hbd (j₁ := 2) (j₂ := 0)
        (Or.inr rfl) (Or.inl rfl) p₁ 0 (Or.inr hp₁) (Or.inl rfl)
      have h := Work.KMTPlan.A6.le_min_mul h00 h20
      simpa only [Work.KMTPlan.A6.wt_zero, Work.KMTPlan.A6.wt_eq_min hp₁,
        Work.KMTPlan.A6.rho_zero, mul_assoc] using h
    · have h02 := kf_case σ C r₁ r₂ hid hbd (j₁ := 0) (j₂ := 2)
        (Or.inl rfl) (Or.inr rfl) p₁ p₂ (Or.inl rfl) (Or.inr hp₂)
      have h20 := kf_case σ C r₁ r₂ hid hbd (j₁ := 2) (j₂ := 0)
        (Or.inr rfl) (Or.inl rfl) p₁ p₂ (Or.inr hp₁) (Or.inl rfl)
      have h22 := kf_case σ C r₁ r₂ hid hbd (j₁ := 2) (j₂ := 2)
        (Or.inr rfl) (Or.inr rfl) p₁ p₂ (Or.inr hp₁) (Or.inr hp₂)
      have h := Work.KMTPlan.A6.le_mul_min_min h00 h02 h20 h22
      simpa only [Work.KMTPlan.A6.wt_eq_min hp₁, Work.KMTPlan.A6.wt_eq_min hp₂,
        mul_assoc] using h

/-! ## Summation over the lattice -/

/-- **The `ℓ¹` mass of the Fourier coefficients.** -/
theorem hiCrudeTsum (K : ℤ × ℤ → ℂ) (C r₁ r₂ : ℝ) (hC : 0 ≤ C)
    (hr₁ : 0 < r₁) (hr₁1 : r₁ ≤ 1) (hr₂ : 0 < r₂) (hr₂1 : r₂ ≤ 1)
    (h : ∀ p : ℤ × ℤ, ‖K p‖ ≤ C * Work.KMTPlan.A6.wt r₁ p.1 * Work.KMTPlan.A6.wt r₂ p.2) :
    ∑' p : ℤ × ℤ, ‖K p‖ ≤ 100 * C := by
  obtain ⟨hs₁, hb₁⟩ := Work.KMTPlan.A6.wt_tsum_le r₁ hr₁ hr₁1
  obtain ⟨hs₂, hb₂⟩ := Work.KMTPlan.A6.wt_tsum_le r₂ hr₂ hr₂1
  have hmul : Summable (fun p : ℤ × ℤ =>
      Work.KMTPlan.A6.wt r₁ p.1 * Work.KMTPlan.A6.wt r₂ p.2) :=
    hs₁.mul_of_nonneg hs₂ (fun p => Work.KMTPlan.A6.wt_nonneg hr₁.le p)
      (fun p => Work.KMTPlan.A6.wt_nonneg hr₂.le p)
  have hmaj : Summable (fun p : ℤ × ℤ =>
      C * (Work.KMTPlan.A6.wt r₁ p.1 * Work.KMTPlan.A6.wt r₂ p.2)) := hmul.mul_left C
  have hpt : ∀ p : ℤ × ℤ, ‖K p‖ ≤
      C * (Work.KMTPlan.A6.wt r₁ p.1 * Work.KMTPlan.A6.wt r₂ p.2) := by
    intro p
    rw [← mul_assoc]
    exact h p
  have hsumm : Summable (fun p : ℤ × ℤ => ‖K p‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hpt hmaj
  have hle : (∑' p : ℤ × ℤ, ‖K p‖)
      ≤ ∑' p : ℤ × ℤ, C * (Work.KMTPlan.A6.wt r₁ p.1 * Work.KMTPlan.A6.wt r₂ p.2) :=
    hsumm.tsum_le_tsum hpt hmaj
  have hEq : (∑' p : ℤ × ℤ, C * (Work.KMTPlan.A6.wt r₁ p.1 * Work.KMTPlan.A6.wt r₂ p.2))
      = C * ((∑' p : ℤ, Work.KMTPlan.A6.wt r₁ p) * (∑' p : ℤ, Work.KMTPlan.A6.wt r₂ p)) := by
    rw [tsum_mul_left]
    rw [Summable.tsum_mul_tsum (f := Work.KMTPlan.A6.wt r₁) (g := Work.KMTPlan.A6.wt r₂)
      hs₁ hs₂ hmul]
  have hb : C * ((∑' p : ℤ, Work.KMTPlan.A6.wt r₁ p) * (∑' p : ℤ, Work.KMTPlan.A6.wt r₂ p))
      ≤ 100 * C := by
    have hA₁ : 0 ≤ ∑' p : ℤ, Work.KMTPlan.A6.wt r₁ p :=
      tsum_nonneg (fun p => Work.KMTPlan.A6.wt_nonneg hr₁.le p)
    have hA₂ : 0 ≤ ∑' p : ℤ, Work.KMTPlan.A6.wt r₂ p :=
      tsum_nonneg (fun p => Work.KMTPlan.A6.wt_nonneg hr₂.le p)
    have hb₁' : (∑' p : ℤ, Work.KMTPlan.A6.wt r₁ p) ≤ 4 := hb₁
    have hb₂' : (∑' p : ℤ, Work.KMTPlan.A6.wt r₂ p) ≤ 4 := hb₂
    have h16 : (∑' p : ℤ, Work.KMTPlan.A6.wt r₁ p)
        * (∑' p : ℤ, Work.KMTPlan.A6.wt r₂ p) ≤ 16 := by
      have h := mul_le_mul hb₁' hb₂' hA₂ (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    have h1 : C * ((∑' p : ℤ, Work.KMTPlan.A6.wt r₁ p)
        * (∑' p : ℤ, Work.KMTPlan.A6.wt r₂ p)) ≤ C * 16 :=
      mul_le_mul_of_nonneg_left h16 hC
    linarith [h1, hC]
  exact hle.trans (hEq.le.trans hb)

/-- **The `ℝ²` case of the crude multiplier bound**, in the curried form used by the proof. -/
theorem hiCrudeMult_curried (σ : ℝ → ℝ → ℂ)
    (hsm : ContDiff ℝ 4 (fun p : ℝ × ℝ => σ p.1 p.2))
    (hc : HasCompactSupport (fun p : ℝ × ℝ => σ p.1 p.2))
    {C r₁ r₂ : ℝ} (hC : 0 ≤ C)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₁1 : r₁ ≤ 1) (hr₂1 : r₂ ≤ 1)
    (hbd : ∀ i₁ i₂ : ℕ, i₁ ≤ 2 → i₂ ≤ 2 →
      ∫ z : ℝ × ℝ, ‖Work.KMTPlan.A6.dp i₁ i₂ σ z.1 z.2‖ ≤
        C * r₁ ^ ((1 : ℝ) - (i₁ : ℝ)) * r₂ ^ ((1 : ℝ) - (i₂ : ℝ))) :
    ∑' p : ℤ × ℤ, ‖kf σ p.1 p.2‖ ≤ 100 * C := by
  have hInt : ∀ i₁ i₂ : ℕ, i₁ ≤ 2 → i₂ ≤ 2 →
      Integrable (fun z : ℝ × ℝ => Work.KMTPlan.A6.dp i₁ i₂ σ z.1 z.2) volume := by
    intro i₁ i₂ h₁ h₂
    exact integrable_dp σ i₁ i₂ (hsm.of_le (by exact_mod_cast (by omega : i₁ + i₂ ≤ 4))) hc
  have hc0 : ∀ x : ℝ, HasCompactSupport (fun y : ℝ => σ x y) := by
    intro x
    simpa using compSupp_fiber_snd (fun p : ℝ × ℝ => σ p.1 p.2) hc x
  have hid : ∀ i₁ i₂ : ℕ, i₁ ≤ 2 → i₂ ≤ 2 → ∀ q₁ q₂ : ℤ,
      kf (Work.KMTPlan.A6.dp i₁ i₂ σ) q₁ q₂
        = (2 * (Real.pi : ℂ) * Complex.I * (q₁ : ℂ)) ^ i₁
          * (2 * (Real.pi : ℂ) * Complex.I * (q₂ : ℂ)) ^ i₂ * kf σ q₁ q₂ := by
    intro i₁ i₂ h₁ h₂ q₁ q₂
    have hJ : ContDiff ℝ (i₁ : WithTop ℕ∞)
        (fun p : ℝ × ℝ => Work.KMTPlan.A6.dp2 i₂ σ p.1 p.2) :=
      Work.KMTPlan.A6.cdp_contDiff_dp2_iter σ i₁ i₂ (by
        have h : ((i₁ + i₂ : ℕ) : WithTop ℕ∞) ≤ 4 := by
          exact_mod_cast (by omega : i₁ + i₂ ≤ 4)
        exact hsm.of_le h)
    refine kf_dp σ i₁ i₂ q₁ q₂ (hInt 0 0 (by norm_num) (by norm_num))
      (hInt 0 i₂ (by norm_num) h₂) (hInt i₁ i₂ h₁ h₂)
      (Work.KMTPlan.A6.cdp_fiber₂ σ i₂ (hsm.of_le (by
        exact_mod_cast (by omega : i₂ ≤ 4))))
      (fun x => by
        simpa using compSupp_fiber_snd (fun p : ℝ × ℝ => σ p.1 p.2) hc x)
      (fun y => Work.KMTPlan.A6.cdp_fiber₁ (Work.KMTPlan.A6.dp2 i₂ σ) i₁ hJ y)
      (fun y => compSupp_iteratedDeriv_fiber (fun p : ℝ × ℝ => σ p.1 p.2) hc i₂ y)
  exact hiCrudeTsum (fun p : ℤ × ℤ => kf σ p.1 p.2) C r₁ r₂ hC hr₁ hr₁1 hr₂ hr₂1
    (fun p => by rw [mul_assoc]; exact kf_le σ C r₁ r₂ hid hbd p.1 p.2)

end

end Work.KMTAreas.A7
