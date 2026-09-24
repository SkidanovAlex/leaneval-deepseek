import Mathlib
import Submission.Work.GM.Trace.Defs

/-!
# GM Lemma 4.3(1): uniform-in-`t` decay of `ĥ_t(ξ)`

`h_t(u) = w(u)² u^{it}` (GM (4.4)) is smooth and supported in `[1,2]`.  Writing
`h_t = w² · u^{i t}` and using that the `k`-th `u`-derivative of `u^{it} = exp (i t log u)`
is `(∏_{i<k} (i t - i)) · u^{it - k}` (of modulus `≤_k (1+|t|)^k` on `u ≥ 1`), the Leibniz
rule bounds the `j`-th derivative of `h_t` by `C_j (1+|t|)^j` on `[1,2]`, whence

  `(2π|ξ|)^j ‖ĥ_t(ξ)‖ ≤ ∫ ‖(h_t)^{(j)}‖ ≤ C_j (1+|t|)^j`   (`Real.fourier_iteratedDeriv`),

which is GM Lemma 4.3(1).
-/

open Complex Finset MeasureTheory Filter
open scoped BigOperators Topology
set_option autoImplicit false

namespace Work.GM.Trace

open Submission.GM Submission.LargeValues

/-! ## The two factors of `h_t` -/

/-- The oscillatory factor `u^{it} = exp (i t log u)`. -/
noncomputable def hphi (t u : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ) * (Real.log u : ℂ))

/-- `w(u)²` viewed as a complex valued function. -/
noncomputable def hw2C (u : ℝ) : ℂ := ((w2 u : ℝ) : ℂ)

theorem hfunLog_eq_mul (t : ℝ) : hfunLog t = hw2C * hphi t := rfl

theorem hfun_eq_mul (t : ℝ) : hfun t = hw2C * hphi t :=
  (funext (hfun_eq_hfunLog t)).trans (hfunLog_eq_mul t)

/-! ## Calculus of `u ↦ exp (c log u)` -/

/-- The iterated derivative of a `ℝ → ℂ` function obtained by coercing an `ℝ → ℝ` function
is the coercion of the iterated derivative. -/
theorem deriv_ofReal_comp (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => ((f y : ℝ) : ℂ)) x = ((deriv f x : ℝ) : ℂ) := by
  by_cases h : DifferentiableAt ℝ f x
  · exact (h.hasDerivAt.ofReal_comp).deriv
  · have h2 : ¬ DifferentiableAt ℝ (fun y : ℝ => ((f y : ℝ) : ℂ)) x := by
      intro hd
      have hcomp : DifferentiableAt ℝ (Complex.re ∘ fun y : ℝ => ((f y : ℝ) : ℂ)) x :=
        Complex.reCLM.differentiableAt.comp x hd
      exact h (by simpa [Function.comp_def] using hcomp)
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h2]
    simp

theorem iteratedDeriv_ofReal_comp : ∀ (k : ℕ) (f : ℝ → ℝ),
    iteratedDeriv k (fun y => ((f y : ℝ) : ℂ)) = fun y => ((iteratedDeriv k f y : ℝ) : ℂ) := by
  intro k
  induction k with
  | zero => intro f; ext x; simp
  | succ k ih =>
    intro f
    have hd : deriv (fun y : ℝ => ((f y : ℝ) : ℂ)) = fun y => ((deriv f y : ℝ) : ℂ) :=
      funext fun x => deriv_ofReal_comp f x
    rw [iteratedDeriv_succ', hd, ih (deriv f)]
    ext x
    simp only [iteratedDeriv_succ']

theorem cexp_ofReal_log {x : ℝ} (hx : 0 < x) :
    Complex.exp ((Real.log x : ℝ) : ℂ) = (x : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log hx]

theorem inv_eq_cexp_neg_log {x : ℝ} (hx : 0 < x) :
    ((x : ℂ))⁻¹ = Complex.exp (-(Real.log x : ℂ)) := by
  rw [Complex.exp_neg, cexp_ofReal_log hx]

/-- The derivative of `u ↦ exp (c · log u)` at a positive point `x`. -/
theorem hasDerivAt_cexp_mul_log (c : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => Complex.exp (c * (Real.log u : ℂ)))
      (Complex.exp (c * (Real.log x : ℂ)) * (c * (x : ℂ)⁻¹)) x := by
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx)
  have h2 : HasDerivAt (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
    h1.ofReal_comp
  have h3 : HasDerivAt (fun u : ℝ => c * ((Real.log u : ℝ) : ℂ)) (c * ((x⁻¹ : ℝ) : ℂ)) x :=
    h2.const_mul c
  have h4 : HasDerivAt (fun u : ℝ => Complex.exp (c * ((Real.log u : ℝ) : ℂ)))
      (Complex.exp (c * ((Real.log x : ℝ) : ℂ)) * (c * ((x⁻¹ : ℝ) : ℂ))) x := h3.cexp
  rw [Complex.ofReal_inv] at h4
  exact h4

/-- The `k`-th iterated derivative of `u ↦ exp (c · log u)` at a positive point:
`(∏_{i<k} (c - i)) · exp((c - k) log x)`. -/
theorem iteratedDeriv_cexp_mul_log (c : ℂ) (k : ℕ) :
    ∀ x : ℝ, 0 < x →
      iteratedDeriv k (fun u : ℝ => Complex.exp (c * (Real.log u : ℂ))) x
        = (∏ i ∈ Finset.range k, (c - (i : ℂ))) *
          Complex.exp ((c - (k : ℂ)) * (Real.log x : ℂ)) := by
  induction k with
  | zero =>
      intro x _
      simp
  | succ k ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      have hev : (fun u => iteratedDeriv k (fun u : ℝ => Complex.exp (c * (Real.log u : ℂ))) u)
          =ᶠ[nhds x] (fun u => (∏ i ∈ Finset.range k, (c - (i : ℂ))) *
            Complex.exp ((c - (k : ℂ)) * (Real.log u : ℂ))) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
        exact ih u hu
      rw [Filter.EventuallyEq.deriv_eq hev]
      have hg : HasDerivAt (fun u : ℝ => Complex.exp ((c - (k : ℂ)) * (Real.log u : ℂ)))
          (Complex.exp ((c - (k : ℂ)) * (Real.log x : ℂ)) *
            ((c - (k : ℂ)) * (x : ℂ)⁻¹)) x :=
        hasDerivAt_cexp_mul_log (c - (k : ℂ)) hx
      rw [deriv_const_mul _ hg.differentiableAt]
      rw [hg.deriv]
      rw [Finset.prod_range_succ, inv_eq_cexp_neg_log hx]
      have key : Complex.exp ((c - (k : ℂ)) * (Real.log x : ℂ)) *
            ((c - (k : ℂ)) * Complex.exp (-(Real.log x : ℂ)))
          = (c - (k : ℂ)) * Complex.exp ((c - ((k + 1 : ℕ) : ℂ)) * (Real.log x : ℂ)) := by
        have h1 : Complex.exp ((c - (k : ℂ)) * (Real.log x : ℂ)) *
              ((c - (k : ℂ)) * Complex.exp (-(Real.log x : ℂ)))
            = (c - (k : ℂ)) * (Complex.exp ((c - (k : ℂ)) * (Real.log x : ℂ)) *
                Complex.exp (-(Real.log x : ℂ))) := by ring
        rw [h1, ← Complex.exp_add]
        congr 1
        congr 1
        push_cast
        ring
      rw [key]
      ring

/-- The iterated derivatives of the oscillatory factor: for `x > 0`,
`(d/dx)^k x^{it} = (∏_{i<k} (it - i)) · x^{it-k}`. -/
theorem hphi_iteratedDeriv (t : ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (hphi t) x
      = (∏ i ∈ Finset.range k, (Complex.I * (t : ℂ) - (i : ℂ))) *
        Complex.exp ((Complex.I * (t : ℂ) - (k : ℂ)) * (Real.log x : ℂ)) := by
  change iteratedDeriv k (fun u : ℝ => Complex.exp (Complex.I * (t : ℂ) * (Real.log u : ℂ))) x
      = (∏ i ∈ Finset.range k, (Complex.I * (t : ℂ) - (i : ℂ))) *
        Complex.exp ((Complex.I * (t : ℂ) - (k : ℂ)) * (Real.log x : ℂ))
  exact iteratedDeriv_cexp_mul_log (Complex.I * (t : ℂ)) k x hx

/-! ## Smoothness and support of `h_t` -/

theorem contDiff_hw2C : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hw2C :=
  Complex.ofRealCLM.contDiff.comp w2_contDiff

theorem contDiffAt_hphi (t : ℝ) (n : WithTop ℕ∞) {x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ n (hphi t) x := by
  have hlog : ContDiffAt ℝ n (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp x (Real.contDiffAt_log.mpr hx)
  have h2 : ContDiffAt ℝ n (fun u : ℝ => (Complex.I * (t : ℂ)) • ((Real.log u : ℝ) : ℂ)) x :=
    hlog.const_smul (Complex.I * (t : ℂ))
  have h3 : ContDiffAt ℝ n (Complex.exp) ((Complex.I * (t : ℂ)) • ((Real.log x : ℝ) : ℂ)) :=
    Complex.contDiff_exp.contDiffAt
  exact h3.comp x h2

theorem contDiff_hfun (t : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hfun t) := by
  rw [hfun_eq_mul]
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < 1
  · have hmem : ∀ᶠ y in nhds x, (hw2C * hphi t) y = (0 : ℂ) := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      have hy' : y ∉ Set.Icc (1 : ℝ) 2 := fun h => absurd h.1 (not_le.mpr hy)
      rw [Pi.mul_apply, hw2C, hphi, w2_eq_zero_of_notMem hy']
      simp
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hmem
  · push Not at hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at hx; norm_num at hx
    exact (contDiff_hw2C.contDiffAt).mul (contDiffAt_hphi t _ hx0)

theorem hasCompactSupport_hfun (t : ℝ) : HasCompactSupport (hfun t) := by
  refine HasCompactSupport.intro (K := Set.Icc (1 : ℝ) 2) isCompact_Icc (fun x hx => ?_)
  rw [hfun]
  have h := bumpW_eq_zero_of_notMem hx
  rw [h]
  norm_num

theorem integrable_iteratedDeriv_hfun (t : ℝ) (n : ℕ) :
    Integrable (iteratedDeriv n (hfun t)) := by
  have hcs : HasCompactSupport (hfun t) := hasCompactSupport_hfun t
  have hsupp : HasCompactSupport (iteratedDeriv n (hfun t)) := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact (hcs.iteratedFDeriv (𝕜 := ℝ) n).comp_left (map_zero _)
  exact ((contDiff_hfun t).continuous_iteratedDeriv n (by exact_mod_cast le_top))
    |>.integrable_of_hasCompactSupport hsupp

/-! ## Derivative bounds -/

/-- A uniform bound for `|(d/dx)^k w|`, from `bumpW_deriv_bdd`. -/
noncomputable def wderivBound (k : ℕ) : ℝ := Classical.choose (bumpW_deriv_bdd k)

theorem wderivBound_nonneg (k : ℕ) : 0 ≤ wderivBound k :=
  (Classical.choose_spec (bumpW_deriv_bdd k)).1

theorem abs_iteratedDeriv_bumpW_le (k : ℕ) (x : ℝ) :
    |iteratedDeriv k bumpW x| ≤ wderivBound k :=
  (Classical.choose_spec (bumpW_deriv_bdd k)).2 x

/-- A uniform bound for `|(d/dx)^k (w²)|`, from the Leibniz rule and `wderivBound`. -/
noncomputable def w2derivBound (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * wderivBound i * wderivBound (k - i)

theorem w2derivBound_nonneg (k : ℕ) : 0 ≤ w2derivBound k := by
  rw [w2derivBound]
  exact Finset.sum_nonneg fun i _ => by
    have h1 := wderivBound_nonneg i
    have h2 := wderivBound_nonneg (k - i)
    positivity

theorem abs_iteratedDeriv_w2_le (k : ℕ) (x : ℝ) :
    |iteratedDeriv k w2 x| ≤ w2derivBound k := by
  have hw2 : w2 = bumpW * bumpW := funext fun y => by rw [w2, pow_two]; rfl
  rw [hw2]
  rw [iteratedDeriv_mul ((bumpW_contDiff.contDiffAt).of_le (by exact_mod_cast le_top))
    ((bumpW_contDiff.contDiffAt).of_le (by exact_mod_cast le_top))]
  rw [w2derivBound]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have h2 : |iteratedDeriv i bumpW x| ≤ wderivBound i := abs_iteratedDeriv_bumpW_le i x
  have h3 : |iteratedDeriv (k - i) bumpW x| ≤ wderivBound (k - i) :=
    abs_iteratedDeriv_bumpW_le (k - i) x
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.choose i : ℝ))]
  have hA : (0 : ℝ) ≤ (k.choose i : ℝ) := by positivity
  have hAi : (0 : ℝ) ≤ (k.choose i : ℝ) * wderivBound i := mul_nonneg hA (wderivBound_nonneg i)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hA) (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_left h3 hAi)

theorem norm_iteratedDeriv_hw2C_le (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k hw2C x‖ ≤ w2derivBound k := by
  have h1 : iteratedDeriv k hw2C = fun y => ((iteratedDeriv k w2 y : ℝ) : ℂ) := by
    rw [show hw2C = fun y : ℝ => ((w2 y : ℝ) : ℂ) from rfl]
    exact iteratedDeriv_ofReal_comp k w2
  rw [h1]
  change ‖(((iteratedDeriv k w2 x : ℝ)) : ℂ)‖ ≤ w2derivBound k
  simpa using abs_iteratedDeriv_w2_le k x

/-- `∏_{i<k} (1+i)`, the factorial-like constant coming from the derivatives of `w²`. -/
noncomputable def phifact (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (1 + (i : ℝ))

theorem phifact_nonneg (k : ℕ) : 0 ≤ phifact k :=
  Finset.prod_nonneg fun i _ => by positivity

theorem norm_iteratedDeriv_hphi_le (t : ℝ) (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖iteratedDeriv k (hphi t) x‖ ≤ phifact k * (1 + |t|) ^ k := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  rw [hphi_iteratedDeriv t k hx0, norm_mul]
  have hprod : ‖∏ i ∈ Finset.range k, (Complex.I * (t : ℂ) - (i : ℂ))‖
      ≤ ∏ i ∈ Finset.range k, (1 + |t|) * (1 + (i : ℝ)) := by
    refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) ?_)
    intro i hi
    calc ‖Complex.I * (t : ℂ) - (i : ℂ)‖ ≤ ‖Complex.I * (t : ℂ)‖ + ‖(i : ℂ)‖ := norm_sub_le _ _
      _ = |t| + (i : ℝ) := by simp
      _ ≤ (1 + |t|) * (1 + (i : ℝ)) := by
          nlinarith [abs_nonneg t, (Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))]
  have hexp : ‖Complex.exp ((Complex.I * (t : ℂ) - (k : ℂ)) * (Real.log x : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    have hre : ((Complex.I * (t : ℂ) - (k : ℂ)) * (Real.log x : ℂ)).re = -(k * Real.log x) := by
      simp [Complex.mul_re, Complex.sub_re, Complex.natCast_re, Complex.natCast_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_le_one_iff]
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  calc ‖∏ i ∈ Finset.range k, (Complex.I * (t : ℂ) - (i : ℂ))‖ *
        ‖Complex.exp ((Complex.I * (t : ℂ) - (k : ℂ)) * (Real.log x : ℂ))‖
      ≤ (∏ i ∈ Finset.range k, (1 + |t|) * (1 + (i : ℝ))) * 1 :=
        mul_le_mul hprod hexp (norm_nonneg _) (Finset.prod_nonneg fun i _ => by positivity)
    _ = phifact k * (1 + |t|) ^ k := by
        rw [phifact, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
        ring

/-- The overall constant multiplying `(1+|t|)^j` in the pointwise bound for the `j`-th
derivative of `h_t`. -/
noncomputable def Cjconst (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * w2derivBound i * phifact (j - i)

theorem Cjconst_nonneg (j : ℕ) : 0 ≤ Cjconst j := by
  rw [Cjconst]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (by positivity) (w2derivBound_nonneg i)) (phifact_nonneg (j - i))

theorem norm_iteratedDeriv_hfun_le (t : ℝ) (j : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖iteratedDeriv j (hfun t) x‖ ≤ Cjconst j * (1 + |t|) ^ j := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hmul : iteratedDeriv j (hfun t) x
      = ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℂ) * iteratedDeriv i hw2C x *
          iteratedDeriv (j - i) (hphi t) x := by
    rw [hfun_eq_mul]
    exact iteratedDeriv_mul ((contDiff_hw2C.contDiffAt).of_le (by exact_mod_cast le_top))
      (contDiffAt_hphi t _ (ne_of_gt hx0))
  rw [hmul]
  calc ‖∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℂ) * iteratedDeriv i hw2C x *
          iteratedDeriv (j - i) (hphi t) x‖
      ≤ ∑ i ∈ Finset.range (j + 1), ‖((j.choose i : ℕ) : ℂ) * iteratedDeriv i hw2C x *
          iteratedDeriv (j - i) (hphi t) x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℝ) * w2derivBound i * phifact (j - i)) *
          (1 + |t|) ^ j := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [norm_mul, norm_mul, RCLike.norm_natCast]
        have h1 : ‖iteratedDeriv i hw2C x‖ ≤ w2derivBound i := norm_iteratedDeriv_hw2C_le i x
        have h2 : ‖iteratedDeriv (j - i) (hphi t) x‖ ≤ phifact (j - i) * (1 + |t|) ^ (j - i) :=
          norm_iteratedDeriv_hphi_le t (j - i) hx
        have hp : (1 : ℝ) ≤ 1 + |t| := by have := abs_nonneg t; linarith
        have hpow : (1 + |t|) ^ (j - i) ≤ (1 + |t|) ^ j :=
          pow_le_pow_right₀ hp (Nat.sub_le j i)
        have hA : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
        have hAw : (0 : ℝ) ≤ (j.choose i : ℝ) * w2derivBound i :=
          mul_nonneg hA (w2derivBound_nonneg i)
        have hAwp : (0 : ℝ) ≤ (j.choose i : ℝ) * w2derivBound i * phifact (j - i) :=
          mul_nonneg hAw (phifact_nonneg (j - i))
        calc ((j.choose i : ℝ)) * ‖iteratedDeriv i hw2C x‖ *
              ‖iteratedDeriv (j - i) (hphi t) x‖
            ≤ (j.choose i : ℝ) * w2derivBound i *
                (phifact (j - i) * (1 + |t|) ^ (j - i)) :=
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hA) (norm_nonneg _)).trans
                (mul_le_mul_of_nonneg_left h2 hAw)
          _ ≤ (j.choose i : ℝ) * w2derivBound i * (phifact (j - i) * (1 + |t|) ^ j) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (phifact_nonneg _)) hAw
          _ = ((j.choose i : ℝ) * w2derivBound i * phifact (j - i)) * (1 + |t|) ^ j := by ring
    _ = Cjconst j * (1 + |t|) ^ j := by
        rw [Cjconst, Finset.sum_mul]

theorem iteratedDeriv_hfun_eq_zero_of_notMem (t : ℝ) (j : ℕ) {x : ℝ}
    (hx : x ∉ Set.Icc (1 : ℝ) 2) : iteratedDeriv j (hfun t) x = 0 := by
  have hmem : ∀ᶠ y in nhds x, hfun t y = 0 := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    rw [hfun]
    have h := bumpW_eq_zero_of_notMem hy
    rw [h]; norm_num
  have h2 : iteratedDeriv j (hfun t) =ᶠ[nhds x] iteratedDeriv j (fun _ : ℝ => (0 : ℂ)) :=
    Filter.EventuallyEq.iteratedDeriv hmem j
  have h3 : iteratedDeriv j (fun _ : ℝ => (0 : ℂ)) x = 0 := by simp
  exact (h2.eq_of_nhds).trans h3

theorem integral_iteratedDeriv_hfun_le (t : ℝ) (j : ℕ) :
    ∫ x, ‖iteratedDeriv j (hfun t) x‖ ≤ Cjconst j * (1 + |t|) ^ j := by
  have hg0 : ∀ x ∉ Set.Icc (1 : ℝ) 2, ‖iteratedDeriv j (hfun t) x‖ = 0 := by
    intro x hx
    rw [iteratedDeriv_hfun_eq_zero_of_notMem t j hx, norm_zero]
  have hC : IntegrableOn (fun _ : ℝ => Cjconst j * (1 + |t|) ^ j) (Set.Icc (1 : ℝ) 2) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; norm_num)
      (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
  have h2 := integral_mono_ae (μ := volume.restrict (Set.Icc (1 : ℝ) 2))
      (f := fun x => ‖iteratedDeriv j (hfun t) x‖)
      (g := fun _ => Cjconst j * (1 + |t|) ^ j)
      ((integrable_iteratedDeriv_hfun t j).norm.integrableOn) hC ?_
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (1 : ℝ) 2)
      (f := fun x => ‖iteratedDeriv j (hfun t) x‖) hg0]
    calc ∫ x in Set.Icc (1 : ℝ) 2, ‖iteratedDeriv j (hfun t) x‖
        ≤ ∫ x in Set.Icc (1 : ℝ) 2, Cjconst j * (1 + |t|) ^ j := h2
      _ = Cjconst j * (1 + |t|) ^ j := by
          rw [setIntegral_const, Measure.real_def, Real.volume_Icc]; norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact norm_iteratedDeriv_hfun_le t j hx.1

/-! ## The decay estimate -/

theorem norm_two_pi_I_mul (x : ℝ) :
    ‖(2 * Real.pi * Complex.I * (x : ℂ))‖ = 2 * Real.pi * |x| := by
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_I, mul_one]
  rw [show ‖(Real.pi : ℂ)‖ = Real.pi by simp [abs_of_nonneg Real.pi_pos.le]]
  simp

theorem hhat_decay_deriv :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, ξ ≠ 0 →
      ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j := by
  intro j
  refine ⟨Cjconst j / (2 * Real.pi) ^ j, div_nonneg (Cjconst_nonneg j) (by positivity), ?_⟩
  intro t ξ hξ
  have hfour := Real.fourier_iteratedDeriv (f := hfun t) (N := (j : ℕ∞)) (n := j)
    ((contDiff_hfun t).of_le (by exact_mod_cast le_top))
    (fun n _ => integrable_iteratedDeriv_hfun t n) (le_refl _)
  have hnorm : ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) ^ j‖ = (2 * Real.pi * |ξ|) ^ j := by
    rw [norm_pow, norm_two_pi_I_mul]
  have h1 : ‖FourierTransform.fourier (iteratedDeriv j (hfun t)) ξ‖
      ≤ ∫ x, ‖iteratedDeriv j (hfun t) x‖ := by
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [Circle.norm_smul]
  have hbound : ‖Submission.GM.hhat t ξ‖ * (2 * Real.pi * |ξ|) ^ j
      ≤ Cjconst j * (1 + |t|) ^ j := by
    have h3 : ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) ^ j • FourierTransform.fourier (hfun t) ξ‖
        ≤ Cjconst j * (1 + |t|) ^ j := by
      rw [← congrFun hfour ξ]
      exact h1.trans (integral_iteratedDeriv_hfun_le t j)
    rw [norm_smul, hnorm] at h3
    rwa [mul_comm] at h3
  have hpos : 0 < (2 * Real.pi * |ξ|) ^ j := by positivity
  have h4 : ‖Submission.GM.hhat t ξ‖
      ≤ (Cjconst j * (1 + |t|) ^ j) / (2 * Real.pi * |ξ|) ^ j :=
    (le_div_iff₀ hpos).mpr hbound
  refine h4.trans (le_of_eq ?_)
  rw [mul_pow]
  field_simp

end Work.GM.Trace
