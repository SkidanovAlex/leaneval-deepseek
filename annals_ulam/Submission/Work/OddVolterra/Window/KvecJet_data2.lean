import Mathlib
import Submission.Work.OddVolterra.Window.KvecJet_data
import Submission.Work.OddVolterra.Window.KvecDefs
import Submission.Work.OddVolterra.Window.Zrad_jet_bounds_gen
import Submission.Work.OddVolterra.Window.deriv_deriv_pi
import Submission.Work.OddVolterra.Existence.hquot_contDiff
import Submission.Commons.Analysis.Calculus.iteratedFDeriv_intervalIntegral_comp_smul

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## Elementary second-derivative helpers -/

/-- The `m`-th derivative of the zero function is `0`. -/
private lemma kjd2_iteratedDeriv_zero (m : ℕ) (a : ℝ) :
    iteratedDeriv m (0 : ℝ → ℝ) a = 0 := by
  change iteratedDeriv m (fun _ : ℝ => (0 : ℝ)) a = 0
  rw [iteratedDeriv_const]
  split_ifs <;> simp

/-- The second derivative of an `m`-th iterated derivative is the `(m+2)`-nd derivative. -/
private lemma kjd2_deriv2_iteratedDeriv (f : ℝ → ℝ) (m : ℕ) (a : ℝ) :
    deriv (deriv (fun u : ℝ => iteratedDeriv m f u)) a = iteratedDeriv (m + 2) f a := by
  have h1 : deriv (fun u : ℝ => iteratedDeriv m f u) = iteratedDeriv (m + 1) f :=
    (iteratedDeriv_succ (n := m) (f := f)).symm
  rw [h1]
  have h2 : deriv (iteratedDeriv (m + 1) f) a = iteratedDeriv (m + 2) f a := by
    show deriv (iteratedDeriv (m + 1) f) a = iteratedDeriv (m + 1 + 1) f a
    exact congrFun (iteratedDeriv_succ (n := m + 1) (f := f)).symm a
  exact h2

/-- `iteratedDeriv 2 f` is the second derivative of `f`. -/
private lemma kjd2_iteratedDeriv_two (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- The second derivative of a constant function is `0`. -/
private lemma kjd2_deriv2_const (c : ℝ) (a : ℝ) : deriv (deriv (fun _ : ℝ => c)) a = 0 := by
  have h : deriv (fun _ : ℝ => c) = fun _ : ℝ => (0 : ℝ) := by funext x; simp
  rw [h]; simp

/-- The second derivative of the identity is `0`. -/
private lemma kjd2_deriv2_id (a : ℝ) : deriv (deriv (fun u : ℝ => u)) a = 0 := by
  have h : deriv (fun u : ℝ => u) = fun _ : ℝ => (1 : ℝ) := by funext x; simp
  rw [h]; simp

/-- The second derivative of an affine function is `0`. -/
private lemma kjd2_iteratedDeriv_two_affine (c d a : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => c * x + d) a = 0 := by
  have h1 : deriv (fun x : ℝ => c * x + d) = fun _ : ℝ => c := by
    funext x
    have h := (((hasDerivAt_id x).const_mul c).add_const d)
    simpa using h.deriv
  rw [kjd2_iteratedDeriv_two, h1]
  simp

/-- The second `u`-derivative of the radicand jet `u ↦ kjet f σ t u i` is the `(i+2)`-nd
derivative of `Zrad f (·,σ,t)`. -/
private lemma kjd2_deriv2_kjet {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (σ t : ℝ) (i : ℕ) (a : ℝ) :
    deriv (deriv (fun u : ℝ => kjet f σ t u i)) a
      = iteratedDeriv (i + 2) (fun v : ℝ => KernelExt.Zrad f (v, σ, t)) a := by
  have h1 : (fun u : ℝ => kjet f σ t u i)
      = fun u : ℝ => iteratedDeriv i (fun v : ℝ => KernelExt.Zrad f (v, σ, t)) u := by
    funext u
    exact kjet_eq_Zrad hf σ t u i
  rw [h1]
  exact kjd2_deriv2_iteratedDeriv _ i a

/-! ## The first and second derivatives of the divided difference -/

/-- The `u`-derivative of `hquot h · σ` is the average of `h''` along the segment `[u,σ]`. -/
private lemma kjd2_hasDerivAt_hquot {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ u : ℝ) :
    HasDerivAt (fun x : ℝ => hquot h x σ)
      (∫ τ in (0 : ℝ)..1, (1 - τ) * iteratedDeriv 2 h (u + τ * (σ - u))) u := by
  have hdc : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
    simpa only [Function.iterate_one] using hh.iterate_deriv 1
  have hdd2 : (fun x : ℝ => iteratedDeriv 2 h x) = deriv (deriv h) := by
    funext x
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hdc2 : Continuous (fun x : ℝ => iteratedDeriv 2 h x) := by
    rw [hdd2]
    exact hdc.continuous_deriv (by simp)
  have hf : Continuous (Function.uncurry fun t τ : ℝ => deriv h (t + τ * (σ - t))) :=
    hdc.continuous.comp
      (continuous_fst.add (continuous_snd.mul (continuous_const.sub continuous_fst)))
  have hf' : Continuous (Function.uncurry fun t τ : ℝ =>
      (1 - τ) * iteratedDeriv 2 h (t + τ * (σ - t))) :=
    (continuous_const.sub continuous_snd).mul
      (hdc2.comp (continuous_fst.add (continuous_snd.mul (continuous_const.sub continuous_fst))))
  have hdiff : ∀ t τ : ℝ, HasDerivAt (fun t : ℝ => deriv h (t + τ * (σ - t)))
      ((1 - τ) * iteratedDeriv 2 h (t + τ * (σ - t))) t := by
    intro t τ
    have hφ : HasDerivAt (fun t : ℝ => t + τ * (σ - t)) (1 - τ) t := by
      have he : (fun t : ℝ => t + τ * (σ - t)) = fun t : ℝ => t + τ * (-t) + τ * σ := by
        funext t; ring
      rw [he]
      have he' : (1 : ℝ) - τ = 1 + τ * (-1) := by ring
      rw [he']
      exact (((hasDerivAt_id t).add (((hasDerivAt_id t).neg).const_mul τ))).add_const (τ * σ)
    have hdh : HasDerivAt (deriv h) (iteratedDeriv 2 h (t + τ * (σ - t))) (t + τ * (σ - t)) := by
      have hd : DifferentiableAt ℝ (deriv h) (t + τ * (σ - t)) :=
        (hdc.differentiable (by simp)).differentiableAt
      have h2 : iteratedDeriv 2 h (t + τ * (σ - t)) = deriv (deriv h) (t + τ * (σ - t)) :=
        congrFun hdd2 _
      simpa [h2] using hd.hasDerivAt
    have hcomp := hdh.comp t hφ
    have he'' : iteratedDeriv 2 h (t + τ * (σ - t)) * (1 - τ)
        = (1 - τ) * iteratedDeriv 2 h (t + τ * (σ - t)) := by ring
    rw [← he'']
    exact hcomp
  have hmain := Commons.Analysis.Calculus.hasDerivAt_intervalIntegral_of_continuous
    (f := fun t τ : ℝ => deriv h (t + τ * (σ - t)))
    (f' := fun t τ : ℝ => (1 - τ) * iteratedDeriv 2 h (t + τ * (σ - t)))
    (a := (0 : ℝ)) (b := 1) (t₀ := u) hf hf' hdiff
  simpa [hquot] using hmain

/-- The derivative of `hquot h · σ`, as a function. -/
private lemma kjd2_deriv_hquot_eq {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) :
    deriv (fun x : ℝ => hquot h x σ)
      = fun x : ℝ => ∫ τ in (0 : ℝ)..1, (1 - τ) * iteratedDeriv 2 h (x + τ * (σ - x)) := by
  funext u
  exact (kjd2_hasDerivAt_hquot hh σ u).deriv

/-- `|hquot h a σ| ≤ δ` when `|h'| ≤ δ`. -/
private lemma kjd2_hquot_bound {h : ℝ → ℝ} {δ : ℝ} (h1 : ∀ s : ℝ, |deriv h s| ≤ δ) (σ a : ℝ) :
    |hquot h a σ| ≤ δ := by
  have hpoint : ∀ τ ∈ Set.uIoc (0 : ℝ) 1, ‖deriv h (a + τ * (σ - a))‖ ≤ δ := by
    intro τ _
    simpa [Real.norm_eq_abs] using h1 (a + τ * (σ - a))
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun τ : ℝ => deriv h (a + τ * (σ - a))) (C := δ) hpoint
  simpa [hquot, Real.norm_eq_abs] using hmain

/-- `|d/da (hquot h · σ) a| ≤ δ` when `|h''| ≤ δ`. -/
private lemma kjd2_deriv_hquot_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (h2 : ∀ s : ℝ, |iteratedDeriv 2 h s| ≤ δ) (σ a : ℝ) :
    |deriv (fun x : ℝ => hquot h x σ) a| ≤ δ := by
  rw [kjd2_deriv_hquot_eq hh σ]
  have hpoint : ∀ τ ∈ Set.uIoc (0 : ℝ) 1,
      ‖(1 - τ) * iteratedDeriv 2 h (a + τ * (σ - a))‖ ≤ δ := by
    intro τ hτ
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |1 - τ| ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
      rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
    calc |1 - τ| * |iteratedDeriv 2 h (a + τ * (σ - a))| ≤ 1 * δ :=
          mul_le_mul h1 (h2 _) (abs_nonneg _) (by norm_num)
      _ = δ := by ring
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun τ : ℝ => (1 - τ) * iteratedDeriv 2 h (a + τ * (σ - a))) (C := δ) hpoint
  simpa [Real.norm_eq_abs] using hmain

/-- **Second derivative of the divided difference.**  If `|h'''| ≤ δ` then
`|d²/da² (hquot h · σ) a| ≤ δ`. -/
private lemma kjd2_hquot_deriv2 {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (h3 : ∀ s : ℝ, |iteratedDeriv 3 h s| ≤ δ) (σ a : ℝ) :
    |deriv (deriv (fun x : ℝ => hquot h x σ)) a| ≤ δ := by
  have h2cd : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => iteratedDeriv 2 h x) := by
    have h := hh.iterate_deriv 2
    simpa [iteratedDeriv_eq_iterate] using h
  have h2c : Continuous (fun x : ℝ => iteratedDeriv 2 h x) := h2cd.continuous
  have hderiv3 : ∀ x : ℝ, |deriv (fun x : ℝ => iteratedDeriv 2 h x) x| ≤ δ := by
    intro x
    have he : deriv (fun x : ℝ => iteratedDeriv 2 h x) x = iteratedDeriv 3 h x :=
      congrFun (iteratedDeriv_succ (n := 2) (f := h)).symm x
    rw [he]; exact h3 x
  have hlip2 : ∀ u v : ℝ, |iteratedDeriv 2 h u - iteratedDeriv 2 h v| ≤ δ * |u - v| := by
    intro u v
    exact abs_sub_le_mul_of_deriv_bound (f := fun x : ℝ => iteratedDeriv 2 h x) (C := δ)
      (fun x => (h2cd.differentiable (by simp)).differentiableAt) hderiv3 u v
  have hcontg : ∀ y : ℝ,
      IntervalIntegrable (fun τ : ℝ => (1 - τ) * iteratedDeriv 2 h (y + τ * (σ - y))) volume 0 1 :=
    fun y => (((continuous_const.sub continuous_id).mul (h2c.comp (by fun_prop)))).intervalIntegrable _ _
  have hLipG : ∀ x : ℝ,
      ‖(fun y : ℝ => ∫ τ in (0 : ℝ)..1, (1 - τ) * iteratedDeriv 2 h (y + τ * (σ - y))) x
        - (fun y : ℝ => ∫ τ in (0 : ℝ)..1, (1 - τ) * iteratedDeriv 2 h (y + τ * (σ - y))) a‖
      ≤ δ * ‖x - a‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    show |(∫ τ in (0 : ℝ)..1, (1 - τ) * iteratedDeriv 2 h (x + τ * (σ - x)))
        - (∫ τ in (0 : ℝ)..1, (1 - τ) * iteratedDeriv 2 h (a + τ * (σ - a)))| ≤ δ * |x - a|
    rw [← intervalIntegral.integral_sub (hcontg x) (hcontg a)]
    have hpoint : ∀ τ ∈ Set.uIoc (0 : ℝ) 1,
        ‖(1 - τ) * iteratedDeriv 2 h (x + τ * (σ - x))
          - (1 - τ) * iteratedDeriv 2 h (a + τ * (σ - a))‖ ≤ δ * |x - a| := by
      intro τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
      rw [Real.norm_eq_abs]
      have hfac : (1 - τ) * iteratedDeriv 2 h (x + τ * (σ - x))
            - (1 - τ) * iteratedDeriv 2 h (a + τ * (σ - a))
          = (1 - τ) * (iteratedDeriv 2 h (x + τ * (σ - x))
              - iteratedDeriv 2 h (a + τ * (σ - a))) := by ring
      rw [hfac, abs_mul]
      have habs1 : |1 - τ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
      have hd2 : |iteratedDeriv 2 h (x + τ * (σ - x)) - iteratedDeriv 2 h (a + τ * (σ - a))|
          ≤ δ * (|1 - τ| * |x - a|) := by
        have h := hlip2 (x + τ * (σ - x)) (a + τ * (σ - a))
        have harg : |(x + τ * (σ - x)) - (a + τ * (σ - a))| = |1 - τ| * |x - a| := by
          rw [show (x + τ * (σ - x)) - (a + τ * (σ - a)) = (1 - τ) * (x - a) by ring, abs_mul]
        rwa [harg] at h
      calc |1 - τ| * |iteratedDeriv 2 h (x + τ * (σ - x)) - iteratedDeriv 2 h (a + τ * (σ - a))|
          ≤ 1 * (δ * (|1 - τ| * |x - a|)) :=
            mul_le_mul habs1 hd2 (abs_nonneg _) (by norm_num)
        _ ≤ δ * |x - a| := by
            have h3 : δ * (|1 - τ| * |x - a|) ≤ δ * (1 * |x - a|) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right habs1 (abs_nonneg _)) hδ0
            calc 1 * (δ * (|1 - τ| * |x - a|)) = δ * (|1 - τ| * |x - a|) := by ring
              _ ≤ δ * (1 * |x - a|) := h3
              _ = δ * |x - a| := by ring
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun τ : ℝ => (1 - τ) * iteratedDeriv 2 h (x + τ * (σ - x))
        - (1 - τ) * iteratedDeriv 2 h (a + τ * (σ - a))) (C := δ * |x - a|) hpoint
    rw [Real.norm_eq_abs] at hint
    calc |∫ τ in (0 : ℝ)..1, ((1 - τ) * iteratedDeriv 2 h (x + τ * (σ - x))
            - (1 - τ) * iteratedDeriv 2 h (a + τ * (σ - a)))|
        ≤ (δ * |x - a|) * |1 - 0| := hint
      _ = δ * |x - a| := by norm_num
  rw [kjd2_deriv_hquot_eq hh σ]
  rw [← Real.norm_eq_abs]
  refine norm_deriv_le_of_lip' hδ0 (Filter.Eventually.of_forall ?_)
  intro x
  exact hLipG x

/-! ## The second derivative of the Abel radicand -/

/-- **Second `a`-derivative of the Abel radicand.**  On the transition window,
`|d² krad| ≤ 14 δ`, and the same bound holds for the difference from the unperturbed radicand
(whose second derivative vanishes identically). -/
private lemma kjd2_krad_deriv2 (h : ℝ → ℝ) (δ σ t a : ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hbnd : ∀ k : ℕ, k ≤ 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    (hσ : σ ∈ Set.Icc (7 / 10 : ℝ) 1) (ht2 : |t| ≤ 2)
    (ha : a ∈ Set.Icc (9 / 20 : ℝ) σ) :
    |deriv (deriv (fun a' : ℝ => krad h σ t a')) a| ≤ 14 * δ ∧
    |deriv (deriv (fun a' : ℝ => krad h σ t a')) a -
     deriv (deriv (fun a' : ℝ => krad 0 σ t a')) a| ≤ 14 * δ := by
  have h0 : ∀ s : ℝ, |h s| ≤ δ := fun s => by simpa using hbnd 0 (by norm_num) s
  have h1 : ∀ s : ℝ, |deriv h s| ≤ δ := fun s => by
    simpa [iteratedDeriv_one] using hbnd 1 (by norm_num) s
  have h2 : ∀ s : ℝ, |iteratedDeriv 2 h s| ≤ δ := fun s => hbnd 2 (by norm_num) s
  have h3 : ∀ s : ℝ, |iteratedDeriv 3 h s| ≤ δ := fun s => hbnd 3 (by norm_num) s
  have hσ1 : 7 / 10 ≤ σ := hσ.1
  have hσ2 : σ ≤ 1 := hσ.2
  have ha1 : 9 / 20 ≤ a := ha.1
  have ha2 : a ≤ σ := ha.2
  -- the divided difference and its derivatives
  have hA0 : |hquot h a σ| ≤ δ := kjd2_hquot_bound h1 σ a
  have hA1 : |deriv (fun x : ℝ => hquot h x σ) a| ≤ δ := kjd2_deriv_hquot_bound hh h2 σ a
  have hA2 : |iteratedDeriv 2 (fun x : ℝ => hquot h x σ) a| ≤ δ := by
    rw [kjd2_iteratedDeriv_two]
    exact kjd2_hquot_deriv2 hh hδ0 h3 σ a
  -- the two factors
  have hf_deriv : deriv (fun x : ℝ => t + hquot h x σ) = deriv (fun x : ℝ => hquot h x σ) :=
    deriv_const_add' t
  have hf2 : iteratedDeriv 2 (fun x : ℝ => t + hquot h x σ) a
      = iteratedDeriv 2 (fun x : ℝ => hquot h x σ) a := by
    rw [kjd2_iteratedDeriv_two, kjd2_iteratedDeriv_two, hf_deriv]
  have hg1 : deriv (fun x : ℝ => (σ + x) * t + h σ + h x) a = t + deriv h a := by
    have hhd : DifferentiableAt ℝ h a := (hh.differentiable (by simp)).differentiableAt
    have h1' : HasDerivAt (fun x : ℝ => (σ + x) * t + h σ) t a := by
      have h := (((hasDerivAt_id a).const_add σ).mul_const t).add_const (h σ)
      simpa using h
    have h2' : HasDerivAt (fun x : ℝ => (σ + x) * t + h σ + h x) (t + deriv h a) a :=
      h1'.add hhd.hasDerivAt
    exact h2'.deriv
  have hg2 : iteratedDeriv 2 (fun x : ℝ => (σ + x) * t + h σ + h x) a
      = iteratedDeriv 2 h a := by
    have hsplit : (fun x : ℝ => (σ + x) * t + h σ + h x)
        = (fun x : ℝ => t * x + (σ * t + h σ)) + h := by
      funext x; simp only [Pi.add_apply]; ring
    rw [hsplit, iteratedDeriv_add (by fun_prop)
      (hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
      kjd2_iteratedDeriv_two_affine, zero_add]
  -- the pointwise bounds on the factors
  have hf0b : |t + hquot h a σ| ≤ 3 := by
    calc |t + hquot h a σ| ≤ |t| + |hquot h a σ| := abs_add_le _ _
      _ ≤ 2 + δ := by linarith
      _ ≤ 3 := by linarith
  have hf1b : |deriv (fun x : ℝ => t + hquot h x σ) a| ≤ δ := by
    rw [congrFun hf_deriv a]; exact hA1
  have hf2b : |iteratedDeriv 2 (fun x : ℝ => t + hquot h x σ) a| ≤ δ := by
    rw [hf2]; exact hA2
  have hg0b : |(σ + a) * t + h σ + h a| ≤ 5 := by
    have hsa : |σ + a| ≤ 2 := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ + a)]; linarith
    have hsum : |h σ + h a| ≤ 2 * δ := by
      have h1' := abs_le.mp (h0 σ); have h2' := abs_le.mp (h0 a)
      rw [abs_le]; constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
    calc |(σ + a) * t + h σ + h a| = |(σ + a) * t + (h σ + h a)| := by ring_nf
      _ ≤ |(σ + a) * t| + |h σ + h a| := abs_add_le _ _
      _ = |σ + a| * |t| + |h σ + h a| := by rw [abs_mul]
      _ ≤ 2 * 2 + 2 * δ := by
          exact add_le_add (mul_le_mul hsa ht2 (abs_nonneg _) (by norm_num)) hsum
      _ ≤ 5 := by linarith
  have hg1b : |deriv (fun x : ℝ => (σ + x) * t + h σ + h x) a| ≤ 3 := by
    rw [hg1]
    calc |t + deriv h a| ≤ |t| + |deriv h a| := abs_add_le _ _
      _ ≤ 2 + δ := by linarith [h1 a]
      _ ≤ 3 := by linarith
  have hg2b : |iteratedDeriv 2 (fun x : ℝ => (σ + x) * t + h σ + h x) a| ≤ δ := by
    rw [hg2]; exact h2 a
  -- the product rule for the second derivative
  have hqc : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => hquot h x σ) :=
    (Work.OddVolterra.Existence.hquot_contDiff hh).comp (contDiff_id.prodMk contDiff_const)
  have hfcd : ContDiffAt ℝ 2 (fun x : ℝ => t + hquot h x σ) a :=
    (contDiff_const.add hqc).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgcd : ContDiffAt ℝ 2 (fun x : ℝ => (σ + x) * t + h σ + h x) a :=
    ((((contDiff_const.add contDiff_id).mul contDiff_const).add contDiff_const).add hh).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hkrad_eq : (fun a' : ℝ => krad h σ t a')
      = (fun x : ℝ => t + hquot h x σ) * (fun x : ℝ => (σ + x) * t + h σ + h x) := by
    funext a'
    rw [krad_apply]
    simp only [Pi.mul_apply, line]
    ring
  have hmul := iteratedDeriv_mul (f := fun x : ℝ => t + hquot h x σ)
    (g := fun x : ℝ => (σ + x) * t + h σ + h x) (n := 2) (x := a) hfcd hgcd
  have h2krad : iteratedDeriv 2 (fun a' : ℝ => krad h σ t a') a
      = (t + hquot h a σ) * iteratedDeriv 2 (fun x : ℝ => (σ + x) * t + h σ + h x) a
        + 2 * deriv (fun x : ℝ => t + hquot h x σ) a
            * deriv (fun x : ℝ => (σ + x) * t + h σ + h x) a
        + iteratedDeriv 2 (fun x : ℝ => t + hquot h x σ) a * ((σ + a) * t + h σ + h a) := by
    rw [hkrad_eq, hmul]
    simp only [Finset.sum_range_succ]
    norm_num
  -- the estimate
  have hbound : |deriv (deriv (fun a' : ℝ => krad h σ t a')) a| ≤ 14 * δ := by
    rw [← kjd2_iteratedDeriv_two, h2krad]
    have hb1 : |(t + hquot h a σ) * iteratedDeriv 2 (fun x : ℝ => (σ + x) * t + h σ + h x) a|
        ≤ 3 * δ := by
      rw [abs_mul]
      exact mul_le_mul hf0b hg2b (abs_nonneg _) (by norm_num)
    have hb2 : |2 * deriv (fun x : ℝ => t + hquot h x σ) a
        * deriv (fun x : ℝ => (σ + x) * t + h σ + h x) a| ≤ 6 * δ := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc 2 * |deriv (fun x : ℝ => t + hquot h x σ) a|
            * |deriv (fun x : ℝ => (σ + x) * t + h σ + h x) a|
          = 2 * (|deriv (fun x : ℝ => t + hquot h x σ) a|
            * |deriv (fun x : ℝ => (σ + x) * t + h σ + h x) a|) := by ring
        _ ≤ 2 * (δ * 3) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hf1b hg1b (abs_nonneg _) hδ0) (by norm_num)
        _ = 6 * δ := by ring
    have hb3 : |iteratedDeriv 2 (fun x : ℝ => t + hquot h x σ) a * ((σ + a) * t + h σ + h a)|
        ≤ δ * 5 := by
      rw [abs_mul]
      exact mul_le_mul hf2b hg0b (abs_nonneg _) hδ0
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
    refine le_trans (add_le_add (add_le_add hb1 hb2) hb3) ?_
    exact le_of_eq (by ring)
  have hder0 : deriv (deriv (fun a' : ℝ => krad 0 σ t a')) a = 0 := by
    have hk0 : (fun a' : ℝ => krad 0 σ t a') = fun a' : ℝ => t ^ 2 * (σ + a') := by
      funext a'
      rw [krad_apply, hquot_zero]
      simp only [line, Pi.zero_apply]
      ring
    rw [hk0]
    have he : (fun a' : ℝ => t ^ 2 * (σ + a')) = fun a' : ℝ => t ^ 2 * a' + t ^ 2 * σ := by
      funext x; ring
    rw [he]
    have hd : deriv (fun x : ℝ => t ^ 2 * x + t ^ 2 * σ) = fun _ : ℝ => t ^ 2 := by
      funext x
      have h := (((hasDerivAt_id x).const_mul (t ^ 2)).add_const (t ^ 2 * σ))
      simpa using h.deriv
    rw [hd]
    simp
  refine ⟨hbound, ?_⟩
  rw [hder0, sub_zero]
  exact hbound

/-! ## The main theorem -/

/-- (`Work.OddVolterra.Window`, module `Submission.Work.OddVolterra.Window.KvecJet_data2`.)
Second-order jet data for the transition window: there is a constant `B ≥ 0` (depending on `n` only)
such that for `σ ∈ [7/10,1]`, `a ∈ [9/20, σ]`, `z 0, z 1 ≥ 1/5`, `|z i| ≤ 2`, `h` smooth with
support in `[1-2τ, 1-τ]` and `|h^(k)| ≤ δ ≤ 1/100` for all `k ≤ n+3`, the jet curve
`u ↦ KJet n h σ z u` (values in the finite-type function space `KJIx n → ℝ`) has value, first and
second `u`-derivative at `a` bounded by `B` (resp. `B*δ` for the difference from the unperturbed
jet of `h = 0`): conjuncts 1 and 2 are the bounds on the first derivative of the perturbed and
unperturbed jet curves, 3 and 4 the closeness of the values and of the first derivatives, and the
last two the bound on the second derivative of the perturbed jet curve and its closeness to that of
the unperturbed one.

Coordinatewise (`KJet` is a Pi-type, so `deriv_deriv_pi` applies with the smoothness of the jet
curve coming from `KvecJet_data`), the entries are `u`, `σ`, `-z 0`, `z 1`,
`krad h σ (-z 0) u`, `krad h σ (z 1) u`, `z 2`, `z 3`, `kjet h σ (-z 0) u k`,
`kjet h σ (z 1) u k` (`k ≤ n+1`) and `iteratedDeriv (j+1) h u` (`j ≤ n`).  The first four conjuncts
already follow from `KvecJet_data` with constant `KJbz n`; the second `u`-derivatives are `0` for
the constant entries, `d² krad` for the two radicand entries (`krad_deriv2_data`, whose hypotheses
`|h^(k)| ≤ δ`, `k ≤ 3`, follow from `k ≤ n+3` since `n ≥ 1`),
`iteratedDeriv (k+2) (Zrad h (·,σ,t))` for the radicand-jet entries (`k+2 ≤ n+3`, bounded resp.
`B*δ`-close to `h = 0` by `Zrad_jet_bounds_gen (n+3)`, using
`kjet h σ t u k = iteratedDeriv k (Zrad h (·,σ,t)) u` and `iteratedDeriv_succ`), and
`iteratedDeriv (j+3) h` for the last block (`j+3 ≤ n+3`).  Take `B` to be larger than the two
constants supplied by `Zrad_jet_bounds_gen (n+3)` and `krad_deriv2_data` and than `KJbz n`. -/
theorem KvecJet_data2 (n : ℕ) (hn : 1 ≤ n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (h : ℝ → ℝ) (δ σ : ℝ) (z : St) (a : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      σ ∈ Set.Icc (7 / 10 : ℝ) 1 →
      1 / 5 ≤ z 0 → 1 / 5 ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
      a ∈ Set.Icc (9 / 20 : ℝ) σ →
      (‖deriv (fun u : ℝ => KJet n h σ z u) a‖ ≤ B ∧
       ‖deriv (fun u : ℝ => KJet n 0 σ z u) a‖ ≤ B ∧
       ‖KJet n h σ z a - KJet n 0 σ z a‖ ≤ B * δ ∧
       ‖deriv (fun u : ℝ => KJet n h σ z u) a - deriv (fun u : ℝ => KJet n 0 σ z u) a‖ ≤ B * δ ∧
       ‖deriv (deriv (fun u : ℝ => KJet n h σ z u)) a‖ ≤ B ∧
       ‖deriv (deriv (fun u : ℝ => KJet n h σ z u)) a -
        deriv (deriv (fun u : ℝ => KJet n 0 σ z u)) a‖ ≤ B * δ) := by
  obtain ⟨Zbz, _, hZbz⟩ := Zrad_jet_bounds_gen (n + 3)
  set B : ℝ := max (KJbz n) (max (max Zbz 1) 14) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]; exact le_trans (KJbz_nonneg n) (le_max_left _ _)
  have hBK : KJbz n ≤ B := by rw [hBdef]; exact le_max_left _ _
  have hBZ : Zbz ≤ B := by
    rw [hBdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hB1 : 1 ≤ B := by
    rw [hBdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hB14 : 14 ≤ B := by
    rw [hBdef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨B, hB0, ?_⟩
  intro h δ σ z a hh hδ0 hδ1 hsupp hjet hσ hz0 hz1 hz ha
  -- basic window data
  have hδ1' : δ ≤ 1 := by linarith
  have hσ1 : 7 / 10 ≤ σ := hσ.1
  have hσ2 : σ ≤ 1 := hσ.2
  have ha1 : 9 / 20 ≤ a := ha.1
  have ha2 : a ≤ σ := ha.2
  have haS : a ∈ Set.Icc (9 / 20 : ℝ) 1 := ⟨ha1, le_trans ha2 hσ2⟩
  have hzt1 : |-(z 0)| ≤ 2 := by rw [abs_neg]; exact hz 0
  have hzt2 : |z 1| ≤ 2 := hz 1
  have hjet3 : ∀ k : ℕ, k ≤ 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ :=
    fun k hk s => hjet k (by omega) s
  have hjet2 : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ :=
    fun k hk s => hjet k (by omega) s
  have hBδ : 0 ≤ B * δ := mul_nonneg hB0 hδ0
  -- the first-order jet data
  obtain ⟨hmem, hcd1, hcd0, hder1, hder0, hclose, hclosed⟩ :=
    KvecJet_data (n := n) (hn := hn) (h := h) (hh := hh) (δ := δ) (σ := σ) (z := z)
      (hδ0 := hδ0) (hδ1 := hδ1) (hsupp := hsupp) (hjet := hjet2) (hσ := hσ)
      (hz0 := hz0) (hz1 := hz1) (hz := hz) (a := a) (ha := ha)
  -- the radicand data and the radicand-jet data
  have hK1 := kjd2_krad_deriv2 h δ σ (-(z 0)) a hh hδ0 hδ1 hjet3 hσ hzt1 ha
  have hK2 := kjd2_krad_deriv2 h δ σ (z 1) a hh hδ0 hδ1 hjet3 hσ hzt2 ha
  have hZg1 := hZbz h δ hh hδ0 hδ1' hjet σ hσ (-(z 0)) hzt1 a haS
  have hZg2 := hZbz h δ hh hδ0 hδ1' hjet σ hσ (z 1) hzt2 a haS
  -- smoothness of the two jet curves and the second-derivative identities
  have h2h : ContDiffAt ℝ 2 (fun u : ℝ => KJet n h σ z u) a :=
    hcd1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have h2z : ContDiffAt ℝ 2 (fun u : ℝ => KJet n 0 σ z u) a :=
    hcd0.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdd1 : deriv (deriv (fun u : ℝ => KJet n h σ z u)) a
      = fun i => deriv (deriv (fun u : ℝ => KJet n h σ z u i)) a := deriv_deriv_pi h2h
  have hdd0 : deriv (deriv (fun u : ℝ => KJet n 0 σ z u)) a
      = fun i => deriv (deriv (fun u : ℝ => KJet n 0 σ z u i)) a := deriv_deriv_pi h2z
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have h01 : ContDiff ℝ 1 (0 : ℝ → ℝ) := contDiff_const
  refine ⟨le_trans hder1 hBK, le_trans hder0 hBK,
    le_trans hclose (mul_le_mul_of_nonneg_right hBK hδ0),
    le_trans hclosed (mul_le_mul_of_nonneg_right hBK hδ0), ?_, ?_⟩
  · rw [hdd1, pi_norm_le_iff_of_nonneg hB0]
    intro i
    rw [Real.norm_eq_abs]
    cases i with
    | aa =>
      show |deriv (deriv (fun u : ℝ => u)) a| ≤ B
      rw [kjd2_deriv2_id]; simpa using hB0
    | sg =>
      show |deriv (deriv (fun _ : ℝ => σ)) a| ≤ B
      rw [kjd2_deriv2_const]; simpa using hB0
    | t1 =>
      show |deriv (deriv (fun _ : ℝ => -(z 0))) a| ≤ B
      rw [kjd2_deriv2_const]; simpa using hB0
    | t2 =>
      show |deriv (deriv (fun _ : ℝ => z 1)) a| ≤ B
      rw [kjd2_deriv2_const]; simpa using hB0
    | kd1 =>
      show |deriv (deriv (fun u : ℝ => krad h σ (-(z 0)) u)) a| ≤ B
      exact le_trans hK1.1 (le_trans (mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ 14) hδ1') hB14)
    | kd2 =>
      show |deriv (deriv (fun u : ℝ => krad h σ (z 1) u)) a| ≤ B
      exact le_trans hK2.1 (le_trans (mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ 14) hδ1') hB14)
    | c2 =>
      show |deriv (deriv (fun _ : ℝ => z 2)) a| ≤ B
      rw [kjd2_deriv2_const]; simpa using hB0
    | c3 =>
      show |deriv (deriv (fun _ : ℝ => z 3)) a| ≤ B
      rw [kjd2_deriv2_const]; simpa using hB0
    | Z1 k =>
      show |deriv (deriv (fun u : ℝ => kjet h σ (-(z 0)) u k.1)) a| ≤ B
      rw [kjd2_deriv2_kjet hh1 σ (-(z 0)) k.1 a]
      exact le_trans (hZg1.1 (k.1 + 2) (by omega)) hBZ
    | Z2 k =>
      show |deriv (deriv (fun u : ℝ => kjet h σ (z 1) u k.1)) a| ≤ B
      rw [kjd2_deriv2_kjet hh1 σ (z 1) k.1 a]
      exact le_trans (hZg2.1 (k.1 + 2) (by omega)) hBZ
    | w j =>
      show |deriv (deriv (fun u : ℝ => iteratedDeriv (j.1 + 1) h u)) a| ≤ B
      rw [kjd2_deriv2_iteratedDeriv h (j.1 + 1) a]
      have hj : |iteratedDeriv (j.1 + 3) h a| ≤ δ :=
        hjet (j.1 + 3) (by have := j.2; omega) a
      have hj' : |iteratedDeriv (j.1 + 1 + 2) h a| ≤ δ := by
        rwa [show j.1 + 1 + 2 = j.1 + 3 from rfl]
      exact le_trans (le_trans hj' hδ1') hB1
  · rw [hdd1, hdd0, pi_norm_le_iff_of_nonneg hBδ]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    cases i with
    | aa =>
      show |deriv (deriv (fun u : ℝ => u)) a - deriv (deriv (fun u : ℝ => u)) a| ≤ B * δ
      rw [sub_self, abs_zero]; exact hBδ
    | sg =>
      show |deriv (deriv (fun _ : ℝ => σ)) a - deriv (deriv (fun _ : ℝ => σ)) a| ≤ B * δ
      rw [sub_self, abs_zero]; exact hBδ
    | t1 =>
      show |deriv (deriv (fun _ : ℝ => -(z 0))) a - deriv (deriv (fun _ : ℝ => -(z 0))) a| ≤ B * δ
      rw [sub_self, abs_zero]; exact hBδ
    | t2 =>
      show |deriv (deriv (fun _ : ℝ => z 1)) a - deriv (deriv (fun _ : ℝ => z 1)) a| ≤ B * δ
      rw [sub_self, abs_zero]; exact hBδ
    | kd1 =>
      show |deriv (deriv (fun u : ℝ => krad h σ (-(z 0)) u)) a -
        deriv (deriv (fun u : ℝ => krad 0 σ (-(z 0)) u)) a| ≤ B * δ
      exact le_trans hK1.2 (mul_le_mul_of_nonneg_right hB14 hδ0)
    | kd2 =>
      show |deriv (deriv (fun u : ℝ => krad h σ (z 1) u)) a -
        deriv (deriv (fun u : ℝ => krad 0 σ (z 1) u)) a| ≤ B * δ
      exact le_trans hK2.2 (mul_le_mul_of_nonneg_right hB14 hδ0)
    | c2 =>
      show |deriv (deriv (fun _ : ℝ => z 2)) a - deriv (deriv (fun _ : ℝ => z 2)) a| ≤ B * δ
      rw [sub_self, abs_zero]; exact hBδ
    | c3 =>
      show |deriv (deriv (fun _ : ℝ => z 3)) a - deriv (deriv (fun _ : ℝ => z 3)) a| ≤ B * δ
      rw [sub_self, abs_zero]; exact hBδ
    | Z1 k =>
      show |deriv (deriv (fun u : ℝ => kjet h σ (-(z 0)) u k.1)) a -
        deriv (deriv (fun u : ℝ => kjet 0 σ (-(z 0)) u k.1)) a| ≤ B * δ
      rw [kjd2_deriv2_kjet hh1 σ (-(z 0)) k.1 a,
        kjd2_deriv2_kjet h01 σ (-(z 0)) k.1 a]
      exact le_trans (hZg1.2 (k.1 + 2) (by omega))
        (mul_le_mul_of_nonneg_right hBZ hδ0)
    | Z2 k =>
      show |deriv (deriv (fun u : ℝ => kjet h σ (z 1) u k.1)) a -
        deriv (deriv (fun u : ℝ => kjet 0 σ (z 1) u k.1)) a| ≤ B * δ
      rw [kjd2_deriv2_kjet hh1 σ (z 1) k.1 a,
        kjd2_deriv2_kjet h01 σ (z 1) k.1 a]
      exact le_trans (hZg2.2 (k.1 + 2) (by omega))
        (mul_le_mul_of_nonneg_right hBZ hδ0)
    | w j =>
      show |deriv (deriv (fun u : ℝ => iteratedDeriv (j.1 + 1) h u)) a -
        deriv (deriv (fun u : ℝ => iteratedDeriv (j.1 + 1) (0 : ℝ → ℝ) u)) a| ≤ B * δ
      rw [kjd2_deriv2_iteratedDeriv h (j.1 + 1) a,
        kjd2_deriv2_iteratedDeriv (0 : ℝ → ℝ) (j.1 + 1) a,
        kjd2_iteratedDeriv_zero (j.1 + 1 + 2) a, sub_zero]
      have hj : |iteratedDeriv (j.1 + 3) h a| ≤ δ :=
        hjet (j.1 + 3) (by have := j.2; omega) a
      have hj' : |iteratedDeriv (j.1 + 1 + 2) h a| ≤ δ := by
        rwa [show j.1 + 1 + 2 = j.1 + 3 from rfl]
      calc |iteratedDeriv (j.1 + 1 + 2) h a| ≤ δ := hj'
        _ = 1 * δ := by ring
        _ ≤ B * δ := mul_le_mul_of_nonneg_right hB1 hδ0

end

end Work.OddVolterra.Window
