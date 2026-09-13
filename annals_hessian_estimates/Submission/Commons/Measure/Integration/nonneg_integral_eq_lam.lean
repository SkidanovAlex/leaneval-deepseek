import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.CompletePartialOrder

/-!
# `Λ` agrees with the integral on nonnegative admissible smooth functions

Let `X` be a finite-dimensional inner product space, `s ⊆ X` a set, `μ` a measure on `X` and
`Λ : (X → ℝ) → ℝ` a functional satisfying

* `Λ` is additive and positively homogeneous on smooth functions whose (topological) support is
  contained in `s`;
* `Λ` is nonnegative on nonnegative such functions;
* `Λ f = ∫ f ∂μ` for every *compactly supported* smooth `f` with `tsupport f ⊆ s`.

The main result, `Commons.Measure.Integration.nonneg_integral_eq_lam`, shows that then
`∫ Φ ∂μ = Λ Φ` for *every* nonnegative smooth `Φ` with `tsupport Φ ⊆ s`, no compactness of the
support being assumed.

The proof has two halves.

* *Lower bound* (`lintegral_ofReal_le` / `integral_le_Lam`): for nonnegative admissible `ψ` the
  functions `ψ * cut n` (with `cut n` a smooth cutoff equal to `1` on the ball of radius `n+1`
  and compactly supported) increase to `ψ`, so monotone convergence together with the
  hypothesis `hCc` on compactly supported functions gives `∫⁻ ofReal ψ ≤ ofReal (Λ ψ)` and
  hence `∫ ψ ≤ Λ ψ`.  In particular `ψ` is integrable whenever `Λ ψ < ∞`.

* *Upper bound* (`le_integral_of_nonneg`): the "growth trick".  Compare `ψ` with the weighted
  function `Ψ = ψ * ‖x‖²` (still admissible and nonnegative).  Cutting `ψ = ψ * cut n +
  ψ * (1 - cut n)` and using `hCc` for the compactly supported piece shows
  `Λ ψ - ∫ ψ = Λ (ψ (1-cut n)) - ∫ ψ (1-cut n)`, while on the support of `1 - cut n` one has
  `‖x‖² > (n+1)²`.  Applying monotonicity of `Λ` to the pointwise inequality
  `(n+1)² * ψ (1 - cut n) ≤ Ψ (1 - cut n)` yields `(n+1)² * (Λ ψ - ∫ ψ) ≤ Λ Ψ` for all `n`, so
  the difference `Λ ψ - ∫ ψ` must vanish.  Consequently `Λ ψ ≤ ∫ ψ`, and the equality follows.
-/

namespace Commons.Measure.Integration

open MeasureTheory Metric Set Filter Function
open scoped ContDiff ENNReal Topology

section Cut

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The smooth cutoff `x ↦ 1 - s (‖x‖²/(n+1)² - 1)`, where `s` is `Real.smoothTransition`.  It
equals `1` on the ball of radius `n + 1` about the origin and vanishes outside the ball of
radius `2 * (n + 1)`. -/
private noncomputable def cut (n : ℕ) : X → ℝ :=
  fun x => 1 - Real.smoothTransition (‖x‖ ^ 2 / ((n : ℝ) + 1) ^ 2 - 1)

private lemma cut_smooth (n : ℕ) : ContDiff ℝ ∞ (cut (X := X) n) := by
  unfold cut
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((contDiff_norm_sq ℝ).div_const (((n : ℝ) + 1) ^ 2)).sub contDiff_const))

private lemma cut_nonneg (n : ℕ) (x : X) : 0 ≤ cut (X := X) n x := by
  have h := Real.smoothTransition.le_one (‖x‖ ^ 2 / ((n : ℝ) + 1) ^ 2 - 1)
  unfold cut
  linarith

private lemma cut_le_one (n : ℕ) (x : X) : cut (X := X) n x ≤ 1 := by
  have h := Real.smoothTransition.nonneg (‖x‖ ^ 2 / ((n : ℝ) + 1) ^ 2 - 1)
  unfold cut
  linarith

private lemma cut_eq_one (n : ℕ) {x : X} (h : ‖x‖ ≤ (n : ℝ) + 1) : cut (X := X) n x = 1 := by
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have h1 : ‖x‖ ^ 2 / ((n : ℝ) + 1) ^ 2 - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hpos]
    nlinarith [norm_nonneg x, h]
  unfold cut
  rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero]

private lemma cut_eq_zero (n : ℕ) {x : X} (h : 2 * ((n : ℝ) + 1) ^ 2 ≤ ‖x‖ ^ 2) :
    cut (X := X) n x = 0 := by
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have h1 : 1 ≤ ‖x‖ ^ 2 / ((n : ℝ) + 1) ^ 2 - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hpos]
    linarith
  unfold cut
  rw [Real.smoothTransition.one_of_one_le h1, sub_self]

private lemma norm_sq_gt_of_cut_ne_one (n : ℕ) {x : X} (h : cut (X := X) n x ≠ 1) :
    ((n : ℝ) + 1) ^ 2 < ‖x‖ ^ 2 := by
  by_contra hcon
  push_neg at hcon
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have h1 : ‖x‖ ^ 2 / ((n : ℝ) + 1) ^ 2 - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hpos]
    exact hcon
  have hone : cut (X := X) n x = 1 := by
    unfold cut
    rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero]
  exact h hone

private lemma cut_tsupport_subset (n : ℕ) :
    tsupport (cut (X := X) n) ⊆ closedBall (0 : X) (2 * ((n : ℝ) + 1)) := by
  apply closure_minimal _ (isClosed_closedBall)
  intro x hx
  rw [Function.mem_support] at hx
  rw [mem_closedBall, dist_zero_right]
  by_contra hcon
  push_neg at hcon
  refine hx (cut_eq_zero n ?_)
  have hB : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h1 : 2 * ((n : ℝ) + 1) * ((n : ℝ) + 1) ≤ ‖x‖ * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hcon.le hB
  have h2 : ‖x‖ * ((n : ℝ) + 1) ≤ ‖x‖ * ‖x‖ :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg x)
  nlinarith [h1, h2]

private lemma cut_hasCompactSupport [FiniteDimensional ℝ X] (n : ℕ) :
    HasCompactSupport (cut (X := X) n) :=
  (isCompact_closedBall (0 : X) (2 * ((n : ℝ) + 1))).of_isClosed_subset
    (isClosed_tsupport _) (cut_tsupport_subset n)

private lemma cut_mono (x : X) : Monotone (fun n => cut (X := X) n x) := by
  intro a b hab
  have ha : (0 : ℝ) < ((a : ℝ) + 1) ^ 2 := by positivity
  have hb : (0 : ℝ) < ((b : ℝ) + 1) ^ 2 := by positivity
  have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have h2 : ((a : ℝ) + 1) ^ 2 ≤ ((b : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h3 : ‖x‖ ^ 2 / ((b : ℝ) + 1) ^ 2 ≤ ‖x‖ ^ 2 / ((a : ℝ) + 1) ^ 2 := by
    rw [div_le_div_iff₀ hb ha]
    nlinarith [sq_nonneg ‖x‖, h2]
  have h4 : Real.smoothTransition (‖x‖ ^ 2 / ((b : ℝ) + 1) ^ 2 - 1)
      ≤ Real.smoothTransition (‖x‖ ^ 2 / ((a : ℝ) + 1) ^ 2 - 1) :=
    Real.smoothTransition.monotone (by linarith)
  unfold cut
  linarith

private lemma cut_tendsto (x : X) : Tendsto (fun n => cut (X := X) n x) atTop (𝓝 1) := by
  refine Tendsto.congr' ?_ (tendsto_const_nhds)
  filter_upwards [eventually_ge_atTop (Nat.ceil ‖x‖)] with n hn
  exact (cut_eq_one n (by
    have h1 : (Nat.ceil ‖x‖ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : ‖x‖ ≤ (Nat.ceil ‖x‖ : ℝ) := Nat.le_ceil ‖x‖
    linarith)).symm

end Cut

section Main

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  {s : Set X} {Λ : (X → ℝ) → ℝ} {μ : Measure X}

private lemma smul_eq_mul_fun (c : ℝ) (f : X → ℝ) : (c • f : X → ℝ) = fun x => c * f x := by
  ext x
  rw [Pi.smul_apply, smul_eq_mul]

private lemma tsupport_const_mul_subset (c : ℝ) (f : X → ℝ) :
    tsupport (fun x => c * f x) ⊆ tsupport f := by
  apply closure_mono
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h
  exact hx (by rw [h, mul_zero])

/-- Monotonicity of `Λ` on admissible smooth functions: if both functions are smooth with support
in `s` and `f ≤ g` pointwise, then `Λ f ≤ Λ g`. -/
private lemma Lam_mono
    (hadd : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ContDiff ℝ ∞ ψ → tsupport ψ ⊆ s →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hpos : ∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → 0 ≤ φ → 0 ≤ Λ φ)
    {f g : X → ℝ} (hf : ContDiff ℝ ∞ f) (hfs : tsupport f ⊆ s)
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ s) (hle : f ≤ g) : Λ f ≤ Λ g := by
  have hdf : ContDiff ℝ ∞ (g - f) := hg.sub hf
  have hdfs : tsupport (g - f) ⊆ s := (tsupport_sub g f).trans (union_subset hgs hfs)
  have hnn : 0 ≤ g - f := fun x => sub_nonneg.mpr (hle x)
  have h0 : 0 ≤ Λ (g - f) := hpos _ hdf hdfs hnn
  have key : Λ g = Λ f + Λ (g - f) := by
    have h : f + (g - f) = g := by ext x; simp
    rw [← hadd f (g - f) hf hfs hdf hdfs, h]
  linarith

/-- The measure theoretic integral of a nonnegative admissible smooth function is bounded by
`Λ` applied to it. -/
private lemma lintegral_ofReal_le
    (hadd : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ContDiff ℝ ∞ ψ → tsupport ψ ⊆ s →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hpos : ∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → 0 ≤ φ → 0 ≤ Λ φ)
    (hint : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s →
      Integrable f μ)
    (hCc : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s →
      ∫ x, f x ∂μ = Λ f)
    {ψ : X → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ s) (hψnn : 0 ≤ ψ) :
    ∫⁻ x, ENNReal.ofReal (ψ x) ∂μ ≤ ENNReal.ofReal (Λ ψ) := by
  have hGs : ∀ n, ContDiff ℝ ∞ (fun x => ψ x * cut (X := X) n x) :=
    fun n => hψ.mul (cut_smooth n)
  have hGnn : ∀ n, 0 ≤ fun x => ψ x * cut (X := X) n x :=
    fun n x => mul_nonneg (hψnn x) (cut_nonneg n x)
  have hGc : ∀ n, HasCompactSupport (fun x => ψ x * cut (X := X) n x) := fun n =>
    (cut_hasCompactSupport n).mono'
      ((support_mul_subset_right ψ (cut (X := X) n)).trans subset_closure)
  have hGsupp : ∀ n, tsupport (fun x => ψ x * cut (X := X) n x) ⊆ s := fun n =>
    (tsupport_mul_subset_left (f := ψ) (g := cut (X := X) n)).trans hψs
  have hGint : ∀ n, Integrable (fun x => ψ x * cut (X := X) n x) μ := fun n =>
    hint _ (hGs n) (hGc n) (hGsupp n)
  have hGval : ∀ n, ∫ x, ψ x * cut (X := X) n x ∂μ
      = Λ (fun x => ψ x * cut (X := X) n x) := fun n => hCc _ (hGs n) (hGc n) (hGsupp n)
  have hGle : ∀ n, Λ (fun x => ψ x * cut (X := X) n x) ≤ Λ ψ := fun n =>
    Lam_mono hadd hpos (hGs n) (hGsupp n) hψ hψs
      (fun x => mul_le_of_le_one_right (hψnn x) (cut_le_one n x))
  have hmeas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (ψ x * cut (X := X) n x)) μ :=
    fun n => ((hGs n).continuous.measurable.ennreal_ofReal).aemeasurable
  have hmono : ∀ᵐ x ∂μ, Monotone (fun n => ENNReal.ofReal (ψ x * cut (X := X) n x)) :=
    Eventually.of_forall fun x => monotone_nat_of_le_succ fun n =>
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (cut_mono x n.le_succ) (hψnn x))
  have htend : ∀ᵐ x ∂μ,
      Tendsto (fun n => ENNReal.ofReal (ψ x * cut (X := X) n x)) atTop
        (𝓝 (ENNReal.ofReal (ψ x))) :=
    Eventually.of_forall fun x => ENNReal.tendsto_ofReal (by
      have h := (cut_tendsto x).mul_const (ψ x)
      simpa only [one_mul, mul_comm (cut (X := X) _ x) (ψ x)] using h)
  have hMCT := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htend
  refine le_of_tendsto hMCT (Eventually.of_forall fun n => ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal (hGint n) (Eventually.of_forall (hGnn n))]
  exact ENNReal.ofReal_le_ofReal (le_trans (le_of_eq (hGval n)) (hGle n))

/-- Integrability of any nonnegative admissible smooth function. -/
private lemma integrable_of_nonneg
    (hadd : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ContDiff ℝ ∞ ψ → tsupport ψ ⊆ s →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hpos : ∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → 0 ≤ φ → 0 ≤ Λ φ)
    (hint : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s →
      Integrable f μ)
    (hCc : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s →
      ∫ x, f x ∂μ = Λ f)
    {f : X → ℝ} (hf : ContDiff ℝ ∞ f) (hfs : tsupport f ⊆ s) (hfn : 0 ≤ f) :
    Integrable f μ := by
  refine ⟨hf.continuous.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have heq : (fun x => ‖f x‖ₑ) = fun x => ENNReal.ofReal (f x) := by
    funext x
    exact Real.enorm_eq_ofReal (hfn x)
  rw [heq]
  exact lt_of_le_of_lt (lintegral_ofReal_le hadd hpos hint hCc hf hfs hfn)
    ENNReal.ofReal_lt_top

/-- The (Bochner) integral of a nonnegative admissible smooth function is bounded by `Λ`. -/
private lemma integral_le_Lam
    (hadd : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ContDiff ℝ ∞ ψ → tsupport ψ ⊆ s →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hpos : ∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → 0 ≤ φ → 0 ≤ Λ φ)
    (hint : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s →
      Integrable f μ)
    (hCc : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s →
      ∫ x, f x ∂μ = Λ f)
    {f : X → ℝ} (hf : ContDiff ℝ ∞ f) (hfs : tsupport f ⊆ s) (hfn : 0 ≤ f) :
    ∫ x, f x ∂μ ≤ Λ f := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hfn)
    hf.continuous.aestronglyMeasurable]
  calc (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal
      ≤ (ENNReal.ofReal (Λ f)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (lintegral_ofReal_le hadd hpos hint hCc hf hfs hfn)
    _ = Λ f := ENNReal.toReal_ofReal (hpos f hf hfs hfn)

/-- **The growth trick.**  For a nonnegative admissible smooth function `ψ` one has
`Λ ψ ≤ ∫ ψ ∂μ`.  The proof compares `ψ` with the weighted function `ψ * ‖x‖²`; outside the ball
of radius `n + 1` the weight is larger than `(n + 1)²`, which bounds `Λ ψ - ∫ ψ` uniformly in `n`
by `Λ (ψ * ‖x‖²)`. -/
private lemma le_integral_of_nonneg
    (hadd : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ContDiff ℝ ∞ ψ → tsupport ψ ⊆ s →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hsmul : ∀ (a : ℝ) φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → Λ (a • φ) = a * Λ φ)
    (hpos : ∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → 0 ≤ φ → 0 ≤ Λ φ)
    (hint : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s →
      Integrable f μ)
    (hCc : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s →
      ∫ x, f x ∂μ = Λ f)
    {ψ : X → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ s) (hψnn : 0 ≤ ψ) :
    Λ ψ ≤ ∫ x, ψ x ∂μ := by
  set Ψ : X → ℝ := fun x => ψ x * ‖x‖ ^ 2 with hΨ
  have hΨsmooth : ContDiff ℝ ∞ Ψ := hψ.mul (contDiff_norm_sq ℝ)
  have hΨs : tsupport Ψ ⊆ s :=
    (tsupport_mul_subset_left (f := ψ) (g := fun x : X => ‖x‖ ^ 2)).trans hψs
  have hΨnn : 0 ≤ Ψ := fun x => mul_nonneg (hψnn x) (by positivity)
  have hΨint : Integrable Ψ μ :=
    integrable_of_nonneg hadd hpos hint hCc hΨsmooth hΨs hΨnn
  have key : ∀ n : ℕ, ((n : ℝ) + 1) ^ 2 * (Λ ψ - ∫ x, ψ x ∂μ) ≤ Λ Ψ := by
    intro n
    set c : ℝ := ((n : ℝ) + 1) ^ 2 with hc
    have hg_smooth : ContDiff ℝ ∞ (fun x => ψ x * (1 - cut (X := X) n x)) :=
      hψ.mul (contDiff_const.sub (cut_smooth n))
    have hg_s : tsupport (fun x => ψ x * (1 - cut (X := X) n x)) ⊆ s :=
      (tsupport_mul_subset_left (f := ψ) (g := fun x => 1 - cut (X := X) n x)).trans hψs
    have hg_nn : 0 ≤ fun x => ψ x * (1 - cut (X := X) n x) := fun x =>
      mul_nonneg (hψnn x) (by linarith [cut_le_one n x])
    have hg_int : Integrable (fun x => ψ x * (1 - cut (X := X) n x)) μ :=
      integrable_of_nonneg hadd hpos hint hCc hg_smooth hg_s hg_nn
    have hh_smooth : ContDiff ℝ ∞ (fun x => ψ x * cut (X := X) n x) := hψ.mul (cut_smooth n)
    have hh_c : HasCompactSupport (fun x => ψ x * cut (X := X) n x) :=
      (cut_hasCompactSupport n).mono'
        ((support_mul_subset_right ψ (cut (X := X) n)).trans subset_closure)
    have hh_s : tsupport (fun x => ψ x * cut (X := X) n x) ⊆ s :=
      (tsupport_mul_subset_left (f := ψ) (g := cut (X := X) n)).trans hψs
    have hh_int : Integrable (fun x => ψ x * cut (X := X) n x) μ :=
      hint _ hh_smooth hh_c hh_s
    have hsplit : ψ = (fun x => ψ x * (1 - cut (X := X) n x))
        + (fun x => ψ x * cut (X := X) n x) := by
      funext x
      simp only [Pi.add_apply]
      ring
    have hΛψ : Λ ψ = Λ (fun x => ψ x * (1 - cut (X := X) n x))
        + ∫ x, ψ x * cut (X := X) n x ∂μ := by
      conv_lhs => rw [hsplit]
      rw [hadd _ _ hg_smooth hg_s hh_smooth hh_s, hCc _ hh_smooth hh_c hh_s]
    have hIntψ : ∫ x, ψ x ∂μ = ∫ x, ψ x * (1 - cut (X := X) n x) ∂μ
        + ∫ x, ψ x * cut (X := X) n x ∂μ := by
      conv_lhs => rw [hsplit]
      simp only [Pi.add_apply]
      exact integral_add hg_int hh_int
    have hd : Λ ψ - ∫ x, ψ x ∂μ
        = Λ (fun x => ψ x * (1 - cut (X := X) n x))
          - ∫ x, ψ x * (1 - cut (X := X) n x) ∂μ := by
      rw [hΛψ, hIntψ]; ring
    have hle : (fun x => c * (ψ x * (1 - cut (X := X) n x)))
        ≤ (fun x => Ψ x * (1 - cut (X := X) n x)) := by
      intro x
      simp only [hΨ]
      rcases eq_or_lt_of_le (hψnn x) with hψ0 | hψpos
      · rw [← hψ0]; simp
      · by_cases hc1 : 1 - cut (X := X) n x = 0
        · rw [hc1]
          simp
        · have hc1pos : 0 < 1 - cut (X := X) n x :=
            lt_of_le_of_ne (by linarith [cut_le_one n x]) (Ne.symm hc1)
          have hcut_ne : cut (X := X) n x ≠ 1 := by
            intro hh
            exact hc1 (by rw [hh]; ring)
          have hc_le : c ≤ ‖x‖ ^ 2 := by
            have hgt := norm_sq_gt_of_cut_ne_one n hcut_ne
            rw [hc]
            linarith
          have hmul := mul_le_mul_of_nonneg_right hc_le (mul_nonneg hψpos.le hc1pos.le)
          calc c * (ψ x * (1 - cut (X := X) n x))
              ≤ ‖x‖ ^ 2 * (ψ x * (1 - cut (X := X) n x)) := hmul
            _ = ψ x * ‖x‖ ^ 2 * (1 - cut (X := X) n x) := by ring
    have hcs : ContDiff ℝ ∞ (fun x => c * (ψ x * (1 - cut (X := X) n x))) :=
      contDiff_const.mul hg_smooth
    have hcss : tsupport (fun x => c * (ψ x * (1 - cut (X := X) n x))) ⊆ s :=
      (tsupport_const_mul_subset c _).trans hg_s
    have hws : ContDiff ℝ ∞ (fun x => Ψ x * (1 - cut (X := X) n x)) :=
      hΨsmooth.mul (contDiff_const.sub (cut_smooth n))
    have hwss : tsupport (fun x => Ψ x * (1 - cut (X := X) n x)) ⊆ s :=
      (tsupport_mul_subset_left (f := Ψ) (g := fun x => 1 - cut (X := X) n x)).trans hΨs
    have hmono : Λ (fun x => c * (ψ x * (1 - cut (X := X) n x)))
        ≤ Λ (fun x => Ψ x * (1 - cut (X := X) n x)) :=
      Lam_mono hadd hpos hcs hcss hws hwss hle
    have hΛc : Λ (fun x => c * (ψ x * (1 - cut (X := X) n x)))
        = c * Λ (fun x => ψ x * (1 - cut (X := X) n x)) := by
      have h1 := hsmul c _ hg_smooth hg_s
      rwa [smul_eq_mul_fun] at h1
    have hwc_smooth : ContDiff ℝ ∞ (fun x => Ψ x * cut (X := X) n x) :=
      hΨsmooth.mul (cut_smooth n)
    have hwc_c : HasCompactSupport (fun x => Ψ x * cut (X := X) n x) :=
      (cut_hasCompactSupport n).mono'
        ((support_mul_subset_right Ψ (cut (X := X) n)).trans subset_closure)
    have hwc_s : tsupport (fun x => Ψ x * cut (X := X) n x) ⊆ s :=
      (tsupport_mul_subset_left (f := Ψ) (g := cut (X := X) n)).trans hΨs
    have hΨsplit : Ψ = (fun x => Ψ x * (1 - cut (X := X) n x))
        + (fun x => Ψ x * cut (X := X) n x) := by
      funext x
      simp only [Pi.add_apply]
      ring
    have hΛΨ : Λ Ψ = Λ (fun x => Ψ x * (1 - cut (X := X) n x))
        + ∫ x, Ψ x * cut (X := X) n x ∂μ := by
      conv_lhs => rw [hΨsplit]
      rw [hadd _ _ hws hwss hwc_smooth hwc_s, hCc _ hwc_smooth hwc_c hwc_s]
    have htail_nn : 0 ≤ ∫ x, Ψ x * cut (X := X) n x ∂μ :=
      integral_nonneg (fun x => mul_nonneg (hΨnn x) (cut_nonneg n x))
    have hleΨ : Λ (fun x => Ψ x * (1 - cut (X := X) n x)) ≤ Λ Ψ := by linarith
    have hcΛg : c * Λ (fun x => ψ x * (1 - cut (X := X) n x)) ≤ Λ Ψ := by
      rw [← hΛc]
      exact le_trans hmono hleΨ
    have hcint : c * ∫ x, ψ x * (1 - cut (X := X) n x) ∂μ
        = ∫ x, c * (ψ x * (1 - cut (X := X) n x)) ∂μ := (integral_const_mul c _).symm
    have hnn_int : 0 ≤ ∫ x, c * (ψ x * (1 - cut (X := X) n x)) ∂μ :=
      integral_nonneg (fun x => mul_nonneg (by positivity) (hg_nn x))
    rw [hd]
    nlinarith [hcΛg, hcint, hnn_int]
  by_contra hcon
  push_neg at hcon
  set d : ℝ := Λ ψ - ∫ x, ψ x ∂μ with hd_def
  have hdpos : 0 < d := by rw [hd_def]; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (Λ Ψ / d)
  have hkeyd := key N
  have h2 : Λ Ψ < ((N : ℝ) + 1) ^ 2 * d := by
    have hNd : Λ Ψ < (N : ℝ) * d := (div_lt_iff₀ hdpos).mp hN
    have hle : (N : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      nlinarith [hN0]
    nlinarith [hNd, hle, hdpos.le]
  linarith

end Main

open MeasureTheory Metric Set Filter Function in
open scoped ContDiff ENNReal Topology in
theorem nonneg_integral_eq_lam
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] {s : Set X} {Λ : (X → ℝ) → ℝ} {μ : Measure X}
    (hint : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s → Integrable f μ)
    (hadd : ∀ φ ψ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → ContDiff ℝ ∞ ψ → tsupport ψ ⊆ s →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hsmul : ∀ (a : ℝ) φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → Λ (a • φ) = a * Λ φ)
    (hpos : ∀ φ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s → 0 ≤ φ → 0 ≤ Λ φ)
    (hCc : ∀ f : X → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ s →
      ∫ x, f x ∂μ = Λ f)
    {Φ : X → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hsub : tsupport Φ ⊆ s) (hΦ0 : 0 ≤ Φ) :
    ∫ x, Φ x ∂μ = Λ Φ :=
  le_antisymm (integral_le_Lam hadd hpos hint hCc hΦ hsub hΦ0)
    (le_integral_of_nonneg hadd hsmul hpos hint hCc hΦ hsub hΦ0)

end Commons.Measure.Integration