import Mathlib
import Submission.Vinogradov.Decoupling
import Submission.Commons.Analysis.Integral.interval_avg_tendsto
import Submission.Commons.Analysis.Integral.intervalIntegral_indicator_Ioo
import Submission.Commons.Analysis.Integral.intervalIntegrable_indicator_mul_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory Complex
open scoped Real BigOperators Interval
open LeanEval.NumberTheory.VinogradovMeanValue

set_option autoImplicit false

namespace Submission.Vinogradov

noncomputable section
open Classical

/-!
# The extension operator of the moment curve (decoupling input)

This module fixes the operator-theoretic vocabulary of BDG's ℓ²-decoupling
theorem for the moment curve (BDG, Ann. Math. 184 (2016), Thm 1.2):

    E_J g(x) = ∫_J g(t) · e(x·γ(t)) dt ,    γ(t) = (t, t², …, tᵏ),

`x ∈ E k = ℝᵏ`, `J` an interval in `ℝ`, `g : ℝ → ℂ`.  The eventual role of
this module (with `Decoupling.lean`, which already contains the ball-weight /
norm infrastructure `wLpPowAvg`, `ballWeight`, `bdg_discrete_restriction`,
…) is to prove the critical discrete restriction bound `bdg_critical` from
the decoupling theorem: applying decoupling to the family of step functions
`g_τ = Σᵢ aᵢ/(2τ)·1_{(tᵢ−τ,tᵢ+τ)}` and passing to the limit `τ → 0⁺` turns
`E_{[0,1]} g_τ` into the separated character sum `Σᵢ aᵢ e(x·γ(tᵢ))`
(=`sepCharSum k a t x`), exactly BDG's proof of their discrete restriction
theorem in §"From decouplings to exponential sums".

Nothing in this module is imported by the main chain yet; it is a standalone
foundation.  All lemmas below are proved (no sorries).

Contents (second half of the module): the **step-function discretisation
family** `g_τ = Σᵢ (aᵢ/(2τ))·1_{(tᵢ−τ,tᵢ+τ)}` and its extension values
`extOpChar k a t τ x` (the finite sum of per-bump interval integrals of
`momChar`), with three proved facts that engine the `τ → 0⁺` passage of BDG's
"From decouplings to exponential sums" argument:

* `extOpChar_tendsto_sepCharSum` — pointwise in `x`, as `τ → 0⁺`, the
  extension values converge to the separated character sum `sepCharSum`;
* `extOpChar_norm_le` — domination `‖E g_τ(x)‖ ≤ Σᵢ‖aᵢ‖`, uniform in `x`
  and `τ`;
* `wLpPow_tendsto_extOpChar` / `wLpPow_tendsto_extOpChar'` — the weighted
  `L^p` limit `wLpPow p (E g_τ) → wLpPow p (sepCharSum)` against any ball
  weight `w_B`, by dominated convergence (natural exponent; the real-exponent
  form follows by `wLpPow_natCast`), and its `wLpPowAvg`-normalised form
  `wLpPowAvg_tendsto_extOpChar` (the normalisation in which `bdg_critical` is
  stated);
* `extOp_charStep_eq_extOpChar` — for `τ` small enough that every bump
  `(tᵢ−τ,tᵢ+τ)` lies in `(0,1)`, the interval extension over `[0,1]` equals
  the whole-line per-bump sum; hence the interval-form pointwise limit
  `extOp_charStep_tendsto_sepCharSum` (points strictly inside `(0,1)`;
  boundary points split across cells and are handled separately in the
  eventual derivation).
-/

/-- The real phase `x·γ(t) = Σⱼ xⱼ t^{j+1}` of the moment-curve character. -/
noncomputable def momPhase (k : ℕ) (x : E k) (t : ℝ) : ℝ :=
  ∑ j : Fin k, x j * t ^ (j.val + 1)

/-- The phase is continuous in the curve parameter `t`. -/
lemma momPhase_continuous (k : ℕ) (x : E k) : Continuous (fun t : ℝ => momPhase k x t) := by
  unfold momPhase
  fun_prop

/-- `momChar` is the complex exponential of `2πi` times the phase. -/
lemma momChar_eq_exp (k : ℕ) (x : E k) (t : ℝ) :
    momChar k x t = Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((momPhase k x t : ℝ) : ℂ)) := by
  simp [momChar, momPhase]

/-- The moment-curve character is continuous in the curve parameter `t`. -/
lemma momChar_continuous_t (k : ℕ) (x : E k) : Continuous (fun t : ℝ => momChar k x t) := by
  unfold momChar
  fun_prop

/-- The extension operator `E_J g(x) = ∫_J g(t)·e(x·γ(t)) dt` over the real
interval `J = [a, b]` (Lebesgue integral on the `t`-line). -/
noncomputable def extOp (k : ℕ) (g : ℝ → ℂ) (a b : ℝ) (x : E k) : ℂ :=
  intervalIntegral (fun t : ℝ => g t * momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ)

/-- Pointwise bound on `E_J g`: `‖E_J g(x)‖ ≤ ∫_J ‖g(t)‖ dt` for `a ≤ b`. -/
lemma extOp_norm_le (k : ℕ) (g : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) (x : E k) :
    ‖extOp k g a b x‖ ≤ intervalIntegral (fun t : ℝ => ‖g t‖) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  unfold extOp
  calc
    ‖intervalIntegral (fun t : ℝ => g t * momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖
        ≤ intervalIntegral (fun t : ℝ => ‖g t * momChar k x t‖) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
          intervalIntegral.norm_integral_le_integral_norm hab
    _ = intervalIntegral (fun t : ℝ => ‖g t‖) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          change ‖g t * momChar k x t‖ = ‖g t‖
          rw [norm_mul, momChar_norm_one, mul_one]

/-- Additivity of the extension operator over adjacent intervals:
`E_{[a,c]} = E_{[a,b]} + E_{[b,c]}`. -/
lemma extOp_add_adjacent (k : ℕ) (g : ℝ → ℂ) {a b c : ℝ} (x : E k)
    (hab : IntervalIntegrable (fun t : ℝ => g t * momChar k x t)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b)
    (hbc : IntervalIntegrable (fun t : ℝ => g t * momChar k x t)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) b c) :
    extOp k g a c x = extOp k g a b x + extOp k g b c x := by
  unfold extOp
  exact (intervalIntegral.integral_add_adjacent_intervals hab hbc).symm

/-- The extension operator is linear in the source function: constant factors
pull out of the integral. -/
lemma extOp_const_mul (k : ℕ) (g : ℝ → ℂ) (c : ℂ) (a b : ℝ) (x : E k) :
    extOp k (fun t : ℝ => c * g t) a b x = c * extOp k g a b x := by
  unfold extOp
  simp_rw [mul_assoc]
  calc
    intervalIntegral (fun t : ℝ => c * (g t * momChar k x t)) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        = intervalIntegral (fun t : ℝ => (g t * momChar k x t) * c) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          ring
    _ = (intervalIntegral (fun t : ℝ => g t * momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ)) * c :=
          intervalIntegral.integral_mul_const c (fun t : ℝ => g t * momChar k x t)
    _ = c * intervalIntegral (fun t : ℝ => g t * momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          ring

/-- `E_J` of a constant function: `E_J c (x) = c · ∫_J e(x·γ(t)) dt`. -/
lemma extOp_const_char (k : ℕ) (c : ℂ) (a b : ℝ) (x : E k) :
    extOp k (fun _ : ℝ => c) a b x =
      c * intervalIntegral (fun t : ℝ => momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  unfold extOp
  calc
    intervalIntegral (fun t : ℝ => c * momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        = intervalIntegral (fun t : ℝ => momChar k x t * c) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          ring
    _ = (intervalIntegral (fun t : ℝ => momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ)) * c :=
          intervalIntegral.integral_mul_const c (fun t : ℝ => momChar k x t)
    _ = c * intervalIntegral (fun t : ℝ => momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          ring


/-- The moment-curve character is continuous in the extension variable `x`
(at a fixed curve parameter `t`). -/
lemma momChar_continuous_x (k : ℕ) (t : ℝ) : Continuous (fun x : E k => momChar k x t) := by
  unfold momChar
  fun_prop

/-- `x ↦ ∫_{t ∈ [a,b]} e(x·γ(t)) dt` is continuous in the extension variable
`x` (the parameter integral is controlled by the constant bound `1`, so
dominated convergence applies). -/
lemma momChar_Icc_integral_continuous (k : ℕ) (a b : ℝ) :
    Continuous (fun x : E k => ∫ t in Set.Icc a b, momChar k x t) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc a b)
  have hInt := MeasureTheory.continuousAt_of_dominated (μ := μ) (G := ℂ) (X := E k) (x₀ := x₀)
    (F := fun x : E k => fun t : ℝ => momChar k x t) (bound := fun _ : ℝ => (1 : ℝ))
  have hmeas : ∀ᶠ x : E k in nhds x₀, AEStronglyMeasurable (fun t : ℝ => momChar k x t) μ := by
    filter_upwards with x
    exact Continuous.aestronglyMeasurable (momChar_continuous_t k x)
  have hbound : ∀ᶠ x : E k in nhds x₀, ∀ᵐ t ∂μ, ‖momChar k x t‖ ≤ (1 : ℝ) := by
    filter_upwards with x
    filter_upwards with t
    rw [momChar_norm_one]
  have hvol : (volume : Measure ℝ) (Set.Icc a b) ≠ ⊤ :=
    (measure_Icc_lt_top (μ := (volume : Measure ℝ))).ne
  have hbint : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by
    dsimp [μ]
    exact (integrableOn_const (s := Set.Icc a b) (μ := (volume : Measure ℝ)) (C := (1 : ℝ)) hvol).integrable
  have hcont : ∀ᵐ t ∂μ, ContinuousAt (fun x : E k => momChar k x t) x₀ := by
    filter_upwards with t
    exact (momChar_continuous_x k t).continuousAt
  have hc := hInt hmeas hbound hbint hcont
  have hfun : (fun x : E k => ∫ t in Set.Icc a b, momChar k x t) =
        fun x : E k => ∫ t, momChar k x t ∂((volume : Measure ℝ).restrict (Set.Icc a b)) := by
    funext x
    rfl
  simpa [hfun] using hc

/-- `x ↦ ∫_{a}^{b} e(x·γ(t)) dt` (interval-integral form) is continuous in
`x` for `a ≤ b`. -/
lemma intervalIntegral_momChar_continuous (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun x : E k =>
      intervalIntegral (fun t : ℝ => momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have h1 : (fun x : E k =>
        intervalIntegral (fun t : ℝ => momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      = fun x : E k => ∫ t in Set.Icc a b, momChar k x t := by
    funext x
    rw [intervalIntegral.integral_of_le hab]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [h1]
  exact momChar_Icc_integral_continuous k a b

/-- The extension operator `E_{[a,b]} 1` of the constant function is continuous
in the extension variable `x` (for `a ≤ b`). -/
lemma extOp_one_continuous (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun x : E k => extOp k (fun _ : ℝ => (1 : ℂ)) a b x) := by
  have h : (fun x : E k => extOp k (fun _ : ℝ => (1 : ℂ)) a b x)
      = fun x : E k => intervalIntegral (fun t : ℝ => momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    funext x
    unfold extOp
    apply intervalIntegral.integral_congr
    intro t ht
    simp
  rw [h]
  exact intervalIntegral_momChar_continuous k hab

/-- `x ↦ E_{[a,b]}(c·1)(x)` is continuous in `x` for `a ≤ b` (constant source). -/
lemma extOp_const_continuous (k : ℕ) (c : ℂ) {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun x : E k => extOp k (fun _ : ℝ => c) a b x) := by
  have h : (fun x : E k => extOp k (fun _ : ℝ => c) a b x)
      = fun x : E k => c * intervalIntegral (fun t : ℝ => momChar k x t) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    funext x
    rw [extOp_const_char]
  rw [h]
  exact (intervalIntegral_momChar_continuous k hab).const_mul c


/-- **Shrinking-interval limit for the character**: for fixed `x`, the average
of `e(x·γ(t))` over the symmetric interval `[t₀−τ, t₀+τ]` converges to the
value at `t₀` as `τ → 0⁺`.  (Instance of the commons lemma
`Commons.Analysis.Integral.interval_avg_tendsto`; this is the per-term engine
of the discretisation step `E_{[0,1]} g_τ → sepCharSum`.) -/
lemma momChar_interval_avg_tendsto (k : ℕ) (x : E k) (t₀ : ℝ) :
    Filter.Tendsto
      (fun τ : ℝ => (1 / (2 * τ)) • intervalIntegral (fun t : ℝ => momChar k x t)
        (t₀ - τ) (t₀ + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (momChar k x t₀)) := by
  simpa using (Commons.Analysis.Integral.interval_avg_tendsto (f := fun t : ℝ => momChar k x t)
    (momChar_continuous_t k x) (t₀ := t₀))


/-! ## The step-function family `g_τ` (discretisation input)

Following BDG's derivation of the discrete restriction bound from decoupling
("apply decoupling to `g = (1/2τ)·Σᵢ aᵢ·1_{(tᵢ−τ,tᵢ+τ)}`, then let `τ → 0`"),
we fix the step functions `g_τ` and prove the two limit facts that engine
that argument: (i) the extension values `E g_τ(x)` converge pointwise (for
each `x`, as `τ → 0⁺`) to the separated character sum `sepCharSum k a t x`;
(ii) they are dominated by `Σᵢ‖aᵢ‖` uniformly in `x` and `τ`, so any
`L^p`-norm limit against a weight follows by dominated convergence.  `E g_τ`
is taken over the whole `t`-line (the bumps `(tᵢ−τ,tᵢ+τ)` shrink to the
points `tᵢ`); for `τ` small enough that all bumps lie inside `(0,1)` this
equals the interval extension `extOp` over `[0,1]` (integration restricted to
the bumps), and the decoupling cells `((i−1)/N, i/N]` are then handled by the
adjacent-additivity of `extOp`.  Nothing here needs the deep decoupling
theorem; all lemmas below are proved. -/

/-- `g_τ(u) = Σᵢ (aᵢ/(2τ))·1_{(tᵢ−τ,tᵢ+τ)}(u)` — the step function whose
extension operator converges to the separated character sum as `τ → 0⁺`.
Coefficient `(aᵢ·(1/(2τ)) : ℂ)` (real inverse cast). -/
def charStep {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) (τ : ℝ) (u : ℝ) : ℂ :=
  ∑ i : Fin N, (a i * ((1 / (2 * τ) : ℝ) : ℂ)) *
    Set.indicator (Set.Ioo (t i - τ) (t i + τ)) (fun _ : ℝ => (1 : ℂ)) u

/-- `E g_τ(x)` over the whole `t`-line: `∫_ℝ g_τ(t)e(x·γ(t))dt` (finite sum of
per-bump interval integrals; equal to the ℝ-integral by linearity when the
bumps are pairwise disjoint, and in the limit `τ → 0⁺`). -/
def extOpChar (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) (τ : ℝ) (x : E k) : ℂ :=
  ∑ i : Fin N, (a i * ((1 / (2 * τ) : ℝ) : ℂ)) *
    intervalIntegral (fun u : ℝ => momChar k x u) (t i - τ) (t i + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ)

/-- per-term convergence: `a·(1/(2τ))·∫_{t₀−τ}^{t₀+τ} momChar → a·momChar(x,t₀)`. -/
lemma extOpChar_term_tendsto (k : ℕ) (x : E k) (a : ℂ) (t₀ : ℝ) :
    Filter.Tendsto
      (fun τ : ℝ => (a * ((1 / (2 * τ) : ℝ) : ℂ)) *
        intervalIntegral (fun u : ℝ => momChar k x u) (t₀ - τ) (t₀ + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (a * momChar k x t₀)) := by
  have hav : Filter.Tendsto
      (fun τ : ℝ => a * (((1 / (2 * τ) : ℝ) : ℂ) *
        intervalIntegral (fun u : ℝ => momChar k x u) (t₀ - τ) (t₀ + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (a * momChar k x t₀)) := by
    have h0 := Commons.Analysis.Integral.interval_avg_tendsto (f := fun u : ℝ => momChar k x u)
      (momChar_continuous_t k x) (t₀ := t₀)
    have h1 : Filter.Tendsto
        (fun τ : ℝ => ((1 / (2 * τ) : ℝ) : ℂ) * intervalIntegral (fun u : ℝ => momChar k x u) (t₀ - τ) (t₀ + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (momChar k x t₀)) := by
      simpa [Algebra.smul_def] using h0
    exact Filter.Tendsto.const_mul a h1
  refine Filter.Tendsto.congr ?_ hav
  intro τ
  ring

/-- pointwise (in `x`) convergence of the extension of `g_τ` to the separated
character sum, as `τ → 0⁺`. -/
lemma extOpChar_tendsto_sepCharSum (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) (x : E k) :
    Filter.Tendsto (fun τ : ℝ => extOpChar k a t τ x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sepCharSum k a t x)) := by
  unfold extOpChar sepCharSum
  exact tendsto_finsetSum Finset.univ
    (fun i _ => extOpChar_term_tendsto k x (a i) (t i))

/-- norm of the real cast into `ℂ`: `‖(x:ℂ)‖ = |x|`. -/
lemma norm_ofReal_complex (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  have h₁ : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq (z := (x : ℂ)), Complex.normSq_ofReal]
    ring
  calc
    ‖(x : ℂ)‖ = Real.sqrt (‖(x : ℂ)‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg (norm_nonneg (x : ℂ))]
    _ = Real.sqrt (x ^ 2) := by rw [h₁]
    _ = |x| := Real.sqrt_sq_eq_abs x

/-- interval integral of the constant `1` over `[a,b]`, `a ≤ b`: equals `b−a`. -/
lemma intervalIntegral_one_const (a b : ℝ) (hab : a ≤ b) :
    (∫ u in a..b, (1 : ℝ) ∂(volume : Measure ℝ)) = b - a := by
  rw [intervalIntegral.integral_const]
  simp

/-- the interval integral of `momChar` (modulus 1) over `[a,b]` is bounded by
the length `b − a` (for `a ≤ b`). -/
lemma norm_intervalIntegral_momChar_le (k : ℕ) (x : E k) (a b : ℝ) (hab : a ≤ b) :
    ‖intervalIntegral (fun u : ℝ => momChar k x u) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖ ≤ b - a := by
  calc
    ‖intervalIntegral (fun u : ℝ => momChar k x u) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖
        ≤ intervalIntegral (fun u : ℝ => ‖momChar k x u‖) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
          intervalIntegral.norm_integral_le_integral_norm hab
    _ = intervalIntegral (fun u : ℝ => (1 : ℝ)) a b (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          apply intervalIntegral.integral_congr
          intro u _hu
          exact momChar_norm_one k x u
    _ = b - a := intervalIntegral_one_const a b hab

/-- domination: `‖E g_τ(x)‖ ≤ Σᵢ‖aᵢ‖`, uniformly in `x` and `τ > 0` — the
bound used for dominated convergence in the `τ → 0⁺` limit against any weight. -/
lemma extOpChar_norm_le (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) (x : E k) :
    ∀ τ : ℝ, 0 < τ → ‖extOpChar k a t τ x‖ ≤ ∑ i : Fin N, ‖a i‖ := by
  intro τ hτ
  unfold extOpChar
  calc
    ‖∑ i : Fin N, (a i * ((1 / (2 * τ) : ℝ) : ℂ)) *
        intervalIntegral (fun u : ℝ => momChar k x u) (t i - τ) (t i + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖
        ≤ ∑ i : Fin N, ‖(a i * ((1 / (2 * τ) : ℝ) : ℂ)) *
            intervalIntegral (fun u : ℝ => momChar k x u) (t i - τ) (t i + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ i : Fin N, ‖a i‖ := by
          apply Finset.sum_le_sum
          intro i hi
          have hii : t i - τ ≤ t i + τ := by linarith
          have hlen : ‖intervalIntegral (fun u : ℝ => momChar k x u) (t i - τ) (t i + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖ ≤ 2 * τ := by
            have h := norm_intervalIntegral_momChar_le k x (t i - τ) (t i + τ) hii
            linarith
          have hn : ‖a i * ((1 / (2 * τ) : ℝ) : ℂ)‖ = ‖a i‖ / (2 * τ) := by
            rw [norm_mul]
            have hc : ‖(((1 / (2 * τ) : ℝ) : ℂ))‖ = (2 * τ)⁻¹ := by
              rw [norm_ofReal_complex (1 / (2 * τ))]
              rw [abs_of_nonneg (one_div_nonneg.mpr (mul_nonneg (by norm_num) (le_of_lt hτ)))]
              rw [one_div]
            rw [hc]
            ring
          calc
            ‖(a i * ((1 / (2 * τ) : ℝ) : ℂ)) * intervalIntegral (fun u : ℝ => momChar k x u) (t i - τ) (t i + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖
                = ‖a i * ((1 / (2 * τ) : ℝ) : ℂ)‖ * ‖intervalIntegral (fun u : ℝ => momChar k x u) (t i - τ) (t i + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖ := by
                  rw [norm_mul]
            _ ≤ ‖a i * ((1 / (2 * τ) : ℝ) : ℂ)‖ * (2 * τ) := by
                  exact mul_le_mul_of_nonneg_left hlen (norm_nonneg _)
            _ = ‖a i‖ := by
                  rw [hn]
                  exact div_mul_cancel₀ (‖a i‖) (ne_of_gt (mul_pos (by norm_num) hτ))


/-- continuity in `x` of the extension value of the step function (for `τ ≥ 0`). -/
lemma extOpChar_continuous (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Continuous (fun x : E k => extOpChar k a t τ x) := by
  unfold extOpChar
  have hii : ∀ i : Fin N, t i - τ ≤ t i + τ := by
    intro i
    linarith
  have hcont (i : Fin N) : Continuous (fun x : E k =>
      (a i * ((1 / (2 * τ) : ℝ) : ℂ)) *
        intervalIntegral (fun u : ℝ => momChar k x u) (t i - τ) (t i + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    have hc : Continuous (fun x : E k =>
        intervalIntegral (fun u : ℝ => momChar k x u) (t i - τ) (t i + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :=
      intervalIntegral_momChar_continuous k (hii i)
    exact hc.const_mul (a i * ((1 / (2 * τ) : ℝ) : ℂ))
  exact continuous_finset_sum Finset.univ (fun i _hi => hcont i)

/-- pointwise limit of the integrand `x ↦ ‖E g_τ(x)‖^p · w_B(x)` (natural `p`). -/
lemma wLpPow_integrand_tendsto (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ)
    {R : ℝ} (hR : 0 < R) (c : E k) (p : ℕ) :
    ∀ x : E k, Filter.Tendsto
      (fun τ : ℝ => ‖extOpChar k a t τ x‖ ^ p * ballWeight k c R x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (‖sepCharSum k a t x‖ ^ p * ballWeight k c R x)) := by
  intro x
  have hmain := extOpChar_tendsto_sepCharSum k a t x
  have hn : Continuous fun z : ℂ => ‖z‖ ^ p := continuous_norm.pow p
  have hnp := hn.continuousAt.tendsto.comp hmain
  have hb : Continuous fun r : ℝ => r * ballWeight k c R x := by
    fun_prop
  have hb2 := hb.continuousAt.tendsto.comp hnp
  simpa [Function.comp_def] using hb2

/-- weighted `L^p` limit: as `τ → 0⁺`, `∫ ‖E g_τ‖^p w_B → ∫ ‖sepCharSum‖^p w_B`
(natural exponent `p`; `R > 0`, `k ≥ 1`). -/
lemma wLpPow_tendsto_extOpChar (k : ℕ) (hk : 1 ≤ k) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ)
    {R : ℝ} (hR : 0 < R) (c : E k) (p : ℕ) :
    Filter.Tendsto
      (fun τ : ℝ => ∫ x : E k, ‖extOpChar k a t τ x‖ ^ p * ballWeight k c R x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x : E k, ‖sepCharSum k a t x‖ ^ p * ballWeight k c R x)) := by
  let M : ℝ := ∑ i : Fin N, ‖a i‖
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  let bound : E k → ℝ := fun x => M ^ p * ballWeight k c R x
  have hl : l = nhdsWithin 0 (Set.Ioi 0) := rfl
  have hbint : Integrable bound volume := by
    dsimp [bound]
    exact (ballWeight_integrable k hk c hR).const_mul (M ^ p)
  have hF_meas : ∀ᶠ τ : ℝ in l, AEStronglyMeasurable
      (fun x : E k => ‖extOpChar k a t τ x‖ ^ p * ballWeight k c R x) volume := by
    rw [hl]
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with τ hτ
    have hτ0 : 0 ≤ τ := le_of_lt (Set.mem_Ioo.mp hτ).1
    have hc : Continuous (fun x : E k => ‖extOpChar k a t τ x‖ ^ p * ballWeight k c R x) := by
      have h1 : Continuous (fun x : E k => ‖extOpChar k a t τ x‖ ^ p) := by
        exact (continuous_norm.pow p).comp (extOpChar_continuous k a t hτ0)
      exact h1.mul (ballWeight_continuous k c hR)
    exact hc.aestronglyMeasurable
  have h_bound : ∀ᶠ τ : ℝ in l, ∀ᵐ (x : E k) ∂volume, ‖‖extOpChar k a t τ x‖ ^ p * ballWeight k c R x‖ ≤ bound x := by
    rw [hl]
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with τ hτ
    filter_upwards with x
    have hnorm : ‖extOpChar k a t τ x‖ ≤ M := by
      dsimp [M]
      exact extOpChar_norm_le k a t x τ (Set.mem_Ioo.mp hτ).1
    have hw0 : 0 ≤ ballWeight k c R x := le_of_lt (ballWeight_pos k c hR x)
    have hpow : ‖extOpChar k a t τ x‖ ^ p ≤ M ^ p := pow_le_pow_left₀ (norm_nonneg _) hnorm p
    calc
      ‖‖extOpChar k a t τ x‖ ^ p * ballWeight k c R x‖ = ‖extOpChar k a t τ x‖ ^ p * ballWeight k c R x := by
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) p) hw0)]
      _ ≤ M ^ p * ballWeight k c R x := mul_le_mul_of_nonneg_right hpow hw0
  have h_lim : ∀ᵐ (x : E k) ∂volume, Filter.Tendsto
      (fun τ : ℝ => ‖extOpChar k a t τ x‖ ^ p * ballWeight k c R x) l (nhds (‖sepCharSum k a t x‖ ^ p * ballWeight k c R x)) := by
    filter_upwards with x
    simpa [hl] using wLpPow_integrand_tendsto k a t hR c p x
  have hdc := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure (E k))) (F := fun τ : ℝ => fun x : E k => ‖extOpChar k a t τ x‖ ^ p * ballWeight k c R x)
      (f := fun x : E k => ‖sepCharSum k a t x‖ ^ p * ballWeight k c R x)
      bound (l := l) hF_meas h_bound hbint h_lim
  simpa [l] using hdc


/-- `wLpPow` at a natural exponent equals the natural-power integral (bridge
from the real-rpow convention of `Decoupling.wLpPow` to the natural powers of
`wLpPow_tendsto_extOpChar`). -/
lemma wLpPow_natCast (k : ℕ) (c : E k) (R : ℝ) (p : ℕ) (f : E k → ℂ) :
    wLpPow k c R (p : ℝ) f = ∫ x : E k, ‖f x‖ ^ p * ballWeight k c R x := by
  unfold wLpPow
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [Real.rpow_natCast]

/-- the `wLpPow`-form of the weighted `L^p` limit (natural exponent cast to
real): `wLpPow p (E g_τ) → wLpPow p (sepCharSum)` as `τ → 0⁺`. -/
lemma wLpPow_tendsto_extOpChar' (k : ℕ) (hk : 1 ≤ k) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ)
    {R : ℝ} (hR : 0 < R) (c : E k) (p : ℕ) :
    Filter.Tendsto
      (fun τ : ℝ => wLpPow k c R (p : ℝ) (fun x : E k => extOpChar k a t τ x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (wLpPow k c R (p : ℝ) (sepCharSum k a t))) := by
  have hbase := wLpPow_tendsto_extOpChar k hk a t hR c p
  -- both sides equal the natural-power integrals
  have hL : (fun τ : ℝ => wLpPow k c R (p : ℝ) (fun x : E k => extOpChar k a t τ x))
      = fun τ : ℝ => ∫ x : E k, ‖extOpChar k a t τ x‖ ^ p * ballWeight k c R x := by
    funext τ
    exact wLpPow_natCast k c R p (fun x : E k => extOpChar k a t τ x)
  have hR' : wLpPow k c R (p : ℝ) (sepCharSum k a t)
      = ∫ x : E k, ‖sepCharSum k a t x‖ ^ p * ballWeight k c R x :=
    wLpPow_natCast k c R p (sepCharSum k a t)
  simpa [hL, hR'] using hbase


/-- **Bridge**: when every bump `(tᵢ−τ,tᵢ+τ)` is contained in `(0,1)`, the
interval extension operator over `[0,1]` of the step function `g_τ` equals the
whole-line per-bump sum `extOpChar` (each bump contributes exactly its own
interval integral). -/
lemma extOp_charStep_eq_extOpChar (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) (x : E k)
    (hinside : ∀ i : Fin N, 0 ≤ t i - τ ∧ t i + τ ≤ 1) :
    extOp k (charStep a t τ) 0 1 x = extOpChar k a t τ x := by
  unfold extOp extOpChar
  have hcongr : (fun u : ℝ => charStep a t τ u * momChar k x u)
      = fun u : ℝ => ∑ i : Fin N,
          (a i * ((1 / (2 * τ) : ℝ) : ℂ)) *
            Set.indicator (Set.Ioo (t i - τ) (t i + τ)) (fun _ : ℝ => (1 : ℂ)) u * momChar k x u := by
    funext u
    unfold charStep
    rw [Finset.sum_mul]
  rw [hcongr, intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [show (fun u : ℝ => a i * ((1 / (2 * τ) : ℝ) : ℂ) *
        Set.indicator (Set.Ioo (t i - τ) (t i + τ)) (fun _ : ℝ => (1 : ℂ)) u * momChar k x u)
        = fun u : ℝ => (a i * ((1 / (2 * τ) : ℝ) : ℂ)) *
            (Set.indicator (Set.Ioo (t i - τ) (t i + τ)) (fun _ : ℝ => (1 : ℂ)) u * momChar k x u) from by
          funext u; ring]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have h0 : (0:ℝ) ≤ t i - τ := (hinside i).1
    have h1 : t i + τ ≤ 1 := (hinside i).2
    have h2 : t i - τ ≤ t i + τ := by linarith
    have hint : IntervalIntegrable (fun u : ℝ => momChar k x u) (MeasureTheory.volume : MeasureTheory.Measure ℝ) 0 1 :=
      Continuous.intervalIntegrable (momChar_continuous_t k x) (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) 0 1
    exact Commons.Analysis.Integral.intervalIntegral_indicator_Ioo h0 h2 h1 hint
  · intro i _hi
    exact Commons.Analysis.Integral.intervalIntegrable_indicator_mul_continuous
      (momChar_continuous_t k x) (a i * ((1 / (2 * τ) : ℝ) : ℂ))

/-- **Interval-`[0,1]` pointwise limit**: for points strictly inside `(0,1)`,
the extension operator over `[0,1]` of `g_τ` converges, pointwise in `x`, to
the separated character sum (BDG's actual object; the whole-line `extOpChar`
agrees with it for `τ` small enough that all bumps sit inside `[0,1]`).
(Boundary points `tᵢ = i/N` / `tᵢ = 1` split across adjacent cells — handled
separately in the eventual derivation.) -/
lemma extOp_charStep_tendsto_sepCharSum (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ)
    (ht : ∀ i : Fin N, 0 < t i ∧ t i < 1) (x : E k) :
    Filter.Tendsto (fun τ : ℝ => extOp k (charStep a t τ) 0 1 x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sepCharSum k a t x)) := by
  refine Filter.Tendsto.congr' ?_ (extOpChar_tendsto_sepCharSum k a t x)
  have h_pos : ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < τ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with τ hτ
    exact (Set.mem_Ioo.mp hτ).1
  have h_ev : ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ i : Fin N, 0 ≤ t i - τ ∧ t i + τ ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    have hpos : 0 < min (t i) (1 - t i) := lt_min (ht i).1 (sub_pos.mpr (ht i).2)
    filter_upwards [Ioo_mem_nhdsGT hpos] with τ hτ
    obtain ⟨_hτ0, hτδ⟩ := Set.mem_Ioo.mp hτ
    refine ⟨by linarith [lt_of_lt_of_le hτδ (min_le_left (t i) (1 - t i))],
            by linarith [lt_of_lt_of_le hτδ (min_le_right (t i) (1 - t i))]⟩
  filter_upwards [h_pos, h_ev] with τ hτ0 hτ
  exact (extOp_charStep_eq_extOpChar k a t (le_of_lt hτ0) x hτ).symm


/-- the `wLpPowAvg`-normalised weighted `L^p` limit (the normalisation used by
`bdg_critical`): dividing the `wLpPow` limit by the (τ-independent) ball
volume. -/
lemma wLpPowAvg_tendsto_extOpChar (k : ℕ) (hk : 1 ≤ k) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ)
    {R : ℝ} (hR : 0 < R) (c : E k) (p : ℕ) :
    Filter.Tendsto
      (fun τ : ℝ => wLpPowAvg k c R (p : ℝ) (fun x : E k => extOpChar k a t τ x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (wLpPowAvg k c R (p : ℝ) (sepCharSum k a t))) := by
  have hbase := wLpPow_tendsto_extOpChar' k hk a t hR c p
  have hdiv : (fun τ : ℝ => wLpPowAvg k c R (p : ℝ) (fun x : E k => extOpChar k a t τ x))
      = fun τ : ℝ => wLpPow k c R (p : ℝ) (fun x : E k => extOpChar k a t τ x) / ballVol k c R := by
    funext τ
    rfl
  have htop : wLpPowAvg k c R (p : ℝ) (sepCharSum k a t)
      = wLpPow k c R (p : ℝ) (sepCharSum k a t) / ballVol k c R := rfl
  rw [hdiv, htop]
  exact hbase.div_const (ballVol k c R)

end
end Submission.Vinogradov
