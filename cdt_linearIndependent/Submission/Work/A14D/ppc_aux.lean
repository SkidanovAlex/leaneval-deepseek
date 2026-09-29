import Mathlib
import Submission.Work.A14.defs
import Submission.Work.C7.g_form
import Submission.Work.C7.evA_Lps
import Submission.Work.C17I.hasSum_tsum_of_poly_growth
import Submission.Work.C17f.deriv_hasSum_powSeries
import Submission.Work.C17f.differentiableOn_of_hasSum_powSeries
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.C17.Bsubst_poly_growth
import Submission.Work.C17.Js_bound
import Submission.Work.C17.B5_pullback
import Submission.Work.C17I.seventeen_subst_eval
import Submission.Work.CPull.evp_aux
import Submission.Work.CPull.evp_sympPhi
import Submission.Work.CPull.evp_add_mul
import Submission.Work.A14D.H_cont

/-!
# `Work.A14D.ppc_aux` — infrastructure for the continuation of the seven pure pullbacks

Shared tools for `Work.A14D.pure_pullback_cont`:

* term-by-term differentiation of the evaluation functional `evp` (`evp_deriv`);
* polynomial growth bounds for the coefficients of the pullbacks `Bᵢ ∘ y` (from
  `Work.C17.Bsubst_poly_growth`), of `Jps`, `Li₂`, `log(1−x)`, `y = x²/(x−1)`, and for the
  derived series;
* a holomorphic branch of `log(1 − z)` on a convex open set `S` avoiding `1`, matching the
  principal branch on `S ∩ ball 0 1`;
* the generic continuation lemma `cont_of_convex_ode`: a solution of a first-order linear ODE
  `y' = A z · y + b z`, holomorphic on `S ∩ ball 0 1` with `A, b` holomorphic on the convex open
  `S`, extends to a solution on all of `S` (agreeing with the given one on `S ∩ ball 0 1`);
* the elementary geometry of `SU`, `SL` and the auxiliary points `±i/2`.
-/

namespace Work.A14D

open Complex Metric
open PowerSeries
open scoped BigOperators

noncomputable section

/-! ## 1. Growth of coefficients -/

/-- `‖(q : ℂ)‖ = |(q : ℝ)|` for a rational `q`. -/
lemma norm_ratCast_aux (q : ℚ) : ‖(q : ℂ)‖ = |(q : ℝ)| := by simp

/-- The coefficients of the pullback `(pureB j) ∘ y` grow polynomially. -/
theorem pureB_subst_poly_growth (j : Fin 7) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ n : ℕ,
      ‖((PowerSeries.coeff n ((Submission.CDTPlan.pureB j).subst Submission.CDT.sympY) : ℚ) : ℂ)‖
        ≤ C * ((n : ℝ) + 1) ^ k := by
  obtain ⟨C, k, hk⟩ := Work.C17.Bsubst_poly_growth j
  refine ⟨C, ?_, k, fun n => ?_⟩
  · have h0 := hk 0
    simp only [Nat.cast_zero, zero_add, one_pow, mul_one] at h0
    exact le_trans (abs_nonneg _) h0
  · rw [norm_ratCast_aux]
    exact hk n

/-- The coefficients of `y = x²/(x−1)` are bounded by `1`. -/
lemma poly_growth_sympY :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ n : ℕ,
      ‖((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ k := by
  refine ⟨1, zero_le_one, 0, fun n => ?_⟩
  rw [pow_zero, mul_one, norm_ratCast_aux, Work.CPull.coeff_sympY_eq n]
  split_ifs <;> norm_num

/-- The coefficients of `log(1−x) = Σ −xⁿ/n` are bounded by `1`. -/
lemma poly_growth_Lps :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ n : ℕ,
      ‖((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ k := by
  refine ⟨1, zero_le_one, 0, fun n => ?_⟩
  rw [pow_zero, mul_one]
  have h : ((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ)
      = if n = 0 then 0 else -((n : ℂ))⁻¹ := by
    rw [Work.C7.coeff_Lps]
    split_ifs with hn
    · simp
    · push_cast; ring
  rw [h]
  split_ifs with hn
  · simp
  · rw [norm_neg, norm_inv, Complex.norm_natCast]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    exact inv_le_one_of_one_le₀ hn1

/-- The coefficients of `Li₂(x) = Σ xⁿ/n²` are bounded by `1`. -/
lemma poly_growth_Li2ps :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ n : ℕ,
      ‖((PowerSeries.coeff n Work.C7.Li2ps : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ k := by
  refine ⟨1, zero_le_one, 0, fun n => ?_⟩
  rw [pow_zero, mul_one]
  have h : ((PowerSeries.coeff n Work.C7.Li2ps : ℚ) : ℂ)
      = if n = 0 then 0 else -(((n : ℂ)) ^ 2)⁻¹ * (-1) := by
    rw [Work.C7.coeff_Li2ps]
    split_ifs with hn
    · simp
    · push_cast; ring
  rw [h]
  split_ifs with hn
  · simp
  · simp only [norm_mul, norm_neg, norm_inv, norm_pow, Complex.norm_natCast, norm_one, mul_one]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    exact inv_le_one_of_one_le₀ (by nlinarith : (1 : ℝ) ≤ (n : ℝ) ^ 2)

/-- The coefficients of `Jps` grow polynomially (from the ODE it satisfies). -/
lemma poly_growth_Jps :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ n : ℕ,
      ‖((PowerSeries.coeff n Work.C7.Jps : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ k := by
  have hJode := Work.C7.J_ode Work.C7.g_form.1 Work.C17.g4_form Work.C17.B5_pullback
  obtain ⟨C, k, hk⟩ := Work.C17.Js_bound hJode
  refine ⟨C, ?_, k, fun n => ?_⟩
  · have h0 := hk 0
    simp only [Nat.cast_zero, zero_add, one_pow, mul_one] at h0
    exact le_trans (abs_nonneg _) h0
  · rw [norm_ratCast_aux]
    exact hk n

/-- Polynomial growth passes to the derived series. -/
lemma poly_growth_deriv {f : PowerSeries ℚ} {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    (hb : ∀ n : ℕ, ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ k) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∃ k' : ℕ, ∀ n : ℕ,
      ‖((PowerSeries.coeff n (PowerSeries.derivative (R := ℚ) f) : ℚ) : ℂ)‖
        ≤ C' * ((n : ℝ) + 1) ^ k' := by
  refine ⟨C * 2 ^ k, by positivity, k + 1, fun n => ?_⟩
  have h1 : ((PowerSeries.coeff n (PowerSeries.derivative (R := ℚ) f) : ℚ) : ℂ)
      = (((n : ℚ) + 1 : ℚ) : ℂ) * ((PowerSeries.coeff (n + 1) f : ℚ) : ℂ) := by
    rw [PowerSeries.coeff_derivative]
    push_cast
    ring
  have hcast : ‖(((n : ℚ) + 1 : ℚ) : ℂ)‖ = (n : ℝ) + 1 := by
    rw [norm_ratCast_aux]
    have hnn : (0 : ℝ) ≤ ((n : ℚ) + 1 : ℚ) := by positivity
    rw [abs_of_nonneg hnn]
    push_cast
    ring
  have h2 : ‖((PowerSeries.coeff (n + 1) f : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 2) ^ k := by
    have h := hb (n + 1)
    have hp : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
    rwa [hp] at h
  have h3 : ((n : ℝ) + 2) ^ k ≤ (2 * ((n : ℝ) + 1)) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  have h4 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [h1, norm_mul, hcast]
  calc ((n : ℝ) + 1) * ‖((PowerSeries.coeff (n + 1) f : ℚ) : ℂ)‖
      ≤ ((n : ℝ) + 1) * (C * ((n : ℝ) + 2) ^ k) := mul_le_mul_of_nonneg_left h2 h4
    _ ≤ ((n : ℝ) + 1) * (C * (2 * ((n : ℝ) + 1)) ^ k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hC) h4
    _ = (C * 2 ^ k) * ((n : ℝ) + 1) ^ (k + 1) := by rw [mul_pow, pow_succ]; ring

/-! ## 2. Summability and differentiability from polynomial growth -/

/-- Positive-radius absolute summability from polynomial growth of the coefficients. -/
lemma summable_abs_coeff_of_poly_growth {f : PowerSeries ℚ} {C : ℝ} {k : ℕ} (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ k)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n‖) := by
  set r : ℝ := max ‖z‖ (1 / 2) with hr
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hr1 : r < 1 := max_lt hz (by norm_num)
  have hzr : ‖z‖ ≤ r := le_max_left _ _
  have hb' : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n) :=
    Work.C17I.summable_pow_add_one_mul_geometric hr0 hr1
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hb'.mul_left C)
  have h1 : ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ * ‖z‖ ^ n
      ≤ (C * ((n : ℝ) + 1) ^ k) * ‖z‖ ^ n :=
    mul_le_mul_of_nonneg_right (hb n) (pow_nonneg (norm_nonneg z) n)
  have h2 : (C * ((n : ℝ) + 1) ^ k) * ‖z‖ ^ n
      ≤ (C * ((n : ℝ) + 1) ^ k) * r ^ n :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg z) hzr n) (by positivity)
  rw [norm_mul, norm_pow]
  calc ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ * ‖z‖ ^ n
      ≤ (C * ((n : ℝ) + 1) ^ k) * r ^ n := le_trans h1 h2
    _ = C * (((n : ℝ) + 1) ^ k * r ^ n) := by ring

/-- The evaluation of a polynomially-growing series is holomorphic on the unit disc. -/
lemma differentiableOn_evp_of_poly_growth {f : PowerSeries ℚ} {C : ℝ} {k : ℕ} (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ k) :
    DifferentiableOn ℂ (fun z : ℂ => Work.CPull.evp f z) (Metric.ball 0 1) :=
  Work.C17f.differentiableOn_of_hasSum_powSeries (c := fun n => ((PowerSeries.coeff n f : ℚ) : ℂ))
    (r := 1) (F := fun z => Work.CPull.evp f z) fun z hz => by
      simpa [Work.CPull.evp] using Work.C17I.hasSum_tsum_of_poly_growth hC hb z hz

/-- `evp (derivative f) z = deriv (fun w => evp f w) z` on the unit disc, for polynomially
growing coefficients. -/
theorem evp_deriv {f : PowerSeries ℚ} {C : ℝ} {k : ℕ} (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ k)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Work.CPull.evp (PowerSeries.derivative (R := ℚ) f) z = deriv (fun w => Work.CPull.evp f w) z := by
  have hhs : ∀ w : ℂ, ‖w‖ < 1 → HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * w ^ n)
      (Work.CPull.evp f w) := by
    intro w hw
    simpa [Work.CPull.evp] using Work.C17I.hasSum_tsum_of_poly_growth hC hb w hw
  have hd := Work.C17f.deriv_hasSum_powSeries
    (fun n => ((PowerSeries.coeff n f : ℚ) : ℂ)) 1 (fun w => Work.CPull.evp f w) hhs z hz
  rw [← hd.tsum_eq, Work.CPull.evp]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_derivative]
  push_cast
  ring

/-! ## 3. A holomorphic branch of `log (1 − z)` on a convex set avoiding `1` -/

/-- `1 - z ∈ slitPlane` for `‖z‖ < 1` (its real part is positive). -/
lemma one_sub_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) : (1 - z) ∈ Complex.slitPlane := by
  refine Or.inl ?_
  have h := Complex.re_le_norm z
  have h2 : z.re < 1 := by linarith [Complex.re_le_norm z, hz]
  simpa using sub_pos.mpr h2

/-- The principal branch `z ↦ log (1 − z)` is holomorphic on the unit disc. -/
lemma differentiableOn_log_one_sub :
    DifferentiableOn ℂ (fun z : ℂ => Complex.log (1 - z)) (Metric.ball 0 1) :=
  ((differentiableOn_const (1 : ℂ)).sub differentiableOn_id).clog
    (fun z hz => one_sub_mem_slitPlane (by simpa [Metric.mem_ball, dist_zero_right] using hz))

/-- Its derivative on the unit disc is `1/(z-1)`. -/
lemma hasDerivAt_log_one_sub {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ => Complex.log (1 - w)) ((z - 1)⁻¹) z := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := (hasDerivAt_id z).const_sub 1
  have h2 : HasDerivAt (fun w : ℂ => Complex.log (1 - w)) ((-1) / (1 - z)) z :=
    h1.clog (one_sub_mem_slitPlane hz)
  have he : ((-1) / (1 - z)) = (z - 1)⁻¹ := by
    rw [div_eq_mul_inv, show z - 1 = (1 - z) * (-1) by ring, mul_inv, inv_neg, inv_one]
    ring
  rwa [he] at h2

/-- On a convex open set `S` avoiding `1`, there is a holomorphic branch `𝓛` of `log (1 − z)`
with `𝓛' = 1/(z − 1)`, normalised to coincide with the principal branch at a prescribed point
`z₀ ∈ S ∩ ball 0 1`. -/
theorem exists_log_branch {S : Set ℂ} (hSo : IsOpen S) (hSc : Convex ℝ S) {z₀ : ℂ}
    (hz₀ : z₀ ∈ S ∩ Metric.ball 0 1) (h1 : (1 : ℂ) ∉ S) :
    ∃ 𝓛 : ℂ → ℂ, DifferentiableOn ℂ 𝓛 S ∧ 𝓛 z₀ = Complex.log (1 - z₀) ∧
      (∀ z ∈ S, HasDerivAt 𝓛 ((z - 1)⁻¹) z) ∧
      ∀ z ∈ S ∩ Metric.ball 0 1, 𝓛 z = Complex.log (1 - z) := by
  have hb : DifferentiableOn ℂ (fun z : ℂ => (z - 1)⁻¹) S := by
    have h : DifferentiableOn ℂ (fun z : ℂ => 1 / (z - 1)) S := by
      refine DifferentiableOn.div (differentiableOn_const (1 : ℂ))
        (differentiableOn_id.sub (differentiableOn_const (1 : ℂ))) ?_
      intro z hz h
      have hz1 : z = 1 := sub_eq_zero.mp h
      exact h1 (by rw [hz1] at hz; exact hz)
    refine h.congr ?_
    intro z _
    rw [one_div]
  obtain ⟨Y, hYd, hY₀, hYode⟩ :=
    Work.C17g.linear_ode_convex (k := 1) hSc hSo (fun _ _ _ => (0 : ℂ))
      (fun z _ => (z - 1)⁻¹)
      (differentiableOn_pi.mpr fun i => differentiableOn_pi.mpr fun j => by
        fin_cases i; fin_cases j
        exact differentiableOn_const 0)
      (differentiableOn_pi.mpr fun i => by fin_cases i; exact hb)
      z₀ hz₀.1 (fun _ => Complex.log (1 - z₀))
  let 𝓛 : ℂ → ℂ := fun z => Y z 0
  have h𝓛d : DifferentiableOn ℂ 𝓛 S := (differentiableOn_pi.mp hYd) 0
  have h𝓛₀ : 𝓛 z₀ = Complex.log (1 - z₀) := by
    show Y z₀ 0 = _
    rw [congrFun hY₀ 0]
  have h𝓛' : ∀ z ∈ S, HasDerivAt 𝓛 ((z - 1)⁻¹) z := by
    intro z hz
    have h := (hasDerivAt_pi.mp (hYode z hz)) 0
    have hder : (Finset.univ.sum fun j : Fin 1 => (0 : ℂ) * Y z j) + (z - 1)⁻¹
        = (z - 1)⁻¹ := by simp
    rw [hder] at h
    exact h
  have hUo : IsOpen (S ∩ Metric.ball 0 1) := hSo.inter Metric.isOpen_ball
  have hUc : IsPreconnected (S ∩ Metric.ball 0 1) :=
    (hSc.inter (convex_ball 0 1)).isPreconnected
  have heq := Work.OdeCont.uniqueness (k := 1) hUo hUc
    (fun _ (_ _ : Fin 1) => (0 : ℂ)) (fun z _ => (z - 1)⁻¹)
    (fun i j => by
      show DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) (S ∩ Metric.ball 0 1)
      exact differentiableOn_const 0)
    (fun i => by
      show DifferentiableOn ℂ (fun z : ℂ => (z - 1)⁻¹) (S ∩ Metric.ball 0 1)
      exact hb.mono Set.inter_subset_left)
    (fun z _ => 𝓛 z) (fun z _ => Complex.log (1 - z))
    (differentiableOn_pi.mpr fun i => by
      fin_cases i
      exact h𝓛d.mono Set.inter_subset_left)
    (differentiableOn_pi.mpr fun i => by
      fin_cases i
      exact differentiableOn_log_one_sub.mono Set.inter_subset_right)
    (fun z hz => by
      rw [hasDerivAt_pi]
      intro _
      simpa [Fin.sum_univ_one] using h𝓛' z hz.1)
    (fun z hz => by
      rw [hasDerivAt_pi]
      intro _
      simpa [Fin.sum_univ_one] using
        hasDerivAt_log_one_sub (by simpa [Metric.mem_ball, dist_zero_right] using hz.2))
    hz₀ (by simp [h𝓛₀])
  refine ⟨𝓛, h𝓛d, h𝓛₀, h𝓛', fun z hz => ?_⟩
  exact congrFun (heq hz) 0

/-! ## 4. Continuation of a solution of a first-order linear ODE to a convex set -/

/-- A solution of `y' = A z · y + b z` on `S ∩ ball 0 1`, with `A, b` holomorphic on the convex
open set `S`, extends to a solution on all of `S` agreeing with it on `S ∩ ball 0 1`. -/
theorem cont_of_convex_ode {S : Set ℂ} (hSc : Convex ℝ S) (hSo : IsOpen S)
    {A b : ℂ → ℂ} (hAd : DifferentiableOn ℂ A S) (hbd : DifferentiableOn ℂ b S)
    {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f (S ∩ Metric.ball 0 1))
    (hfode : ∀ z ∈ S ∩ Metric.ball 0 1, HasDerivAt f (A z * f z + b z) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S ∩ Metric.ball 0 1) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F S ∧ (∀ z ∈ S, HasDerivAt F (A z * F z + b z) z) ∧
      ∀ z ∈ S ∩ Metric.ball 0 1, F z = f z := by
  obtain ⟨Y, hYd, hY₀, hYode⟩ :=
    Work.C17g.linear_ode_convex (k := 1) hSc hSo (fun z _ _ => A z) (fun z _ => b z)
      (differentiableOn_pi.mpr fun i => differentiableOn_pi.mpr fun j => by
        fin_cases i; fin_cases j
        show DifferentiableOn ℂ (fun z : ℂ => A z) S
        exact hAd)
      (differentiableOn_pi.mpr fun i => by
        fin_cases i
        show DifferentiableOn ℂ (fun z : ℂ => b z) S
        exact hbd)
      z₀ hz₀.1 (fun _ => f z₀)
  let F : ℂ → ℂ := fun z => Y z 0
  have hFd : DifferentiableOn ℂ F S := (differentiableOn_pi.mp hYd) 0
  have hFode : ∀ z ∈ S, HasDerivAt F (A z * F z + b z) z := by
    intro z hz
    have h := (hasDerivAt_pi.mp (hYode z hz)) 0
    have hder : (Finset.univ.sum fun j : Fin 1 => A z * Y z j) + b z = A z * F z + b z := by
      simp [F]
    rw [hder] at h
    exact h
  have hUo : IsOpen (S ∩ Metric.ball 0 1) := hSo.inter Metric.isOpen_ball
  have hUc : IsPreconnected (S ∩ Metric.ball 0 1) :=
    (hSc.inter (convex_ball 0 1)).isPreconnected
  have heq := Work.OdeCont.uniqueness (k := 1) hUo hUc
    (fun z _ _ => A z) (fun z _ => b z)
    (fun i j => by
      show DifferentiableOn ℂ (fun z : ℂ => A z) (S ∩ Metric.ball 0 1)
      exact hAd.mono Set.inter_subset_left)
    (fun i => by
      show DifferentiableOn ℂ (fun z : ℂ => b z) (S ∩ Metric.ball 0 1)
      exact hbd.mono Set.inter_subset_left)
    (fun z _ => F z) (fun z _ => f z)
    (differentiableOn_pi.mpr fun i => by
      fin_cases i
      exact hFd.mono Set.inter_subset_left)
    (differentiableOn_pi.mpr fun i => by
      fin_cases i
      exact hfd)
    (fun z hz => by
      rw [hasDerivAt_pi]
      intro _
      simpa [Fin.sum_univ_one] using hFode z hz.1)
    (fun z hz => by
      rw [hasDerivAt_pi]
      intro _
      simpa [Fin.sum_univ_one] using hfode z hz)
    hz₀ (by funext i; simpa [F] using congrFun hY₀ 0)
  refine ⟨F, hFd, hFode, fun z hz => ?_⟩
  exact congrFun (heq hz) 0

/-! ## 5. The auxiliary points and the geometry of `SU`, `SL` -/

/-- `0 ∉ SU`, `1 ∉ SU`, `2 ∈ SU`. -/
lemma zero_notMem_SU : (0 : ℂ) ∉ SU := by
  intro h; have h' := mem_SU_iff.mp h; norm_num at h'
lemma one_notMem_SU : (1 : ℂ) ∉ SU := by
  intro h; have h' := mem_SU_iff.mp h; norm_num at h'
lemma two_mem_SU : (2 : ℂ) ∈ SU := by
  rw [mem_SU_iff]; norm_num

/-- `0 ∉ SL`, `1 ∉ SL`. -/
lemma zero_notMem_SL : (0 : ℂ) ∉ SL := by
  intro h; have h' := mem_SL_iff.mp h; norm_num at h'
lemma one_notMem_SL : (1 : ℂ) ∉ SL := by
  intro h; have h' := mem_SL_iff.mp h; norm_num at h'

/-- The point `i/2` lies in `SU ∩ ball 0 1`. -/
lemma I_half_mem_SU : (((1 / 2 : ℝ) : ℂ) * Complex.I) ∈ SU ∩ Metric.ball 0 1 := by
  have hre : ((((1 / 2 : ℝ) : ℂ) * Complex.I)).re = 0 := by simp
  have him : ((((1 / 2 : ℝ) : ℂ) * Complex.I)).im = 1 / 2 := by simp
  have hnorm : ‖(((1 / 2 : ℝ) : ℂ) * Complex.I)‖ = 1 / 2 := by
    rw [norm_mul]; simp
  refine ⟨?_, ?_⟩
  · rw [mem_SU_iff, hre, him]; norm_num
  · rw [Metric.mem_ball, dist_zero_right, hnorm]; norm_num

/-- The point `-i/2` lies in `SL ∩ ball 0 1`. -/
lemma neg_I_half_mem_SL : (-(((1 / 2 : ℝ) : ℂ) * Complex.I)) ∈ SL ∩ Metric.ball 0 1 := by
  have hre : (-(((1 / 2 : ℝ) : ℂ) * Complex.I)).re = 0 := by simp
  have him : (-(((1 / 2 : ℝ) : ℂ) * Complex.I)).im = -(1 / 2) := by simp
  have hnorm : ‖-(((1 / 2 : ℝ) : ℂ) * Complex.I)‖ = 1 / 2 := by
    rw [norm_neg, norm_mul]; simp
  refine ⟨?_, ?_⟩
  · rw [mem_SL_iff, hre, him]; norm_num
  · rw [Metric.mem_ball, dist_zero_right, hnorm]; norm_num

end


end Work.A14D
