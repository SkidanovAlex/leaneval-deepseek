/-
# ZeroFreeTables — HBTheorem1_complex_h4

The case `ord χ₁ = 4` of HB Lemma 9.5: for the exceptional pair `(χ₁, ρ₁)` of a quartic
character, `λ₁ = lamOf q ρ₁ ≥ 348/1000` for all large `q`.

Route.  Take the Liu–Wang pointwise inequality
`0 ≤ (1 + cos θ)(1 + 2 cos θ)² = 5 + 8 cos θ + 4 cos 2θ + cos 3θ`
at `cos θ = Re(χ₁(n) n^{-iν})` (`ν = Im ρ₁`), summed against `Λ(n) n^{-β} f(log n / log q)`:
`0 ≤ 5·K(β,χ₀) + 8·K(β+iν,χ₁) + 4·K(β+2iν,χ₁²) + K(β+3iν,χ₁³)`
(`ksum_trigPoly_nonneg`).  Bound the four terms by HB Lemma 5.3 (principal character) and
HB Lemma 5.2 with the parametric constant `c = 1/8` (the φ = 1/4 small-order input): the
`χ₁`-term keeps its exceptional zero `ρ₁`, giving `-log q·F(0)` (the main negative term),
while the `χ₁²`- and `χ₁³`-terms are dropped (all their window zeros have `λ ≥ λ₁` by the wide
minimality `IsMin1WideAt 10`).  With HB Lemma 7.2's test function `f = tf72f (3/4)` this gives
`0 ≤ log q·[5F(-λ₁) - 8F(0) + (13/8) f(0)] + O(ε log q)`, and the numeric values
`F(0) = 8/9`, `f(0) = 4/5`, `F(-λ₁) ≤ 1147/1000` for `λ₁ ≤ 348/1000` make the bracket negative.

The `λ = 1/8` inputs come from the proved short-order versions of HB Lemma 3.1:
`Work.ZeroFreeTables.L31ord.lemma3_1_free_ord` for primitive characters of order `≤ log N`
(used for `χ₁` and `χ₁³`, whose conductor is `≥ 55`), and
`Work.LinnikAreas.l31free.lemma3_1_free_gen_real` together with
`Work.ZeroFreeTables.Table4.QuarterBoundReal` for the real character `χ₁²` (any conductor).
If the conductor of `χ₁` is below `55`, the proved uniform zero-free regions
(`LFunction_zeroFree_offAxis_uniform`, `LFunction_zeroFree_uniform_realAxis`) applied to the
primitive character of conductor `≤ 54` finish the job.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.ksum_trigPoly_nonneg
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound
import Submission.Work.ZeroFreeTables.l31_ord
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen_real
import Submission.Work.LinnikAreas.area1
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg
import Submission.Work.ZeroFreeTables.Table4.QuarterBoundReal
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Commons.NumberTheory.Linnik.Ksum_principal_le
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
import Submission.Work.ZeroFreeTables.H4.Tf72FNegLamLe

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The Liu–Wang combination -/

/-- The Chebyshev polynomial of the Liu–Wang inequality: for `x ∈ [-1,1]`,
`5·T₀(x) + 8·T₁(x) + 4·T₂(x) + T₃(x) = (1+x)(1+2x)² ≥ 0`. -/
theorem liuWang_poly_nonneg (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ 5 * (Polynomial.Chebyshev.T ℝ (0 : ℤ)).eval x
      + 8 * (Polynomial.Chebyshev.T ℝ (1 : ℤ)).eval x
      + 4 * (Polynomial.Chebyshev.T ℝ (2 : ℤ)).eval x
      + (Polynomial.Chebyshev.T ℝ (3 : ℤ)).eval x := by
  have h0 : (Polynomial.Chebyshev.T ℝ (0 : ℤ)).eval x = 1 := by
    rw [Polynomial.Chebyshev.T_zero]; simp
  have h1 : (Polynomial.Chebyshev.T ℝ (1 : ℤ)).eval x = x := by
    rw [Polynomial.Chebyshev.T_one]; simp
  have h2 : (Polynomial.Chebyshev.T ℝ (2 : ℤ)).eval x = 2 * x ^ 2 - 1 := by
    rw [Polynomial.Chebyshev.T_two]; simp
  have h3 : (Polynomial.Chebyshev.T ℝ (3 : ℤ)).eval x = 4 * x ^ 3 - 3 * x := by
    have hrec : (Polynomial.Chebyshev.T ℝ (3 : ℤ)) =
        2 * Polynomial.X * Polynomial.Chebyshev.T ℝ (2 : ℤ) - Polynomial.Chebyshev.T ℝ (1 : ℤ) := by
      have h := Polynomial.Chebyshev.T_add_two (R := ℝ) 1
      simpa using h
    rw [hrec]
    simp [Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one]
    ring
  rw [h0, h1, h2, h3]
  have hfac : 5 * 1 + 8 * x + 4 * (2 * x ^ 2 - 1) + (4 * x ^ 3 - 3 * x)
      = (1 + x) * (1 + 2 * x) ^ 2 := by ring
  rw [hfac]
  have h1x : 0 ≤ 1 + x := by linarith [hx.1]
  exact mul_nonneg h1x (sq_nonneg _)

/-- **The Liu–Wang combination of Heath-Brown `K`-sums** for a quartic character:
`0 ≤ 5K(β,χ₀) + 8K(β+iν,χ) + 4K(β+2iν,χ²) + K(β+3iν,χ³)`. -/
theorem liuWang_combination {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 ≤ f t)
    {x₀ L β ν : ℝ} (hL : 0 < L) (hx₀ : 0 ≤ x₀) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    (χ : DirichletCharacter ℂ q) :
    0 ≤ 5 * Ksum q f L (β : ℂ) 1
      + 8 * Ksum q f L ((β : ℂ) + (ν : ℂ) * Complex.I) χ
      + 4 * Ksum q f L ((β : ℂ) + 2 * (ν : ℂ) * Complex.I) (χ ^ 2)
      + Ksum q f L ((β : ℂ) + 3 * (ν : ℂ) * Complex.I) (χ ^ 3) := by
  set c : ℕ → ℝ := fun k => if k = 0 then 5 else if k = 1 then 8 else if k = 2 then 4 else if k = 3 then 1 else 0
    with hc
  have hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ ∑ k ∈ Finset.range (3 + 1), c k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x := by
    intro x hx
    have hsum : ∑ k ∈ Finset.range (3 + 1), c k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x
        = 5 * (Polynomial.Chebyshev.T ℝ (0 : ℤ)).eval x
          + 8 * (Polynomial.Chebyshev.T ℝ (1 : ℤ)).eval x
          + 4 * (Polynomial.Chebyshev.T ℝ (2 : ℤ)).eval x
          + (Polynomial.Chebyshev.T ℝ (3 : ℤ)).eval x := by
      simp [hc, Finset.sum_range_succ]
    rw [hsum]
    exact liuWang_poly_nonneg x hx
  have hmain := ksum_trigPoly_nonneg (q := q) (f := f) hf (x₀ := x₀) (L := L) (β := β)
    (γ := ν) hL hx₀ hsupp (c := c) (d := 3) hP χ
  have hexp : ∑ k ∈ Finset.range (3 + 1), c k *
      Ksum q f L ((β : ℂ) + ((k : ℝ) * ν : ℂ) * Complex.I) (χ ^ k)
      = 5 * Ksum q f L (β : ℂ) 1
        + 8 * Ksum q f L ((β : ℂ) + (ν : ℂ) * Complex.I) χ
        + 4 * Ksum q f L ((β : ℂ) + 2 * (ν : ℂ) * Complex.I) (χ ^ 2)
        + Ksum q f L ((β : ℂ) + 3 * (ν : ℂ) * Complex.I) (χ ^ 3) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc, pow_zero, pow_one, pow_two, pow_succ]
    norm_num
  rwa [hexp] at hmain

/-- The primitive character inducing a non-principal character is non-principal. -/
theorem primitive_ne_one_aux {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  apply hχ
  rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
  exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level

/-- `Ksum`, unfolded. -/
theorem Ksum_def' (q : ℕ) [NeZero q] (f : ℝ → ℝ) (L : ℝ) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    Ksum q f L s χ = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / L) := rfl

/-- If `u` lies in the `δ`-window of the line `1 + i·Im s`, with `|Im s| ≤ 3` and `δ < 1`, then
`|Im u| ≤ 10`. -/
theorem abs_im_le_ten_of_window {s u : ℂ} {δ : ℝ} (hδ : δ < 1) (hs : |s.im| ≤ 3)
    (h : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) : |u.im| ≤ 10 := by
  have h3 := Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)
  have h3b : (((1 : ℂ) + (s.im : ℂ) * Complex.I - u)).im = s.im - u.im := by simp
  rw [h3b, abs_sub_comm] at h3
  have h4 : |u.im| ≤ |u.im - s.im| + |s.im| := by
    calc |u.im| = |(u.im - s.im) + s.im| := by ring_nf
      _ ≤ |u.im - s.im| + |s.im| := abs_add_le _ _
  linarith

/-- The conductor of a character of level `q ≠ 0`, as a real number, is positive. -/
lemma conductor_cast_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (0 : ℝ) < ((χ.conductor : ℕ) : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero)

/-- A `zeroMult` zero of `χ` is a zero of the divisor of the completed `L`-function of the
primitive character inducing `χ`. -/
theorem divisor_ne_zero_of_zeroMult_aux {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) {R : ℝ} {u : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) R) (hzm : zeroMult χ u ≠ 0) :
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 R)) u ≠ 0 := by
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction
      (primitive_ne_one_aux χ hχ)).analyticAt z
  have hcast : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R)) u =
      ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u : ℕ) : ℤ) :=
    Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu
  have hnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
    revert hzm
    simp only [zeroMult]
    intro h; exact h
  intro h0
  rw [hcast] at h0
  exact hnat (by exact_mod_cast h0)

/-! ## Helper lemmas for the transport of zeros and `L`-function zeros -/

/-- A window zero (positive order of the completed `L`-function of the primitive character) is a
`zeroMult` zero of `χ`. -/
theorem zeroMult_ne_zero_of_divisor_aux {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) {R : ℝ} {u : ℂ}
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 R)) u ≠ 0) : zeroMult χ u ≠ 0 := by
  have hu : u ∈ Metric.closedBall (0 : ℂ) R :=
    Commons.Analysis.Complex.divisor_mem_of_ne_zero hdiv
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction
      (primitive_ne_one_aux χ hχ)).analyticAt z
  have hcast : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R)) u =
      ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u : ℕ) : ℤ) :=
    Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu
  have hnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
    intro h0
    exact hdiv (by rw [hcast, h0]; rfl)
  revert hnat
  simp only [zeroMult]
  intro h; exact h

/-- A `zeroMult` zero of `χ` is a zero of the ordinary `L`-function of the primitive character
inducing `χ`. -/
theorem LFunction_prim_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) {u : ℂ} (h : zeroMult χ u ≠ 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter u = 0 := by
  have hΛ : DirichletCharacter.completedLFunction χ.primitiveCharacter u = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (by simpa only [zeroMult] using h)
  have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter
    (primitive_ne_one_aux χ hχ) (DirichletCharacter.primitiveCharacter_isPrimitive χ) hΛ
  have hordC : analyticOrderNatAt
      (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
    simpa only [zeroMult] using h
  have hord := Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
    χ.primitiveCharacter (primitive_ne_one_aux χ hχ) hstrip.1 hstrip.2
  have hordL : analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) u ≠ 0 := by
    rw [hord]; exact hordC
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hordL


/-- **The large-conductor case of HB Lemma 9.5 for `ord χ₁ = 4`**: the F-method with the
Liu–Wang combination.  The value of the test-function transform at `-λ₁` is supplied as a
hypothesis (discharged by `H4.Tf72FNegLamLe`). -/
theorem hbTheorem1_complex_h4_large
    (hFval : ∀ lam₁ : ℝ, 0 ≤ lam₁ → lam₁ ≤ 87 / 250 →
      ∫ t in (0 : ℝ)..(8 / 3), Real.exp (lam₁ * t) * tf72f (3 / 4) t ≤ 1147 / 1000) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → orderOf χ₁ = 4 → 1000 ≤ χ₁.conductor →
        (348 : ℝ) / 1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  classical
  set ε : ℝ := 1 / 10000 with hεdef
  have hε : 0 < ε := by norm_num [hεdef]
  set f : ℝ → ℝ := tf72f (3 / 4) with hfdef
  have h34 : (0 : ℝ) < 3 / 4 := by norm_num
  have hfcont : ContinuousOn f (Set.Ici 0) := by rw [hfdef]; exact tf72f_cont _ h34
  have hfsupp : ∀ t : ℝ, 8 / 3 ≤ t → f t = 0 := by
    intro t ht
    have h2 : (2 : ℝ) / (3 / 4) = 8 / 3 := by norm_num
    rw [hfdef]
    exact tf72f_supp _ h34 t (by rw [h2]; exact ht)
  have hfdiff : ContDiffOn ℝ 2 f (Set.Ioo 0 (8 / 3)) := by
    have h2 : (2 : ℝ) / (3 / 4) = 8 / 3 := by norm_num
    rw [hfdef, ← h2]
    exact tf72f_diff _ h34
  obtain ⟨B, hB0, hBnd⟩ := tf72f_bound (3 / 4) h34
  have hfB : ∀ t ∈ Set.Ioo (0 : ℝ) (8 / 3), ‖iteratedDeriv 2 f t‖ ≤ B := by
    intro t ht
    have h2 : (2 : ℝ) / (3 / 4) = 8 / 3 := by norm_num
    rw [hfdef]
    exact hBnd t (by rwa [← h2] at ht)
  have hfnn : ∀ t : ℝ, 0 ≤ f t := by rw [hfdef]; exact tf72f_nonneg _ h34
  have hf0pos : 0 < f 0 := by rw [hfdef, tf72f_at_zero _ h34]; norm_num
  have hf0val : f 0 = 4 / 5 := by rw [hfdef, tf72f_at_zero _ h34]; norm_num
  have hFc : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0 : ℝ)..(8 / 3), Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re := by
    intro z hz
    have h2 : (2 : ℝ) / (3 / 4) = 8 / 3 := by norm_num
    have h := tf72Fc_re_nonneg (3 / 4) h34 z hz
    rw [hfdef, ← h2]
    exact h
  have hF0 : (∫ t in (0 : ℝ)..(8 / 3), f t) = 8 / 9 := by
    have h2 : (2 : ℝ) / (3 / 4) = 8 / 3 := by norm_num
    rw [hfdef, ← h2]
    exact tf72f_intervalIntegral _ h34
  obtain ⟨qP, hKP⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le (8 / 3) B (by norm_num) hB0 (f := f) hfcont hfsupp hfdiff hfB hε hf0pos
  obtain ⟨L₀₄, δ₄, hδ₄0, hδ₄1, hfree4⟩ :=
    L31ord.lemma3_1_free_ord (φ := (1 : ℝ) / 4) (by norm_num) (ε := ε / 4) (by positivity)
      Work.LinnikAreas.LBoundSmall_holds
  obtain ⟨L₀₂, δ₂, hδ₂0, hδ₂1, hreal⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen_real (φ := (1 : ℝ) / 4) (by norm_num)
      (ε := ε / 4) (by positivity)
      (fun k hk ε' hε' => Work.ZeroFreeTables.Table4.QuarterBoundReal k hk hε')
  obtain ⟨qS, hKS⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi (8 / 3) B (1 / 8) (by norm_num) hB0 (f := f) hfcont
    hfsupp hfdiff hfB hf0pos hFc hε hδ₄0 hδ₄1
  obtain ⟨qT₁, hKT1⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi (8 / 3) B (1 / 8) (by norm_num) hB0 (f := f) hfcont
    hfsupp hfdiff hfB hf0pos hFc hε hδ₄0 hδ₄1
  obtain ⟨qT₂, hKT2⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi (8 / 3) B (1 / 8) (by norm_num) hB0 (f := f) hfcont
    hfsupp hfdiff hfB hf0pos hFc hε hδ₂0 hδ₂1
  refine ⟨qP + qS + qT₁ + qT₂ + (Nat.ceil (Real.exp (max L₀₄ L₀₂)) + 2)
      + (Nat.ceil (Real.exp (87 / (250 * δ₄))) + 1) + 1000000, ?_⟩
  intro q hq hqne χ₁ ρ₁ hm hord hbig
  have hqP : qP ≤ q := by omega
  have hqS : qS ≤ q := by omega
  have hqT₁ : qT₁ ≤ q := by omega
  have hqT₂ : qT₂ ≤ q := by omega
  have hqL₀ : Nat.ceil (Real.exp (max L₀₄ L₀₂)) + 2 ≤ q := by omega
  have hqδ : Nat.ceil (Real.exp (87 / (250 * δ₄))) + 1 ≤ q := by omega
  have hqmillion : 1000000 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  haveI : NeZero q := hqne
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hL₀₄le : L₀₄ ≤ Real.log (q : ℝ) := by
    have h3 : (Nat.ceil (Real.exp (max L₀₄ L₀₂)) : ℝ) ≤ (q : ℝ) :=
      by exact_mod_cast (by omega : Nat.ceil (Real.exp (max L₀₄ L₀₂)) ≤ q)
    have hcpos : (0 : ℝ) < (Nat.ceil (Real.exp (max L₀₄ L₀₂)) : ℝ) :=
      lt_of_lt_of_le (Real.exp_pos _) (Nat.le_ceil _)
    calc L₀₄ ≤ max L₀₄ L₀₂ := le_max_left _ _
      _ = Real.log (Real.exp (max L₀₄ L₀₂)) := (Real.log_exp _).symm
      _ ≤ Real.log (Nat.ceil (Real.exp (max L₀₄ L₀₂)) : ℝ) :=
          Real.log_le_log (Real.exp_pos _) (Nat.le_ceil _)
      _ ≤ Real.log (q : ℝ) := Real.log_le_log hcpos h3
  have hL₀₂le : L₀₂ ≤ Real.log (q : ℝ) := by
    have h3 : (Nat.ceil (Real.exp (max L₀₄ L₀₂)) : ℝ) ≤ (q : ℝ) :=
      by exact_mod_cast (by omega : Nat.ceil (Real.exp (max L₀₄ L₀₂)) ≤ q)
    have hcpos : (0 : ℝ) < (Nat.ceil (Real.exp (max L₀₄ L₀₂)) : ℝ) :=
      lt_of_lt_of_le (Real.exp_pos _) (Nat.le_ceil _)
    calc L₀₂ ≤ max L₀₄ L₀₂ := le_max_right _ _
      _ = Real.log (Real.exp (max L₀₄ L₀₂)) := (Real.log_exp _).symm
      _ ≤ Real.log (Nat.ceil (Real.exp (max L₀₄ L₀₂)) : ℝ) :=
          Real.log_le_log (Real.exp_pos _) (Nat.le_ceil _)
      _ ≤ Real.log (q : ℝ) := Real.log_le_log hcpos h3
  have hδ4log : 87 / 250 ≤ δ₄ * Real.log (q : ℝ) := by
    have h3 : Real.exp (87 / (250 * δ₄)) ≤ (q : ℝ) := by
      have h1 : Real.exp (87 / (250 * δ₄))
          ≤ (Nat.ceil (Real.exp (87 / (250 * δ₄))) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (Real.exp (87 / (250 * δ₄))) : ℝ) ≤ (q : ℝ) :=
        by exact_mod_cast (by omega : Nat.ceil (Real.exp (87 / (250 * δ₄))) ≤ q)
      linarith
    have h4 : 87 / (250 * δ₄) ≤ Real.log (q : ℝ) := by
      rw [Real.le_log_iff_exp_le hqpos]
      exact h3
    calc 87 / 250 = δ₄ * (87 / (250 * δ₄)) := by field_simp
      _ ≤ δ₄ * Real.log (q : ℝ) := mul_le_mul_of_nonneg_left h4 hδ₄0.le
  have hχ1 : χ₁ ≠ 1 := hm.1.1.1
  have hzm1 : zeroMult χ₁ ρ₁ ≠ 0 := hm.1.1.2.1
  have hν1 : |ρ₁.im| ≤ 1 := hm.1.1.2.2
  have hwide := hm.2
  haveI hcond1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hconle : (χ₁.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (by omega) χ₁.conductor_dvd_level
  have hlam_nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq2 hm.1.1
  by_contra hcon
  push_neg at hcon
  have hlt : Work.LinnikContract.lamOf q ρ₁ ≤ 87 / 250 := by
    have h348 : (348 : ℝ) / 1000 = 87 / 250 := by norm_num
    linarith [hcon, h348.le, h348.ge]
  have hlog6 : (6 : ℝ) ≤ Real.log (q : ℝ) := by
    have h6 : (1000000 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqmillion
    have h7 := Real.log_le_log (by norm_num : (0 : ℝ) < 1000000) h6
    have h8 : Real.log (1000000 : ℝ) = 6 * Real.log 10 := by
      rw [show (1000000 : ℝ) = 10 ^ 6 by norm_num, Real.log_pow]; norm_num
    have h9 : (2 : ℝ) ≤ Real.log 10 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10)]
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    rw [h8] at h7; linarith
  have hsqrtge : (348 : ℝ) / 1000 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have h4 : (348 : ℝ) / 1000 ≤ Real.log (Real.log (q : ℝ)) := by
      have h5 : Real.log 6 ≤ Real.log (Real.log (q : ℝ)) := Real.log_le_log (by norm_num) hlog6
      have h6 : (348 : ℝ) / 1000 ≤ Real.log 6 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        have h7 : Real.exp (348 / 1000) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
        linarith [Real.exp_one_lt_three, h7]
      linarith [h5, h6]
    calc (348 : ℝ) / 1000 ≤ Real.sqrt ((348 : ℝ) / 1000) := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      _ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := Real.sqrt_le_sqrt h4
  have hβ : |ρ₁.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have h1 : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q : ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    have h2 : |ρ₁.re - 1| = 1 - ρ₁.re := by
      have h3 : 0 ≤ 1 - ρ₁.re := by rw [h1]; exact div_nonneg hlam_nn hlogq.le
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [h2, h1]
    rw [div_le_div_iff₀ hlogq hlogq]
    nlinarith [hlt, hsqrtge, hlogq]
  -- ## order bookkeeping
  have h4one : χ₁ ^ 4 = 1 := by
    have hd : orderOf χ₁ ∣ 4 := hord ▸ dvd_rfl
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  have h3inv : χ₁ ^ 3 = χ₁⁻¹ := by
    have h : χ₁ ^ 3 * χ₁ = 1 := by
      have h2 : χ₁ ^ 3 * χ₁ = χ₁ ^ 4 := by group
      rw [h2, h4one]
    exact eq_inv_of_mul_eq_one_left h
  have hχ3ne : χ₁ ^ 3 ≠ 1 := by
    intro h
    have h1 : orderOf (χ₁ ^ 3) = 1 := orderOf_eq_one_iff.mpr h
    have h2 : orderOf (χ₁ ^ 3) = 4 := by rw [h3inv, orderOf_inv, hord]
    omega
  have hχ2ne : χ₁ ^ 2 ≠ 1 := by
    intro h
    have hd : orderOf χ₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    have h4dvd : (4 : ℕ) ∣ 2 := by rw [← hord]; exact hd
    have hle : 4 ≤ 2 := Nat.le_of_dvd (by norm_num) h4dvd
    omega
  have hord3 : orderOf (χ₁ ^ 3) = 4 := by rw [h3inv, orderOf_inv, hord]
  have hcond3 : (χ₁ ^ 3).conductor = χ₁.conductor := by
    rw [h3inv, DirichletCharacter.conductor_inv]
  haveI hcond3' : NeZero (χ₁ ^ 3).conductor := by rw [hcond3]; exact hcond1
  have hord2 : orderOf (χ₁ ^ 2) = 2 := by
    have hdvd : orderOf (χ₁ ^ 2) ∣ 2 := by
      apply orderOf_dvd_iff_pow_eq_one.mpr
      calc (χ₁ ^ 2) ^ 2 = χ₁ ^ 4 := by group
        _ = 1 := h4one
    have hne1 : orderOf (χ₁ ^ 2) ≠ 1 := by
      intro h1
      exact hχ2ne (orderOf_eq_one_iff.mp h1)
    rcases (by norm_num : Nat.Prime 2).eq_one_or_self_of_dvd (orderOf (χ₁ ^ 2)) hdvd with h1 | h2
    · exact absurd h1 hne1
    · exact h2
  haveI hcond2' : NeZero (χ₁ ^ 2).conductor := ⟨(χ₁ ^ 2).conductor_ne_zero⟩
  have hsqq : ((χ₁ ^ 2).primitiveCharacter) ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one,
      Commons.NumberTheory.DirichletCharacter.orderOf_primitiveCharacter, hord2]
  have hcond2ge : 3 ≤ (χ₁ ^ 2).conductor := by
    by_contra hc
    have hN : (χ₁ ^ 2).conductor ≤ 2 := by omega
    exact hχ2ne (Work.LinnikAreas.eq_one_of_conductor_le_two (χ₁ ^ 2) hN)
  have hordprim1 : orderOf χ₁.primitiveCharacter = 4 := by
    rw [Commons.NumberTheory.DirichletCharacter.orderOf_primitiveCharacter, hord]
  have hordprim3 : orderOf (χ₁ ^ 3).primitiveCharacter = 4 := by
    rw [Commons.NumberTheory.DirichletCharacter.orderOf_primitiveCharacter, hord3]
  have hcpos : (0 : ℝ) < ((χ₁.conductor : ℕ) : ℝ) := conductor_cast_pos χ₁
  have hlogM1 : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hcpos hconle
  have h4log : (4 : ℝ) ≤ Real.log ((χ₁.conductor : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le hcpos]
    have h81 : Real.exp 4 < 81 := by
      have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
        simpa using (Real.exp_nat_mul 1 4)
      rw [h4, show Real.exp 1 ^ 4 = (Real.exp 1 ^ 2) ^ 2 by ring,
        show (81 : ℝ) = 9 ^ 2 by norm_num, sq_lt_sq,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.exp 1 ^ 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (9 : ℝ))]
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    have h1000 : (81 : ℝ) ≤ ((χ₁.conductor : ℕ) : ℝ) := by
      have h1 : (1000 : ℝ) ≤ ((χ₁.conductor : ℕ) : ℝ) := by exact_mod_cast hbig
      linarith
    linarith
  -- ## the Lemma 5.2 hypotheses
  have hφval : (1 : ℝ) / 4 / 2 = 1 / 8 := by norm_num
  have hL52_1 : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8) ε δ₄ := by
    intro s hs1 hs2 hs3
    have h := hfree4 (by omega : 3 ≤ χ₁.conductor) χ₁.primitiveCharacter
      (primitive_ne_one_aux χ₁ hχ1) (DirichletCharacter.primitiveCharacter_isPrimitive χ₁)
      (by rw [hordprim1]; exact h4log) (L := Real.log (q : ℝ)) hL₀₄le hlogM1 s hs1 hs2 hs3
    rw [hφval] at h
    exact h
  have hL52_3 : Commons.NumberTheory.Linnik.L52Hyp (χ₁ ^ 3) (1 / 8) ε δ₄ := by
    intro s hs1 hs2 hs3
    have h4log' : (4 : ℝ) ≤ Real.log (((χ₁ ^ 3).conductor : ℕ) : ℝ) := by
      rw [hcond3]; exact h4log
    have hlog3 : Real.log (((χ₁ ^ 3).conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
      rw [hcond3]; exact hlogM1
    have h3le : 3 ≤ (χ₁ ^ 3).conductor := by rw [hcond3]; omega
    have h := hfree4 h3le (χ₁ ^ 3).primitiveCharacter (primitive_ne_one_aux (χ₁ ^ 3) hχ3ne)
      (DirichletCharacter.primitiveCharacter_isPrimitive (χ₁ ^ 3))
      (by rw [hordprim3]; exact h4log') (L := Real.log (q : ℝ)) hL₀₄le hlog3 s hs1 hs2 hs3
    rw [hφval] at h
    exact h
  have hL52_2 : Commons.NumberTheory.Linnik.L52Hyp (χ₁ ^ 2) (1 / 8) ε δ₂ := by
    intro s hs1 hs2 hs3
    have hcon2le : (((χ₁ ^ 2).conductor : ℕ) : ℝ) ≤ (q : ℝ) := by
      have hdvd : (χ₁ ^ 2).conductor ∣ q := (χ₁ ^ 2).conductor_dvd_level
      exact_mod_cast Nat.le_of_dvd (by omega : 0 < q) hdvd
    have hlog2 : Real.log (((χ₁ ^ 2).conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (conductor_cast_pos (χ₁ ^ 2)) hcon2le
    have h := hreal hcond2ge (χ₁ ^ 2).primitiveCharacter (primitive_ne_one_aux (χ₁ ^ 2) hχ2ne)
      (DirichletCharacter.primitiveCharacter_isPrimitive (χ₁ ^ 2)) hsqq
      (L := Real.log (q : ℝ)) hL₀₂le hlog2 s hs1 hs2 hs3
    rw [hφval] at h
    exact h
  -- ## the window hypotheses for the exceptional zero
  have hnn1 : 0 ≤ 1 - ρ₁.re := by
    have h2 : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q : ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [h2]; exact div_nonneg hlam_nn hlogq.le
  have hstrip1 : 0 < ρ₁.re ∧ ρ₁.re < 1 :=
    Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter
      (primitive_ne_one_aux χ₁ hχ1) (DirichletCharacter.primitiveCharacter_isPrimitive χ₁)
      (apply_eq_zero_of_analyticOrderNatAt_ne_zero (by simpa only [zeroMult] using hzm1))
  have hmem1 : ρ₁ ∈ Metric.closedBall (0 : ℂ) (|ρ₁.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |ρ₁.re| ≤ 1 := by rw [abs_of_pos hstrip1.1]; exact hstrip1.2.le
    calc ‖ρ₁‖ ≤ |ρ₁.re| + |ρ₁.im| := Complex.norm_le_abs_re_add_abs_im ρ₁
      _ ≤ |ρ₁.im| + 1 := by linarith
      _ ≤ |ρ₁.im| + 2 := by linarith
  have hwinpred : ‖(1 : ℂ) + (((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I).im : ℂ) * Complex.I - ρ₁‖
      ≤ δ₄ := by
    have h1 : (1 : ℂ) + (((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I).im : ℂ) * Complex.I - ρ₁
        = ((1 - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn1]
    have h2 : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q : ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [h2, div_le_iff₀ hlogq]
    nlinarith [hlt, hδ4log]
  have hwin1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I).im| + 2))) ρ₁ ≠ 0 :=
    divisor_ne_zero_of_zeroMult_aux χ₁ hχ1 (by simpa using hmem1) hzm1
  have hslo1 : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ ρ₁.re := by
    have h1 : -|ρ₁.re - 1| ≤ ρ₁.re - 1 := neg_abs_le _
    linarith [hβ, h1]
  have hsim1 : |ρ₁.im| ≤ 10 * Real.log (q : ℝ) := by
    have h10 : (1 : ℝ) ≤ 10 * Real.log (q : ℝ) := by linarith [hlog6]
    linarith [hν1]
  have hsi1 : ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I).im = ρ₁.im := by simp
  have hsr1 : ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I).re = ρ₁.re := by simp
  have hsr2 : ((ρ₁.re : ℂ) + 2 * (ρ₁.im : ℂ) * Complex.I).re = ρ₁.re := by simp
  have hsi2 : ((ρ₁.re : ℂ) + 2 * (ρ₁.im : ℂ) * Complex.I).im = 2 * ρ₁.im := by simp
  have hsr3 : ((ρ₁.re : ℂ) + 3 * (ρ₁.im : ℂ) * Complex.I).re = ρ₁.re := by simp
  have hsi3 : ((ρ₁.re : ℂ) + 3 * (ρ₁.im : ℂ) * Complex.I).im = 3 * ρ₁.im := by simp
  have hsim2 : |((ρ₁.re : ℂ) + 2 * (ρ₁.im : ℂ) * Complex.I).im| ≤ 10 * Real.log (q : ℝ) := by
    rw [hsi2]
    have h2 : |2 * ρ₁.im| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [hν1]
    linarith [hlog6, h2]
  have hsim3 : |((ρ₁.re : ℂ) + 3 * (ρ₁.im : ℂ) * Complex.I).im| ≤ 10 * Real.log (q : ℝ) := by
    rw [hsi3]
    have h2 : |3 * ρ₁.im| ≤ 3 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      linarith [hν1]
    linarith [hlog6, h2]
  have hzw1 : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I).im| + 2))) u ≠ 0 →
      ‖(1 : ℂ) + (((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I).im : ℂ) * Complex.I - u‖ ≤ δ₄ →
      u.re ≤ ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I).re := by
    intro u hdiv hwin
    have hzm : zeroMult χ₁ u ≠ 0 := zeroMult_ne_zero_of_divisor_aux χ₁ hχ1 hdiv
    have huim : |u.im| ≤ 10 :=
      abs_im_le_ten_of_window hδ₄1 (by rw [hsi1]; linarith [hν1]) hwin
    have hle := hwide χ₁ u hχ1 hzm huim
    rw [show Work.LinnikContract.lamOf q u = (1 - u.re) * Real.log (q : ℝ) from rfl,
      show Work.LinnikContract.lamOf q ρ₁ = (1 - ρ₁.re) * Real.log (q : ℝ) from rfl] at hle
    rw [hsr1]
    nlinarith [hle, hlogq]
  have hzw2 : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction ((χ₁ ^ 2).primitiveCharacter))
      (Metric.closedBall 0 (|((ρ₁.re : ℂ) + 2 * (ρ₁.im : ℂ) * Complex.I).im| + 2))) u ≠ 0 →
      ‖(1 : ℂ) + (((ρ₁.re : ℂ) + 2 * (ρ₁.im : ℂ) * Complex.I).im : ℂ) * Complex.I - u‖ ≤ δ₂ →
      u.re ≤ ((ρ₁.re : ℂ) + 2 * (ρ₁.im : ℂ) * Complex.I).re := by
    intro u hdiv hwin
    have hzm : zeroMult (χ₁ ^ 2) u ≠ 0 := zeroMult_ne_zero_of_divisor_aux (χ₁ ^ 2) hχ2ne hdiv
    have huim : |u.im| ≤ 10 := by
      refine abs_im_le_ten_of_window hδ₂1 ?_ hwin
      rw [hsi2]
      have h2 : |2 * ρ₁.im| ≤ 2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith [hν1]
      linarith
    have hle := hwide (χ₁ ^ 2) u hχ2ne hzm huim
    rw [show Work.LinnikContract.lamOf q u = (1 - u.re) * Real.log (q : ℝ) from rfl,
      show Work.LinnikContract.lamOf q ρ₁ = (1 - ρ₁.re) * Real.log (q : ℝ) from rfl] at hle
    rw [hsr2]
    nlinarith [hle, hlogq]
  have hzw3 : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction ((χ₁ ^ 3).primitiveCharacter))
      (Metric.closedBall 0 (|((ρ₁.re : ℂ) + 3 * (ρ₁.im : ℂ) * Complex.I).im| + 2))) u ≠ 0 →
      ‖(1 : ℂ) + (((ρ₁.re : ℂ) + 3 * (ρ₁.im : ℂ) * Complex.I).im : ℂ) * Complex.I - u‖ ≤ δ₄ →
      u.re ≤ ((ρ₁.re : ℂ) + 3 * (ρ₁.im : ℂ) * Complex.I).re := by
    intro u hdiv hwin
    have hzm : zeroMult (χ₁ ^ 3) u ≠ 0 := zeroMult_ne_zero_of_divisor_aux (χ₁ ^ 3) hχ3ne hdiv
    have huim : |u.im| ≤ 10 := by
      refine abs_im_le_ten_of_window hδ₄1 ?_ hwin
      rw [hsi3]
      have h2 : |3 * ρ₁.im| ≤ 3 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
        linarith [hν1]
      linarith
    have hle := hwide (χ₁ ^ 3) u hχ3ne hzm huim
    rw [show Work.LinnikContract.lamOf q u = (1 - u.re) * Real.log (q : ℝ) from rfl,
      show Work.LinnikContract.lamOf q ρ₁ = (1 - ρ₁.re) * Real.log (q : ℝ) from rfl] at hle
    rw [hsr3]
    nlinarith [hle, hlogq]
  have hs_eq : ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁ = 0 :=
    sub_eq_zero.mpr (Complex.re_add_im ρ₁)
  have hF0c0 : (∫ t in (0 : ℝ)..(8 / 3),
      Complex.exp (-(((0 : ℂ) * (Real.log (q : ℝ)) * (t : ℂ)))) * ((f t : ℝ) : ℂ)).re = 8 / 9 := by
    have h1 : ∀ t : ℝ, Complex.exp (-(((0 : ℂ) * (Real.log (q : ℝ)) * (t : ℂ))))
        * ((f t : ℝ) : ℂ) = ((f t : ℝ) : ℂ) := by
      intro t
      rw [zero_mul, zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_congr (fun t _ => h1 t), intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_re]
    exact hF0
  -- ## the four `K`-bounds
  have hb1 : Ksum q f (Real.log (q : ℝ)) ((ρ₁.re : ℂ)) 1
      ≤ Real.log (q : ℝ) * (1147 / 1000) + f 0 * ε * Real.log (q : ℝ) := by
    have h := hKP (q := q) hqP (β := ρ₁.re) (lam := Work.LinnikContract.lamOf q ρ₁)
      (by rw [Work.LinnikContract.lamOf]; ring) hβ
    rw [← Ksum_def'] at h
    have h3 : (∫ t in (0 : ℝ)..(8 / 3),
        Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t) ≤ 1147 / 1000 :=
      hFval (Work.LinnikContract.lamOf q ρ₁) hlam_nn hlt
    have h4 : Real.log (q : ℝ) * (∫ t in (0 : ℝ)..(8 / 3),
        Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t) ≤ Real.log (q : ℝ) * (1147 / 1000) :=
      mul_le_mul_of_nonneg_left h3 hlogq.le
    linarith [h, h4]
  have hb2 : Ksum q f (Real.log (q : ℝ)) ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) χ₁
      ≤ -(Real.log (q : ℝ)) * (8 / 9) + f 0 * (1 / 8 + ε) * Real.log (q : ℝ) := by
    have h := hKS (q := q) hqS χ₁ hχ1 (s := (ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I)
      (ρ := ρ₁) (by rw [hsr1]; exact hβ) (by rw [hsi1]; exact hsim1)
      (by rw [hsr1]; exact hslo1) hL52_1 hwin1 hwinpred hzw1
    rw [hs_eq] at h
    rw [hF0c0] at h
    rw [← Ksum_def'] at h
    exact h
  have hb3 : Ksum q f (Real.log (q : ℝ)) ((ρ₁.re : ℂ) + 2 * (ρ₁.im : ℂ) * Complex.I) (χ₁ ^ 2)
      ≤ f 0 * (1 / 8 + ε) * Real.log (q : ℝ) := by
    have h := hKT2 (q := q) hqT₂ (χ₁ ^ 2) hχ2ne
      (s := (ρ₁.re : ℂ) + 2 * (ρ₁.im : ℂ) * Complex.I)
      (by rw [hsr2]; exact hβ) hsim2 (by rw [hsr2]; exact hslo1) hL52_2 hzw2
    rw [← Ksum_def'] at h
    exact h
  have hb4 : Ksum q f (Real.log (q : ℝ)) ((ρ₁.re : ℂ) + 3 * (ρ₁.im : ℂ) * Complex.I) (χ₁ ^ 3)
      ≤ f 0 * (1 / 8 + ε) * Real.log (q : ℝ) := by
    have h := hKT1 (q := q) hqT₁ (χ₁ ^ 3) hχ3ne
      (s := (ρ₁.re : ℂ) + 3 * (ρ₁.im : ℂ) * Complex.I)
      (by rw [hsr3]; exact hβ) hsim3 (by rw [hsr3]; exact hslo1) hL52_3 hzw3
    rw [← Ksum_def'] at h
    exact h
  -- ## the combination and the contradiction
  have hcomb := liuWang_combination (q := q) (f := f) hfnn (L := Real.log (q : ℝ))
    (x₀ := 8 / 3) (β := ρ₁.re) (ν := ρ₁.im) hlogq (by norm_num) hfsupp χ₁
  have hsum : 5 * Ksum q f (Real.log (q : ℝ)) ((ρ₁.re : ℂ)) 1
      + 8 * Ksum q f (Real.log (q : ℝ)) ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) χ₁
      + 4 * Ksum q f (Real.log (q : ℝ)) ((ρ₁.re : ℂ) + 2 * (ρ₁.im : ℂ) * Complex.I) (χ₁ ^ 2)
      + Ksum q f (Real.log (q : ℝ)) ((ρ₁.re : ℂ) + 3 * (ρ₁.im : ℂ) * Complex.I) (χ₁ ^ 3)
      ≤ Real.log (q : ℝ) * (5 * (1147 / 1000) - 8 * (8 / 9) + (13 / 8) * (4 / 5)
          + 18 * ε * (4 / 5)) := by
    have h1 := mul_le_mul_of_nonneg_left hb1 (by norm_num : (0 : ℝ) ≤ 5)
    have h2 := mul_le_mul_of_nonneg_left hb2 (by norm_num : (0 : ℝ) ≤ 8)
    have h3 := mul_le_mul_of_nonneg_left hb3 (by norm_num : (0 : ℝ) ≤ 4)
    rw [hf0val] at h1 h2 h3 hb4
    linarith [h1, h2, h3, hb4]
  have hneg : 5 * (1147 / 1000) - 8 * (8 / 9) + (13 / 8) * (4 / 5) + 18 * ε * (4 / 5) < 0 := by
    rw [hεdef]; norm_num
  have hlt0 : Real.log (q : ℝ) * (5 * (1147 / 1000) - 8 * (8 / 9) + (13 / 8) * (4 / 5)
      + 18 * ε * (4 / 5)) < 0 := mul_neg_of_pos_of_neg hlogq hneg
  linarith [hcomb, hsum, hlt0]
/-- **The small-conductor case of HB Lemma 9.5 for `ord χ₁ = 4`.**  A quartic character of
conductor at most `999` has no minimal zero with `λ₁ < 0.348` once `q` is large: the classical
zero-free regions for `L(s,χ)` — uniform off the real axis, and on it when `χ` is not real —
give `1 - Re ρ ≥ c₀ > 0` for every zero of the (fixed) character, whence
`λ₁ = (1 - Re ρ₁)·log q ≥ c₀ log q → ∞`. -/
theorem hbTheorem1_complex_h4_small : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → orderOf χ₁ = 4 → χ₁.conductor ≤ 999 →
      (348 : ℝ) / 1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  obtain ⟨c₂, hc₂pos, hc₂⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
  set c₀ : ℝ := min (c₁ / Real.log (999 * 3)) (c₂ / Real.log (2 * 999)) with hc₀def
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]
    exact lt_min (div_pos hc₁pos (Real.log_pos (by norm_num)))
      (div_pos hc₂pos (Real.log_pos (by norm_num)))
  have hc₀₁ : c₀ ≤ c₁ / Real.log (999 * 3) := by rw [hc₀def]; exact min_le_left _ _
  have hc₀₂ : c₀ ≤ c₂ / Real.log (2 * 999) := by rw [hc₀def]; exact min_le_right _ _
  refine ⟨Nat.ceil (Real.exp ((348 : ℝ) / 1000 / c₀)) + 1, ?_⟩
  intro q hq hqne χ₁ ρ₁ hm hord hcond
  haveI : NeZero q := hqne
  haveI hcond1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hlogq : (348 : ℝ) / 1000 / c₀ ≤ Real.log (q : ℝ) := by
    have h1 : Real.exp ((348 : ℝ) / 1000 / c₀)
        ≤ ((Nat.ceil (Real.exp ((348 : ℝ) / 1000 / c₀)) + 1 : ℕ) : ℝ) := by
      have h := Nat.le_ceil (Real.exp ((348 : ℝ) / 1000 / c₀))
      push_cast
      linarith
    have h2 : ((Nat.ceil (Real.exp ((348 : ℝ) / 1000 / c₀)) + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hq
    rw [Real.le_log_iff_exp_le hqpos]
    exact le_trans h1 h2
  have hχ1 : χ₁ ≠ 1 := hm.1.1.1
  have hzm : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hm.1.1.2.1
  have him1 : |ρ₁.im| ≤ 1 := hm.1.1.2.2
  have hcondnn : (0 : ℝ) < ((χ₁.conductor : ℕ) : ℝ) := conductor_cast_pos χ₁
  have hcondle : ((χ₁.conductor : ℕ) : ℝ) ≤ 999 := by exact_mod_cast hcond
  have hcondge1 : (1 : ℝ) ≤ ((χ₁.conductor : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ₁.conductor_ne_zero
  have hL0 : DirichletCharacter.LFunction χ₁.primitiveCharacter ρ₁ = 0 :=
    LFunction_prim_eq_zero χ₁ hχ1 hzm
  have hord4 : orderOf χ₁.primitiveCharacter = 4 := by
    rw [Commons.NumberTheory.DirichletCharacter.orderOf_primitiveCharacter, hord]
  have hsq : χ₁.primitiveCharacter * χ₁.primitiveCharacter ≠ 1 := by
    intro h
    have h2 : χ₁.primitiveCharacter ^ 2 = 1 := by rw [pow_two]; exact h
    have hd : orderOf χ₁.primitiveCharacter ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hord4] at hd
    have h42 : 4 ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega
  have hkey : c₀ ≤ 1 - ρ₁.re := by
    rcases eq_or_ne ρ₁.im 0 with him0 | himne
    · have hposN : 0 < Real.log (2 * ((χ₁.conductor : ℕ) : ℝ)) :=
        Real.log_pos (by linarith [hcondge1])
      have hlogN : Real.log (2 * ((χ₁.conductor : ℕ) : ℝ)) ≤ Real.log (2 * 999) :=
        Real.log_le_log (by positivity) (by linarith [hcondle])
      have hcc : c₂ / Real.log (2 * 999) ≤ c₂ / Real.log (2 * ((χ₁.conductor : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2 * 999)) hposN]
        nlinarith [hlogN, hc₂pos]
      by_contra hcon
      have hσ : 1 - c₂ / Real.log (2 * ((χ₁.conductor : ℕ) : ℝ)) ≤ ρ₁.re := by linarith
      have hne := hc₂ χ₁.conductor χ₁.primitiveCharacter
        (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) (primitive_ne_one_aux χ₁ hχ1) hsq
        ρ₁.re hσ
      have hρ : ((ρ₁.re : ℂ)) = ρ₁ := by
        have h := Complex.re_add_im ρ₁
        rw [him0] at h
        simpa using h
      rw [hρ] at hne
      exact absurd hL0 hne
    · have hposm : 0 < ((χ₁.conductor : ℕ) : ℝ) * (|ρ₁.im| + 2) :=
        by nlinarith [hcondnn, abs_nonneg ρ₁.im]
      have hlogm : Real.log (((χ₁.conductor : ℕ) : ℝ) * (|ρ₁.im| + 2)) ≤ Real.log (999 * 3) :=
        Real.log_le_log hposm (by nlinarith [hcondle, him1])
      have hcc : c₁ / Real.log (999 * 3) ≤ c₁ / Real.log (((χ₁.conductor : ℕ) : ℝ) * (|ρ₁.im| + 2)) := by
        rw [div_le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 999 * 3))
          (Real.log_pos (by nlinarith [hcondge1, abs_nonneg ρ₁.im]))]
        nlinarith [hlogm, hc₁pos]
      by_contra hcon
      have hσ : 1 - c₁ / Real.log (((χ₁.conductor : ℕ) : ℝ) * (|ρ₁.im| + 2)) ≤ ρ₁.re := by linarith
      have hne := hc₁ χ₁.primitiveCharacter (DirichletCharacter.primitiveCharacter_isPrimitive χ₁)
        (primitive_ne_one_aux χ₁ hχ1) ρ₁.re ρ₁.im himne hσ
      rw [Complex.re_add_im ρ₁] at hne
      exact absurd hL0 hne
  have hlam : Work.LinnikContract.lamOf q ρ₁ = (1 - ρ₁.re) * Real.log (q : ℝ) := rfl
  rw [hlam]
  have hlogqnn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hmul := mul_le_mul hkey hlogq (by positivity : (0 : ℝ) ≤ (348 : ℝ) / 1000 / c₀)
    (le_trans hc₀pos.le hkey)
  have hsimp : c₀ * ((348 : ℝ) / 1000 / c₀) = (348 : ℝ) / 1000 := by field_simp
  linarith [hmul, hsimp]

/-- **HB Lemma 9.5, the case `ord χ₁ = 4`** (Heath-Brown, PLMS (3) **64** (1992), Lemma 9.5):
for a quartic character `χ₁` and a minimal zero `ρ₁` of height `≤ 10`, `λ₁ ≥ 0.348` for all
sufficiently large moduli `q`. -/
theorem HBTheorem1_complex_h4 : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → orderOf χ₁ = 4 →
      (348 : ℝ) / 1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  obtain ⟨q₁, hq₁⟩ := hbTheorem1_complex_h4_large (fun lam h0 h1 => H4.Tf72FNegLamLe h0 h1)
  obtain ⟨q₂, hq₂⟩ := hbTheorem1_complex_h4_small
  refine ⟨max q₁ q₂, ?_⟩
  intro q hq hqne χ₁ ρ₁ hm hord
  by_cases hbig : 1000 ≤ χ₁.conductor
  · exact hq₁ q (le_trans (le_max_left _ _) hq) χ₁ ρ₁ hm hord hbig
  · exact hq₂ q (le_trans (le_max_right _ _) hq) χ₁ ρ₁ hm hord (by omega)

end Work.ZeroFreeTables
