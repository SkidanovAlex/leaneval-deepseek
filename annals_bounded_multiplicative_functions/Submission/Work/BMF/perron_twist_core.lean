import Mathlib
import Submission.Commons.Analysis.Complex.exists_perron_formula_bound
import Submission.Commons.NumberTheory.Zeta.mangoldtPerronError_bound
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # Twisted Perron/contour core for `N10` (`vk_prime_sums`)

The twisted truncated Perron formula for `Σ_{n ≤ x} χ(n)Λ(n) n^{-iu}` and the contour-shift
identity used by `Submission/Work/BMF/vk_prime_sums.lean`.

(Original guidance: ROUTE: read Submission/Work/BMF/DESIGN.md (the lead's design for MRTTZ; your node's section has exact formulas). Shared definitions: Submission/Work/BMF/Defs.lean (do NOT edit). Owned library assets (chen_theorem Mertens/PNT/Siegel–Walfisz/zero-free regions, annals_large_value_estimates mean-value theorems + halasz_bound, bourgain Weyl differencing, and a v4.34 port of the Vinogradov mean value theorem) are being copied into Submission/Commons/ and Submission/Vinogradov/ now. See DESIGN.md §8 for exact module names, and import them once they exist instead of re-proving. Siblings run in parallel.

# N10 `vk_prime_sums`: Vinogradov–Korobov prime sums, uniform in small moduli

See DESIGN.md §N10 and ASSETS.md for the owned library.  The parts of the route that are
formalised here:

* `chiLambdaTwist` and `perron_twisted` (step 4, the truncated Perron formula at the twisted
  point `1 + 1/log x + iu`, obtained from the generic
  `Commons.Analysis.Complex.exists_perron_formula_bound`);
* the target `vk_prime_sums` itself.
-/

namespace Work.BMF

open Polynomial

open scoped BigOperators

/-- The coefficient sequence `n ↦ χ(n)·Λ(n)·n^{-iu}` of the twisted von Mangoldt sum. -/
noncomputable def chiLambdaTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) : ℕ → ℂ :=
  fun n => χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))

lemma chiLambdaTwist_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) (n : ℕ) :
    ‖chiLambdaTwist χ u n‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one (n : ZMod q)
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  rcases eq_or_ne n 0 with h | h
  · subst h
    simp [chiLambdaTwist]
  · have hpow : ‖(n : ℂ) ^ (-(Complex.I * u))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
      simp
    calc ‖chiLambdaTwist χ u n‖
        = ‖χ n‖ * ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ *
            ‖(n : ℂ) ^ (-(Complex.I * u))‖ := by
          simp only [chiLambdaTwist, norm_mul]
      _ = ‖χ n‖ * (ArithmeticFunction.vonMangoldt n : ℝ) *
            ‖(n : ℂ) ^ (-(Complex.I * u))‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
      _ = ‖χ n‖ * (ArithmeticFunction.vonMangoldt n : ℝ) := by rw [hpow, mul_one]
      _ ≤ 1 * (ArithmeticFunction.vonMangoldt n : ℝ) := by gcongr
      _ = (ArithmeticFunction.vonMangoldt n : ℝ) := one_mul _

/-- Twisting a Dirichlet sequence by `n^{-iu}` shifts the L-series argument by `iu`. -/
lemma LSeries_mul_cpow_neg_I (a : ℕ → ℂ) (u : ℝ) (w : ℂ) :
    LSeries (fun n => a n * (n : ℂ) ^ (-(Complex.I * u))) w =
      LSeries a (w + (u : ℂ) * Complex.I) := by
  have h1 : ∀ n : ℕ, LSeries.term (fun n => a n * (n : ℂ) ^ (-(Complex.I * u))) w n
      = LSeries.term a (w + (u : ℂ) * Complex.I) n := by
    intro n
    rcases eq_or_ne n 0 with h | h
    · subst h; simp [LSeries.term_zero]
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast h
      rw [LSeries.term_of_ne_zero h, LSeries.term_of_ne_zero h]
      rw [mul_div_assoc, div_eq_mul_inv, div_eq_mul_inv,
        ← Complex.cpow_neg ((n : ℂ)) (w + (u : ℂ) * Complex.I),
        ← Complex.cpow_neg ((n : ℂ)) w,
        ← Complex.cpow_add (-(Complex.I * u)) (-w) hn0]
      rw [show (-(Complex.I * u)) + (-w) = -(w + (u : ℂ) * Complex.I) by ring]
  simp only [LSeries]
  exact tsum_congr h1

/-- **Truncated Perron formula at the twisted point `1 + 1/log x + iu`.**  There is an absolute
constant `C > 0` such that for `x ≥ 3` not a natural number and `T ≥ 2`,
`‖(1/2π)∫_{-T}^{T} L(χΛ)(1+1/log x + i(u+t)) · x^{1+1/log x+it}/(1+1/log x+it) dt
   - Σ_{n≤x} χ(n)Λ(n)n^{-iu}‖ ≤ C (x log²x/T + log x)`. -/
theorem perron_twisted_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u x T : ℝ),
      3 ≤ x → (∀ n : ℕ, (n : ℝ) ≠ x) → 2 ≤ T →
      ‖(1 / (2 * Real.pi)) *
          (∫ t in (-T)..T,
            LSeries (chiLambdaTwist χ u)
                (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
              (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, chiLambdaTwist χ u n‖
        ≤ C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.Analysis.Complex.exists_perron_formula_bound
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Commons.NumberTheory.Zeta.mangoldtPerronError_bound
  refine ⟨C₀ * C₁, by positivity, ?_⟩
  intro q _inst χ u x T hx3 hxnat hT
  have hx1 : 1 < x := by linarith
  set c : ℝ := 1 + 1 / Real.log x with hc
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hc_gt_one : 1 < c := by
    rw [hc]
    have : 0 < 1 / Real.log x := by positivity
    linarith
  have hcpos : 0 < c := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  obtain ⟨hsum_comp, hbound_comp⟩ := hC₁ x hx3 T hT
  have hsum_a : Summable (fun n : ℕ => ‖chiLambdaTwist χ u n‖ / (n : ℝ) ^ c) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow hc_gt_one)
    gcongr
    exact chiLambdaTwist_norm_le χ u n
  have hmain := hC₀ (chiLambdaTwist χ u) c x T hcpos hx1 (by linarith) hxnat hsum_a
  refine le_trans hmain ?_
  have hterm_le : ∀ n : ℕ, ‖chiLambdaTwist χ u n‖ * (x / (n : ℝ)) ^ c *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (x / (n : ℝ)) ^ c *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) := by
    intro n
    have h3 := chiLambdaTwist_norm_le χ u n
    gcongr
  have hsum_a' : Summable (fun n : ℕ => ‖chiLambdaTwist χ u n‖ * (x / (n : ℝ)) ^ c *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hterm_le hsum_comp
    have h1 : (0 : ℝ) ≤ (x / (n : ℝ)) ^ c :=
      Real.rpow_nonneg (div_nonneg hxpos.le (Nat.cast_nonneg n)) c
    have h2 : (0 : ℝ) ≤ min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) :=
      le_min zero_le_one (by positivity)
    positivity
  have hle : (∑' n : ℕ, ‖chiLambdaTwist χ u n‖ * (x / (n : ℝ)) ^ c *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|)))
      ≤ (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (x / (n : ℝ)) ^ c *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) :=
    Summable.tsum_le_tsum hterm_le hsum_a' hsum_comp
  calc C₀ * (∑' n : ℕ, ‖chiLambdaTwist χ u n‖ * (x / (n : ℝ)) ^ c *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|)))
      ≤ C₀ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (x / (n : ℝ)) ^ c *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) :=
        mul_le_mul_of_nonneg_left hle hC₀pos.le
    _ ≤ C₀ * (C₁ * (x * (Real.log x) ^ 2 / T + Real.log x)) :=
        mul_le_mul_of_nonneg_left hbound_comp hC₀pos.le
    _ = C₀ * C₁ * (x * (Real.log x) ^ 2 / T + Real.log x) := by ring

/-! ## The twisted explicit formula

We set up the contour-shift machinery for the twisted sum `Σ_{n ≤ x} χ(n) Λ(n) n^{-iu}`,
mirroring `Commons.NumberTheory.DirichletCharacter.psiChi_uniform_bound_primitive` but with the
`L`-function evaluated on the vertical line `Re s = 1 + 1/log x` shifted by `iu`. -/

open MeasureTheory intervalIntegral
open scoped Interval Topology

/-- The twisted Perron integrand `w ↦ −(L′/L)(w + iu, χ) · x^w / w`. -/
noncomputable def chiGTw {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u x : ℝ)
    (w : ℂ) : ℂ :=
  -(deriv (DirichletCharacter.LFunction χ) (w + (u : ℂ) * Complex.I)) /
    DirichletCharacter.LFunction χ (w + (u : ℂ) * Complex.I) * (x : ℂ) ^ w / w

/-- The twisted truncated Perron integral on `Re w = 1 + 1/log x`, `|Im w| ≤ T`. -/
noncomputable def chiPerronTw {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (u x T : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ t in (-T)..T,
    chiGTw χ u x (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)

/-- `chiGTw` is the L-series of `χΛ` evaluated at the shifted point, on `Re w > 1`. -/
lemma chiGTw_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (u : ℝ) {x : ℝ} (hx : 0 < x) {w : ℂ} (hw : 1 < w.re) (hw0 : w ≠ 0) :
    chiGTw χ u x w = LSeries (fun n : ℕ => (χ (n : ZMod q) : ℂ) *
        (ArithmeticFunction.vonMangoldt n : ℂ)) (w + (u : ℂ) * Complex.I) *
        (x : ℂ) ^ w / w := by
  have hre : 1 < (w + (u : ℂ) * Complex.I).re := by simpa using hw
  have h := Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
    χ hre
  rw [logDeriv_apply] at h
  have h1 : LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod q) : ℂ)) (w + (u : ℂ) * Complex.I) =
      -(deriv (DirichletCharacter.LFunction χ) (w + (u : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ (w + (u : ℂ) * Complex.I)) := by
    rw [h, neg_neg]
  have h2 : LSeries (fun n : ℕ => (χ (n : ZMod q) : ℂ) *
      (ArithmeticFunction.vonMangoldt n : ℂ)) (w + (u : ℂ) * Complex.I) =
      LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod q) : ℂ)) (w + (u : ℂ) * Complex.I) :=
    LSeries_congr (fun {n} _ => by ring) _
  rw [chiGTw, h2, h1]
  ring_nf

private lemma cpow_diff' {x : ℝ} (hx : 0 < x) : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) := by
  have h : (fun s : ℂ => (x : ℂ) ^ s) = fun s : ℂ => Complex.exp ((Real.log x : ℂ) * s) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hx)), Complex.ofReal_log hx.le]
  rw [h]; fun_prop

/-- `chiGTw` is holomorphic wherever `L(· + iu, χ)` does not vanish and `w ≠ 0`. -/
lemma chiGTw_differentiableOn {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (u : ℝ) {x : ℝ} (hx : 0 < x) {U : Set ℂ}
    (h0 : ∀ w ∈ U, w ≠ 0) (hL : ∀ w ∈ U, DirichletCharacter.LFunction χ (w + (u:ℂ)*Complex.I) ≠ 0) :
    DifferentiableOn ℂ (chiGTw χ u x) U := by
  intro w hw
  unfold chiGTw
  have hshift : DifferentiableAt ℂ (fun z : ℂ => z + (u:ℂ)*Complex.I) w :=
    differentiableAt_id.add_const _
  have hLd : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) (w + (u:ℂ)*Complex.I) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableAt
  have hLdd : DifferentiableAt ℂ (fun z : ℂ => deriv (DirichletCharacter.LFunction χ) z)
      (w + (u:ℂ)*Complex.I) :=
    ((DirichletCharacter.differentiable_LFunction hχ).deriv).differentiableAt
  have h1 : DifferentiableAt ℂ (fun z : ℂ =>
      -(deriv (DirichletCharacter.LFunction χ) (z + (u:ℂ)*Complex.I)) /
        DirichletCharacter.LFunction χ (z + (u:ℂ)*Complex.I)) w :=
    (hLdd.comp w hshift).neg.div (hLd.comp w hshift) (hL w hw)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ z) w := (cpow_diff' hx).differentiableAt
  exact ((h1.mul h2).div differentiableAt_id (h0 w hw)).differentiableWithinAt

/-- **Rectangle-edge decomposition** (Cauchy's theorem on a rectangle): if `H` is
complex-differentiable on `[σ₁, c] × [-T, T]`, the integral over the right edge is the integral
over the left edge plus the two horizontal edges. -/
theorem rect_edge_decomp {σ₁ c T : ℝ} {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (Set.uIcc σ₁ c ×ℂ Set.uIcc (-T) T)) :
    (1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in σ₁..c, H ((u : ℂ) + (T : ℂ) * Complex.I)) -
         (∫ u in σ₁..c, H ((u : ℂ) - (T : ℂ) * Complex.I)))
      + (1 / (2 * Real.pi)) * (∫ t in (-T)..T, H ((σ₁ : ℂ) + (t : ℂ) * Complex.I))
      = (1 / (2 * Real.pi)) * (∫ t in (-T)..T, H ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  set z : ℂ := (σ₁ : ℂ) - (T : ℂ) * Complex.I with hz
  set w : ℂ := (c : ℂ) + (T : ℂ) * Complex.I with hw
  have hzre : z.re = σ₁ := by simp [hz]
  have hzim : z.im = -T := by simp [hz]
  have hwre : w.re = c := by simp [hw]
  have hwim : w.im = T := by simp [hw]
  have hdiff : DifferentiableOn ℂ H ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    simpa only [hzre, hwre, hzim, hwim] using hH
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H z w hdiff
  simp only [smul_eq_mul] at h
  have e1 : (∫ x in z.re..w.re, H (x + z.im * Complex.I))
      = ∫ u in σ₁..c, H ((u : ℂ) - (T : ℂ) * Complex.I) := by
    rw [hzre, hwre, hzim]
    exact intervalIntegral.integral_congr fun u _ => by
      have harg : (↑u : ℂ) + ↑(-T) * Complex.I = (↑u : ℂ) - Complex.I * ↑T := by
        push_cast; ring
      rw [harg, mul_comm (Complex.I : ℂ) (↑T : ℂ)]
  have e2 : (∫ x in z.re..w.re, H (x + w.im * Complex.I))
      = ∫ u in σ₁..c, H ((u : ℂ) + (T : ℂ) * Complex.I) := by
    simp only [hzre, hwre, hwim]
  have e3 : (∫ y in z.im..w.im, H (w.re + y * Complex.I))
      = ∫ t in (-T)..T, H ((c : ℂ) + (t : ℂ) * Complex.I) := by
    simp only [hzim, hwim, hwre]
  have e4 : (∫ y in z.im..w.im, H (z.re + y * Complex.I))
      = ∫ t in (-T)..T, H ((σ₁ : ℂ) + (t : ℂ) * Complex.I) := by
    simp only [hzim, hwim, hzre]
  rw [e1, e2, e3, e4] at h
  have h1 : Complex.I * (∫ t in (-T)..T, H ((c : ℂ) + (t : ℂ) * Complex.I)) =
      ((∫ u in σ₁..c, H ((u : ℂ) + (T : ℂ) * Complex.I)) -
        (∫ u in σ₁..c, H ((u : ℂ) - (T : ℂ) * Complex.I))) +
      Complex.I * (∫ t in (-T)..T, H ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [← sub_eq_zero]
    rw [← h]
    ring
  have hL : (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      (Complex.I * (∫ t in (-T)..T, H ((c : ℂ) + (t : ℂ) * Complex.I))) =
      (1 / (2 * (Real.pi : ℂ))) * (∫ t in (-T)..T, H ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    field_simp
    try ring
  have hR : (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      (((∫ u in σ₁..c, H ((u : ℂ) + (T : ℂ) * Complex.I)) -
        (∫ u in σ₁..c, H ((u : ℂ) - (T : ℂ) * Complex.I))) +
        Complex.I * (∫ t in (-T)..T, H ((σ₁ : ℂ) + (t : ℂ) * Complex.I))) =
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        ((∫ u in σ₁..c, H ((u : ℂ) + (T : ℂ) * Complex.I)) -
         (∫ u in σ₁..c, H ((u : ℂ) - (T : ℂ) * Complex.I))) +
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ t in (-T)..T, H ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) := by
    field_simp
    try ring
  have key := congrArg (fun y : ℂ => (1 / (2 * (Real.pi : ℂ) * Complex.I)) * y) h1
  rw [hL, hR] at key
  exact key.symm

/-- **The contour-shift identity for the twisted Perron integral**: if `L(·,χ)` has no zero in
the horizontal strip `{σ₁ ≤ Re s ≤ 1 + 1/log x, |Im s - u| ≤ T}`, then the twisted Perron
integral equals the sum of the three other edge integrals. -/
theorem chiPerronTw_rect {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {u x T σ₁ : ℝ} (hx : 1 < x) (hT : 0 < T) (hσ₁ : 0 < σ₁)
    (hσ₁lt : σ₁ < 1 + 1 / Real.log x)
    (hL0 : ∀ s : ℂ, s.re ∈ Set.Icc σ₁ (1 + 1 / Real.log x) → |s.im - u| ≤ T →
      DirichletCharacter.LFunction χ s ≠ 0) :
    chiPerronTw χ u x T =
      (1 / (2 * Real.pi * Complex.I)) *
        ((∫ v in σ₁..(1 + 1 / Real.log x),
            chiGTw χ u x ((v : ℂ) + (T : ℂ) * Complex.I)) -
         (∫ v in σ₁..(1 + 1 / Real.log x),
            chiGTw χ u x ((v : ℂ) - (T : ℂ) * Complex.I))) +
      (1 / (2 * Real.pi)) *
        (∫ t in (-T)..T, chiGTw χ u x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hTpos : 0 < T := hT
  have hdiff : DifferentiableOn ℂ (chiGTw χ u x)
      (Set.uIcc σ₁ (1 + 1 / Real.log x) ×ℂ Set.uIcc (-T) T) := by
    refine chiGTw_differentiableOn χ hχ u (by linarith : (0:ℝ) < x) ?_ ?_
    · intro w hw h0w
      have h1 := (Complex.mem_reProdIm.mp hw).1
      rw [Set.uIcc_of_le (by linarith : σ₁ ≤ 1 + 1 / Real.log x)] at h1
      have hre0 : w.re = 0 := by rw [h0w]; simp
      linarith [h1.1, hσ₁, hre0]
    · intro w hw
      have h1 := (Complex.mem_reProdIm.mp hw).1
      have h2 := (Complex.mem_reProdIm.mp hw).2
      rw [Set.uIcc_of_le (by linarith : σ₁ ≤ 1 + 1 / Real.log x)] at h1
      rw [Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)] at h2
      refine hL0 (w + (u : ℂ) * Complex.I) ?_ ?_
      · have : (w + (u : ℂ) * Complex.I).re = w.re := by simp
        rw [this]; exact h1
      · have him : (w + (u : ℂ) * Complex.I).im = w.im + u := by simp
        rw [him, add_sub_cancel_right, abs_le]
        exact h2
  have hperron : chiPerronTw χ u x T =
      (1 / (2 * Real.pi)) *
        (∫ t in (-T)..T,
          chiGTw χ u x (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := rfl
  rw [hperron]
  exact (rect_edge_decomp hdiff).symm

/-- The twisted Perron integral differs from the twisted sum by the standard truncation error. -/
theorem chiPerronTw_sub_sum_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
      (u x T : ℝ), 3 ≤ x → (∀ n : ℕ, (n : ℝ) ≠ x) → 2 ≤ T →
      ‖chiPerronTw χ u x T -
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, chiLambdaTwist χ u n‖
        ≤ C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  obtain ⟨C, hC, hper⟩ := perron_twisted_uniform
  refine ⟨C, hC, ?_⟩
  intro q _inst χ hχ u x T hx3 hxnat hT
  have hx1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hc1 : 1 < 1 + 1 / Real.log x := by
    have : 0 < 1 / Real.log x := by positivity
    linarith
  -- replace the L-series integrand by `chiGTw`
  have hcongr : (∫ t in (-T)..T,
        LSeries (chiLambdaTwist χ u)
            (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
          (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      = ∫ t in (-T)..T,
          chiGTw χ u x (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    beta_reduce
    set s : ℂ := ((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs
    have hsr : 1 < s.re := by
      have hre : s.re = 1 + 1 / Real.log x := by simp [hs]
      rw [hre]; exact hc1
    have hsne : s ≠ 0 := by
      intro h0
      have h1 : s.re = 0 := by rw [h0]; simp
      have hre : s.re = 1 + 1 / Real.log x := by simp [hs]
      rw [hre] at h1; linarith [hc1, h1]
    have htw : LSeries (chiLambdaTwist χ u) s =
        LSeries (fun n : ℕ => (χ (n : ZMod q) : ℂ) *
          (ArithmeticFunction.vonMangoldt n : ℂ)) (s + (u : ℂ) * Complex.I) := by
      have hfun : chiLambdaTwist χ u = fun n : ℕ =>
          ((χ (n : ZMod q) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
            (n : ℂ) ^ (-(Complex.I * u)) := by
        funext n
        simp [chiLambdaTwist]
      rw [hfun, LSeries_mul_cpow_neg_I]
    rw [htw, chiGTw_eq_LSeries χ hχ u (by linarith : (0:ℝ) < x) hsr hsne]
  have h := hper χ u x T hx3 hxnat hT
  have hkey : (1 / (2 * Real.pi)) * (∫ t in (-T)..T,
        LSeries (chiLambdaTwist χ u)
            (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
          (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      = chiPerronTw χ u x T := by
    rw [chiPerronTw, hcongr]
  rw [hkey] at h
  exact h


end Work.BMF
