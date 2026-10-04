import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_normSq_seriesFun
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `hasDerivAt_integral_normSq_seriesFun`: the `L²` energy of a time dependent Fourier series

Layer A of the STE Fourier toolkit.  For a time dependent coefficient family
`c : ℝ → (ι → ℤ) → ℂ` which is differentiable in time with (constant) derivative `c'`,
absolutely summable derivative (`hdom`) and locally uniformly bounded coefficients (`hb`),

  `t ↦ ∫_{unitCube} ‖seriesFun (c t)‖²`

is differentiable at `t₀` with derivative the doubled real part of the `L²` pairing of the
derivative series with the conjugate of the series at `t₀`:

  `2 * Re ∫_{unitCube} seriesFun c' · conj (seriesFun (c t₀))`.

This is the "differentiate the energy" step of the Friedrichs-mollifier energy method
(design A8/D2): the time derivative of the `L²` norm squared is twice the `L²` pairing with
the time derivative.

## Proof

Everything is reduced to the coefficient side.

* The pointwise real derivative of `s ↦ ‖f s‖²` for a differentiable `f : ℝ → ℂ` is
  `2 * Re (f' * conj (f t))` (`hasDerivAt_normsq_of_hasDerivAt_aux`): write
  `‖z‖² = (z * conj z).re`, apply the product rule together with `HasDerivAt.star`, and take
  real parts.
* Parseval for series-representable functions (`integral_normSq_seriesFun`) turns the integral
  into `Σ'_k ‖c t k‖²`, and the coefficient family is dominated by the summable `b` on a whole
  ball around `t₀` (`hb`), so the derivative bound `2‖c' k‖ b k` is summable and the
  term-by-term differentiation lemma `hasDerivAt_tsum_of_isPreconnected` applies.
* Finally `integral_seriesFun_mul_conj` computes the `L²` pairing of the two series and
  `Complex.re` commutes with the (summable) `tsum` (`ContinuousLinearMap.map_tsum`), which
  identifies `Σ'_k 2 * Re (c' k * conj (c t₀ k))` with the stated derivative.

No Parseval for arbitrary functions, no completeness of `L²`: every step is elementary and
uses only the absolute convergence of the series.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- `‖z‖ ^ 2`, as a complex number, is the product of `z` with its conjugate. -/
private lemma ofReal_normSq_eq_mul_star' (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The pointwise real derivative of `s ↦ ‖f s‖ ^ 2`.**  For a complex-valued function `f`
of a real variable with `HasDerivAt f z' t`, the real function `s ↦ ‖f s‖ ^ 2` has derivative
`2 * Re (z' * conj (f t))` at `t`. -/
private lemma hasDerivAt_normsq_of_hasDerivAt_aux {f : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (h : HasDerivAt f z' t) :
    HasDerivAt (fun s => ‖f s‖ ^ 2) (2 * (z' * star (f t)).re) t := by
  -- product rule for `s ↦ f s * star (f s)`, whose real part is `‖f s‖ ^ 2`
  have hmul : HasDerivAt (fun s => f s * star (f s)) (z' * star (f t) + f t * star z') t :=
    h.mul h.star
  have hre : HasDerivAt (fun s => Complex.reCLM (f s * star (f s)))
      (Complex.reCLM (z' * star (f t) + f t * star z')) t :=
    (Complex.reCLM.hasFDerivAt (x := f t * star (f t))).comp_hasDerivAt t hmul
  have hfun : (fun s => Complex.reCLM (f s * star (f s))) = fun s => ‖f s‖ ^ 2 := by
    funext s
    rw [Complex.reCLM_apply, ← ofReal_normSq_eq_mul_star', Complex.ofReal_re]
  rw [hfun] at hre
  refine hre.congr_deriv ?_
  -- `z * conj z'` is the conjugate of `z' * conj z`, so the two summands have the same real part
  have hstar : f t * star z' = star (z' * star (f t)) := by
    rw [star_mul, star_star, mul_comm]
  rw [hstar, Complex.reCLM_apply, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/-- `Σ'_k 2 * Re (c k * conj (d k))` is the doubled real part of the `L²` pairing of the
Fourier series with coefficient families `c` and `d` (both in `ℓ¹`). -/
private theorem two_mul_re_integral_seriesFun_mul_star_aux (c d : (ι → ℤ) → ℂ)
    (hc : Summable (fun k : ι → ℤ => ‖c k‖)) (hd : Summable (fun k : ι → ℤ => ‖d k‖)) :
    2 * Complex.re (∫ x in Work.Diff.STE.unitCube (ι := ι),
        Work.Diff.STE.seriesFun c x * star (Work.Diff.STE.seriesFun d x))
      = ∑' k : ι → ℤ, 2 * (c k * star (d k)).re := by
  rw [Work.Diff.STE.integral_seriesFun_mul_conj c d hc hd]
  -- summability of the coefficient family of the pairing, needed for `map_tsum`
  have hdsum : Summable (fun k : ι → ℤ => c k * star (d k)) := by
    refine Summable.of_norm_bounded (g := fun k => (∑' l : ι → ℤ, ‖c l‖) * ‖d k‖)
      (hd.mul_left _) (fun k => ?_)
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_right (hc.le_tsum k (fun j _ => norm_nonneg _)) (norm_nonneg _)
  rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hdsum, ← tsum_mul_left]
  simp only [Complex.reCLM_apply]


theorem hasDerivAt_integral_normSq_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ → (ι → ℤ) → ℂ) (c' : (ι → ℤ) → ℂ) (t₀ : ℝ)
    (hc : ∀ (k : ι → ℤ) (t : ℝ), HasDerivAt (fun s => c s k) (c' k) t)
    (hdom : Summable (fun k : ι → ℤ => ‖c' k‖))
    (hb : ∃ b : (ι → ℤ) → ℝ, Summable b ∧
      Filter.Eventually (fun t : ℝ => ∀ k : ι → ℤ, ‖c t k‖ ≤ b k) (nhds t₀)) :
    HasDerivAt (fun t => ∫ x in Work.Diff.STE.unitCube (ι := ι),
        ‖Work.Diff.STE.seriesFun (c t) x‖ ^ 2)
      (2 * Complex.re (∫ x in Work.Diff.STE.unitCube (ι := ι),
        Work.Diff.STE.seriesFun c' x * star (Work.Diff.STE.seriesFun (c t₀) x))) t₀ := by
  classical
  -- `hb` holds on a whole ball around `t₀`
  obtain ⟨b, hbsum, hbev⟩ := hb
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hbev
  have ht₀s : t₀ ∈ Metric.ball t₀ ε := Metric.mem_ball_self hεpos
  have hbnd : ∀ t ∈ Metric.ball t₀ ε, ∀ k : ι → ℤ, ‖c t k‖ ≤ b k := fun t ht => hε ht
  have hb0 : ∀ k : ι → ℤ, 0 ≤ b k := fun k => (norm_nonneg _).trans (hbnd t₀ ht₀s k)
  have hBnn : 0 ≤ ∑' k : ι → ℤ, b k := tsum_nonneg hb0
  have hcle : ∀ k : ι → ℤ, ‖c t₀ k‖ ≤ ∑' l : ι → ℤ, b l := fun k =>
    (hbnd t₀ ht₀s k).trans (hbsum.le_tsum k (fun j _ => hb0 j))
  have hDle : ∀ k : ι → ℤ, ‖c' k‖ ≤ ∑' l : ι → ℤ, ‖c' l‖ :=
    fun k => hdom.le_tsum k (fun j _ => norm_nonneg _)
  -- the summabilities entering `hasDerivAt_tsum_of_isPreconnected`
  have hc0 : Summable (fun k : ι → ℤ => ‖c t₀ k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (hbnd t₀ ht₀s) hbsum
  have hc0sq : Summable (fun k : ι → ℤ => ‖c t₀ k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
      (hbsum.mul_left (∑' l : ι → ℤ, b l))
    rw [sq]
    exact mul_le_mul (hcle k) (hbnd t₀ ht₀s k) (norm_nonneg _) hBnn
  have hu : Summable (fun k : ι → ℤ => 2 * ‖c' k‖ * b k) := by
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (hb0 k)) (fun k => ?_)
      (hbsum.mul_left (2 * ∑' l : ι → ℤ, ‖c' l‖))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hDle k) (by norm_num)) (hb0 k)
  have hbev' : ∀ᶠ t in nhds t₀, ∀ k : ι → ℤ, ‖c t k‖ ≤ b k :=
    Filter.mem_of_superset (Metric.ball_mem_nhds t₀ hεpos) hε
  -- term by term differentiation of the coefficient energy `Σ'_k ‖c t k‖²`
  have hderiv : HasDerivAt (fun t => ∑' k : ι → ℤ, ‖c t k‖ ^ 2)
      (∑' k : ι → ℤ, 2 * (c' k * star (c t₀ k)).re) t₀ :=
    hasDerivAt_tsum_of_isPreconnected (u := fun k : ι → ℤ => 2 * ‖c' k‖ * b k) hu
      Metric.isOpen_ball Metric.isPreconnected_ball
      (fun k t _ => hasDerivAt_normsq_of_hasDerivAt_aux (hc k t))
      (fun k t ht => by
        have hw : ‖2 * (c' k * star (c t k)).re‖ ≤ 2 * (‖c' k‖ * b k) := by
          calc ‖2 * (c' k * star (c t k)).re‖
              = 2 * ‖(c' k * star (c t k)).re‖ := by rw [norm_mul, Real.norm_ofNat]
            _ ≤ 2 * ‖c' k * star (c t k)‖ := by
                exact mul_le_mul_of_nonneg_left
                  (by simpa [Real.norm_eq_abs] using
                    Complex.abs_re_le_norm (c' k * star (c t k))) (by norm_num)
            _ = 2 * (‖c' k‖ * ‖c t k‖) := by rw [norm_mul, norm_star]
            _ ≤ 2 * (‖c' k‖ * b k) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hbnd t ht k) (norm_nonneg _)) (by norm_num)
        simpa only [mul_assoc] using hw)
      ht₀s hc0sq ht₀s
  -- Parseval identifies the physical energy with the coefficient energy
  have hcongr : (fun t => ∫ x in Work.Diff.STE.unitCube (ι := ι),
        ‖Work.Diff.STE.seriesFun (c t) x‖ ^ 2)
      =ᶠ[nhds t₀] (fun t => ∑' k : ι → ℤ, ‖c t k‖ ^ 2) := by
    filter_upwards [hbev'] with t ht
    exact Work.Diff.STE.integral_normSq_seriesFun (c t)
      (Summable.of_nonneg_of_le (fun k => norm_nonneg _) ht hbsum)
  refine (hderiv.congr_of_eventuallyEq hcongr).congr_deriv ?_
  exact (two_mul_re_integral_seriesFun_mul_star_aux c' (c t₀) hdom hc0).symm

end Work.Diff.STE
