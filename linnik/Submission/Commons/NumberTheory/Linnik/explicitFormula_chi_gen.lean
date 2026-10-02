import Mathlib
import Submission.Commons.Analysis.Complex.lapX_sub_inv_bound
import Submission.Commons.Analysis.Complex.twisted_inversion_regularized
import Submission.Commons.Analysis.Complex.regularized_leftEdge_bound_alt
import Submission.Commons.Analysis.Complex.regularized_kernel_bound_negRe
import Submission.Commons.NumberTheory.DirichletCharacter.regularized_divisor_contour_shift_gen
import Submission.Commons.NumberTheory.DirichletCharacter.smoothed_vonMangoldt_eq_line_regularized

open Complex DirichletCharacter Metric Filter Set Topology
open scoped Real Topology BigOperators

set_option maxHeartbeats 8000000
set_option autoImplicit false

attribute [local instance] Classical.propDecidable

namespace Commons.NumberTheory.Linnik

noncomputable section

/-!
# The general smoothed explicit formula (Heath-Brown (1992), equation (5.7))

`Commons.NumberTheory.Linnik.explicitFormula_chi_gen` is the smoothed explicit formula for a
primitive non-trivial Dirichlet character with a general weight `f` (i.e. `f 0 ≠ 0`), in the
range `|Re s - 1| ≤ √(log L)/L`, `|Im s| ≤ L`, with error
`O((log L)^{-1/2} log(2 + ‖s‖))`.

The proof proceeds via the `α`-line identity and a contour shift, with the `f(0)`-regularized
kernel `Φ u = ∫_0^{x₀} e^{-(s-u)Lt} f t dt - f 0/((s-u)L)`:

* `Commons.NumberTheory.DirichletCharacter.smoothed_vonMangoldt_eq_line_regularized` gives
  `Σ_n Λ(n)χ(n)n^{-s} f(log n/L) = -(L/2π) ∫_τ (L'/L)(χ,α+iτ) Φ(α+iτ) dτ`;
* `Commons.NumberTheory.DirichletCharacter.regularized_divisor_contour_shift_gen` moves the line
  `Re w = α` to `Re w = -1/2`, producing `Σ'_u div(u)Φ(u)`;
* `Commons.Analysis.Complex.regularized_leftEdge_bound_alt` bounds the left-edge integral
  (the `log N` term cancels against
  `Commons.Analysis.Complex.regularized_vertical_integral_eq_zero`).

The `α`-line and contour-shift identities are combined with
`Commons.Analysis.Complex.lapX_sub_inv_bound` (for the value `Φ 0`) to yield the stated bound.
-/

/-- The second iterated derivative of `fun t => ((f t : ℝ) : ℂ)` is the complexification
of `iteratedDeriv 2 f`. -/
lemma ofReal_iteratedDeriv_two_eq {f : ℝ → ℝ} {x₀ t : ℝ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) x₀)) (ht : t ∈ Set.Ioo (0:ℝ) x₀) :
    iteratedDeriv 2 (fun s => ((f s : ℝ) : ℂ)) t = ((iteratedDeriv 2 f t : ℝ) : ℂ) := by
  have hmem : Set.Ioo (0:ℝ) x₀ ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
  have hdiff1 : DifferentiableOn ℝ f (Set.Ioo (0:ℝ) x₀) :=
    hf2.differentiableOn (by norm_num)
  have hd1 : ∀ s ∈ Set.Ioo (0:ℝ) x₀,
      deriv (fun u => ((f u : ℝ) : ℂ)) s = ((deriv f s : ℝ) : ℂ) := by
    intro s hs
    exact ((hdiff1.hasDerivAt (Ioo_mem_nhds hs.1 hs.2)).ofReal_comp).deriv
  have heq : deriv (fun u => ((f u : ℝ) : ℂ)) =ᶠ[𝓝 t] (fun s => ((deriv f s : ℝ) : ℂ)) := by
    filter_upwards [hmem] with s hs using hd1 s hs
  have hdiff2 : DifferentiableOn ℝ (deriv f) (Set.Ioo (0:ℝ) x₀) := by
    have h := hf2.differentiableOn_iteratedDerivWithin (m := 1) (by norm_num) (uniqueDiffOn_Ioo 0 x₀)
    refine h.congr ?_
    intro y hy
    rw [iteratedDerivWithin_one, derivWithin_of_isOpen isOpen_Ioo hy]
  have hd2 : HasDerivAt (fun s => ((deriv f s : ℝ) : ℂ))
      (((deriv (deriv f) t : ℝ)) : ℂ) t :=
    (hdiff2.hasDerivAt hmem).ofReal_comp
  rw [show iteratedDeriv 2 (fun u => ((f u : ℝ) : ℂ)) t
        = deriv (deriv (fun u => ((f u : ℝ) : ℂ))) t from by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]]
  rw [heq.deriv_eq, hd2.deriv]
  congr 1
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]



/-- Transfer of the `C²`-bound to the complexification. -/
lemma norm_ofReal_iteratedDeriv_two_le {f : ℝ → ℝ} {x₀ B t : ℝ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) x₀)) (ht : t ∈ Set.Ioo (0:ℝ) x₀)
    (hB : ‖iteratedDeriv 2 f t‖ ≤ B) :
    ‖iteratedDeriv 2 (fun s => ((f s : ℝ) : ℂ)) t‖ ≤ B := by
  rw [ofReal_iteratedDeriv_two_eq hf2 ht]
  simpa [RCLike.norm_ofReal, Real.norm_eq_abs] using hB



set_option maxHeartbeats 8000000

/-- The `ℂ`-valued form of the general smoothed explicit formula (Heath-Brown (5.7)). -/
theorem explicitFormula_chi_gen_crux (x₀ B : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive) {f : ℝ → ℂ}
      (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
      {L : ℝ} (hL : 1 < L),
      ∀ s : ℂ, |s.re - 1| ≤ Real.sqrt (Real.log L) / L → |s.im| ≤ L →
        DirichletCharacter.LFunction χ s ≠ 0 →
        ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
              f (Real.log n / L))
          + (L : ℂ) * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
              ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)
                - f 0 / ((s - u) * (L : ℂ))))
          + f 0 * logDeriv (DirichletCharacter.LFunction χ) s‖
        ≤ C *
            (B * x₀ + ‖f 0‖ / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + ‖s‖) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro N _ χ hχ hχprim f hcont hsupp hf2 hBnd L hL
  intro s hsre hsim hLs
  have hLpos : (0:ℝ) < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hlogLnn : (0:ℝ) ≤ Real.log L := hlogL.le
  -- The exponent range
  set δ : ℝ := Real.sqrt (Real.log L) / L with hδdef
  have hδnn : 0 ≤ δ := by rw [hδdef]; positivity
  have hlogLt : Real.log L < L^2/4 := by
    rcases eq_or_ne L 2 with h2 | h2
    · rw [h2]; linarith only [Real.log_two_lt_d9]
    · have h1 : Real.log L < L - 1 := Real.log_lt_sub_one_of_pos hLpos (by linarith)
      have h3 : L - 1 < L^2/4 := by
        have h4 : (0:ℝ) < (L-2)^2 := by positivity
        linarith
      linarith
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδhalf : δ < 1/2 := by
    rw [hδdef, div_lt_iff₀ hLpos]
    have hsq : Real.sqrt (Real.log L) < L/2 := by
      rw [Real.sqrt_lt' (by linarith : (0:ℝ) < L/2)]
      linarith only [hlogLt]
    linarith
  set α : ℝ := 1 + 2*δ with hαdef
  have hα1 : 1 < α := by rw [hαdef]; linarith
  have hα2 : α < 2 := by rw [hαdef]; linarith
  have hsr : s.re - 1 ≤ δ := (abs_le.mp hsre).2
  have hsrg : -(δ) ≤ s.re - 1 := (abs_le.mp hsre).1
  have hασ : s.re < α := by rw [hαdef]; linarith
  have hsrepos : 0 < s.re := by linarith
  have hsre_half : (1:ℝ)/2 ≤ s.re := by linarith
  have hnorm_half : (1:ℝ)/2 ≤ ‖s‖ := le_trans hsre_half (Complex.re_le_norm s)
  -- abbreviations
  set lg : ℝ := Real.log (2 + ‖s‖) with hlgdef
  have hlgpos : 0 < lg := by
    rw [hlgdef]
    apply Real.log_pos
    have : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
    linarith
  have hlg2 : Real.log 2 ≤ lg := by
    rw [hlgdef]
    apply Real.log_le_log (by norm_num)
    have : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
    linarith
  set A : ℝ := 3 * B * x₀ + 2 * ‖f 0‖ / x₀ with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  -- the three ingredients
  have hline :=
    Commons.NumberTheory.DirichletCharacter.smoothed_vonMangoldt_eq_line_regularized
      (x₀ := x₀) (B := B) hx₀ hB hcont hf2 hBnd hsupp χ hχ hχprim hL hα1 hασ
  have hshift :=
    Commons.NumberTheory.DirichletCharacter.regularized_divisor_contour_shift_gen
      (x₀ := x₀) (B := B) hx₀ hB hcont hf2 hBnd hsupp χ hχ hχprim hL hα1 hα2 hασ
      (by linarith : -(1/2:ℝ) < s.re) hLs
  have hleft :=
    Commons.Analysis.Complex.regularized_leftEdge_bound_alt
      (x₀ := x₀) (B := B) hx₀ hB hcont hf2 hBnd hsupp χ hχ hχprim hL (by linarith : (0:ℝ) < s.re + 1/2)
  -- name the three integrals
  set Ia : ℂ := ∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (τ : ℂ) * Complex.I) *
      ((∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
        - f 0 / ((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))) with hIadef
  set Il : ℂ := ∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) *
      ((∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
        - f 0 / ((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))) with hIldef
  set Φ0 : ℂ := (∫ t in (0:ℝ)..x₀, Complex.exp (-((s - 0) * (L : ℂ) * (t : ℂ))) * f t)
      - f 0 / ((s - 0) * (L : ℂ)) with hΦ0def
  -- rewrite the ingredients
  have hline' : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
        f (Real.log n / L))
      = -(L / (2 * (Real.pi : ℂ))) * Ia := by
    rw [hIadef]; exact hline
  have hshift' :
      (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)
          - f 0 / ((s - u) * (L : ℂ))))
        = (1 / (2 * (Real.pi : ℂ))) * (Ia - Il)
          - logDeriv (DirichletCharacter.LFunction χ) s * (f 0 / (L : ℂ))
          - (if χ.Even then Φ0 else 0) := by
    rw [hIadef, hIldef]
    rw [hΦ0def]
    exact hshift
  have hleft' : ‖Il‖ ≤ A / L^2 * 2000 * (lg + 1) := by
    rw [hIldef, hAdef, hlgdef]; exact hleft
  have hΦ0b : ‖Φ0‖ ≤ A / (L^2 * ‖s‖^2) := by
    rw [hΦ0def, hAdef]
    have hz : 0 < (s * (L:ℂ)).re := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_pos hsrepos hLpos
    have h := Commons.Analysis.Complex.lapX_sub_inv_bound
      (x₀ := x₀) (B := B) (f := f) hx₀ hB hcont hf2 hBnd hsupp (z := s * (L:ℂ)) hz
    have hnorm : ‖s * (L:ℂ)‖^2 = L^2 * ‖s‖^2 := by
      rw [norm_mul, Complex.norm_of_nonneg hLpos.le]; ring
    rw [hnorm] at h
    simpa using h
  have hifb : ‖(if χ.Even then Φ0 else 0)‖ ≤ A / (L^2 * ‖s‖^2) := by
    by_cases h : χ.Even
    · simp only [if_pos h]; exact hΦ0b
    · simp only [if_neg h, norm_zero]; positivity
  -- the main identity
  have hmain :
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
            f (Real.log n / L))
        + (L : ℂ) * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
            ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)
              - f 0 / ((s - u) * (L : ℂ))))
        + f 0 * logDeriv (DirichletCharacter.LFunction χ) s
      = -(L / (2 * (Real.pi : ℂ))) * Il - (L : ℂ) * (if χ.Even then Φ0 else 0) := by
    rw [hline', hshift']
    have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLpos.ne'
    have hpi2 : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  rw [hmain]
  -- the bound
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlg_half : (1:ℝ)/2 ≤ lg := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 2) (by have := norm_nonneg s; linarith : (2:ℝ) ≤ 2 + ‖s‖)
    rw [hlgdef]
    linarith [Real.log_two_gt_d9]
  have h1s : 1 / ‖s‖^2 ≤ 4 := by
    have h2 : (1:ℝ)/4 ≤ ‖s‖^2 := by nlinarith only [hnorm_half, norm_nonneg s]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖s‖^2)]
    linarith only [h2]
  have hALnn : (0:ℝ) ≤ A / L := by positivity
  have heq1 : (L / (2 * Real.pi)) * (A / L^2 * 2000 * (lg + 1))
      = (A / L) * (1000 / Real.pi) * (lg + 1) := by
    field_simp
    ring
  have heq2 : L * (A / (L^2 * ‖s‖^2)) = (A / L) * (1 / ‖s‖^2) := by
    field_simp
    try ring
  have hinvL : L⁻¹ ≤ (Real.log L) ^ (-(1/2 : ℝ)) := by
    have hsq : Real.sqrt (Real.log L) ≤ L := by
      rw [Real.sqrt_le_iff]
      refine ⟨hLpos.le, ?_⟩
      have := Real.log_le_sub_one_of_pos hLpos
      nlinarith only [this, hLpos, sq_nonneg (L - 1)]
    have hspos : 0 < Real.sqrt (Real.log L) := Real.sqrt_pos.mpr hlogL
    have h1 : (Real.log L) ^ (-(1/2 : ℝ)) = (Real.sqrt (Real.log L))⁻¹ := by
      rw [Real.rpow_neg hlogLnn, Real.sqrt_eq_rpow]
    rw [h1]
    exact (inv_le_inv₀ hLpos hspos).mpr hsq
  have hleft' : ‖Il‖ ≤ A / L^2 * 2000 * (lg + 1) := by
    rw [hIldef, hAdef, hlgdef]; exact hleft
  have hΦ0b : ‖Φ0‖ ≤ A / (L^2 * ‖s‖^2) := by
    rw [hΦ0def, hAdef]
    have hz : 0 < (s * (L:ℂ)).re := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_pos hsrepos hLpos
    have h := Commons.Analysis.Complex.lapX_sub_inv_bound
      (x₀ := x₀) (B := B) (f := f) hx₀ hB hcont hf2 hBnd hsupp (z := s * (L:ℂ)) hz
    have hnorm : ‖s * (L:ℂ)‖^2 = L^2 * ‖s‖^2 := by
      rw [norm_mul, Complex.norm_of_nonneg hLpos.le]; ring
    rw [hnorm] at h
    simpa using h
  have hifb : ‖(if χ.Even then Φ0 else 0)‖ ≤ A / (L^2 * ‖s‖^2) := by
    by_cases h : χ.Even
    · simp only [if_pos h]; exact hΦ0b
    · simp only [if_neg h, norm_zero]; positivity
  have hLy : ‖(L / (2 * (Real.pi : ℂ))) * Il‖ ≤ (L / (2 * Real.pi)) * (A / L^2 * 2000 * (lg + 1)) := by
    rw [norm_mul]
    have hc : ‖(L : ℂ) / (2 * (Real.pi : ℂ))‖ = L / (2 * Real.pi) := by
      rw [show (L : ℂ) / (2 * (Real.pi : ℂ)) = ((L / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_of_nonneg (show (0:ℝ) ≤ L / (2 * Real.pi) by positivity)]
    rw [hc]
    exact mul_le_mul_of_nonneg_left hleft' (by positivity)
  have hLb : ‖(L : ℂ) * (if χ.Even then Φ0 else 0)‖ ≤ L * (A / (L^2 * ‖s‖^2)) := by
    rw [norm_mul, Complex.norm_of_nonneg hLpos.le]
    exact mul_le_mul_of_nonneg_left hifb hLpos.le
  -- the numerical steps
  set P : ℝ := (3000 / Real.pi) + 12 with hPdef
  set Q : ℝ := B * x₀ + ‖f 0‖ / x₀ + 1 with hQdef
  set M : ℝ := (Real.log L) ^ (-(1/2 : ℝ)) with hMdef
  have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
  have hMnn : 0 ≤ M := by rw [hMdef]; exact Real.rpow_nonneg hlogLnn _
  have hA3 : A ≤ 3 * Q := by
    rw [hAdef, hQdef]
    have h1 : (0:ℝ) ≤ ‖f 0‖ / x₀ := by positivity
    have h2 : (2:ℝ) * ‖f 0‖ / x₀ = 2 * (‖f 0‖ / x₀) := by ring
    rw [h2]
    linarith only [h1]
  have hALbound : A / L ≤ 3 * Q * M := by
    have h1 : A / L ≤ 3 * Q / L := by
      exact div_le_div_of_nonneg_right hA3 hLpos.le
    have h2 : 3 * Q / L ≤ 3 * Q * M := by
      rw [div_eq_mul_inv, hMdef]
      exact mul_le_mul_of_nonneg_left hinvL (by positivity)
    linarith only [h1, h2]
  have hstep1 : (L / (2 * Real.pi)) * (A / L^2 * 2000 * (lg + 1)) + L * (A / (L^2 * ‖s‖^2))
      ≤ (A / L) * P * lg := by
    rw [heq1, heq2]
    have h1 : (A / L) * (1000 / Real.pi) * (lg + 1) ≤ (A / L) * (1000 / Real.pi) * (3 * lg) := by
      have hc : (0:ℝ) ≤ (A / L) * (1000 / Real.pi) := by positivity
      have h5 : lg + 1 ≤ 3 * lg := by linarith only [hlg_half]
      exact mul_le_mul_of_nonneg_left h5 hc
    have h2 : (A / L) * (1 / ‖s‖^2) ≤ (A / L) * (12 * lg) := by
      have h4 : 1 / ‖s‖^2 ≤ 12 * lg := by linarith only [h1s, hlg_half]
      exact mul_le_mul_of_nonneg_left h4 hALnn
    have h3 : (A / L) * (1000 / Real.pi) * (3 * lg) + (A / L) * (12 * lg) = (A / L) * P * lg := by
      rw [hPdef]; ring
    linarith only [h1, h2, h3.le, h3.ge]
  have hstep2 : (A / L) * P * lg ≤ 3 * P * Q * M * lg := by
    have hc : (0:ℝ) ≤ P * lg := by rw [hPdef]; positivity
    have h := mul_le_mul_of_nonneg_right hALbound hc
    calc (A / L) * P * lg = (A / L) * (P * lg) := by ring
      _ ≤ 3 * Q * M * (P * lg) := h
      _ = 3 * P * Q * M * lg := by ring
  have hstep3 : 3 * P * Q * M * lg ≤ 100000 * Q * M * lg := by
    have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
    have h1 : 3 * P ≤ 100000 := by
      rw [hPdef]
      have h2 : 3000 / Real.pi < 1000 := by
        rw [div_lt_iff₀ (by linarith only [hpi] : (0:ℝ) < Real.pi)]
        linarith only [hpi]
      linarith only [h2]
    have hc : (0:ℝ) ≤ Q * M * lg := by positivity
    have h := mul_le_mul_of_nonneg_right h1 hc
    calc 3 * P * Q * M * lg = (3 * P) * (Q * M * lg) := by ring
      _ ≤ 100000 * (Q * M * lg) := h
      _ = 100000 * Q * M * lg := by ring
  calc ‖-(L / (2 * (Real.pi : ℂ))) * Il - (L : ℂ) * (if χ.Even then Φ0 else 0)‖
      ≤ ‖(L / (2 * (Real.pi : ℂ))) * Il‖ + ‖(L : ℂ) * (if χ.Even then Φ0 else 0)‖ := by
        simpa only [neg_mul, norm_neg] using
          norm_sub_le (-((L / (2 * (Real.pi : ℂ))) * Il)) ((L : ℂ) * (if χ.Even then Φ0 else 0))
    _ ≤ (L / (2 * Real.pi)) * (A / L^2 * 2000 * (lg + 1)) + L * (A / (L^2 * ‖s‖^2)) := add_le_add hLy hLb
    _ ≤ (A / L) * P * lg := hstep1
    _ ≤ 3 * P * Q * M * lg := hstep2
    _ ≤ 100000 * Q * M * lg := hstep3
    _ = 100000 * (B * x₀ + ‖f 0‖ / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + ‖s‖) := by
        rw [hQdef, hMdef, hlgdef]



/-- The general smoothed explicit formula with the `f(0)`-term: the `ℝ`-valued statement. -/
theorem explicitFormula_chi_gen (x₀ B : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive) {f : ℝ → ℝ}
      (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
      {L : ℝ} (hL : 1 < L),
      ∀ s : ℂ, |s.re - 1| ≤ Real.sqrt (Real.log L) / L → |s.im| ≤ L →
        DirichletCharacter.LFunction χ s ≠ 0 →
        ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
              ((f (Real.log n / L) : ℝ) : ℂ))
          + L * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
              ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ))
                - ((f 0 : ℝ) : ℂ) / ((s - u) * L)))
          + ((f 0 : ℝ) : ℂ) * logDeriv (DirichletCharacter.LFunction χ) s‖
        ≤ C * (B * x₀ + |f 0| / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + ‖s‖) := by
  obtain ⟨C, hCpos, hC⟩ := explicitFormula_chi_gen_crux x₀ B hx₀ hB
  refine ⟨C, hCpos, ?_⟩
  intro N _ χ hχ hχprim f hcont hsupp hf2 hBnd L hL s hsre hsim hLs
  set g : ℝ → ℂ := fun t => ((f t : ℝ) : ℂ) with hgdef
  have hcontg : ContinuousOn g (Set.Icc 0 x₀) := by
    change ContinuousOn (fun t => ((f t : ℝ) : ℂ)) (Set.Icc 0 x₀)
    exact Complex.continuous_ofReal.comp_continuousOn (hcont.mono Set.Icc_subset_Ici_self)
  have hsuppg : ∀ t : ℝ, x₀ ≤ t → g t = 0 := by
    intro t ht; rw [hgdef]; simp [hsupp t ht]
  have hf2g : ContDiffOn ℝ 2 g (Set.Ioo (0:ℝ) x₀) := by
    change ContDiffOn ℝ 2 (fun t => ((f t : ℝ) : ℂ)) (Set.Ioo (0:ℝ) x₀)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hf2
  have hBndg : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 g t‖ ≤ B := by
    intro t ht
    change ‖iteratedDeriv 2 (fun s => ((f s : ℝ) : ℂ)) t‖ ≤ B
    exact norm_ofReal_iteratedDeriv_two_le hf2 ht (hBnd t ht)
  have key := hC χ hχ hχprim hcontg hsuppg hf2g hBndg hL s hsre hsim hLs
  have hLHS : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
            g (Real.log n / L))
        + (L : ℂ) * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
            ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * g t)
              - g 0 / ((s - u) * (L : ℂ))))
        + g 0 * logDeriv (DirichletCharacter.LFunction χ) s
      = (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
              ((f (Real.log n / L) : ℝ) : ℂ))
          + L * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
              ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ))
                - ((f 0 : ℝ) : ℂ) / ((s - u) * L)))
          + ((f 0 : ℝ) : ℂ) * logDeriv (DirichletCharacter.LFunction χ) s := by
    simp only [hgdef]
  rw [hLHS] at key
  have hg0 : ‖g 0‖ / x₀ = |f 0| / x₀ := by
    rw [hgdef]
    simp [Complex.normSq_ofReal]
  rw [hg0] at key
  exact key

end

end Commons.NumberTheory.Linnik
