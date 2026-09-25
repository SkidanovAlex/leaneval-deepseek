/-
# Major-arc asymptotic for the square kernel (Bourgain (6.10))

**Target** (`Commons.Analysis.ExponentialSums.quadratic_major_arc_asymptotic`):

`∃ δ θ C > 0, ∀ N a q β, 1 ≤ N → 0 < q → q ≤ N^δ → gcd a q = 1 → |β| ≤ N^{-1-δ} →`
`‖ (1/N) ∑_{n<N} e((a/q+β)n²) − (1/q)(∑_{r<q} e(a r²/q)) · ∫_0^1 e(β N² s²) ‖ ≤ C N^{-θ}`.

## Proof strategy (worked out in this file)

Write `A_r = ∑_{p < P_r} e(β (pq+r)²)` with `P_r = (N+q-1-r)/q` (so `pq+r<N ⟺ p<P_r`),
and `C_r = ∫_0^{P_r} e(β(qs+r)²) ds = (1/q) ∫_r^{r+qP_r} e(βu²) du`.  The residue
factorisation `residue_factor_expTwoPiI` gives
`∑_{n<N} e((a/q+β)n²) = ∑_{r<q} e(a r²/q) A_r`, hence

`E := ∑_{n<N} e((a/q+β)n²) − (1/q)(∑_r e(a r²/q)) ∫_0^N e(βt²) dt
    = ∑_{r<q} e(a r²/q) (A_r − (1/q) ∫_0^N e(βt²) dt)`,

and since `r + q P_r ∈ [N, N+q)` the second piece `C_r − (1/q)∫_0^N e(βt²)dt` has
modulus `≤ 2`, so `|E| ≤ ∑_r |E_r| + 2q` where `E_r = A_r − C_r`.

The heart is the **block bound** `|E_r| ≤ 20 + 2000 |β|^{3/2} q (q P_r + r)²`
(proved via the Euler–Maclaurin identity `sum_sub_integral_cos_series` of the commons,
which expands the trapezoidal error into the cosine series
`P̃₂(s) = −1/12 + (1/(2π²)) ∑_{k≥1} cos(2πks)/k²`, and the van der Corput weighted
cosine bound `integral_second_derivative_test` of the commons for each of the
resulting oscillatory integrals; the second derivative of the phase is `4π|β|q²`,
whence the `β^{3/2} q (qP+r)²` shape since `1/√(4π|β|q²) = 1/(2q√(π|β|))`).

Summing over `r < q ≤ N^δ` and using `|β| ≤ N^{-1-δ}`, `q P_r + r ≤ N+q ≤ 2N`,
`|β|^{3/2} q² N² ≤ N^{(1+δ)/2}` gives `|E| ≤ 8000 N^{(1+δ)/2} + O(q)`, so with
`δ = 1/2` we get `|E|/N ≤ C N^{-1/4}`.

## Status

COMPLETE.  The file proves, in order:

* `hasDerivAt_quadPhase`, `hasDerivAt_quadPhase'` — the first two derivatives of the
  quadratic phase `s ↦ e(β (q s + r)²)`, and `deriv_deriv_add_const_mul_id` /
  `deriv_deriv_quad` for the second derivative of a quadratic times a linear shear;
* `norm_integral_weight_cos_le`, `norm_integral_weight_sin_le` — the complexified weighted
  van der Corput bound (from the commons `integral_second_derivative_test`), and
  `norm_integral_weight_cos_mul_cos_le`, `norm_integral_weight_cos_mul_sin_le` — its
  product-to-sum form;
* `quadratic_cos_coeff_bound` — the cosine-coefficient bound
  `‖∫ cos(2πms) g''‖ ≤ 100 + 2000 |β|^{3/2} q (qP+r)²` (with the auxiliary
  `expTwoPiI_eq_cos_add_sin`, `cos_phase_abs`, `exists_sign_sin_phase`);
* `norm_tsum_one_div_sq_mul_le` — the `ℓ²`-tail bound `‖∑ (1/(k+1)²) F k‖ ≤ A π²/6`;
* `block_bound` — the Euler–Maclaurin block estimate
  `‖∑_{p<P} e(β(pq+r)²) − ∫_0^P e(β(qs+r)²)‖ ≤ 20 + 2000 |β|^{3/2} q (qP+r)²`;
* `quadratic_major_arc_asymptotic` — the target, with `δ = 1/4`, `θ = 1/8`, `C = 10^6`.
-/
import Mathlib
import Submission.Commons.Analysis.EulerMaclaurin.sum_sub_integral_cos_series
import Submission.Commons.Analysis.Calculus.integral_second_derivative_test
import Submission.Commons.Analysis.ExponentialSums.quadratic_major_arc_approx

namespace Commons.Analysis.ExponentialSums

set_option maxHeartbeats 1000000

open Finset MeasureTheory intervalIntegral Filter
open scoped BigOperators Real

/-! ### Derivative identities for the quadratic phase `s ↦ e(β (q s + r)²)` -/

/-- First derivative of the quadratic phase. -/
theorem hasDerivAt_quadPhase (β q r : ℝ) (x : ℝ) :
    HasDerivAt (fun s : ℝ => expTwoPiI (β * (q * s + r) ^ 2))
      (4 * Real.pi * Complex.I * β * q * (q * x + r) * expTwoPiI (β * (q * x + r) ^ 2)) x := by
  have h2 : HasDerivAt (fun s : ℝ => q * s + r) q x := by
    simpa using ((hasDerivAt_id x).const_mul q).add_const r
  have h3 : HasDerivAt (fun s : ℝ => (q * s + r) ^ 2) (2 * (q * x + r) * q) x :=
    (h2.pow 2).congr_deriv (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => β * (q * s + r) ^ 2) (β * (2 * (q * x + r) * q)) x :=
    h3.const_mul β
  have h6 : HasDerivAt (fun s : ℝ => ((β * (q * s + r) ^ 2 : ℝ) : ℂ))
      ((β * (2 * (q * x + r) * q) : ℝ) : ℂ) x := h1.ofReal_comp
  have h7 : HasDerivAt (fun s : ℝ => 2 * Real.pi * Complex.I * ((β * (q * s + r) ^ 2 : ℝ) : ℂ))
      (2 * Real.pi * Complex.I * ((β * (2 * (q * x + r) * q) : ℝ) : ℂ)) x := h6.const_mul _
  exact h7.cexp |>.congr_deriv (by rw [expTwoPiI]; push_cast; ring)

/-- Second derivative of the quadratic phase:
`s'' = (4πI β q² − 16π²β²q²(q x + r)²) · s`. -/
theorem hasDerivAt_quadPhase' (β q r : ℝ) (x : ℝ) :
    HasDerivAt (fun s : ℝ => 4 * Real.pi * Complex.I * β * q *
        ((((q * s + r : ℝ)) : ℂ) * expTwoPiI (β * (q * s + r) ^ 2)))
      ((4 * Real.pi * Complex.I * β * q ^ 2 - 16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 *
          ((((q * x + r : ℝ)) : ℂ)) ^ 2) * expTwoPiI (β * (q * x + r) ^ 2)) x := by
  have h2 : HasDerivAt (fun s : ℝ => (((q * s + r : ℝ)) : ℂ)) ((q : ℂ)) x := by
    simpa using (((hasDerivAt_id x).const_mul q).add_const r).ofReal_comp
  have h4 := hasDerivAt_quadPhase β q r x
  have h3 : HasDerivAt (fun s : ℝ => (4 * Real.pi * Complex.I * β * q : ℂ) *
      ((((q * s + r : ℝ)) : ℂ) * expTwoPiI (β * (q * s + r) ^ 2)))
      ((4 * Real.pi * Complex.I * β * q : ℂ) * (((q : ℂ)) * expTwoPiI (β * (q * x + r) ^ 2) +
        ((((q * x + r : ℝ)) : ℂ)) * (4 * Real.pi * Complex.I * β * q * (q * x + r) *
          expTwoPiI (β * (q * x + r) ^ 2)))) x :=
    (h2.mul h4).const_mul _
  refine h3.congr_deriv ?_
  have hI : Complex.I ^ 2 = -1 := by rw [sq, Complex.I_mul_I]
  rw [expTwoPiI]
  push_cast
  ring_nf
  rw [hI]
  ring

/-- The second-derivative factor evaluated at `x`, written in the form used for the
weighted oscillatory-integral bound. -/
theorem quadPhase_secondDeriv_eq (β q r x : ℝ) :
    4 * Real.pi * Complex.I * β * q ^ 2 - 16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * x + r) ^ 2
      = (4 * Real.pi * Complex.I * β * q ^ 2 : ℂ)
        + (-(16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * x + r) ^ 2) : ℂ) := by
  ring

/-- **Weighted oscillatory-integral bound.**  For a monotone nonnegative weight `w` and a
`C²` phase `φ` with `φ'' ≥ lam > 0`, `‖∫_0^P (w s : ℂ) * (cos (φ s) : ℂ)‖ ≤ 4 w P / √lam`.
This is the complexified form of `Commons.Analysis.Calculus.integral_second_derivative_test`. -/
theorem norm_integral_weight_cos_le {P lam : ℝ} (hP : 0 ≤ P) (hlam : 0 < lam) {w φ : ℝ → ℝ}
    (hw : MonotoneOn w (Set.Icc 0 P)) (hw0 : ∀ x ∈ Set.Icc 0 P, 0 ≤ w x)
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc 0 P))
    (h2 : ∀ x ∈ Set.Ioo 0 P, lam ≤ deriv (deriv φ) x) :
    ‖∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.cos (φ s) : ℝ) : ℂ)‖
      ≤ 4 * w P / Real.sqrt lam := by
  have h := Commons.Analysis.Calculus.integral_second_derivative_test hP hlam hw hw0 hφ h2
  have hcast : (∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.cos (φ s) : ℝ) : ℂ))
      = ((∫ s in (0:ℝ)..P, w s * Real.cos (φ s) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro s hs
    push_cast
    ring
  rw [hcast]
  have hn : ‖(((∫ s in (0:ℝ)..P, w s * Real.cos (φ s)) : ℝ) : ℂ)‖
      = |∫ s in (0:ℝ)..P, w s * Real.cos (φ s)| := RCLike.norm_ofReal _
  rw [hn]
  exact h

/-- **Weighted oscillatory-integral bound, sine version.** -/
theorem norm_integral_weight_sin_le {P lam : ℝ} (hP : 0 ≤ P) (hlam : 0 < lam) {w φ : ℝ → ℝ}
    (hw : MonotoneOn w (Set.Icc 0 P)) (hw0 : ∀ x ∈ Set.Icc 0 P, 0 ≤ w x)
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc 0 P))
    (h2 : ∀ x ∈ Set.Ioo 0 P, lam ≤ deriv (deriv φ) x) :
    ‖∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.sin (φ s) : ℝ) : ℂ)‖
      ≤ 4 * w P / Real.sqrt lam := by
  have hφ' : ContDiffOn ℝ 2 (fun s : ℝ => φ s - Real.pi / 2) (Set.Icc 0 P) :=
    hφ.sub contDiffOn_const
  have h2' : ∀ x ∈ Set.Ioo 0 P, lam ≤ deriv (deriv (fun s : ℝ => φ s - Real.pi / 2)) x := by
    intro x hx
    have hev : deriv (fun s : ℝ => φ s - Real.pi / 2) =ᶠ[nhds x] deriv φ := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      have hyd : DifferentiableAt ℝ φ y :=
        (hφ.contDiffAt (Icc_mem_nhds hy.1 hy.2)).differentiableAt (by norm_num)
      rw [show (fun s : ℝ => φ s - Real.pi / 2) = (φ - fun _ => Real.pi / 2) from rfl,
        deriv_sub hyd (differentiableAt_const _), deriv_const]
      ring
    rw [hev.deriv_eq]
    exact h2 x hx
  have h := norm_integral_weight_cos_le hP hlam hw hw0 hφ' h2'
  refine le_trans (le_of_eq ?_) h
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hcs : Real.cos (φ s - Real.pi / 2) = Real.sin (φ s) := by
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  show ((w s : ℝ) : ℂ) * ((Real.sin (φ s) : ℝ) : ℂ)
    = ((w s : ℝ) : ℂ) * ((Real.cos (φ s - Real.pi / 2) : ℝ) : ℂ)
  rw [← hcs]


lemma deriv_deriv_add_const_mul_id {θ : ℝ → ℝ} {c x : ℝ} (h : ContDiffAt ℝ 2 θ x) :
    deriv (deriv (fun s : ℝ => θ s + c * s)) x = deriv (deriv θ) x := by
  have h1 : HasDerivAt (deriv θ) (deriv (deriv θ) x) x :=
    ((h.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have h2 : HasDerivAt (fun y => deriv θ y + c) (deriv (deriv θ) x) x := h1.add_const c
  have heq : deriv (fun s : ℝ => θ s + c * s) =ᶠ[nhds x] fun y => deriv θ y + c := by
    filter_upwards [h.eventually (by norm_num)] with y hy
    have hd : DifferentiableAt ℝ θ y := hy.differentiableAt (by norm_num)
    have hd2 : DifferentiableAt ℝ (fun s : ℝ => c * s) y :=
      (differentiableAt_id (x := y)).const_mul c
    have hdy : deriv (fun s : ℝ => c * s) y = c := by
      rw [show (fun s : ℝ => c * s) = (fun s => c * id s) from rfl,
        deriv_const_mul c differentiableAt_id, deriv_id, mul_one]
    rw [show (fun s : ℝ => θ s + c * s) = (θ + fun s : ℝ => c * s) from rfl,
      deriv_add hd hd2, hdy]
  exact (heq.hasDerivAt_iff.mpr h2).deriv

lemma second_deriv_shift {P : ℝ} {θ : ℝ → ℝ} (hθ : ContDiffOn ℝ 2 θ (Set.Icc 0 P)) {c : ℝ} {x : ℝ}
    (hx : x ∈ Set.Ioo 0 P) :
    deriv (deriv (fun s : ℝ => θ s + c * s)) x = deriv (deriv θ) x ∧
    deriv (deriv (fun s : ℝ => θ s - c * s)) x = deriv (deriv θ) x := by
  have hca : ContDiffAt ℝ 2 θ x := hθ.contDiffAt (Icc_mem_nhds hx.1 hx.2)
  refine ⟨deriv_deriv_add_const_mul_id hca, ?_⟩
  have hfe : (fun s : ℝ => θ s - c * s) = fun s : ℝ => θ s + (-c) * s := by
    funext s; ring
  rw [hfe, deriv_deriv_add_const_mul_id hca]

theorem norm_integral_weight_cos_mul_cos_le {P lam m : ℝ} (hP : 0 ≤ P) (hlam : 0 < lam)
    {w θ : ℝ → ℝ} (hw : MonotoneOn w (Set.Icc 0 P)) (hw0 : ∀ x ∈ Set.Icc 0 P, 0 ≤ w x)
    (hwc : ContinuousOn w (Set.Icc 0 P))
    (hθ : ContDiffOn ℝ 2 θ (Set.Icc 0 P))
    (h2 : ∀ x ∈ Set.Ioo 0 P, lam ≤ deriv (deriv θ) x) :
    ‖∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.cos (2 * Real.pi * m * s) : ℝ) : ℂ)
        * ((Real.cos (θ s) : ℝ) : ℂ)‖ ≤ 4 * w P / Real.sqrt lam := by
  have hφ₁ : ContDiffOn ℝ 2 (fun s : ℝ => θ s - 2 * Real.pi * m * s) (Set.Icc 0 P) :=
    hθ.sub (contDiffOn_const.mul contDiffOn_id)
  have hφ₂ : ContDiffOn ℝ 2 (fun s : ℝ => θ s + 2 * Real.pi * m * s) (Set.Icc 0 P) :=
    hθ.add (contDiffOn_const.mul contDiffOn_id)
  have h2₁ : ∀ x ∈ Set.Ioo 0 P, lam ≤ deriv (deriv (fun s : ℝ => θ s - 2*Real.pi*m*s)) x := by
    intro x hx; rw [(second_deriv_shift hθ hx).2]; exact h2 x hx
  have h2₂ : ∀ x ∈ Set.Ioo 0 P, lam ≤ deriv (deriv (fun s : ℝ => θ s + 2*Real.pi*m*s)) x := by
    intro x hx; rw [(second_deriv_shift hθ hx).1]; exact h2 x hx
  have hcos : (fun s : ℝ => ((w s : ℝ) : ℂ) * ((Real.cos (2 * Real.pi * m * s) : ℝ) : ℂ)
        * ((Real.cos (θ s) : ℝ) : ℂ))
      = fun s : ℝ => (1/2:ℂ) * (((w s : ℝ) : ℂ) * ((Real.cos (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ)
          + ((w s : ℝ) : ℂ) * ((Real.cos (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ)) := by
    funext s
    rw [Real.cos_sub, Real.cos_add]
    push_cast
    ring
  have hF₁i : IntervalIntegrable
      (fun s : ℝ => ((w s : ℝ) : ℂ) * ((Real.cos (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ))
      volume (0:ℝ) P := by
    refine (show ContinuousOn (fun s : ℝ => ((w s : ℝ) : ℂ)
        * ((Real.cos (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ)) (Set.uIcc (0:ℝ) P) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hP]
    exact (Complex.continuous_ofReal.comp_continuousOn hwc).mul
      (Complex.continuous_ofReal.comp_continuousOn (Real.continuous_cos.comp_continuousOn hφ₁.continuousOn))
  have hF₂i : IntervalIntegrable
      (fun s : ℝ => ((w s : ℝ) : ℂ) * ((Real.cos (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ))
      volume (0:ℝ) P := by
    refine (show ContinuousOn (fun s : ℝ => ((w s : ℝ) : ℂ)
        * ((Real.cos (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ)) (Set.uIcc (0:ℝ) P) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hP]
    exact (Complex.continuous_ofReal.comp_continuousOn hwc).mul
      (Complex.continuous_ofReal.comp_continuousOn (Real.continuous_cos.comp_continuousOn hφ₂.continuousOn))
  rw [hcos, intervalIntegral.integral_const_mul, intervalIntegral.integral_add hF₁i hF₂i, norm_mul]
  have h12 : ‖((1/2 : ℂ))‖ = (1/2 : ℝ) := by norm_num
  rw [h12]
  have hb₁ := norm_integral_weight_cos_le hP hlam hw hw0 hφ₁ h2₁
  have hb₂ := norm_integral_weight_cos_le hP hlam hw hw0 hφ₂ h2₂
  calc (1/2 : ℝ) * ‖(∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.cos (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ))
          + (∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.cos (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ))‖
      ≤ (1/2 : ℝ) * (‖∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.cos (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ)‖
          + ‖∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.cos (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ)‖) := by
        have := norm_add_le (∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.cos (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ))
          (∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.cos (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ))
        nlinarith
    _ ≤ (1/2 : ℝ) * (4 * w P / Real.sqrt lam + 4 * w P / Real.sqrt lam) := by
        have := add_le_add hb₁ hb₂
        nlinarith
    _ = 4 * w P / Real.sqrt lam := by ring

theorem norm_integral_weight_cos_mul_sin_le {P lam m : ℝ} (hP : 0 ≤ P) (hlam : 0 < lam)
    {w θ : ℝ → ℝ} (hw : MonotoneOn w (Set.Icc 0 P)) (hw0 : ∀ x ∈ Set.Icc 0 P, 0 ≤ w x)
    (hwc : ContinuousOn w (Set.Icc 0 P))
    (hθ : ContDiffOn ℝ 2 θ (Set.Icc 0 P))
    (h2 : ∀ x ∈ Set.Ioo 0 P, lam ≤ deriv (deriv θ) x) :
    ‖∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.cos (2 * Real.pi * m * s) : ℝ) : ℂ)
        * ((Real.sin (θ s) : ℝ) : ℂ)‖ ≤ 4 * w P / Real.sqrt lam := by
  have hφ₁ : ContDiffOn ℝ 2 (fun s : ℝ => θ s - 2 * Real.pi * m * s) (Set.Icc 0 P) :=
    hθ.sub (contDiffOn_const.mul contDiffOn_id)
  have hφ₂ : ContDiffOn ℝ 2 (fun s : ℝ => θ s + 2 * Real.pi * m * s) (Set.Icc 0 P) :=
    hθ.add (contDiffOn_const.mul contDiffOn_id)
  have h2₁ : ∀ x ∈ Set.Ioo 0 P, lam ≤ deriv (deriv (fun s : ℝ => θ s - 2*Real.pi*m*s)) x := by
    intro x hx; rw [(second_deriv_shift hθ hx).2]; exact h2 x hx
  have h2₂ : ∀ x ∈ Set.Ioo 0 P, lam ≤ deriv (deriv (fun s : ℝ => θ s + 2*Real.pi*m*s)) x := by
    intro x hx; rw [(second_deriv_shift hθ hx).1]; exact h2 x hx
  have hsin : (fun s : ℝ => ((w s : ℝ) : ℂ) * ((Real.cos (2 * Real.pi * m * s) : ℝ) : ℂ)
        * ((Real.sin (θ s) : ℝ) : ℂ))
      = fun s : ℝ => (1/2:ℂ) * (((w s : ℝ) : ℂ) * ((Real.sin (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ)
          + ((w s : ℝ) : ℂ) * ((Real.sin (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ)) := by
    funext s
    rw [Real.sin_add, Real.sin_sub]
    push_cast
    ring
  have hF₁i : IntervalIntegrable
      (fun s : ℝ => ((w s : ℝ) : ℂ) * ((Real.sin (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ))
      volume (0:ℝ) P := by
    refine (show ContinuousOn (fun s : ℝ => ((w s : ℝ) : ℂ)
        * ((Real.sin (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ)) (Set.uIcc (0:ℝ) P) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hP]
    exact (Complex.continuous_ofReal.comp_continuousOn hwc).mul
      (Complex.continuous_ofReal.comp_continuousOn (Real.continuous_sin.comp_continuousOn hφ₁.continuousOn))
  have hF₂i : IntervalIntegrable
      (fun s : ℝ => ((w s : ℝ) : ℂ) * ((Real.sin (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ))
      volume (0:ℝ) P := by
    refine (show ContinuousOn (fun s : ℝ => ((w s : ℝ) : ℂ)
        * ((Real.sin (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ)) (Set.uIcc (0:ℝ) P) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hP]
    exact (Complex.continuous_ofReal.comp_continuousOn hwc).mul
      (Complex.continuous_ofReal.comp_continuousOn (Real.continuous_sin.comp_continuousOn hφ₂.continuousOn))
  rw [hsin, intervalIntegral.integral_const_mul, intervalIntegral.integral_add hF₂i hF₁i, norm_mul]
  have h12 : ‖((1/2 : ℂ))‖ = (1/2 : ℝ) := by norm_num
  rw [h12]
  have hb₁ := norm_integral_weight_sin_le hP hlam hw hw0 hφ₁ h2₁
  have hb₂ := norm_integral_weight_sin_le hP hlam hw hw0 hφ₂ h2₂
  calc (1/2 : ℝ) * ‖(∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.sin (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ))
          + (∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.sin (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ))‖
      ≤ (1/2 : ℝ) * (‖∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.sin (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ)‖
          + ‖∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.sin (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ)‖) := by
        have := norm_add_le (∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.sin (θ s + 2 * Real.pi * m * s) : ℝ) : ℂ))
          (∫ s in (0:ℝ)..P, ((w s : ℝ) : ℂ) * ((Real.sin (θ s - 2 * Real.pi * m * s) : ℝ) : ℂ))
        nlinarith
    _ ≤ (1/2 : ℝ) * (4 * w P / Real.sqrt lam + 4 * w P / Real.sqrt lam) := by
        have := add_le_add hb₂ hb₁
        nlinarith
    _ = 4 * w P / Real.sqrt lam := by ring

lemma deriv_deriv_quad (c q r : ℝ) (x : ℝ) :
    deriv (deriv (fun s : ℝ => c * (q * s + r) ^ 2)) x = 2 * c * q ^ 2 := by
  have hderiv : deriv (fun s : ℝ => c * (q * s + r) ^ 2)
      = fun s => c * (2 * (q * s + r) * q) := by
    funext t
    have ht : HasDerivAt (fun s : ℝ => q * s + r) q t := by
      simpa using ((hasDerivAt_id t).const_mul q).add_const r
    have h2 : HasDerivAt (fun s : ℝ => (q * s + r) ^ 2) (2 * (q * t + r) * q) t :=
      (ht.pow 2).congr_deriv (by ring)
    exact (h2.const_mul c).deriv
  rw [hderiv]
  have h2 : HasDerivAt (fun s : ℝ => c * (2 * (q * s + r) * q)) (c * (2 * q * q)) x := by
    have hx1 : HasDerivAt (fun s : ℝ => q * s + r) q x := by
      simpa using ((hasDerivAt_id x).const_mul q).add_const r
    have h3 : HasDerivAt (fun s : ℝ => 2 * (q * s + r)) (2 * q) x := hx1.const_mul 2
    have h4 : HasDerivAt (fun s : ℝ => 2 * (q * s + r) * q) (2 * q * q) x := by
      simpa using h3.mul_const q
    simpa using h4.const_mul c
  rw [h2.deriv]
  ring

/-- `exp (2πi y) = cos (2πy) + sin (2πy) i`. -/
lemma expTwoPiI_eq_cos_add_sin (y : ℝ) :
    expTwoPiI y
      = (Real.cos (2 * Real.pi * y) : ℂ) + (Real.sin (2 * Real.pi * y) : ℂ) * Complex.I := by
  rw [expTwoPiI_def]
  have h : (2 * Real.pi * Complex.I * (y : ℂ)) = (((2 * Real.pi * y : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I]

lemma cos_phase_abs (a y : ℝ) :
    Real.cos (2 * Real.pi * a * y) = Real.cos (2 * Real.pi * |a| * y) := by
  rcases le_or_gt 0 a with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, show 2 * Real.pi * a * y = -(2 * Real.pi * (-a) * y) by ring, Real.cos_neg]

lemma exists_sign_sin_phase (a : ℝ) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ y : ℝ, Real.sin (2 * Real.pi * a * y) = σ * Real.sin (2 * Real.pi * |a| * y) := by
  rcases le_or_gt 0 a with h | h
  · exact ⟨1, Or.inl rfl, fun y => by rw [abs_of_nonneg h, one_mul]⟩
  · rw [abs_of_neg h]
    refine ⟨-1, Or.inr rfl, fun y => ?_⟩
    rw [show 2 * Real.pi * a * y = -(2 * Real.pi * (-a) * y) by ring, Real.sin_neg]
    ring


theorem quadratic_cos_coeff_bound (β : ℝ) {q r P : ℝ} (hq : 0 < q) (hr : 0 ≤ r)
    (hP : 0 ≤ P) (hβ : |β| * q * (q * P + r) ≤ 4) (m : ℕ) :
    ‖∫ s in (0:ℝ)..P, ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
        ((4 * Real.pi * Complex.I * β * q ^ 2 - 16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) *
          expTwoPiI (β * (q * s + r) ^ 2))‖
      ≤ 100 + 2000 * |β| * Real.sqrt |β| * q * (q * P + r) ^ 2 := by
  by_cases hβ0 : β = 0
  · subst hβ0
    simp
  have hb0 : 0 < |β| := abs_pos.mpr hβ0
  have hlam_pos : 0 < 4 * Real.pi * |β| * q ^ 2 := by positivity
  -- (1) arithmetic
  have hA1 : 4 * Real.pi * |β| * q ^ 2 * P ≤ 100 := by
    have h1 : |β| * q ^ 2 * P ≤ 4 := by
      have h2 : q ^ 2 * P ≤ q * (q * P + r) := by nlinarith [hq, hr, hP]
      nlinarith [h2, abs_nonneg β, hβ, hq]
    nlinarith [h1, Real.pi_lt_four, Real.pi_pos]
  have hA2 : 8 * (16 * Real.pi^2 * β^2 * q^2 * (q*P+r)^2) / Real.sqrt (4 * Real.pi * |β| * q^2)
      ≤ 2000 * |β| * Real.sqrt |β| * q * (q*P+r)^2 := by
    have hlam : Real.sqrt (4 * Real.pi * |β| * q^2)
        = 2 * q * (Real.sqrt Real.pi * Real.sqrt |β|) := by
      have h : (2*q)^2 * (Real.pi * |β|) = 4 * Real.pi * |β| * q^2 := by ring
      rw [← h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul Real.pi_pos.le]
    set u : ℝ := Real.sqrt |β| with hu
    set v : ℝ := Real.sqrt Real.pi with hv
    have hu0 : 0 ≤ u := by rw [hu]; exact Real.sqrt_nonneg _
    have hv0 : 0 ≤ v := by rw [hv]; exact Real.sqrt_nonneg _
    have hv2 : v ≤ 2 := by
      rw [hv]
      have h4 : Real.sqrt 4 = 2 := by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [← h4]
      exact Real.sqrt_le_sqrt Real.pi_lt_four.le
    have hu2 : u^2 = |β| := by rw [hu]; exact Real.sq_sqrt (abs_nonneg β)
    have hv2' : v^2 = Real.pi := by rw [hv]; exact Real.sq_sqrt Real.pi_pos.le
    rw [hlam]
    rw [show β^2 = u^2 * u^2 from by rw [← sq_abs, hu2]; ring]
    rw [show Real.pi^2 = v^2 * v^2 from by rw [hv2']; ring]
    rw [show |β| = u^2 from hu2.symm]
    have hv3 : v^3 ≤ 8 := by nlinarith [hv0, hv2, sq_nonneg v]
    have hkey : 128 * v^4 ≤ 4000 * v := by nlinarith [hv0, hv3]
    have hC : 0 ≤ u^4 * q^2 * (q*P+r)^2 := by positivity
    rw [div_le_iff₀ (by positivity)]
    ring_nf
    nlinarith [hkey, hC]
  -- (2) weight and phase data
  have hw_mono : MonotoneOn (fun s : ℝ => 16 * Real.pi^2 * β^2 * q^2 * (q*s+r)^2) (Set.Icc 0 P) := by
    intro x hx y hy hxy
    have hc : 0 ≤ 16 * Real.pi^2 * β^2 * q^2 := by positivity
    have hx1 : 0 ≤ q * x + r := by nlinarith [hx.1, hq, hr]
    have hxy' : q * x + r ≤ q * y + r := by nlinarith [hxy, hq]
    have h2 : (q*x+r)^2 ≤ (q*y+r)^2 := by nlinarith [hx1, hxy']
    nlinarith [hc, h2, sq_nonneg (q*x+r)]
  have hw0 : ∀ x ∈ Set.Icc 0 P, 0 ≤ 16 * Real.pi^2 * β^2 * q^2 * (q*x+r)^2 := by
    intro x _; positivity
  have hwcont : ContinuousOn (fun s : ℝ => 16 * Real.pi^2 * β^2 * q^2 * (q*s+r)^2) (Set.Icc 0 P) := by
    fun_prop
  have hθcont : ContDiffOn ℝ 2 (fun s : ℝ => 2 * Real.pi * (|β| * (q * s + r) ^ 2)) (Set.Icc 0 P) := by
    fun_prop
  have h2θ : ∀ x ∈ Set.Ioo 0 P, 4 * Real.pi * |β| * q ^ 2
      ≤ deriv (deriv (fun s : ℝ => 2 * Real.pi * (|β| * (q * s + r) ^ 2))) x := by
    intro x hx
    rw [show (fun s : ℝ => 2 * Real.pi * (|β| * (q * s + r) ^ 2))
          = (fun s : ℝ => (2 * Real.pi * |β|) * (q * s + r) ^ 2) from by funext s; ring,
        deriv_deriv_quad (2 * Real.pi * |β|) q r x]
    exact le_of_eq (by ring)
  -- (3) the two product-to-sum bounds
  have hPLcos := norm_integral_weight_cos_mul_cos_le (P := P) (lam := 4 * Real.pi * |β| * q^2)
      (m := (m:ℝ)) (w := fun s : ℝ => 16 * Real.pi^2 * β^2 * q^2 * (q*s+r)^2)
      (θ := fun s : ℝ => 2 * Real.pi * (|β| * (q * s + r) ^ 2))
      hP hlam_pos hw_mono hw0 hwcont hθcont h2θ
  have hPLsin := norm_integral_weight_cos_mul_sin_le (P := P) (lam := 4 * Real.pi * |β| * q^2)
      (m := (m:ℝ)) (w := fun s : ℝ => 16 * Real.pi^2 * β^2 * q^2 * (q*s+r)^2)
      (θ := fun s : ℝ => 2 * Real.pi * (|β| * (q * s + r) ^ 2))
      hP hlam_pos hw_mono hw0 hwcont hθcont h2θ
  -- (4) phase comparisons
  have hcosEq : ∀ s : ℝ, Real.cos (2 * Real.pi * (β * (q*s+r)^2))
      = Real.cos (2 * Real.pi * (|β| * (q*s+r)^2)) := by
    intro s
    have h := cos_phase_abs β ((q*s+r)^2)
    rwa [show 2 * Real.pi * β * (q*s+r)^2 = 2 * Real.pi * (β * (q*s+r)^2) by ring,
         show 2 * Real.pi * |β| * (q*s+r)^2 = 2 * Real.pi * (|β| * (q*s+r)^2) by ring] at h
  obtain ⟨σ, hσ1, hσ⟩ := exists_sign_sin_phase β
  have hsinEq : ∀ s : ℝ, Real.sin (2 * Real.pi * (β * (q*s+r)^2))
      = σ * Real.sin (2 * Real.pi * (|β| * (q*s+r)^2)) := by
    intro s
    have h := hσ ((q*s+r)^2)
    rwa [show 2 * Real.pi * β * (q*s+r)^2 = 2 * Real.pi * (β * (q*s+r)^2) by ring,
         show 2 * Real.pi * |β| * (q*s+r)^2 = 2 * Real.pi * (|β| * (q*s+r)^2) by ring] at h
  have hσnorm : ‖((σ : ℝ) : ℂ)‖ = 1 := by
    rcases hσ1 with h | h <;> rw [h] <;> simp
  have hGexp : ∀ s : ℝ, expTwoPiI (β * (q*s+r)^2)
      = (Real.cos (2 * Real.pi * (β * (q*s+r)^2)) : ℂ)
        + (Real.sin (2 * Real.pi * (β * (q*s+r)^2)) : ℂ) * Complex.I :=
    fun s => expTwoPiI_eq_cos_add_sin _
  -- (5) decomposition of the integral
  set W : ℝ → ℂ := fun s => ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
      (4 * Real.pi * Complex.I * β * q ^ 2) * expTwoPiI (β * (q * s + r) ^ 2) with hW
  set V : ℝ → ℂ := fun s => ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
      (-(16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2)) * expTwoPiI (β * (q * s + r) ^ 2) with hV
  set Wu : ℝ → ℂ := fun s => ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
      (16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) * expTwoPiI (β * (q * s + r) ^ 2) with hWu
  have hWi : IntervalIntegrable W volume (0:ℝ) P := by
    apply Continuous.intervalIntegrable; rw [hW]; simp only [expTwoPiI_def]; fun_prop
  have hVi : IntervalIntegrable V volume (0:ℝ) P := by
    apply Continuous.intervalIntegrable; rw [hV]; simp only [expTwoPiI_def]; fun_prop
  have hsplit : (∫ s in (0:ℝ)..P, ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
        ((4 * Real.pi * Complex.I * β * q ^ 2 - 16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) *
          expTwoPiI (β * (q * s + r) ^ 2)))
      = (∫ s in (0:ℝ)..P, W s) + (∫ s in (0:ℝ)..P, V s) := by
    rw [← intervalIntegral.integral_add hWi hVi]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [hW, hV]
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hWb : ‖∫ s in (0:ℝ)..P, W s‖ ≤ 100 := by
    have hWcongr : (∫ s in (0:ℝ)..P, W s) = (4 * Real.pi * Complex.I * β * q ^ 2 : ℂ) *
        (∫ s in (0:ℝ)..P, ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) * expTwoPiI (β * (q * s + r) ^ 2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [hW]; ring
    rw [hWcongr, norm_mul]
    have hc1 : ‖(4 * Real.pi * Complex.I * β * q ^ 2 : ℂ)‖ = 4 * Real.pi * |β| * q ^ 2 := by
      rw [show (4 * Real.pi * Complex.I * β * q ^ 2 : ℂ)
            = ((4 * Real.pi * β * q^2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_mul, Complex.norm_I, mul_one]
      rw [show ‖(((4 * Real.pi * β * q^2 : ℝ)) : ℂ)‖ = |4 * Real.pi * β * q^2| from RCLike.norm_ofReal _]
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi), abs_of_nonneg (sq_nonneg q)]
    rw [hc1]
    have hbound : ‖(∫ s in (0:ℝ)..P, ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ)
        * expTwoPiI (β * (q * s + r) ^ 2))‖ ≤ P := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := P) (C := 1)
        (f := fun s : ℝ => ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) * expTwoPiI (β * (q * s + r) ^ 2))
        (fun x hx => by
          rw [norm_mul, show ‖(((Real.cos (2 * Real.pi * (m:ℝ) * x) : ℝ)) : ℂ)‖ = |Real.cos (2 * Real.pi * (m:ℝ) * x)| from RCLike.norm_ofReal _, norm_expTwoPiI, mul_one]
          exact Real.abs_cos_le_one _)
      rw [one_mul, sub_zero, abs_of_nonneg hP] at h
      exact h
    have hcoef : 0 ≤ 4 * Real.pi * |β| * q ^ 2 := by positivity
    nlinarith [hbound, hA1, hcoef]
  have hVb : ‖∫ s in (0:ℝ)..P, V s‖
      ≤ 8 * (16 * Real.pi^2 * β^2 * q^2 * (q*P+r)^2) / Real.sqrt (4 * Real.pi * |β| * q^2) := by
    have hVcongr : (∫ s in (0:ℝ)..P, V s) = -(∫ s in (0:ℝ)..P, Wu s) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [hV, hWu]; ring
    rw [hVcongr, norm_neg]
    have hWuG : (∫ s in (0:ℝ)..P, Wu s)
        = (∫ s in (0:ℝ)..P, ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
              (16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) * (Real.cos (2 * Real.pi * (β * (q*s+r)^2)) : ℂ))
          + Complex.I * (∫ s in (0:ℝ)..P, ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
              (16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) * (Real.sin (2 * Real.pi * (β * (q*s+r)^2)) : ℂ)) := by
      rw [← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_add
            (by apply Continuous.intervalIntegrable; fun_prop : IntervalIntegrable
              (fun s : ℝ => ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
                (16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) * (Real.cos (2 * Real.pi * (β * (q*s+r)^2)) : ℂ)) volume (0:ℝ) P)
            (by apply Continuous.intervalIntegrable; fun_prop : IntervalIntegrable
              (fun s : ℝ => Complex.I * (((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
                (16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) * (Real.sin (2 * Real.pi * (β * (q*s+r)^2)) : ℂ))) volume (0:ℝ) P)]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [hWu, hGexp]
      ring
    rw [hWuG]
    refine le_trans (norm_add_le _ _) ?_
    have hI1 : ‖∫ s in (0:ℝ)..P, ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
              (16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) * (Real.cos (2 * Real.pi * (β * (q*s+r)^2)) : ℂ)‖
          ≤ 4 * (16 * Real.pi^2 * β^2 * q^2 * (q*P+r)^2) / Real.sqrt (4 * Real.pi * |β| * q^2) := by
      rw [show (∫ s in (0:ℝ)..P, ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
              (16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) * (Real.cos (2 * Real.pi * (β * (q*s+r)^2)) : ℂ))
            = (∫ s in (0:ℝ)..P, ((16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2 : ℝ) : ℂ) *
              ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) * (Real.cos (2 * Real.pi * (|β| * (q*s+r)^2)) : ℂ)) from by
        apply intervalIntegral.integral_congr
        intro s _
        simp only []
        rw [hcosEq s]; push_cast; ring]
      exact hPLcos
    have hI2 : ‖∫ s in (0:ℝ)..P, ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
              (16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) * (Real.sin (2 * Real.pi * (β * (q*s+r)^2)) : ℂ)‖
          ≤ 4 * (16 * Real.pi^2 * β^2 * q^2 * (q*P+r)^2) / Real.sqrt (4 * Real.pi * |β| * q^2) := by
      rw [show (∫ s in (0:ℝ)..P, ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
              (16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) * (Real.sin (2 * Real.pi * (β * (q*s+r)^2)) : ℂ))
            = ((σ : ℝ) : ℂ) * (∫ s in (0:ℝ)..P, ((16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2 : ℝ) : ℂ) *
              ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) * (Real.sin (2 * Real.pi * (|β| * (q*s+r)^2)) : ℂ)) from by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro s _
        simp only []
        rw [hsinEq s]; push_cast; ring]
      rw [norm_mul, hσnorm, one_mul]
      exact hPLsin
    have hI2b : ‖Complex.I * (∫ s in (0:ℝ)..P, ((Real.cos (2 * Real.pi * (m:ℝ) * s) : ℝ) : ℂ) *
              (16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) * (Real.sin (2 * Real.pi * (β * (q*s+r)^2)) : ℂ))‖
          ≤ 4 * (16 * Real.pi^2 * β^2 * q^2 * (q*P+r)^2) / Real.sqrt (4 * Real.pi * |β| * q^2) := by
      rw [norm_mul, Complex.norm_I, one_mul]
      exact hI2
    have he : 4 * (16 * Real.pi^2 * β^2 * q^2 * (q*P+r)^2) / Real.sqrt (4 * Real.pi * |β| * q^2)
        + 4 * (16 * Real.pi^2 * β^2 * q^2 * (q*P+r)^2) / Real.sqrt (4 * Real.pi * |β| * q^2)
        = 8 * (16 * Real.pi^2 * β^2 * q^2 * (q*P+r)^2) / Real.sqrt (4 * Real.pi * |β| * q^2) := by
      ring
    linarith [hI1, hI2b, he]
  linarith



/-! ### The `ℓ²` tail bound for the cosine series -/

/-- Weighted `ℓ²`-tail bound: if `‖F k‖ ≤ A` for all `k` then `‖∑_k (1/(k+1)²) F k‖ ≤ A π²/6`. -/
theorem norm_tsum_one_div_sq_mul_le (A : ℝ) {F : ℕ → ℂ} (hF : ∀ k, ‖F k‖ ≤ A) :
    ‖∑' k : ℕ, (1 / ((k : ℝ) + 1) ^ 2) * F k‖ ≤ A * Real.pi ^ 2 / 6 := by
  have hcong : (∑' k : ℕ, (1 / ((k : ℝ) + 1) ^ 2) * F k)
      = ∑' k : ℕ, ((1 / ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * F k := by
    apply tsum_congr
    intro k
    rw [show ((1 / ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) = (1 / ((k : ℝ) + 1) ^ 2) by push_cast; ring]
  rw [hcong]
  have hcollapse : (Real.pi ^ 2 / 6 : ℝ) + ∑ i ∈ Finset.range 1, (1:ℝ) / (i:ℝ)^2 = Real.pi ^ 2 / 6 := by
    rw [Finset.sum_range_one]; norm_num
  have hzeta : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h2 : HasSum (fun n : ℕ => (1:ℝ) / (n:ℝ)^2)
        ((Real.pi^2/6) + ∑ i ∈ Finset.range 1, (1:ℝ)/(i:ℝ)^2) := by
      rw [hcollapse]; exact hasSum_zeta_two
    have h : HasSum (fun n : ℕ => (1:ℝ) / (((n+1 : ℕ) : ℝ))^2) (Real.pi^2/6) :=
      (hasSum_nat_add_iff (f := fun n : ℕ => (1:ℝ)/(n:ℝ)^2) 1).2 h2
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hsum1 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := hzeta.summable
  have hbase : Summable (fun k : ℕ => A * (1 / ((k : ℝ) + 1) ^ 2)) := hsum1.mul_left A
  have hcmp : ∀ k : ℕ, (1 / ((k : ℝ) + 1) ^ 2) * ‖F k‖ ≤ A * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    have h1 : 0 ≤ 1 / ((k : ℝ) + 1) ^ 2 := by positivity
    calc (1 / ((k : ℝ) + 1) ^ 2) * ‖F k‖ ≤ (1 / ((k : ℝ) + 1) ^ 2) * A :=
          mul_le_mul_of_nonneg_left (hF k) h1
      _ = A * (1 / ((k : ℝ) + 1) ^ 2) := by ring
  have hFn : ∀ k : ℕ, ‖((1 / ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * F k‖
      = (1 / ((k : ℝ) + 1) ^ 2) * ‖F k‖ := by
    intro k
    rw [norm_mul,
        show ‖(((1 / ((k : ℝ) + 1) ^ 2 : ℝ)) : ℂ)‖ = |1 / ((k : ℝ) + 1) ^ 2| from RCLike.norm_ofReal _,
        abs_of_nonneg (by positivity)]
  have hsum2 : Summable (fun k : ℕ => ‖((1 / ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * F k‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hbase
    rw [hFn k]
    exact hcmp k
  have hsum3 : Summable (fun k : ℕ => (1 / ((k : ℝ) + 1) ^ 2) * ‖F k‖) := hsum2.congr hFn
  calc ‖∑' k : ℕ, ((1 / ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * F k‖
      ≤ ∑' k : ℕ, ‖((1 / ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * F k‖ := norm_tsum_le_tsum_norm hsum2
    _ = ∑' k : ℕ, (1 / ((k : ℝ) + 1) ^ 2) * ‖F k‖ := tsum_congr hFn
    _ ≤ ∑' k : ℕ, A * (1 / ((k : ℝ) + 1) ^ 2) := Summable.tsum_le_tsum hcmp hsum3 hbase
    _ = A * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := tsum_mul_left
    _ = A * Real.pi ^ 2 / 6 := by rw [hzeta.tsum_eq]; ring

/-! ### The block bound (Euler–Maclaurin + van der Corput) -/

/-- **Block bound (Euler–Maclaurin).**  For `P ≥ 1`, `q > 0`, `r ≥ 0` and `|β| q (qP + r) ≤ 4`,
`‖∑_{p<P} e(β(pq+r)²) − ∫_0^P e(β(qs+r)²) ds‖ ≤ 20 + 2000 |β|^{3/2} q (qP + r)²`. -/
theorem block_bound (β : ℝ) {q r : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (P : ℕ) (hP : 1 ≤ P)
    (hβ : |β| * q * (q * (P:ℝ) + r) ≤ 4) :
    ‖(∑ p ∈ Finset.range P, expTwoPiI (β * (q * (p:ℝ) + r) ^ 2))
        - ∫ s in (0:ℝ)..(P:ℝ), expTwoPiI (β * (q * s + r) ^ 2)‖
      ≤ 20 + 2000 * |β| * Real.sqrt |β| * q * (q * (P:ℝ) + r) ^ 2 := by
  have hPr : (0:ℝ) ≤ (P:ℝ) := by positivity
  set g : ℝ → ℂ := fun s => expTwoPiI (β * (q * s + r) ^ 2) with hg
  set g' : ℝ → ℂ := fun s => 4 * Real.pi * Complex.I * β * q *
      ((((q * s + r : ℝ)) : ℂ) * expTwoPiI (β * (q * s + r) ^ 2)) with hg'
  set g'' : ℝ → ℂ := fun s => (4 * Real.pi * Complex.I * β * q ^ 2
      - 16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) * expTwoPiI (β * (q * s + r) ^ 2) with hg''
  have h1 : ∀ x : ℝ, HasDerivAt g (g' x) x := by
    intro x
    simp only [hg, hg']
    exact (hasDerivAt_quadPhase β q r x).congr_deriv (by push_cast; ring)
  have h2 : ∀ x : ℝ, HasDerivAt g' (g'' x) x := by
    intro x
    simp only [hg', hg'']
    exact (hasDerivAt_quadPhase' β q r x).congr_deriv (by push_cast; ring)
  have hcont : Continuous g'' := by
    simp only [hg'', expTwoPiI_def]; fun_prop
  have hem := Commons.Analysis.EulerMaclaurin.sum_sub_integral_cos_series P hP g g' g'' h1 h2 hcont
  have hL : (∑ p ∈ Finset.range P, expTwoPiI (β * (q * (p:ℝ) + r) ^ 2))
      - ∫ s in (0:ℝ)..(P:ℝ), expTwoPiI (β * (q * s + r) ^ 2)
      = (∑ p ∈ Finset.range P, g p) - ∫ s in (0:ℝ)..(P:ℝ), g s := by
    simp only [hg]
  rw [hL, hem]
  have hc4 : ‖(4 * Real.pi * Complex.I * β * q : ℂ)‖ = 4 * Real.pi * |β| * q := by
    rw [show (4 * Real.pi * Complex.I * β * q : ℂ) = ((4 * Real.pi * β * q : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
        Complex.norm_mul, Complex.norm_I, mul_one,
        show ‖(((4 * Real.pi * β * q : ℝ)) : ℂ)‖ = |4 * Real.pi * β * q| from RCLike.norm_ofReal _,
        abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi), abs_of_nonneg hq.le]
  have hgn : ∀ s ∈ Set.Icc (0:ℝ) (P:ℝ), ‖g' s‖ = 4 * Real.pi * |β| * q * (q * s + r) := by
    intro s hs
    simp only [hg']
    have hs0 : 0 ≤ q * s + r := by
      have h1 : 0 ≤ q * s := mul_nonneg hq.le hs.1
      linarith
    rw [norm_mul, hc4, norm_mul, norm_expTwoPiI, mul_one,
        show ‖(((q * s + r : ℝ)) : ℂ)‖ = |q * s + r| from RCLike.norm_ofReal _,
        abs_of_nonneg hs0]
  have hgn0 : ‖g 0‖ = 1 := by simp only [hg]; exact norm_expTwoPiI _
  have hgnP : ‖g (P:ℝ)‖ = 1 := by simp only [hg]; exact norm_expTwoPiI _
  have hb1 : ‖(g 0 - g (P:ℝ)) / 2‖ ≤ 1 := by
    rw [norm_div, show ‖(2:ℂ)‖ = 2 from by norm_num]
    have h2' : ‖g 0 - g (P:ℝ)‖ ≤ 2 := by
      calc ‖g 0 - g (P:ℝ)‖ ≤ ‖g 0‖ + ‖g (P:ℝ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hgn0, hgnP]; norm_num
    linarith
  have hb2 : ‖(g' (P:ℝ) - g' 0) / 12‖ ≤ 9 := by
    rw [norm_div, show ‖(12:ℂ)‖ = 12 from by norm_num]
    have hpi4 : 0 ≤ 4 * Real.pi := by positivity
    have hnP : ‖g' (P:ℝ)‖ ≤ 16 * Real.pi := by
      rw [hgn (P:ℝ) ⟨hPr, le_rfl⟩]
      nlinarith [hβ, hpi4]
    have hn0 : ‖g' 0‖ ≤ 16 * Real.pi := by
      rw [hgn 0 ⟨le_rfl, hPr⟩]
      simp only [mul_zero, zero_add]
      have hrle : r ≤ q * (P:ℝ) + r := by nlinarith [hPr, hq]
      have habq : 0 ≤ |β| * q := mul_nonneg (abs_nonneg β) hq.le
      have h4 : |β| * q * r ≤ 4 := by nlinarith [hβ, hrle, habq]
      nlinarith [h4, hpi4]
    have h2' : ‖g' (P:ℝ) - g' 0‖ ≤ 32 * Real.pi := by
      calc ‖g' (P:ℝ) - g' 0‖ ≤ ‖g' (P:ℝ)‖ + ‖g' 0‖ := norm_sub_le _ _
        _ ≤ 16 * Real.pi + 16 * Real.pi := add_le_add hnP hn0
        _ = 32 * Real.pi := by ring
    have hπ : 32 * Real.pi / 12 ≤ 9 := by
      have h := Real.pi_lt_d2; linarith
    have hdiv : ‖g' (P:ℝ) - g' 0‖ / 12 ≤ 32 * Real.pi / 12 :=
      div_le_div_of_nonneg_right h2' (by norm_num)
    linarith
  have hb3 : ‖(1 / (2 * Real.pi ^ 2) : ℂ) * (∑' k : ℕ, (1 / ((k : ℝ) + 1) ^ 2) *
        ∫ s in (0 : ℝ)..(P : ℝ), (Real.cos (2 * Real.pi * ((k : ℝ) + 1) * s) : ℂ) * g'' s)‖
      ≤ (100 + 2000 * |β| * Real.sqrt |β| * q * (q * (P:ℝ) + r) ^ 2) / 12 := by
    have hA0 : 0 ≤ 100 + 2000 * |β| * Real.sqrt |β| * q * (q * (P:ℝ) + r) ^ 2 := by positivity
    have hI : ∀ k : ℕ, ‖∫ s in (0:ℝ)..(P:ℝ),
        (Real.cos (2 * Real.pi * ((k : ℝ) + 1) * s) : ℂ) * g'' s‖
        ≤ 100 + 2000 * |β| * Real.sqrt |β| * q * (q * (P:ℝ) + r) ^ 2 := by
      intro k
      have hcoef := quadratic_cos_coeff_bound β hq hr hPr hβ (k+1)
      have hcoe : ∀ s : ℝ,
          (Real.cos (2 * Real.pi * ((k : ℝ) + 1) * s) : ℂ) * g'' s
            = ((Real.cos (2 * Real.pi * (((k+1 : ℕ) : ℝ)) * s) : ℝ) : ℂ) *
              ((4 * Real.pi * Complex.I * β * q ^ 2
                - 16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) *
                expTwoPiI (β * (q * s + r) ^ 2)) := by
        intro s
        rw [hg'']
        push_cast; ring
      rw [show (∫ s in (0:ℝ)..(P:ℝ), (Real.cos (2 * Real.pi * ((k : ℝ) + 1) * s) : ℂ) * g'' s)
            = (∫ s in (0:ℝ)..(P:ℝ), ((Real.cos (2 * Real.pi * (((k+1 : ℕ) : ℝ)) * s) : ℝ) : ℂ) *
              ((4 * Real.pi * Complex.I * β * q ^ 2
                - 16 * Real.pi ^ 2 * β ^ 2 * q ^ 2 * (q * s + r) ^ 2) *
                expTwoPiI (β * (q * s + r) ^ 2))) from by
          apply intervalIntegral.integral_congr
          intro s _
          simp only []
          exact hcoe s]
      exact hcoef
    have hts : ‖∑' k : ℕ, (1 / ((k : ℝ) + 1) ^ 2) *
        (∫ s in (0:ℝ)..(P:ℝ), (Real.cos (2 * Real.pi * ((k : ℝ) + 1) * s) : ℂ) * g'' s)‖
        ≤ (100 + 2000 * |β| * Real.sqrt |β| * q * (q * (P:ℝ) + r) ^ 2) * Real.pi ^ 2 / 6 :=
      norm_tsum_one_div_sq_mul_le _ hI
    rw [norm_mul]
    have hcn : ‖(1 / (2 * Real.pi ^ 2) : ℂ)‖ = 1 / (2 * Real.pi ^ 2) := by
      rw [norm_div]
      have hd : ((2 * Real.pi ^ 2 : ℂ)) = (((2 * Real.pi ^ 2 : ℝ)) : ℂ) := by push_cast; ring
      rw [show ‖(1:ℂ)‖ = 1 from by norm_num,
          show ‖((2 * Real.pi ^ 2 : ℂ))‖ = |(2 * Real.pi ^ 2 : ℝ)| from by
            rw [hd]; exact RCLike.norm_ofReal _,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi ^ 2)]
    rw [hcn]
    calc (1 / (2 * Real.pi ^ 2)) * ‖∑' k : ℕ, (1 / ((k : ℝ) + 1) ^ 2) *
          (∫ s in (0:ℝ)..(P:ℝ), (Real.cos (2 * Real.pi * ((k : ℝ) + 1) * s) : ℂ) * g'' s)‖
        ≤ (1 / (2 * Real.pi ^ 2)) *
            ((100 + 2000 * |β| * Real.sqrt |β| * q * (q * (P:ℝ) + r) ^ 2) * Real.pi ^ 2 / 6) :=
          mul_le_mul_of_nonneg_left hts (by positivity)
      _ = (100 + 2000 * |β| * Real.sqrt |β| * q * (q * (P:ℝ) + r) ^ 2) / 12 := by
          refine mul_left_cancel₀ (by positivity : (Real.pi:ℝ) ^ 2 ≠ 0) ?_
          field_simp; ring
  calc ‖(g 0 - g (P:ℝ)) / 2 + (g' (P:ℝ) - g' 0) / 12
        - (1 / (2 * Real.pi ^ 2) : ℂ) * (∑' k : ℕ, (1 / ((k : ℝ) + 1) ^ 2) *
          ∫ s in (0 : ℝ)..(P : ℝ), (Real.cos (2 * Real.pi * ((k : ℝ) + 1) * s) : ℂ) * g'' s)‖
      ≤ ‖(g 0 - g (P:ℝ)) / 2 + (g' (P:ℝ) - g' 0) / 12‖
        + ‖(1 / (2 * Real.pi ^ 2) : ℂ) * (∑' k : ℕ, (1 / ((k : ℝ) + 1) ^ 2) *
          ∫ s in (0 : ℝ)..(P : ℝ), (Real.cos (2 * Real.pi * ((k : ℝ) + 1) * s) : ℂ) * g'' s)‖ :=
        norm_sub_le _ _
    _ ≤ (‖(g 0 - g (P:ℝ)) / 2‖ + ‖(g' (P:ℝ) - g' 0) / 12‖)
        + (100 + 2000 * |β| * Real.sqrt |β| * q * (q * (P:ℝ) + r) ^ 2) / 12 :=
        add_le_add (norm_add_le _ _) hb3
    _ ≤ 20 + 2000 * |β| * Real.sqrt |β| * q * (q * (P:ℝ) + r) ^ 2 := by
        have hX : 0 ≤ 2000 * |β| * Real.sqrt |β| * q * (q * (P:ℝ) + r) ^ 2 := by positivity
        nlinarith [hb1, hb2, hX]

/-! ### The major-arc asymptotic -/

/-- **Major-arc asymptotic for the square kernel (Bourgain (6.10)).**  For a rational
`a/q` in lowest terms with small denominator `q ≤ N^δ` and `|β| ≤ N^{-1-δ}`, the normalized
quadratic exponential sum splits as a Gauss-sum weight times the oscillatory integral,
up to a power saving:
`(1/N) ∑_{n<N} e((a/q+β) n²) = S(a/q) · v_N(β) + O(N^{-θ})`,
where `S(a/q) = q^{-1} ∑_{r<q} e(a r²/q)` and `v_N(β) = ∫_0^1 e(β N² s²) ds`. -/
theorem quadratic_major_arc_asymptotic :
    ∃ δ : ℝ, 0 < δ ∧ ∃ θ : ℝ, 0 < θ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (a : ℤ) (q : ℕ) (b : ℝ), 1 ≤ N → 0 < q → (q : ℝ) ≤ (N : ℝ) ^ δ →
        Int.gcd a (q : ℤ) = 1 → |b| ≤ ((N : ℝ) ^ (1 + δ))⁻¹ →
        ‖(N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I *
              ((((a : ℝ) / (q : ℝ) + b) * (n : ℝ) ^ 2 : ℝ) : ℂ))
          - ((q : ℂ)⁻¹ * ∑ r ∈ Finset.range q,
              Complex.exp (2 * Real.pi * Complex.I * ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) : ℝ)))
            * (∫ s in (0 : ℝ)..1,
                Complex.exp (2 * Real.pi * Complex.I * ((b * (N : ℝ) ^ 2 * s ^ 2 : ℝ) : ℂ)))‖
        ≤ C * ((N : ℝ) ^ θ)⁻¹ := by
  refine ⟨1/4, by norm_num, 1/8, by norm_num, 10^6, by norm_num, ?_⟩
  intro N a q b hN hq hqN hgcd hb
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqN' : (q:ℝ) ≤ (N:ℝ) := by
    calc (q:ℝ) ≤ (N:ℝ)^((1:ℝ)/4) := hqN
      _ ≤ (N:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = (N:ℝ) := Real.rpow_one _
  have hqN'' : q ≤ N := by exact_mod_cast hqN'
  -- exponent facts
  have hb5 : |b| ≤ (N:ℝ)^(-((5:ℝ)/4)) := by
    have h : (1:ℝ) + 1/4 = 5/4 := by norm_num
    rw [h] at hb
    have heq : (((N:ℝ)^((5:ℝ)/4))⁻¹) = (N:ℝ)^(-((5:ℝ)/4)) :=
      (Real.rpow_neg hNpos.le ((5:ℝ)/4)).symm
    rwa [heq] at hb
  have hbq : |b| * (q:ℝ) ≤ (N:ℝ)^(-(1:ℝ)) := by
    calc |b| * (q:ℝ) ≤ (N:ℝ)^(-((5:ℝ)/4)) * (N:ℝ)^((1:ℝ)/4) :=
          mul_le_mul hb5 hqN (by positivity) (by positivity)
      _ = (N:ℝ)^(-((5:ℝ)/4) + (1:ℝ)/4) := (Real.rpow_add hNpos _ _).symm
      _ = (N:ℝ)^(-(1:ℝ)) := by norm_num
  have hbs : |b| * Real.sqrt |b| ≤ (N:ℝ)^(-((15:ℝ)/8)) := by
    have hs : Real.sqrt |b| ≤ (N:ℝ)^(-((5:ℝ)/8)) := by
      calc Real.sqrt |b| ≤ Real.sqrt ((N:ℝ)^(-((5:ℝ)/4))) := Real.sqrt_le_sqrt hb5
        _ = ((N:ℝ)^(-((5:ℝ)/4)))^((1:ℝ)/2) := Real.sqrt_eq_rpow _
        _ = (N:ℝ)^(-((5:ℝ)/4) * ((1:ℝ)/2)) := (Real.rpow_mul hNpos.le _ _).symm
        _ = (N:ℝ)^(-((5:ℝ)/8)) := by norm_num
    calc |b| * Real.sqrt |b| ≤ (N:ℝ)^(-((5:ℝ)/4)) * (N:ℝ)^(-((5:ℝ)/8)) :=
          mul_le_mul hb5 hs (Real.sqrt_nonneg _) (by positivity)
      _ = (N:ℝ)^(-((5:ℝ)/4) + -((5:ℝ)/8)) := (Real.rpow_add hNpos _ _).symm
      _ = (N:ℝ)^(-((15:ℝ)/8)) := by norm_num
  -- main objects
  set S : ℂ := ∑ n ∈ Finset.range N, expTwoPiI (((a:ℝ)/(q:ℝ) + b) * (n:ℝ)^2) with hS
  set G : ℂ := ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) with hG
  set Iv : ℂ := ∫ t in (0:ℝ)..(N:ℝ), expTwoPiI (b * t^2) with hIv
  set v : ℂ := ∫ s in (0:ℝ)..1, expTwoPiI (b * (N:ℝ)^2 * s^2) with hvdef
  -- integral substitution
  have hv : v = (N:ℝ)⁻¹ * Iv := by
    have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
    rw [hvdef, hIv]
    rw [show (∫ s in (0:ℝ)..1, expTwoPiI (b * (N:ℝ)^2 * s^2))
          = ∫ s in (0:ℝ)..1, (fun t : ℝ => expTwoPiI (b * t^2)) ((N:ℝ) * s) from by
        apply intervalIntegral.integral_congr
        intro s _
        simp only []
        rw [show b * (N:ℝ)^2 * s^2 = b * ((N:ℝ) * s)^2 by ring]]
    rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => expTwoPiI (b * t^2)) hNne]
    simp
  -- residue factorisation
  have hfac : S = ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
      ∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2) := by
    rw [hS]
    exact residue_factor_expTwoPiI N q hq a b
  -- change the goal into `S,G,Iv,v` form
  have hSform : (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * ((((a : ℝ) / (q : ℝ) + b) * (n : ℝ) ^ 2 : ℝ) : ℂ))) = S := by
    rw [hS]; simp only [expTwoPiI_def]
  have hGform : (∑ r ∈ Finset.range q,
        Complex.exp (2 * Real.pi * Complex.I * ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) : ℝ))) = G := by
    rw [hG]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    show expTwoPiI ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ)) = expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2)
    congr 1
    ring
  have hvform : (∫ s in (0 : ℝ)..1,
        Complex.exp (2 * Real.pi * Complex.I * ((b * (N : ℝ) ^ 2 * s ^ 2 : ℝ) : ℂ))) = v := by
    rw [hvdef]; simp only [expTwoPiI_def]
  rw [hSform, hGform, hvform, hv]
  -- per-residue block bound
  have hcont_f : Continuous (fun u : ℝ => expTwoPiI (b * u^2)) := by
    simp only [expTwoPiI_def]; fun_prop
  have hblock : ∀ r ∈ Finset.range q,
      ‖(N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q),
            expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
        - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv)‖
      ≤ (N:ℝ)⁻¹ * (22 + 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2) := by
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
    have hrq' : (r:ℝ) < (q:ℝ) := by exact_mod_cast hrq
    obtain ⟨hPr1, hPr2, hPr3⟩ := div_block_bounds hq hrq hqN''
    set Pr : ℕ := (N + q - 1 - r) / q with hPrdef
    -- key bounds on `q * Pr + r`
    have hPr2' : (q:ℝ) * (Pr:ℝ) + (r:ℝ) ≤ (N:ℝ) + (q:ℝ) := by
      have h1 : Pr * q ≤ N + q - 1 - r := by rw [hPrdef]; exact Nat.div_mul_le_self _ _
      have hcast : ((Pr * q : ℕ) : ℝ) ≤ ((N + q - 1 - r : ℕ) : ℝ) := by exact_mod_cast h1
      have h2 : ((N + q - 1 - r : ℕ) : ℝ) = (N:ℝ) + (q:ℝ) - 1 - (r:ℝ) := by
        have hle1 : 1 + r ≤ N + q := by omega
        rw [show N + q - 1 - r = (N + q) - (1 + r) by omega, Nat.cast_sub hle1]
        push_cast; ring
      rw [Nat.cast_mul, h2] at hcast
      linarith
    have hY : (q:ℝ) * (Pr:ℝ) + (r:ℝ) ≤ 3 * (N:ℝ) := by
      nlinarith [hPr2', hqN', hN1]
    have hYabs : |(q:ℝ) * (Pr:ℝ) + (r:ℝ) - (N:ℝ)| ≤ (q:ℝ) := by
      have hR : (N:ℝ) - (q:ℝ) ≤ (q:ℝ) * (Pr:ℝ) + (r:ℝ) := by linarith [hPr3, hr0]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hβ4 : |b| * (q:ℝ) * ((q:ℝ) * (Pr:ℝ) + (r:ℝ)) ≤ 4 := by
      have h1 : |b| * (q:ℝ) * ((q:ℝ) * (Pr:ℝ) + (r:ℝ)) ≤ (N:ℝ)^(-(1:ℝ)) * (3 * (N:ℝ)) :=
        mul_le_mul hbq hY (by positivity) (by positivity)
      have h2 : (N:ℝ)^(-(1:ℝ)) * (3 * (N:ℝ)) = 3 := by
        rw [show (N:ℝ)^(-(1:ℝ)) * (3 * (N:ℝ)) = 3 * ((N:ℝ)^(-(1:ℝ)) * (N:ℝ)^(1:ℝ)) from by
              rw [Real.rpow_one]; ring,
            ← Real.rpow_add hNpos, show (-(1:ℝ) + 1) = 0 by ring, Real.rpow_zero]
        ring
      linarith [h1, h2]
    -- the block bound
    have hC1 : ‖(∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
        - ∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2)‖
        ≤ 20 + 2000 * |b| * Real.sqrt |b| * (q:ℝ) * ((q:ℝ) * (Pr:ℝ) + (r:ℝ))^2 := by
      rw [show (∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
            = ∑ p ∈ Finset.range Pr, expTwoPiI (b * (q * (p:ℝ) + r)^2) from by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [show (((p*q+r:ℕ):ℝ)) = q * (p:ℝ) + r by push_cast; ring]]
      exact block_bound b hq0 hr0 Pr hPr1 hβ4
    -- the endpoint discrepancy
    have hC2 : ‖(∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2)) - (q:ℂ)⁻¹ * Iv‖ ≤ 2 := by
      have hsub : (∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2))
          = (q:ℂ)⁻¹ * (∫ u in (r:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2)) := by
        rw [show (∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2))
              = ∫ s in (0:ℝ)..(Pr:ℝ), (fun u : ℝ => expTwoPiI (b * u^2)) ((q:ℝ) * s + (r:ℝ)) from by
            apply intervalIntegral.integral_congr
            intro s _
            rfl]
        rw [intervalIntegral.integral_comp_mul_add (fun u : ℝ => expTwoPiI (b * u^2)) (ne_of_gt hq0) (r:ℝ)]
        rw [show ((q:ℝ) * 0 + (r:ℝ)) = (r:ℝ) by ring]
        rw [Complex.real_smul]
        rw [show (((q:ℝ)⁻¹ : ℝ) : ℂ) = (q:ℂ)⁻¹ from by
          rw [Complex.ofReal_inv, Complex.ofReal_natCast]]
      have hsub2 : (q:ℂ)⁻¹ * (∫ u in (r:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2)) - (q:ℂ)⁻¹ * Iv
          = (q:ℂ)⁻¹ * ((∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
              - (∫ u in (0:ℝ)..(N:ℝ), expTwoPiI (b * u^2))
              - (∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2))) := by
        rw [hIv]
        rw [show (∫ u in (r:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
              = (∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
                - (∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2)) from
          (intervalIntegral.integral_interval_sub_left
            (hcont_f.intervalIntegrable _ _) (hcont_f.intervalIntegrable _ _)).symm]
        ring
      rw [hsub, hsub2, norm_mul]
      rw [show ‖((q:ℂ))⁻¹‖ = (q:ℝ)⁻¹ from by
        have heq : (q:ℂ)⁻¹ = (((q:ℝ)⁻¹ : ℝ) : ℂ) := by
          rw [Complex.ofReal_inv, Complex.ofReal_natCast]
        rw [heq, show ‖(((q:ℝ)⁻¹ : ℝ) : ℂ)‖ = |(q:ℝ)⁻¹| from RCLike.norm_ofReal _,
            abs_of_nonneg (by positivity)]]
      have hlen1 : ‖(∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
            - (∫ u in (0:ℝ)..(N:ℝ), expTwoPiI (b * u^2))‖
          ≤ |(q:ℝ) * (Pr:ℝ) + (r:ℝ) - (N:ℝ)| := by
        rw [intervalIntegral.integral_interval_sub_left
              (hcont_f.intervalIntegrable _ _) (hcont_f.intervalIntegrable _ _)]
        calc ‖∫ u in (N:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2)‖
            ≤ 1 * |(q:ℝ) * (Pr:ℝ) + (r:ℝ) - (N:ℝ)| :=
              intervalIntegral.norm_integral_le_of_norm_le_const
                (fun u hu => by rw [norm_expTwoPiI])
          _ = |(q:ℝ) * (Pr:ℝ) + (r:ℝ) - (N:ℝ)| := by ring
      have hlen2 : ‖(∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2))‖ ≤ (r:ℝ) := by
        calc ‖∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2)‖
            ≤ 1 * |(r:ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const
              (fun u hu => by rw [norm_expTwoPiI])
          _ = (r:ℝ) := by rw [sub_zero, abs_of_nonneg hr0, one_mul]
      have hmain2 : ‖(∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
            - (∫ u in (0:ℝ)..(N:ℝ), expTwoPiI (b * u^2))
            - (∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2))‖ ≤ 2 * (q:ℝ) := by
        have h := norm_sub_le
          ((∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2)) - (∫ u in (0:ℝ)..(N:ℝ), expTwoPiI (b * u^2)))
          (∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2))
        linarith [h, hlen1, hlen2, hYabs]
      calc (q:ℝ)⁻¹ * ‖(∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
              - (∫ u in (0:ℝ)..(N:ℝ), expTwoPiI (b * u^2))
              - (∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2))‖
          ≤ (q:ℝ)⁻¹ * (2 * (q:ℝ)) := mul_le_mul_of_nonneg_left hmain2 (by positivity)
        _ = 2 := by field_simp
    -- combine
    have hfac2 : (N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
        - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv)
        = (N:ℝ)⁻¹ * ((∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
            - (q:ℂ)⁻¹ * Iv) := by
      rw [hPrdef]; ring
    rw [hfac2, norm_mul]
    rw [show ‖(((N:ℝ)⁻¹ : ℝ) : ℂ)‖ = (N:ℝ)⁻¹ from by
      rw [show ‖(((N:ℝ)⁻¹ : ℝ) : ℂ)‖ = |(N:ℝ)⁻¹| from RCLike.norm_ofReal _,
          abs_of_nonneg (by positivity)]]
    have hmain3 : ‖(∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
        - (q:ℂ)⁻¹ * Iv‖ ≤ 22 + 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2 := by
      have hsplit : (∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2)) - (q:ℂ)⁻¹ * Iv
          = ((∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
              - ∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2))
            + ((∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2)) - (q:ℂ)⁻¹ * Iv) := by
        ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have hY2 : ((q:ℝ) * (Pr:ℝ) + (r:ℝ))^2 ≤ (3 * (N:ℝ))^2 := by
        have h1 : 0 ≤ (q:ℝ) * (Pr:ℝ) + (r:ℝ) := by positivity
        nlinarith [hY, h1]
      have hfin : 2000 * |b| * Real.sqrt |b| * (q:ℝ) * ((q:ℝ) * (Pr:ℝ) + (r:ℝ))^2
          ≤ 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2 := by
        have h0 : 0 ≤ |b| * Real.sqrt |b| * (q:ℝ) := by positivity
        nlinarith [hY2, h0]
      linarith [hC1, hC2, hfin]
    exact mul_le_mul_of_nonneg_left hmain3 (by positivity)
  -- rewrite the goal into the summed form
  have e1 : (N:ℝ)⁻¹ * S
      = ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
          ((N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))) := by
    rw [hfac, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    ring
  have e2 : (q:ℂ)⁻¹ * G * ((N:ℝ)⁻¹ * Iv)
      = ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
          ((q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv)) := by
    rw [hG, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    ring
  have hfac3 : (N:ℝ)⁻¹ * S - (q:ℂ)⁻¹ * G * ((N:ℝ)⁻¹ * Iv)
      = ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
          ((N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
            - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv)) := by
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    ring
  rw [hfac3]
  -- sum over residues
  have hsum : ‖∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
        ((N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
          - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv))‖
      ≤ 22 * (N:ℝ)^(-((3:ℝ)/4)) + 18000 * (N:ℝ)^(-((3:ℝ)/8)) := by
    calc ‖∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
          ((N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
            - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv))‖
        ≤ ∑ r ∈ Finset.range q, ‖expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
          ((N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
            - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv))‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ Finset.range q, (N:ℝ)⁻¹ * (22 + 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2) := by
          refine Finset.sum_le_sum (fun r hr => ?_)
          rw [norm_mul, norm_expTwoPiI, one_mul]
          exact hblock r hr
      _ = (q:ℝ) * ((N:ℝ)⁻¹ * (22 + 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 22 * (N:ℝ)^(-((3:ℝ)/4)) + 18000 * (N:ℝ)^(-((3:ℝ)/8)) := by
          have h1 : (q:ℝ) * (N:ℝ)⁻¹ ≤ (N:ℝ)^(-((3:ℝ)/4)) := by
            calc (q:ℝ) * (N:ℝ)⁻¹ ≤ (N:ℝ)^((1:ℝ)/4) * (N:ℝ)⁻¹ :=
                  mul_le_mul_of_nonneg_right hqN (by positivity)
              _ = (N:ℝ)^((1:ℝ)/4) * (N:ℝ)^(-(1:ℝ)) := by rw [← Real.rpow_neg_one]
              _ = (N:ℝ)^((1:ℝ)/4 + -(1:ℝ)) := (Real.rpow_add hNpos _ _).symm
              _ = (N:ℝ)^(-((3:ℝ)/4)) := by norm_num
          have h2 : |b| * Real.sqrt |b| * (q:ℝ)^2 * (N:ℝ) ≤ (N:ℝ)^(-((3:ℝ)/8)) := by
            have hq2 : (q:ℝ)^2 ≤ (N:ℝ)^((1:ℝ)/2) := by
              have h := mul_self_le_mul_self hq0.le hqN
              have h2' : ((N:ℝ)^((1:ℝ)/4)) * ((N:ℝ)^((1:ℝ)/4)) = (N:ℝ)^((1:ℝ)/2) := by
                rw [← Real.rpow_add hNpos, show ((1:ℝ)/4 + (1:ℝ)/4) = (1:ℝ)/2 by norm_num]
              calc (q:ℝ)^2 = (q:ℝ) * (q:ℝ) := by ring
                _ ≤ ((N:ℝ)^((1:ℝ)/4)) * ((N:ℝ)^((1:ℝ)/4)) := h
                _ = (N:ℝ)^((1:ℝ)/2) := h2'
            have h3 : |b| * Real.sqrt |b| * (q:ℝ)^2 * (N:ℝ)
                ≤ (N:ℝ)^(-((15:ℝ)/8)) * ((N:ℝ)^((1:ℝ)/2) * (N:ℝ)^(1:ℝ)) := by
              have h0q : 0 ≤ (q:ℝ)^2 := sq_nonneg _
              have h0N : 0 ≤ (N:ℝ) := hNpos.le
              have hmul := mul_le_mul hbs hq2 h0q (by positivity : (0:ℝ) ≤ (N:ℝ)^(-((15:ℝ)/8)))
              have hmul2 : |b| * Real.sqrt |b| * (q:ℝ)^2 * (N:ℝ)
                  ≤ ((N:ℝ)^(-((15:ℝ)/8)) * (N:ℝ)^((1:ℝ)/2)) * (N:ℝ) :=
                mul_le_mul_of_nonneg_right hmul h0N
              have key : ((N:ℝ)^(-((15:ℝ)/8)) * (N:ℝ)^((1:ℝ)/2)) * (N:ℝ)
                  = (N:ℝ)^(-((15:ℝ)/8)) * ((N:ℝ)^((1:ℝ)/2) * (N:ℝ)^(1:ℝ)) := by
                rw [mul_assoc]
                congr 1
                congr 1
                exact (Real.rpow_one _).symm
              calc |b| * Real.sqrt |b| * (q:ℝ)^2 * (N:ℝ)
                  ≤ ((N:ℝ)^(-((15:ℝ)/8)) * (N:ℝ)^((1:ℝ)/2)) * (N:ℝ) := hmul2
                _ = (N:ℝ)^(-((15:ℝ)/8)) * ((N:ℝ)^((1:ℝ)/2) * (N:ℝ)^(1:ℝ)) := key
            have h4 : (N:ℝ)^(-((15:ℝ)/8)) * ((N:ℝ)^((1:ℝ)/2) * (N:ℝ)^(1:ℝ)) = (N:ℝ)^(-((3:ℝ)/8)) := by
              rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
              congr 1
              ring
            linarith [h3, h4]
          have e : (q:ℝ) * ((N:ℝ)⁻¹ * (22 + 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2))
              = 22 * ((q:ℝ) * (N:ℝ)⁻¹) + 18000 * (|b| * Real.sqrt |b| * (q:ℝ)^2 * (N:ℝ)) := by
            field_simp
          rw [e]
          linarith [h1, h2]
  -- final numeric bound
  refine le_trans hsum ?_
  rw [show 10^6 * ((N:ℝ)^((1:ℝ)/8))⁻¹ = 10^6 * (N:ℝ)^(-((1:ℝ)/8)) from by
    rw [(Real.rpow_neg hNpos.le ((1:ℝ)/8)).symm]]
  have hA : (N:ℝ)^(-((3:ℝ)/4)) = (N:ℝ)^(-((5:ℝ)/8)) * (N:ℝ)^(-((1:ℝ)/8)) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hB : (N:ℝ)^(-((3:ℝ)/8)) = (N:ℝ)^(-((1:ℝ)/4)) * (N:ℝ)^(-((1:ℝ)/8)) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hP : (N:ℝ)^(-((1:ℝ)/8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hQ : (N:ℝ)^(-((1:ℝ)/4)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hR : (N:ℝ)^(-((5:ℝ)/8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hP0 : 0 < (N:ℝ)^(-((1:ℝ)/8)) := Real.rpow_pos_of_pos hNpos _
  rw [hA, hB]
  nlinarith [hP, hQ, hR, hP0]

end Commons.Analysis.ExponentialSums
