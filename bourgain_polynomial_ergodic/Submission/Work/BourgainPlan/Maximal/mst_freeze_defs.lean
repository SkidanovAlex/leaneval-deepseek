import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs
import Submission.Work.BourgainPlan.Maximal.mstHat_bound
import Submission.Work.BourgainPlan.Maximal.mst_major_err1_l2

/-!
# The vocabulary of the per-arc "freezing" coefficient estimate (MST §4.4, eq. (99))

This module fixes the objects of the single-arc error estimate `mst_lvl_freeze_coeff`.

For an arc `β ∈ 𝒰(s+1)`, the level scale `c = c_s = 2^{s(d−χ)}` (`d = P.natDegree`) and the level
scale `J = ⌊exp √(s+1)⌋` of the density kernel, MST's error term at one arc and one dyadic scale
`2^k` is

  `f_β(ξ) = (star (G β) − star (m_J ξ)) · star (Φ_{2^k}(ξ − β)) · η_s(ξ − β)`,

the function `mstFreezeFn` below.  Its `ℓ¹` Fourier coefficient norm is `≲ exp(−√(s+1)/2)`
(`mst_lvl_freeze_coeff`).

The proof of that estimate freezes the arc: writing `r = iwRep β` for the canonical representative,
one works with the *lifted* symbols on `ℝ`,

* `mstTht P J β r u = star (G β) − star (polyWeylKernel P J (r + u))` — the one-arc error symbol
  read at the fundamental offset `u` (the lift of `star (mstG P β) − star (mstWeyl P J ξ)` around
  `ξ = β`, legitimate because `polyWeylKernel P J` is `1`-periodic, `polyWeylKernel_add_int`);
* `mstFreezeXi P J β c η w = mstTht P J β (iwRep β) (w/c) · η w` — the dilated symbol against the
  fixed bump `η`, whose transform `mstHat (mstFreezeXi …)` is what the shifted-lattice sampling
  bound is applied to.

The two "size" constants of the lifted symbol are the sup bounds

* `‖(mstTht …)'(u)‖ ≤ mstThtL P J = 2π · (Σᵢ |cᵢ|) · J^d`,
* `‖(mstTht …)''(u)‖ ≤ (mstThtL P J)²`,

proved in the companion module `mst_freeze_deriv`; they are what makes the quadratic decay
constant of `mstHat (mstFreezeXi …)` small, since `mstThtL P J / c_s → 0` subexponentially.
-/

open MeasureTheory Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- **The one-arc error symbol, lifted to `ℝ`.**  For the canonical representative `r` of the arc
`β` (`r = iwRep β`), `star (mstG P β) − star (polyWeylKernel P J (r + u))` is the value of
`star (mstG P β) − star (mstWeyl P J ξ)` at `ξ = β + (u : 𝕋)`: the lift is legitimate because
`polyWeylKernel P J` is `1`-periodic (`polyWeylKernel_add_int`). -/
def mstTht (P : Polynomial ℤ) (J : ℕ) (β : Circ) (r u : ℝ) : ℂ :=
  star (mstG P β) - star (polyWeylKernel P J (r + u))

@[simp] theorem mstTht_apply (P : Polynomial ℤ) (J : ℕ) (β : Circ) (r u : ℝ) :
    mstTht P J β r u = star (mstG P β) - star (polyWeylKernel P J (r + u)) := rfl

/-- **The frozen symbol `Ξ`**: the lifted arc-error symbol at the dilated offset `w/c`, against the
fixed bump `η`, `w ↦ mstTht P J β (iwRep β) (w/c) · η w`.  This is the function whose transform
`mstHat Ξ` appears in the sampling bound. -/
def mstFreezeXi (P : Polynomial ℤ) (J : ℕ) (β : Circ) (c : ℝ) (η : ℝ → ℂ) : ℝ → ℂ :=
  fun w => mstTht P J β (iwRep β) (w / c) * η w

@[simp] theorem mstFreezeXi_apply (P : Polynomial ℤ) (J : ℕ) (β : Circ) (c : ℝ) (η : ℝ → ℂ)
    (w : ℝ) : mstFreezeXi P J β c η w = mstTht P J β (iwRep β) (w / c) * η w := rfl

/-- **The single-arc error term** of MST §4.4 (eq. (99)) at the dyadic scale `2^k`:
`ξ ↦ (star (G β) − star (m_J ξ)) · star (Φ_{2^k}(ξ − β)) · η_s(ξ − β)`. -/
def mstFreezeFn (P : Polynomial ℤ) (J d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s k : ℕ) (β : Circ) :
    Circ → ℂ :=
  fun ξ => (star (mstG P β) - star (mstWeyl P J ξ)) *
    (star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β))

@[simp] theorem mstFreezeFn_apply (P : Polynomial ℤ) (J d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s k : ℕ)
    (β ξ : Circ) :
    mstFreezeFn P J d χ η s k β ξ
      = (star (mstG P β) - star (mstWeyl P J ξ)) *
        (star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β)) := rfl

/-- The size `Σᵢ |cᵢ|` of the coefficients of `P`: `|P(n)| ≤ (mstCoeffB P) · J^d` for `n < J`,
`J ≥ 1`. -/
def mstCoeffB (P : Polynomial ℤ) : ℝ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), |((P.coeff i : ℤ) : ℝ)|

/-- **The sup bound `L` for the first derivative of the lifted error symbol**:
`mstThtL P J = 2π · (Σᵢ |cᵢ|) · J^d`. -/
def mstThtL (P : Polynomial ℤ) (J : ℕ) : ℝ :=
  2 * Real.pi * mstCoeffB P * (J : ℝ) ^ P.natDegree

theorem mstCoeffB_nonneg (P : Polynomial ℤ) : 0 ≤ mstCoeffB P := by
  unfold mstCoeffB; positivity

theorem mstThtL_nonneg (P : Polynomial ℤ) (J : ℕ) : 0 ≤ mstThtL P J := by
  unfold mstThtL; have := mstCoeffB_nonneg P; positivity

/-- `star (exp (w · I)) = exp (−w · I)` for real `w`. -/
theorem star_exp_ofReal_mul_I (w : ℝ) :
    star (Complex.exp (((w : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((-w : ℝ) : ℂ) * Complex.I) := by
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- **The conjugate Weyl kernel as a finite sum of exponentials.**  Since `P` takes integer values,
`star (polyWeylKernel P J x) = J⁻¹ Σ_{n<J} e^{−2πi x P(n)}`.  This is the form in which the
`C²`-regularity and the derivative bounds of the lifted symbol are proved. -/
theorem star_polyWeylKernel_expand (P : Polynomial ℤ) (J : ℕ) (x : ℝ) :
    star (polyWeylKernel P J x) = (((J : ℝ)⁻¹ : ℂ) *
      ∑ n ∈ Finset.range J, Complex.exp
        (((-(2 * Real.pi * (x * ((P.eval (n : ℤ) : ℤ) : ℝ))) : ℝ) : ℂ) * Complex.I)) := by
  rw [polyWeylKernel, star_mul]
  have h : star (((J:ℝ)⁻¹ : ℂ)) = ((J:ℝ)⁻¹ : ℂ) := by simp
  rw [h, mul_comm]
  congr 1
  rw [show star (∑ n ∈ Finset.range J, Complex.exp (2 * (Real.pi:ℂ) * Complex.I *
        (((x * ((P.eval (n : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ)))
      = starRingEnd ℂ (∑ n ∈ Finset.range J, Complex.exp (2 * (Real.pi:ℂ) * Complex.I *
        (((x * ((P.eval (n : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ))) from rfl]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        (((x * ((P.eval (n : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ)
      = (((2 * Real.pi * (x * ((P.eval (n : ℤ) : ℤ) : ℝ))) : ℝ) : ℂ) * Complex.I from by
    push_cast; ring]
  exact star_exp_ofReal_mul_I _

/-- The level bump read through the level scale: `mstEta d χ η n ζ = η (c_n · iwRep ζ)` with
`c_n = mstScale d χ n`. -/
theorem mstEta_eq_mstScale (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ) (ζ : Circ) :
    mstEta d χ η n ζ = η (mstScale d χ n * iwRep ζ) := by
  rw [mstEta_apply, mstScale_apply]

/-- The Weyl kernel only depends on the class of its argument, so reading it through the canonical
lift of a real point is the same as evaluating it at the point. -/
theorem polyWeylKernel_iwRep_coe (P : Polynomial ℤ) (J : ℕ) (x : ℝ) :
    polyWeylKernel P J (iwRep ((x : ℝ) : Circ)) = polyWeylKernel P J x :=
  polyWeylKernel_of_coe_eq P J (by rw [coe_iwRep])

/-- The canonical lift of a translate: `iwRep (β + u) = iwRep β + u + k` for some integer `k`. -/
theorem iwRep_add_coe_sub_int (β : Circ) (u : ℝ) :
    ∃ k : ℤ, iwRep (β + ((u : ℝ) : Circ)) = iwRep β + u + k := by
  have hzero : (((iwRep (β + ((u : ℝ) : Circ)) - iwRep β - u) : ℝ) : Circ) = 0 := by
    simp only [AddCircle.coe_sub, AddCircle.coe_add, coe_iwRep]
    abel
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  rw [Int.smul_one_eq_cast] at hk
  refine ⟨k, ?_⟩
  linarith

/-- **The lifted symbol is the circle symbol**: at `ξ = β + (u : 𝕋)` the value
`star (mstG P β) − star (mstWeyl P J ξ)` is `mstTht P J β (iwRep β) u` (periodicity of the Weyl
kernel). -/
theorem mstTht_eq_mstWeyl (P : Polynomial ℤ) (J : ℕ) (β : Circ) (u : ℝ) :
    mstTht P J β (iwRep β) u = star (mstG P β)
      - star (mstWeyl P J (β + ((u : ℝ) : Circ))) := by
  obtain ⟨k, hk⟩ := iwRep_add_coe_sub_int β u
  rw [mstTht_apply, mstWeyl_apply, hk, polyWeylKernel_add_int P J (iwRep β + u) k]

/-- The frozen symbol at the point `w` is the lifted symbol at the dilated offset `w/c` times the
bump `η`. -/
theorem mstFreezeXi_apply' (P : Polynomial ℤ) (J : ℕ) (β : Circ) (c : ℝ) (η : ℝ → ℂ) (w : ℝ) :
    mstFreezeXi P J β c η w = mstTht P J β (iwRep β) (w / c) * η w := rfl


/-- **Truncation to the support.**  If `h` vanishes off the closed interval `Icc (-r) r` and
`0 ≤ r ≤ R`, then the interval integral of `h` over `(-R, R)` equals its interval integral over
`(-r, r)`.  (The same statement as the private helper inside `fourierCoeff_mstEta`, exported here
because the dilation dictionary of the freezing estimate needs it.) -/
theorem intervalIntegral_eq_of_support {h : ℝ → ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R)
    (hsupp : ∀ x : ℝ, r < |x| → h x = 0) :
    ∫ x in -R..R, h x = ∫ x in -r..r, h x := by
  have hIcc : (Set.Icc (-R) R).indicator h = (Set.Icc (-r) r).indicator h := by
    funext x
    by_cases hx : x ∈ Set.Icc (-r) r
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem (Set.Icc_subset_Icc (by linarith) (by linarith) hx)]
    · by_cases hx2 : x ∈ Set.Icc (-R) R
      · have hx' : r < |x| := by
          rw [Set.mem_Icc] at hx2
          have hc : x < -r ∨ r < x := by
            by_contra hcon
            push Not at hcon
            exact hx ⟨hcon.1, hcon.2⟩
          rcases hc with hc | hc
          · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
          · exact lt_of_lt_of_le hc (le_abs_self x)
        rw [Set.indicator_of_notMem hx, Set.indicator_of_mem hx2, hsupp x hx']
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx2]
  calc ∫ x in -R..R, h x
      = ∫ x in Set.Ioc (-R) R, h x := intervalIntegral.integral_of_le (by linarith)
    _ = ∫ x in Set.Icc (-R) R, h x := (integral_Icc_eq_integral_Ioc).symm
    _ = ∫ x, (Set.Icc (-R) R).indicator h x := (integral_indicator measurableSet_Icc).symm
    _ = ∫ x, (Set.Icc (-r) r).indicator h x := by rw [hIcc]
    _ = ∫ x in Set.Icc (-r) r, h x := integral_indicator measurableSet_Icc
    _ = ∫ x in Set.Ioc (-r) r, h x := integral_Icc_eq_integral_Ioc
    _ = ∫ x in -r..r, h x := (intervalIntegral.integral_of_le (by linarith)).symm


/-- The character `u ↦ e^{−2πi u t}` in the precise shape (`Complex.exp (((-2π(u·t) : ℝ) : ℂ) * I)`)
in which it occurs in `mstHat`, `mst_freeze_lift_pointwise`, `mst_freeze_fubini` and
`mstHat_dilate_eq`. -/
def mstFreezeChar (u t : ℝ) : ℂ :=
  Complex.exp ((((-(2 * Real.pi * (u * t))) : ℝ) : ℂ) * Complex.I)

@[simp] theorem mstFreezeChar_apply (u t : ℝ) :
    mstFreezeChar u t = Complex.exp ((((-(2 * Real.pi * (u * t))) : ℝ) : ℂ) * Complex.I) := rfl

theorem mstFreezeChar_zero (u : ℝ) : mstFreezeChar u 0 = 1 := by
  simp [mstFreezeChar]

/-- `e^{−2πi u (s+t)} = e^{−2πi u s} · e^{−2πi u t}`. -/
theorem mstFreezeChar_add (u s t : ℝ) :
    mstFreezeChar u (s + t) = mstFreezeChar u s * mstFreezeChar u t := by
  rw [mstFreezeChar, mstFreezeChar, mstFreezeChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `e^{−2πi u t} = e^{−2πi t u}` (the order of the factors in the phase is irrelevant). -/
theorem mstFreezeChar_comm (u t : ℝ) : mstFreezeChar u t = mstFreezeChar t u := by
  rw [mstFreezeChar, mstFreezeChar]
  congr 2
  ring

/-- `fourier (−m)` at a real representative is the character `e^{−2πi m x}`. -/
theorem fourier_neg_coe_eq (m : ℤ) (x : ℝ) :
    fourier (-m) ((x : ℝ) : Circ) = mstFreezeChar x (m : ℝ) := by
  rw [fourier_coe_apply, mstFreezeChar]
  congr 1
  push_cast
  ring


end

end Work.BourgainPlan.Maximal
