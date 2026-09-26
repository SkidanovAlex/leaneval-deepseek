/-
# The local contour shift away from the translate pole

The CKMRV contour integral `∫_0^∞ K(τ,it) e^{-πr²t} dt` is an integral along the *imaginary
axis*.  Its integrand has, for `τ` in the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` near the boundary line
`Re τ = 1`, a pole of `z ↦ K(τ,z)` at `z = τ - 1` (CKMRV Theorem 4.9(3)) whose real part
`Re τ - 1 ∈ (-1,0)` sits just *left* of the contour; the modulus of the integrand therefore has
a spike of height `≍ 1/|1 - Re τ|` at the height `t = Im τ - 1`, and no bound of the form
`‖K(τ,it)‖ ≤ poly(scale τ)` can hold there.

The remedy formalised here is the *local* contour shift: since the pole lies on the far side of
the contour (on the left when `Re τ > 0`, on the right when `Re τ < 0`), the segment
`{z = it : t ∈ [Im τ - 1, Im τ + 1]}` of the contour can be moved in the *real* direction, by a
distance small enough to keep every pole strictly outside the swept rectangle and large enough
to put the contour at a fixed positive distance from the pole.  Two features make this the
right move:

* no pole is crossed, so there is **no residue term** — the identity is the plain
  Cauchy–Goursat identity for a rectangle;
* the shift is in the real direction, so `|e^{πir²z}|` is **unchanged**, and the Gaussian
  damping `e^{-πr²t}` is preserved exactly.

`Work.Asymptotics.HalfFunnel.integral_vertical_segment_shift` is the identity, in the form in
which it is applied below: the shift of a vertical segment, the two horizontal edges of the
swept rectangle being the correction terms.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KMinusSlash
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.Rigidity.ReduceElement.exists_reduce_element

namespace Work.Asymptotics.HalfFunnel

open MeasureTheory intervalIntegral Complex Filter

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

/-- **The rectangle identity for a vertical segment, shifted in the real direction.**

If `F` is complex-differentiable on the closed rectangle with corners `a·i`, `b·i`,
`h + b·i`, `h + a·i` (so that, in particular, no pole of `F` lies in it), then

`i ∫_a^b F(it) dt = i ∫_a^b F(h + it) dt + ∫_0^h F(x + ai) dx - ∫_0^h F(x + bi) dx`.

This is Cauchy–Goursat for the boundary of the rectangle, split into its four sides: the two
vertical sides (the shift) and the two horizontal sides (the correction). -/
theorem integral_vertical_segment_shift {F : ℂ → ℂ} {a b h : ℝ}
    (hF : DifferentiableOn ℂ F (Set.uIcc (0 : ℝ) h ×ℂ Set.uIcc a b)) :
    (∫ y in a..b, F ((y : ℂ) * Complex.I) * Complex.I)
      = (∫ y in a..b, F ((h : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
        + (∫ x in 0..h, F ((x : ℂ) + (a : ℂ) * Complex.I))
        - (∫ x in 0..h, F ((x : ℂ) + (b : ℂ) * Complex.I)) := by
  have hzre : (((a : ℂ) * Complex.I)).re = 0 := by simp
  have hzim : (((a : ℂ) * Complex.I)).im = a := by simp
  have hwre : (((h : ℂ) + (b : ℂ) * Complex.I)).re = h := by simp
  have hwim : (((h : ℂ) + (b : ℂ) * Complex.I)).im = b := by simp
  have hmain := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((a : ℂ) * Complex.I) ((h : ℂ) + (b : ℂ) * Complex.I) (by
      rw [hzre, hzim, hwre, hwim]; exact hF)
  rw [hzre, hzim, hwre, hwim] at hmain
  -- turn the leftover `↑(0:ℝ) + ↑y * I` into `↑y * I`
  have hzero : (∫ y : ℝ in a..b, F (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y : ℝ in a..b, F ((y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    norm_num
  rw [hzero] at hmain
  -- convert `I • c` into `c * I`
  have e1 : ∀ c : ℂ, Complex.I • c = c * Complex.I := fun c => by
    rw [smul_eq_mul, mul_comm]
  rw [e1, e1] at hmain
  -- split the interval integrals into a constant times `I`
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  -- hmain : (A1 - A2) + B1 - B2 = 0 ; goal : B2 = (B1 + A1) - A2
  have h := sub_eq_zero.mp hmain
  rw [← h]
  ring


/-- **The same identity, divided by `I`** — the form in which it is applied.  With
`F` complex-differentiable on the swept rectangle,

`∫_a^b F(it) dt = ∫_a^b F(h + it) dt - i ∫_0^h F(x + ai) dx + i ∫_0^h F(x + bi) dx`. -/
theorem integral_vertical_segment_shift' {F : ℂ → ℂ} {a b h : ℝ}
    (hF : DifferentiableOn ℂ F (Set.uIcc (0 : ℝ) h ×ℂ Set.uIcc a b)) :
    (∫ y in a..b, F ((y : ℂ) * Complex.I))
      = (∫ y in a..b, F ((h : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I * (∫ x in 0..h, F ((x : ℂ) + (a : ℂ) * Complex.I))
        + Complex.I * (∫ x in 0..h, F ((x : ℂ) + (b : ℂ) * Complex.I)) := by
  have hmain0 := integral_vertical_segment_shift (F := F) hF
  have hXeq : (∫ y in a..b, F ((y : ℂ) * Complex.I) * Complex.I)
      = (∫ y in a..b, F ((y : ℂ) * Complex.I)) * Complex.I :=
    intervalIntegral.integral_mul_const _ _
  have hYeq : (∫ y in a..b, F ((h : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
      = (∫ y in a..b, F ((h : ℂ) + (y : ℂ) * Complex.I)) * Complex.I :=
    intervalIntegral.integral_mul_const _ _
  rw [hXeq, hYeq] at hmain0
  -- hmain0 : X * I = (Y * I + A) - B, with X, Y, A, B the four integrals
  have hkey : (∫ y in a..b, F ((y : ℂ) * Complex.I)) * Complex.I
      = ((∫ y in a..b, F ((h : ℂ) + (y : ℂ) * Complex.I)) * Complex.I
          + (∫ x in 0..h, F ((x : ℂ) + (a : ℂ) * Complex.I)))
        - (∫ x in 0..h, F ((x : ℂ) + (b : ℂ) * Complex.I)) := hmain0
  have hI : Complex.I⁻¹ * Complex.I = (1 : ℂ) := inv_mul_cancel₀ Complex.I_ne_zero
  have h1 : Complex.I⁻¹ * ((∫ y in a..b, F ((y : ℂ) * Complex.I)) * Complex.I)
      = ∫ y in a..b, F ((y : ℂ) * Complex.I) := by
    have hcomm : Complex.I⁻¹ * ((∫ y in a..b, F ((y : ℂ) * Complex.I)) * Complex.I)
        = (∫ y in a..b, F ((y : ℂ) * Complex.I)) * (Complex.I⁻¹ * Complex.I) := by ring
    rw [hcomm, hI, mul_one]
  have h2 : Complex.I⁻¹ * ((∫ y in a..b, F ((h : ℂ) + (y : ℂ) * Complex.I)) * Complex.I)
      = ∫ y in a..b, F ((h : ℂ) + (y : ℂ) * Complex.I) := by
    have hcomm : Complex.I⁻¹ * ((∫ y in a..b, F ((h : ℂ) + (y : ℂ) * Complex.I)) * Complex.I)
        = (∫ y in a..b, F ((h : ℂ) + (y : ℂ) * Complex.I)) * (Complex.I⁻¹ * Complex.I) := by ring
    rw [hcomm, hI, mul_one]
  have hval := congrArg (fun w : ℂ => Complex.I⁻¹ * w) hkey
  rw [mul_sub, mul_add, h1, h2] at hval
  have hIinv : Complex.I⁻¹ = -Complex.I := by
    rw [← Complex.inv_I]
  rw [hIinv] at hval
  rw [hval]
  ring

theorem spike_shift_kernel {k : ℂ → ℂ} {a b h r : ℝ}
    (hk : DifferentiableOn ℂ k (Set.uIcc (0 : ℝ) h ×ℂ Set.uIcc a b)) :
    (∫ y in a..b, k ((y : ℂ) * Complex.I) * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (y : ℂ))))
      = (∫ y in a..b, k ((h : ℂ) + (y : ℂ) * Complex.I)
            * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * ((h : ℂ) + (y : ℂ) * Complex.I)))
        - Complex.I * (∫ x in 0..h, k ((x : ℂ) + (a : ℂ) * Complex.I)
            * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * ((x : ℂ) + (a : ℂ) * Complex.I)))
        + Complex.I * (∫ x in 0..h, k ((x : ℂ) + (b : ℂ) * Complex.I)
            * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * ((x : ℂ) + (b : ℂ) * Complex.I))) := by
  set c : ℂ := Real.pi * Complex.I * (r : ℂ) ^ 2 with hc
  have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (c * z)) :=
    Complex.differentiable_exp.comp ((differentiable_const c).mul differentiable_id)
  have hFdiff : DifferentiableOn ℂ (fun z : ℂ => k z * Complex.exp (c * z))
      (Set.uIcc (0 : ℝ) h ×ℂ Set.uIcc a b) :=
    hk.mul hexp.differentiableOn
  have hmain' := integral_vertical_segment_shift' (F := fun z : ℂ => k z * Complex.exp (c * z))
    hFdiff
  -- identify the integrands
  have e_left : ∀ y : ℝ, k ((y : ℂ) * Complex.I) * Complex.exp (c * ((y : ℂ) * Complex.I))
      = k ((y : ℂ) * Complex.I) * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (y : ℂ))) := by
    intro y
    have harg : c * ((y : ℂ) * Complex.I) = -(Real.pi * (r : ℂ) ^ 2 * (y : ℂ)) := by
      have hI2 : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
      rw [hc]
      calc Real.pi * Complex.I * (r : ℂ) ^ 2 * ((y : ℂ) * Complex.I)
          = Real.pi * (r : ℂ) ^ 2 * (y : ℂ) * (Complex.I * Complex.I) := by ring
        _ = Real.pi * (r : ℂ) ^ 2 * (y : ℂ) * (-1) := by rw [hI2]
        _ = -(Real.pi * (r : ℂ) ^ 2 * (y : ℂ)) := by ring
    rw [harg]
  have e_shift : ∀ y : ℝ, k ((h : ℂ) + (y : ℂ) * Complex.I)
        * Complex.exp (c * ((h : ℂ) + (y : ℂ) * Complex.I))
      = k ((h : ℂ) + (y : ℂ) * Complex.I)
        * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * ((h : ℂ) + (y : ℂ) * Complex.I)) := by
    intro y
    have harg : c * ((h : ℂ) + (y : ℂ) * Complex.I)
        = Real.pi * Complex.I * (r : ℂ) ^ 2 * ((h : ℂ) + (y : ℂ) * Complex.I) := by
      rw [hc]
    rw [harg]
  have e_a : ∀ x : ℝ, k ((x : ℂ) + (a : ℂ) * Complex.I)
        * Complex.exp (c * ((x : ℂ) + (a : ℂ) * Complex.I))
      = k ((x : ℂ) + (a : ℂ) * Complex.I)
        * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * ((x : ℂ) + (a : ℂ) * Complex.I)) := by
    intro x
    have harg : c * ((x : ℂ) + (a : ℂ) * Complex.I)
        = Real.pi * Complex.I * (r : ℂ) ^ 2 * ((x : ℂ) + (a : ℂ) * Complex.I) := by
      rw [hc]
    rw [harg]
  have e_b : ∀ x : ℝ, k ((x : ℂ) + (b : ℂ) * Complex.I)
        * Complex.exp (c * ((x : ℂ) + (b : ℂ) * Complex.I))
      = k ((x : ℂ) + (b : ℂ) * Complex.I)
        * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * ((x : ℂ) + (b : ℂ) * Complex.I)) := by
    intro x
    have harg : c * ((x : ℂ) + (b : ℂ) * Complex.I)
        = Real.pi * Complex.I * (r : ℂ) ^ 2 * ((x : ℂ) + (b : ℂ) * Complex.I) := by
      rw [hc]
    rw [harg]
  rw [intervalIntegral.integral_congr (fun y _ => e_left y),
      intervalIntegral.integral_congr (fun y _ => e_shift y),
      intervalIntegral.integral_congr (fun x _ => e_a x),
      intervalIntegral.integral_congr (fun x _ => e_b x)] at hmain'
  exact hmain'


/-! ## The swept rectangle is orbit-free

The spike shift of `spike_shift_kernel` is applied with the rectangle
`[0, 1/4] × [Im τ - 1, Im τ + 1]`.  For this to be legitimate the kernel must be holomorphic
there, and the only obstruction is the coincidence set `j z = j τ`, i.e. the `SL(2,ℤ)`-orbit of
`τ`.  The next lemma is the quantitative form of the orbit avoidance: *no* translate of `τ` has
its real part in `[0,1/4]` while its imaginary part lies in `[Im τ - 1, Im τ + 1]`.

The proof is the classical height argument.  If `γ • τ` has imaginary part `≥ Im τ - 1`, then
its denominator `c τ + d` must be small: either `c = 0`, in which case `γ` is a translate
`±Tᵏ` and `Re (γ • τ) = Re τ + (integer) ∉ [0,1/4]` because `1/4 < Re τ < 1`; or `c ≠ 0`, in
which case `‖c τ + d‖² ≥ (c Im τ)² ≥ (Im τ)²` forces
`Im (γ • τ) = Im τ / ‖c τ + d‖² ≤ 1/Im τ ≤ 1/2 < Im τ - 1`. -/
theorem orbit_free_funnelStrip {τ : UpperHalfPlane} (hτ : τ ∈ Work.Asymptotics.DomainD)
    (h2 : 2 ≤ τ.im) (hre : (1 / 4 : ℝ) < τ.re) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ¬ ((γ • τ).re ∈ Set.Icc (0 : ℝ) (1 / 4) ∧ (γ • τ).im ∈ Set.Icc (τ.im - 1) (τ.im + 1)) := by
  rintro ⟨hre', him'⟩
  have hτre : τ.re < 1 := (Work.Asymptotics.mem_DomainD.mp hτ).2.1
  have hpos : 0 < τ.im := τ.im_pos
  by_cases hc : γ 1 0 = 0
  · -- upper triangular: `γ` is a translate
    have hdet : (γ 0 0 : ℤ) * (γ 1 1 : ℤ) = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe γ
      rw [Matrix.det_fin_two] at h
      rw [hc] at h
      linarith [h]
    have hu : γ 0 0 = 1 ∨ γ 0 0 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hdet
    have ha2 : (γ 0 0 : ℤ) * (γ 0 0 : ℤ) = 1 := by
      rcases hu with h | h <;> rw [h] <;> norm_num
    have had : (γ 0 0 : ℤ) = (γ 1 1 : ℤ) := by
      rcases hu with h | h
      · rw [h] at hdet; omega
      · rw [h] at hdet; omega
    have haC : ((γ 0 0 : ℤ) : ℂ) * ((γ 0 0 : ℤ) : ℂ) = 1 := by
      rw [← Int.cast_mul, ha2]; norm_num
    have hane : ((γ 0 0 : ℤ) : ℂ) ≠ 0 := by
      intro h0; rw [h0] at haC; norm_num at haC
    have hbC : ((γ 0 1 : ℤ) : ℂ) * ((γ 0 0 : ℤ) : ℂ)
        = (((γ 0 0 : ℤ) * (γ 0 1 : ℤ) : ℤ) : ℂ) := by
      push_cast; ring
    have hval : ((γ • τ : UpperHalfPlane) : ℂ)
        = (τ : ℂ) + (((γ 0 0 : ℤ) * (γ 0 1 : ℤ) : ℤ) : ℂ) := by
      have hmain := Work.Rigidity.ReduceElement.coe_smul_eq γ τ
      rw [hc] at hmain
      simp only [Int.cast_zero, zero_mul, zero_add] at hmain
      rw [hmain]
      have hadC : ((γ 1 1 : ℤ) : ℂ) = ((γ 0 0 : ℤ) : ℂ) := by rw [← had]
      rw [hadC, div_eq_iff hane]
      rw [add_mul, ← hbC]
      rw [show ((γ 0 1 : ℤ) : ℂ) * ((γ 0 0 : ℤ) : ℂ) * ((γ 0 0 : ℤ) : ℂ)
            = ((γ 0 1 : ℤ) : ℂ) * (((γ 0 0 : ℤ) : ℂ) * ((γ 0 0 : ℤ) : ℂ)) from by ring,
        haC, mul_one]
      ring
    have hreval : (γ • τ).re = τ.re + (((γ 0 0 : ℤ) * (γ 0 1 : ℤ) : ℤ) : ℝ) := by
      have := congrArg Complex.re hval
      simpa using this
    by_cases hle : (0 : ℝ) ≤ (((γ 0 0 : ℤ) * (γ 0 1 : ℤ) : ℤ) : ℝ)
    · have hge : τ.re ≤ (γ • τ).re := by rw [hreval]; linarith
      have := hre'.2
      linarith
    · have hneg : (((γ 0 0 : ℤ) * (γ 0 1 : ℤ) : ℤ) : ℝ) < 0 := not_le.mp hle
      have hle' : (γ • τ).re ≤ τ.re - 1 := by
        rw [hreval]
        have hint : ((γ 0 0 : ℤ) * (γ 0 1 : ℤ) : ℤ) ≤ -1 := by
          have h2 : ((γ 0 0 : ℤ) * (γ 0 1 : ℤ) : ℤ) < 0 := by exact_mod_cast hneg
          omega
        have : (((γ 0 0 : ℤ) * (γ 0 1 : ℤ) : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hint
        linarith
      have := hre'.1
      linarith
  · -- `c ≠ 0`: the denominator is large
    have hbig : τ.im ≤ ‖Work.Kernels.jFun γ (τ : ℂ)‖ := by
      have him : (Work.Kernels.jFun γ (τ : ℂ)).im = ((γ 1 0 : ℤ) : ℝ) * τ.im := by
        rw [Work.Kernels.jFun_apply]
        simp [Complex.add_im, Complex.mul_im]
      have h1 : |(Work.Kernels.jFun γ (τ : ℂ)).im| ≤ ‖Work.Kernels.jFun γ (τ : ℂ)‖ :=
        Complex.abs_im_le_norm _
      have h2 : (1 : ℝ) ≤ |((γ 1 0 : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc
      have h3 : τ.im ≤ |((γ 1 0 : ℤ) : ℝ)| * τ.im := by
        calc τ.im = 1 * τ.im := (one_mul _).symm
          _ ≤ |((γ 1 0 : ℤ) : ℝ)| * τ.im := mul_le_mul_of_nonneg_right h2 hpos.le
      rw [him, abs_mul, abs_of_pos hpos] at h1
      linarith
    have hnormpos : 0 < ‖Work.Kernels.jFun γ (τ : ℂ)‖ :=
      norm_pos_iff.mpr (Work.Kernels.jFun_ne_zero γ τ)
    have himval : (γ • τ).im = τ.im / ‖Work.Kernels.jFun γ (τ : ℂ)‖ ^ 2 :=
      Work.Kernels.im_smul_eq γ τ
    have hle : (γ • τ).im ≤ 1 / 2 := by
      rw [himval]
      have hsquare : τ.im ^ 2 ≤ ‖Work.Kernels.jFun γ (τ : ℂ)‖ ^ 2 := by
        nlinarith [hbig, hnormpos, hpos]
      have hkey : τ.im / ‖Work.Kernels.jFun γ (τ : ℂ)‖ ^ 2 ≤ τ.im / τ.im ^ 2 :=
        div_le_div_of_nonneg_left hpos.le (by positivity) hsquare
      have hsecond : τ.im / τ.im ^ 2 = 1 / τ.im := by
        field_simp
      rw [hsecond] at hkey
      refine le_trans hkey ?_
      rw [div_le_div_iff₀ hpos (by norm_num : (0:ℝ) < 2)]
      linarith
    have := him'.1
    linarith


/-! ## The CKMRV kernel along the contour, as a function of the contour variable

`Kaxis (Kfun ℓ d) τ t = Kfun ℓ d τ (i t)` is the integrand of the CKMRV transform on the
imaginary axis.  For the local contour shift it is convenient to view it as the restriction to
`z = it` of a function on the whole plane, namely the extension by `0` of
`z ↦ K^{(d)}(τ, z)` (defined on `ℍ`). -/
noncomputable def kExt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  if 0 < z.im then Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z) else 0

lemma kExt_of_im_pos (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) {z : ℂ}
    (hz : 0 < z.im) : kExt ℓ d τ z = Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z) := by
  rw [kExt]; simp [hz]

/-- On the contour the extension is the CKMRV contour integrand. -/
lemma kExt_imagAxis (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) {t : ℝ}
    (ht : 0 < t) :
    kExt ℓ d τ ((t : ℂ) * Complex.I) = Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t := by
  have him : (((t : ℂ) * Complex.I)).im = t := by simp
  have hpos : 0 < (((t : ℂ) * Complex.I)).im := by rw [him]; exact ht
  have hfun : kExt ℓ d τ ((t : ℂ) * Complex.I)
      = Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I)) :=
    kExt_of_im_pos ℓ d τ hpos
  have hpt : UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) = Work.Kernels.imagAxis t ht := by
    apply UpperHalfPlane.ext
    show (((UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) : UpperHalfPlane)) : ℂ)
        = ((t : ℂ) * Complex.I)
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
  rw [hfun, hpt, Work.Kernels.Kaxis, dif_pos ht]

/-- **The extension `kExt ℓ d τ` is holomorphic on the swept rectangle.**

This discharges the analyticity hypothesis of `kernelTransform_spike_shift`.  On the rectangle
the imaginary part is `≥ Im τ - 1 ≥ 1 > 0`, so `ofComplex` is a right inverse, and by
`orbit_free_funnelStrip` no point of the rectangle is in the `SL(2,ℤ)`-orbit of `τ`; hence
`j z ≠ j τ` there and `Work.Residues.mdifferentiableAt_Kfun_snd` applies. -/
theorem kExt_differentiableOn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : UpperHalfPlane} (hτ : τ ∈ Work.Asymptotics.DomainD) (h2 : 2 ≤ τ.im)
    (hre : (1 / 4 : ℝ) < τ.re) :
    DifferentiableOn ℂ (kExt ℓ d τ)
      (Set.uIcc (0 : ℝ) (1 / 4) ×ℂ Set.uIcc (τ.im - 1) (τ.im + 1)) := by
  have hpos : ∀ z ∈ Set.uIcc (0 : ℝ) (1 / 4) ×ℂ Set.uIcc (τ.im - 1) (τ.im + 1), 0 < z.im := by
    intro z hz
    have h := hz.2
    rw [Set.mem_preimage, Set.uIcc_of_le (by linarith : τ.im - 1 ≤ τ.im + 1)] at h
    have h1 : (1 : ℝ) ≤ τ.im - 1 := by linarith
    linarith [h.1]
  have hcomp : DifferentiableOn ℂ
      (fun w : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w))
      (Set.uIcc (0 : ℝ) (1 / 4) ×ℂ Set.uIcc (τ.im - 1) (τ.im + 1)) := by
    intro z hz
    have hzimpos := hpos z hz
    have hcoe : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
      rw [show (UpperHalfPlane.ofComplex z : UpperHalfPlane) = ⟨z, hzimpos⟩ from
        UpperHalfPlane.ofComplex_apply_of_im_pos hzimpos]
    have hzre : z.re ∈ Set.Icc (0 : ℝ) (1 / 4) := by
      have h := hz.1
      rw [Set.mem_preimage, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4)] at h
      exact h
    have hzim : z.im ∈ Set.Icc (τ.im - 1) (τ.im + 1) := by
      have h := hz.2
      rw [Set.mem_preimage, Set.uIcc_of_le (by linarith : τ.im - 1 ≤ τ.im + 1)] at h
      exact h
    have hjn : Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)
        ≠ Work.Kernels.jInvariantFun τ := by
      intro hjeq
      obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
      refine orbit_free_funnelStrip hτ h2 hre γ ⟨?_, ?_⟩
      · have h1 : (γ • τ).re = z.re := by
          rw [hγ]
          show (((UpperHalfPlane.ofComplex z : UpperHalfPlane)) : ℂ).re = z.re
          rw [hcoe]
        rw [h1]; exact hzre
      · have h1 : (γ • τ).im = z.im := by
          rw [hγ]
          show (((UpperHalfPlane.ofComplex z : UpperHalfPlane)) : ℂ).im = z.im
          rw [hcoe]
        rw [h1]; exact hzim
    have hmd := Work.Residues.mdifferentiableAt_Kfun_snd ℓ d hd τ (UpperHalfPlane.ofComplex z) hjn
    have h := (UpperHalfPlane.mdifferentiableAt_iff
      (f := fun ζ : UpperHalfPlane => Work.Kernels.Kfun ℓ d τ ζ)
      (τ := UpperHalfPlane.ofComplex z)).mp hmd
    have h2' : DifferentiableAt ℂ
        (fun w : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w)) z := hcoe ▸ h
    exact h2'.differentiableWithinAt
  have heq : Set.EqOn (kExt ℓ d τ)
      (fun w : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w))
      (Set.uIcc (0 : ℝ) (1 / 4) ×ℂ Set.uIcc (τ.im - 1) (τ.im + 1)) := by
    intro z hz
    exact kExt_of_im_pos ℓ d τ (hpos z hz)
  exact hcomp.congr heq

/-- **The spike shift for the CKMRV contour integrand.**

For `τ ∈ 𝒟` with `2 ≤ Im τ` and `1/4 < Re τ` — so that the translate pole `z = τ - 1` of
`z ↦ K^{(d)}(τ,z)` (CKMRV Theorem 4.9(3)) lies strictly to the *left* of the contour, outside
the swept rectangle `[0,1/4] × [Im τ - 1, Im τ + 1]` — the segment
`{z = it : t ∈ [Im τ - 1, Im τ + 1]}` of the contour may be replaced by its shift by `1/4` in
the real direction, at the cost of the two horizontal edges of the swept rectangle:

`∫ K(τ,it) e^{-πr²t} dt = ∫ K(τ, 1/4+it) e^{πir²(1/4+it)} dt - i ∫_0^{1/4} K(τ,x+ai)e^{πir²(x+ai)} dx
   + i ∫_0^{1/4} K(τ,x+bi)e^{πir²(x+bi)} dx`,  `a = Im τ - 1`, `b = Im τ + 1`.

Two things are visible in the conclusion and were the point of the whole manoeuvre: there is
**no residue term** (no pole is crossed), and on the shifted segment
`|e^{πir²(1/4+it)}| = e^{-πr²t}` is *the same* Gaussian damping as before (the shift is purely
in the real direction).  The `K^{(d)}`-factors are assembled from `Work.Residues` and
Theorem 4.9 of CKMRV; the correction terms are the edge integrals, whose moduli are
`≈ |K| e^{-πr²(Im τ ∓ 1)}`, i.e. exponentially small as soon as `r ≠ 0`. -/
theorem kernelTransform_spike_shift (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ : UpperHalfPlane} (hτ : τ ∈ Work.Asymptotics.DomainD)
    (h2 : 2 ≤ τ.im) (hre : (1 / 4 : ℝ) < τ.re) (r : ℝ) :
    (∫ y in (τ.im - 1)..(τ.im + 1),
        kExt ℓ d τ ((y : ℂ) * Complex.I)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (y : ℂ))))
      = (∫ y in (τ.im - 1)..(τ.im + 1),
            kExt ℓ d τ (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
              * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2
                  * (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)))
        - Complex.I * (∫ x in (0 : ℝ)..(1 / 4),
            kExt ℓ d τ ((x : ℂ) + ((τ.im - 1 : ℝ) : ℂ) * Complex.I)
              * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2
                  * ((x : ℂ) + ((τ.im - 1 : ℝ) : ℂ) * Complex.I)))
        + Complex.I * (∫ x in (0 : ℝ)..(1 / 4),
            kExt ℓ d τ ((x : ℂ) + ((τ.im + 1 : ℝ) : ℂ) * Complex.I)
              * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2
                  * ((x : ℂ) + ((τ.im + 1 : ℝ) : ℂ) * Complex.I))) := by
  set c : ℂ := Real.pi * Complex.I * (r : ℂ) ^ 2 with hc
  have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (c * z)) :=
    Complex.differentiable_exp.comp ((differentiable_const c).mul differentiable_id)
  have hk : DifferentiableOn ℂ (kExt ℓ d τ)
      (Set.uIcc (0 : ℝ) (1 / 4) ×ℂ Set.uIcc (τ.im - 1) (τ.im + 1)) :=
    kExt_differentiableOn ℓ d hd hτ h2 hre
  have hFdiff : DifferentiableOn ℂ (fun z : ℂ => kExt ℓ d τ z * Complex.exp (c * z))
      (Set.uIcc (0 : ℝ) (1 / 4) ×ℂ Set.uIcc (τ.im - 1) (τ.im + 1)) :=
    hk.mul hexp.differentiableOn
  have hmain' := integral_vertical_segment_shift'
    (F := fun z : ℂ => kExt ℓ d τ z * Complex.exp (c * z)) hFdiff
  have hI2 : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
  have e_left : ∀ y : ℝ, kExt ℓ d τ ((y : ℂ) * Complex.I) * Complex.exp (c * ((y : ℂ) * Complex.I))
      = kExt ℓ d τ ((y : ℂ) * Complex.I) * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (y : ℂ))) := by
    intro y
    have harg : c * ((y : ℂ) * Complex.I) = -(Real.pi * (r : ℂ) ^ 2 * (y : ℂ)) := by
      rw [hc]
      calc Real.pi * Complex.I * (r : ℂ) ^ 2 * ((y : ℂ) * Complex.I)
          = Real.pi * (r : ℂ) ^ 2 * (y : ℂ) * (Complex.I * Complex.I) := by ring
        _ = Real.pi * (r : ℂ) ^ 2 * (y : ℂ) * (-1) := by rw [hI2]
        _ = -(Real.pi * (r : ℂ) ^ 2 * (y : ℂ)) := by ring
    rw [harg]
  have e_shift : ∀ y : ℝ, kExt ℓ d τ (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        * Complex.exp (c * (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = kExt ℓ d τ (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2
            * (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := by
    intro y
    have harg : c * (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        = Real.pi * Complex.I * (r : ℂ) ^ 2 * (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
      rw [hc]
    rw [harg]
  have e_a : ∀ x : ℝ, kExt ℓ d τ ((x : ℂ) + ((τ.im - 1 : ℝ) : ℂ) * Complex.I)
        * Complex.exp (c * ((x : ℂ) + ((τ.im - 1 : ℝ) : ℂ) * Complex.I))
      = kExt ℓ d τ ((x : ℂ) + ((τ.im - 1 : ℝ) : ℂ) * Complex.I)
        * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2
            * ((x : ℂ) + ((τ.im - 1 : ℝ) : ℂ) * Complex.I)) := by
    intro x
    have harg : c * ((x : ℂ) + ((τ.im - 1 : ℝ) : ℂ) * Complex.I)
        = Real.pi * Complex.I * (r : ℂ) ^ 2
            * ((x : ℂ) + ((τ.im - 1 : ℝ) : ℂ) * Complex.I) := by
      rw [hc]
    rw [harg]
  have e_b : ∀ x : ℝ, kExt ℓ d τ ((x : ℂ) + ((τ.im + 1 : ℝ) : ℂ) * Complex.I)
        * Complex.exp (c * ((x : ℂ) + ((τ.im + 1 : ℝ) : ℂ) * Complex.I))
      = kExt ℓ d τ ((x : ℂ) + ((τ.im + 1 : ℝ) : ℂ) * Complex.I)
        * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2
            * ((x : ℂ) + ((τ.im + 1 : ℝ) : ℂ) * Complex.I)) := by
    intro x
    have harg : c * ((x : ℂ) + ((τ.im + 1 : ℝ) : ℂ) * Complex.I)
        = Real.pi * Complex.I * (r : ℂ) ^ 2
            * ((x : ℂ) + ((τ.im + 1 : ℝ) : ℂ) * Complex.I) := by
      rw [hc]
    rw [harg]
  rw [intervalIntegral.integral_congr (fun y _ => e_left y),
      intervalIntegral.integral_congr (fun y _ => e_shift y),
      intervalIntegral.integral_congr (fun x _ => e_a x),
      intervalIntegral.integral_congr (fun x _ => e_b x)] at hmain'
  exact hmain'

/-- **The spike shift in the form of the contour integrand.**

This is `kernelTransform_spike_shift` with the left-hand side written as the CKMRV contour
integrand `Kaxis (Kfun ℓ d) τ` (the two agree by `kExt_imagAxis`), i.e. the exact statement
that the spike `{t : |t - Im τ| ≤ 1}` of `t ↦ ‖K(τ,it)‖` may be replaced by its shift by
`1/4` in the real direction, with no residue term and with the Gaussian damping preserved. -/
theorem kernelTransform_spike_shift_axis (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ : UpperHalfPlane} (hτ : τ ∈ Work.Asymptotics.DomainD)
    (h2 : 2 ≤ τ.im) (hre : (1 / 4 : ℝ) < τ.re) (r : ℝ) :
    (∫ y in (τ.im - 1)..(τ.im + 1),
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ y
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (y : ℂ))))
      = (∫ y in (τ.im - 1)..(τ.im + 1),
            kExt ℓ d τ (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
              * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2
                  * (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)))
        - Complex.I * (∫ x in (0 : ℝ)..(1 / 4),
            kExt ℓ d τ ((x : ℂ) + ((τ.im - 1 : ℝ) : ℂ) * Complex.I)
              * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2
                  * ((x : ℂ) + ((τ.im - 1 : ℝ) : ℂ) * Complex.I)))
        + Complex.I * (∫ x in (0 : ℝ)..(1 / 4),
            kExt ℓ d τ ((x : ℂ) + ((τ.im + 1 : ℝ) : ℂ) * Complex.I)
              * Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2
                  * ((x : ℂ) + ((τ.im + 1 : ℝ) : ℂ) * Complex.I))) := by
  have hcast : (∫ y in (τ.im - 1)..(τ.im + 1),
        kExt ℓ d τ ((y : ℂ) * Complex.I)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (y : ℂ))))
      = ∫ y in (τ.im - 1)..(τ.im + 1),
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ y
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (y : ℂ))) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    have hy0 : 0 < y := by
      have hmem := hy
      rw [Set.uIcc_of_le (by linarith : τ.im - 1 ≤ τ.im + 1)] at hmem
      have h1 : (1 : ℝ) ≤ τ.im - 1 := by linarith
      linarith [hmem.1]
    rw [kExt_imagAxis ℓ d τ hy0]
  rw [← hcast]
  exact kernelTransform_spike_shift ℓ d hd hτ h2 hre r


/-! ## The `S`-duality of the contour integrand

The CKMRV kernels are exchanged by the slash action of `S = [[0,-1],[1,0]]`
(`Work.Kernels.Khat_eq_neg_slash`): `K̂ = -K|^τ_{d/2}S`, i.e. pointwise
`K̂(σ,z) = -(σ)^{-d/2}K(Sσ,z)`.  Since `S` is an involution this can be inverted, and on the
contour `z = it` it becomes the *duality* of the two contour integrands

  `K(τ,it) = -((Sτ))^{d/2} · K̂(Sτ,it)`,

which identifies the low range `t → 0` of `K` at the funnel point `τ` (where the obstruction is
the *removable* pole `z = Sτ = -1/τ` of `z ↦ K(τ,z)`, of height `Im(Sτ) = Im τ/|τ|²`, i.e.
`t ≈ 1/Im τ`) with the behaviour of `K̂` at the *dual* point `Sτ`, near the cusp `0`. -/
theorem khat_eq_neg_slash_pt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : UpperHalfPlane) :
    Work.Kernels.Khat ℓ d τ z
      = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * Work.Kernels.Kfun ℓ d (ModularGroup.S • τ) z := by
  have h := congr_fun (Work.Kernels.Khat_eq_neg_slash ℓ d hd z) τ
  rw [h, Work.Kernels.slash_apply']
  have hj : Work.Kernels.jFun ModularGroup.S (τ : ℂ) = (τ : ℂ) := by
    rw [Work.Kernels.jFun_apply]
    simp
  rw [hj]
  ring

/-- `S • (S • τ) = τ`. -/
lemma S_smul_S_smul (τ : UpperHalfPlane) :
    ModularGroup.S • (ModularGroup.S • τ) = τ := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
  apply UpperHalfPlane.ext
  field_simp

/-- **`S`-duality of the CKMRV contour integrand.** -/
theorem kaxis_dual (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      = - (((ModularGroup.S • τ : UpperHalfPlane)) : ℂ) ^ (d / 2)
          * Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) (ModularGroup.S • τ) t := by
  have h := khat_eq_neg_slash_pt ℓ d hd (ModularGroup.S • τ) (Work.Kernels.imagAxis t ht)
  rw [S_smul_S_smul τ] at h
  rw [Work.Kernels.Kaxis, dif_pos ht, Work.Kernels.Kaxis, dif_pos ht]
  -- h : Khat (Sτ) z = -((Sτ))^{-d/2} * Kfun τ z
  have hβ : (((ModularGroup.S • τ : UpperHalfPlane)) : ℂ) ≠ 0 := by
    intro h0
    have him : ((((ModularGroup.S • τ : UpperHalfPlane)) : ℂ)).im = 0 := by rw [h0]; simp
    rw [UpperHalfPlane.coe_im] at him
    exact (ModularGroup.S • τ).im_pos.ne' him
  set β : ℂ := (((ModularGroup.S • τ : UpperHalfPlane)) : ℂ) ^ (-((d : ℤ) / 2)) with hβdef
  have hβne : β ≠ 0 := zpow_ne_zero _ hβ
  have hkey : Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)
      = - β⁻¹ * Work.Kernels.Khat ℓ d (ModularGroup.S • τ) (Work.Kernels.imagAxis t ht) := by
    rw [h]
    field_simp
  rw [hkey]
  have hβinv : β⁻¹ = (((ModularGroup.S • τ : UpperHalfPlane)) : ℂ) ^ (d / 2) := by
    have hk : ((d : ℤ) / 2) = ((d / 2 : ℕ) : ℤ) := by
      rcases hd with h8 | h24
      · rw [h8]; norm_num
      · rw [h24]; norm_num
    rw [hβdef]
    show ((((ModularGroup.S • τ : UpperHalfPlane)) : ℂ) ^ (-(((d : ℤ) / 2))))⁻¹
        = (((ModularGroup.S • τ : UpperHalfPlane)) : ℂ) ^ (d / 2)
    rw [← zpow_neg, neg_neg, hk, zpow_natCast]
  rw [hβinv]


end

end Work.Asymptotics.HalfFunnel
