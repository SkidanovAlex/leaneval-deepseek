import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Obstruction
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip
import Submission.Work.Asymptotics.exists_jprime_lower_near_imagAxis
import Submission.Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general
import Submission.Work.Asymptotics.lipschitz_jInvariantFun_local
import Submission.Work.Asymptotics.bad_line_slice_simple_zero
import Submission.Work.Asymptotics.j_sub_I_quadratic

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold MatrixGroups

namespace Work.Asymptotics

open Work.Kernels

/-! ## A measure-theoretic input

If `‖f t‖` dominates `c/|t - t₀|` near `t₀ > 0`, then `f` is not Bochner integrable on `(0,∞)`.
This is the mechanism by which `kernelTransform` takes the junk value `0` at a point where a
pole of the kernel meets the contour. -/
lemma not_integrableOn_of_mul_abs_sub_lower {f : ℝ → ℂ} {t₀ c : ℝ} (ht₀ : 0 < t₀) (hc : 0 < c)
    (h : ∀ᶠ t in 𝓝[≠] t₀, c ≤ ‖f t‖ * |t - t₀|) :
    ¬ MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  have hO : (fun x : ℝ => (x - t₀)⁻¹) =O[𝓝[≠] t₀] f := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨c⁻¹, ?_⟩
    filter_upwards [h] with t ht
    rcases eq_or_ne t t₀ with rfl | htne
    · rw [Real.norm_eq_abs, abs_inv, sub_self, abs_zero, inv_zero]
      exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg _)
    · rw [Real.norm_eq_abs, abs_inv]
      have hkey : 1 ≤ (c⁻¹ * ‖f t‖) * |t - t₀| := by
        have hh : c⁻¹ * c ≤ c⁻¹ * (‖f t‖ * |t - t₀|) :=
          mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hc.le)
        rw [inv_mul_cancel₀ (ne_of_gt hc)] at hh
        simpa only [mul_assoc] using hh
      calc |t - t₀|⁻¹ = 1 * |t - t₀|⁻¹ := (one_mul _).symm
        _ ≤ ((c⁻¹ * ‖f t‖) * |t - t₀|) * |t - t₀|⁻¹ :=
              mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr (abs_nonneg _))
        _ = c⁻¹ * ‖f t‖ := by
              rw [mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr (sub_ne_zero.mpr htne)), mul_one]
  have hni : ¬ IntervalIntegrable f volume t₀ (t₀ + 1) :=
    not_intervalIntegrable_of_sub_inv_isBigO_punctured hO (by linarith)
      (by rw [Set.mem_uIcc]; left; exact ⟨le_refl t₀, by linarith⟩)
  intro hf
  refine hni ?_
  rw [intervalIntegrable_iff]
  refine hf.mono_set ?_
  intro x hx
  rw [Set.mem_Ioi]
  rw [Set.mem_uIoc] at hx
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · linarith
  · linarith

/-! ## Elementary facts about the bad line -/

/-- The norm of the contour exponential `e^{-πr²t}`. -/
lemma norm_exp_neg_pi_sq_mul (r t : ℝ) :
    ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ = Real.exp (-(Real.pi * r ^ 2 * t)) := by
  rw [Complex.norm_exp]
  congr 1
  have h : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.ofReal_re]

/-- The point `ofComplex (i t)` of the upper half plane. -/
lemma ofComplex_mul_I_apply (t : ℝ) (ht : 0 < t) :
    ((UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) : ℍ) : ℂ) = (t : ℂ) * Complex.I := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using ht)]

/-- `ofComplex (i t)` is `imagAxis t`. -/
lemma ofComplex_mul_I_eq_imagAxis (t : ℝ) (ht : 0 < t) :
    UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) = imagAxis t ht := by
  apply UpperHalfPlane.ext
  rw [ofComplex_mul_I_apply t ht]
  rfl

/-- The distance from `i t` to `i t₀`. -/
lemma norm_ofComplex_mul_I_sub (t t₀ : ℝ) (ht : 0 < t) (ht₀ : 0 < t₀) :
    ‖((UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) : ℍ) : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖
      = |t - t₀| := by
  rw [ofComplex_mul_I_apply t ht]
  rw [show ((imagAxis t₀ ht₀ : ℍ) : ℂ) = (t₀ : ℂ) * Complex.I from rfl]
  rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs]

/-- The parametrisation `t ↦ i t` of the contour is continuous. -/
lemma continuousAt_ofComplex_mul_I (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ContinuousAt (fun t : ℝ => UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I)) t₀ := by
  have h1 : ContinuousAt (fun t : ℝ => (t : ℂ) * Complex.I) t₀ :=
    Complex.continuous_ofReal.continuousAt.mul continuousAt_const
  have h2 : ContinuousAt (fun z : ℂ => UpperHalfPlane.ofComplex z) ((t₀ : ℂ) * Complex.I) := by
    have hopen : {z : ℂ | 0 < z.im} ∈ 𝓝 ((t₀ : ℂ) * Complex.I) :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simpa using ht₀)
    exact (Work.Asymptotics.continuousOn_ofComplex_im_pos.continuousAt hopen)
  exact h2.comp (f := fun t : ℝ => (t : ℂ) * Complex.I) h1

/-- Euclidean balls form a neighbourhood basis of `ℍ` (the topology of `ℍ` is induced by the
coercion to `ℂ`, but its `Dist` instance is the *hyperbolic* one, so this is worth recording). -/
lemma euclidean_ball_mem_nhds (z : ℍ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ w : ℍ in 𝓝 z, ‖(w : ℂ) - (z : ℂ)‖ < ρ := by
  have hopen : IsOpen {w : ℍ | ‖(w : ℂ) - (z : ℂ)‖ < ρ} :=
    isOpen_lt (continuous_norm.comp (UpperHalfPlane.continuous_coe.sub continuous_const))
      continuous_const
  exact hopen.mem_nhds (by simpa using hρ)

/-- For `τ` with `τ.re = n` (`n = ±1`), the translate `τ - n` has coordinate `i τ.im`. -/
lemma bl_coe_neg_vadd (τ : UpperHalfPlane) (n : ℤ) (hre : τ.re = (n : ℝ)) :
    (((-(n : ℝ)) +ᵥ τ : UpperHalfPlane) : ℂ) = (τ.im : ℂ) * Complex.I := by
  rw [UpperHalfPlane.coe_vadd]
  have hτ : (τ : ℂ) = (n : ℂ) + (τ.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re,
        hre]
    · simp [Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_im]
  rw [hτ]
  push_cast
  ring

/-- The translate `τ - n` (`n = ±1`, `τ.re = n`) is `imagAxis τ.im`. -/
lemma neg_vadd_eq_imagAxis (τ : UpperHalfPlane) (n : ℤ) (hre : τ.re = (n : ℝ)) :
    ((-(n : ℝ)) +ᵥ τ : UpperHalfPlane) = imagAxis τ.im τ.im_pos := by
  apply UpperHalfPlane.ext
  rw [bl_coe_neg_vadd τ n hre]
  rfl

/-- Off the pole divisor the kernel is the cleared value over the `j`-difference. -/
lemma norm_Kfun_eq_cleared (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {τ w : ℍ}
    (h : jInvariantFun w ≠ jInvariantFun τ) :
    ‖Kfun ℓ d τ w‖ = ‖AfunFun ℓ d τ w‖ / ‖jInvariantFun w - jInvariantFun τ‖ := by
  have hτw : jInvariantFun τ ≠ jInvariantFun w := fun hh => h hh.symm
  have hm : Kfun ℓ d τ w * (jInvariantFun τ - jInvariantFun w) = AfunFun ℓ d τ w :=
    Kfun_mul_slope_eq_AfunFun ℓ d hd τ w hτw
  have h2 : jInvariantFun w - jInvariantFun τ ≠ 0 := fun hh => h (sub_eq_zero.mp hh)
  have h3 : ‖Kfun ℓ d τ w‖ * ‖jInvariantFun w - jInvariantFun τ‖ = ‖AfunFun ℓ d τ w‖ := by
    rw [norm_sub_rev, ← norm_mul, hm]
  rw [eq_div_iff (norm_ne_zero_iff.mpr h2), h3]

/-! ## The final step: a `1/|t - t₀|` lower bound on the contour forces the junk value -/

lemma kernelTransform_eq_zero_of_line_lower (K : ℍ → ℍ → ℂ) (τ : ℍ) (r : ℝ) {t₀ c : ℝ}
    (ht₀ : 0 < t₀) (hc : 0 < c)
    (h : ∀ᶠ t : ℝ in 𝓝[≠] t₀, c ≤
      ‖K τ (UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I)) *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ * |t - t₀|) :
    kernelTransform K τ r = 0 := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[≠] t₀, 0 < t := by
    have h1 : ∀ᶠ t : ℝ in 𝓝 t₀, 0 < t := isOpen_Ioi.mem_nhds ht₀
    exact h1.filter_mono nhdsWithin_le_nhds
  have h' : ∀ᶠ t : ℝ in 𝓝[≠] t₀, c ≤
      ‖Kaxis K τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ * |t - t₀| := by
    filter_upwards [h, hpos] with t ht htpos
    have h2 : imagAxis t htpos = UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) :=
      (ofComplex_mul_I_eq_imagAxis t htpos).symm
    rw [Kaxis, dif_pos htpos, h2]
    exact ht
  have hni := not_integrableOn_of_mul_abs_sub_lower ht₀ hc h'
  have hzero : (∫ t in Set.Ioi (0 : ℝ),
      Kaxis K τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) = 0 :=
    integral_undef hni
  simp only [kernelTransform, hzero, mul_zero]

/-- Elementary estimate: `a e / (4 L) ≤ (A / J) E x` from `a/2 ≤ A`, `e/2 ≤ E`, `J ≤ L x`
and positivity of `a, e, J, L, x`. -/
lemma div_estimate {a e A E J L x : ℝ} (ha : 0 < a) (he : 0 < e) (hJ : 0 < J) (hL : 0 < L)
    (hx : 0 < x) (hA : a / 2 ≤ A) (hE : e / 2 ≤ E) (hJL : J ≤ L * x) :
    a * e / (4 * L) ≤ A / J * E * x := by
  have hJLpos : 0 < L * x := mul_pos hL hx
  have hA0 : 0 ≤ A := by linarith
  have hE0 : 0 ≤ E := by linarith
  have h1 : (a / 2) / (L * x) ≤ A / J := by
    rw [div_le_div_iff₀ hJLpos hJ]
    have h2 : a / 2 * J ≤ a / 2 * (L * x) := mul_le_mul_of_nonneg_left hJL (by linarith)
    have h3 : a / 2 * (L * x) ≤ A * (L * x) := mul_le_mul_of_nonneg_right hA hJLpos.le
    linarith
  have h4 : a * e / (4 * L) = (a / 2) / (L * x) * (e / 2) * x := by
    field_simp
    ring
  rw [h4]
  calc (a / 2) / (L * x) * (e / 2) * x ≤ A / J * (e / 2) * x := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by linarith)) hx.le
    _ ≤ A / J * E * x := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (div_nonneg hA0 hJ.le)) hx.le

/-! ## The non-degenerate case `τ.im ≠ 1`

At such a point the pole of `z ↦ K^{(d)}(τ,z)` on the contour carries the non-zero residue
`n/(2π)` (CKMRV Theorem 4.9(3)); equivalently the cleared value `AfunFun τ (τ - n)` equals
`-(n/2π)j'(τ-n) ≠ 0`.  The contour integrand then dominates `c/|t - τ.im|`, hence is not
integrable, and the transform is the junk value `0`. -/
theorem kernelTransform_eq_zero_bad_line_of_im_ne_one (ℓ : LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {τ : UpperHalfPlane} (n : ℤ) (hn : n = 1 ∨ n = -1)
    (hre : τ.re = (n : ℝ)) (ht : τ.im ≠ 1) :
    kernelTransform (Kfun ℓ d) τ r = 0 := by
  set t₀ : ℝ := τ.im with ht₀def
  have ht₀pos : 0 < t₀ := ht₀def ▸ τ.im_pos
  have ht₁ : t₀ ≠ 1 := by
    intro hcon
    rw [ht₀def] at hcon
    exact ht hcon
  set φ : ℝ → ℍ := fun t => UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) with hφdef
  have hφimg : φ t₀ = imagAxis t₀ ht₀pos := ofComplex_mul_I_eq_imagAxis t₀ ht₀pos
  have hφpole : φ t₀ = (-(n : ℝ)) +ᵥ τ := by
    rw [hφimg, neg_vadd_eq_imagAxis τ n hre]
  set z₀ : ℍ := φ t₀ with hz₀def
  have hz₀coe : (z₀ : ℂ) = (t₀ : ℂ) * Complex.I := by
    rw [hz₀def, hφdef, ofComplex_mul_I_apply t₀ ht₀pos]
  have hz₀img : z₀ = imagAxis t₀ ht₀pos := by rw [hz₀def]; exact hφimg
  have hz₀j : jInvariantFun z₀ = jInvariantFun τ := by
    have h1 : z₀ = (-(n : ℝ)) +ᵥ τ := by rw [hz₀def]; exact hφpole
    rw [h1]; exact jInvariantFun_neg_vadd τ n hn
  -- the cleared value at the pole is non-zero
  have hval : AfunFun ℓ d τ z₀ = -((n : ℂ) / (2 * Real.pi)) * Work.Residues.jprime z₀ := by
    have h1 : z₀ = (-(n : ℝ)) +ᵥ τ := by rw [hz₀def]; exact hφpole
    rw [h1]
    exact AfunFun_neg_vadd ℓ d hd τ n hn (fun z => Work.Residues.AfunPlus_neg_one d hd z)
      (fun z => Work.Residues.AfunMinus_neg_one ℓ d hd z)
  have hjp : Work.Residues.jprime z₀ ≠ 0 := by
    obtain ⟨η, c, hη, hc, hb⟩ := exists_jprime_lower_near_imagAxis ht₀pos ht₁
    have h0 : ‖(z₀ : ℂ) - Complex.I * (t₀ : ℂ)‖ = 0 := by
      rw [hz₀coe, mul_comm]; simp
    have h1 := hb z₀ (by rw [h0]; exact hη)
    intro hcon
    rw [hcon, norm_zero] at h1
    exact absurd h1 (not_le.mpr hc)
  have hAz₀ : AfunFun ℓ d τ z₀ ≠ 0 := by
    rw [hval]
    refine mul_ne_zero (neg_ne_zero.mpr (div_ne_zero ?_ ?_)) hjp
    · rcases hn with h | h <;> rw [h] <;> norm_num
    · push_cast
      exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hApos : 0 < ‖AfunFun ℓ d τ z₀‖ := norm_pos_iff.mpr hAz₀
  -- local data
  obtain ⟨ρJ, hρJ, cJ, hcJ, hbJ⟩ := MiddleRange.exists_diffQuotient_lower_general ht₀pos ht₁
  have hbJ' : ∀ p q : ℍ, ‖(p : ℂ) - (z₀ : ℂ)‖ < ρJ → ‖(q : ℂ) - (z₀ : ℂ)‖ < ρJ →
      cJ * ‖(p : ℂ) - (q : ℂ)‖ ≤ ‖jInvariantFun p - jInvariantFun q‖ := by
    intro p q hp hq
    rw [hz₀img] at hp hq
    exact hbJ p q hp hq
  obtain ⟨rL, L, hrL, hLnn, hbL⟩ := lipschitz_jInvariantFun_local z₀
  set L' : ℝ := max L 1 with hL'def
  have hL'pos : 0 < L' := lt_of_lt_of_le one_pos (le_max_right L 1)
  -- the parametrisation is continuous at `t₀`
  have hpar : ContinuousAt φ t₀ := by
    rw [hφdef]; exact continuousAt_ofComplex_mul_I t₀ ht₀pos
  -- the Lipschitz bound in the `t`-variable
  have hLline : ∀ᶠ t : ℝ in 𝓝[≠] t₀,
      ‖jInvariantFun (φ t) - jInvariantFun τ‖ ≤ L * |t - t₀| := by
    have h1 : ∀ᶠ w : ℍ in 𝓝 z₀, ‖jInvariantFun w - jInvariantFun τ‖ ≤ L * ‖(w : ℂ) - (z₀ : ℂ)‖ := by
      refine (euclidean_ball_mem_nhds z₀ hrL).mono ?_
      intro w hw
      have h2 := hbL w z₀ hw (by rw [sub_self]; simpa using hrL)
      rwa [hz₀j] at h2
    have h2 : ∀ᶠ t : ℝ in 𝓝 t₀, ‖jInvariantFun (φ t) - jInvariantFun τ‖ ≤
        L * ‖((φ t : ℍ) : ℂ) - (z₀ : ℂ)‖ := hpar.tendsto.eventually h1
    have htpos : ∀ᶠ t : ℝ in 𝓝[≠] t₀, 0 < t :=
      Eventually.filter_mono nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds ht₀pos : ∀ᶠ t : ℝ in 𝓝 t₀, 0 < t)
    filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds h2, htpos] with t ht' htpos'
    have hnorm : ‖((φ t : ℍ) : ℂ) - (z₀ : ℂ)‖ = |t - t₀| := by
      rw [hφdef, hz₀img]
      exact norm_ofComplex_mul_I_sub t t₀ htpos' ht₀pos
    rw [hnorm] at ht'
    exact ht'
  -- the lower bound for `A` in the `t`-variable
  have hAline : ∀ᶠ t : ℝ in 𝓝[≠] t₀, ‖AfunFun ℓ d τ z₀‖ / 2 ≤ ‖AfunFun ℓ d τ (φ t)‖ := by
    have h1 : ∀ᶠ w : ℍ in 𝓝 z₀, ‖AfunFun ℓ d τ z₀‖ / 2 ≤ ‖AfunFun ℓ d τ w‖ := by
      have h2 : ContinuousAt (fun w : UpperHalfPlane => AfunFun ℓ d τ w) z₀ :=
        (mdifferentiable_AfunFun_snd ℓ d hd τ).continuous.continuousAt
      have h3 : Tendsto (fun w : UpperHalfPlane => ‖AfunFun ℓ d τ w - AfunFun ℓ d τ z₀‖)
          (𝓝 z₀) (𝓝 0) := by
        have h4 : Tendsto (fun w : UpperHalfPlane => AfunFun ℓ d τ w - AfunFun ℓ d τ z₀)
            (𝓝 z₀) (𝓝 0) := by
          have h5 := h2.tendsto.sub (tendsto_const_nhds :
            Tendsto (fun _ : UpperHalfPlane => AfunFun ℓ d τ z₀) (𝓝 z₀) (𝓝 (AfunFun ℓ d τ z₀)))
          simpa using h5
        simpa using h4.norm
      filter_upwards [h3.eventually (eventually_lt_nhds (half_pos hApos))] with w hw
      have h4 : ‖AfunFun ℓ d τ z₀‖ - ‖AfunFun ℓ d τ w‖ ≤ ‖AfunFun ℓ d τ w - AfunFun ℓ d τ z₀‖ := by
        have h5 := norm_sub_norm_le (AfunFun ℓ d τ z₀) (AfunFun ℓ d τ w)
        rwa [norm_sub_rev] at h5
      linarith [h4, hw]
    exact Eventually.filter_mono nhdsWithin_le_nhds (hpar.tendsto.eventually h1)
  -- the divisor is avoided
  have hjline : ∀ᶠ t : ℝ in 𝓝[≠] t₀, jInvariantFun (φ t) ≠ jInvariantFun τ := by
    have h1 : ∀ᶠ t : ℝ in 𝓝[≠] t₀, ‖((φ t : ℍ) : ℂ) - (z₀ : ℂ)‖ < ρJ :=
      Eventually.filter_mono nhdsWithin_le_nhds (hpar.tendsto.eventually (euclidean_ball_mem_nhds z₀ hρJ))
    have htpos : ∀ᶠ t : ℝ in 𝓝[≠] t₀, 0 < t :=
      Eventually.filter_mono nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds ht₀pos : ∀ᶠ t : ℝ in 𝓝 t₀, 0 < t)
    filter_upwards [h1, htpos, self_mem_nhdsWithin] with t ht' htpos' htne
    intro hcon
    have h2 : cJ * ‖((φ t : ℍ) : ℂ) - (z₀ : ℂ)‖ ≤ ‖jInvariantFun (φ t) - jInvariantFun z₀‖ :=
      hbJ' (φ t) z₀ ht' (by rw [sub_self, norm_zero]; exact hρJ)
    rw [hcon, hz₀j, sub_self, norm_zero] at h2
    have h3 : 0 < ‖((φ t : ℍ) : ℂ) - (z₀ : ℂ)‖ := by
      refine norm_pos_iff.mpr (fun hzero => htne ?_)
      have h4 : ((φ t : ℍ) : ℂ) = (t : ℂ) * Complex.I := by
        rw [hφdef, ofComplex_mul_I_apply t htpos']
      have hzero' : ((φ t : ℍ) : ℂ) = (z₀ : ℂ) := sub_eq_zero.mp hzero
      have h5 : (t : ℂ) * Complex.I = (t₀ : ℂ) * Complex.I := by rw [← h4, hzero', hz₀coe]
      have h6 : (t : ℂ) = (t₀ : ℂ) := mul_right_cancel₀ Complex.I_ne_zero h5
      exact Complex.ofReal_injective h6
    exact (not_lt_of_ge h2) (mul_pos hcJ h3)
  -- the exponential bound
  have hexpline : ∀ᶠ t : ℝ in 𝓝[≠] t₀,
      Real.exp (-(Real.pi * r ^ 2 * t₀)) / 2 ≤ Real.exp (-(Real.pi * r ^ 2 * t)) := by
    have hc' : Continuous (fun t : ℝ => Real.exp (-(Real.pi * r ^ 2 * t))) := by fun_prop
    have h1 : Tendsto (fun t : ℝ => Real.exp (-(Real.pi * r ^ 2 * t))) (𝓝[≠] t₀)
        (𝓝 (Real.exp (-(Real.pi * r ^ 2 * t₀)))) :=
      hc'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine h1.eventually (eventually_ge_nhds ?_)
    have := Real.exp_pos (-(Real.pi * r ^ 2 * t₀))
    linarith
  -- the final estimate on the contour
  refine kernelTransform_eq_zero_of_line_lower (K := Kfun ℓ d) (τ := τ) (r := r) (t₀ := t₀)
    (c := ‖AfunFun ℓ d τ z₀‖ * Real.exp (-(Real.pi * r ^ 2 * t₀)) / (4 * L')) ht₀pos ?_ ?_
  · exact div_pos (mul_pos hApos (Real.exp_pos _)) (by positivity)
  · filter_upwards [hAline, hLline, hjline, hexpline] with t hAt hLt hjt hext
    have hdiv : 0 < ‖jInvariantFun (φ t) - jInvariantFun τ‖ :=
      norm_pos_iff.mpr (fun hh => hjt (sub_eq_zero.mp hh))
    have htne : t ≠ t₀ := by
      intro h
      rw [h] at hjt
      rw [hz₀j] at hjt
      exact hjt rfl
    have hypos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr htne)
    have hLt' : ‖jInvariantFun (φ t) - jInvariantFun τ‖ ≤ L' * |t - t₀| :=
      le_trans hLt (mul_le_mul_of_nonneg_right (le_max_left L 1) (abs_nonneg _))
    have hexp'' : Real.exp (-(Real.pi * r ^ 2 * t₀)) / 2 ≤
        ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ := by
      rw [norm_exp_neg_pi_sq_mul]; exact hext
    rw [norm_mul, norm_Kfun_eq_cleared ℓ d hd hjt]
    exact div_estimate hApos (Real.exp_pos _) hdiv hL'pos hypos hAt hexp'' hLt'

/-- **The elliptic mechanism.**  If the slice `A` of the kernel at `τ` (with `j τ = j i`) has
a *simple* zero at the elliptic point `i`, while `j - j i` has a *double* zero there which is
bounded above by a quadratic expression, then the contour integrand dominates `const/|t - 1|`
and the transform is the junk value `0`. -/
lemma kernelTransform_eq_zero_of_slice_simple_zero (K : ℍ → ℍ → ℂ) (A : ℍ → ℂ) (τ : ℍ) (r : ℝ)
    (hdec : ∀ w : ℍ, jInvariantFun w ≠ jInvariantFun τ →
      K τ w = A w / (jInvariantFun τ - jInvariantFun w))
    (hjτ : jInvariantFun τ = jInvariantFun UpperHalfPlane.I)
    (hslice : ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ w : ℍ,
      ‖(w : ℂ) - Complex.I‖ < ρ → c * ‖(w : ℂ) - Complex.I‖ ≤ ‖A w‖)
    (hjup : ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ w : ℍ, ‖(w : ℂ) - Complex.I‖ < ρ →
      ‖jInvariantFun w - jInvariantFun UpperHalfPlane.I‖ ≤ C * ‖(w : ℂ) - Complex.I‖ ^ 2)
    (hjlow : ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ w : ℍ, ‖(w : ℂ) - Complex.I‖ < ρ →
      c * ‖(w : ℂ) - Complex.I‖ ^ 2 ≤ ‖jInvariantFun w - jInvariantFun UpperHalfPlane.I‖) :
    kernelTransform K τ r = 0 := by
  obtain ⟨ρA, cA, hρA, hcA, boundA⟩ := hslice
  obtain ⟨ρU, CU, hρU, hCU, boundU⟩ := hjup
  obtain ⟨ρL, cL, hρL, hcL, boundL⟩ := hjlow
  set φ : ℝ → ℍ := fun t => UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) with hφdef
  have hφI : φ 1 = UpperHalfPlane.I := by
    rw [hφdef]
    apply UpperHalfPlane.ext
    rw [ofComplex_mul_I_apply 1 one_pos, UpperHalfPlane.coe_I, Complex.ofReal_one, one_mul]
  have hpar : ContinuousAt φ 1 := by
    rw [hφdef]; exact continuousAt_ofComplex_mul_I 1 one_pos
  have hballA : ∀ᶠ t : ℝ in 𝓝[≠] (1 : ℝ), ‖((φ t : ℍ) : ℂ) - Complex.I‖ < ρA := by
    have h1 : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ), ‖((φ t : ℍ) : ℂ) - Complex.I‖ < ρA := by
      have h2 : ∀ᶠ w : ℍ in 𝓝 (φ 1), ‖(w : ℂ) - Complex.I‖ < ρA := by
        rw [hφI]
        exact euclidean_ball_mem_nhds UpperHalfPlane.I hρA
      exact hpar.tendsto.eventually h2
    exact Eventually.filter_mono nhdsWithin_le_nhds h1
  have hballU : ∀ᶠ t : ℝ in 𝓝[≠] (1 : ℝ), ‖((φ t : ℍ) : ℂ) - Complex.I‖ < ρU := by
    have h1 : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ), ‖((φ t : ℍ) : ℂ) - Complex.I‖ < ρU := by
      have h2 : ∀ᶠ w : ℍ in 𝓝 (φ 1), ‖(w : ℂ) - Complex.I‖ < ρU := by
        rw [hφI]
        exact euclidean_ball_mem_nhds UpperHalfPlane.I hρU
      exact hpar.tendsto.eventually h2
    exact Eventually.filter_mono nhdsWithin_le_nhds h1
  have hballL : ∀ᶠ t : ℝ in 𝓝[≠] (1 : ℝ), ‖((φ t : ℍ) : ℂ) - Complex.I‖ < ρL := by
    have h1 : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ), ‖((φ t : ℍ) : ℂ) - Complex.I‖ < ρL := by
      have h2 : ∀ᶠ w : ℍ in 𝓝 (φ 1), ‖(w : ℂ) - Complex.I‖ < ρL := by
        rw [hφI]
        exact euclidean_ball_mem_nhds UpperHalfPlane.I hρL
      exact hpar.tendsto.eventually h2
    exact Eventually.filter_mono nhdsWithin_le_nhds h1
  have htpos : ∀ᶠ t : ℝ in 𝓝[≠] (1 : ℝ), 0 < t :=
    Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have hexp : ∀ᶠ t : ℝ in 𝓝[≠] (1 : ℝ),
      Real.exp (-(Real.pi * r ^ 2 * (1 : ℝ))) / 2 ≤ Real.exp (-(Real.pi * r ^ 2 * t)) := by
    have hc' : Continuous (fun t : ℝ => Real.exp (-(Real.pi * r ^ 2 * t))) := by fun_prop
    have h1 : Tendsto (fun t : ℝ => Real.exp (-(Real.pi * r ^ 2 * t))) (𝓝[≠] (1 : ℝ))
        (𝓝 (Real.exp (-(Real.pi * r ^ 2 * (1 : ℝ))))) :=
      hc'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine h1.eventually (eventually_ge_nhds ?_)
    have := Real.exp_pos (-(Real.pi * r ^ 2 * (1 : ℝ)))
    linarith
  refine kernelTransform_eq_zero_of_line_lower (K := K) (τ := τ) (r := r) (t₀ := 1)
    (c := cA / CU * (Real.exp (-(Real.pi * r ^ 2 * (1 : ℝ))) / 2)) one_pos ?_ ?_
  · positivity
  · filter_upwards [hballA, hballU, hballL, htpos, hexp, self_mem_nhdsWithin]
      with t hA1 hU1 hL1 htpos' hexp' htne
    have hIcoe : ((imagAxis 1 one_pos : ℍ) : ℂ) = Complex.I := by
      change (1 : ℂ) * Complex.I = Complex.I
      rw [one_mul]
    have hdist : ‖((φ t : ℍ) : ℂ) - Complex.I‖ = |t - 1| := by
      have h1 : Complex.I = ((imagAxis 1 one_pos : ℍ) : ℂ) := hIcoe.symm
      rw [h1]
      exact norm_ofComplex_mul_I_sub t 1 htpos' one_pos
    have habs : 0 < |t - 1| := abs_pos.mpr (sub_ne_zero.mpr htne)
    have hA2 : cA * |t - 1| ≤ ‖A (φ t)‖ := by
      have h := boundA (φ t) hA1
      rwa [hdist] at h
    have hU2 : ‖jInvariantFun (φ t) - jInvariantFun τ‖ ≤ CU * |t - 1| ^ 2 := by
      have h := boundU (φ t) hU1
      rw [hdist] at h
      rw [hjτ]
      exact h
    have hL2 : cL * |t - 1| ^ 2 ≤ ‖jInvariantFun (φ t) - jInvariantFun τ‖ := by
      have h := boundL (φ t) hL1
      rw [hdist] at h
      rw [hjτ]
      exact h
    have hdiv : jInvariantFun (φ t) ≠ jInvariantFun τ := by
      intro hcon
      have h1 : cL * |t - 1| ^ 2 ≤ 0 := by
        rw [hcon, sub_self, norm_zero] at hL2
        exact hL2
      have h2 : 0 < cL * |t - 1| ^ 2 := mul_pos hcL (pow_pos habs 2)
      linarith
    have hJpos : 0 < ‖jInvariantFun τ - jInvariantFun (φ t)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hdiv))
    have hK : K τ (φ t) = A (φ t) / (jInvariantFun τ - jInvariantFun (φ t)) := hdec (φ t) hdiv
    rw [hK, norm_mul, norm_div]
    have hexp'' : Real.exp (-(Real.pi * r ^ 2 * (1 : ℝ))) / 2 ≤
        ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ := by
      rw [norm_exp_neg_pi_sq_mul]; exact hexp'
    have h5 : 0 < CU * |t - 1| ^ 2 := mul_pos hCU (pow_pos habs 2)
    have hX : cA / CU ≤ ‖A (φ t)‖ / (CU * |t - 1| ^ 2) * |t - 1| := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hCU h5]
      nlinarith [hA2, habs, hCU, norm_nonneg (A (φ t))]
    have hY : ‖A (φ t)‖ / (CU * |t - 1| ^ 2) * |t - 1| ≤
        ‖A (φ t)‖ / ‖jInvariantFun τ - jInvariantFun (φ t)‖ * |t - 1| := by
      have h6 : ‖jInvariantFun τ - jInvariantFun (φ t)‖ ≤ CU * |t - 1| ^ 2 := by
        rw [norm_sub_rev]; exact hU2
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (norm_nonneg _) hJpos h6) (abs_nonneg _)
    calc cA / CU * (Real.exp (-(Real.pi * r ^ 2 * (1 : ℝ))) / 2)
        ≤ (‖A (φ t)‖ / (CU * |t - 1| ^ 2) * |t - 1|) *
            (Real.exp (-(Real.pi * r ^ 2 * (1 : ℝ))) / 2) :=
          mul_le_mul hX (le_refl _) (by positivity) (by positivity)
      _ ≤ (‖A (φ t)‖ / ‖jInvariantFun τ - jInvariantFun (φ t)‖ * |t - 1|) *
            ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ :=
          mul_le_mul hY hexp'' (by positivity) (by positivity)
      _ = ‖A (φ t)‖ / ‖jInvariantFun τ - jInvariantFun (φ t)‖ *
            ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ * |t - 1| := by ring

/-- **The elliptic case at the reference point `τ = n + i`.**  At `τ = n + i` the pole
`z₀ = τ - n = i` is the elliptic point of order two; the residue is still `n/(2π) ≠ 0`, so the
contour integrand is not integrable and the transform vanishes.  Its analytic input is
`bad_line_AfunFun_slice_simple_zero`. -/
theorem kernelTransform_eq_zero_bad_line_at_I (ℓ : LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    kernelTransform (Kfun ℓ d) ((n : ℝ) +ᵥ imagAxis 1 one_pos) r = 0 := by
  set τ : ℍ := (n : ℝ) +ᵥ imagAxis 1 one_pos with hτdef
  have hI : (imagAxis 1 one_pos : ℍ) = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    change (1 : ℂ) * Complex.I = Complex.I
    rw [one_mul]
  have hτj : jInvariantFun τ = jInvariantFun UpperHalfPlane.I := by
    rcases hn with h | h
    · rw [hτdef, h, hI]
      simpa using KernelFacts.jInvariantFun_vadd_one UpperHalfPlane.I
    · rw [hτdef, h, hI]
      simpa using jInvariantFun_neg_vadd UpperHalfPlane.I (1 : ℤ) (Or.inl rfl)
  refine kernelTransform_eq_zero_of_slice_simple_zero (Kfun ℓ d)
    (fun w => AfunFun ℓ d τ w) τ r ?_ hτj ?_ ?_ ?_
  · intro w hw
    have hne' : jInvariantFun τ ≠ jInvariantFun w := fun hh => hw hh.symm
    have hden : jInvariantFun τ - jInvariantFun w ≠ 0 := sub_ne_zero.mpr hne'
    rw [eq_div_iff hden]
    exact Kfun_mul_slope_eq_AfunFun ℓ d hd τ w hne'
  · exact bad_line_AfunFun_slice_simple_zero ℓ d hd n hn
  · obtain ⟨ρ, c, C, hρ, hc, hC, hb⟩ := j_sub_I_quadratic
    exact ⟨ρ, C, hρ, hC, fun z hz => (hb z hz).2⟩
  · obtain ⟨ρ, c, C, hρ, hc, hC, hb⟩ := j_sub_I_quadratic
    exact ⟨ρ, c, hρ, hc, fun z hz => (hb z hz).1⟩

/-- **The elliptic case `τ.im = 1`.**  The two branches of the pole divisor merge at the
elliptic point `z₀ = i`, and the residue of `z ↦ K^{(d)}(τ,z)` there is still `n/(2π) ≠ 0`;
hence the contour integrand is not integrable and the transform vanishes. -/
theorem kernelTransform_eq_zero_bad_line_of_im_eq_one_of_slice (ℓ : LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    ∀ τ : UpperHalfPlane, τ.re = (n : ℝ) → τ.im = 1 →
      kernelTransform (Kfun ℓ d) τ r = 0 := by
  intro τ hre ht
  have hτ : τ = (n : ℝ) +ᵥ imagAxis 1 one_pos := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd]
    have h1 : ((imagAxis 1 one_pos : ℍ) : ℂ) = (1 : ℂ) * Complex.I := rfl
    rw [h1]
    have h2 : (τ : ℂ) = (n : ℂ) + (1 : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re,
          hre]
      · simp [Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_im, ht]
    rw [h2]
    push_cast
    ring
  rw [hτ]
  exact kernelTransform_eq_zero_bad_line_at_I ℓ d hd r n hn

/-! ## The main theorem -/

theorem bad_line_kernelTransform_eq_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {s₀ : ℝ} (hs₀ : 0 < s₀) (r : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : UpperHalfPlane,
      (τ.re = 1 ∨ τ.re = -1) → |τ.im - s₀| < δ →
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r = 0 := by
  refine ⟨1, one_pos, ?_⟩
  intro τ hre _
  rcases hre with hre | hre
  · by_cases h1 : τ.im = 1
    · exact kernelTransform_eq_zero_bad_line_of_im_eq_one_of_slice ℓ d hd r 1 (Or.inl rfl) τ
        (by simpa using hre) h1
    · exact kernelTransform_eq_zero_bad_line_of_im_ne_one ℓ d hd r 1 (Or.inl rfl)
        (by simpa using hre) h1
  · by_cases h1 : τ.im = 1
    · exact kernelTransform_eq_zero_bad_line_of_im_eq_one_of_slice ℓ d hd r (-1) (Or.inr rfl) τ
        (by simpa using hre) h1
    · exact kernelTransform_eq_zero_bad_line_of_im_ne_one ℓ d hd r (-1) (Or.inr rfl)
        (by simpa using hre) h1

end Work.Asymptotics
