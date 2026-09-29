import Mathlib
import Submission.Work.TMComp.Kotani.RectDefs

/-!
# Cauchy's integral formula on the boundary of a rectangle

Let `f : ℂ → ℂ` be complex differentiable on the closed rectangle `[a,b] × [c,d]` (as a subset of
`ℂ`) and let `z` be a point of the *open* rectangle.  Then the counterclockwise boundary integral
of `w ↦ (w - z)⁻¹ * f w` equals `2πi f z`.

The proof splits the integrand as

  `(w - z)⁻¹ * f w = (w - z)⁻¹ * (f w - f z) + (w - z)⁻¹ * f z`.

* The first term is the difference quotient of `f` at `z` off the point `z`; extended by `deriv f z`
  it is `dslope f z`, which is continuous on the closed rectangle and complex differentiable on the
  open rectangle except at the single point `z`, so Cauchy–Goursat
  (`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`) gives that its
  boundary integral vanishes.
* The second term reduces the statement to the residue computation `∮ (w - z)⁻¹ dw = 2πi`, which is
  done here by hand: along the four sides the integrand has the explicit antiderivatives
  `log ((·) + ki - z)` (bottom and top), `log (m + (·)i - z)` (right) and
  `log (-i * (m + (·)i - z))` (left, where the rotated branch is needed to stay inside
  `Complex.slitPlane`), and the four resulting boundary values combine to `2πi` using the two
  elementary identities `log u - log (-i u) = πi/2` (second quadrant) and
  `log (-i u) - log u = 3πi/2` (third quadrant).
-/

namespace Work.TMComp.RedC8

open MeasureTheory intervalIntegral Set Complex Filter
open scoped Topology

noncomputable section



/-- `log u - log (-I*u) = (π/2) I` for `u` in the open second quadrant. -/
private lemma log_sub_log_negI_mul {u : ℂ} (hre : u.re < 0) (him : 0 < u.im) :
    Complex.log u - Complex.log (-Complex.I * u) = (Real.pi / 2 : ℂ) * Complex.I := by
  have hu : u ≠ 0 := by
    intro h; rw [h] at him; simp at him
  have harg_gt : Real.pi / 2 < u.arg := by
    by_contra h
    rw [not_lt] at h
    rcases (Complex.arg_le_pi_div_two_iff.1 h) with h1 | h1
    · linarith
    · linarith
  have hsum : (-Complex.I).arg + u.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_neg_I, Set.mem_Ioc]
    exact ⟨by linarith [Real.pi_pos, harg_gt],
      by have := Complex.arg_le_pi u; linarith [Real.pi_pos]⟩
  have hlog : Complex.log (-Complex.I * u) = Complex.log (-Complex.I) + Complex.log u :=
    Complex.log_mul (by simp) hu hsum
  rw [hlog, Complex.log_neg_I]
  ring

/-- `log (-I*u) - log u = (3π/2) I` for `u` in the open third quadrant. -/
private lemma log_negI_mul_sub_log {u : ℂ} (hre : u.re < 0) (him : u.im < 0) :
    Complex.log (-Complex.I * u) - Complex.log u = (3 * Real.pi / 2 : ℂ) * Complex.I := by
  have hu : u ≠ 0 := by
    intro h; rw [h] at him; simp at him
  have hneg : -u ≠ 0 := neg_ne_zero.mpr hu
  have harg_lt : u.arg < 0 := Complex.arg_neg_iff.2 him
  have h1 : |(-u).arg| < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]
    left
    simp only [Complex.neg_re]
    linarith
  have hsum1 : Complex.I.arg + (-u).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_I]
    have h2 := (abs_lt.1 h1).2
    have h3 := Complex.neg_pi_lt_arg (-u)
    refine ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsum2 : (-1 : ℂ).arg + u.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_neg_one]
    have h3 := Complex.neg_pi_lt_arg u
    refine ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hB : Complex.log (Complex.I * (-u)) = Complex.log Complex.I + Complex.log (-u) :=
    Complex.log_mul (by simp) hneg hsum1
  have hD : Complex.log (-1 * u) = Complex.log (-1) + Complex.log u :=
    Complex.log_mul (by norm_num) hu hsum2
  have hstep1 : -Complex.I * u = Complex.I * (-u) := by ring
  rw [hstep1, hB, show -u = -1 * u by ring, hD, Complex.log_I, Complex.log_neg_one]
  ring

private lemma I_mul_negI_mul (x : ℂ) : Complex.I * (-Complex.I * x) = x := by
  rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

lemma negI_mul_negI_mul (x : ℂ) : -Complex.I * (-Complex.I * x) = -x := by
  rw [← mul_assoc, neg_mul, mul_neg, Complex.I_mul_I, neg_neg, neg_one_mul]

private lemma hasDerivAt_log_horiz (z : ℂ) (c x : ℝ) (h : c ≠ z.im) :
    HasDerivAt (fun t : ℝ => Complex.log ((t:ℂ) + (c:ℂ)*Complex.I - z))
      (((x:ℂ) + (c:ℂ)*Complex.I - z)⁻¹) x := by
  have hmem : ((x:ℂ) + (c:ℂ)*Complex.I - z) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_not_le_zero]
    intro hle
    have him0 : ((x:ℂ) + (c:ℂ)*Complex.I - z).im = 0 := by
      have := (Complex.le_def.1 hle).2
      simpa using this
    simp at him0
    exact h (sub_eq_zero.mp him0)
  have hd : HasDerivAt (fun t : ℝ => (t:ℂ) + (c:ℂ)*Complex.I - z) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((c:ℂ)*Complex.I - z)
  simpa only [Function.comp_def, mul_one] using (Complex.hasDerivAt_log hmem).comp x hd

private lemma hasDerivAt_log_vert (z : ℂ) (b x : ℝ) (h : z.re < b) :
    HasDerivAt (fun t : ℝ => Complex.log ((b:ℂ) + (t:ℂ)*Complex.I - z))
      (Complex.I * (((b:ℂ) + (x:ℂ)*Complex.I - z)⁻¹)) x := by
  have hmem : ((b:ℂ) + (x:ℂ)*Complex.I - z) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_not_le_zero]
    intro hle
    have hre : ((b:ℂ) + (x:ℂ)*Complex.I - z).re = b - z.re := by simp
    have := (Complex.le_def.1 hle).1
    rw [hre] at this
    simp at this
    linarith
  have hd : HasDerivAt (fun t : ℝ => (b:ℂ) + (t:ℂ)*Complex.I - z) Complex.I x := by
    have h1 : HasDerivAt (fun t : ℝ => (t:ℂ) * Complex.I) (1 * Complex.I) x :=
      (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I
    simpa using h1.add_const ((b:ℂ) - z)
  simpa only [Function.comp_def, mul_comm] using (Complex.hasDerivAt_log hmem).comp x hd

private lemma hasDerivAt_log_vert_rot (z : ℂ) (a x : ℝ) (h : a < z.re) :
    HasDerivAt (fun t : ℝ => Complex.log (-Complex.I * ((a:ℂ) + (t:ℂ)*Complex.I - z)))
      (Complex.I * (((a:ℂ) + (x:ℂ)*Complex.I - z)⁻¹)) x := by
  have hmem : (-Complex.I * ((a:ℂ) + (x:ℂ)*Complex.I - z)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_not_le_zero]
    intro hle
    have him : (-Complex.I * ((a:ℂ) + (x:ℂ)*Complex.I - z)).im = z.re - a := by simp
    have := (Complex.le_def.1 hle).2
    rw [him] at this
    simp at this
    linarith
  have hd : HasDerivAt (fun t : ℝ => -Complex.I * ((a:ℂ) + (t:ℂ)*Complex.I - z)) 1 x := by
    have h1 : HasDerivAt (fun t : ℝ => (a:ℂ) + (t:ℂ)*Complex.I - z) Complex.I x := by
      have h2 : HasDerivAt (fun t : ℝ => (t:ℂ) * Complex.I) (1 * Complex.I) x :=
        (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I
      simpa using h2.add_const ((a:ℂ) - z)
    have h3 := h1.const_mul (-Complex.I)
    simpa using h3
  have hcomp := (Complex.hasDerivAt_log hmem).comp x hd
  have key : (-Complex.I * ((a:ℂ) + (x:ℂ)*Complex.I - z))⁻¹ * 1 =
      Complex.I * (((a:ℂ) + (x:ℂ)*Complex.I - z)⁻¹) := by
    rw [mul_one, mul_inv, inv_neg, Complex.inv_I]
    ring
  simpa only [Function.comp_def, key] using hcomp

private lemma integral_horiz (z : ℂ) (c : ℝ) (h : c ≠ z.im) (a b : ℝ) :
    ∫ x in a..b, (((x:ℂ) + (c:ℂ)*Complex.I - z)⁻¹)
      = Complex.log ((b:ℂ) + (c:ℂ)*Complex.I - z)
        - Complex.log ((a:ℂ) + (c:ℂ)*Complex.I - z) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_log_horiz z c x h) ?_
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.inv₀ ?_ ?_
  · fun_prop
  · intro x hx hzero
    have him0 : ((x:ℂ) + (c:ℂ)*Complex.I - z).im = 0 := by rw [hzero]; simp
    simp at him0
    exact h (sub_eq_zero.mp him0)

private lemma integral_vert (z : ℂ) (b : ℝ) (h : z.re < b) (c d : ℝ) :
    ∫ y in c..d, (((b:ℂ) + (y:ℂ)*Complex.I - z)⁻¹)
      = -Complex.I * (Complex.log ((b:ℂ) + (d:ℂ)*Complex.I - z)
        - Complex.log ((b:ℂ) + (c:ℂ)*Complex.I - z)) := by
  have hderiv : ∀ y ∈ Set.uIcc c d,
      HasDerivAt (fun t : ℝ => Complex.log ((b:ℂ) + (t:ℂ)*Complex.I - z))
        (Complex.I * (((b:ℂ) + (y:ℂ)*Complex.I - z)⁻¹)) y :=
    fun y hy => hasDerivAt_log_vert z b y h
  have hint : IntervalIntegrable
      (fun y : ℝ => Complex.I * (((b:ℂ) + (y:ℂ)*Complex.I - z)⁻¹)) volume c d := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ ?_ ?_
    · fun_prop
    · intro y hy h0
      have hre : ((b:ℂ) + (y:ℂ)*Complex.I - z).re = b - z.re := by simp
      rw [h0] at hre
      simp at hre
      linarith
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at h
  rw [← h, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

private lemma integral_vert_rot (z : ℂ) (a : ℝ) (h : a < z.re) (c d : ℝ) :
    ∫ y in c..d, (((a:ℂ) + (y:ℂ)*Complex.I - z)⁻¹)
      = -Complex.I * (Complex.log (-Complex.I * ((a:ℂ) + (d:ℂ)*Complex.I - z))
        - Complex.log (-Complex.I * ((a:ℂ) + (c:ℂ)*Complex.I - z))) := by
  have hderiv : ∀ y ∈ Set.uIcc c d,
      HasDerivAt (fun t : ℝ => Complex.log (-Complex.I * ((a:ℂ) + (t:ℂ)*Complex.I - z)))
        (Complex.I * (((a:ℂ) + (y:ℂ)*Complex.I - z)⁻¹)) y :=
    fun y hy => hasDerivAt_log_vert_rot z a y h
  have hint : IntervalIntegrable
      (fun y : ℝ => Complex.I * (((a:ℂ) + (y:ℂ)*Complex.I - z)⁻¹)) volume c d := by
    have hcont : ContinuousOn (fun y : ℝ => Complex.I * (((a:ℂ) + (y:ℂ)*Complex.I - z)⁻¹))
        (Set.uIcc c d) := by
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.inv₀ ?_ ?_
      · fun_prop
      · intro y hy h0
        have hre : ((a:ℂ) + (y:ℂ)*Complex.I - z).re = a - z.re := by simp
        rw [h0] at hre
        simp at hre
        linarith
    exact hcont.intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at h
  rw [← h, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

private theorem rectBdIntegral_inv_sub_eq {a b c d : ℝ} (z : ℂ) (ha : a < z.re) (hb : z.re < b)
    (hc : c < z.im) (hd : z.im < d) :
    Work.TMComp.Kotani.rectBdIntegral a b c d (fun w => (w - z)⁻¹)
      = 2 * (Real.pi : ℂ) * Complex.I := by
  have hmc : c ≠ z.im := ne_of_lt hc
  have hmd : d ≠ z.im := ne_of_gt hd
  have h1 := integral_horiz z c hmc a b
  have h2 := integral_horiz z d hmd a b
  have h3 := integral_vert z b hb c d
  have h4 := integral_vert_rot z a ha c d
  simp only [Work.TMComp.Kotani.rectBdIntegral]
  rw [h1, h2, h3, h4]
  simp only [I_mul_negI_mul]
  have hA : Complex.log ((a:ℂ) + (d:ℂ)*Complex.I - z)
      - Complex.log (-Complex.I * ((a:ℂ) + (d:ℂ)*Complex.I - z))
      = (Real.pi / 2 : ℂ) * Complex.I :=
    log_sub_log_negI_mul (by simp; linarith) (by simp; linarith)
  have hB : Complex.log (-Complex.I * ((a:ℂ) + (c:ℂ)*Complex.I - z))
      - Complex.log ((a:ℂ) + (c:ℂ)*Complex.I - z)
      = (3 * Real.pi / 2 : ℂ) * Complex.I :=
    log_negI_mul_sub_log (by simp; linarith) (by simp; linarith)
  have hsplit : (Complex.log ((b:ℂ) + (c:ℂ)*Complex.I - z)
        - Complex.log ((a:ℂ) + (c:ℂ)*Complex.I - z)
        - (Complex.log ((b:ℂ) + (d:ℂ)*Complex.I - z)
          - Complex.log ((a:ℂ) + (d:ℂ)*Complex.I - z))
        + (Complex.log ((b:ℂ) + (d:ℂ)*Complex.I - z)
          - Complex.log ((b:ℂ) + (c:ℂ)*Complex.I - z))
        - (Complex.log (-Complex.I * ((a:ℂ) + (d:ℂ)*Complex.I - z))
          - Complex.log (-Complex.I * ((a:ℂ) + (c:ℂ)*Complex.I - z))))
      = (Complex.log ((a:ℂ) + (d:ℂ)*Complex.I - z)
          - Complex.log (-Complex.I * ((a:ℂ) + (d:ℂ)*Complex.I - z)))
        + (Complex.log (-Complex.I * ((a:ℂ) + (c:ℂ)*Complex.I - z))
          - Complex.log ((a:ℂ) + (c:ℂ)*Complex.I - z)) := by
    ring
  rw [hsplit, hA, hB]
  ring

/-! ### Piece 1: the difference quotient has vanishing boundary integral -/

private theorem rectBdIntegral_dslope_eq_zero {a b c d : ℝ} {f : ℂ → ℂ} (z : ℂ)
    (ha : a < z.re) (hb : z.re < b) (hc : c < z.im) (hd : z.im < d)
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    Work.TMComp.Kotani.rectBdIntegral a b c d (dslope f z) = 0 := by
  have hab : a < b := ha.trans hb
  have hcd : c < d := hc.trans hd
  have hsub : Set.Ioo a b ×ℂ Set.Ioo c d ⊆ Set.uIcc a b ×ℂ Set.uIcc c d := by
    rw [Complex.reProdIm_subset_iff]
    exact Set.prod_mono (Set.Ioo_subset_Icc_self.trans Set.Icc_subset_uIcc)
      (Set.Ioo_subset_Icc_self.trans Set.Icc_subset_uIcc)
  have hRnhds : (Set.uIcc a b ×ℂ Set.uIcc c d) ∈ 𝓝 z := by
    refine Filter.mem_of_superset ?_ hsub
    exact (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds
      (by rw [Complex.mem_reProdIm]; exact ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩)
  have hcont : ContinuousOn (dslope f z) (Set.uIcc a b ×ℂ Set.uIcc c d) :=
    (continuousOn_dslope hRnhds).2 ⟨hf.continuousOn, hf.differentiableAt hRnhds⟩
  have hdiff : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ℂ Set.Ioo (min c d) (max c d) \ {z},
      DifferentiableAt ℂ (dslope f z) x := by
    intro x hx
    have hxmem : x ∈ Set.Ioo a b ×ℂ Set.Ioo c d := by
      simpa [min_eq_left hab.le, max_eq_right hab.le, min_eq_left hcd.le,
        max_eq_right hcd.le] using hx.1
    have hxne : x ≠ z := by simpa using hx.2
    have hnbd : (Set.Ioo a b ×ℂ Set.Ioo c d) ∈ 𝓝 x :=
      (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hxmem
    have hfx : DifferentiableAt ℂ f x := (hf.mono hsub).differentiableAt hnbd
    exact (differentiableAt_dslope_of_ne hxne).2 hfx
  have hcont' : ContinuousOn (dslope f z)
      (Set.uIcc (((a:ℂ) + (c:ℂ)*Complex.I).re) (((b:ℂ) + (d:ℂ)*Complex.I).re)
        ×ℂ Set.uIcc (((a:ℂ) + (c:ℂ)*Complex.I).im) (((b:ℂ) + (d:ℂ)*Complex.I).im)) := by
    simpa using hcont
  have hdiff' : ∀ x ∈ Set.Ioo (min (((a:ℂ) + (c:ℂ)*Complex.I).re) (((b:ℂ) + (d:ℂ)*Complex.I).re))
        (max (((a:ℂ) + (c:ℂ)*Complex.I).re) (((b:ℂ) + (d:ℂ)*Complex.I).re))
      ×ℂ Set.Ioo (min (((a:ℂ) + (c:ℂ)*Complex.I).im) (((b:ℂ) + (d:ℂ)*Complex.I).im))
        (max (((a:ℂ) + (c:ℂ)*Complex.I).im) (((b:ℂ) + (d:ℂ)*Complex.I).im)) \ {z},
      DifferentiableAt ℂ (dslope f z) x := by
    simpa using hdiff
  have hmain := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    (dslope f z) ((a:ℂ) + (c:ℂ)*Complex.I) ((b:ℂ) + (d:ℂ)*Complex.I) {z}
    (Set.countable_singleton z) hcont' hdiff' 
  simpa [Work.TMComp.Kotani.rectBdIntegral] using hmain

/-! ### Integrability of the edge restrictions of `(w - z)⁻¹ * u w` -/

private lemma continuousOn_inv_sub_mul_horiz {a b c d : ℝ} {u : ℂ → ℂ} {z : ℂ} {k : ℝ}
    (hu : ContinuousOn u (Set.uIcc a b ×ℂ Set.uIcc c d)) (hk : k ≠ z.im)
    (hkc : k ∈ Set.uIcc c d) :
    ContinuousOn (fun x : ℝ => ((x:ℂ) + (k:ℂ)*Complex.I - z)⁻¹
      * u ((x:ℂ) + (k:ℂ)*Complex.I)) (Set.uIcc a b) := by
  have h1 : ContinuousOn (fun x : ℝ => ((x:ℂ) + (k:ℂ)*Complex.I - z)⁻¹) (Set.uIcc a b) := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro x hx hzero
    have him0 : ((x:ℂ) + (k:ℂ)*Complex.I - z).im = 0 := by rw [hzero]; simp
    simp at him0
    exact hk (sub_eq_zero.mp him0)
  have h2 : ContinuousOn (fun x : ℝ => u ((x:ℂ) + (k:ℂ)*Complex.I)) (Set.uIcc a b) := by
    refine hu.comp (by fun_prop) ?_
    intro x hx
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using hx, by simpa using hkc⟩
  exact h1.mul h2

private lemma continuousOn_inv_sub_mul_vert {a b c d : ℝ} {u : ℂ → ℂ} {z : ℂ} {m : ℝ}
    (hu : ContinuousOn u (Set.uIcc a b ×ℂ Set.uIcc c d)) (hm : m ≠ z.re)
    (hma : m ∈ Set.uIcc a b) :
    ContinuousOn (fun y : ℝ => ((m:ℂ) + (y:ℂ)*Complex.I - z)⁻¹
      * u ((m:ℂ) + (y:ℂ)*Complex.I)) (Set.uIcc c d) := by
  have h1 : ContinuousOn (fun y : ℝ => ((m:ℂ) + (y:ℂ)*Complex.I - z)⁻¹) (Set.uIcc c d) := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro y hy hzero
    have hre0 : ((m:ℂ) + (y:ℂ)*Complex.I - z).re = 0 := by rw [hzero]; simp
    simp at hre0
    exact hm (sub_eq_zero.mp hre0)
  have h2 : ContinuousOn (fun y : ℝ => u ((m:ℂ) + (y:ℂ)*Complex.I)) (Set.uIcc c d) := by
    refine hu.comp (by fun_prop) ?_
    intro y hy
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using hma, by simpa using hy⟩
  exact h1.mul h2

private lemma intervalIntegrable_four_edges {a b c d : ℝ} {u : ℂ → ℂ} {z : ℂ}
    (hu : ContinuousOn u (Set.uIcc a b ×ℂ Set.uIcc c d))
    (ha : a ≠ z.re) (hb : b ≠ z.re) (hc : c ≠ z.im) (hd : d ≠ z.im) :
    IntervalIntegrable (fun x : ℝ => ((x:ℂ) + (c:ℂ)*Complex.I - z)⁻¹
        * u ((x:ℂ) + (c:ℂ)*Complex.I)) volume a b ∧
    IntervalIntegrable (fun x : ℝ => ((x:ℂ) + (d:ℂ)*Complex.I - z)⁻¹
        * u ((x:ℂ) + (d:ℂ)*Complex.I)) volume a b ∧
    IntervalIntegrable (fun y : ℝ => ((b:ℂ) + (y:ℂ)*Complex.I - z)⁻¹
        * u ((b:ℂ) + (y:ℂ)*Complex.I)) volume c d ∧
    IntervalIntegrable (fun y : ℝ => ((a:ℂ) + (y:ℂ)*Complex.I - z)⁻¹
        * u ((a:ℂ) + (y:ℂ)*Complex.I)) volume c d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (continuousOn_inv_sub_mul_horiz hu hc (by simp)).intervalIntegrable
  · exact (continuousOn_inv_sub_mul_horiz hu hd (by simp)).intervalIntegrable
  · exact (continuousOn_inv_sub_mul_vert hu hb (by simp)).intervalIntegrable
  · exact (continuousOn_inv_sub_mul_vert hu ha (by simp)).intervalIntegrable

/-! ### The Cauchy integral formula on a rectangle -/

theorem rectBdIntegral_cauchy {a b c d : ℝ} {f : ℂ → ℂ} (z : ℂ) (ha : a < z.re)
    (hb : z.re < b) (hc : c < z.im) (hd : z.im < d)
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    Work.TMComp.Kotani.rectBdIntegral a b c d (fun w => (w - z)⁻¹ * f w)
      = 2 * (Real.pi : ℂ) * Complex.I * f z := by
  have hsz : (fun w : ℂ => f w - f z) = fun w => f w - f z := rfl
  have huf : ContinuousOn (fun w : ℂ => f w - f z) (Set.uIcc a b ×ℂ Set.uIcc c d) :=
    hf.continuousOn.sub continuousOn_const
  have huc : ContinuousOn (fun _ : ℂ => f z) (Set.uIcc a b ×ℂ Set.uIcc c d) :=
    continuousOn_const
  obtain ⟨fp1, fp2, fp3, fp4⟩ :=
    intervalIntegrable_four_edges huf (ne_of_lt ha) (ne_of_gt hb) (ne_of_lt hc) (ne_of_gt hd)
  obtain ⟨gp1, gp2, gp3, gp4⟩ :=
    intervalIntegrable_four_edges huc (ne_of_lt ha) (ne_of_gt hb) (ne_of_lt hc) (ne_of_gt hd)
  have hadd : Work.TMComp.Kotani.rectBdIntegral a b c d (fun w => (w - z)⁻¹ * f w)
      = Work.TMComp.Kotani.rectBdIntegral a b c d (fun w => (w - z)⁻¹ * (f w - f z))
        + Work.TMComp.Kotani.rectBdIntegral a b c d (fun w => (w - z)⁻¹ * f z) := by
    rw [← Work.TMComp.Kotani.rectBdIntegral_add a b c d
      (fun w => (w - z)⁻¹ * (f w - f z)) (fun w => (w - z)⁻¹ * f z)
      fp1 gp1 fp2 gp2 fp3 gp3 fp4 gp4]
    exact Work.TMComp.Kotani.rectBdIntegral_congr (fun w => by ring)
  have hG : Work.TMComp.Kotani.rectBdIntegral a b c d (fun w => (w - z)⁻¹ * (f w - f z))
      = 0 := by
    have hkey : ∀ w : ℂ, w ≠ z → dslope f z w = (w - z)⁻¹ * (f w - f z) := by
      intro w hw
      rw [dslope_of_ne f hw, slope]
      simp [smul_eq_mul]
    have hne_c : ∀ x : ℝ, ((x:ℂ) + (c:ℂ)*Complex.I) ≠ z := by
      intro x hxz
      have him0 : (((x:ℂ) + (c:ℂ)*Complex.I).im) = z.im := by rw [hxz]
      simp at him0
      exact (ne_of_lt hc) him0
    have hne_d : ∀ x : ℝ, ((x:ℂ) + (d:ℂ)*Complex.I) ≠ z := by
      intro x hxz
      have him0 : (((x:ℂ) + (d:ℂ)*Complex.I).im) = z.im := by rw [hxz]
      simp at him0
      exact (ne_of_gt hd) him0
    have hne_b : ∀ y : ℝ, ((b:ℂ) + (y:ℂ)*Complex.I) ≠ z := by
      intro y hyz
      have hre0 : (((b:ℂ) + (y:ℂ)*Complex.I).re) = z.re := by rw [hyz]
      simp at hre0
      exact (ne_of_gt hb) hre0
    have hne_a : ∀ y : ℝ, ((a:ℂ) + (y:ℂ)*Complex.I) ≠ z := by
      intro y hyz
      have hre0 : (((a:ℂ) + (y:ℂ)*Complex.I).re) = z.re := by rw [hyz]
      simp at hre0
      exact (ne_of_lt ha) hre0
    have e1 : (∫ x : ℝ in a..b, dslope f z ((x:ℂ) + (c:ℂ)*Complex.I))
        = ∫ x : ℝ in a..b, ((x:ℂ) + (c:ℂ)*Complex.I - z)⁻¹
            * (f ((x:ℂ) + (c:ℂ)*Complex.I) - f z) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      exact hkey _ (hne_c x)
    have e2 : (∫ x : ℝ in a..b, dslope f z ((x:ℂ) + (d:ℂ)*Complex.I))
        = ∫ x : ℝ in a..b, ((x:ℂ) + (d:ℂ)*Complex.I - z)⁻¹
            * (f ((x:ℂ) + (d:ℂ)*Complex.I) - f z) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      exact hkey _ (hne_d x)
    have e3 : (∫ y : ℝ in c..d, dslope f z ((b:ℂ) + (y:ℂ)*Complex.I))
        = ∫ y : ℝ in c..d, ((b:ℂ) + (y:ℂ)*Complex.I - z)⁻¹
            * (f ((b:ℂ) + (y:ℂ)*Complex.I) - f z) := by
      refine intervalIntegral.integral_congr ?_
      intro y hy
      exact hkey _ (hne_b y)
    have e4 : (∫ y : ℝ in c..d, dslope f z ((a:ℂ) + (y:ℂ)*Complex.I))
        = ∫ y : ℝ in c..d, ((a:ℂ) + (y:ℂ)*Complex.I - z)⁻¹
            * (f ((a:ℂ) + (y:ℂ)*Complex.I) - f z) := by
      refine intervalIntegral.integral_congr ?_
      intro y hy
      exact hkey _ (hne_a y)
    have hcongr : Work.TMComp.Kotani.rectBdIntegral a b c d (dslope f z)
        = Work.TMComp.Kotani.rectBdIntegral a b c d (fun w => (w - z)⁻¹ * (f w - f z)) := by
      simp only [Work.TMComp.Kotani.rectBdIntegral]
      rw [e1, e2, e3, e4]
    rw [← hcongr, rectBdIntegral_dslope_eq_zero z ha hb hc hd hf]
  have hH : Work.TMComp.Kotani.rectBdIntegral a b c d (fun w => (w - z)⁻¹ * f z)
      = f z * (2 * (Real.pi : ℂ) * Complex.I) := by
    have hcongr : Work.TMComp.Kotani.rectBdIntegral a b c d (fun w => (w - z)⁻¹ * f z)
        = Work.TMComp.Kotani.rectBdIntegral a b c d (fun w => f z * (w - z)⁻¹) :=
      Work.TMComp.Kotani.rectBdIntegral_congr (fun w => by ring)
    rw [hcongr, Work.TMComp.Kotani.rectBdIntegral_const_mul,
      rectBdIntegral_inv_sub_eq z ha hb hc hd]
  rw [hadd, hG, hH]
  ring


end

end Work.TMComp.RedC8
