import Mathlib
import Submission.Work.Asymptotics.rectangle_winding

namespace Work.Asymptotics

open Complex MeasureTheory intervalIntegral Filter Topology

/-- The closed axis-parallel rectangle with corners `(x₁, y₁)` and `(x₂, y₂)`. -/
private def rect (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ :=
  {z : ℂ | x₁ ≤ z.re ∧ z.re ≤ x₂ ∧ y₁ ≤ z.im ∧ z.im ≤ y₂}

/-- The rectangle is the product of its real and imaginary projections. -/
private lemma rect_eq_reProdIm (x₁ x₂ y₁ y₂ : ℝ) (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    Set.uIcc x₁ x₂ ×ℂ Set.uIcc y₁ y₂ = rect x₁ x₂ y₁ y₂ := by
  rw [Set.uIcc_of_le hx, Set.uIcc_of_le hy]
  ext z
  simp only [rect, Complex.mem_reProdIm, Set.mem_Icc, Set.mem_ofPred_eq]
  tauto

/-- **Residue theorem for a rectangle.**  Let `f` be continuous on a closed rectangle except at a
single interior point `z₀`, holomorphic on the open rectangle except at `z₀`, and suppose that
`f z - c / (z - z₀)` extends holomorphically to `z₀` (so `f` has at most a simple pole of residue
`c` at `z₀`).  Then the counterclockwise boundary integral of `f` over the rectangle equals
`2 π i c`. -/
theorem residue_rectangle (f : ℂ → ℂ) (z₀ c : ℂ) (x₁ x₂ y₁ y₂ : ℝ)
    (hx₁ : x₁ < z₀.re) (hx₂ : z₀.re < x₂) (hy₁ : y₁ < z₀.im) (hy₂ : z₀.im < y₂)
    (hcont : ContinuousOn f ({z : ℂ | x₁ ≤ z.re ∧ z.re ≤ x₂ ∧ y₁ ≤ z.im ∧ z.im ≤ y₂} \ {z₀}))
    (hhol : ∀ z : ℂ, x₁ < z.re → z.re < x₂ → y₁ < z.im → z.im < y₂ → z ≠ z₀ →
      DifferentiableAt ℂ f z)
    (hrem : DifferentiableAt ℂ (fun z => f z - c / (z - z₀)) z₀) :
    (∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I))
      - (∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₂ : ℂ) * Complex.I))
      + Complex.I * (∫ y : ℝ in y₁..y₂, f ((x₂ : ℂ) + (y : ℂ) * Complex.I))
      - Complex.I * (∫ y : ℝ in y₁..y₂, f ((x₁ : ℂ) + (y : ℂ) * Complex.I))
      = 2 * (Real.pi : ℂ) * Complex.I * c := by
  have hcont' : ContinuousOn f (rect x₁ x₂ y₁ y₂ \ {z₀}) := hcont
  -- `g` is the holomorphic part of `f`, `h` the singular part `(z - z₀)⁻¹`.
  set g : ℂ → ℂ := fun z => f z - c / (z - z₀) with hgdef
  set h : ℂ → ℂ := fun z => (z - z₀)⁻¹ with hhdef
  have hx12 : x₁ ≤ x₂ := le_of_lt (lt_trans hx₁ hx₂)
  have hy12 : y₁ ≤ y₂ := le_of_lt (lt_trans hy₁ hy₂)
  have hrem' : DifferentiableAt ℂ g z₀ := by rw [hgdef]; exact hrem
  -- `g` is continuous on the closed rectangle.
  have hgc : ContinuousOn g (rect x₁ x₂ y₁ y₂) := by
    intro z hz
    rcases eq_or_ne z z₀ with rfl | hne
    · exact hrem'.continuousAt.continuousWithinAt
    · have hmem : ({z₀}ᶜ : Set ℂ) ∈ 𝓝 z :=
        isOpen_compl_singleton.mem_nhds (by simpa using hne)
      have hmem' : rect x₁ x₂ y₁ y₂ \ {z₀} ∈ 𝓝[rect x₁ x₂ y₁ y₂] z := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨{z₀}ᶜ, hmem, fun x hx => ⟨hx.2, hx.1⟩⟩
      have h1 : ContinuousWithinAt f (rect x₁ x₂ y₁ y₂ \ {z₀}) z :=
        hcont'.continuousWithinAt ⟨hz, hne⟩
      have h2 : ContinuousWithinAt f (rect x₁ x₂ y₁ y₂) z :=
        h1.mono_of_mem_nhdsWithin hmem'
      have h3 : ContinuousWithinAt (fun z => c / (z - z₀)) (rect x₁ x₂ y₁ y₂) z :=
        (continuousAt_const.div (continuousAt_id.sub_const z₀)
          (sub_ne_zero.mpr hne)).continuousWithinAt
      rw [hgdef]
      exact h2.sub h3
  have hfg : ∀ z : ℂ, f z = g z + c * h z := by
    intro z
    rw [hgdef, hhdef]
    simp only [div_eq_mul_inv]
    ring
  -- On each edge of the rectangle the integral of `f` splits into the integrals of `g` and `h`.
  have split_seg : ∀ {a b : ℝ} (φ : ℝ → ℂ), Continuous φ →
      Set.MapsTo φ (Set.uIcc a b) (rect x₁ x₂ y₁ y₂) → Continuous (fun t => h (φ t)) →
      (∫ t in a..b, f (φ t)) = (∫ t in a..b, g (φ t)) + c * (∫ t in a..b, h (φ t)) := by
    intro a b φ hφc hφR hφh
    have hcomp : ContinuousOn (fun t => g (φ t)) (Set.uIcc a b) := hgc.comp' hφc.continuousOn hφR
    have hgint : IntervalIntegrable (fun t => g (φ t)) volume a b := hcomp.intervalIntegrable
    have hhint : IntervalIntegrable (fun t => c * h (φ t)) volume a b :=
      (hφh.const_mul c).intervalIntegrable a b
    rw [intervalIntegral.integral_congr (fun t _ => hfg (φ t)),
      intervalIntegral.integral_add hgint hhint, intervalIntegral.integral_const_mul]
  -- The edges avoid `z₀` in one of the two coordinate directions.
  have him_b : ∀ x : ℝ, (((x:ℂ) + (y₁:ℂ)*I) - z₀).im = y₁ - z₀.im := by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.mul_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  have him_t : ∀ x : ℝ, (((x:ℂ) + (y₂:ℂ)*I) - z₀).im = y₂ - z₀.im := by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.mul_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  have hre_r : ∀ y : ℝ, (((x₂:ℂ) + (y:ℂ)*I) - z₀).re = x₂ - z₀.re := by
    intro y; simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, mul_one, mul_zero]; ring
  have hre_l : ∀ y : ℝ, (((x₁:ℂ) + (y:ℂ)*I) - z₀).re = x₁ - z₀.re := by
    intro y; simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, mul_one, mul_zero]; ring
  have e_b : (∫ x in x₁..x₂, f ((x:ℂ) + (y₁:ℂ)*I))
      = (∫ x in x₁..x₂, g ((x:ℂ) + (y₁:ℂ)*I)) + c * (∫ x in x₁..x₂, h ((x:ℂ) + (y₁:ℂ)*I)) := by
    refine split_seg (a := x₁) (b := x₂) (φ := fun x : ℝ => (x:ℂ) + (y₁:ℂ)*I) (by fun_prop) ?_ ?_
    · intro x hx
      rw [Set.uIcc_of_le hx12, Set.mem_Icc] at hx
      simp only [rect, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, add_zero, zero_add, sub_zero]
      exact ⟨hx.1, hx.2, le_rfl, hy12⟩
    · rw [hhdef]
      refine Continuous.inv₀ ?_ ?_
      · fun_prop
      · intro x hne
        have h0 : (((x:ℂ) + (y₁:ℂ)*I) - z₀).im = 0 := by rw [hne, Complex.zero_im]
        rw [him_b x] at h0; linarith
  have e_t : (∫ x in x₁..x₂, f ((x:ℂ) + (y₂:ℂ)*I))
      = (∫ x in x₁..x₂, g ((x:ℂ) + (y₂:ℂ)*I)) + c * (∫ x in x₁..x₂, h ((x:ℂ) + (y₂:ℂ)*I)) := by
    refine split_seg (a := x₁) (b := x₂) (φ := fun x : ℝ => (x:ℂ) + (y₂:ℂ)*I) (by fun_prop) ?_ ?_
    · intro x hx
      rw [Set.uIcc_of_le hx12, Set.mem_Icc] at hx
      simp only [rect, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, add_zero, zero_add, sub_zero]
      exact ⟨hx.1, hx.2, hy12, le_rfl⟩
    · rw [hhdef]
      refine Continuous.inv₀ ?_ ?_
      · fun_prop
      · intro x hne
        have h0 : (((x:ℂ) + (y₂:ℂ)*I) - z₀).im = 0 := by rw [hne, Complex.zero_im]
        rw [him_t x] at h0; linarith
  have e_r : (∫ y in y₁..y₂, f ((x₂:ℂ) + (y:ℂ)*I))
      = (∫ y in y₁..y₂, g ((x₂:ℂ) + (y:ℂ)*I)) + c * (∫ y in y₁..y₂, h ((x₂:ℂ) + (y:ℂ)*I)) := by
    refine split_seg (a := y₁) (b := y₂) (φ := fun y : ℝ => (x₂:ℂ) + (y:ℂ)*I) (by fun_prop) ?_ ?_
    · intro y hy
      rw [Set.uIcc_of_le hy12, Set.mem_Icc] at hy
      simp only [rect, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, add_zero, zero_add, sub_zero]
      exact ⟨hx12, le_rfl, hy.1, hy.2⟩
    · rw [hhdef]
      refine Continuous.inv₀ ?_ ?_
      · fun_prop
      · intro y hne
        have h0 : (((x₂:ℂ) + (y:ℂ)*I) - z₀).re = 0 := by rw [hne, Complex.zero_re]
        rw [hre_r y] at h0; linarith
  have e_l : (∫ y in y₁..y₂, f ((x₁:ℂ) + (y:ℂ)*I))
      = (∫ y in y₁..y₂, g ((x₁:ℂ) + (y:ℂ)*I)) + c * (∫ y in y₁..y₂, h ((x₁:ℂ) + (y:ℂ)*I)) := by
    refine split_seg (a := y₁) (b := y₂) (φ := fun y : ℝ => (x₁:ℂ) + (y:ℂ)*I) (by fun_prop) ?_ ?_
    · intro y hy
      rw [Set.uIcc_of_le hy12, Set.mem_Icc] at hy
      simp only [rect, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, add_zero, zero_add, sub_zero]
      exact ⟨le_rfl, hx12, hy.1, hy.2⟩
    · rw [hhdef]
      refine Continuous.inv₀ ?_ ?_
      · fun_prop
      · intro y hne
        have h0 : (((x₁:ℂ) + (y:ℂ)*I) - z₀).re = 0 := by rw [hne, Complex.zero_re]
        rw [hre_l y] at h0; linarith
  -- Cauchy–Goursat for the holomorphic part `g` (its removable singularity has been filled in).
  have hG : (∫ x in x₁..x₂, g ((x:ℂ) + (y₁:ℂ)*I)) - (∫ x in x₁..x₂, g ((x:ℂ) + (y₂:ℂ)*I))
      + I * (∫ y in y₁..y₂, g ((x₂:ℂ) + (y:ℂ)*I)) - I * (∫ y in y₁..y₂, g ((x₁:ℂ) + (y:ℂ)*I)) = 0 := by
    have key := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable g
      ((x₁:ℂ) + (y₁:ℂ)*I) ((x₂:ℂ) + (y₂:ℂ)*I) ∅ Set.countable_empty
      (by
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
          add_zero, zero_add, sub_zero]
        rw [rect_eq_reProdIm x₁ x₂ y₁ y₂ hx12 hy12]
        exact hgc)
      (by
        intro z hz
        simp only [Set.sdiff_empty, Complex.mem_reProdIm, Set.mem_Ioo] at hz
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
          add_zero, zero_add, sub_zero] at hz
        rw [min_eq_left hx12, max_eq_right hx12, min_eq_left hy12, max_eq_right hy12] at hz
        rcases eq_or_ne z z₀ with rfl | hne
        · exact hrem'
        · have hf : DifferentiableAt ℂ f z := hhol z hz.1.1 hz.1.2 hz.2.1 hz.2.2 hne
          have hdiv : DifferentiableAt ℂ (fun w => c / (w - z₀)) z := by
            have h1 : DifferentiableAt ℂ (fun w : ℂ => (w - z₀)⁻¹) z :=
              (differentiableAt_id.sub_const z₀).inv (sub_ne_zero.mpr hne)
            simpa only [div_eq_mul_inv] using h1.const_mul c
          rw [hgdef]
          exact hf.sub hdiv)
    simpa [smul_eq_mul] using key
  -- The boundary integral of the singular part is the winding number `2 π i`.
  have hH : (∫ x in x₁..x₂, h ((x:ℂ) + (y₁:ℂ)*I)) - (∫ x in x₁..x₂, h ((x:ℂ) + (y₂:ℂ)*I))
      + I * (∫ y in y₁..y₂, h ((x₂:ℂ) + (y:ℂ)*I)) - I * (∫ y in y₁..y₂, h ((x₁:ℂ) + (y:ℂ)*I))
      = 2 * (Real.pi : ℂ) * I := by
    simp only [hhdef]
    exact rectangle_winding z₀ x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂
  have hsplit : (∫ x in x₁..x₂, f ((x:ℂ) + (y₁:ℂ)*I)) - (∫ x in x₁..x₂, f ((x:ℂ) + (y₂:ℂ)*I))
      + I * (∫ y in y₁..y₂, f ((x₂:ℂ) + (y:ℂ)*I)) - I * (∫ y in y₁..y₂, f ((x₁:ℂ) + (y:ℂ)*I))
      = ((∫ x in x₁..x₂, g ((x:ℂ) + (y₁:ℂ)*I)) - (∫ x in x₁..x₂, g ((x:ℂ) + (y₂:ℂ)*I))
          + I * (∫ y in y₁..y₂, g ((x₂:ℂ) + (y:ℂ)*I)) - I * (∫ y in y₁..y₂, g ((x₁:ℂ) + (y:ℂ)*I)))
        + c * ((∫ x in x₁..x₂, h ((x:ℂ) + (y₁:ℂ)*I)) - (∫ x in x₁..x₂, h ((x:ℂ) + (y₂:ℂ)*I))
          + I * (∫ y in y₁..y₂, h ((x₂:ℂ) + (y:ℂ)*I)) - I * (∫ y in y₁..y₂, h ((x₁:ℂ) + (y:ℂ)*I))) := by
    rw [e_b, e_t, e_r, e_l]; ring
  rw [hsplit, hG, hH]; ring

end Work.Asymptotics
