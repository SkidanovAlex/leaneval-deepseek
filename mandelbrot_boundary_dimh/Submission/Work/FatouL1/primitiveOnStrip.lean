import Mathlib

/-!
# FATOU-L1: primitives of holomorphic functions on a vertical strip

Mathlib has Morera's theorem on disks (`DifferentiableOn.isExactOn_ball`) but not on
simply connected domains.  Here we prove the case needed by the FATOU-L1 area: a holomorphic
function on an open vertical strip `{z | a < Re z < b}` has a primitive.

The primitive is the classical "wedge integral" `z ↦ wedgeIntegral p z f` from a base point
`p` in the strip.  The key point is that the strip is *axis-parallel rectangle convex*: the
rectangle `Rectangle (z.re + c.im * I) (w.re + z.im * I)` used in Mathlib's proof of the
additivity of the wedge integral lies in the strip as soon as `z` and `w` do (the strip
constrains only the real part).  Hence the wedge integral is path independent, and the
derivative computation of `IsConservativeOn.hasDerivAt_wedgeIntegral` applies.
-/

namespace Work.FatouL1

open Complex MeasureTheory Metric Set
open scoped Topology Interval

noncomputable section

variable {α β : ℝ} {f : ℂ → ℂ}

/-- The open vertical strip `{z : ℂ | α < z.re ∧ z.re < β}`. -/
def strip (α β : ℝ) : Set ℂ := {z : ℂ | α < z.re ∧ z.re < β}

@[simp] lemma mem_strip {z : ℂ} : z ∈ strip α β ↔ α < z.re ∧ z.re < β := Iff.rfl

lemma strip_isOpen : IsOpen (strip α β) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- If `x` and `y` are in the open interval `(α,β)`, so is the whole unordered interval. -/
lemma uIcc_subset_of_mem_Ioo {x y : ℝ} (hx : x ∈ Ioo α β) (hy : y ∈ Ioo α β) :
    [[x, y]] ⊆ Ioo α β := by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h]; exact Icc_subset_Ioo hx.1 hy.2
  · rw [uIcc_of_ge h]; exact Icc_subset_Ioo hy.1 hx.2

/-- An axis-parallel rectangle lies in the strip as soon as its two defining corners do. -/
lemma rectangle_subset_strip {z w : ℂ} (hz : z ∈ strip α β) (hw : w ∈ strip α β) :
    Rectangle z w ⊆ strip α β := by
  intro ζ hζ
  simp only [Complex.Rectangle, Complex.mem_reProdIm] at hζ
  exact uIcc_subset_of_mem_Ioo hz hw hζ.1

/-- **Path independence of the wedge integral on a strip.**  For `f` holomorphic on the strip and
`c, z, w` in the strip, going from `c` to `w` directly (as a horizontal followed by a vertical
segment) agrees with going through `z`; equivalently the wedge integral from `z` to `w` is the
difference of the wedge integrals from `c`. -/
lemma wedgeIntegral_sub_eq_of_strip (hf : DifferentiableOn ℂ f (strip α β))
    {c z w : ℂ} (hc : c ∈ strip α β) (hz : z ∈ strip α β) (hw : w ∈ strip α β) :
    wedgeIntegral c w f - wedgeIntegral c z f = wedgeIntegral z w f := by
  have hcont : ContinuousOn f (strip α β) := hf.continuousOn
  have hcons : IsConservativeOn f (strip α β) := hf.isConservativeOn
  have mapsH (a₁ a₂ b : ℝ) (h₁ : (a₁ : ℂ) + b * I ∈ strip α β)
      (h₂ : (a₂ : ℂ) + b * I ∈ strip α β) :
      MapsTo (fun x : ℝ => (x : ℂ) + b * I) [[a₁, a₂]] (strip α β) := by
    intro x hx
    have h₁' : a₁ ∈ Ioo α β := by simpa [mem_strip] using h₁
    have h₂' : a₂ ∈ Ioo α β := by simpa [mem_strip] using h₂
    simpa [mem_strip] using uIcc_subset_of_mem_Ioo h₁' h₂' hx
  have mapsV (a b₁ b₂ : ℝ) (h₁ : (a : ℂ) + b₁ * I ∈ strip α β)
      (h₂ : (a : ℂ) + b₂ * I ∈ strip α β) :
      MapsTo (fun y : ℝ => (a : ℂ) + y * I) [[b₁, b₂]] (strip α β) := by
    intro y hy
    simpa [mem_strip] using h₁
  have integrableHoriz (a₁ a₂ b : ℝ) (h₁ : (a₁ : ℂ) + b * I ∈ strip α β)
      (h₂ : (a₂ : ℂ) + b * I ∈ strip α β) :
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + b * I)) volume a₁ a₂ :=
    (hcont.comp (by fun_prop) (mapsH a₁ a₂ b h₁ h₂)).intervalIntegrable
  have integrableVert (a b₁ b₂ : ℝ) (h₁ : (a : ℂ) + b₁ * I ∈ strip α β)
      (h₂ : (a : ℂ) + b₂ * I ∈ strip α β) :
      IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + y * I)) volume b₁ b₂ :=
    (hcont.comp (by fun_prop) (mapsV a b₁ b₂ h₁ h₂)).intervalIntegrable
  have hI₁ : (∫ x in c.re..w.re, f (x + c.im * I))
      = (∫ x in c.re..z.re, f (x + c.im * I)) + (∫ x in z.re..w.re, f (x + c.im * I)) := by
    rw [intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableHoriz
    · simpa using hc
    · simpa [mem_strip] using hz
    · simpa [mem_strip] using hz
    · simpa [mem_strip] using hw
  have hI₂ : I • (∫ y in c.im..w.im, f (w.re + y * I))
      = I • (∫ y in c.im..z.im, f (w.re + y * I))
        + I • (∫ y in z.im..w.im, f (w.re + y * I)) := by
    rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableVert
    · simpa [mem_strip] using hw
    · simpa [mem_strip] using hw
    · simpa [mem_strip] using hw
    · simpa using hw
  have hI₀ : (∫ x in z.re..w.re, f (x + c.im * I)) - (∫ x in z.re..w.re, f (x + z.im * I))
      + I • (∫ y in c.im..z.im, f (w.re + y * I))
      - I • (∫ y in c.im..z.im, f (z.re + y * I)) = 0 := by
    have hU : Rectangle (z.re + c.im * I) (w.re + z.im * I) ⊆ strip α β :=
      rectangle_subset_strip (by simpa [mem_strip] using hz) (by simpa [mem_strip] using hw)
    have h1 : wedgeIntegral (z.re + c.im * I) (w.re + z.im * I) f
        = - wedgeIntegral (w.re + z.im * I) (z.re + c.im * I) f :=
      hcons _ _ hU
    have h2 := wedgeIntegral_add_wedgeIntegral_eq (z.re + c.im * I) (w.re + z.im * I) f
    rw [h1, neg_add_cancel] at h2
    simpa using h2.symm
  simp only [wedgeIntegral]
  grind

/-- A holomorphic function on an open vertical strip has a primitive. -/
theorem primitiveOnStrip {a b : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | a < z.re ∧ z.re < b}) :
    Complex.IsExactOn f {z : ℂ | a < z.re ∧ z.re < b} := by
  show IsExactOn f (strip a b)
  by_cases hne : (strip a b).Nonempty
  · obtain ⟨p, hp⟩ := hne
    refine ⟨fun z => wedgeIntegral p z f, fun z hz => ?_⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp strip_isOpen z hz
    have hderiv : HasDerivAt (fun w => wedgeIntegral z w f) (f z) z :=
      Complex.IsConservativeOn.hasDerivAt_wedgeIntegral
        (hf.continuousOn.mono hball) (mem_ball_self hr) (hf.mono hball).isConservativeOn
    have hev : (fun w => wedgeIntegral p w f) =ᶠ[𝓝 z]
        (fun w => wedgeIntegral z w f + wedgeIntegral p z f) := by
      filter_upwards [strip_isOpen.mem_nhds hz] with w hw
      exact sub_eq_iff_eq_add.mp (wedgeIntegral_sub_eq_of_strip hf hp hz hw)
    exact (hderiv.add_const (wedgeIntegral p z f)).congr_of_eventuallyEq hev
  · exact ⟨fun _ => 0, fun z hz => (hne ⟨z, hz⟩).elim⟩

end

end Work.FatouL1
