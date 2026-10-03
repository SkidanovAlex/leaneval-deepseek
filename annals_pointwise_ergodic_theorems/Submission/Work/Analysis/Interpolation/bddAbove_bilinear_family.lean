import Mathlib
import Submission.Work.Analysis.Interpolation.Basic

namespace Work.Analysis.Interpolation

open MeasureTheory
open scoped ENNReal NNReal

/-!
# Boundedness of a bilinear form along the analytic families of simple functions

Let `Λ` be any (merely) bilinear complex-valued form on functions on `α` and `β`, and let
`f : SimpleFunc α ℂ`, `g : SimpleFunc β ℂ` be simple.  Write

`F z = analyticFamily f a₀ a₁ z`, `G z = analyticFamily g b₀ b₁ z`

for the analytic families attached to `f`, `g` with *real* endpoint exponents `a₀, a₁`, resp.
`b₀, b₁`.  The main result of this file is

`bddAbove_bilinear_family`:

if the value `Λ (F z) (G z)` is the finite sum over the level sets of `f` and `g` with the
`z`-dependent coefficients `phasePow c (expFamily a₀ a₁ z) * phasePow d (expFamily b₀ b₁ z)`
(hypothesis `hΛ`), then the function
`z ↦ ‖Λ (F z) (G z)‖` is bounded above on the closed vertical strip `0 ≤ re z ≤ 1`.

This is the "boundedness on the strip" input of Hadamard's three-lines theorem
(`Complex.HadamardThreeLines.norm_le_sSupNormIm`), needed when the three-lines argument is
applied to an arbitrary (merely) bilinear form rather than a linear map.

The proof is quantitative.  On the strip `0 ≤ x ≤ 1` the exponent
`(expFamily a₀ a₁ z).re = (1 - x) * a₀ + x * a₁` is the convex combination of `a₀` and `a₁`
with weights `1 - x, x`, hence lies between `min a₀ a₁` and `max a₀ a₁`; consequently, for
`c ≠ 0`, `‖phasePow c (expFamily a₀ a₁ z)‖ = ‖c‖ ^ (expFamily a₀ a₁ z).re` is bounded by
`max 1 (max (‖c‖ ^ a₀) (‖c‖ ^ a₁))` (monotonicity of `ρ ↦ ρ ^ s`, in the two regimes
`1 ≤ ρ` and `ρ ≤ 1`).  Feeding these bounds through the finite double sum and the triangle
inequality gives a bound which is a *constant* (a finite sum of constants).

## Main results

* `expFamily_re_mem_Icc_of_mem`: the real part of the exponent on the strip;
* `rpow_le_max_one_of_mem_Icc`: `ρ ^ s ≤ max 1 (max (ρ ^ a₀) (ρ ^ a₁))` for `s` between the
  endpoints;
* `norm_phasePow_expFamily_le_of_re_mem`: the pointwise bound of `norm ∘ phasePow ∘ expFamily`;
* `bddAbove_image_norm_of_le`, `norm_double_sum_le`: elementary "boundedness from a pointwise
  bound" and triangle-inequality tool lemmas;
* `bddAbove_bilinear_family`: the target.
-/

/-- On the closed vertical strip `0 ≤ re z ≤ 1`, the real part of the affine exponent family
`expFamily a₀ a₁ z = (1 - z) * a₀ + z * a₁` (with real exponents `a₀`, `a₁`) is the convex
combination `(1 - z.re) * a₀ + z.re * a₁`, hence lies between `min a₀ a₁` and `max a₀ a₁`. -/
lemma expFamily_re_mem_Icc_of_mem {a₀ a₁ : ℝ} {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    (expFamily (a₀ : ℂ) (a₁ : ℂ) z).re ∈ Set.Icc (min a₀ a₁) (max a₀ a₁) := by
  have hx1 : 0 ≤ 1 - z.re := by linarith [hz.1, hz.2]
  rw [expFamily_ofReal_re]
  constructor
  · have hid : (1 - z.re) * min a₀ a₁ + z.re * min a₀ a₁ = min a₀ a₁ := by ring
    have h := add_le_add (mul_le_mul_of_nonneg_left (min_le_left a₀ a₁) hx1)
      (mul_le_mul_of_nonneg_left (min_le_right a₀ a₁) hz.1)
    rw [hid] at h
    exact h
  · have hid : (1 - z.re) * max a₀ a₁ + z.re * max a₀ a₁ = max a₀ a₁ := by ring
    have h := add_le_add (mul_le_mul_of_nonneg_left (le_max_left a₀ a₁) hx1)
      (mul_le_mul_of_nonneg_left (le_max_right a₀ a₁) hz.1)
    exact le_trans h hid.le

/-- For a positive base `ρ` and an exponent `s` lying between `a₀` and `a₁`, the power `ρ ^ s`
is bounded by `max 1 (max (ρ ^ a₀) (ρ ^ a₁))`.

Since `ρ ^ ·` is increasing when `1 ≤ ρ` and decreasing when `ρ ≤ 1`, the value at the interior
point `s` is bounded by the value at the endpoint `max a₀ a₁`, resp. `min a₀ a₁`. -/
lemma rpow_le_max_one_of_mem_Icc {ρ a₀ a₁ s : ℝ} (hρ : 0 < ρ)
    (hs : s ∈ Set.Icc (min a₀ a₁) (max a₀ a₁)) :
    ρ ^ s ≤ max 1 (max (ρ ^ a₀) (ρ ^ a₁)) := by
  have h₁ : ρ ^ min a₀ a₁ ≤ max 1 (max (ρ ^ a₀) (ρ ^ a₁)) := by
    rcases le_total a₀ a₁ with hle | hle
    · rw [min_eq_left hle]
      exact (le_max_left (ρ ^ a₀) (ρ ^ a₁)).trans (le_max_right 1 _)
    · rw [min_eq_right hle]
      exact (le_max_right (ρ ^ a₀) (ρ ^ a₁)).trans (le_max_right 1 _)
  have h₂ : ρ ^ max a₀ a₁ ≤ max 1 (max (ρ ^ a₀) (ρ ^ a₁)) := by
    rcases le_total a₀ a₁ with hle | hle
    · rw [max_eq_right hle]
      exact (le_max_right (ρ ^ a₀) (ρ ^ a₁)).trans (le_max_right 1 _)
    · rw [max_eq_left hle]
      exact (le_max_left (ρ ^ a₀) (ρ ^ a₁)).trans (le_max_right 1 _)
  rcases le_total 1 ρ with hρ1 | hρ1
  · exact (Real.rpow_le_rpow_of_exponent_le hρ1 hs.2).trans h₂
  · exact (Real.rpow_le_rpow_of_exponent_ge hρ hρ1 hs.1).trans h₁

/-- Pointwise bound for the elementary analytic family along the closed vertical strip:
for `re z ∈ [0, 1]` and real exponents `a₀, a₁`,

`‖phasePow c (expFamily a₀ a₁ z)‖ ≤ max 1 (max (‖c‖ ^ a₀) (‖c‖ ^ a₁))`.

For `c = 0` the left-hand side vanishes; for `c ≠ 0` it is `‖c‖ ^ (expFamily a₀ a₁ z).re`
(the phase factor `c/‖c‖` has modulus one was taken out), and the exponent lies between
`a₀` and `a₁` by `expFamily_re_mem_Icc_of_mem`. -/
lemma norm_phasePow_expFamily_le_of_re_mem {c : ℂ} {a₀ a₁ : ℝ} {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ‖phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z)‖ ≤ max 1 (max (‖c‖ ^ a₀) (‖c‖ ^ a₁)) := by
  by_cases hc : c = 0
  · subst hc
    simp
  · have hnorm : ‖phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z)‖
        = ‖c‖ ^ (expFamily (a₀ : ℂ) (a₁ : ℂ) z).re := by
      rw [phasePow, norm_mul, norm_phase_of_ne_zero hc, mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hc)]
    rw [hnorm]
    exact rpow_le_max_one_of_mem_Icc (norm_pos_iff.mpr hc) (expFamily_re_mem_Icc_of_mem hz)

/-- If `‖F z‖ ≤ M` for all `z ∈ s`, then the `norm` of `F` is bounded above on `s`. -/
lemma bddAbove_image_norm_of_le {E : Type*} [NormedAddCommGroup E] {F : ℂ → E} {s : Set ℂ}
    {M : ℝ} (h : ∀ z ∈ s, ‖F z‖ ≤ M) : BddAbove ((norm ∘ F) '' s) := by
  rw [bddAbove_def]
  refine ⟨M, ?_⟩
  rintro y ⟨z, hz, hyz⟩
  rw [← hyz]
  exact h z hz

/-- Triangle inequality for a finite double sum: `‖∑ i ∑ j, T i j‖ ≤ ∑ i ∑ j, ‖T i j‖` with
each summand dominated by `U i j`. -/
lemma norm_double_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ) (T : ι → κ → ℂ)
    (U : ι → κ → ℝ) (h : ∀ i ∈ s, ∀ j ∈ t, ‖T i j‖ ≤ U i j) :
    ‖∑ i ∈ s, ∑ j ∈ t, T i j‖ ≤ ∑ i ∈ s, ∑ j ∈ t, U i j := by
  refine (norm_sum_le s (fun i => ∑ j ∈ t, T i j)).trans (Finset.sum_le_sum fun i hi => ?_)
  exact (norm_sum_le t (fun j => T i j)).trans (Finset.sum_le_sum fun j hj => h i hi j hj)

lemma bddAbove_bilinear_family {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (Λ : (α → ℂ) → (β → ℂ) → ℂ) (f : SimpleFunc α ℂ) (g : SimpleFunc β ℂ) (a₀ a₁ b₀ b₁ : ℝ) (hΛ : ∀ z : ℂ, Λ (Work.Analysis.Interpolation.analyticFamily (f : α → ℂ) (a₀ : ℂ) (a₁ : ℂ) z) (Work.Analysis.Interpolation.analyticFamily (g : β → ℂ) (b₀ : ℂ) (b₁ : ℂ) z) = ∑ c ∈ f.range, ∑ d ∈ g.range, (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily (a₀ : ℂ) (a₁ : ℂ) z) * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily (b₀ : ℂ) (b₁ : ℂ) z)) * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ))))) : BddAbove ((norm ∘ fun z : ℂ => Λ (Work.Analysis.Interpolation.analyticFamily (f : α → ℂ) (a₀ : ℂ) (a₁ : ℂ) z) (Work.Analysis.Interpolation.analyticFamily (g : β → ℂ) (b₀ : ℂ) (b₁ : ℂ) z)) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  -- The explicit bound: the finite double sum of the "constant" terms
  -- `bound c * bound d * ‖Λ 1_{f⁻¹{c}} 1_{g⁻¹{d}}‖`.
  refine bddAbove_image_norm_of_le (M := ∑ c ∈ f.range, ∑ d ∈ g.range,
    (max 1 (max (‖c‖ ^ a₀) (‖c‖ ^ a₁))) * (max 1 (max (‖d‖ ^ b₀) (‖d‖ ^ b₁))) *
      ‖Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))‖) ?_
  intro z hz
  have hzre : z.re ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  -- Per-term bound, from the pointwise bound on the `phasePow` factors.
  have hterm : ∀ c ∈ f.range, ∀ d ∈ g.range,
      ‖(phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z) * phasePow d (expFamily (b₀ : ℂ) (b₁ : ℂ) z)) *
        Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))‖
      ≤ (max 1 (max (‖c‖ ^ a₀) (‖c‖ ^ a₁))) * (max 1 (max (‖d‖ ^ b₀) (‖d‖ ^ b₁))) *
        ‖Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))‖ := by
    intro c _ d _
    have hc : 0 ≤ max 1 (max (‖c‖ ^ a₀) (‖c‖ ^ a₁)) := le_trans zero_le_one (le_max_left 1 _)
    have hd : 0 ≤ max 1 (max (‖d‖ ^ b₀) (‖d‖ ^ b₁)) := le_trans zero_le_one (le_max_left 1 _)
    simp only [norm_mul]
    exact mul_le_mul
      (mul_le_mul (norm_phasePow_expFamily_le_of_re_mem hzre)
        (norm_phasePow_expFamily_le_of_re_mem hzre) (norm_nonneg _) hc)
      le_rfl (norm_nonneg _) (mul_nonneg hc hd)
  rw [hΛ z]
  exact norm_double_sum_le f.range g.range
    (fun c d => (phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z) * phasePow d (expFamily (b₀ : ℂ) (b₁ : ℂ) z)) *
      Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ))))
    (fun c d => (max 1 (max (‖c‖ ^ a₀) (‖c‖ ^ a₁))) * (max 1 (max (‖d‖ ^ b₀) (‖d‖ ^ b₁))) *
      ‖Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))‖)
    hterm

end Work.Analysis.Interpolation
