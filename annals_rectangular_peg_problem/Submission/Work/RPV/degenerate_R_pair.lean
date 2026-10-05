import Mathlib
import Submission.Work.RPV.Defs

/-!
# The degenerate rectangles `[A,A,B,B]` and `[A,B,B,A]` (`Work.RPV`)

Every segment `[A,B]` in the plane is a rectangle with a vanishing side: it is a rotated,
axis-parallel degenerate rectangle.  Concretely, for any two points `A B : ℂ` the corner list
`![A,A,B,B]` (resp. `![A,B,B,A]`) is `RectangularPegProblem.R z' w' θ'` for suitable
`θ' z' w'`, where `z' - w'` is purely imaginary (resp. real) of modulus `‖A - B‖`.

This is the degenerate case `z.re = w.re` / `z.im = w.im` of the "similarity bookkeeping" used
to reduce the generic rectangle-existence statement to the challenge `theorem_1`: the
non-degenerate corners `x, x', y, y'` of the paper always come with `x ≠ y`, and a pair of
distinct points `A, B` has to be reachable by a rectangle of one of the two possible
degenerate shapes.

The construction: if `z = A/u`, `w = B/u` with `‖u‖ = 1` and `(A - B)/u` purely imaginary
(so `z.re = w.re`), then
`R z w θ = ![z*u, ((w.re) + z.im*I)*u, w*u, (z.re + w.im*I)*u] = ![A, A, B, B]`,
because `w.re + z.im*I = z` and `z.re + w.im*I = w`.  The angle `θ` with
`θ.toCircle = u` exists because every unit complex number is `exp (θ * I)`.
-/

namespace Work.RPV

open RectangularPegProblem Complex

/-- If `θ.toCircle = u` and `(A - B)/u = ‖A - B‖ * I` (so that `A/u - B/u` is purely imaginary,
i.e. `z = A/u`, `w = B/u` are the endpoints of a rotated vertical segment) then the degenerate
rectangle `![A, A, B, B]` is exhibited by `z = A/u`, `w = B/u`, `θ`. -/
private lemma degenerate_R_pair_vert (A B : ℂ) (θ : Real.Angle) (u : ℂ)
    (hθ : (θ.toCircle : ℂ) = u) (hu : u ≠ 0) (hd : (A - B) / u = ↑‖A - B‖ * I) :
    RectangularPegProblem.R (A / u) (B / u) θ = ![A, A, B, B] ∧
      |(A / u).re - (B / u).re| = 0 ∧ |(A / u).im - (B / u).im| = ‖A - B‖ := by
  have hsub : A / u - B / u = ↑‖A - B‖ * I := by rw [← sub_div, hd]
  have hre : (A / u).re = (B / u).re := by
    have h : (A / u).re - (B / u).re = 0 := by simpa using congrArg Complex.re hsub
    exact sub_eq_zero.mp h
  have h1 : ((B / u).re + (A / u).im * I) = A / u := by
    rw [Complex.ext_iff]
    constructor
    · simp [hre]
    · simp
  have h2 : ((A / u).re + (B / u).im * I) = B / u := by
    rw [Complex.ext_iff]
    constructor
    · simp [hre]
    · simp
  have hA : A / u * u = A := div_mul_cancel₀ A hu
  have hB : B / u * u = B := div_mul_cancel₀ B hu
  refine ⟨?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [RectangularPegProblem.R, hθ, h1, h2, hA, hB]
  · simp [hre]
  · rw [← Complex.sub_im, hsub]
    simp

/-- If `θ.toCircle = u` and `(A - B)/u = ‖A - B‖` (so that `A/u - B/u` is real, i.e. `z = A/u`,
`w = B/u` are the endpoints of a rotated horizontal segment) then the degenerate rectangle
`![A, B, B, A]` is exhibited by `z = A/u`, `w = B/u`, `θ`. -/
private lemma degenerate_R_pair_horiz (A B : ℂ) (θ : Real.Angle) (u : ℂ)
    (hθ : (θ.toCircle : ℂ) = u) (hu : u ≠ 0) (hd : (A - B) / u = ↑‖A - B‖) :
    RectangularPegProblem.R (A / u) (B / u) θ = ![A, B, B, A] ∧
      |(A / u).re - (B / u).re| = ‖A - B‖ ∧ |(A / u).im - (B / u).im| = 0 := by
  have hsub : A / u - B / u = ↑‖A - B‖ := by rw [← sub_div, hd]
  have him : (A / u).im = (B / u).im := by
    have h : (A / u).im - (B / u).im = 0 := by simpa using congrArg Complex.im hsub
    exact sub_eq_zero.mp h
  have h1 : ((B / u).re + (A / u).im * I) = B / u := by
    rw [Complex.ext_iff]
    constructor
    · simp
    · simp [him]
  have h2 : ((A / u).re + (B / u).im * I) = A / u := by
    rw [Complex.ext_iff]
    constructor
    · simp
    · simp [him]
  have hA : A / u * u = A := div_mul_cancel₀ A hu
  have hB : B / u * u = B := div_mul_cancel₀ B hu
  refine ⟨?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [RectangularPegProblem.R, hθ, h1, h2, hA, hB]
  · rw [← Complex.sub_re, hsub]
    simp
  · simp [him]

theorem degenerate_R_pair (A B : ℂ) :
    (∃ (θ' : Real.Angle) (z' w' : ℂ),
        RectangularPegProblem.R z' w' θ' = ![A, A, B, B] ∧
        |z'.re - w'.re| = 0 ∧ |z'.im - w'.im| = ‖A - B‖) ∧
    (∃ (θ' : Real.Angle) (z' w' : ℂ),
        RectangularPegProblem.R z' w' θ' = ![A, B, B, A] ∧
        |z'.re - w'.re| = ‖A - B‖ ∧ |z'.im - w'.im| = 0) := by
  constructor
  · by_cases hAB : A = B
    · refine ⟨0, A, A, ?_, by simp, by simp [hAB]⟩
      funext i
      fin_cases i <;> simp [RectangularPegProblem.R, hAB, Complex.re_add_im]
    · have hd0 : (A - B) ≠ 0 := sub_ne_zero.mpr hAB
      have hnorm_ne : (‖A - B‖ : ℂ) ≠ 0 := by simp [norm_ne_zero_iff.mpr hd0]
      set u : ℂ := (A - B) / (↑‖A - B‖ * I) with hu_eq
      have hu : u ≠ 0 := by
        rw [hu_eq]
        exact div_ne_zero hd0 (mul_ne_zero hnorm_ne I_ne_zero)
      have hunit : ‖u‖ = 1 := by
        rw [hu_eq, norm_div]
        have hI : ‖(↑‖A - B‖ : ℂ) * I‖ = ‖A - B‖ := by simp
        rw [hI]
        exact div_self (norm_ne_zero_iff.mpr hd0)
      have hd : (A - B) / u = ↑‖A - B‖ * I := by
        rw [hu_eq, div_div_eq_mul_div]
        exact mul_div_cancel_left₀ _ hd0
      obtain ⟨r, hr⟩ := (Complex.norm_eq_one_iff u).mp hunit
      exact ⟨(↑r : Real.Angle), A / u, B / u,
        degenerate_R_pair_vert A B _ u (by rw [Real.Angle.toCircle_coe]; exact hr) hu hd⟩
  · by_cases hAB : A = B
    · refine ⟨0, A, A, ?_, by simp [hAB], by simp⟩
      funext i
      fin_cases i <;> simp [RectangularPegProblem.R, hAB, Complex.re_add_im]
    · have hd0 : (A - B) ≠ 0 := sub_ne_zero.mpr hAB
      have hnorm_ne : (‖A - B‖ : ℂ) ≠ 0 := by simp [norm_ne_zero_iff.mpr hd0]
      set u : ℂ := (A - B) / ↑‖A - B‖ with hu_eq
      have hu : u ≠ 0 := by
        rw [hu_eq]
        exact div_ne_zero hd0 hnorm_ne
      have hunit : ‖u‖ = 1 := by
        rw [hu_eq, norm_div]
        simp only [Complex.norm_real]
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact div_self (norm_ne_zero_iff.mpr hd0)
      have hd : (A - B) / u = ↑‖A - B‖ := by
        rw [hu_eq, div_div_eq_mul_div]
        exact mul_div_cancel_left₀ _ hd0
      obtain ⟨r, hr⟩ := (Complex.norm_eq_one_iff u).mp hunit
      exact ⟨(↑r : Real.Angle), A / u, B / u,
        degenerate_R_pair_horiz A B _ u (by rw [Real.Angle.toCircle_coe]; exact hr) hu hd⟩

end Work.RPV
