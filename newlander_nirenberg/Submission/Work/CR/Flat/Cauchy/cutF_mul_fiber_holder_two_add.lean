/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Hölder estimate for `cutF j · F` on the tracked polydisc

The cutoff `openCut` is smooth, takes values in the real interval `[0,1]` and is
(by hypothesis) Lipschitz with constant `L`.  This file proves the analogous
statement to `cutFbar_mul_bound`, but for `cutF j` itself rather than for its
`∂̄`-derivative:

`a ↦ openCut (a j) · F a` is Hölder of exponent `α ∈ (0,1)` with constant
`(2 + L) · A` on the region where the coordinates different from `j` are
tracked (`‖a l‖ < trTrack` for `l ≠ j`) and `F` is bounded by `A` and Hölder of
exponent `α` with constant `A` on `trackSet`.

The point (shared with `cutFbar_mul_bound`) is that the `j`-th coordinate is
*not* required to be tracked: when `‖a j‖ ≥ trTrack > cutOut` the cutoff itself
vanishes, so the product is zero and the Lipschitz bound on `openCut` replaces
the vanishing.

The two elementary bounds used are

* `‖openCut ζ - openCut ζ'‖ ≤ 1` (the cutoff takes values in `[0,1]`), and
* `min (L d) 1 ≤ (1 + L) · d ^ α` for `0 ≤ d` and `0 < α < 1`.

With these, the standard decomposition
`cutF a · F a - cutF a' · F a' = cutF a · (F a - F a') + (cutF a - cutF a') · F a'`
gives the coefficient `1 + (1 + L) = 2 + L`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolRec

namespace Work.CR.Flat.Cauchy

open MeasureTheory Set

/-- The cutoff `openCut` takes values in the real interval `[0,1]`, hence the
oscillation of `openCut` is at most `1`. -/
lemma norm_openCut_sub_le_one (ζ ζ' : ℂ) : ‖openCut ζ - openCut ζ'‖ ≤ 1 := by
  rw [openCut_eq_openCutReal, openCut_eq_openCutReal, ← Complex.ofReal_sub]
  have key : ‖((openCutReal (Complex.normSq ζ) - openCutReal (Complex.normSq ζ') : ℝ) : ℂ)‖ =
      |openCutReal (Complex.normSq ζ) - openCutReal (Complex.normSq ζ')| := RCLike.norm_ofReal _
  rw [key]
  have h1 := openCutReal_nonneg (Complex.normSq ζ)
  have h2 := openCutReal_le_one (Complex.normSq ζ)
  have h3 := openCutReal_nonneg (Complex.normSq ζ')
  have h4 := openCutReal_le_one (Complex.normSq ζ')
  rw [abs_le]
  constructor <;> linarith

private lemma le_rpow_self {d α : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hα1 : α < 1) :
    d ≤ d ^ α := by
  have h := Real.rpow_le_rpow_of_exponent_ge hd hd1 (le_of_lt hα1)
  rwa [Real.rpow_one] at h

/-- The interpolation bound on the oscillation of a bounded Lipschitz cutoff:
for `0 ≤ d`, `0 < α < 1` and `D = d ^ α` one has `min (L · d) 1 ≤ (1 + L) · D`.
The two cases are `d ≤ 1` (where `d ≤ d ^ α`) and `d ≥ 1` (where `1 ≤ d ^ α`). -/
private lemma min_osc_le {L d D α : ℝ} (hL : 0 ≤ L) (hd : 0 ≤ d) (hα : 0 < α) (hα1 : α < 1)
    (hD : D = d ^ α) : min (L * d) 1 ≤ (1 + L) * D := by
  have hD0 : 0 ≤ D := by rw [hD]; exact Real.rpow_nonneg hd α
  rcases eq_or_lt_of_le hd with h | h
  · subst h
    rw [mul_zero, min_eq_left zero_le_one, hD, Real.zero_rpow (ne_of_gt hα), mul_zero]
  · rcases le_total d 1 with h1 | h1
    · have h2 : d ≤ d ^ α := le_rpow_self h h1 hα1
      calc min (L * d) 1 ≤ L * d := min_le_left _ _
        _ ≤ L * d ^ α := mul_le_mul_of_nonneg_left h2 hL
        _ = L * D := by rw [hD]
        _ ≤ (1 + L) * D := mul_le_mul_of_nonneg_right (by linarith : L ≤ 1 + L) hD0
    · have h2 : 1 ≤ d ^ α := Real.one_le_rpow h1 (le_of_lt hα)
      calc min (L * d) 1 ≤ 1 := min_le_right _ _
        _ ≤ d ^ α := h2
        _ = D := by rw [hD]
        _ ≤ (1 + L) * D := le_mul_of_one_le_left hD0 (by linarith : (1:ℝ) ≤ 1 + L)

/-- **The Hölder estimate for `cutF j · F`.**  On the region where the
coordinates different from `j` are tracked, the map `a ↦ openCut (a j) · F a` is
Hölder of exponent `α` with constant `(2 + L) A`, whenever `F` is bounded by `A`
and Hölder of exponent `α` with constant `A` on `trackSet` and `openCut` is
Lipschitz with constant `L`. -/
lemma cutF_mul_fiber_holder_two_add {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {j : Fin n} {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ ζ ζ' : ℂ, ‖openCut ζ - openCut ζ'‖ ≤ L * ‖ζ - ζ'‖)
    {F : (Fin n → ℂ) → ℂ} {A : ℝ} (hA0 : 0 ≤ A)
    (hF : ∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A)
    (hFh : ∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet →
      ‖F x - F y‖ ≤ A * ‖x - y‖ ^ α) :
    ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
      (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
      ‖cutF j a * F a - cutF j a' * F a'‖ ≤ (2 + L) * A * ‖a - a'‖ ^ α := by
  intro a a' ha ha'
  simp only [cutF_apply]
  set d : ℝ := ‖a - a'‖ with hddef
  set D : ℝ := d ^ α with hDdef
  have hd0 : 0 ≤ d := by rw [hddef]; exact norm_nonneg _
  have hD0 : 0 ≤ D := by rw [hDdef]; exact Real.rpow_nonneg hd0 α
  have hDR : D = ‖a - a'‖ ^ α := by rw [hDdef, hddef]
  have hcotr : cutOut < trTrack := by norm_num [cutOut, trTrack]
  have hjd : ‖a j - a' j‖ ≤ d := by
    rw [hddef]; simpa using norm_le_pi_norm (a - a') j
  have hosc : ‖openCut (a j) - openCut (a' j)‖ ≤ min (L * d) 1 := by
    refine le_min ?_ (norm_openCut_sub_le_one _ _)
    calc ‖openCut (a j) - openCut (a' j)‖ ≤ L * ‖a j - a' j‖ := hLip _ _
      _ ≤ L * d := mul_le_mul_of_nonneg_left hjd hL0
  -- If a point is not in `trackSet` but all its non-`j` coordinates are tracked,
  -- then its `j`-th coordinate is at least `trTrack`, hence `openCut` vanishes there.
  have hmem_j : ∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < trTrack) → z ∉ trackSet →
      trTrack ≤ ‖z j‖ := by
    intro z hz hzS
    have hex : ∃ l : Fin n, trTrack ≤ ‖z l‖ := by
      by_contra hcon
      exact hzS fun l => not_le.mp fun hlt => hcon ⟨l, hlt⟩
    obtain ⟨l, hl⟩ := hex
    by_cases hlj : l = j
    · rwa [hlj] at hl
    · exact absurd (hz l hlj) (not_lt.mpr hl)
  have hbase : ((1 + L) * D) * A ≤ (2 + L) * A * D := by
    calc ((1 + L) * D) * A = (D * A) * (1 + L) := by ring
      _ ≤ (D * A) * (2 + L) := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hD0 hA0)
      _ = (2 + L) * A * D := by ring
  by_cases haS : a ∈ trackSet
  · by_cases ha'S : a' ∈ trackSet
    · -- both points inside `trackSet`: use the Hölder bound for `F`
      have hFU : ‖F a - F a'‖ ≤ A * D := by rw [hDdef, hddef]; exact hFh a a' haS ha'S
      calc ‖openCut (a j) * F a - openCut (a' j) * F a'‖
          = ‖openCut (a j) * (F a - F a') + (openCut (a j) - openCut (a' j)) * F a'‖ :=
              congrArg norm (by ring)
        _ ≤ ‖openCut (a j) * (F a - F a')‖ + ‖(openCut (a j) - openCut (a' j)) * F a'‖ :=
              norm_add_le _ _
        _ = ‖openCut (a j)‖ * ‖F a - F a'‖ + ‖openCut (a j) - openCut (a' j)‖ * ‖F a'‖ := by
              rw [norm_mul, norm_mul]
        _ ≤ 1 * (A * D) + ((1 + L) * D) * A := by
              apply add_le_add
              · exact mul_le_mul (norm_openCut_le_one _) hFU (norm_nonneg _) zero_le_one
              · exact mul_le_mul (hosc.trans (min_osc_le hL0 hd0 hα hα1 hDdef))
                  (hF a' ha'S) (norm_nonneg _) (mul_nonneg (by linarith) hD0)
        _ = (2 + L) * A * D := by ring
        _ = (2 + L) * A * ‖a - a'‖ ^ α := by rw [hDR]
    · -- `a` is tracked, `a'` is not: the cutoff at `a'` vanishes
      have hja' : trTrack ≤ ‖a' j‖ := hmem_j a' ha' ha'S
      have hza' : openCut (a' j) = 0 := openCut_eq_zero_of_le_norm (le_trans hcotr.le hja')
      have hle : ‖openCut (a j)‖ ≤ min (L * d) 1 := by
        have h := hosc; rwa [hza', sub_zero] at h
      rw [hza', zero_mul, sub_zero, norm_mul]
      calc ‖openCut (a j)‖ * ‖F a‖
          ≤ (min (L * d) 1) * A :=
            mul_le_mul hle (hF a haS) (norm_nonneg _) (le_min (mul_nonneg hL0 hd0) zero_le_one)
        _ ≤ ((1 + L) * D) * A := mul_le_mul_of_nonneg_right (min_osc_le hL0 hd0 hα hα1 hDdef) hA0
        _ ≤ (2 + L) * A * D := hbase
        _ = (2 + L) * A * ‖a - a'‖ ^ α := by rw [hDR]
  · have hja : trTrack ≤ ‖a j‖ := hmem_j a ha haS
    have hza : openCut (a j) = 0 := openCut_eq_zero_of_le_norm (le_trans hcotr.le hja)
    by_cases ha'S : a' ∈ trackSet
    · -- `a` is not tracked, `a'` is: the cutoff at `a` vanishes
      have hle : ‖openCut (a' j)‖ ≤ min (L * d) 1 := by
        have h := hosc; rw [norm_sub_rev] at h; rwa [hza, sub_zero] at h
      rw [hza, zero_mul, zero_sub, norm_neg, norm_mul]
      calc ‖openCut (a' j)‖ * ‖F a'‖
          ≤ (min (L * d) 1) * A :=
            mul_le_mul hle (hF a' ha'S) (norm_nonneg _) (le_min (mul_nonneg hL0 hd0) zero_le_one)
        _ ≤ ((1 + L) * D) * A := mul_le_mul_of_nonneg_right (min_osc_le hL0 hd0 hα hα1 hDdef) hA0
        _ ≤ (2 + L) * A * D := hbase
        _ = (2 + L) * A * ‖a - a'‖ ^ α := by rw [hDR]
    · -- neither point is tracked: the product is `0` on both sides
      have hja' : trTrack ≤ ‖a' j‖ := hmem_j a' ha' ha'S
      have hza' : openCut (a' j) = 0 := openCut_eq_zero_of_le_norm (le_trans hcotr.le hja')
      rw [hza, hza', zero_mul, zero_mul, sub_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (by linarith) hA0) (Real.rpow_nonneg (norm_nonneg _) α)

end Work.CR.Flat.Cauchy
