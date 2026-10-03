import Mathlib
import Submission.Work.Peluse.VanDerCorput.Defs
import Submission.Work.Peluse.PET.vdc_boundary_card

namespace Work.Peluse.PET

/-!
# The van der Corput boundary error (PET step)

`vdc_boundary` is the elementary bookkeeping lemma needed when passing from the *filtered*
correlation sums of Peluse's van der Corput inequality to the *unfiltered* range `[1,M]`:

for `g : ℤ → ℂ` with `‖g‖ ≤ 1` and any shift `a : ℤ`,

`∑_{y ∈ [1,M], y+a ∈ [1,M]} Re(conj (g (y+a)) · g y) ≤ ∑_{y ∈ [1,M]} Re(conj (g (y+a)) · g y) + |a|`.

Two ingredients:

* `Work.Peluse.PET.vdc_boundary_card` (proved in its own file): the complement
  `{y ∈ [1,M] : y + a ∉ [1,M]}` has at most `|a|` elements;
* `re_ge_neg_one` below: every summand is `≥ -1`, because `‖g‖ ≤ 1`.

Splitting the full sum into the filtered part and its complement, the complement contributes
at least `-(card complement) ≥ -|a|`, which gives the claim.
-/

/-- Every summand of the correlation sum is at least `-1`, since `‖g‖ ≤ 1`. -/
private lemma re_ge_neg_one (g : ℤ → ℂ) (hg : ∀ y : ℤ, ‖g y‖ ≤ 1) (a y : ℤ) :
    -(1 : ℝ) ≤ (star (g (y + a)) * g y).re := by
  have h1 : -(‖star (g (y + a)) * g y‖) ≤ (star (g (y + a)) * g y).re := by
    have h := Complex.re_le_norm (-(star (g (y + a)) * g y))
    rw [Complex.neg_re, norm_neg] at h
    linarith
  have h2 : ‖star (g (y + a)) * g y‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    nlinarith [hg (y + a), hg y, norm_nonneg (g (y + a)), norm_nonneg (g y)]
  linarith

set_option linter.unusedVariables false in
theorem vdc_boundary {M : ℕ} (hM : 1 ≤ M) (g : ℤ → ℂ) (hg : ∀ y : ℤ, ‖g y‖ ≤ 1) (a : ℤ) :
    ∑ y ∈ (Finset.Icc (1 : ℤ) (M : ℤ)).filter
        (fun y => y + a ∈ Finset.Icc (1 : ℤ) (M : ℤ)), (star (g (y + a)) * g y).re
      ≤ (∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), (star (g (y + a)) * g y).re) + |(a : ℝ)| := by
  set S : Finset ℤ := Finset.Icc (1 : ℤ) (M : ℤ) with hS
  -- split the full sum into the filtered part and its complement
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun y => y + a ∈ S)
      (fun y => (star (g (y + a)) * g y).re)
  -- the complement contributes at least `-|a|`, as it has at most `|a|` elements
  have hE : -((a.natAbs : ℕ) : ℝ) ≤
      ∑ y ∈ S.filter (fun y => ¬ (y + a ∈ S)), (star (g (y + a)) * g y).re := by
    have h1 : ∀ y ∈ S.filter (fun y => ¬ (y + a ∈ S)),
        -(1 : ℝ) ≤ (star (g (y + a)) * g y).re := fun y _ => re_ge_neg_one g hg a y
    have h2 := Finset.sum_le_sum h1
    have h3 : (∑ y ∈ S.filter (fun y => ¬ (y + a ∈ S)), (-(1 : ℝ)))
        = -(((S.filter (fun y => ¬ (y + a ∈ S))).card : ℕ) : ℝ) := by
      rw [Finset.sum_const]
      simp
    rw [h3] at h2
    have h4 : (((S.filter (fun y => ¬ (y + a ∈ S))).card : ℕ) : ℝ)
        ≤ ((a.natAbs : ℕ) : ℝ) := by
      rw [hS]
      exact_mod_cast vdc_boundary_card M a
    linarith
  have habs : ((a.natAbs : ℕ) : ℝ) = |(a : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  linarith [hsplit, hE, habs.le, habs.ge]

end Work.Peluse.PET
