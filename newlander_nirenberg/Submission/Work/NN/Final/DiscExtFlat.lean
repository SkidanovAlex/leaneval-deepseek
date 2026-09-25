/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The flat (half-space) route to the one-sided disc extension

This file sets up the reduction of the one-variable disc-extension property `DiscExt α c`
(from a function on `U × ball(0,1)` to one on `U × ball(0,c)`) to the *flat* Seeley extension
`Work.NN.Final.flatOneSidedExtension` (from `W × {0 < t}` to `W × {-δ < t}`).

The disc is straightened by the radial profile

  `discTau z = (1 - ‖z‖²)/2`,

which is smooth (a polynomial in the real coordinates), is positive exactly inside the unit
disc, and satisfies `‖z‖ * exp (discTau z) ≤ 1`; the latter is the inequality
`log s ≤ s - 1` and is what makes the unfolding land in the open unit disc.

* `discFold p = ((p.1, p.2), discTau p.2)` — the folding `X × ℂ → (X × ℂ) × ℝ`;
* `discUnfold2 q = (q.1.1, q.1.2 * exp (discTau q.1.2 - q.2))` — the unfolding
  `(X × ℂ) × ℝ → X × ℂ`, with `discUnfold2 ∘ discFold = id`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.DiscExtDefs

noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The radial profile `(1 - ‖z‖²)/2`: positive inside the unit disc, negative outside. -/
def discTau (z : ℂ) : ℝ := (1 - Complex.normSq z) / 2

lemma discTau_eq (z : ℂ) : discTau z = (1 - ‖z‖ ^ 2) / 2 := by
  rw [discTau, Complex.sq_norm]

lemma discTau_pos_iff {z : ℂ} : 0 < discTau z ↔ ‖z‖ < 1 := by
  rw [discTau_eq]
  constructor
  · intro h
    have h1 : ‖z‖ ^ 2 < 1 := by linarith
    nlinarith [norm_nonneg z]
  · intro h
    have h1 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    linarith

lemma discTau_nonpos_iff {z : ℂ} : discTau z ≤ 0 ↔ 1 ≤ ‖z‖ := by
  rw [discTau_eq]
  constructor
  · intro h
    have h1 : 1 ≤ ‖z‖ ^ 2 := by linarith
    nlinarith [norm_nonneg z]
  · intro h
    have h1 : 1 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    linarith

/-- The basic inequality making the unfolding land in the unit disc. -/
lemma norm_mul_exp_discTau_le_one (z : ℂ) : ‖z‖ * Real.exp (discTau z) ≤ 1 := by
  have hsq : (‖z‖ * Real.exp (discTau z)) ^ 2 = ‖z‖ ^ 2 * Real.exp (1 - ‖z‖ ^ 2) := by
    rw [mul_pow]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    rw [discTau_eq]; ring
  have hle : ‖z‖ ^ 2 * Real.exp (1 - ‖z‖ ^ 2) ≤ 1 := by
    have h2 : ‖z‖ ^ 2 ≤ Real.exp (‖z‖ ^ 2 - 1) := by
      linarith [Real.add_one_le_exp (‖z‖ ^ 2 - 1)]
    have h3 : Real.exp (‖z‖ ^ 2 - 1) * Real.exp (1 - ‖z‖ ^ 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; rw [Real.exp_zero]
    have h4 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (1 - ‖z‖ ^ 2)).le
    simpa only [h3, mul_one] using h4
    
  have hnn : 0 ≤ ‖z‖ * Real.exp (discTau z) := by positivity
  have key : (‖z‖ * Real.exp (discTau z)) ^ 2 ≤ 1 := by rw [hsq]; exact hle
  nlinarith [key, hnn]

/-- The folding map `X × ℂ → (X × ℂ) × ℝ`. -/
def discFold (p : X × ℂ) : (X × ℂ) × ℝ := ((p.1, p.2), discTau p.2)

@[simp] lemma discFold_apply (p : X × ℂ) : discFold p = ((p.1, p.2), discTau p.2) := rfl

@[simp] lemma discFold_fst (p : X × ℂ) : (discFold p).1 = (p.1, p.2) := rfl

@[simp] lemma discFold_snd (p : X × ℂ) : (discFold p).2 = discTau p.2 := rfl

/-- The unfolding map `(X × ℂ) × ℝ → X × ℂ`. -/
def discUnfold2 (q : (X × ℂ) × ℝ) : X × ℂ :=
  (q.1.1, q.1.2 * (Real.exp (discTau q.1.2 - q.2) : ℂ))

@[simp] lemma discUnfold2_apply (q : (X × ℂ) × ℝ) :
    discUnfold2 q = (q.1.1, q.1.2 * (Real.exp (discTau q.1.2 - q.2) : ℂ)) := rfl

/-- The unfolding is a left inverse of the folding. -/
@[simp] lemma discUnfold2_discFold (p : X × ℂ) : discUnfold2 (discFold p) = p := by
  simp [discUnfold2, discFold]

/-- Points of the open half space are unfolded into the open unit disc. -/
lemma norm_discUnfold2_snd_lt_one (q : (X × ℂ) × ℝ) (hq : 0 < q.2) :
    ‖(discUnfold2 q).2‖ < 1 := by
  rcases eq_or_lt_of_le (norm_nonneg q.1.2) with h | h
  · have hz : q.1.2 = 0 := by
      simpa [← norm_eq_zero] using h.symm
    rw [discUnfold2_apply, hz, zero_mul, norm_zero]
    norm_num
  · have hb := norm_mul_exp_discTau_le_one q.1.2
    have hexp : Real.exp (discTau q.1.2 - q.2) < Real.exp (discTau q.1.2) :=
      Real.exp_lt_exp.mpr (by linarith)
    calc ‖(discUnfold2 q).2‖
        = ‖q.1.2‖ * Real.exp (discTau q.1.2 - q.2) := by
          rw [discUnfold2_apply, norm_mul,
            show ‖((Real.exp (discTau q.1.2 - q.2) : ℝ) : ℂ)‖
              = Real.exp (discTau q.1.2 - q.2) from by
              rw [Complex.ofReal_exp, Complex.norm_exp, Complex.ofReal_re]]
      _ < ‖q.1.2‖ * Real.exp (discTau q.1.2) := mul_lt_mul_of_pos_left hexp h
      _ ≤ 1 := hb

/-! ## Smoothness and the half-space bound -/

lemma contDiff_discTau : ContDiff ℝ ∞ discTau := by
  have h : discTau = fun z : ℂ => (1 - (Complex.reCLM z * Complex.reCLM z
      + Complex.imCLM z * Complex.imCLM z)) / 2 := by
    funext z; rw [discTau, Complex.normSq_apply]; rfl
  rw [h]; fun_prop

lemma contDiff_discFold : ContDiff ℝ ∞ (discFold (X := X)) := by
  exact (by fun_prop : ContDiff ℝ ∞ (fun p : X × ℂ => ((p.1, p.2) : X × ℂ))).prodMk
    (contDiff_discTau.comp (by fun_prop))

lemma contDiff_discUnfold2 : ContDiff ℝ ∞ (discUnfold2 (X := X)) := by
  have ht : ContDiff ℝ ∞ (fun q : (X × ℂ) × ℝ => discTau q.1.2) :=
    contDiff_discTau.comp (by fun_prop)
  have hexp : ContDiff ℝ ∞ (fun q : (X × ℂ) × ℝ => Real.exp (discTau q.1.2 - q.2)) :=
    Real.contDiff_exp.comp (ht.sub (by fun_prop))
  have hof : ContDiff ℝ ∞ (fun q : (X × ℂ) × ℝ => ((Real.exp (discTau q.1.2 - q.2) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hexp
  exact (by fun_prop : ContDiff ℝ ∞ (fun q : (X × ℂ) × ℝ => q.1.1)).prodMk
    ((by fun_prop : ContDiff ℝ ∞ (fun q : (X × ℂ) × ℝ => q.1.2)).mul hof)

/-- The radial profile stays above `-(c²-1)/2` on the open disc of radius `c`. -/
lemma discTau_gt {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : ‖z‖ < c) :
    -((c ^ 2 - 1) / 2) < discTau z := by
  have h1 : ‖z‖ ^ 2 < c ^ 2 := by nlinarith [norm_nonneg z]
  rw [discTau_eq]
  linarith

end Work.NN.Final
