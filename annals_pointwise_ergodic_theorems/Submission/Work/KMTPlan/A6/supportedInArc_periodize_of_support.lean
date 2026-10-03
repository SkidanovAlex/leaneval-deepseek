import Mathlib
import Submission.Work.Analysis.IonescuWainger.EtaCut
import Submission.Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.memLp_periodize
import Submission.Work.Analysis.IonescuWainger.multiplier_add
import Submission.Work.Analysis.IonescuWainger.multiplier_comp
import Submission.Work.Analysis.IonescuWainger.norm_iwOpSet_le
import Submission.Work.Analysis.IonescuWainger.one_div_le_norm_of_ne
import Submission.Work.Analysis.IonescuWainger.supportedInArc_periodize

/-!
# Support of the periodisation, in the form needed by A6

Let `φ : ℝ → ℂ` be a function whose support is contained in the real arc
`ℝ_{≤k} = [-2^k, 2^k]`, i.e.

`φ x ≠ 0 → |x| ≤ 2^k`     (`k ≤ 0`, so `2^k ≤ 1`).

Then the periodisation `Φ = periodize φ` on the frequency circle `ℝ/ℤ` is supported, as a
function on the circle, in the image of that same arc:

`Φ ξ ≠ 0 → ∃ θ ∈ ℝ_{≤k}, θ ≡ ξ  (mod 1)`.

This is `Work.Analysis.IonescuWainger.supportedInArc_periodize` with the summability
hypothesis `∀ x, Summable fun j : ℤ => φ (x + j)` **removed**: the latter is not needed,
because the argument only uses that, if *every* translate `x + j` is a zero of `φ`, then the
`tsum` defining `periodize φ ξ` is the sum of the zero family, hence `0` (a `tsum` of a
vanishing family is `0` whether or not it converges, in the Hausdorff setting where `tsum`
is defined).  Concretely, for `ξ` with `Φ ξ ≠ 0` some translate `x₀ + j` of the canonical
representative `x₀ ∈ [0,1)` of `ξ` must be a non-zero of `φ`; then `x₀ + j ∈ ℝ_{≤k}` by
hypothesis, and `x₀ + j ≡ ξ (mod 1)`.

The requested A6 statement is the special case `k = -3u` (`u ≥ 1`), where the hypothesis
`|ξ| ≤ 2^{-3u}` is exactly membership in `ℝ_{≤-3u}`; note that the numerical smallness of
`2^{-3u} ≤ 1/8` is *not* used.  (The hypothesis `hu : 1 ≤ u` is therefore also not needed,
but the statement is kept verbatim as requested.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.KMTPlan.A6

/-- **Support of the periodisation.**  If the support of `φ : ℝ → ℂ` is contained in the real
arc `realArc k`, then the periodisation `periodize φ : ℝ/ℤ → ℂ` is supported in the image of
that arc in `ℝ/ℤ`.  No summability hypothesis on the translates of `φ` is needed. -/
theorem supportedInArc_periodize_of_arc {k : ℤ} {φ : ℝ → ℂ}
    (hφ : ∀ x : ℝ, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k) :
    Work.Analysis.IonescuWainger.SupportedInArc k
      (Work.Analysis.IonescuWainger.periodize φ) := by
  intro ξ hξ
  -- Some translate `x₀ + j` of the canonical representative `x₀` of `ξ` is a non-zero of `φ`.
  obtain ⟨j, hj⟩ : ∃ j : ℤ, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + j) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hξ (by
      unfold Work.Analysis.IonescuWainger.periodize
      have h0 : (fun k : ℤ => φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k))
          = fun _ : ℤ => (0 : ℂ) := funext fun k => hcon k
      rw [h0, tsum_zero])
  refine ⟨(AddCircle.equivIco (1 : ℝ) 0 ξ).val + j, hφ _ hj, ?_⟩
  -- `x₀ + j ≡ x₀ ≡ ξ  (mod 1)`.
  have hxc : ((AddCircle.equivIco (1 : ℝ) 0 ξ).val
      : Work.Analysis.IonescuWainger.Circle) = ξ := by simp
  have hjc : ((j : ℝ) : Work.Analysis.IonescuWainger.Circle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨j, by simp⟩
  rw [AddCircle.coe_add, hxc, hjc, add_zero]

/-- **A6: support of the periodisation from a pointwise support condition.**
If `φ ξ ≠ 0` forces `|ξ| ≤ 2^{-3u}` with `u ≥ 1`, then the periodisation of `φ` is supported
in the arc `ℝ_{≤-3u}`. -/
theorem supportedInArc_periodize_of_support (u : ℕ) (hu : 1 ≤ u) (φ : ℝ → ℂ)
    (hφ : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ)))) :
    Work.Analysis.IonescuWainger.SupportedInArc (-(3 * (u : ℤ)))
      (Work.Analysis.IonescuWainger.periodize φ) := by
  refine supportedInArc_periodize_of_arc fun x hx => ?_
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
  exact ⟨neg_le_of_abs_le (hφ x hx), le_of_abs_le (hφ x hx)⟩

end Work.KMTPlan.A6
