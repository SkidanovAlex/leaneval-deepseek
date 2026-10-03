import Mathlib
import Submission.Work.Analysis.Variation.variationalNorm_eq_iSup_VrFull
import Submission.Work.Analysis.Paraproduct.SmallScale

namespace Work.KMTPlan.A6

open scoped ENNReal NNReal BigOperators

/-- **Vanishing makes the truncated variation independent of the truncation.**  If the sequence
`a` vanishes beyond `K` and `K < L`, then the `r`-variation truncated at any `M` is bounded by the
`r`-variation truncated at `L`.

Indeed, given a chain `u` with `u i ≤ M`, replacing `u i` by `min (u i) L` does not change any of
the values `a (u i)` (either `u i ≤ L` and nothing happens, or `u i > L > K`, in which case both
`a (u i)` and `a L` vanish), so no jump changes, while the clamped chain is bounded by `L`. -/
lemma Vr_le_of_vanishing {r : ℝ} {a : ℕ → ℂ} {K L M : ℕ} (hKL : K < L)
    (h : ∀ k : ℕ, K < k → a k = 0) :
    Work.Analysis.Variation.Vr r M a ≤ Work.Analysis.Variation.Vr r L a := by
  unfold Work.Analysis.Variation.Vr
  refine iSup_le fun J => iSup_le fun u => iSup_le fun hu => iSup_le fun h0 => iSup_le fun hM => ?_
  set v : Fin (J + 1) → ℕ := fun i => min (u i) L with hv
  have hvu : ∀ i, a (v i) = a (u i) := by
    intro i
    simp only [hv]
    rcases lt_or_ge (u i) L with hlt | hle
    · rw [min_eq_left hlt.le]
    · rw [min_eq_right hle]
      rcases eq_or_lt_of_le hle with heq | hlt'
      · rw [← heq]
      · rw [h (u i) (lt_trans hKL hlt'), h L hKL]
  have hmonov : Monotone v := by
    intro i j hij
    simp only [hv]
    exact min_le_min (hu hij) le_rfl
  have hv0 : v 0 = 0 := by simp only [hv]; simp [h0]
  have hvL : ∀ i, v i ≤ L := by intro i; simp only [hv]; exact min_le_right _ _
  have hsum : (∑ j : Fin J, ‖a (u j.succ) - a (u j.castSucc)‖ₑ ^ r)
      = ∑ j : Fin J, ‖a (v j.succ) - a (v j.castSucc)‖ₑ ^ r :=
    Finset.sum_congr rfl fun j _ => by rw [← hvu j.succ, ← hvu j.castSucc]
  rw [hsum]
  exact le_iSup_of_le J (le_iSup_of_le v (le_iSup_of_le hmonov
    (le_iSup_of_le hv0 (le_iSup_of_le hvL le_rfl))))

/-- **Vanishing and the supremum term.**  If `a` vanishes beyond `K`, the supremum of `‖a k‖ₑ`
over `k < M + 1` is bounded by the supremum over `k < K + 2`. -/
lemma iSup_enorm_fin_le_of_vanishing {a : ℕ → ℂ} {K : ℕ} (h : ∀ k : ℕ, K < k → a k = 0)
    (M : ℕ) : (⨆ k : Fin (M + 1), ‖a k‖ₑ) ≤ ⨆ k : Fin (K + 1 + 1), ‖a k‖ₑ := by
  refine iSup_le fun k => ?_
  rcases lt_or_ge (k : ℕ) (K + 1) with hk | hk
  · exact le_iSup (fun k : Fin (K + 1 + 1) => ‖a k‖ₑ) ⟨k, by omega⟩
  · rw [h k (by omega), enorm_zero]
    exact bot_le

/-- **The full truncated variational norm of a vanishing sequence is monotone in the truncation,
for any truncation above the support end.**  This is the conjunction of the two previous lemmas:
the supremum term and the variation term are each bounded by their counterparts at `K + 1`. -/
lemma VrFull_le_of_vanishing {r : ℝ} {a : ℕ → ℂ} {K : ℕ}
    (h : ∀ k : ℕ, K < k → a k = 0) (M : ℕ) :
    Work.Analysis.Variation.VrFull r M a ≤ Work.Analysis.Variation.VrFull r (K + 1) a := by
  unfold Work.Analysis.Variation.VrFull
  exact add_le_add (iSup_enorm_fin_le_of_vanishing h M)
    (Vr_le_of_vanishing (Nat.lt_succ_self K) h)

open MeasureTheory PointwiseErgodicTheorems in
open scoped ENNReal NNReal BigOperators in
/-- **The bridge from the truncated `V²`-norm to the full variational norm.**  If the family `u`
vanishes beyond `K`, then the *untruncated* `variationalNorm r` (over all of `ℕ`) of `u` is at most
the truncated `VrFull 2 (K+1)` norm of `u`, for every `r ≥ 2`.  This is what converts the
Rademacher--Menshov output (`VrFull`) into the target's norm. -/
theorem variationalNorm_le_VrFull {r : ℝ≥0} (hr : 2 ≤ r) (K : ℕ) (u : ℕ → ℂ)
    (h : ∀ k : ℕ, K < k → u k = 0) :
    PointwiseErgodicTheorems.variationalNorm r u
      ≤ Work.Analysis.Variation.VrFull 2 (K + 1) u := by
  -- The exponent is lowered to `2` by the elementary `ℓ^r ≤ ℓ²`-monotonicity of `varPart`;
  -- the truncated `VrFull 2 (K+1)` norm then bounds the untruncated `variationalNorm 2`.
  refine (Work.Analysis.Paraproduct.variationalNorm_mono_of_two_le hr u).trans ?_
  rw [Work.Analysis.Variation.variationalNorm_eq_iSup_VrFull 2 (by norm_num) u]
  refine iSup_le fun M => ?_
  have h2 : ((2 : ℝ≥0) : ℝ) = (2 : ℝ) := by norm_num
  rw [h2]
  exact VrFull_le_of_vanishing h M

end Work.KMTPlan.A6
