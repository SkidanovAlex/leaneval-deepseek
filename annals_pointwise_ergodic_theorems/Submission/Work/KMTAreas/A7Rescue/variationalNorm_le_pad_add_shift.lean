import Mathlib
import Submission.Work.KMTAreas.A7Hi2.dilVarRealScale

/-!
# Splitting the variational norm at a cut point

For `r ≥ 1` and any sequence `a : ℕ → ℂ`, the `r`-variational norm of `a` is bounded by the sum
of

* the variational norm of the *clamped* sequence `k ↦ a (min k n₀)` (constant after `n₀`), and
* the variational norm of the *shifted tail* `k ↦ a (n₀ + k)`.

This is the bookkeeping identity that lets a variational estimate for a sequence be assembled from
a variational estimate for its head and one for its tail.

## The proof

Write `b k = a (min k n₀)`, `c k = a (n₀ + k)` and `e k = c (k - n₀) - c 0`.  Then
`a = b + e` pointwise: for `k ≤ n₀` both `e k = 0` and `b k = a k`; for `n₀ ≤ k` we have
`b k = a n₀`, `c (k - n₀) = a k`, and the two copies of `a n₀` cancel.

* The *superemum* parts satisfy `⨆ k ‖a k‖ₑ ≤ (⨆ k ‖b k‖ₑ) + (⨆ k ‖c k‖ₑ)`: every `k` falls in
  the head (`‖a k‖ₑ = ‖b k‖ₑ`) or in the tail (`‖a k‖ₑ = ‖c (k - n₀)‖ₑ`).
* The *variation* parts satisfy `varPart r a ≤ varPart r b + varPart r c`, because subadditivity
  (`varPart_add_le`) reduces this to `varPart r e ≤ varPart r c`.  Subtracting the constant `c 0`
  does not change any increment (`varPart_sub_const`), and `k ↦ k - n₀` is monotone, so every
  chain of `k ↦ c (k - n₀)` is a chain of `c` with the same increments
  (`varPart_comp_mono_le`).

Adding the triangle inequality for `ℝ≥0∞` and reassociating gives the claim.
-/

namespace Work.KMTAreas.A7Rescue

open scoped ENNReal NNReal

/-- Reindexing a sequence along a monotone map does not increase the variation part: the images of
the chains of `n ↦ a (ψ n)` under `ψ` are chains of `a` with the same increments. -/
private lemma varPart_comp_mono_le (r : NNReal) {ψ : ℕ → ℕ} (hψ : Monotone ψ) (a : ℕ → ℂ) :
    Submission.PointwiseErgodicTheorems.varPart r (fun n => a (ψ n))
      ≤ Submission.PointwiseErgodicTheorems.varPart r a := by
  rw [Submission.PointwiseErgodicTheorems.varPart]
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  exact le_iSup_of_le J (le_iSup_of_le (ψ ∘ N) (le_iSup_of_le (hψ.comp hN) le_rfl))

/-- Subtracting a constant leaves every increment, hence the variation part, unchanged. -/
private lemma varPart_sub_const (r : NNReal) (z : ℂ) (a : ℕ → ℂ) :
    Submission.PointwiseErgodicTheorems.varPart r (fun n => a n - z)
      = Submission.PointwiseErgodicTheorems.varPart r a := by
  rw [Submission.PointwiseErgodicTheorems.varPart, Submission.PointwiseErgodicTheorems.varPart]
  refine le_antisymm (iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_)
    (iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_)
  · rw [show (fun i : Fin J => a (N (↑i + 1)) - z - (a (N ↑i) - z))
        = (fun i : Fin J => a (N (↑i + 1)) - a (N ↑i)) from by funext i; ring]
    exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
  · rw [show (fun i : Fin J => a (N (↑i + 1)) - a (N ↑i))
        = (fun i : Fin J => a (N (↑i + 1)) - z - (a (N ↑i) - z)) from by funext i; ring]
    exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))

theorem variationalNorm_le_pad_add_shift {r : NNReal} (hr : 1 ≤ r) (a : ℕ → ℂ) (n₀ : ℕ) :
    PointwiseErgodicTheorems.variationalNorm r a
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun k => a (min k n₀))
        + PointwiseErgodicTheorems.variationalNorm r (fun k => a (n₀ + k)) := by
  set b : ℕ → ℂ := fun k => a (min k n₀) with hb
  set c : ℕ → ℂ := fun k => a (n₀ + k) with hc
  set e : ℕ → ℂ := fun k => c (k - n₀) - c 0 with he
  have hadd : a = b + e := by
    funext k
    by_cases hk : k ≤ n₀
    · have h1 : min k n₀ = k := min_eq_left hk
      have h2 : k - n₀ = 0 := Nat.sub_eq_zero_of_le hk
      simp [hb, hc, he, h1, h2]
    · have hk' : n₀ ≤ k := le_of_lt (Nat.lt_of_not_le hk)
      have h1 : min k n₀ = n₀ := min_eq_right hk'
      have h2 : n₀ + (k - n₀) = k := Nat.add_sub_cancel' hk'
      simp [hb, hc, he, h1, h2]
  have hsup : (⨆ k, ‖a k‖ₑ) ≤ (⨆ k, ‖b k‖ₑ) + (⨆ k, ‖c k‖ₑ) := by
    refine iSup_le fun k => ?_
    by_cases hk : k ≤ n₀
    · rw [show a k = b k by simp [hb, min_eq_left hk]]
      exact le_add_right (le_iSup (fun k => ‖b k‖ₑ) k)
    · have hk' : n₀ ≤ k := le_of_lt (Nat.lt_of_not_le hk)
      rw [show a k = c (k - n₀) by
        simp only [hc]
        rw [Nat.add_sub_cancel' hk']]
      exact le_add_left (le_iSup (fun k => ‖c k‖ₑ) (k - n₀))
  have hvar : Submission.PointwiseErgodicTheorems.varPart r a
      ≤ Submission.PointwiseErgodicTheorems.varPart r b
        + Submission.PointwiseErgodicTheorems.varPart r c := by
    rw [hadd]
    calc Submission.PointwiseErgodicTheorems.varPart r (b + e)
        ≤ Submission.PointwiseErgodicTheorems.varPart r b
            + Submission.PointwiseErgodicTheorems.varPart r e :=
          Submission.PointwiseErgodicTheorems.varPart_add_le hr b e
      _ ≤ Submission.PointwiseErgodicTheorems.varPart r b
            + Submission.PointwiseErgodicTheorems.varPart r c := by
          refine add_le_add le_rfl ?_
          calc Submission.PointwiseErgodicTheorems.varPart r e
              = Submission.PointwiseErgodicTheorems.varPart r (fun k => c (k - n₀) - c 0) := by
                rw [he]
            _ = Submission.PointwiseErgodicTheorems.varPart r (fun k => c (k - n₀)) :=
                varPart_sub_const r (c 0) (fun k => c (k - n₀))
            _ ≤ Submission.PointwiseErgodicTheorems.varPart r c :=
                varPart_comp_mono_le r (fun i j hij => Nat.sub_le_sub_right hij n₀) c
  calc PointwiseErgodicTheorems.variationalNorm r a
      = (⨆ k, ‖a k‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r a := rfl
    _ ≤ ((⨆ k, ‖b k‖ₑ) + (⨆ k, ‖c k‖ₑ))
          + (Submission.PointwiseErgodicTheorems.varPart r b
              + Submission.PointwiseErgodicTheorems.varPart r c) := add_le_add hsup hvar
    _ = ((⨆ k, ‖b k‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r b)
          + ((⨆ k, ‖c k‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r c) := by
        rw [add_add_add_comm]
    _ = PointwiseErgodicTheorems.variationalNorm r b
          + PointwiseErgodicTheorems.variationalNorm r c := by
        rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add,
            Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
    _ = PointwiseErgodicTheorems.variationalNorm r (fun k => a (min k n₀))
          + PointwiseErgodicTheorems.variationalNorm r (fun k => a (n₀ + k)) := by
        rw [hb, hc]

end Work.KMTAreas.A7Rescue
