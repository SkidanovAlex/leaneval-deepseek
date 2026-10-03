/-
# The shell symbol `DiSym ρ l k` is bounded by `1` on non-aliasing frequencies

The Littlewood--Paley *shell* symbol of §5 of Krause--Mirek--Tao,

`DiSym ρ l k = iwSymbolSet (kmtSet ρ l) (periodize (η_{≤k} − η_{≤k−1}))`,

is the sum of the translates `ξ ↦ (η_{≤k} − η_{≤k−1})(ξ − α)`, `α ∈ (ℚ/ℤ)_l`, of the
periodisation of the difference of the two rescaled cutoffs.  When the arithmetic frequencies
`(ℚ/ℤ)_l` are non-aliasing at scale `k` the arcs `α + ℝ_{≤k}` are pairwise disjoint, so at most
one summand can be nonzero; hence it suffices to know that the *single* module

`Ψ = periodize (η_{≤k} − η_{≤k−1})`

is supported in `ℝ_{≤k}` and bounded by `1`.  Both are elementary:

* `η_{≤k} − η_{≤k−1}` vanishes where both cutoffs vanish, i.e. off `ℝ_{≤k}` (the difference of two
  nonzero terms is zero unless one of them is nonzero, and each of the two cutoffs is supported in
  the coarser arc `ℝ_{≤k}`);
* `η_{≤k} − η_{≤k−1}` is a difference of two *real* numbers in `[0,1]` (the KMT cutoff `η` is
  real-valued with `0 ≤ η ≤ 1`), so it is bounded by `1` in modulus;

and the periodisation of a function supported in `ℝ_{≤k}` does not increase the sup norm when
`2^{k+1} < 1` (`Work.Analysis.IWMultiplier.periodize_norm_le`: at every point of the circle at
most one of the summands `φ (x + j)` is nonzero).  This is the hypothesis `h2` of the statement.

The two facts about `DiSym` announced in `BesselDefs` are therefore `DiSym_support` (the support,
in the sharper annulus form used in §5) and this file's `DiSym_norm_le`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BesselDefs
import Submission.Work.KMTAreas.A7.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Finset
open scoped BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- The difference `η_{≤k} − η_{≤k−1}` of the rescaled KMT cutoffs is supported in the arc
`ℝ_{≤k}`: a nonzero value of the difference forces one of the two cutoffs to be nonzero, and both
cutoffs are supported in `ℝ_{≤k}` (the finer one, in `ℝ_{≤k−1} ⊆ ℝ_{≤k}`). -/
theorem etaCut_sub_ne_zero_mem_realArc (k : ℤ) {x : ℝ}
    (h : (etaCut Work.KMTContract.kmtEta k - etaCut Work.KMTContract.kmtEta (k - 1)) x ≠ 0) :
    x ∈ realArc k := by
  rw [Pi.sub_apply] at h
  rcases eq_or_ne (etaCut Work.KMTContract.kmtEta k x) 0 with h1 | h1
  · have h2 : etaCut Work.KMTContract.kmtEta (k - 1) x ≠ 0 := by
      intro h2
      exact h (by rw [h1, h2, sub_zero])
    exact realArc_mono (by omega : k - 1 ≤ k)
      (Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc (k - 1) h2)
  · exact Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc k h1

/-- The difference `η_{≤k} − η_{≤k−1}` of the rescaled KMT cutoffs is bounded by `1` in modulus:
it is the difference of the two *real* numbers `η(y)` and `η(y/2)`, both of which lie in `[0,1]`
because the KMT cutoff `η` is real-valued with `0 ≤ η ≤ 1`. -/
theorem norm_etaCut_sub_le_one (k : ℤ) (x : ℝ) :
    ‖(etaCut Work.KMTContract.kmtEta k - etaCut Work.KMTContract.kmtEta (k - 1)) x‖ ≤ 1 := by
  have h1 : (0 : ℝ) ≤ Work.KMTContract.kmtBump (x / (2 : ℝ) ^ k) :=
    Work.KMTContract.kmtEta_nonneg _
  have h2 : Work.KMTContract.kmtBump (x / (2 : ℝ) ^ k) ≤ 1 := Work.KMTContract.kmtEta_le_one _
  have h3 : (0 : ℝ) ≤ Work.KMTContract.kmtBump (x / (2 : ℝ) ^ (k - 1)) :=
    Work.KMTContract.kmtEta_nonneg _
  have h4 : Work.KMTContract.kmtBump (x / (2 : ℝ) ^ (k - 1)) ≤ 1 :=
    Work.KMTContract.kmtEta_le_one _
  have hval : (etaCut Work.KMTContract.kmtEta k - etaCut Work.KMTContract.kmtEta (k - 1)) x
      = ((Work.KMTContract.kmtBump (x / (2 : ℝ) ^ k)
          - Work.KMTContract.kmtBump (x / (2 : ℝ) ^ (k - 1)) : ℝ) : ℂ) := by
    simp only [Pi.sub_apply, etaCut, Work.KMTContract.kmtEta, ← Complex.ofReal_sub]
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The family of translates `j ↦ (η_{≤k} − η_{≤k−1})(x + j)` is summable, being the difference of
the summable families of translates of the two cutoffs (`A7.summable_etaCut_shift`). -/
theorem summable_etaCut_sub_shift (k : ℤ) (x : ℝ) :
    Summable fun j : ℤ =>
      (etaCut Work.KMTContract.kmtEta k - etaCut Work.KMTContract.kmtEta (k - 1)) (x + j) := by
  simpa [Pi.sub_apply] using
    (Work.KMTAreas.A7.summable_etaCut_shift k x).sub
      (Work.KMTAreas.A7.summable_etaCut_shift (k - 1) x)

/-- The periodisation is additive on the difference of the two cutoffs. -/
theorem periodize_etaCut_sub (k : ℤ) :
    periodize (etaCut Work.KMTContract.kmtEta k - etaCut Work.KMTContract.kmtEta (k - 1))
      = periodize (etaCut Work.KMTContract.kmtEta k)
        - periodize (etaCut Work.KMTContract.kmtEta (k - 1)) := by
  funext ξ
  simp only [periodize, Pi.sub_apply]
  exact (Work.KMTAreas.A7.summable_etaCut_shift k _).tsum_sub
    (Work.KMTAreas.A7.summable_etaCut_shift (k - 1) _)

/-- **The shell symbol `DiSym ρ l k` is bounded by `1` on non-aliasing frequencies.**

The symbol is `∑_{α ∈ (ℚ/ℤ)_l} Ψ (ξ - α)` with `Ψ = periodize (η_{≤k} − η_{≤k−1})`; the
periodisation `Ψ` is supported in `ℝ_{≤k}` and bounded by `1`, so non-aliasing at scale `k`
leaves at most one nonzero summand, of modulus at most `1`. -/
theorem DiSym_norm_le (ρ : ℝ) (l : ℕ) (k : ℤ) (h2 : (2:ℝ)^(k+1) < 1)
    (hNA : Work.Analysis.IonescuWainger.NonAliasing k (Work.KMTPlan.A6.kmtSet ρ l)) :
    ∀ ξ, ‖Work.KMTPlan.A6.DiSym ρ l k ξ‖ ≤ 1 := by
  have hsupp : ∀ x, (etaCut Work.KMTContract.kmtEta k
      - etaCut Work.KMTContract.kmtEta (k - 1)) x ≠ 0 → x ∈ realArc k :=
    fun _ hx => etaCut_sub_ne_zero_mem_realArc k hx
  have hSupp : SupportedInArc k
      (periodize (etaCut Work.KMTContract.kmtEta k - etaCut Work.KMTContract.kmtEta (k - 1))) :=
    supportedInArc_periodize hsupp (summable_etaCut_sub_shift k)
  have hBnd : ∀ ξ, ‖periodize (etaCut Work.KMTContract.kmtEta k
      - etaCut Work.KMTContract.kmtEta (k - 1)) ξ‖ ≤ 1 :=
    Work.Analysis.IWMultiplier.periodize_norm_le h2 hsupp (norm_etaCut_sub_le_one k)
  intro ξ
  unfold DiSym
  rw [← periodize_etaCut_sub k]
  exact norm_iwSymbolSet_le_of_nonAliasing hNA hSupp (by norm_num) hBnd ξ

end

end Work.KMTPlan.A6
